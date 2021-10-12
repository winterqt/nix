#include "derivations.hh"
#include "globals.hh"
#include "local-store.hh"
#include "local-fs-store.hh"
#include "finally.hh"
#include "find-roots.hh"

#include <functional>
#include <queue>
#include <algorithm>
#include <regex>
#include <random>

#include <sys/types.h>
#include <sys/stat.h>
#include <sys/statvfs.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <climits>

namespace nix {


static string gcLockName = "gc.lock";
static string gcRootsDir = "gcroots";


/* Acquire the global GC lock.  This is used to prevent new Nix
   processes from starting after the temporary root files have been
   read.  To be precise: when they try to create a new temporary root
   file, they will block until the garbage collector has finished /
   yielded the GC lock. */
AutoCloseFD LocalStore::openGCLock(LockType lockType)
{
    Path fnGCLock = (format("%1%/%2%")
        % stateDir % gcLockName).str();

    debug(format("acquiring global GC lock '%1%'") % fnGCLock);

    AutoCloseFD fdGCLock = open(fnGCLock.c_str(), O_RDWR | O_CREAT | O_CLOEXEC, 0600);
    if (!fdGCLock)
        throw SysError("opening global GC lock '%1%'", fnGCLock);

    if (!lockFile(fdGCLock.get(), lockType, false)) {
        printInfo("waiting for the big garbage collector lock...");
        lockFile(fdGCLock.get(), lockType, true);
    }

    /* !!! Restrict read permission on the GC root.  Otherwise any
       process that can open the file for reading can DoS the
       collector. */

    return fdGCLock;
}


static void makeSymlink(const Path & link, const Path & target)
{
    /* Create directories up to `gcRoot'. */
    createDirs(dirOf(link));

    /* Create the new symlink. */
    Path tempLink = (format("%1%.tmp-%2%-%3%")
        % link % getpid() % random()).str();
    createSymlink(target, tempLink);

    /* Atomically replace the old one. */
    if (rename(tempLink.c_str(), link.c_str()) == -1)
        throw SysError("cannot rename '%1%' to '%2%'",
            tempLink , link);
}


void LocalStore::syncWithGC()
{
    AutoCloseFD fdGCLock = openGCLock(ltRead);
}


void LocalStore::addIndirectRoot(const Path & path)
{
    string hash = hashString(htSHA1, path).to_string(Base32, false);
    Path realRoot = canonPath((format("%1%/%2%/auto/%3%")
        % stateDir % gcRootsDir % hash).str());
    makeSymlink(realRoot, path);
}


Path LocalFSStore::addPermRoot(const StorePath & storePath, const Path & _gcRoot)
{
    Path gcRoot(canonPath(_gcRoot));

    if (isInStore(gcRoot))
        throw Error(
                "creating a garbage collector root (%1%) in the Nix store is forbidden "
                "(are you running nix-build inside the store?)", gcRoot);

    /* Don't clobber the link if it already exists and doesn't
       point to the Nix store. */
    if (pathExists(gcRoot) && (!isLink(gcRoot) || !isInStore(readLink(gcRoot))))
        throw Error("cannot create symlink '%1%'; already exists", gcRoot);
    makeSymlink(gcRoot, printStorePath(storePath));
    addIndirectRoot(gcRoot);

    /* Grab the global GC root, causing us to block while a GC is in
       progress.  This prevents the set of permanent roots from
       increasing while a GC is in progress. */
    syncWithGC();

    return gcRoot;
}


void LocalStore::addTempRoot(const StorePath & path)
{
    auto state(_state.lock());

    /* Create the temporary roots file for this process. */
    if (!state->fdTempRoots) {

        while (1) {
            AutoCloseFD fdGCLock = openGCLock(ltRead);

            if (pathExists(fnTempRoots))
                /* It *must* be stale, since there can be no two
                   processes with the same pid. */
                unlink(fnTempRoots.c_str());

            state->fdTempRoots = openLockFile(fnTempRoots, true);

            fdGCLock = -1;

            debug(format("acquiring read lock on '%1%'") % fnTempRoots);
            lockFile(state->fdTempRoots.get(), ltRead, true);

            /* Check whether the garbage collector didn't get in our
               way. */
            struct stat st;
            if (fstat(state->fdTempRoots.get(), &st) == -1)
                throw SysError("statting '%1%'", fnTempRoots);
            if (st.st_size == 0) break;

            /* The garbage collector deleted this file before we could
               get a lock.  (It won't delete the file after we get a
               lock.)  Try again. */
        }

    }

    /* Upgrade the lock to a write lock.  This will cause us to block
       if the garbage collector is holding our lock. */
    debug(format("acquiring write lock on '%1%'") % fnTempRoots);
    lockFile(state->fdTempRoots.get(), ltWrite, true);

    string s = printStorePath(path) + '\0';
    writeFull(state->fdTempRoots.get(), s);

    /* Downgrade to a read lock. */
    debug(format("downgrading to read lock on '%1%'") % fnTempRoots);
    lockFile(state->fdTempRoots.get(), ltRead, true);
}


static std::string censored = "{censored}";


void LocalStore::findTempRoots(FDs & fds, Roots & tempRoots, bool censor)
{
    /* Read the `temproots' directory for per-process temporary root
       files. */
    for (auto & i : readDirectory(tempRootsDir)) {
        if (i.name[0] == '.') {
            // Ignore hidden files. Some package managers (notably portage) create
            // those to keep the directory alive.
            continue;
        }
        Path path = tempRootsDir + "/" + i.name;

        pid_t pid = std::stoi(i.name);

        debug(format("reading temporary root file '%1%'") % path);
        FDPtr fd(new AutoCloseFD(open(path.c_str(), O_CLOEXEC | O_RDWR, 0666)));
        if (!*fd) {
            /* It's okay if the file has disappeared. */
            if (errno == ENOENT) continue;
            throw SysError("opening temporary roots file '%1%'", path);
        }

        /* This should work, but doesn't, for some reason. */
        //FDPtr fd(new AutoCloseFD(openLockFile(path, false)));
        //if (*fd == -1) continue;

        /* Try to acquire a write lock without blocking.  This can
           only succeed if the owning process has died.  In that case
           we don't care about its temporary roots. */
        if (lockFile(fd->get(), ltWrite, false)) {
            printInfo("removing stale temporary roots file '%1%'", path);
            unlink(path.c_str());
            writeFull(fd->get(), "d");
            continue;
        }

        /* Acquire a read lock.  This will prevent the owning process
           from upgrading to a write lock, therefore it will block in
           addTempRoot(). */
        debug(format("waiting for read lock on '%1%'") % path);
        lockFile(fd->get(), ltRead, true);

        /* Read the entire file. */
        string contents = readFile(fd->get());

        /* Extract the roots. */
        string::size_type pos = 0, end;

        while ((end = contents.find((char) 0, pos)) != string::npos) {
            Path root(contents, pos, end - pos);
            debug("got temporary root '%s'", root);
            tempRoots[parseStorePath(root)].emplace(censor ? censored : fmt("{temp:%d}", pid));
            pos = end + 1;
        }

        fds.push_back(fd); /* keep open */
    }
}

void LocalStore::findRootsNoTempNoExternalDaemon(Roots & roots, bool censor)
{
    debug("Can’t connect to the tracing daemon socket, fallback to the internal trace");

    using namespace nix::roots_tracer;

    const TracerConfig opts {
      .storeDir = fs::path(storeDir),
      .stateDir = fs::path(stateDir.get())
    };
    const std::set<fs::path> standardRoots = {
        opts.stateDir / fs::path(gcRootsDir),
        opts.stateDir / fs::path("gcroots"),
    };
    auto traceResult = traceStaticRoots(opts, standardRoots);
    auto runtimeRoots = getRuntimeRoots(opts);
    traceResult.storeRoots.insert(runtimeRoots.begin(), runtimeRoots.end());
    for (auto & [rawRootInStore, externalRoots] : traceResult.storeRoots) {
        if (!isInStore(rawRootInStore)) continue;
        auto rootInStore = toStorePath(rawRootInStore).first;
        if (!isValidPath(rootInStore)) continue;
        std::unordered_set<std::string> primRoots;
        for (const auto & externalRoot : externalRoots)
            primRoots.insert(externalRoot.string());
        roots.emplace(rootInStore, primRoots);
    }
}


Roots LocalStore::findRoots(bool censor)
{
    Roots roots;
    findRootsNoTemp(roots, censor);

    FDs fds;
    findTempRoots(fds, roots, censor);

    return roots;
}

void LocalStore::findRootsNoTemp(Roots & roots, bool censor)
{

    auto fd = AutoCloseFD(socket(PF_UNIX, SOCK_STREAM
        #ifdef SOCK_CLOEXEC
        | SOCK_CLOEXEC
        #endif
        , 0));
    if (!fd)
        throw SysError("cannot create Unix domain socket");
    closeOnExec(fd.get());

    string socketPath = settings.gcSocketPath.get() != "auto"
        ? settings.gcSocketPath.get()
        : stateDir.get() + "/gc-socket/socket";

    struct sockaddr_un addr;
    addr.sun_family = AF_UNIX;

    if (socketPath.size() + 1 >= sizeof(addr.sun_path))
        throw Error("socket path '%1%' is too long", socketPath);
    strcpy(addr.sun_path, socketPath.c_str());

    if (::connect(fd.get(), (struct sockaddr *) &addr, sizeof(addr)) == -1)
        return findRootsNoTempNoExternalDaemon(roots, censor);

    settings.requireExperimentalFeature("external-gc-daemon");

    try {
        StringMap unescapes = {
            { "\\n", "\n"},
            { "\\t", "\t"},
        };
        while (true) {
            auto line = readLine(fd.get());
            if (line.empty()) break; // TODO: Handle the broken symlinks
            auto parsedLine = tokenizeString<std::vector<string>>(line, "\t");
            if (parsedLine.size() != 2)
                throw Error("Invalid result from the gc helper");
            auto rawDestPath = rewriteStrings(parsedLine[0], unescapes);
            auto retainer = rewriteStrings(parsedLine[1], unescapes);
            if (!isInStore(rawDestPath)) continue;
            try {
                auto destPath = toStorePath(rawDestPath).first;
                if (!isValidPath(destPath)) continue;
                roots[destPath].insert(
                    (!censor || isInDir(retainer, stateDir)) ? retainer : censored);
            } catch (Error &) {
            }
        }
    } catch (EndOfFile &) {
    }
}

typedef std::unordered_map<Path, std::unordered_set<std::string>> UncheckedRoots;

struct GCLimitReached { };

struct LocalStore::GCState
{
    const GCOptions & options;
    GCResults & results;
    StorePathSet roots;
    StorePathSet tempRoots;
    StorePathSet dead;
    StorePathSet alive;
    bool gcKeepOutputs;
    bool gcKeepDerivations;
    uint64_t bytesInvalidated;
    bool moveToTrash = true;
    bool shouldDelete;
    GCState(const GCOptions & options, GCResults & results)
        : options(options), results(results), bytesInvalidated(0) { }
};


bool LocalStore::isActiveTempFile(const GCState & state,
    const Path & path, const string & suffix)
{
    return hasSuffix(path, suffix)
        && state.tempRoots.count(parseStorePath(string(path, 0, path.size() - suffix.size())));
}


void LocalStore::deleteGarbage(GCState & state, const Path & path)
{
    uint64_t bytesFreed;
    deletePath(path, bytesFreed);
    state.results.bytesFreed += bytesFreed;
}


void LocalStore::deletePathRecursive(GCState & state, const Path & path)
{
    checkInterrupt();

    uint64_t size = 0;

    auto storePath = maybeParseStorePath(path);
    if (storePath && isValidPath(*storePath)) {
        StorePathSet referrers;
        queryReferrers(*storePath, referrers);
        for (auto & i : referrers)
            if (printStorePath(i) != path) deletePathRecursive(state, printStorePath(i));
        size = queryPathInfo(*storePath)->narSize;
        invalidatePathChecked(*storePath);
    }

    Path realPath = realStoreDir + "/" + std::string(baseNameOf(path));

    struct stat st;
    if (lstat(realPath.c_str(), &st)) {
        if (errno == ENOENT) return;
        throw SysError("getting status of %1%", realPath);
    }

    printInfo(format("deleting '%1%'") % path);

    state.results.paths.insert(path);

    /* If the path is not a regular file or symlink, move it to the
       trash directory.  The move is to ensure that later (when we're
       not holding the global GC lock) we can delete the path without
       being afraid that the path has become alive again.  Otherwise
       delete it right away. */
    if (state.moveToTrash && S_ISDIR(st.st_mode)) {
        // Estimate the amount freed using the narSize field.  FIXME:
        // if the path was not valid, need to determine the actual
        // size.
        try {
            if (chmod(realPath.c_str(), st.st_mode | S_IWUSR) == -1)
                throw SysError("making '%1%' writable", realPath);
            Path tmp = trashDir + "/" + std::string(baseNameOf(path));
            if (rename(realPath.c_str(), tmp.c_str()))
                throw SysError("unable to rename '%1%' to '%2%'", realPath, tmp);
            state.bytesInvalidated += size;
        } catch (SysError & e) {
            if (e.errNo == ENOSPC) {
                printInfo(format("note: can't create move '%1%': %2%") % realPath % e.msg());
                deleteGarbage(state, realPath);
            }
        }
    } else
        deleteGarbage(state, realPath);

    if (state.results.bytesFreed + state.bytesInvalidated > state.options.maxFreed) {
        printInfo(format("deleted or invalidated more than %1% bytes; stopping") % state.options.maxFreed);
        throw GCLimitReached();
    }
}


bool LocalStore::canReachRoot(GCState & state, StorePathSet & visited, const StorePath & path)
{
    if (visited.count(path)) return false;

    if (state.alive.count(path)) return true;

    if (state.dead.count(path)) return false;

    if (state.roots.count(path)) {
        debug("cannot delete '%1%' because it's a root", printStorePath(path));
        state.alive.insert(path);
        return true;
    }

    visited.insert(path);

    if (!isValidPath(path)) return false;

    StorePathSet incoming;

    /* Don't delete this path if any of its referrers are alive. */
    queryReferrers(path, incoming);

    /* If keep-derivations is set and this is a derivation, then
       don't delete the derivation if any of the outputs are alive. */
    if (state.gcKeepDerivations && path.isDerivation()) {
        for (auto & [name, maybeOutPath] : queryPartialDerivationOutputMap(path))
            if (maybeOutPath &&
                isValidPath(*maybeOutPath) &&
                queryPathInfo(*maybeOutPath)->deriver == path
                )
                incoming.insert(*maybeOutPath);
    }

    /* If keep-outputs is set, then don't delete this path if there
       are derivers of this path that are not garbage. */
    if (state.gcKeepOutputs) {
        auto derivers = queryValidDerivers(path);
        for (auto & i : derivers)
            incoming.insert(i);
    }

    for (auto & i : incoming)
        if (i != path)
            if (canReachRoot(state, visited, i)) {
                state.alive.insert(path);
                return true;
            }

    return false;
}


void LocalStore::tryToDelete(GCState & state, const Path & path)
{
    checkInterrupt();

    auto realPath = realStoreDir + "/" + std::string(baseNameOf(path));
    if (realPath == linksDir || realPath == trashDir) return;

    //Activity act(*logger, lvlDebug, format("considering whether to delete '%1%'") % path);

    auto storePath = maybeParseStorePath(path);

    if (!storePath || !isValidPath(*storePath)) {
        /* A lock file belonging to a path that we're building right
           now isn't garbage. */
        if (isActiveTempFile(state, path, ".lock")) return;

        /* Don't delete .chroot directories for derivations that are
           currently being built. */
        if (isActiveTempFile(state, path, ".chroot")) return;

        /* Don't delete .check directories for derivations that are
           currently being built, because we may need to run
           diff-hook. */
        if (isActiveTempFile(state, path, ".check")) return;
    }

    StorePathSet visited;

    if (storePath && canReachRoot(state, visited, *storePath)) {
        debug("cannot delete '%s' because it's still reachable", path);
    } else {
        /* No path we visited was a root, so everything is garbage.
           But we only delete ‘path’ and its referrers here so that
           ‘nix-store --delete’ doesn't have the unexpected effect of
           recursing into derivations and outputs. */
        for (auto & i : visited)
            state.dead.insert(i);
        if (state.shouldDelete)
            deletePathRecursive(state, path);
    }
}


/* Unlink all files in /nix/store/.links that have a link count of 1,
   which indicates that there are no other links and so they can be
   safely deleted.  FIXME: race condition with optimisePath(): we
   might see a link count of 1 just before optimisePath() increases
   the link count. */
void LocalStore::removeUnusedLinks(const GCState & state)
{
    AutoCloseDir dir(opendir(linksDir.c_str()));
    if (!dir) throw SysError("opening directory '%1%'", linksDir);

    int64_t actualSize = 0, unsharedSize = 0;

    struct dirent * dirent;
    while (errno = 0, dirent = readdir(dir.get())) {
        checkInterrupt();
        string name = dirent->d_name;
        if (name == "." || name == "..") continue;
        Path path = linksDir + "/" + name;

        auto st = lstat(path);

        if (st.st_nlink != 1) {
            actualSize += st.st_size;
            unsharedSize += (st.st_nlink - 1) * st.st_size;
            continue;
        }

        printMsg(lvlTalkative, format("deleting unused link '%1%'") % path);

        if (unlink(path.c_str()) == -1)
            throw SysError("deleting '%1%'", path);

        state.results.bytesFreed += st.st_size;
    }

    struct stat st;
    if (stat(linksDir.c_str(), &st) == -1)
        throw SysError("statting '%1%'", linksDir);
    int64_t overhead = st.st_blocks * 512ULL;

    printInfo("note: currently hard linking saves %.2f MiB",
        ((unsharedSize - actualSize - overhead) / (1024.0 * 1024.0)));
}


void LocalStore::collectGarbage(const GCOptions & options, GCResults & results)
{
    GCState state(options, results);
    state.gcKeepOutputs = settings.gcKeepOutputs;
    state.gcKeepDerivations = settings.gcKeepDerivations;

    /* Using `--ignore-liveness' with `--delete' can have unintended
       consequences if `keep-outputs' or `keep-derivations' are true
       (the garbage collector will recurse into deleting the outputs
       or derivers, respectively).  So disable them. */
    if (options.action == GCOptions::gcDeleteSpecific && options.ignoreLiveness) {
        state.gcKeepOutputs = false;
        state.gcKeepDerivations = false;
    }

    state.shouldDelete = options.action == GCOptions::gcDeleteDead || options.action == GCOptions::gcDeleteSpecific;

    if (state.shouldDelete)
        deletePath(reservedPath);

    /* Acquire the global GC root.  This prevents
       a) New roots from being added.
       b) Processes from creating new temporary root files. */
    AutoCloseFD fdGCLock = openGCLock(ltWrite);

    /* Find the roots.  Since we've grabbed the GC lock, the set of
       permanent roots cannot increase now. */
    printInfo("finding garbage collector roots...");
    Roots rootMap;
    if (!options.ignoreLiveness)
        rootMap = findRoots(true);

    for (auto & i : rootMap) state.roots.insert(i.first);

    /* Read the temporary roots.  This acquires read locks on all
       per-process temporary root files.  So after this point no paths
       can be added to the set of temporary roots. */
    FDs fds;
    Roots tempRoots;
    findTempRoots(fds, tempRoots, true);
    for (auto & root : tempRoots) {
        state.tempRoots.insert(root.first);
        state.roots.insert(root.first);
    }

    /* After this point the set of roots or temporary roots cannot
       increase, since we hold locks on everything.  So everything
       that is not reachable from `roots' is garbage. */

    if (state.shouldDelete) {
        if (pathExists(trashDir)) deleteGarbage(state, trashDir);
        try {
            createDirs(trashDir);
        } catch (SysError & e) {
            if (e.errNo == ENOSPC) {
                printInfo("note: can't create trash directory: %s", e.msg());
                state.moveToTrash = false;
            }
        }
    }

    /* Now either delete all garbage paths, or just the specified
       paths (for gcDeleteSpecific). */

    if (options.action == GCOptions::gcDeleteSpecific) {

        for (auto & i : options.pathsToDelete) {
            tryToDelete(state, printStorePath(i));
            if (state.dead.find(i) == state.dead.end())
                throw Error(
                    "cannot delete path '%1%' since it is still alive. "
                    "To find out why use: "
                    "nix-store --query --roots",
                    printStorePath(i));
        }

    } else if (options.maxFreed > 0) {

        if (state.shouldDelete)
            printInfo("deleting garbage...");
        else
            printInfo("determining live/dead paths...");

        try {

            AutoCloseDir dir(opendir(realStoreDir.get().c_str()));
            if (!dir) throw SysError("opening directory '%1%'", realStoreDir);

            /* Read the store and immediately delete all paths that
               aren't valid.  When using --max-freed etc., deleting
               invalid paths is preferred over deleting unreachable
               paths, since unreachable paths could become reachable
               again.  We don't use readDirectory() here so that GCing
               can start faster. */
            Paths entries;
            struct dirent * dirent;
            while (errno = 0, dirent = readdir(dir.get())) {
                checkInterrupt();
                string name = dirent->d_name;
                if (name == "." || name == "..") continue;
                Path path = storeDir + "/" + name;
                auto storePath = maybeParseStorePath(path);
                if (storePath && isValidPath(*storePath))
                    entries.push_back(path);
                else
                    tryToDelete(state, path);
            }

            dir.reset();

            /* Now delete the unreachable valid paths.  Randomise the
               order in which we delete entries to make the collector
               less biased towards deleting paths that come
               alphabetically first (e.g. /nix/store/000...).  This
               matters when using --max-freed etc. */
            vector<Path> entries_(entries.begin(), entries.end());
            std::mt19937 gen(1);
            std::shuffle(entries_.begin(), entries_.end(), gen);

            for (auto & i : entries_)
                tryToDelete(state, i);

        } catch (GCLimitReached & e) {
        }
    }

    if (state.options.action == GCOptions::gcReturnLive) {
        for (auto & i : state.alive)
            state.results.paths.insert(printStorePath(i));
        return;
    }

    if (state.options.action == GCOptions::gcReturnDead) {
        for (auto & i : state.dead)
            state.results.paths.insert(printStorePath(i));
        return;
    }

    /* Allow other processes to add to the store from here on. */
    fdGCLock = -1;
    fds.clear();

    /* Delete the trash directory. */
    printInfo(format("deleting '%1%'") % trashDir);
    deleteGarbage(state, trashDir);

    /* Clean up the links directory. */
    if (options.action == GCOptions::gcDeleteDead || options.action == GCOptions::gcDeleteSpecific) {
        printInfo("deleting unused links...");
        removeUnusedLinks(state);
    }

    /* While we're at it, vacuum the database. */
    //if (options.action == GCOptions::gcDeleteDead) vacuumDB();
}


void LocalStore::autoGC(bool sync)
{
    static auto fakeFreeSpaceFile = getEnv("_NIX_TEST_FREE_SPACE_FILE");

    auto getAvail = [this]() -> uint64_t {
        if (fakeFreeSpaceFile)
            return std::stoll(readFile(*fakeFreeSpaceFile));

        struct statvfs st;
        if (statvfs(realStoreDir.get().c_str(), &st))
            throw SysError("getting filesystem info about '%s'", realStoreDir);

        return (uint64_t) st.f_bavail * st.f_frsize;
    };

    std::shared_future<void> future;

    {
        auto state(_state.lock());

        if (state->gcRunning) {
            future = state->gcFuture;
            debug("waiting for auto-GC to finish");
            goto sync;
        }

        auto now = std::chrono::steady_clock::now();

        if (now < state->lastGCCheck + std::chrono::seconds(settings.minFreeCheckInterval)) return;

        auto avail = getAvail();

        state->lastGCCheck = now;

        if (avail >= settings.minFree || avail >= settings.maxFree) return;

        if (avail > state->availAfterGC * 0.97) return;

        state->gcRunning = true;

        std::promise<void> promise;
        future = state->gcFuture = promise.get_future().share();

        std::thread([promise{std::move(promise)}, this, avail, getAvail]() mutable {

            try {

                /* Wake up any threads waiting for the auto-GC to finish. */
                Finally wakeup([&]() {
                    auto state(_state.lock());
                    state->gcRunning = false;
                    state->lastGCCheck = std::chrono::steady_clock::now();
                    promise.set_value();
                });

                GCOptions options;
                options.maxFreed = settings.maxFree - avail;

                printInfo("running auto-GC to free %d bytes", options.maxFreed);

                GCResults results;

                collectGarbage(options, results);

                _state.lock()->availAfterGC = getAvail();

            } catch (...) {
                // FIXME: we could propagate the exception to the
                // future, but we don't really care.
                ignoreException();
            }

        }).detach();
    }

 sync:
    // Wait for the future outside of the state lock.
    if (sync) future.get();
}


}
