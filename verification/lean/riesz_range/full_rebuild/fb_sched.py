#!/usr/bin/env python3
"""fb_sched.py -- phase B of fb_run.sh: build the RieszN7 modules of build_order.txt with the recorded recipe
`LEAN_NUM_THREADS=1 lean -j1 -DElab.async=false -o <M>.olean -i <M>.ilean <M>.lean` (run in riesz_range/lean, relative
source path), dependency-aware, in two slots (AI-written 2026-11-20).

Slot 1 holds <work>/lean.lock (shared with other projects), slot 2 holds lean2.lock (RieszN7 only).
A module starts only when its RieszN7 imports are built, the load average is < 8, and MemAvailable >= expected peak +
3 GiB (expected = max peak RSS of the module in the checked build's build.tsv, else 9.5 GiB). Modules expected above
5 GiB use slot 1 only. Watchdog: MemAvailable < 3 GiB -> stop the most recently started job's own process group
(TERM, then KILL) and requeue it (at most 3 attempts per module). Each job: nice 19, ionice idle, own session.
Stops starting new modules at the first real failure; exit 0 only if every module built with rc 0.
Resumable: a module with an rc-0 line in build.tsv and an existing olean is skipped.
"""
import fcntl, os, re, signal, subprocess, sys, time

R = "<fresh>"
W = R + "/repo/riesz_range/lean"
B = W + "/.lake/build/lib/lean"
LOCKS = ["<work>/lean.lock", "<work>/lean2.lock"]
CHECKED_TSV = "<build>/build.tsv"
LEAN = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean")
TSV = R + "/build.tsv"
ML = R + "/mlogs"
GiB = 1 << 20  # in kB
HEAVY = 5 * GiB
os.makedirs(ML, exist_ok=True)


def log(msg):
    print(time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "sched", msg, flush=True)


def memav():
    for line in open("/proc/meminfo"):
        if line.startswith("MemAvailable:"):
            return int(line.split()[1])


def load1():
    return float(open("/proc/loadavg").read().split()[0])


order = [m.strip() for m in open(W + "/build_order.txt") if m.strip().startswith("RieszN7.")]
idx = {m: i for i, m in enumerate(order)}
deps = {}
imp = re.compile(r"^\s*import\s+(.+)$")
for m in order:
    ds = set()
    for line in open(W + "/" + m.replace(".", "/") + ".lean", encoding="utf-8"):
        mm = imp.match(line)
        if mm:
            for t in mm.group(1).split():
                if t in idx:
                    ds.add(t)
    deps[m] = ds

expect = {}
for line in open(CHECKED_TSV):
    f = line.rstrip("\n").split("\t")
    if len(f) >= 4 and f[1] == "0" and f[3].isdigit():
        expect[f[0]] = max(expect.get(f[0], 0), int(f[3]))

done = set()
if os.path.exists(TSV):
    for line in open(TSV):
        f = line.split("\t")
        if len(f) > 1 and f[1] == "0" and os.path.exists(B + "/" + f[0].replace(".", "/") + ".olean"):
            done.add(f[0])
log(f"{len(order)} modules, {len(done)} already built, {sum(1 for m in order if expect.get(m, 0) > HEAVY)} expected > 5 GiB")

env = dict(os.environ, LEAN_NUM_THREADS="1", TMPDIR=R + "/tmp")
env["LEAN_PATH"] = ":".join([B] + [p + "/.lake/build/lib/lean" for p in sorted(
    os.path.join(W, ".lake/packages", d) for d in os.listdir(W + "/.lake/packages"))])

running = {}   # slot -> (module, Popen, start, lockfd)
attempts = {}
failed = None
pending = [m for m in order if m not in done]


def try_lock(slot):
    fd = os.open(LOCKS[slot], os.O_RDWR | os.O_CREAT, 0o644)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        return fd
    except OSError:
        os.close(fd)
        return None


def start(slot, m, fd):
    f = m.replace(".", "/")
    os.makedirs(os.path.dirname(B + "/" + f), exist_ok=True)
    cmd = ["nice", "-n", "19", "ionice", "-c3", "/usr/bin/time", "-v", "-o", f"{ML}/{m}.time",
           LEAN, "-j1", "-DElab.async=false", "-o", f"{B}/{f}.olean", "-i", f"{B}/{f}.ilean", f + ".lean"]
    out = open(f"{ML}/{m}.log", "w")
    p = subprocess.Popen(cmd, cwd=W, env=env, stdout=out, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                         start_new_session=True, pass_fds=())
    out.close()
    running[slot] = (m, p, time.time(), fd)
    attempts[m] = attempts.get(m, 0) + 1


def stop_group(p):
    try:
        os.killpg(p.pid, signal.SIGTERM)
        time.sleep(5)
        os.killpg(p.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def maxrss(m):
    try:
        for line in open(f"{ML}/{m}.time"):
            if "Maximum resident" in line:
                return line.split(":")[1].strip()
    except OSError:
        pass
    return "-"


while pending or running:
    # reap
    for slot in list(running):
        m, p, t0, fd = running[slot]
        rc = p.poll()
        if rc is None:
            continue
        os.close(fd)
        del running[slot]
        wall = int(time.time() - t0)
        with open(TSV, "a") as t:
            t.write(f"{m}\t{rc}\t{wall}\t{maxrss(m)}\t{slot + 1}\t{time.strftime('%Y-%m-%dT%H:%M:%S%z')}\n")
        if rc == 0:
            done.add(m)
            if len(done) % 100 == 0:
                log(f"{len(done)}/{len(order)} built")
        elif rc in (-signal.SIGTERM, -signal.SIGKILL, 137, 143) and getattr(p, "_fb_watchdog", False) and attempts[m] < 3:
            log(f"requeue {m} after watchdog stop (attempt {attempts[m]})")
            pending.insert(0, m)
            pending.sort(key=idx.get)
        else:
            log(f"FAILED {m} rc={rc}; no new modules will be started")
            failed = failed or m
    # watchdog
    if running and memav() < 3 * GiB:
        slot = max(running, key=lambda s: running[s][2])
        m, p, t0, fd = running[slot]
        log(f"watchdog: MemAvailable {memav()} kB < 3 GiB, stopping {m} (slot {slot + 1}, pgid {p.pid})")
        p._fb_watchdog = True
        stop_group(p)
    # start
    if not failed and pending and load1() < 8:
        ready = [m for m in pending if deps[m] <= done][:50]
        for m in ready:
            free = [s for s in (0, 1) if s not in running]
            if not free:
                break
            e = expect.get(m, int(9.5 * GiB))
            if memav() < e + 3 * GiB:
                break
            slots = [s for s in free if s == 0 or e <= HEAVY]
            fd = None
            for s in slots:
                fd = try_lock(s)
                if fd is not None:
                    break
            if fd is None:
                continue
            pending.remove(m)
            start(s, m, fd)
    if failed and not running:
        break
    time.sleep(2)

ok = not failed and len(done) == len(order)
log(f"end: built {len(done)}/{len(order)}, failed={failed}")
sys.exit(0 if ok else 1)
