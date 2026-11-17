"""Run one heavy Mac job at a time (flock(1) is not installed on this Mac).
usage: python3 heavy_lock.py <cmd...>
Waits for the shared lock .mac_heavy.lock and for the 1-minute load average to drop below 10, then runs <cmd> with
all thread variables set to 1 under `nice -n 19 taskpolicy -b`; the lock is held until <cmd> exits."""
import fcntl, os, subprocess, sys, time
# HEAVY_SLOT=B selects the second Mac slot (only when the coordinator has granted it); default slot A.
LOCK = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                    ".mac_heavy_B.lock" if os.environ.get("HEAVY_SLOT") == "B" else ".mac_heavy.lock")
with open(LOCK, "a") as f:
    fcntl.flock(f, fcntl.LOCK_EX)
    while os.getloadavg()[0] >= 10:
        time.sleep(30)
    env = dict(os.environ, **{k: "1" for k in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS",
                                               "MKL_NUM_THREADS", "THREADS")})
    sys.exit(subprocess.call(["nice", "-n", "19", "taskpolicy", "-b"] + sys.argv[1:], env=env))
