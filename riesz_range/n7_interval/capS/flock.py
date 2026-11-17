"""Minimal flock(1) replacement (macOS has none): flock.py LOCKFILE cmd args...
Takes an exclusive flock(2) on LOCKFILE (blocking; interoperates with util-linux flock / fcntl.flock users),
runs cmd, releases on exit, returns cmd's exit status."""
import fcntl, subprocess, sys
fh = open(sys.argv[1], "a")
fcntl.flock(fh, fcntl.LOCK_EX)
sys.exit(subprocess.call(sys.argv[2:]))
