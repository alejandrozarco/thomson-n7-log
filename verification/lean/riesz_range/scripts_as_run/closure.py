# closure.py ROOTDIR... -- MOD : import closure (non-Mathlib) of MOD; prints module count, olean bytes per prefix.
import sys, os, re, collections
args = sys.argv[1:]; k = args.index("--"); roots = args[:k]; mods = args[k+1:]
srcroots = [r.split(":")[0] for r in roots]; olroots = [r.split(":")[1] for r in roots]
def find(m, rs):
    for r in rs:
        p = os.path.join(r, m)
        if os.path.exists(p): return p
    return None
seen = set(); st = list(mods)
while st:
    m = st.pop()
    if m in seen or m.split(".")[0] in ("Mathlib","Init","Std","Lean","Batteries","Aesop","Qq","Plausible","ProofWidgets","LeanSearchClient","ImportGraph"): continue
    seen.add(m)
    f = find(m.replace(".","/") + ".lean", srcroots)
    if not f: print("NOSRC", m, file=sys.stderr); continue
    for line in open(f):
        mm = re.match(r"^\s*import\s+(\S+)", line)
        if mm: st.append(mm.group(1))
sz = collections.Counter(); n = collections.Counter()
for m in seen:
    o = find(m.replace(".","/") + ".olean", olroots); p = m.split(".")[0]
    n[p] += 1; sz[p] += os.path.getsize(o) if o else 0
    if not o: print("NOOLEAN", m, file=sys.stderr)
for p in sz: print(p, n[p], "modules", round(sz[p]/2**20), "MiB olean")
if "-v" in os.environ.get("CL",""):
    for m in sorted(seen): print("M", m)
