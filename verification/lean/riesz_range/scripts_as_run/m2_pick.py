"""m2_pick.py EXPORT -- Fable review M2 (2026-11-12): choose a tamper literal inside this project's certificate data.
lean4export 3.1 ndjson emits each expression once, just before the first declaration that uses it, so a literal's
owning declaration is taken to be the first declaration line after it. Candidates: Nat literals of >= 15 digits that
occur exactly once in the export and whose owning declaration is named RieszN7.Cap.* or RieszN7.Cells.*; preference
for an extension piece (s outside [1/2, 3/2]), so the control is specific to the Full theorem. Prints
'<literal> <new> <declaration> <line>'."""
import hashlib, json, re, sys
EXT = ("P1o3_", "P3o8_", "P5o12_", "P11o24_", "P3o2_19o12", "P19o12_", "P5o3_", "N1o3", "N3o8", "N5o12", "N11o24", "N19o12", "N5o3", "N7o4")
names = {0: ""}
cnt = {}
pending = []          # (literal, line) since the last declaration
cands = []            # (literal, line, declname)
rx_nat = re.compile(r'"natVal":"(\d+)"')
def full(i):
    parts = []
    while i:
        p, s = names[i]; parts.append(s); i = p
    return ".".join(reversed(parts))
for ln, line in enumerate(open(sys.argv[1]), 1):
    if line.startswith('{"in":'):
        o = json.loads(line); n = o["in"]
        if "str" in o: names[n] = (o["str"]["pre"], o["str"]["str"])
        elif "num" in o: names[n] = (o["num"]["pre"], str(o["num"]["i"]))
        continue
    m = rx_nat.search(line)
    if m:
        v = m.group(1)
        if len(v) >= 15:
            h = hashlib.blake2b(v.encode(), digest_size=12).digest(); cnt[h] = cnt.get(h, 0) + 1
            if len(pending) < 50: pending.append((v, ln))
        continue
    if line.startswith('{"def"') or line.startswith('{"thm"') or line.startswith('{"opaque"') or line.startswith('{"axiom"'):
        if pending:
            o = json.loads(line); body = next(iter(o.values())); dn = full(body["name"])
            if dn.startswith("RieszN7.Cap.") or dn.startswith("RieszN7.Cells."):
                cands += [(v, l, dn) for v, l in pending]
                if len(cands) > 20000: cands = cands[-20000:]
        pending = []
    elif line.startswith('{"inductive"') or line.startswith('{"quot"'):
        pending = []
def uniq(v): return cnt[hashlib.blake2b(v.encode(), digest_size=12).digest()] == 1
good = [c for c in cands if uniq(c[0])]
ext = [c for c in good if any(t in c[2] for t in EXT)]
pick = (ext or good)[-1]
new = int(pick[0]) + 1
while hashlib.blake2b(str(new).encode(), digest_size=12).digest() in cnt: new += 1
print(pick[0], new, pick[2], pick[1])
