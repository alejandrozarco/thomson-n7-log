#!/usr/bin/env python3
"""Split upstream ThomsonN7/Solution.lean into ThomsonGen/*.lean modules (M0).

Inputs : upstream Solution.lean (read only), depdump.tsv (from DepDump.lean on the upstream olean).
Outputs: ../<Module>.lean for every chunk, modules.tsv (order, lines, bytes, imports), pruned.tsv.

* Split points are line numbers or declaration names (the declaration range includes its docstring).
* The namespace/section stack and the `open`/`variable` commands in force at a split point are
  re-created at the top of the module; scopes still open at its end are closed.
* Dead declarations are removed: those not reachable from the roots through the term-level
  dependency graph *and* through textual references (identifier fragments), so `simp [foo]` or
  `nlinarith [foo]` hints keep `foo`.  Declarations with attributes and instances are always kept.
* Imports: a module imports the modules of all earlier declarations it references (term graph plus
  textual references), plus a provider for every `open`ed ThomsonN7 namespace; transitively reduced.
"""
import re, sys, os, json, hashlib, collections

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.dirname(HERE)                          # lean/ThomsonGen
SRC = os.environ['UPSTREAM_SOLUTION']                 # set by ../../regen.sh
DUMP = os.path.join(HERE, 'depdump.tsv')
PRE = '_private.ThomsonN7.Solution.0.'

raw = open(SRC, 'rb').read()
SHA = hashlib.sha256(raw).hexdigest()
L = raw.decode('utf-8').split('\n')
if L and L[-1] == '':
    L = L[:-1]
N = len(L)

# ---------------------------------------------------------------- comment stripping
def strip_comments(lines):
    out, depth = [], 0
    for ln in lines:
        s, i = '', 0
        while i < len(ln):
            if depth > 0:
                if ln.startswith('/-', i): depth += 1; i += 2
                elif ln.startswith('-/', i): depth -= 1; i += 2
                else: i += 1
            else:
                if ln.startswith('/-', i): depth += 1; i += 2
                elif ln.startswith('--', i): break
                elif ln[i] == '"':
                    j = i + 1
                    while j < len(ln) and ln[j] != '"':
                        j += 2 if ln[j] == '\\' else 1
                    s += ln[i:j + 1]; i = j + 1
                else:
                    s += ln[i]; i += 1
        out.append(s)
    return out
C = strip_comments(L)

# ---------------------------------------------------------------- scope tracking
# frame = dict(kind, name, header, cmds)
def scan_states():
    """states[n] = frames in force at the *start* of line n (1-based); states[N+1] = final."""
    frames = [dict(kind='file', name='', header=None, cmds=[])]
    states = [None] * (N + 2)
    import copy
    for n in range(1, N + 1):
        states[n] = copy.deepcopy(frames)
        c = C[n - 1]; t = c.strip()
        m = re.match(r'^(noncomputable\s+)?section\b\s*(\S*)\s*$', t)
        if m:
            frames.append(dict(kind='section', name=m.group(2), header=t, cmds=[])); continue
        m = re.match(r'^namespace\s+(\S+)\s*$', t)
        if m:
            frames.append(dict(kind='namespace', name=m.group(1), header=t, cmds=[])); continue
        m = re.match(r'^end\b\s*(\S*)\s*$', t)
        if m and c.startswith('end'):
            f = frames.pop()
            assert f['name'] == m.group(1), (n, f, t)
            continue
        if re.match(r'^(open|variable|universe)\b', t) and not re.search(r'\bin\s*$', t):
            frames[-1]['cmds'].append(t)
    states[N + 1] = frames
    assert len(frames) == 1, frames
    return states
STATES = scan_states()

def cur_ns(frames):
    ns = []
    for f in frames:
        if f['kind'] == 'namespace':
            ns += f['name'].split('.')
    return ns

# ---------------------------------------------------------------- dependency data
rows = [l.split('\t') for l in open(DUMP, encoding='utf-8').read().split('\n') if l]
rng, deps = {}, {}
for r in rows:
    n, a, b = r[0], int(r[2]), int(r[3])
    deps[n] = r[4].split(' ') if len(r) > 4 and r[4] else []
    if a > 0:
        rng[n] = (a, b)
def owner(n):
    m = n[len(PRE):] if n.startswith(PRE) else n
    ps = m.split('.')
    while ps:
        c = '.'.join(ps)
        if c in rng: return c
        ps = ps[:-1]
    return None
G = collections.defaultdict(set)
for n, d in deps.items():
    o = owner(n)
    for x in d:
        ox = owner(x)
        if o and ox and ox != o:
            G[o].add(ox)
DECLS = sorted(set(rng), key=lambda n: rng[n][0])
by_frag = collections.defaultdict(set)
for n in DECLS:
    ps = n.split('.')
    for k in range(1, len(ps) + 1):
        by_frag['.'.join(ps[-k:])].add(n)
IDRE = re.compile(r"[^\W\d][\w'!?₀-₉]*(?:\.[^\W\d][\w'!?₀-₉]*)*")
_tr = {}
def textrefs(n):
    if n in _tr: return _tr[n]
    a, b = rng[n]
    out = set()
    for tok in set(IDRE.findall('\n'.join(C[a - 1:b]))):
        ps = tok.split('.')
        for i in range(len(ps)):
            for j in range(i + 1, len(ps) + 1):
                out |= by_frag.get('.'.join(ps[i:j]), set())
    out.discard(n)
    _tr[n] = out
    return out

def _shared(a, b):
    pa, pb = a.split('.')[:-1], b.split('.')[:-1]
    k = 0
    while k < min(len(pa), len(pb)) and pa[k] == pb[k]: k += 1
    return k
_trs = {}
def textrefs_scoped(n):
    """Textual references used for *imports*: whole identifier tokens resolved like Lean does, i.e.
    among all declarations whose name ends with the token keep those sharing the longest namespace
    prefix with `n` (the innermost namespace wins; `n` itself counts).  Short tokens without `_`
    or `.` are local variables in practice and are ignored."""
    if n in _trs: return _trs[n]
    a, b = rng[n]
    out = set()
    for tok in set(IDRE.findall('\n'.join(C[a - 1:b]))):
        if len(tok) < 4 and '_' not in tok and '.' not in tok:
            continue
        cands = by_frag.get(tok, ())
        if not cands: continue
        best = max(_shared(n, x) for x in cands)
        out |= {x for x in cands if _shared(n, x) == best and x != n and rng[x][0] < a}
    _trs[n] = out
    return out

def closure(roots):
    live, st = set(), [r for r in roots]
    while st:
        x = st.pop()
        if x in live: continue
        live.add(x)
        st.extend((G[x] | textrefs(x)) - live)
    return live

ROOTS = ['ThomsonN7.thomson_seven', 'ThomsonN7.thomson_seven_unique']
# kernel-free upstream lemmas reused by the generic glue (ThomsonGen/Generic/*.lean)
ROOTS += [l.strip() for l in open(os.path.join(HERE, 'gen_roots.txt'), encoding='utf-8')
          if l.strip() and not l.startswith('#')]
for x in ROOTS:
    assert x in rng, x
FORCE = set()
for n in DECLS:
    a, b = rng[n]
    head = ' '.join(L[a - 1:b])[:4000]
    if '@[' in head or re.search(r'^\s*instance\b', '\n'.join(C[a - 1:b]), re.M):
        FORCE.add(n)
PRE_END = 310
LIVE = closure(set(ROOTS) | FORCE | {n for n in DECLS if rng[n][0] <= PRE_END})
DEAD = [n for n in DECLS if n not in LIVE]

live_lines = set()
for n in LIVE:
    a, b = rng[n]
    live_lines.update(range(a, b + 1))
DEAD = [n for n in DEAD if not (set(range(rng[n][0], rng[n][1] + 1)) & live_lines)]
deleted = set()
for n in DEAD:
    a, b = rng[n]
    for k in range(a, b + 1): deleted.add(k)
    k = a - 1                                   # a dangling `open ... in` belongs to the deleted decl
    while k >= 1 and re.search(r'\bin\s*$', C[k - 1].strip()) and C[k - 1].strip().startswith(('open', 'set_option')):
        deleted.add(k); k -= 1

# namespaces that exist before / after pruning
def ns_set(names):
    s = set()
    for n in names:
        ps = n.split('.')
        for k in range(1, len(ps)):
            s.add('.'.join(ps[:k]))
    return s
NS_ALL, NS_LIVE = ns_set(DECLS), ns_set(LIVE)
def resolve_ns(tok, frames):
    """ThomsonN7-internal namespace named by `tok` in the context `frames`, or None (Mathlib etc.)."""
    ns = cur_ns(frames)
    if tok.startswith('_root_.'): tok = tok[7:]; ns = []
    for k in range(len(ns), -1, -1):
        cand = '.'.join(ns[:k] + [tok])
        if cand in NS_ALL:
            return cand
    return None
def fix_open(line, frames):
    """Drop tokens of an `open` naming a ThomsonN7 namespace emptied by pruning."""
    t = line.strip()
    m = re.match(r'^open\s+(scoped\s+)?(.*?)(\s+in)?$', t)
    if not m: return line, []
    toks = m.group(2).split()
    keep, used = [], []
    for tok in toks:
        r = resolve_ns(tok, frames)
        if r is not None and r not in NS_LIVE:
            continue
        keep.append(tok)
        if r is not None: used.append(r)
    if not keep:
        return None, []
    ind = line[:len(line) - len(line.lstrip())]
    return ind + 'open ' + (m.group(1) or '') + ' '.join(keep) + (m.group(3) or ''), used

# ---------------------------------------------------------------- chunks
def D(name):
    return ('decl', 'ThomsonN7.' + name)
CHUNKS = [
    (1, 'Preamble'),
    (311, 'Base'),
    (514, 'ThreePoint'),
    (1584, 'Kron'),
    (2067, 'Cert1'),
    (2229, 'Cert3'),
    (2820, 'M2'),
    (3336, 'M3'),
    (3989, 'P3ext'),
    (4100, 'P1'),
    (4703, 'Gauge'),
    (4882, 'RegB'),
    (5195, 'GV'),
    (5654, 'TwoRegime'),
    (6599, 'Loc1'),
    (6733, 'QCore1'),
    (8263, 'Q2'),
    (8402, 'QCore2'),
    (8668, 'Loc2'),
    (9123, 'CutOneD'),
    (9586, 'Case1Data'),
    (10272, 'Case1Stat'),
    (D('Case1.c1_stat_H'), 'Case1ChkF'),
    (D('Case1.c1_stat_S0'), 'Case1ChkS03'),
    (D('Case1.c1_stat_S4'), 'Case1ChkS47'),
    (D('Case1.c1_K'), 'Case1'),
    (10550, 'Case2Red'),
    (10588, 'Typed'),
    (11300, 'T4'),
    (12000, 'Glue'),
    (12905, 'Coerce'),
    (13760, 'CertF'),
    (14043, 'CertT'),
    (15100, 'SlabOneD'),
    (15583, 'Bridge'),
    (15887, 'Cap/Data'),
    (D('Cert.tc_cap_meta'), 'Cap/ChkMeta'),
    (D('Cert.tc_cap_A'), 'Cap/ChkA'),
    (D('Cert.tc_cap_B'), 'Cap/ChkB'),
    (D('Cert.tc_cap_G'), 'Cap/ChkG'),
    (16092, 'Cap/Contact'),
    (D('Final.capA_check'), 'Cap/ContactChk'),
    (16164, 'Cap/Spec'),
]
for tag, a in [('S9998', 16199), ('S9896', 16528), ('S9694', 16857), ('S9493', 17186), ('S9390', 17515)]:
    cell = {'S9998': 's99_98', 'S9896': 's98_96', 'S9694': 's96_94', 'S9493': 's94_93', 'S9390': 's93_90'}[tag]
    if tag == 'S9998':      # fine-grained (calibration): one module per boolean check
        CHUNKS += [
            (a, f'{tag}/Data'),
            (D(f'Cert.tc_{cell}_meta'), f'{tag}/ChkMeta'),
            (D(f'Cert.tc_{cell}_A'), f'{tag}/ChkA'),
            (D(f'Cert.tc_{cell}_B'), f'{tag}/ChkB'),
            (D(f'Cert.tc_{cell}_G'), f'{tag}/ChkG'),
            ('asm', f'Asm_{cell}_1d', f'{tag}/OneDSpec'),
        ]
    else:                   # coarse: fewer, larger modules
        CHUNKS += [
            (a, f'{tag}/DataChk'),
            ('asm', f'Asm_{cell}_1d', f'{tag}/OneDSpec'),
        ]
CHUNKS += [(17844, 'Final'), (17880, 'Main')]

def start_of(c):
    k = c[0]
    if isinstance(k, int): return k
    if isinstance(k, tuple): return rng[k[1]][0]
    if k == 'asm':
        for i, l in enumerate(L, 1):
            if l == 'section ' + c[1]: return i
        raise KeyError(c)
CH = [(start_of(c), c[-1]) for c in CHUNKS]
CH.sort()
starts = [s for s, _ in CH]
assert len(set(starts)) == len(starts)
SPANS = [(CH[i][0], (CH[i + 1][0] - 1) if i + 1 < len(CH) else N, CH[i][1]) for i in range(len(CH))]

def module_of_line(k):
    for a, b, m in SPANS:
        if a <= k <= b: return m
modname = lambda m: 'ThomsonGen.' + m.replace('/', '.')

# ---------------------------------------------------------------- emit
decl_mod = {n: module_of_line(rng[n][0]) for n in LIVE}
first_in_ns = {}
for n in sorted(LIVE, key=lambda n: rng[n][0]):
    for ns in ns_set([n]):
        first_in_ns.setdefault(ns, n)

texts, needs = {}, {}
for a, b, m in SPANS:
    need = set()
    for n in LIVE:
        if decl_mod[n] != m: continue
        for x in (G[n] | textrefs_scoped(n)):
            if x in LIVE and rng[x][0] < rng[n][0] and decl_mod[x] != m:
                need.add(decl_mod[x])
    out = []
    if m == 'Preamble':
        body = L[0:b]
        texts[m] = '\n'.join(body) + '\n\nend ThomsonN7\n'
        needs[m] = set()
        continue
    fr = STATES[a]
    pre = []
    for f in fr:
        if f['kind'] != 'file':
            pre.append(f['header'])
        for cmd in f['cmds']:
            fixed, used = fix_open(cmd, fr[:fr.index(f) + 1])
            for u in used:
                if u in first_in_ns and decl_mod[first_in_ns[u]] != m and rng[first_in_ns[u]][0] < a:
                    need.add(decl_mod[first_in_ns[u]])
            if fixed is not None: pre.append(fixed)
    body = []
    for k in range(a, b + 1):
        if k in deleted: continue
        line = L[k - 1]
        if re.match(r'^\s*open\b', C[k - 1]):
            fixed, used = fix_open(line, STATES[k])
            for u in used:
                if u in first_in_ns and decl_mod[first_in_ns[u]] != m and rng[first_in_ns[u]][0] < k:
                    need.add(decl_mod[first_in_ns[u]])
            if fixed is None: continue
            line = fixed
        body.append(line)
    # collapse runs of blank lines left by pruning
    b2 = []
    for line in body:
        if line.strip() == '' and b2 and b2[-1].strip() == '': continue
        b2.append(line)
    post = []
    for f in reversed(STATES[b + 1]):
        if f['kind'] == 'file': continue
        post.append('end' + ((' ' + f['name']) if f['name'] else ''))
    need.add('Preamble')
    need.discard(m)
    needs[m] = need
    doc = (f'/-! Split from upstream `ThomsonN7/Solution.lean` (sha256 {SHA[:16]}…), lines {a}–{b},\n'
           f'    by `ThomsonGen/scripts/split.py` (dead declarations removed).  Regenerate; do not edit. -/')
    texts[m] = '\n'.join([doc, ''] + pre + [''] + b2 + [''] + post) + '\n'

order = [m for _, _, m in SPANS]
idx = {m: i for i, m in enumerate(order)}
# transitive reduction
anc = {}
for m in order:
    s = set()
    for d in needs[m]:
        assert idx[d] < idx[m], (m, d)
        s |= {d} | anc[d]
    anc[m] = s
for m in order:
    direct = set(needs[m])
    for d in list(direct):
        if any(d in anc[e] for e in direct if e != d):
            direct.discard(d)
    needs[m] = direct

os.makedirs(OUT, exist_ok=True)
tsv = ['order\tmodule\tfirst_line\tlast_line\tbytes\tlive_decls\tdead_decls\timports']
for (a, b, m) in SPANS:
    imps = sorted(needs[m], key=lambda d: idx[d])
    head = ''.join(f'import {modname(d)}\n' for d in imps) if m != 'Preamble' else ''
    txt = texts[m] if m == 'Preamble' else head + texts[m]
    p = os.path.join(OUT, m + '.lean')
    os.makedirs(os.path.dirname(p), exist_ok=True)
    open(p, 'w', encoding='utf-8').write(txt)
    nl = sum(1 for n in LIVE if decl_mod[n] == m)
    nd = sum(1 for n in DEAD if a <= rng[n][0] <= b)
    tsv.append(f'{idx[m]}\t{modname(m)}\t{a}\t{b}\t{len(txt.encode())}\t{nl}\t{nd}\t{" ".join(modname(d) for d in imps)}')
open(os.path.join(HERE, 'modules.tsv'), 'w').write('\n'.join(tsv) + '\n')
open(os.path.join(HERE, 'pruned.tsv'), 'w').write(
    '\n'.join(f'{n}\t{rng[n][0]}\t{rng[n][1]}' for n in DEAD) + '\n')

# ---------------------------------------------------------------- ThomsonGen/Verbatim/*.lean
# Upstream declarations that our own files use unchanged are not stored there: each list
# scripts/verbatim/<M>.txt yields the module ThomsonGen/Verbatim/<M>.lean with the listed declarations
# (docstring included) copied verbatim, in list order, into the namespace and under the imports/opens
# named in the list's header lines (`namespace X`, `import Y`, `open Z`).
VDIR = os.path.join(HERE, 'verbatim')
for fn in sorted(os.listdir(VDIR)) if os.path.isdir(VDIR) else []:
    if not fn.endswith('.txt'): continue
    mod = fn[:-4]
    ns, imps, opens, names = None, [], [], []
    for l in open(os.path.join(VDIR, fn), encoding='utf-8'):
        l = l.strip()
        if not l or l.startswith('#'): continue
        if l.startswith('namespace '): ns = l.split()[1]
        elif l.startswith('import '): imps.append(l)
        elif l.startswith('open '): opens.append(l)
        else: names.append(l)
    assert ns, fn
    vtxt = imps + ['',
            f'/-! Upstream declarations used unchanged by this package, copied verbatim from upstream',
            f'    `ThomsonN7/Solution.lean` (sha256 {SHA[:16]}…) into namespace `{ns}` by',
            f'    `ThomsonGen/scripts/split.py` (list: `scripts/verbatim/{fn}`).  Regenerate; do not edit. -/',
            '', f'namespace {ns}', ''] + opens + ([''] if opens else [])
    for x in names:
        assert x in rng, x
        a, b = rng[x]
        vtxt += L[a - 1:b] + ['']
    vtxt += [f'end {ns}']
    p = os.path.join(OUT, 'Verbatim', mod + '.lean')
    os.makedirs(os.path.dirname(p), exist_ok=True)
    open(p, 'w', encoding='utf-8').write('\n'.join(vtxt) + '\n')

print(f'{len(SPANS)} modules, {len(LIVE)} live / {len(DEAD)} dead declarations, '
      f'{len(deleted)} lines removed')
