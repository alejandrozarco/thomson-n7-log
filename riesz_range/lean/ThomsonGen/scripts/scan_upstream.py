#!/usr/bin/env python3
"""Scan the stored (committed) Lean files of this package for text taken from upstream Solution.lean
(huwngtran/thomson-n7-lean @ 25f2fa5, formal/lean/ThomsonN7/Solution.lean).

Usage:  UPSTREAM_SOLUTION=path/to/Solution.lean python3 ThomsonGen/scripts/scan_upstream.py [files...]
Default files: every stored .lean file (LogN7/**, LogLean/**, gen/** and the ThomsonGen files re-included in .gitignore).
Default UPSTREAM_SOLUTION: the checkout made by ./regen.sh.

Declarations (with docstring and attributes) are compared whitespace-normalised with every upstream
declaration:
  VERBATIM  identical to an upstream declaration (must be regenerated, not stored);
  TRIVIAL   ratio >= 0.8, but a single code line of <= 100 characters (exempt, listed);
  NEAR      difflib ratio >= 0.8 (an adapted version: the file must cite the upstream name and
            "huwngtran/thomson-n7-lean @ 25f2fa5" in a comment);
  LINES     3+ consecutive non-trivial code lines identical to upstream outside the above (same
            attribution requirement, for the upstream declaration containing them);
  COMMENT   a comment/docstring outside the above that equals an upstream comment line (>= 25
            characters) or shares an 8-word run with upstream comments.
PASS iff there is no VERBATIM and every NEAR, LINES and COMMENT item is attributed (a COMMENT item
counts as attributed when the upstream declaration containing that comment is cited).
"""
import os, re, sys, difflib, collections

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))           # the Lake package directory
SRC = os.environ.get('UPSTREAM_SOLUTION', os.path.join(ROOT, '.upstream/formal/lean/ThomsonN7/Solution.lean'))
THRESH = 0.8
RUN = 3
WORDS = 8

KW = r'(theorem|lemma|def|abbrev|instance|structure|class|inductive|example|opaque|axiom|macro_rules|macro|syntax|elab|notation|infixl?|infixr|attribute)'
MODS = r'((private|protected|noncomputable|nonrec|unsafe|partial|scoped|local)\s+)*'
DECL_RE = re.compile(r'^(@\[[^\]]*\]\s*)*' + MODS + KW + r'\b\s*(?P<name>[^\s:({\[]*)')
MARK_RE = re.compile(r'^\s*--\s*@upstream\b')

def norm(s):
    return ' '.join(s.split())

def split_code_comments(lines):
    """Per line: (code part, comment part).  Handles nested /- -/, docstrings and strings."""
    out, depth = [], 0
    for ln in lines:
        code, cmt, i = '', '', 0
        while i < len(ln):
            if depth > 0:
                if ln.startswith('/-', i): depth += 1; i += 2
                elif ln.startswith('-/', i): depth -= 1; i += 2
                else: cmt += ln[i]; i += 1
            elif ln.startswith('/-', i):
                depth += 1; i += 2
                while i < len(ln) and ln[i] in '-!': i += 1
            elif ln.startswith('--', i):
                cmt += ' ' + ln[i + 2:]; break
            elif ln[i] == '"':
                j = i + 1
                while j < len(ln) and ln[j] != '"':
                    j += 2 if ln[j] == '\\' else 1
                code += ln[i:j + 1]; i = j + 1
            else:
                code += ln[i]; i += 1
        out.append((code, cmt))
    return out

def blocks(lines):
    """Top-level declarations: list of (name, first, last) 1-based line ranges, docstring and
    attributes included.  The full name carries the enclosing namespaces."""
    cc = split_code_comments(lines)
    starts, ns = [], []
    pending_doc = None
    for n, ln in enumerate(lines, 1):
        t = ln.rstrip()
        if t.startswith('/--') and pending_doc is None:
            pending_doc = n
        code = cc[n - 1][0]
        m = re.match(r'^namespace\s+(\S+)', code)
        if m: ns.append(m.group(1)); pending_doc = None; continue
        m = re.match(r'^end\s+(\S+)\s*$', code)
        if m and ns and ns[-1] == m.group(1): ns.pop(); pending_doc = None; continue
        m = DECL_RE.match(code) if code[:1] not in (' ', '\t') else None
        if m:
            name = m.group('name') or '?'
            full = '.'.join(ns + [name]) if not name.startswith('_root_') else name[7:]
            first = pending_doc if pending_doc is not None else n
            # attributes on the previous lines
            while first > 1 and lines[first - 2].startswith('@['):
                first -= 1
            starts.append((full, first))
            pending_doc = None
        elif code.strip() and not code.startswith('@['):
            pending_doc = None
    res = []
    for i, (full, a) in enumerate(starts):
        b = (starts[i + 1][1] - 1) if i + 1 < len(starts) else len(lines)
        # trim trailing blank / non-declaration lines (namespace/end/open/section)
        while b > a and (not cc[b - 1][0].strip() or re.match(r'^(end|namespace|section|open|noncomputable section|variable|set_option)\b', lines[b - 1])):
            b -= 1
        res.append((full, a, b))
    return res

def decl_text(lines, a, b):
    return norm('\n'.join(l for l in lines[a - 1:b] if not MARK_RE.match(l)))

TOK = re.compile(r"\w{1,8}|[^\w\s]")     # long words (hex data) count per 8 characters
def shingles(s, k=4):
    t = TOK.findall(s)
    return {tuple(t[i:i + k]) for i in range(max(0, len(t) - k + 1))}

def trivial(code_line):
    s = norm(code_line)
    if len(s) < 16: return True
    if not re.search(r'[A-Za-z_][A-Za-z_0-9]{2,}', s): return True
    return False

def comment_words(text):
    return re.findall(r"[\w'`]+", text.lower())


def load_upstream():
    U = open(SRC, encoding='utf-8').read().split('\n')
    UB = blocks(U)
    ut, line2decl, first = {}, {}, {}
    for name, a, b in UB:
        ut[name] = decl_text(U, a, b)
        first[name] = a
        for k in range(a, b + 1): line2decl[k] = name
    ush = {k: shingles(v) for k, v in ut.items()}
    inv = collections.defaultdict(set)
    for k, sh in ush.items():
        for g in sh: inv[g].add(k)
    exact = collections.defaultdict(list)
    for k, v in ut.items(): exact[v].append(k)
    ucc = split_code_comments(U)
    useq = [(n, norm(c)) for n, (c, _) in enumerate(ucc, 1) if norm(c)]
    utrip = {}
    for i in range(len(useq) - RUN + 1):
        utrip.setdefault(tuple(c for _, c in useq[i:i + RUN]), useq[i][0])
    ucw, uwl, ucl = [], [], {}
    for n, (_, c) in enumerate(ucc, 1):
        ws = comment_words(c)
        ucw += ws; uwl += [n] * len(ws)
        if len(norm(c)) >= 25: ucl.setdefault(norm(c), n)
    ucg = {}
    for i in range(len(ucw) - WORDS + 1):
        ucg.setdefault(tuple(ucw[i:i + WORDS]), uwl[i])
    return dict(U=U, UB=UB, ut=ut, ush=ush, inv=inv, exact=exact, utrip=utrip, ucl=ucl, ucg=ucg,
                line2decl=line2decl, first=first)

def is_trivial_decl(lines, a, b):
    """One code line of at most 100 characters and no docstring (e.g. `theorem t : c.chk = true :=
    by decide +kernel`, or a one-line record of emitted data): no expressive content."""
    code = [l for l in lines[a - 1:b] if l.strip()]
    return len(code) == 1 and len(norm(code[0])) <= 100 and '/-' not in code[0]

BIG = 20000
def best_match(D, t):
    """(similarity, upstream name) of the most similar upstream declaration.  Candidates share at
    least 3 distinctive token 4-grams (occurring in <= 50 upstream declarations).  Similarity is the
    difflib ratio of the token sequences (8-character word pieces, single symbols); for texts over 20000 characters (emitted certificate data)
    it is the Jaccard index of the 4-gram sets, which bounds the copied fraction from above well
    enough at this scale and keeps the scan fast."""
    if t in D['exact']:
        return 1.0, sorted(D['exact'][t], key=D['first'].get)
    sh = shingles(t)
    cnt = collections.Counter()
    for g in sh:
        ks = D['inv'].get(g)
        if ks and len(ks) <= 50:
            for k in ks: cnt[k] += 1
    best, bk = 0.0, None
    for k, c in cnt.items():
        if c < 3: continue
        u, us = D['ut'][k], D['ush'][k]
        if 2 * min(len(u), len(t)) / (len(u) + len(t)) < THRESH: continue
        jac = len(sh & us) / max(1, len(sh | us))
        if len(t) > BIG or len(u) > BIG:
            r = jac
        else:
            if jac < 0.3: continue
            sm = difflib.SequenceMatcher(None, TOK.findall(t), TOK.findall(u), autojunk=False)
            if sm.real_quick_ratio() < THRESH or sm.quick_ratio() < THRESH: continue
            r = sm.ratio()
        if r > best + 1e-12: best, bk = r, [k]
        elif abs(r - best) <= 1e-12 and bk: bk.append(k)
    # ties (e.g. the same helper in two upstream namespaces): all of them, in upstream order
    return best, sorted(bk, key=D['first'].get) if bk else None

def attributed(text, uname):
    """`uname` (upstream full name) is cited in a comment of the file, together with the pinned source."""
    short = uname[len('ThomsonN7.'):] if uname.startswith('ThomsonN7.') else uname
    return ATTR in text and re.search(r'(?<![\w.])' + re.escape(short) + r'(?![\w\'])', text) is not None

# upstream statement definitions: never exempt as trivial (they come from the regenerated Preamble)
STATEMENT = {'ThomsonN7.R3', 'ThomsonN7.SphereConfig', 'ThomsonN7.cyl', 'ThomsonN7.pentBipyramid'}
ATTR = 'huwngtran/thomson-n7-lean @ 25f2fa5'

def scan_file(D, f, report):
    L = open(os.path.join(ROOT, f), encoding='utf-8').read().split('\n')
    cc = split_code_comments(L)
    cmt_text = '\n'.join(c for _, c in cc)
    verbatim = near = unattr = 0
    covered = set()                                   # lines inside matched declarations
    decl_of_line = {}
    for name, a, b in blocks(L):
        for k in range(a, b + 1): decl_of_line[k] = (name, a, b)
        t = decl_text(L, a, b)
        if not t: continue
        r, ks = best_match(D, t)
        if ks:
            cited = [x for x in ks if attributed(cmt_text, x)]
            k = (cited or ks)[0]
        if r >= THRESH and is_trivial_decl(L, a, b) and not set(ks) & STATEMENT:
            report.append(f'TRIVIAL   {f}:{a}  {name} ~ upstream {k}  ratio {r:.3f} (one short line; exempt)')
            covered.update(range(a, b + 1))
        elif r >= 1.0:
            verbatim += 1
            report.append(f'VERBATIM  {f}:{a}-{b}  {name} = upstream {k}')
            covered.update(range(a, b + 1))
        elif r >= THRESH:
            near += 1
            ok = attributed(cmt_text, k)
            unattr += not ok
            report.append(f'NEAR      {f}:{a}-{b}  {name} ~ upstream {k}  ratio {r:.3f}  '
                          + ('attributed' if ok else 'NOT ATTRIBUTED'))
            covered.update(range(a, b + 1))
    # runs of RUN+ identical non-trivial code lines outside matched declarations
    seq = [(n, norm(c)) for n, (c, _) in enumerate(cc, 1) if norm(c)]
    i = 0
    while i <= len(seq) - RUN:
        w = tuple(c for _, c in seq[i:i + RUN])
        if all(not trivial(c) for c in w) and w in D['utrip']:
            j = i + RUN
            while j < len(seq) and not trivial(seq[j][1]) and tuple(c for _, c in seq[j - RUN + 1:j + 1]) in D['utrip']:
                j += 1
            lines_ = range(seq[i][0], seq[j - 1][0] + 1)
            if not set(lines_) <= covered:
                k = D['line2decl'].get(D['utrip'][w], '?')
                ok = attributed(cmt_text, k)
                unattr += not ok
                near += 1
                d = decl_of_line.get(seq[i][0], ('(no declaration)',))[0]
                report.append(f'LINES     {f}:{seq[i][0]}-{seq[j - 1][0]}  {j - i} lines of {d} identical to upstream {k}  '
                              + ('attributed' if ok else 'NOT ATTRIBUTED'))
            i = j
        else:
            i += 1
    # comments / docstrings outside matched declarations: attributed iff the upstream declaration
    # they come from is cited; comments outside upstream declarations must not be copied at all
    words, wline = [], []
    def cmt_flag(n, ul, what):
        nonlocal unattr
        k = D['line2decl'].get(ul)
        ok = k is not None and attributed(cmt_text, k)
        unattr += not ok
        report.append(f'COMMENT   {f}:{n}  {what} (upstream line {ul}, {k or "outside declarations"})  '
                      + ('attributed' if ok else 'NOT ATTRIBUTED'))
    for n, (_, c) in enumerate(cc, 1):
        if n in covered: continue
        ws = comment_words(c)
        words += ws; wline += [n] * len(ws)
        if len(norm(c)) >= 25 and norm(c) in D['ucl']:
            cmt_flag(n, D['ucl'][norm(c)], 'comment line identical to upstream')
    seen = set()
    for i in range(len(words) - WORDS + 1):
        g = tuple(words[i:i + WORDS])
        if g in D['ucg'] and wline[i] not in seen:
            seen.add(wline[i])
            cmt_flag(wline[i], D['ucg'][g], f'{WORDS}-word run shared with an upstream comment')
    return verbatim, near, unattr

def stored_files():
    gen = set()
    for l in open(os.path.join(HERE, 'generated.sha256')):
        if l.strip(): gen.add(os.path.normpath(l.split()[-1]))
    keep = set()
    for l in open(os.path.join(ROOT, '.gitignore')):
        l = l.strip()
        if l.startswith('!/'): keep.add(l[2:])
    files = []
    for d in ('ThomsonGen', 'LogN7', 'LogLean', 'gen'):
        for dp, _, fs in os.walk(os.path.join(ROOT, d)):
            for fn in fs:
                p = os.path.relpath(os.path.join(dp, fn), ROOT)
                if not fn.endswith('.lean') or os.path.normpath(p) in gen: continue
                if p.startswith('ThomsonGen/') and p not in keep: continue   # regenerated, gitignored
                files.append(p)
    return sorted(files)

def main():
    files = sys.argv[1:] or stored_files()
    D = load_upstream()
    tv = tn = tu = 0
    for f in files:
        rep = []
        v, n, u = scan_file(D, f, rep)
        tv += v; tn += n; tu += u
        for r in rep: print(r, flush=True)
    print(f'scanned {len(files)} stored files against {len(D["UB"])} upstream declarations: '
          f'{tv} verbatim, {tn} near-copies, {tu} without attribution')
    ok = tv == 0 and tu == 0
    print('PASS' if ok else 'FAIL')
    return 0 if ok else 1

if __name__ == '__main__':
    sys.exit(main())
