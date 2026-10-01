"""Split lean/LogLean/LocalGlobal.lean (single file, killed by the memory watchdog) into
LocalGlobA (defs + light checks), LocalGlobB/B2 (expansions), LocalGlobC (pieces), LocalGlobD/D2 (Bombieri lists),
LocalGlobE (per-pair Bombieri) and LocalGlobal (real-side consequences).  Idempotent: reads LocalGlobal.orig.lean."""
import os, re
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, '..', 'LogLean')
orig = os.path.join(LEAN, 'LocalGlobal.orig.lean')
cur = os.path.join(LEAN, 'LocalGlobal.lean')
if not os.path.exists(orig):
    os.rename(cur, orig)
src = open(orig).read()

i_real = src.index('/-! ## Real-side consequences -/')
head, real = src[:i_real], src[i_real:]


def grab(start, end):
    """cut head[start:end) markers (end exclusive; end marker kept in head)"""
    global head
    i = head.index(start)
    j = head.index(end, i) if end else len(head)
    seg = head[i:j]
    head = head[:i] + head[j:]
    return seg


exps = grab('theorem exp2 :', '/-! ### Structured forms of the pieces -/')
pieces = grab('/-! ### Structured forms of the pieces -/', '/-! ### Bombieri data -/')
bomb = grab('/-! ### Bombieri data -/', '/-- per pair: Bombieri squares')
pairb = grab('/-- per pair: Bombieri squares', None)
pairb = pairb[:pairb.rindex('theorem Sok4')] + pairb[pairb.rindex('theorem Sok4'):].split('\n')[0] + '\n'

# ---- A: remaining head
A = head.replace('# LocalGlobal: the global Taylor data and its `(σ, w)` expansion, certified in the kernel ',
                 '# LocalGlobA: definitions of the global level and its light kernel checks (pair sums, `F2 = ½xᵀHx`, lengths)')
A = A.rstrip() + '\n\nend LocalGlobal\n'
open(os.path.join(LEAN, 'LocalGlobA.lean'), 'w').write(A)

HDR = '''import LogLean.LocalGlobA

/-! # {nm}: kernel checks of the global level ({doc}); the consequences are in LocalGlobal -/

namespace LocalGlobal
open LocalKel LocalSP LocalBomb LocalGlobData LocalPairData LocalFrames

'''


def prof(text):
    return re.sub(r'^theorem ', 'set_option profiler true in\ntheorem ', text, flags=re.M)


def thm(text, name):
    m = re.search(r'^theorem %s\b.*?(?=^theorem |^def |^/-|\Z)' % re.escape(name), text, flags=re.M | re.S)
    return m.group(0).rstrip() + '\n'


# ---- B, B2: expansions
B = ''.join(thm(exps, n) for n in ('exp2', 'exp3', 'exp4c0', 'exp4c1'))
B2 = ''.join(thm(exps, n) for n in ('exp4c2', 'exp4c3', 'exp4'))
open(os.path.join(LEAN, 'LocalGlobB.lean'), 'w').write(HDR.format(nm='LocalGlobB', doc='expansions of F₂, F₃ and the first two F₄ chunks') + prof(B) + '\nend LocalGlobal\n')
open(os.path.join(LEAN, 'LocalGlobB2.lean'), 'w').write(HDR.format(nm='LocalGlobB2', doc='the last two F₄ chunks and the piece decomposition') + prof(B2) + '\nend LocalGlobal\n')
# ---- C: pieces (keep defs gamPoly, projPoly, n2_16)
C = pieces.replace('/-! ### Structured forms of the pieces -/\n', '')
open(os.path.join(LEAN, 'LocalGlobC.lean'), 'w').write(HDR.format(nm='LocalGlobC', doc='structured forms of the σ-graded pieces') + prof(C) + '\nend LocalGlobal\n')
# ---- D, D2: Bombieri lists
defs = bomb[:bomb.index('theorem bs3')].replace('/-! ### Bombieri data -/\n', '')
D = ''.join(thm(bomb, n) for n in ('bs3', 'bs4', 'bs41', 'bs42', 'bs43', 'ws3', 'ws41', 'ws42', 'ws43'))
D2 = thm(bomb, 'ws4') + '\n' + '\n'.join(f'theorem Sok16_{d} : Sok (S16 {d}) = true := by decide +kernel' for d in (1, 2, 3, 4)) + '\n'
open(os.path.join(LEAN, 'LocalGlobD.lean'), 'w').write(HDR.format(nm='LocalGlobD', doc='Bombieri squares and sub-sequence checks') + defs + prof(D) + '\nend LocalGlobal\n')
open(os.path.join(LEAN, 'LocalGlobD2.lean'), 'w').write(HDR.replace('import LogLean.LocalGlobA', 'import LogLean.LocalGlobD').format(nm='LocalGlobD2', doc='the degree-4 multinomial list and the `Sok` checks') + prof(D2) + '\nend LocalGlobal\n')
# ---- E: per pair
open(os.path.join(LEAN, 'LocalGlobE.lean'), 'w').write(HDR.format(nm='LocalGlobE', doc='per-pair Bombieri data') + prof(pairb) + '\nend LocalGlobal\n')
# ---- real side
R = '''import LogLean.LocalGlobB
import LogLean.LocalGlobB2
import LogLean.LocalGlobC
import LogLean.LocalGlobD2
import LogLean.LocalGlobE

/-!
# LocalGlobal: real-side consequences of the global kernel checks

`F2_exp F3_exp F4_exp` (the (σ, w) expansions with their structured pieces), `bomb_*` (Bombieri bounds),
`pair_bomb` (per-pair degree 5/6 bounds); `F_sum` and the definitions are in LocalGlobA, the kernel checks in
LocalGlobB–E (split so that each module stays within the memory budget of one `decide +kernel` family).
-/

namespace LocalGlobal
open LocalKel LocalSP LocalBomb LocalGlobData LocalPairData LocalFrames Finset

variable {x : ℕ → ℝ} {a : ℝ}

''' + real
R = R.replace('''  have h := Sok16; simp only [Bool.and_eq_true] at h
  interval_cases d
  · exact h.1.1.1
  · exact h.1.1.2
  · exact h.1.2
  · exact h.2''', '''  interval_cases d
  · exact Sok16_1
  · exact Sok16_2
  · exact Sok16_3
  · exact Sok16_4''')
open(cur, 'w').write(R)
for f in ('A', 'B', 'B2', 'C', 'D', 'D2', 'E'):
    print(f, len(open(os.path.join(LEAN, f'LocalGlob{f}.lean')).read().splitlines()))
print('real', len(R.splitlines()))
