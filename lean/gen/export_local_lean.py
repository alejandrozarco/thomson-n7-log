"""Generator of the data blocks of the Lemma L' Lean modules (LocalAtom, later LocalPairs*, LocalGlobal, LocalBomb).

Reads lean/gen/local_pre_out.json (local_pre.py) and lean/gen/local_atom_out.json (local_atom.py) and rewrites the
region between `-- DATA` and `-- END DATA` of the target file(s).  usage: python3 lean/gen/export_local_lean.py [atom]
"""
import os, sys, json
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, '..', 'LogLean')
J = json.load(open(os.path.join(HERE, 'local_pre_out.json')))
JA = json.load(open(os.path.join(HERE, 'local_atom_out.json')))


def q(x):
    x = Fr(x)
    return f'{x.numerator}' if x.denominator == 1 else f'{x.numerator}/{x.denominator}'


def kel(c):
    return '⟨' + ', '.join(q(v) for v in c) + '⟩'


def replace_region(path, text):
    src = open(path).read()
    i0 = src.index('-- DATA\n') + len('-- DATA\n')
    i1 = src.index('-- END DATA') if '-- END DATA' in src else src.index('end LocalAtom')
    if '-- END DATA' not in src:
        text = text + '-- END DATA\n\n'
    open(path, 'w').write(src[:i0] + text + src[i1:])


CLASSES = ['ring_adj', 'ring_diag', 'pole_ring', 'pole_pole']
SHORT = {'ring_adj': 'adj', 'ring_diag': 'diag', 'pole_ring': 'pole', 'pole_pole': 'pp'}


def t6_lean(name, T, doc):
    rows = [f'(⟨{", ".join(str(e) for e in m[:6])}⟩, {kel(c)})' for m, c in T]
    return f'/-- {doc} -/\ndef {name} : LocalSP.T6 :=\n  [' + ',\n    '.join(rows) + ']\n\n'


def atom_block():
    out = []
    for nm in CLASSES:
        c, ca, s = J['classes'][nm], JA['classes'][nm], SHORT[nm]
        T6 = [(m, cc) for m, cc in c['T6']]
        out.append(t6_lean(f'T6{s}', T6, f'`T6` of class `{nm}` (g = {kel(c["g"])}): {len(T6)} monomials in `A B C C′ rᵢ² rⱼ²`'))
        out.append(f'def g_{s} : Kel := {kel(ca["g"])}\n')
        out.append(f'def W_{s} : Kel := {kel(ca["W"])}\n')
        out.append(f'def inv_{s} : Kel := {kel(ca["inv"])}\n')
        out.append(f'/-- rational upper bound of √(1 − g²) -/\ndef sg_{s} : ℚ := {q(ca["sg"])}\n')
        out.append(f'def cl_{s} : Cls := ⟨SQ2 * sg_{s}, 1/2, sg_{s}, CE⟩\n')
        out.append(f'/-- `K_g` of class `{nm}` (exact err {float(Fr(ca["Kexact"])):.6f}) -/\ndef K_{s} : ℚ := {q(ca["K"])}\n\n')
        out.append(f'set_option profiler true in\ntheorem check_{s} : checkClass cl_{s} g_{s} W_{s} inv_{s} T6{s} K_{s} = true := by\n  decide +kernel\n\n')
        out.append(f'''/-- **Atom-level bound, class `{nm}`.** -/
theorem bound_{s} {{A B C Cp ri rj R a ei ej : ℝ}} (h : Hyp cl_{s} A B C Cp ri rj R a)
    (hei : |ei| ≤ (CE : ℝ) * R ^ 8) (hej : |ej| ≤ (CE : ℝ) * R ^ 8) :
    |PhiR (g_{s}.ev a) (W_{s}.ev a) (inv_{s}.ev a) A B C Cp (nhat ri + ei) (nhat rj + ej)
        - evT6 T6{s} A B C Cp ri rj a| ≤ (K_{s} : ℝ) * R ^ 7 :=
  class_bound h g_{s} W_{s} inv_{s} T6{s} K_{s} check_{s} hei hej

''')
    out.append('end LocalAtom\n\n' + ''.join(f'#print axioms LocalAtom.bound_{SHORT[nm]}\n' for nm in CLASSES))
    return ''.join(out)


if __name__ == '__main__':
    what = sys.argv[1:] or ['atom']
    if 'atom' in what:
        path = os.path.join(LEAN, 'LocalAtom.lean')
        src = open(path).read()
        i0 = src.index('-- DATA\n') + len('-- DATA\n')
        open(path, 'w').write(src[:i0] + '\n' + atom_block())
        print('wrote', path)
