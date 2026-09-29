"""Negative controls for the exact checkers (checkers/check_cell.py, checkers/check_cert.py).

Each control removes or corrupts SOS data of a certificate in memory, writes the copy to a temporary file and runs
the checker on it. The untampered certificate must give ALL_OK = True; every tampered copy must give ALL_OK = False
(a checker exception also counts as a rejection). Exit status 0 iff all outcomes are as expected.

usage: python3 checkers/check_controls.py           (Case 1, slab [-99/100,-49/50], cap; about 3 min on one core)
"""
import copy, json, os, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check_cell  # noqa: E402
import check_cert  # noqa: E402


def controls(J0):
    tags = list(J0["SOS"])
    out = [("untampered", lambda J: None, True),
           ("SOS removed", lambda J: J.pop("SOS"), False),
           ("SOS empty", lambda J: J.__setitem__("SOS", {}), False)]
    for t in tags:
        out.append((f"tag {t} removed", lambda J, t=t: J["SOS"].pop(t), False))
        out.append((f"last block of {t} removed", lambda J, t=t: J["SOS"][t].pop(), False))
    out.append(("extra tag", lambda J: J["SOS"].__setitem__("X", copy.deepcopy(J["SOS"][tags[0]])), False))
    return out


def run(checker, path):
    J0 = json.load(open(path))
    allgood = True
    for name, mod, expect in controls(J0):
        J = copy.deepcopy(J0)
        mod(J)
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
            json.dump(J, f)
        t0 = time.time()
        try:
            got = bool(checker(f.name)["ALL_OK"])
        except Exception as ex:  # a crash is a rejection
            got = False; name += f" (exception {type(ex).__name__})"
        finally:
            os.unlink(f.name)
        good = got == expect
        allgood &= good
        print(f"{os.path.basename(path)}: {name:32s} ALL_OK={got!s:5s} expected={expect!s:5s} "
              f"{'ok' if good else 'UNEXPECTED'} ({time.time() - t0:.0f}s)", flush=True)
    return allgood


if __name__ == "__main__":
    ok = True
    for p in ("cert_case1_log_D10.json", "cert_slab_99_98_log_D10.json"):
        ok &= run(lambda q: check_cell.check(q, verbose=False, do_sanity=False), os.path.join(HERE, "..", "certificates", "cells", p))
    ok &= run(lambda q: check_cert.check(q, verbose=False), os.path.join(HERE, "..", "certificates", "cert_cap_log_D12.json"))
    print("CONTROLS_OK" if ok else "CONTROLS_FAIL")
    sys.exit(0 if ok else 1)
