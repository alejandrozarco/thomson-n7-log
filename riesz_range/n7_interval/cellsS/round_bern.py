"""[cellsS] Exact rounding of the control certificates of a Bernstein solve (sdp_bern.py, mode mu).

usage: python3 round_bern.py sol/bern_<tag>.npz OUTDIR
Splits the npz into one file per control point (sol/<tag>_c<k>.npz) and runs round_cell.main on each
(kernel label "hat": identities + PD only; the s-dependent conditions are checked by check_bern.py).
writes OUTDIR/<tag>_c<k>.json
"""
import json, os, sys
import numpy as np
import round_cell


def main(path, outdir):
    sol = np.load(path)
    meta = json.loads(str(sol["meta"]))
    tag = os.path.basename(path)[:-4]
    os.makedirs(outdir, exist_ok=True)
    outs = []
    for k in range(meta["m"] + 1):
        pre = f"c{k}__"
        arrs = {key[len(pre):]: sol[key] for key in sol.files if key.startswith(pre)}
        mk = dict(meta, control=k, ker=1, riesz_s=None)
        p = os.path.join(os.path.dirname(path), f"{tag}_c{k}.npz")
        np.savez(p, meta=json.dumps(mk), **arrs)
        out = os.path.join(outdir, f"{tag}_c{k}.json")
        rep = round_cell.main(p, out)
        outs.append(out)
        if not rep["ALL_OK"]:
            print("CONTROL", k, "FAILED", flush=True)
    print("WROTE", " ".join(outs), flush=True)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
