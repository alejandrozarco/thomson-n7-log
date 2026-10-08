"""cert3_parse.py -- read a Case 1 `Cert3` data module (upstream `Case1Data.lean` list format, or the mkBlk/hex
format emitted by emit_cert3.py) and the chunk literals (`c1Stat w D (...) = (l1, dx, dy, dz, kev)`) back into
Python, so that `emit_cert3.py --check` re-runs every Lean Bool check on exactly the text that Lean will see."""
import re
from cert3_util import Blk, SBlk, Cert3, mkBlk

INT = re.compile(r"\(\s*(-?\d+)\s*:\s*Int\)")
NAT = re.compile(r"\(\s*(\d+)\s*:\s*Nat\)")
TRIPLE = re.compile(r"\(\(\s*(\d+)\s*:\s*Nat\),\s*\(\s*(\d+)\s*:\s*Nat\),\s*\(\s*(\d+)\s*:\s*Nat\)\)")
NUM = r"(0x[0-9a-fA-F]+|\d+)"


def _num(s):
    return int(s, 16) if s.startswith("0x") else int(s)


def parse_data(text):
    """Returns (cf, env): the `Cert3` value `cf` and the dict of all parsed definitions."""
    body = text.split("\ndef ")[1:]
    env = {}
    for chunk in body:
        head, _, rhs = chunk.partition(":=")
        name, _, typ = head.partition(":")
        name, typ = name.strip(), typ.strip()
        rhs = rhs.split("\nend ")[0].strip()
        if typ == "List Int":
            env[name] = [int(x) for x in INT.findall(rhs)]
        elif typ == "Nat":
            env[name] = _num(re.fullmatch(r"\(?\s*" + NUM + r"(\s*:\s*Nat\))?", rhs).group(1))
        elif typ == "Int":
            env[name] = int(INT.fullmatch(rhs).group(1))
        elif typ == "List (List Int)":
            names = re.findall(r"[A-Za-z_][A-Za-z0-9_]*", rhs.strip("[]"))
            env[name] = [env[n] for n in names]
        elif typ == "List (Nat × Nat × Nat)":
            env[name] = [tuple(int(v) for v in t) for t in TRIPLE.findall(rhs)]
        elif typ == "Blk":
            if rhs.startswith("mkBlk"):
                toks = re.findall(NUM, rhs[len("mkBlk"):])
                r, Bd, Bl, BD, xd, xl, xD = [_num(t) for t in toks]
                env[name] = mkBlk(r, Bd, Bl, BD, xd, xl, xD)
                env[name].packed = (r, Bd, Bl, BD, xd, xl, xD)
            else:
                a, b, cc = [x.strip() for x in rhs.strip("⟨⟩").split(",")]
                env[name] = Blk(env[a], env[b], env[cc])
        elif typ == "SBlk":
            m = re.fullmatch(r"⟨\[(.*?)\],\s*(.*?),\s*([A-Za-z0-9_]+),\s*([A-Za-z0-9_]+)⟩", rhs, re.S)
            g = [int(x) for x in NAT.findall(m.group(1))]
            sigma = int(NAT.fullmatch(m.group(2).strip()).group(1)) if "Nat" in m.group(2) else int(m.group(2))
            env[name] = SBlk(g, sigma, env[m.group(3)], env[m.group(4)])
        elif typ == "Cert3":
            fld = {}
            for key in ("n", "Lam", "an", "ad", "h", "eps", "F", "S"):
                m = re.search(r"\b" + key + r"\s*:=\s*(\[[^\]]*\]|\([^)]*\)|[A-Za-z0-9_]+)", rhs)
                fld[key] = m.group(1)

            def val(s, kind):
                s = s.strip()
                if s in env:
                    return env[s]
                if kind == "list":
                    return [env[x] for x in re.findall(r"[A-Za-z_][A-Za-z0-9_]*", s.strip("[]"))]
                m2 = re.fullmatch(r"\(\s*(-?\d+)\s*:\s*(Int|Nat)\)", s)
                return int(m2.group(1)) if m2 else int(s)
            env[name] = Cert3(val(fld["n"], "n"), val(fld["Lam"], "n"), val(fld["an"], "n"), val(fld["ad"], "n"),
                              val(fld["h"], "n"), val(fld["eps"], "n"), val(fld["F"], "list"), val(fld["S"], "list"))
        else:
            raise ValueError(f"unknown definition type {typ!r} for {name}")
    return env["cf"], env


STAT = re.compile(r"theorem\s+(\S+)\s*:\s*\n?\s*(?:ThomsonN7\.Case1\.)?c1Stat\s+(\d+)\s+(\d+)\s+(.*?)\s*=\s*"
                  r"\((\d+),\s*(\d+),\s*(\d+),\s*(\d+),\s*\(\(?(-?\d+)\)?\s*:\s*Int\)\)\s*:=", re.S)


def parse_stats(text):
    """{theorem name: (w, D, lhs text, (l1, dx, dy, dz, kev))} of the chunk theorems in a module."""
    out = {}
    for m in STAT.finditer(text):
        out[m.group(1)] = (int(m.group(2)), int(m.group(3)), " ".join(m.group(4).split()),
                           tuple(int(m.group(i)) for i in range(5, 10)))
    return out
