#!/usr/bin/env python3
"""Lean data for claims whose free columns need polynomial maps of weight >= 2 (MATH-314).

    poly_to_lean.py vanish OUTDIR SET POLYMAPS NAME=PRESENTATION ... [--chunk N]
    poly_to_lean.py cert   PRESENTATION CLAIM TRACE POLYMAPS MODULE VANISH_FILE

`vanish` writes modules under OUTDIR/SET, `cert` one module to stdout (module names `PolyData.<...>`).

* `vanish`: check 1 of `check_trace --polymaps` for every map of the set against every relator of each
  presentation given, evaluated by the kernel (`checkVanish`, TraceReplay/PolyVanishDefs.lean; soundness
  `vanish_of_check`, TraceReplay/PolyVanish.lean). The distinct relators are grouped by the presentations
  that contain them, and each group is checked once (`C<i>.lean`, `ok`); the module of a presentation joins
  its groups (`van_ok`). The relators are written as lists of factors `(word, k)`: a nested `[word, k]`
  factor as it is, a flat relator longer than 200 letters split into runs `u^k` (`factorize`, the expansion
  asserted equal to the relator here), so that long powers are computed by squaring.
* `cert`: the certificate of a claim (`PolyCert`: the maps, products of weight < n, and an exact integer left
  inverse on the trace's free columns `F`, computed here) and its kernel check on `F` (`checkPolyF`):
  `poly_ok`, and `polymaps_ok` = `poly_ok` and the presentation's `van_ok`. The trace itself is not
  transcribed (`trace_to_lean.py` does that for traces small enough for the kernel).

The presentation, claim, trace and polymaps are cross-checked (sha256, p, d, n, E, id) before anything is
written.
"""
import gzip
import hashlib
import itertools
import json
import os
import re
import sys
from fractions import Fraction
from functools import lru_cache
from math import lcm

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from trace_to_lean import letters_at, lin, off, parse_trace, word  # noqa: E402


def read_pres(path):
    opener = gzip.open if path.endswith(".gz") else open
    with opener(path, "rt") as fh:
        line = fh.readline().rstrip("\n")
    return line, json.loads(line), hashlib.sha256(line.encode()).hexdigest()


def read_polymaps(path, pres_sha):
    line = open(path).readline().rstrip("\n")
    pm = json.loads(line)
    if pm.get("presentation-sha256") != pres_sha:
        sys.exit("polymaps written for another presentation")
    maps = [(int(m["w"]), [int(x) for x in m["lambda"]]) for m in pm["maps"]]
    return maps, hashlib.sha256(line.encode()).hexdigest(), pm


D_GENS = None


def flat_pairs(w):
    if any(isinstance(x, list) for x in w) or len(w) % 2:
        sys.exit("a factor is not a flat word")
    pairs = [(w[i], w[i + 1]) for i in range(0, len(w), 2)]
    if D_GENS is not None and any(not 1 <= g <= D_GENS for g, _ in pairs):
        sys.exit("a generator outside 1..d")
    return pairs


def factorize(pairs, maxp=64):
    """Runs u^k (k >= 4, |u| <= maxp) and single letters in between, greedily; the expansion is the input."""
    out, lit, i = [], [], 0
    while i < len(pairs):
        best = (1, 0)
        for p in range(1, maxp + 1):
            if i + 2 * p > len(pairs):
                break
            k = 1
            while i + (k + 1) * p <= len(pairs) and pairs[i + k * p:i + (k + 1) * p] == pairs[i:i + p]:
                k += 1
            if k >= 4 and k * p > best[0] * best[1]:
                best = (k, p)
        k, p = best
        if k >= 4:
            if lit:
                out.append((lit, 1))
                lit = []
            out.append((pairs[i:i + p], k))
            i += k * p
        else:
            lit.append(pairs[i])
            i += 1
    if lit:
        out.append((lit, 1))
    if [x for u, k in out for _ in range(k) for x in u] != pairs:
        sys.exit("factorize: the runs do not expand to the relator")
    return out


def factors(r):
    """A relator as a list of factors (flat word as pairs, exponent)."""
    if r and isinstance(r[0], list):
        out = []
        for f in r:
            if len(f) != 2 or isinstance(f[1], list):
                sys.exit("bad factor [word, k]")
            out.append((flat_pairs(f[0]), int(f[1])))
        return out
    pairs = flat_pairs(r)
    return factorize(pairs) if len(pairs) > 200 else [(pairs, 1)]


def lean_pairs(pairs):
    return "[" + ", ".join(f"({g}, {e})" for g, e in pairs) + "]"


def lean_rel(fs):
    return "[" + ", ".join(f"({lean_pairs(u)}, {k})" for u, k in fs) + "]"


def lean_maps(maps):
    return "[" + ", ".join(f"({w}, {lam})" for w, lam in maps) + "]"


# --- PolyCert: the same reading of the maps as PolyExact.lean (baseVal, prodVal, covW, colValP) ---

def pos_n(d, u):
    acc = 0
    for j in u:
        acc = acc * d + j
    return off(d, len(u)) + acc


def make_prodval(d, maps):
    def baseval(i, u):
        w, lam = maps[i]
        if 0 < len(u) <= w:
            k = pos_n(d, u) - 1
            return lam[k] if k < len(lam) else 0
        return 0

    @lru_cache(maxsize=None)
    def prodval(kappa, u):
        if not kappa:
            return 1 if not u else 0
        i, rest = kappa[0], kappa[1:]

        def covw(a, b, l):
            if not l:
                return baseval(i, a) * prodval(rest, b)
            j, l2 = l[0], l[1:]
            return covw(a + (j,), b, l2) + covw(a, b + (j,), l2) + covw(a + (j,), b + (j,), l2)
        return covw((), (), u)
    return prodval


def poly_cert(maps, F, d, n):
    """Products kappa (multisets of maps, weight < n) of full rank on F, and rows (C_f, D_f) with
    sum_k C_f[k] * nu_k(X_f') = D_f [f = f'], exactly."""
    prodval = make_prodval(d, maps)
    idx = range(len(maps))
    cands = []
    for size in range(1, n):
        for kappa in itertools.combinations_with_replacement(idx, size):
            if sum(maps[i][0] for i in kappa) < n:
                cands.append(kappa)
    cands.sort(key=lambda k: (sum(maps[i][0] for i in k), len(k), k))
    cols = [tuple(letters_at(d, f)) for f in F]
    rows, chosen = [], []
    for kappa in cands:
        v = [Fraction(prodval(kappa, u)) for u in cols]
        r = v[:]
        for piv, row in rows:
            if r[piv]:
                c = r[piv] / row[piv]
                r = [x - c * y for x, y in zip(r, row)]
        nz = [i for i, x in enumerate(r) if x]
        if nz:
            rows.append((nz[0], r))
            chosen.append((kappa, v))
        if len(chosen) == len(F):
            break
    if len(chosen) < len(F):
        sys.exit(f"the products have rank {len(chosen)} < |F| = {len(F)} on the free columns")
    nf = len(F)
    S = [c[1] for c in chosen]
    A = [S[i][:] + [Fraction(int(i == j)) for j in range(nf)] for i in range(nf)]
    for col in range(nf):
        piv = next(r for r in range(col, nf) if A[r][col])
        A[col], A[piv] = A[piv], A[col]
        pv = A[col][col]
        A[col] = [x / pv for x in A[col]]
        for r in range(nf):
            if r != col and A[r][col]:
                c = A[r][col]
                A[r] = [x - c * y for x, y in zip(A[r], A[col])]
    Sinv = [row[nf:] for row in A]
    out = []
    for f in range(nf):
        row = Sinv[f]
        den = lcm(*[x.denominator for x in row])
        C = [int(x * den) for x in row]
        for f2 in range(nf):
            if sum(C[k] * S[k][f2] for k in range(nf)) != (den if f == f2 else 0):
                sys.exit("the left inverse is wrong")
        out.append((C, den))
    return [list(k) for k, _ in chosen], out


# --- modes ---

def header(w, imports, doc):
    w("module\n")
    for i in imports:
        w(f"public import {i}")
    w("\n@[expose] public section\n")
    w("/-!\n" + doc + "\n-/\n")


def mode_vanish(args):
    """vanish OUTDIR SET POLYMAPS NAME=PRESENTATION ... [--chunk N]: one module per cell of relators (the
    relators shared by exactly the same presentations), and one per presentation joining its cells."""
    chunk = 100
    if "--chunk" in args:
        i = args.index("--chunk")
        chunk = int(args[i + 1])
        args = args[:i] + args[i + 2:]
    outdir, setname, pm_path = args[:3]
    pres_args = [a.split("=", 1) for a in args[3:]]
    pm_line = open(pm_path).readline().rstrip("\n")
    pm = json.loads(pm_line)
    maps = [(int(m["w"]), [int(x) for x in m["lambda"]]) for m in pm["maps"]]
    K = max(w for w, _ in maps) + 1
    press, d = [], None
    global D_GENS
    pm_pres = pm.get("presentation-sha256")
    shas = []
    for name, path in pres_args:
        _, pres, sha = read_pres(path)
        shas.append(sha)
        if d is None:
            d = int(pres["d"])
        elif int(pres["d"]) != d:
            sys.exit("presentations with different d")
        press.append((name, sha, pres["rels"]))
    D_GENS = d
    if pm_pres not in shas:
        sys.exit("the polymaps file was written for none of the presentations")
    if any(len(lam) != off(d, w + 1) - 1 for w, lam in maps):
        sys.exit("a map has the wrong number of values")
    # cells: relator (exact JSON) -> the presentations containing it
    member, order = {}, []
    for pi, (_, _, rels) in enumerate(press):
        for r in rels:
            key = json.dumps(r, separators=(",", ":"))
            if key not in member:
                member[key] = set()
                order.append((key, r))
            member[key].add(pi)
    cells = {}
    for key, r in order:
        cells.setdefault(frozenset(member[key]), []).append(r)
    mods = []          # (module name, relators, cell)
    for cell, rels in cells.items():
        for i in range(0, len(rels), chunk):
            mods.append((f"C{len(mods)}", rels[i:i + chunk], cell))
    base = f"PolyData.Vanish.{setname}"
    os.makedirs(os.path.join(outdir, setname), exist_ok=True)

    def emit(fname, lines):
        with open(os.path.join(outdir, setname, fname + ".lean"), "w") as fh:
            fh.write("\n".join(lines) + "\n")

    out = []
    w = out.append
    header(w, ["GroupDimension.TraceReplay.PolyVanishDefs"],
           f"The polynomial maps of the set `{setname}` (polymaps sha256 of the source file\n"
           f"`{hashlib.sha256(pm_line.encode()).hexdigest()}`; weights {[w_ for w_, _ in maps]}). Generated by `poly_to_lean.py vanish`.")
    w(f"namespace {base}.Maps\n")
    w(f"def maps : List (Nat × List Int) := {lean_maps(maps)}\n")
    w(f"end {base}.Maps")
    emit("Maps", out)
    for mname, rels, cell in mods:
        out = []
        w = out.append
        header(w, [f"{base}.Maps"],
               f"Check 1 of `check_trace --polymaps` in the kernel for {len(rels)} relators shared by the presentations\n"
               f"{sorted(press[i][0] for i in cell)} (set `{setname}`; generated by `poly_to_lean.py vanish`). The relators are\n"
               "factors `(word, k)`: nested factors as given, long flat relators split into runs `u^k` (the expansion\n"
               "asserted equal to the relator by the generator).")
        w(f"namespace {base}.{mname}\n\nopen GroupDimension.TraceReplay\n")
        w("set_option maxHeartbeats 0\n")
        # small literals joined by `++`: elaborating one long list literal is quadratic in its length
        piece = 10
        parts = [rels[i:i + piece] for i in range(0, len(rels), piece)]
        for pi_, part in enumerate(parts):
            w(f"def rels{pi_} : List (List (List (Nat × Int) × Int)) := [")
            w(",\n".join("  " + lean_rel(factors(r)) for r in part) + "]\n")
        w("def rels : List (List (List (Nat × Int) × Int)) :=")
        w("  " + " ++ ".join(f"rels{i}" for i in range(len(parts))) + "\n")
        w("set_option maxRecDepth 100000 in")
        w(f"theorem ok : checkVanish {d} {K} Maps.maps rels = true := by decide +kernel\n")
        w(f"end {base}.{mname}")
        emit(mname, out)
    nest = lambda xs: xs[0] if len(xs) == 1 else f"{xs[0]} ++ ({nest(xs[1:])})"  # noqa: E731
    for pi, (name, sha, rels) in enumerate(press):
        mine = [m for m in mods if pi in m[2]]
        if sorted(json.dumps(r, separators=(",", ":")) for m in mine for r in m[1]) != \
                sorted(set(json.dumps(r, separators=(",", ":")) for r in rels)):
            sys.exit(f"the cells of {name} are not its relators")
        out = []
        w = out.append
        header(w, [f"{base}.{m[0]}" for m in mine],
               f"Check 1 for every map of the set `{setname}` against every relator of the presentation `{name}`\n"
               f"(sha256 `{sha}`, {len(rels)} relators, {len(set(json.dumps(r) for r in rels))} distinct), joined from\n"
               f"{len(mine)} cell modules (generated by `poly_to_lean.py vanish`).")
        w(f"namespace {base}.{name}\n\nopen GroupDimension.TraceReplay\n")
        w(f'def presentationSha : String := "{sha}"\n')
        w(f"def maps : List (Nat × List Int) := {lean_maps(maps)}\n")
        w("/-- The relators of the presentation (each distinct one once; the presented group is the same). -/")
        w(f"def allRels : List (List (List (Nat × Int) × Int)) :=\n  {nest([f'{m[0]}.rels' for m in mine])}\n")
        proof = f"{mine[-1][0]}.ok"
        for m in reversed(mine[:-1]):
            proof = f"checkVanish_append {m[0]}.ok ({proof})"
        w("/-- Check 1 for every map against every relator (`vanish_of_check`: each map satisfies `Vanish`). -/")
        w(f"theorem van_ok : checkVanish {d} {K} maps allRels = true := by")
        w(f"  rw [show maps = Maps.maps from rfl]\n  exact {proof}\n")
        w(f"end {base}.{name}")
        emit(name, out)
    tot = sum(len(m[1]) for m in mods)
    print(f"{setname}: {len(press)} presentations, {tot} distinct relators in {len(mods)} cell modules", file=sys.stderr)


def vanish_meta(path):
    text = open(path).read()
    m = re.search(r'def presentationSha : String := "([0-9a-f]+)"', text)
    k = re.search(r"theorem van_ok : checkVanish (\d+) (\d+) maps allRels", text)
    ns = re.search(r"namespace (PolyData\.\S+)", text)
    mp = re.search(r"def maps : List \(Nat × List Int\) := (.*)\n", text)
    if not (m and k and ns and mp):
        sys.exit("not a vanish module")
    return m.group(1), int(k.group(1)), int(k.group(2)), ns.group(1), mp.group(1)


def load_claim(pres_path, claim_path, trace_path, pm_path, vanish_path):
    _, pres, sha = read_pres(pres_path)
    claim = dict(l.split(" ", 1) for l in open(claim_path).read().splitlines() if " " in l)
    hdr, levels, F, xs, ws, used = parse_trace(trace_path)
    for src, val in (("trace", hdr.get("presentation-sha256")), ("claim", claim.get("presentation-sha256"))):
        if val != sha:
            sys.exit(f"{src} presentation-sha256 {val} != {sha}")
    for key in ("p", "d", "n", "E"):
        if hdr.get(key) != claim.get(key):
            sys.exit(f"trace {key} {hdr.get(key)} != claim {claim.get(key)}")
    if int(hdr["p"]) != pres["p"] or int(hdr["d"]) != pres["d"]:
        sys.exit("p or d differs from the presentation")
    if "nmax" in pres and int(hdr["n"]) > pres["nmax"]:
        sys.exit("n exceeds the presentation's nmax")
    if not F:
        sys.exit("no free columns: use trace_to_lean.py")
    pm_line = open(pm_path).readline().rstrip("\n")
    if hashlib.sha256(pm_line.encode()).hexdigest() != claim.get("polymaps-sha256"):
        sys.exit("polymaps sha256 differs from the claim's polymaps-sha256")
    maps, _, _ = read_polymaps(pm_path, sha)
    vsha, vd, vK, vns, vmaps = vanish_meta(vanish_path)
    if vsha != sha:
        sys.exit("the vanish module is for another presentation")
    if vmaps != lean_maps(maps):
        sys.exit("the vanish module has other maps")
    d, n = int(hdr["d"]), int(hdr["n"])
    if vd != d:
        sys.exit("d differs from the vanish module")
    if any(w >= n for w, _ in maps):
        sys.exit("a map has weight >= n")
    funcs, crows = poly_cert(maps, F, d, n)
    return pres, sha, claim, hdr, levels, F, xs, ws, used, maps, funcs, crows, vns, vK


def write_cert(w, maps, funcs, crows, vns):
    rl = ", ".join(f"({C}, {D})" for C, D in crows)
    w(f"def maps : List (Nat × List Int) := {lean_maps(maps)}\n")
    w(f"theorem maps_eq : maps = {vns}.maps := rfl\n")
    w("/-- The products of base maps (weight `< n`) and the exact integer left inverse on the free columns")
    w("(`poly_to_lean.py`). -/")
    w(f"def cert : PolyCert where\n  maps := maps\n  funcs := {funcs}\n  rows := [{rl}]\n")


def mode_cert(args):
    pres_path, claim_path, trace_path, pm_path, name, vanish_path = args[:6]
    (pres, sha, claim, hdr, levels, F, xs, ws, used, maps, funcs, crows, vns, K) = load_claim(
        pres_path, claim_path, trace_path, pm_path, vanish_path)
    d, n = hdr["d"], hdr["n"]
    out = []
    w = out.append
    header(w, ["GroupDimension.TraceReplay.PolyVanish", vns],
           f"The polynomial-map part of `{claim['id']}`, n = {n}, E = {hdr['E']}, in the kernel (generated by\n"
           f"`poly_to_lean.py cert`; presentation sha256 `{sha}`). The trace itself ({sum(len(l) for _, l in levels)}\n"
           "vectors) is checked by `cert/trace` only; `F` is its line `F`. Given a trace `T` with these\n"
           "`d`, `n`, `F`, `poly_ok` is `checkPoly T cert = true` and the vanish module's `van_ok` is `hvan` of\n"
           "`check_mem_D_poly_presN` (TraceReplay/PolyVanish.lean) for `G = ⟨x | allRels⟩`. What the membership\n"
           "claim then still rests on, outside the kernel: `check T members = true` (the trace; `cert/trace`),\n"
           "the transcription of `F` and of the presentation's relators into `allRels` (this generator), `hsub`\n"
           "(the trace's relators among `allRels`, `expandRel`), and `hord` (the test has `p`-power order in\n"
           "`Δ/Δ^n`; GAP).")
    w(f"namespace PolyData.{name}\n\nopen GroupDimension.TraceReplay\n")
    w("set_option maxHeartbeats 0\n")
    w(f"/-- The free columns of the trace. -/\ndef F : List Nat := {F}\n")
    write_cert(w, maps, funcs, crows, vns)
    w(f"theorem poly_ok : checkPolyF {d} {n} F cert = true := by decide +kernel\n")
    w("/-- The two kernel checks on the polynomial maps: the left inverse on `F`, and check 1 for every map")
    w("against every relator of the presentation. -/")
    w(f"theorem polymaps_ok : checkPolyF {d} {n} F cert = true ∧ checkVanish {d} {K} cert.maps {vns}.allRels = true :=")
    w(f"  ⟨poly_ok, by rw [show cert.maps = {vns}.maps from maps_eq]; exact {vns}.van_ok⟩\n")
    w(f"end PolyData.{name}")
    print("\n".join(out))


def main():
    if len(sys.argv) < 2 or sys.argv[1] not in ("vanish", "cert"):
        sys.exit(__doc__)
    {"vanish": mode_vanish, "cert": mode_cert}[sys.argv[1]](sys.argv[2:])


if __name__ == "__main__":
    main()
