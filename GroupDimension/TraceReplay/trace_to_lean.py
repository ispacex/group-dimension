#!/usr/bin/env python3
"""Write a membership trace (cflint-fast-core cert/TRACE.md) as Lean data for TraceReplay.Check.

    trace_to_lean.py PRESENTATION CLAIM TRACE MODULE_NAME [POLYMAPS] > Data/NAME.lean

A trace with free columns (F nonempty) needs the polynomial maps (cert/polymaps/ID.json, cross-checked
against the claim's polymaps-sha256). Only weight-1 maps (homomorphisms G -> Z) are supported: the
certificate (HomCert, TraceReplay/HomExact.lean) uses the powers phi^K, K < n, of the maps and an integer
matrix C with C * (phi^K(X_f)) = diag(D_f), computed here and checked by the kernel.

PRESENTATION is a presentation JSON line, or a `.jsonl.gz` whose first line is used. The trace header,
the claim and the presentation are cross-checked (sha256 of the presentation line, p, d, n, E, the
claim's id and members) before anything is written.

Only the relators the trace uses are written (a subset of the relators generates a smaller ideal,
so membership in it is stronger). The presentation's word tests and lintests claimed in are written
too; test t >= len(tests) is lintest t - len(tests), the element sum_k c_k (w_k - 1).
"""
import gzip
import hashlib
import json
import sys
from fractions import Fraction
from math import lcm


def word(w):
    if w and isinstance(w[0], list):
        sys.exit("nested words are not supported")
    if len(w) % 2:
        sys.exit("a flat word of odd length")
    return "[" + ", ".join(f"({w[i]}, {w[i + 1]})" for i in range(0, len(w), 2)) + "]"


def off(d, g):
    return sum(d ** i for i in range(g))


def letters_at(d, c):
    """The word at position c (cert/common.h): degree g, then base-d digits, most significant first."""
    g = 0
    while off(d, g + 1) <= c:
        g += 1
    idx = c - off(d, g)
    out = []
    for _ in range(g):
        out.append(idx % d)
        idx //= d
    return out[::-1]


def hval(a, K, s, w):
    if not w:
        return s ** K
    j = w[0]
    aj = a[j] if j < len(a) else 0
    return hval(a, K, s + aj, w[1:]) - hval(a, K, s, w[1:])


def hom_cert(maps, F, d, n):
    """Functionals (a, K) and rows (C_f, D_f) with sum_k C_f[k] * hval(a_k, K_k, 0, X_f') = D_f [f = f']."""
    cands = [(a, K) for K in range(1, n) for a in maps]
    rows, chosen = [], []          # row-reduced copies, to test independence
    for a, K in cands:
        v = [Fraction(hval(a, K, 0, letters_at(d, f))) for f in F]
        r = v[:]
        for piv, row in rows:
            if r[piv]:
                c = r[piv] / row[piv]
                r = [x - c * y for x, y in zip(r, row)]
        nz = [i for i, x in enumerate(r) if x]
        if nz:
            rows.append((nz[0], r))
            chosen.append((a, K, v))
        if len(chosen) == len(F):
            break
    if len(chosen) < len(F):
        sys.exit(f"the powers of the maps have rank {len(chosen)} < |F| = {len(F)} on the free columns")
    nf = len(F)
    S = [c[2] for c in chosen]                       # S[k][f]
    # Sinv with Sinv * S = I (S square, invertible): Gauss-Jordan on [S | I]
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
    Sinv = [row[nf:] for row in A]                   # the two-sided inverse of S
    # C[f][k] with sum_k C[f][k] * S[k][f'] = D_f [f = f']: C = diag(D) * S^{-1}, D_f clearing denominators
    out = []
    for f in range(nf):
        row = Sinv[f]
        den = lcm(*[x.denominator for x in row])
        C = [int(x * den) for x in row]
        for f2 in range(nf):
            assert sum(C[k] * S[k][f2] for k in range(nf)) == (den if f == f2 else 0)
        out.append((C, den))
    funcs = [(a, K) for a, K, _ in chosen]
    return funcs, out


def lin(l):
    return "[" + ", ".join(f"({int(c)}, {word(w)})" for c, w in l) + "]"


def terms(fs):
    k = int(fs[0])
    if len(fs) != 1 + 2 * k:
        sys.exit("bad term count")
    return "[" + ", ".join(f"({fs[1 + 2 * i]}, {fs[2 + 2 * i]})" for i in range(k)) + "]"


def main():
    pres_path, claim_path, trace_path, name = sys.argv[1:5]
    pm_path = sys.argv[5] if len(sys.argv) > 5 else None
    opener = gzip.open if pres_path.endswith(".gz") else open
    with opener(pres_path, "rt") as fh:
        pres_line = fh.readline().rstrip("\n")
    pres = json.loads(pres_line)
    claim = dict(l.split(" ", 1) for l in open(claim_path).read().splitlines() if " " in l)
    if "test_coeffs" in pres and pres["test_coeffs"]:
        sys.exit("test_coeffs are not supported")
    members = [int(x) for x in claim["member"].split(",")]
    hdr, levels, F, xs, ws, used = {}, [], None, [], [], set()
    for line in open(trace_path).read().splitlines():
        f = line.split()
        if f[0] in ("trace-in", "presentation-sha256", "p", "d", "n", "E"):
            hdr[f[0]] = f[1]
        elif f[0] == "level":
            levels.append((int(f[1]), []))
        elif f[0] == "v":
            g = f[3]
            if g == "-":
                gen = ".zero"
            elif g[0] == "r":
                gen = f".rel {int(g[1:])}"
                used.add(int(g[1:]))
            elif g[0] in "LR":
                a, b = g[1:].split(",")
                gen = f".{'lsh' if g[0] == 'L' else 'rsh'} {int(a)} {int(b)}"
            else:
                sys.exit(f"unknown generator: {g}")
            levels[-1][1].append(f"⟨{f[1]}, {f[2]}, {gen}, {terms(f[4:])}⟩")
        elif f[0] == "F":
            F = [int(x) for x in f[2:]]
        elif f[0] == "x":
            xs.append(f"({f[1]}, {terms(f[2:])})")
        elif f[0] == "w":
            ws.append(f"({f[1]}, {terms(f[2:])})")
        elif f[0] == "end":
            break
        else:
            sys.exit(f"unknown trace line: {f[0]}")
    sha = hashlib.sha256(pres_line.encode()).hexdigest()
    for src, val in (("trace", hdr.get("presentation-sha256")), ("claim", claim.get("presentation-sha256"))):
        if val != sha:
            sys.exit(f"{src} presentation-sha256 {val} != {sha}")
    for key in ("p", "d", "n", "E"):
        if hdr.get(key) != claim.get(key):
            sys.exit(f"trace {key} {hdr.get(key)} != claim {claim.get(key)}")
    if int(hdr["p"]) != pres["p"] or int(hdr["d"]) != pres["d"]:
        sys.exit("p or d differs from the presentation")
    if int(hdr["n"]) > pres["nmax"]:
        sys.exit("n exceeds the presentation's nmax")
    if F is None:
        sys.exit("no F line")
    tests = pres.get("tests", [])
    lintests = pres.get("lintests", [])
    nt = len(tests)
    if not members or any(not 0 <= t < nt + len(lintests) for t in members):
        sys.exit("a member is not a test or lintest of the presentation")
    if any(not tests[t][1] for t in members if t < nt) or any(not lintests[t - nt][1] for t in members if t >= nt):
        sys.exit("a member is an empty test or lintest")
    wmem = [t for t in members if t < nt]
    lmem = [t for t in members if t >= nt]
    def elt(t):
        return word(tests[t][1]) if t < nt else lin(lintests[t - nt][1])
    hom = None
    if F:
        if pm_path is None:
            sys.exit("free columns: the polymaps file is needed")
        pm_line = open(pm_path).readline().rstrip("\n")
        if hashlib.sha256(pm_line.encode()).hexdigest() != claim.get("polymaps-sha256"):
            sys.exit("polymaps sha256 differs from the claim's polymaps-sha256")
        pm = json.loads(pm_line)
        if pm.get("presentation-sha256") != hdr["presentation-sha256"]:
            sys.exit("polymaps written for another presentation")
        d = int(hdr["d"])
        if any(m["w"] != 1 or len(m["lambda"]) != d for m in pm["maps"]):
            sys.exit("only weight-1 polynomial maps are supported")
        maps = [[int(x) for x in m["lambda"]] for m in pm["maps"]]
        hom = (maps,) + hom_cert(maps, F, d, int(hdr["n"]))
    out = []
    w = out.append
    imp = "HomExact" if hom else "Magnus"
    w(f"module\n\npublic import GroupDimension.TraceReplay.{imp}\n\n@[expose] public section\n")
    w(f"/-! Trace data: `{claim['id']}`, n = {hdr['n']}, E = {hdr['E']} (generated by `trace_to_lean.py`;")
    w(f"presentation sha256 `{hdr['presentation-sha256']}`).")
    w(f"Members: word tests {wmem}, lintests {lmem}.")
    w("-/\n")
    w(f"namespace GroupDimension.TraceReplay.{name}\n")
    w("set_option maxHeartbeats 0\n")
    w("def rels : List (Nat × List (Nat × Int)) := [")
    w(",\n".join(f"  ({i}, {word(pres['rels'][i])})" for i in sorted(used)) + "]\n")
    w("def tests : List (Nat × List (Nat × Int)) := [")
    w(",\n".join(f"  ({t}, {word(tests[t][1])})" for t in wmem) + "]\n")
    w("def lintests : List (Nat × List (Int × List (Nat × Int))) := [")
    w(",\n".join(f"  ({t}, {lin(lintests[t - nt][1])})" for t in lmem) + "]\n")
    for k, ls in levels:
        w(f"def level{k} : List Line := [")
        w(",\n".join("  " + l for l in ls) + "]\n")
    w("def xs : List (Nat × List (Nat × Int)) := [")
    w(",\n".join("  " + x for x in xs) + "]\n")
    w("def ws : List (Nat × List (Nat × Int)) := [")
    w(",\n".join("  " + x for x in ws) + "]\n")
    w(f"def members : List Nat := {members}\n")
    lv = ", ".join(f"({k}, level{k})" for k, _ in levels)
    w(f"def trace : Trace where\n  d := {hdr['d']}\n  n := {hdr['n']}\n  p := {hdr['p']}\n  E := {hdr['E']}")
    w(f"  rels := rels\n  tests := tests\n  lintests := lintests\n  levels := [{lv}]\n  F := {F}\n  xs := xs\n  ws := ws\n")
    w("/-- The replay, evaluated by the kernel (`decide +kernel`: no `native_decide`, no `ofReduceBool`). -/")
    w("theorem check_ok : check trace members = true := by decide +kernel\n")
    w("instance : NeZero trace.d := ⟨by decide⟩\n")
    w("/-- The certified statement (`TraceReplay.Sound`): every test claimed in has `linElt n (testLin t) ∈ LT`,")
    w("i.e. `mt n w_t − 1` for a word test and `Σ c_k (mt n w_k − 1)` for a lintest,")
    w("where `mt` is the Magnus map truncated below degree `n` (`mt = μ` modulo degree `≥ n` is not")
    w("formalized here) and `LT` is `J_n + p^E A_n` for the relators listed in `rels`, pulled back to")
    w("`ℤ⟨X⟩`; and `p^{E−1} X_w ∈ LT + span{X_f : f ∈ F}` for every word `w ≠ 1`. The statement is about the data in this")
    w("file: `rels`, `tests` and `lintests` are transcribed from the presentation by `trace_to_lean.py`. -/")
    w("theorem certified :\n    (∀ t ∈ members, linElt trace.d trace.n (testLin trace t) ∈ LT trace trace.n) ∧")
    w("    (∀ w : FreeMonoid (Fin trace.d), w ≠ 1 →")
    w("      ((trace.p ^ (trace.E - 1) : ℕ) : ℤ) • MonoidAlgebra.single w 1 ∈\n        LT trace trace.n ⊔ Fspan trace.d trace.F) :=")
    w("  check_sound trace members check_ok\n")
    if hom:
        maps, funcs, crows = hom
        fl = ", ".join(f"({a}, {K})" for a, K in funcs)
        rl = ", ".join(f"({C}, {D})" for C, D in crows)
        w("/-- The weight-1 polynomial maps (cert/polymaps): `a_j = φ(x_{j+1})`. -/")
        w(f"def maps : List (List Int) := {maps}\n")
        w("/-- The functionals `φ^K` and the integer left inverse on the free columns (`trace_to_lean.py`). -/")
        w(f"def hcert : HomCert where\n  funcs := [{fl}]\n  rows := [{rl}]\n")
        w("theorem hom_ok : checkHom trace hcert = true := by decide +kernel\n")
        w("theorem maps_ok : hcert.funcs.all (fun κ => maps.any (fun a => a == κ.1)) = true := by decide\n")
        w("/-- Not vacuous: every map has exponent sum `0` on the relators in `rels` (else `hrel` and `hφ`")
        w("contradict each other), on the tests (else a test has infinite order), and `Σ c_k φ(w_k) = 0` on the")
        w("lintests (else `φ` is nonzero on the lintest's image in `Δ/Δ²`, and `hord` fails). -/")
        w("theorem maps_vanish : maps.all (fun a => trace.rels.all (fun r => expSum trace.d a r.2 == 0) &&")
        w("    trace.tests.all (fun r => expSum trace.d a r.2 == 0) &&")
        w("    trace.lintests.all (fun l => (l.2.map (fun c => c.1 * expSum trace.d a c.2)).sum == 0)) = true := by")
        w("  decide +kernel\n")
    sha = f"{hdr['presentation-sha256'][:4]}…{hdr['presentation-sha256'][-4:]}"
    nn = hdr['n']
    for t in members:
        isw = t < nt
        kind = "Test" if isw else f"Lintest {t} (`{lintests[t - nt][0]}`, the element `Σ c_k (w_k − 1)`)"
        head = f"Test {t}" if isw else kind
        if isw:
            w(f"/-- Test {t} ({claim['id']}), its word written out. -/")
            w(f"theorem certified_test{t} :")
            w(f"    mt {hdr['d']} {nn} {elt(t)} - 1 ∈ LT trace {nn} := by")
            w(f"  have h := certified.1 {t} (by decide)")
            w(f"  rw [testLin_of_word trace (by decide), linElt_single] at h")
            w(f"  exact h\n")
        else:
            w(f"/-- {head} ({claim['id']}), written out. -/")
            w(f"theorem certified_test{t} :")
            w(f"    linElt {hdr['d']} {nn} {elt(t)} ∈ LT trace {nn} :=")
            w(f"  certified.1 {t} (by decide)\n")
        concl = f"gword g {elt(t)} ∈ GroupDimension.D {nn} G" if isw else f"linG g {elt(t)} ∈ augIdeal G ^ {nn}"
        what = f"lies in `D_{nn}(G)`" if isw else f"lies in `Δ^{nn}` of `ℤ[G]`"
        if hom:
            w(f"/-- {head} ({claim['id']}) {what} for every group `G` generated by `g 0, …, g {int(hdr['d']) - 1}`")
            w(f"(generator `i` of a word is `g ⟨i − 1⟩`) in which the relators in `rels` hold (the subset the trace uses,")
            w(f"transcribed from the presentation with sha256 `{sha}`), each assignment `g_j ↦ a_j`, `a ∈ maps`,")
            if isw:
                w("extends to a homomorphism `G → ℤ` (`hφ`), and the test element has `p`-power order (`hw`)")
                w("(`TraceReplay.check_mem_D_hom`, `hord_of_pow_eq_one`). Such a `G` is infinite. It says nothing")
                w("about whether the word is `≠ 1`. -/")
            else:
                w("extends to a homomorphism `G → ℤ` (`hφ`), and the element has `p`-power order in `Δ/Δ^n` (`hord`)")
                w("(`TraceReplay.check_mem_D_hom_lin`). Such a `G` is infinite. -/")
            w(f"theorem mem_D_test{t} {{G : Type*}} [Group G] (g : Fin trace.d → G)")
            w("    (hrel : ∀ r ∈ trace.rels, gword g r.2 = 1) (hgen : Subgroup.closure (Set.range g) = ⊤)")
            w("    (hφ : ∀ a ∈ maps, ∃ φ : G →* Multiplicative ℤ,")
            w("      ∀ j : Fin trace.d, Multiplicative.toAdd (φ (g j)) = a.getD j.val 0)")
            if isw:
                w(f"    (k : ℕ) (hw : gword g {elt(t)} ^ (trace.p ^ k) = 1) :")
                w(f"    {concl} :=")
                w(f"  check_mem_D_hom trace members check_ok hcert hom_ok g hrel hgen")
                w(f"    (homs_of_maps g maps hcert maps_ok hφ) {t} (by decide) (by decide)")
                w(f"    (hord_of_pow_eq_one (n := trace.n) (by decide) _ hw)\n")
            else:
                w(f"    (hord : ∃ m : ℕ, ((trace.p : ℤ) ^ m) • linG g {elt(t)} ∈ augIdeal G ^ trace.n) :")
                w(f"    {concl} :=")
                w(f"  check_mem_D_hom_lin trace members check_ok hcert hom_ok g hrel hgen")
                w(f"    (homs_of_maps g maps hcert maps_ok hφ) {t} (by decide) hord\n")
            continue
        w(f"/-- {head} ({claim['id']}) {what} for every group `G` generated by `g 0, …, g {int(hdr['d']) - 1}`")
        w(f"(generator `i` of a word is `g ⟨i − 1⟩`) in which the relators in `rels` hold (the subset the trace uses,")
        w(f"transcribed from the presentation with sha256 `{sha}`) and `x^{{{hdr['p']}^N}} = 1`")
        if isw:
            w("(`TraceReplay.check_mem_D`). It says nothing about whether the word is `≠ 1`. -/")
        else:
            w("(`TraceReplay.check_mem_D_lin`). -/")
        w(f"theorem mem_D_test{t} {{G : Type*}} [Group G] (g : Fin trace.d → G)")
        w("    (hrel : ∀ r ∈ trace.rels, gword g r.2 = 1) (hgen : Subgroup.closure (Set.range g) = ⊤)")
        w("    (N : ℕ) (hexp : ∀ x : G, x ^ (trace.p ^ N) = 1) :")
        w(f"    {concl} :=")
        if isw:
            w(f"  check_mem_D trace members check_ok rfl g hrel hgen N hexp {t} (by decide) (by decide)\n")
        else:
            w(f"  check_mem_D_lin trace members check_ok rfl g hrel hgen N hexp {t} (by decide)\n")
    w(f"end GroupDimension.TraceReplay.{name}")
    print("\n".join(out))


main()
