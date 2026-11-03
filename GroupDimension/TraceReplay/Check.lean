module

@[expose] public section

/-!
# Replaying a membership trace in the kernel (MATH-314, item 7)

A *membership trace* (cflint-fast-core, `cert/TRACE.md`) is a straight-line program over
`A_k = ℤ⟨X_1..X_d⟩ / (degree ≥ k)`, `k = 2..n`. Each line defines a vector
`V = u·(G + Σ c_i V_i)` where `G` is `0`, `μ(r) − 1` for a relator `r` (truncated to `A_k`), or a
shift `X_j·V'` / `V'·X_j` of a vector `V'` of level `k − 1`. Then
* an `x` line says `p^{E−1} e_c + Σ c_i V_i` has no entry outside the free columns `F`, and
* a `w` line says `μ(w_t) − 1 + Σ c_i V_i = 0`,
all modulo `D = p^E`.

`check` replays a trace with core-Lean data only (no `Array`, structural recursion, `Nat`
arithmetic), so that `decide +kernel` evaluates it in the kernel: no `native_decide`, no
`Lean.ofReduceBool`. Soundness of `check` (every vector lies in `J_k + p^E A_k^+`) is
`TraceReplay/Sound.lean`.

**Positions** (as in `cert/common.h`): a word of length `g` with letters `j_1 … j_g` (`0 ≤ j < d`)
sits at `off g + Σ j_i d^{g−i}`, the first letter most significant, `off g = Σ_{i<g} d^i`.

**Vectors** are sparse: lists of `(position, coefficient)` with coefficients in `[0, D)`. Any id that
is not found reads as the zero vector; this is sound (`0` lies in every `L_k`), so the replay needs
no well-formedness checks of its own beyond the ones listed in `check`. The one exception is a test
word: a missing one would be sound but vacuous, so `check` requires every member's word.
-/

namespace GroupDimension.TraceReplay

/-- A sparse vector: `(position, coefficient)` pairs. -/
abbrev Vec := List (Nat × Nat)

/-- The generator of a line. -/
inductive Gen where
  | zero
  | rel (i : Nat)
  /-- `X_j · V_id`, `V_id` of the previous level -/
  | lsh (id j : Nat)
  /-- `V_id · X_j` -/
  | rsh (id j : Nat)
  deriving Repr

/-- A line `v id u gen K id_1 c_1 …`. -/
structure Line where
  id : Nat
  u : Int
  gen : Gen
  terms : List (Nat × Int)
  deriving Repr

/-- A trace together with the part of the presentation it uses. Words are flat lists of
`(generator, exponent)`, generators `1..d`. -/
structure Trace where
  d : Nat
  n : Nat
  p : Nat
  E : Nat
  /-- `(i, r_i)`: the relators the trace uses, by their index in the presentation -/
  rels : List (Nat × List (Nat × Int))
  /-- `(t, w_t)`: the word tests claimed in -/
  tests : List (Nat × List (Nat × Int))
  /-- `(t, [(c_k, w_k)])`: the lintests claimed in, the elements `Σ c_k (w_k − 1)` -/
  lintests : List (Nat × List (Int × List (Nat × Int))) := []
  levels : List (Nat × List Line)
  F : List Nat
  xs : List (Nat × List (Nat × Int))
  ws : List (Nat × List (Nat × Int))
  deriving Repr

section Arith
variable (D : Nat)

/-- An integer modulo `D`, in `[0, D)`. -/
def red (a : Int) : Nat := (a % (D : Int)).toNat

/-- `Σ_{i<g} d^i`, the first position of degree `g`. -/
def off (d : Nat) : Nat → Nat
  | 0 => 0
  | g + 1 => off d g + d ^ g

/-- The degree of position `c` (at most `fuel + g`). -/
def degAux (d c : Nat) : Nat → Nat → Nat
  | 0, g => g
  | fuel + 1, g => bif Nat.blt c (off d (g + 1)) then g else degAux d c fuel (g + 1)

/-- The degree of position `c` (fuel `c + 1` always suffices, as `off d g ≥ g` for `d ≥ 1`). -/
def degOf (d c : Nat) : Nat := degAux d c (c + 1) 0

/-- Add `a · e_k` to a vector sorted by position, dropping zeros. -/
def ins (k a : Nat) : Vec → Vec
  | [] => bif a % D == 0 then [] else [(k, a % D)]
  | (k', b) :: t =>
    bif Nat.blt k k' then (bif a % D == 0 then (k', b) :: t else (k, a % D) :: (k', b) :: t)
    else bif k == k' then (let s := (a + b) % D; bif s == 0 then t else (k, s) :: t)
    else (k', b) :: ins k a t

/-- `w + a · v`. -/
def addSmul (a : Nat) (v w : Vec) : Vec := v.foldl (fun acc e => ins D e.1 (a * e.2) acc) w

/-- `a · v` (all entries reduced, zeros dropped). -/
def smul (a : Nat) (v : Vec) : Vec := addSmul D a v []

end Arith

/-- Look up a vector by id; a missing id reads as `0`. -/
def find (id : Nat) : List (Nat × Vec) → Vec
  | [] => []
  | (i, v) :: t => bif i == id then v else find id t

/-- `Σ c_i V_i + w`. -/
def combo (D : Nat) (cur : List (Nat × Vec)) (terms : List (Nat × Int)) (w : Vec) : Vec :=
  terms.foldl (fun acc t => addSmul D (red D t.2) (find t.1 cur) acc) w

section Magnus
variable (d n D : Nat)

/-- The generalised binomial coefficient `C(e, m)` (`e` any integer), exactly. -/
def descProd (e : Int) : Nat → Int
  | 0 => 1
  | m + 1 => descProd e m * (e - m)

def fact : Nat → Nat
  | 0 => 1
  | m + 1 => (m + 1) * fact m

def binom (e : Int) (m : Nat) : Int := descProd e m / (fact m : Int)

/-- The terms `a C(e,m) X_c X_j^m`, `m = 1 .. k − 1 − g`, of `X_c · (1 + X_j)^e`, below degree `k`;
`c` has degree `g`, and `idx` is the index (within its degree) of `X_c X_j^{m−1}`. -/
def genPowTerms (k j : Nat) (e : Int) (g a : Nat) : Nat → Nat → Nat → Vec → Vec
  | 0, _, _, acc => acc
  | fuel + 1, m, idx, acc =>
    bif Nat.blt (g + m) k then
      genPowTerms k j e g a fuel (m + 1) (idx * d + j)
        (ins D (off d (g + m) + (idx * d + j)) (a * red D (binom e m)) acc)
    else acc

/-- `x · (1 + X_j)^e`, truncated below degree `k`. -/
def mulGenPow (k j : Nat) (e : Int) (x : Vec) : Vec :=
  x.foldl (fun acc t =>
    let g := degOf d t.1
    genPowTerms d D k j e g t.2 k 1 (t.1 - off d g) acc) x

/-- `μ(w)`, truncated below degree `k` (generators `1..d`). -/
def magnus (k : Nat) (w : List (Nat × Int)) : Vec :=
  w.foldl (fun x f => mulGenPow d D k (f.1 - 1) f.2 x) [(0, 1)]

/-- `μ(w) − 1`, truncated below degree `k`. -/
def magnus1 (k : Nat) (w : List (Nat × Int)) : Vec := ins D 0 (D - 1) (magnus d D k w)

/-- `X_j · v` and `v · X_j` (no truncation: a level `k − 1` vector has degree `< k − 1`, and terms
of degree `≥ k` would lie in the target anyway). -/
def lshift (j : Nat) (v : Vec) : Vec :=
  v.foldl (fun acc t => let g := degOf d t.1
    ins D (off d (g + 1) + j * d ^ g + (t.1 - off d g)) t.2 acc) []

def rshift (j : Nat) (v : Vec) : Vec :=
  v.foldl (fun acc t => let g := degOf d t.1
    ins D (off d (g + 1) + (t.1 - off d g) * d + j) t.2 acc) []

end Magnus

/-- Look up a word by index; a missing one reads as the empty word (`μ − 1 = 0`). -/
def findWord (i : Nat) : List (Nat × List (Nat × Int)) → List (Nat × Int)
  | [] => []
  | (i', w) :: t => bif i' == i then w else findWord i t

/-- Look up a lintest by index; a missing one reads as the empty combination (`0`). -/
def findLin (i : Nat) : List (Nat × List (Int × List (Nat × Int))) → List (Int × List (Nat × Int))
  | [] => []
  | (i', l) :: t => bif i' == i then l else findLin i t

/-- Test `t` as a combination `Σ c_k (w_k − 1)`: a word test `w` is `[(1, w)]`; otherwise the
lintest `t`. -/
def testLin (T : Trace) (t : Nat) : List (Int × List (Nat × Int)) :=
  bif T.tests.any (fun y => y.1 == t) then [(1, findWord t T.tests)] else findLin t T.lintests

/-- `Σ c_k (μ(w_k) − 1)`, truncated below degree `k`. -/
def linVec (d D k : Nat) (l : List (Int × List (Nat × Int))) : Vec :=
  l.foldl (fun acc c => addSmul D (red D c.1) (magnus1 d D k c.2) acc) []

/-- The generator of a line at level `k`. Shifts with a letter `j ≥ d` read as `0`. -/
def genVec (T : Trace) (k : Nat) (prev : List (Nat × Vec)) : Gen → Vec
  | .zero => []
  | .rel i => magnus1 T.d (T.p ^ T.E) k (findWord i T.rels)
  | .lsh id j => bif Nat.blt j T.d then lshift T.d (T.p ^ T.E) j (find id prev) else []
  | .rsh id j => bif Nat.blt j T.d then rshift T.d (T.p ^ T.E) j (find id prev) else []

/-- One level: the vectors in order, each line seeing the earlier ones (newest first). -/
def runLevel (T : Trace) (k : Nat) (prev : List (Nat × Vec)) :
    List Line → List (Nat × Vec) → List (Nat × Vec)
  | [], cur => cur
  | l :: ls, cur =>
    let D := T.p ^ T.E
    let v := smul D (red D l.u) (combo D cur l.terms (genVec T k prev l.gen))
    runLevel T k prev ls ((l.id, v) :: cur)

/-- All levels, `k = 2, 3, …` in order; `none` if a level is out of order. Returns the vectors of
the last level and its `k`. -/
def runLevels (T : Trace) : List (Nat × List Line) → Nat → List (Nat × Vec) →
    Option (Nat × List (Nat × Vec))
  | [], k, prev => some (k, prev)
  | (k', ls) :: rest, k, prev =>
    bif k' == k + 1 then runLevels T rest k' (runLevel T k' prev ls []) else none

/-- The full check:
* the levels are `2, …, n`;
* every relator and test word uses generators `1..d` only, and `d ≥ 2`;
* the free columns `F` are positive (not the constant term);
* every `x` line: `p^{E−1} e_c + Σ c_i V_i` has no nonzero entry outside `F`, and every column
  `1 .. T − 1` is in `F` or has an `x` line;
* every test in `members` is present in `T.tests` with a non-empty word, or in `T.lintests` with a
  non-empty combination (a missing test would read as `0`, and its membership would say nothing),
  and has a `w` line with `x_t + Σ c_i V_i ≡ 0`, where `x_t` is `μ(w_t) − 1` for a word test and
  `Σ c_k (μ(w_k) − 1)` for a lintest (`testLin`, `linVec`).

With `F = []` (rank bound `0`) this is the whole exactness certificate. With `F ≠ []` the free
columns must be shown to meet the torsion trivially; that is `TraceReplay/HomExact.lean`. -/
def check (T : Trace) (members : List Nat) : Bool :=
  let D := T.p ^ T.E
  let okWord (w : List (Nat × Int)) := w.all fun f => Nat.blt 0 f.1 && Nat.ble f.1 T.d
  Nat.blt 1 T.d && Nat.blt 1 T.p && Nat.blt 0 T.E && Nat.blt 1 T.n && T.F.all (fun f => Nat.blt 0 f) &&
  T.rels.all (fun r => okWord r.2) && (T.tests.all (fun t => okWord t.2) && T.lintests.all (fun l => l.2.all (fun c => okWord c.2))) &&
  match runLevels T T.levels 1 [] with
  | none => false
  | some (k, cur) =>
    k == T.n &&
    T.xs.all (fun x => (combo D cur x.2 (ins D x.1 (T.p ^ (T.E - 1)) [])).all
      (fun e => T.F.any (fun f => f == e.1))) &&
    (List.range (off T.d T.n)).all (fun c => c == 0 || T.F.any (fun f => f == c) ||
      T.xs.any (fun x => x.1 == c)) &&
    members.all (fun t => (T.tests.any (fun y => y.1 == t && !y.2.isEmpty) ||
        T.lintests.any (fun y => y.1 == t && !y.2.isEmpty)) &&
      T.ws.any (fun w => w.1 == t &&
        (combo D cur w.2 (linVec T.d D T.n (testLin T t))).isEmpty))

end GroupDimension.TraceReplay
