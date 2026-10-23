module

@[expose] public section

/-!
# The certificate checker for Prop. 5.3 — the computational part

This file uses only Lean core (no Mathlib), so that it can be compiled to native code
(`precompileModules` in `lakefile.toml`) and `native_decide` runs it at native speed. The meaning
of every definition, and the soundness of the check, are in `GroupDimension/Cert1024/Check.lean`.

* `PcPres`: a pc presentation with relative orders `2` (masks of `g_k²` and `g_k⁻¹ g_l g_k`).
* `Mat r`: an `r × r` integer matrix; every matrix in the check is reduced, row `i` modulo
  `2^{a_i}` (the module `V = ⊕ ℤ/2^{a_i}`).
* `checkAux`: the check; `checkStr`: the check of one line of the data (format below).

Line format (written by `compute/cert1024/emit_lean.py` of dimension-subrings), numbers separated
by spaces:
  `id m pow_0 … pow_{m-1} conj_{0,1} … conj_{m-2,m-1} r a_0 … a_{r-1} C`
with `id = 1000·parent + k` (the group `PqDescendants(SmallGroup(512, parent) : StepSize := 1)[k]`),
`m = 10`, masks with bit `j` = exponent of `g_j`, and the `m` matrices `C_k` row-major.
-/

namespace GroupDimension.Cert1024

/-! ## Presentations -/

/-- A pc presentation with relative orders `2`: `pow[k]` is the mask of `g_k²`, `conj[k][l-k-1]`
the mask of `g_k⁻¹ g_l g_k` (`k < l`). -/
structure PcPres where
  pow : List Nat
  conj : List (List Nat)

def PcPres.powMask (P : PcPres) (k : Nat) : Nat := P.pow.getD k 0

def PcPres.conjMask (P : PcPres) (k l : Nat) : Nat := (P.conj.getD k []).getD (l - k - 1) 0

/-- The exponent vector of a mask. -/
def bits {m : Nat} (n : Nat) : Fin m → Bool := fun k => n.testBit k

/-- The words `w_k`, `w_{kl}` only involve generators after `g_k`. -/
def formatOK (m : Nat) (P : PcPres) : Bool :=
  (List.finRange m).all fun k =>
    (List.range (k.val + 1)).all (fun j => !(P.powMask k).testBit j) &&
    (List.finRange m).all fun l =>
      !(decide (k < l)) || (List.range (k.val + 1)).all (fun j => !(P.conjMask k l).testBit j)

/-! ## Reduced matrices -/

section Mat

variable {r : Nat}

/-- An `r × r` integer matrix. -/
abbrev Mat (r : Nat) := Vector (Vector Int r) r

/-- `δ_{ij}`. -/
def delta (i j : Fin r) : Int := if i = j then 1 else 0

/-- The reduced product. -/
def mmul (a : Fin r → Nat) (x y : Mat r) : Mat r :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    ((List.finRange r).map fun k => x[i][k] * y[k][j]).sum % (2 : Int) ^ a i

/-- The reduced identity. -/
def idM (a : Fin r → Nat) : Mat r :=
  Vector.ofFn fun i => Vector.ofFn fun j => delta i j % (2 : Int) ^ a i

/-- `x - 1`, reduced. -/
def subOne (a : Fin r → Nat) (x : Mat r) : Mat r :=
  Vector.ofFn fun i => Vector.ofFn fun j => (x[i][j] - delta i j) % (2 : Int) ^ a i

/-- The zero matrix. -/
def zeroM : Mat r := Vector.ofFn fun _ => Vector.ofFn fun _ => 0

/-- The inverse candidate `1 - N + N² - N³`, `N = x - 1` (it is checked, not trusted). -/
def invM (a : Fin r → Nat) (x : Mat r) : Mat r :=
  let n := subOne a x
  let n2 := mmul a n n
  let n3 := mmul a n2 n
  Vector.ofFn fun i => Vector.ofFn fun j =>
    (delta i j - n[i][j] + n2[i][j] - n3[i][j]) % (2 : Int) ^ a i

/-- Well defined on `V`: `2^{a_i} ∣ x_{ij} 2^{a_j}`. -/
def wdB (a : Fin r → Nat) (x : Mat r) : Bool :=
  (List.finRange r).all fun i => (List.finRange r).all fun j =>
    (x[i][j] * (2 : Int) ^ a j) % (2 : Int) ^ a i == 0

/-- The normal word `C_i^{e_i} ⋯ C_{m-1}^{e_{m-1}}`, reduced. -/
def nwMat {m : Nat} (a : Fin r → Nat) (C : Fin m → Mat r) (e : Fin m → Bool) (i : Nat) : Mat r :=
  if h : i < m then
    (if e ⟨i, h⟩ then mmul a (C ⟨i, h⟩) (nwMat a C e (i + 1)) else nwMat a C e (i + 1))
  else idM a
termination_by m - i

end Mat

/-- `b, f_0, f_1, …` -/
def consB {m : Nat} (b : Bool) (f : Fin m → Bool) : Fin (m + 1) → Bool :=
  fun i => if h : i.val = 0 then b else f ⟨i.val - 1, by omega⟩

/-- All exponent vectors `Fin m → Bool`. -/
def allFns : (m : Nat) → List (Fin m → Bool)
  | 0 => [fun _ => false]
  | m + 1 => (allFns m).flatMap fun f => [consB false f, consB true f]

/-! ## The check -/

section Check

variable {r : Nat}

/-- The conditions on one generator `C_k`: well defined, invertible (with the computed inverse),
the power relation, and the conjugation relations with the later generators. -/
def genOK (m : Nat) (P : PcPres) (a : Fin r → Nat) (C : Fin m → Mat r) (k : Fin m) : Bool :=
  wdB a (C k) && wdB a (invM a (C k)) &&
    mmul a (C k) (invM a (C k)) == idM a && mmul a (invM a (C k)) (C k) == idM a &&
    mmul a (C k) (C k) == nwMat a C (bits (P.powMask k)) 0 &&
    (List.finRange m).all fun l => !(decide (k < l)) ||
      mmul a (C l) (C k) == mmul a (C k) (nwMat a C (bits (P.conjMask k l)) 0)

/-! ### Nilpotency: spanning sets of `Δ^d V`

`Δ^c V = 0` (`Δ` the augmentation ideal, acting through `C_k ↦ N_k = C_k - 1`) is checked on a
spanning set: `B_0` is the standard basis of `ℤ^r`, and `B_{d+1}` is built from the vectors
`N_k b` (`k < m`, `b ∈ B_d`), each reduced against the vectors already taken and kept only if
the remainder is not `0`. The reduction subtracts multiples of vectors already in `B_{d+1}`, so
the subgroup generated by `B_{d+1}` contains every `N_k b`; then `N_{k_1} ⋯ N_{k_d} V` lies in the
subgroup generated by `B_d` (`nilSpan_sound` in `Check.lean`), and the check is `B_c = []`. How
the multiples are chosen (`coefV`, an echelon-type pivot rule) does not matter for soundness. -/

/-- A vector of `ℤ^r` (read in `V`). -/
abbrev Vec (r : Nat) := Vector Int r

/-- The reduced product `x v`. -/
def mvec (a : Fin r → Nat) (x : Mat r) (v : Vec r) : Vec r :=
  Vector.ofFn fun i => ((List.finRange r).map fun k => x[i][k] * v[k]).sum % (2 : Int) ^ a i

/-- The zero vector. -/
def zeroV : Vec r := Vector.ofFn fun _ => 0

/-- `u - c b`, reduced. -/
def axpy (a : Fin r → Nat) (c : Int) (b u : Vec r) : Vec r :=
  Vector.ofFn fun i => (u[i] - c * b[i]) % (2 : Int) ^ a i

/-- The first nonzero coordinate. -/
def pivotV (v : Vec r) : Option (Fin r) := (List.finRange r).find? fun i => v[i] != 0

/-- The `2`-adic valuation of `n ≠ 0` (at most `fuel`). -/
def val2 : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n != 0 && n % 2 == 0 then val2 fuel (n / 2) + 1 else 0

/-- An inverse of an odd `u` modulo `M = 2^e`, `e ≤ 96` (Newton's iteration; not trusted). -/
def invOdd (u M : Int) : Int :=
  let step := fun x : Int => (x * (2 - u * x)) % M
  step (step (step (step (step (u % M)))))

/-- The multiple of `b` to subtract from `u`: at the pivot `i` of `b`, with `b_i = 2^t·odd`, it
kills `u_i` modulo `2^{a_i}` if `2^t ∣ u_i`. (Any integer would be sound.) -/
def coefV (a : Fin r → Nat) (b u : Vec r) : Int :=
  match pivotV b with
  | none => 0
  | some i =>
    let M : Int := 2 ^ a i
    let bi := b[i] % M
    let P : Int := 2 ^ val2 64 bi.toNat
    let ui := u[i] % M
    if ui % P == 0 then (ui / P * invOdd (bi / P) M) % M else 0

/-- The sort key of a vector: its pivot, then the valuation there. -/
def keyV (a : Fin r → Nat) (b : Vec r) : Nat :=
  match pivotV b with
  | none => 0
  | some i => i.val * 128 + val2 64 (b[i] % (2 : Int) ^ a i).toNat

/-- Insert into a list sorted by `keyV`. -/
def insV (a : Fin r → Nat) (w : Vec r) : List (Vec r) → List (Vec r)
  | [] => [w]
  | b :: B => if keyV a w ≤ keyV a b then w :: b :: B else b :: insV a w B

/-- `u` reduced against `B` (in order). -/
def reduceV (a : Fin r → Nat) (B : List (Vec r)) (u : Vec r) : Vec r :=
  B.foldl (fun u b => axpy a (coefV a b u) b u) u

/-- Add `u` to the spanning set `B`: its remainder, unless that is `0`. -/
def addV (a : Fin r → Nat) (B : List (Vec r)) (u : Vec r) : List (Vec r) :=
  let w := reduceV a B u
  if w == zeroV then B else insV a w B

/-- `B_{d+1}` from `B_d`. -/
def spanStep (a : Fin r → Nat) (Ns : List (Mat r)) (B : List (Vec r)) : List (Vec r) :=
  (B.flatMap fun b => Ns.map fun n => mvec a n b).foldl (addV a) []

/-- `B_d`. -/
def spanIter (a : Fin r → Nat) (Ns : List (Mat r)) : Nat → List (Vec r) → List (Vec r)
  | 0, B => B
  | d + 1, B => spanStep a Ns (spanIter a Ns d B)

/-- The standard basis of `ℤ^r`. -/
def basisV (r : Nat) : List (Vec r) :=
  (List.finRange r).map fun i => Vector.ofFn fun j => if i = j then 1 else 0

/-- `Δ^c V = 0`: the spanning set at depth `c` is empty. -/
def nilSpan (m : Nat) (a : Fin r → Nat) (C : Fin m → Mat r) (c : Nat) : Bool :=
  (spanIter a ((List.finRange m).map fun k => subOne a (C k)) c (basisV r)).isEmpty

/-- `Δ⁴ V = 0`, so every product of four matrices `C_k - 1` is `0` on `V` (`nilSpan_sound`). -/
def nilOK (m : Nat) (a : Fin r → Nat) (C : Fin m → Mat r) : Bool := nilSpan m a C 4

/-- The words of length `c` in `Fin m`. -/
def wordsOf (m : Nat) : Nat → List (List (Fin m))
  | 0 => [[]]
  | c + 1 => (wordsOf m c).flatMap fun l => (List.finRange m).map (· :: l)

/-- The unpruned check, for the negative controls only (`Test/Tamper.lean`): every product of
`c` matrices `C_k - 1` is `0`, computed one product at a time (`m^c` products). -/
def nilFull (m : Nat) (a : Fin r → Nat) (C : Fin m → Mat r) (c : Nat) : Bool :=
  (wordsOf m c).all fun l => l.foldr (fun k X => mmul a (subOne a (C k)) X) (idM a) == zeroM

/-- The `2^m` normal words act by pairwise distinct operators. -/
def faithOK (m : Nat) (a : Fin r → Nat) (C : Fin m → Mat r) : Bool :=
  decide ((allFns m).map fun e => nwMat a C e 0).Nodup

/-- The check. -/
def checkAux (m : Nat) (P : PcPres) (a : Fin r → Nat) (C : Fin m → Mat r) : Bool :=
  formatOK m P && ((List.finRange m).all (genOK m P a C) && (nilOK m a C && faithOK m a C))

end Check

/-! ## Decoding a line -/

/-- The numbers of a line. -/
def nums (s : String) : List Nat := (s.splitOn " ").filterMap String.toNat?

/-- The number of pc generators (always `10` here). -/
abbrev M : Nat := 10

/-- The pc presentation of a line. -/
def presOf (s : String) : PcPres :=
  let xs := (nums s).drop 2
  let c := xs.drop M
  { pow := xs.take M
    conj := (List.range M).map fun k =>
      (c.drop (k * M - k * (k + 1) / 2)).take (M - k - 1) }

/-- The rank `r` of the module. -/
def rankOf (s : String) : Nat := ((nums s).drop (2 + M + M * (M - 1) / 2)).headD 0

/-- The numbers after the rank. -/
def tailOf (s : String) : Array Nat := ((nums s).drop (3 + M + M * (M - 1) / 2)).toArray

/-- The exponents `a_i` (from `tailOf s`). -/
def modsOfArr (r : Nat) (ys : Array Nat) : Vector Nat r := Vector.ofFn fun i => ys.getD i 0

/-- The matrices `C_k` (from `tailOf s`). -/
def matsOfArr (r : Nat) (ys : Array Nat) : Vector (Mat r) M :=
  Vector.ofFn fun k => Vector.ofFn fun i => Vector.ofFn fun j =>
    ((ys.getD (r + k.val * r * r + i.val * r + j.val) 0 : Nat) : Int)

/-- The check of one line, all data materialised (passed as arguments, so computed once). -/
def checkVec (P : PcPres) {r : Nat} (av : Vector Nat r) (Cs : Vector (Mat r) M) : Bool :=
  checkAux M P (fun i => av[i]) fun k => Cs[k]

/-- The exponents `a_i` of a line. -/
def modsOf (s : String) : Vector Nat (rankOf s) := modsOfArr (rankOf s) (tailOf s)

/-- The matrices `C_k` of a line. -/
def matsOf (s : String) : Vector (Mat (rankOf s)) M := matsOfArr (rankOf s) (tailOf s)

/-- The line is well formed: every token is a natural number, `m = 10`, and there are exactly
`2 + M + M(M-1)/2 + 1 + r + M r²` numbers. (Not needed for soundness, which holds for any string;
it makes Lean read a line exactly as `verify_lines.g` in GAP does.) -/
def wellFormed (s : String) : Bool :=
  let r := rankOf s
  (s.splitOn " ").all (fun t => t.toNat?.isSome) &&
    (nums s)[1]? == some M &&
    (nums s).length == 3 + M + M * (M - 1) / 2 + r + M * r * r

/-- The check of one line of the data. -/
def checkStr (s : String) : Bool :=
  wellFormed s && checkVec (presOf s) (modsOf s) (matsOf s)

end GroupDimension.Cert1024
