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

/-- Every product of four matrices `C_k - 1` is `0` on `V`. -/
def nilOK (m : Nat) (a : Fin r → Nat) (C : Fin m → Mat r) : Bool :=
  (List.finRange m).all fun k1 => (List.finRange m).all fun k2 => (List.finRange m).all fun k3 =>
    (List.finRange m).all fun k4 =>
      mmul a (subOne a (C k1)) (mmul a (subOne a (C k2)) (mmul a (subOne a (C k3))
        (mmul a (subOne a (C k4)) (idM a)))) == zeroM

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
