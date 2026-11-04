module

public import GroupDimension.TraceReplay.PolyVanishBin

@[expose] public section

/-!
# `checkVanishB` with packed maps (MATH-314)

`checkMap` (PolyVanishDefs.lean) reads `λ` with `List.getD`, a walk along the list of values. For maps of
weight 4 with `d = 6` that list has 1554 entries and check 1 does about 4·10⁷ steps per relator, more than
the kernel can hold in memory for a handful of relators. `checkVanishE` is `checkVanishB` with two changes;
once `encsOk` holds, `checkVanishE = true` implies `checkVanishB = true` (`vanish_of_checkE`,
PolyVanishFastSound.lean):

* the values of each map are packed into one natural number `e`, `W` bits each with offset `B`, and read
  by a shift and a remainder (`lookL`), which the kernel does with GMP. The packing is checked against
  the list once (`encsOk`);
* for each `|U| = a`, `|V| = b` the terms of degree above `w − a − b`, which add nothing, are dropped once
  (`checkMapL`), not skipped again for every `U`, `V`.

Computable, no Mathlib import.
-/

namespace GroupDimension.TraceReplay

/-- Value `p` of a packed list: bits `[W p, W p + W)` of `e`, minus `B`. -/
def rawL (W B e p : Nat) : Int := Int.ofNat ((e >>> (W * p)) % 2 ^ W) - Int.ofNat B

/-- Value `p` of a packed list of length `len` (`0` past the end, as `List.getD`). -/
def lookL (W B len e p : Nat) : Int := bif Nat.blt p len then rawL W B e p else 0

/-- The packed values from position `p` on are the list. -/
def encOkAux (W B e : Nat) : Nat → List Int → Bool
  | _, [] => true
  | p, x :: l => rawL W B e p == x && encOkAux W B e (p + 1) l

/-- `encs` packs the values of `maps`, one `(W, B, e)` per map. -/
def encsOk (maps : List (Nat × List Int)) (encs : List (Nat × Nat × Nat)) : Bool :=
  maps.length == encs.length && (maps.zip encs).all fun me => encOkAux me.2.1 me.2.2.1 me.2.2.2 0 me.1.2

/-- `vanValD` with the values of the map read by `look`. -/
def vanValL (d w : Nat) (look : Nat → Int) (vd : List (Nat × Nat × Int)) (a u b vv : Nat) : Int :=
  vd.foldl (fun s t =>
    bif Nat.blt 0 (a + t.1 + b) && Nat.ble (a + t.1 + b) w then
      s + t.2.2 * look (off d (a + t.1 + b) + (u * d ^ t.1 + t.2.1) * d ^ b + vv - 1)
    else s) 0

/-- `checkMap` with the values read by `look`, and for each `a`, `b` only the terms of degree at most
`w − a − b`. -/
def checkMapL (d w : Nat) (look : Nat → Int) (vd : List (Nat × Nat × Int)) : Bool :=
  (List.range w).all fun a => (List.range (w - a)).all fun b =>
    let vf := vd.filter fun t => Nat.ble (a + t.1 + b) w
    (List.range (d ^ a)).all fun u => (List.range (d ^ b)).all fun vv => vanValL d w look vf a u b vv == 0

/-- `checkVanishRelB` with packed maps. -/
def checkVanishRelE (d K : Nat) (maps : List (Nat × List Int)) (encs : List (Nat × Nat × Nat))
    (r : List (List (Nat × Int) × Int)) : Bool :=
  let vd := withDeg d (subOne (magnusNB d K r))
  (maps.zip encs).all fun me =>
    Nat.ble (me.1.1 + 1) K && checkMapL d me.1.1 (lookL me.2.1 me.2.2.1 me.1.2.length me.2.2.2) vd

/-- `checkVanishB` with packed maps. -/
def checkVanishE (d K : Nat) (maps : List (Nat × List Int)) (encs : List (Nat × Nat × Nat))
    (rels : List (List (List (Nat × Int) × Int))) : Bool :=
  rels.all fun r => checkVanishRelE d K maps encs r

/-- `checkVanishE` over a concatenation. -/
theorem checkVanishE_append {d K : Nat} {maps : List (Nat × List Int)} {encs : List (Nat × Nat × Nat)}
    {a b : List (List (List (Nat × Int) × Int))}
    (ha : checkVanishE d K maps encs a = true) (hb : checkVanishE d K maps encs b = true) :
    checkVanishE d K maps encs (a ++ b) = true := by
  simp only [checkVanishE, List.all_append, Bool.and_eq_true] at *
  exact ⟨ha, hb⟩

end GroupDimension.TraceReplay
