module

public import GroupDimension.TraceReplay.PolyVanish
public import GroupDimension.TraceReplay.PolyVanishFast

@[expose] public section

/-!
# Soundness of `checkVanishE` (MATH-314)

`checkVanishE` (PolyVanishFast.lean) and `checkVanishB` have the same value once `encsOk` holds: the packed
values read back as the list (`lookL_eq`), and the terms `checkMapL` drops add nothing to `vanValD`
(`vanValL_filter`). So `vanish_of_checkE` is `vanish_of_checkB`.
-/

namespace GroupDimension.TraceReplay

theorem rawL_of_encOkAux {W B e : ℕ} : ∀ (q : ℕ) (l : List ℤ), encOkAux W B e q l = true →
    ∀ (i : ℕ) (h : i < l.length), rawL W B e (q + i) = l[i]
  | _, [], _, i, h => by simp at h
  | q, x :: l, hl, i, h => by
    simp only [encOkAux, Bool.and_eq_true, beq_iff_eq] at hl
    cases i with
    | zero => simpa using hl.1
    | succ i =>
      have := rawL_of_encOkAux (q + 1) l hl.2 i (by simpa using h)
      rw [show q + (i + 1) = q + 1 + i by omega, this]
      simp

/-- The packed values read back as the list. -/
theorem lookL_eq {W B e : ℕ} {l : List ℤ} (h : encOkAux W B e 0 l = true) (p : ℕ) :
    lookL W B l.length e p = l.getD p 0 := by
  unfold lookL
  cases hb : Nat.blt p l.length
  · rw [← Bool.not_eq_true, Nat.blt_eq] at hb
    rw [cond_false, List.getD_eq_default _ _ (by omega)]
  · rw [Nat.blt_eq] at hb
    rw [cond_true, List.getD_eq_getElem _ _ hb, ← rawL_of_encOkAux 0 l h p hb, Nat.zero_add]

theorem foldl_filter_of_skip {α β : Type*} (f : β → α → β) (q : α → Bool)
    (hq : ∀ s t, q t = false → f s t = s) : ∀ (l : List α) (s : β), (l.filter q).foldl f s = l.foldl f s
  | [], _ => rfl
  | t :: l, s => by
    cases h : q t
    · rw [List.filter_cons_of_neg (by simp [h]), List.foldl_cons, hq s t h, foldl_filter_of_skip f q hq l s]
    · rw [List.filter_cons_of_pos h, List.foldl_cons, List.foldl_cons, foldl_filter_of_skip f q hq l]

/-- The terms of degree above `w − a − b` add nothing. -/
theorem vanValL_filter (d w : ℕ) (look : ℕ → ℤ) (vd : List (ℕ × ℕ × ℤ)) (a u b vv : ℕ) :
    vanValL d w look (vd.filter fun t => Nat.ble (a + t.1 + b) w) a u b vv = vanValL d w look vd a u b vv := by
  unfold vanValL
  exact foldl_filter_of_skip _ _ (fun s t ht => by simp only [ht, Bool.and_false, cond_false]) vd 0

theorem vanValL_getD (d : ℕ) (m : ℕ × List ℤ) (vd : List (ℕ × ℕ × ℤ)) (a u b vv : ℕ) :
    vanValL d m.1 (fun p => m.2.getD p 0) vd a u b vv = vanValD d m vd a u b vv := rfl

theorem checkMap_of_checkMapL {d : ℕ} {m : ℕ × List ℤ} {look : ℕ → ℤ} (hl : ∀ p, look p = m.2.getD p 0)
    {vd : List (ℕ × ℕ × ℤ)} (h : checkMapL d m.1 look vd = true) : checkMap d m vd = true := by
  have hlook : look = fun p => m.2.getD p 0 := funext hl
  subst hlook
  simp only [checkMapL, checkMap, List.all_eq_true, List.mem_range, beq_iff_eq] at h ⊢
  intro a ha b hb u hu vv hv
  have := h a ha b hb u hu vv hv
  rwa [vanValL_filter, vanValL_getD] at this

theorem exists_mem_zip {α β : Type*} :
    ∀ (l : List α) (l' : List β), l.length = l'.length → ∀ x ∈ l, ∃ y, (x, y) ∈ l.zip l'
  | [], _, _, x, hx => by simp at hx
  | _ :: _, [], h, _, _ => by simp at h
  | a :: l, b :: l', h, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, by simp⟩
    · obtain ⟨y, hy⟩ := exists_mem_zip l l' (by simpa using h) x hx
      exact ⟨y, by simp [hy]⟩

/-- **Soundness of `checkVanishE`.** -/
theorem vanish_of_checkE {d : ℕ} [NeZero d] {K : ℕ} {maps : List (ℕ × List ℤ)} {encs : List (ℕ × ℕ × ℕ)}
    {rels : List (List (List (ℕ × ℤ) × ℤ))} (hE : encsOk maps encs = true)
    (h : checkVanishE d K maps encs rels = true) : ∀ m ∈ maps, Vanish (relSetN d rels) m := by
  apply vanish_of_checkB (K := K)
  simp only [encsOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hE
  obtain ⟨hlen, hok⟩ := hE
  simp only [checkVanishB, checkVanishE, List.all_eq_true] at h ⊢
  intro r hr
  have hr' := h r hr
  simp only [checkVanishRelE, checkVanishRelB, List.all_eq_true, Bool.and_eq_true] at hr' ⊢
  intro m hm
  obtain ⟨y, hz⟩ := exists_mem_zip maps encs hlen m hm
  obtain ⟨hK, hc⟩ := hr' _ hz
  exact ⟨hK, checkMap_of_checkMapL (lookL_eq (hok _ hz)) hc⟩

end GroupDimension.TraceReplay
