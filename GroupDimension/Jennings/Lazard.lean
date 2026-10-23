module

public import GroupDimension.Candidate

@[expose] public section

/-!
# The smallest restricted N-series (Lazard)

For a prime `p` and a group `G`, `lazard p G n` is defined by strong recursion:
`S₀ = S₁ = G` and, for `n ≥ 2`,

  `S_n = ∏_{1 ≤ a, b < n ≤ a + b} [S_a, S_b] · ∏_{1 ≤ a < n ≤ p a} S_a^p`.

By construction it is a restricted N-series: `S` is normal and decreasing,
`[S_a, S_b] ≤ S_{a+b}` (`lazard_comm`) and `S_a^p ≤ S_{pa}` (`lazard_pow`); every restricted
N-series contains it (`lazard_le_of_restrictedSeries`, `Theorem.lean`). The general facts on
`powSubgroup` and `iSup` proved here (`normal_iSup`, `powSubgroup_mono`, `map_powSubgroup`) are
used only for this series. For a finite `p`-group it reaches `1` (`lazard_eventually_bot`): `S_n` lies
in the term `P_{m+1}` of the lower exponent-`p` central series when `p^m ≤ n`, and `P` reaches `1`.

This is the series used for Jennings' theorem (D5-32): the Jennings basis of `𝔽_p[G]` gives
`G ∩ (1 + Δ_{𝔽_p}^n) ≤ S_n`. That `S_n = ∏_{i p^j ≥ n} γ_i^{p^j}` is Lazard's theorem and is not
formalized here; the case needed for candidates (`p = 2`, `n = 5`, class `≤ 3`) is
`ClassThree.lean`.
-/

namespace GroupDimension

open Subgroup
open scoped commutatorElement

variable (p : ℕ) (G : Type*) [Group G]

/-- The smallest restricted N-series of `G` (see the file header). -/
def lazard (n : ℕ) : Subgroup G :=
  if n ≤ 1 then ⊤ else
    (⨆ (a : Fin n) (b : Fin n) (_ : 1 ≤ (a : ℕ) ∧ 1 ≤ (b : ℕ) ∧ n ≤ a + b),
        ⁅lazard a, lazard b⁆) ⊔
      ⨆ (a : Fin n) (_ : 1 ≤ (a : ℕ) ∧ n ≤ p * a), powSubgroup (lazard a) p
termination_by n
decreasing_by all_goals exact Fin.isLt _

variable {p G}

theorem lazard_of_le_one {n : ℕ} (h : n ≤ 1) : lazard p G n = ⊤ := by
  rw [lazard, if_pos h]

theorem lazard_one : lazard p G 1 = ⊤ := lazard_of_le_one le_rfl

theorem lazard_eq {n : ℕ} (h : 2 ≤ n) : lazard p G n =
    (⨆ (a : Fin n) (b : Fin n) (_ : 1 ≤ (a : ℕ) ∧ 1 ≤ (b : ℕ) ∧ n ≤ a + b),
        ⁅lazard p G a, lazard p G b⁆) ⊔
      ⨆ (a : Fin n) (_ : 1 ≤ (a : ℕ) ∧ n ≤ p * a), powSubgroup (lazard p G a) p := by
  rw [lazard, if_neg (by omega)]

theorem commutator_lazard_le {a b n : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (han : a < n) (hbn : b < n)
    (h : n ≤ a + b) : ⁅lazard p G a, lazard p G b⁆ ≤ lazard p G n := by
  rw [lazard_eq (n := n) (by omega)]
  refine le_sup_of_le_left ?_
  refine le_iSup_of_le (⟨a, han⟩ : Fin n) ?_
  refine le_iSup_of_le (⟨b, hbn⟩ : Fin n) ?_
  exact le_iSup_of_le (⟨ha, hb, h⟩ : 1 ≤ a ∧ 1 ≤ b ∧ n ≤ a + b) le_rfl

theorem powSubgroup_lazard_le {a n : ℕ} (ha : 1 ≤ a) (han : a < n) (h : n ≤ p * a) :
    powSubgroup (lazard p G a) p ≤ lazard p G n := by
  rw [lazard_eq (n := n) (by omega)]
  refine le_sup_of_le_right ?_
  refine le_iSup_of_le (⟨a, han⟩ : Fin n) ?_
  exact le_iSup_of_le (⟨ha, h⟩ : 1 ≤ a ∧ n ≤ p * a) le_rfl

/-- To bound `S_n` (`n ≥ 2`) it suffices to bound its generating pieces. -/
theorem lazard_le {n : ℕ} (hn : 2 ≤ n) {K : Subgroup G}
    (hc : ∀ a b, 1 ≤ a → 1 ≤ b → a < n → b < n → n ≤ a + b → ⁅lazard p G a, lazard p G b⁆ ≤ K)
    (hp : ∀ a, 1 ≤ a → a < n → n ≤ p * a → powSubgroup (lazard p G a) p ≤ K) :
    lazard p G n ≤ K := by
  rw [lazard_eq hn]
  exact sup_le (iSup_le fun a => iSup_le fun b => iSup_le fun h =>
      hc a b h.1 h.2.1 a.isLt b.isLt h.2.2)
    (iSup_le fun a => iSup_le fun h => hp a h.1 a.isLt h.2)

/-! ## Normality -/

theorem normal_iSup {ι : Sort*} (f : ι → Subgroup G) (hf : ∀ i, (f i).Normal) :
    (⨆ i, f i).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hle : (⨆ i, f i).map (MulAut.conj g).toMonoidHom ≤ ⨆ i, f i := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun i => le_iSup_of_le i ?_
    rintro _ ⟨y, hy, rfl⟩
    simpa using (hf i).conj_mem y hy g
  simpa using hle (mem_map_of_mem _ hx)

theorem lazard_normal (n : ℕ) : (lazard p G n).Normal := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n ≤ 1
    · rw [lazard_of_le_one hn]; infer_instance
    · rw [lazard_eq (by omega)]
      refine @Subgroup.sup_normal G _ _ _ ?_ ?_
      · exact normal_iSup _ fun a => normal_iSup _ fun b => normal_iSup _ fun _ => by
          haveI := ih a a.isLt
          haveI := ih b b.isLt
          infer_instance
      · exact normal_iSup _ fun a => normal_iSup _ fun _ => by
          haveI := ih a a.isLt
          exact powSubgroup_normal _ _

instance (n : ℕ) : (lazard p G n).Normal := lazard_normal n

/-! ## The restricted N-series properties -/

theorem lazard_succ_le {n : ℕ} (hn : 1 ≤ n) : lazard p G (n + 1) ≤ lazard p G n := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · rw [show n = 1 by omega, lazard_one]; exact le_top
  refine lazard_le (by omega) (fun a b ha hb han hbn h => ?_) (fun a ha han h => ?_)
  · rcases Nat.lt_or_ge a n with ha' | ha'
    · rcases Nat.lt_or_ge b n with hb' | hb'
      · exact commutator_lazard_le ha hb ha' hb' (by omega)
      · rw [show b = n by omega]; exact commutator_le_right _ _
    · rw [show a = n by omega]; exact commutator_le_left _ _
  · rcases Nat.lt_or_ge a n with ha' | ha'
    · exact powSubgroup_lazard_le ha ha' (by omega)
    · rw [show a = n by omega]; exact powSubgroup_le _ _

theorem lazard_antitone {m n : ℕ} (hm : 1 ≤ m) (h : m ≤ n) : lazard p G n ≤ lazard p G m := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih => exact (lazard_succ_le (by omega)).trans ih

/-- `[S_a, S_b] ≤ S_{a+b}`. -/
theorem lazard_comm {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {x y : G} (hx : x ∈ lazard p G a)
    (hy : y ∈ lazard p G b) : ⁅x, y⁆ ∈ lazard p G (a + b) :=
  commutator_lazard_le ha hb (by omega) (by omega) le_rfl (commutator_mem_commutator hx hy)

/-- `S_a^p ≤ S_{pa}`. -/
theorem lazard_pow (hp : 2 ≤ p) {a : ℕ} (ha : 1 ≤ a) {x : G} (hx : x ∈ lazard p G a) :
    x ^ p ∈ lazard p G (p * a) := by
  have : 2 * a ≤ p * a := Nat.mul_le_mul_right a hp
  exact powSubgroup_lazard_le ha (by omega) le_rfl (pow_mem_powSubgroup hx p)

/-! ## In a finite `p`-group `S` reaches `1` -/

theorem powSubgroup_mono {H K : Subgroup G} (h : H ≤ K) (m : ℕ) :
    powSubgroup H m ≤ powSubgroup K m :=
  (closure_le _).mpr fun _ ⟨_, hx, hg⟩ => hg ▸ pow_mem_powSubgroup (h hx) m

theorem map_powSubgroup {H : Type*} [Group H] (f : G →* H) (K : Subgroup G) (m : ℕ) :
    (powSubgroup K m).map f = powSubgroup (K.map f) m := by
  rw [powSubgroup, MonoidHom.map_closure, powSubgroup]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨f x, mem_map_of_mem f hx, by rw [map_pow]⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x ^ m, ⟨x, hx, rfl⟩, map_pow f x m⟩

/-- `S_n ≤ P_{m+1}` when `p^m ≤ n`. -/
theorem lazard_le_expCentral (hp : 2 ≤ p) :
    ∀ m n, 1 ≤ n → p ^ m ≤ n → lazard p G n ≤ expCentral p G (m + 1)
  | 0, _, _, _ => le_top.trans expCentral_one.ge
  | m + 1, n, hn, hpn => by
    have hpm : 2 * p ^ m ≤ p ^ (m + 1) := by
      rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_left _ hp
    have h1 : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by omega)
    have hP : 1 ≤ m + 1 := by omega
    refine lazard_le (by omega) (fun a b ha hb _ _ hab => ?_) (fun a ha _ h => ?_)
    · rcases le_or_gt (p ^ m) a with hpa | hpa
      · calc ⁅lazard p G a, lazard p G b⁆ ≤ ⁅expCentral p G (m + 1), ⊤⁆ :=
            commutator_mono (lazard_le_expCentral hp m a ha hpa) le_top
          _ ≤ expCentral p G (m + 1 + 1) := by rw [expCentral_succ hP]; exact le_sup_left
      · have hpb : p ^ m ≤ b := by omega
        calc ⁅lazard p G a, lazard p G b⁆ ≤ ⁅⊤, expCentral p G (m + 1)⁆ :=
            commutator_mono le_top (lazard_le_expCentral hp m b hb hpb)
          _ = ⁅expCentral p G (m + 1), ⊤⁆ := commutator_comm _ _
          _ ≤ expCentral p G (m + 1 + 1) := by rw [expCentral_succ hP]; exact le_sup_left
    · have hpa : p ^ m ≤ a := by
        have : p * p ^ m ≤ p * a := by rw [← pow_succ']; omega
        exact Nat.le_of_mul_le_mul_left this (by omega)
      calc powSubgroup (lazard p G a) p ≤ powSubgroup (expCentral p G (m + 1)) p :=
          powSubgroup_mono (lazard_le_expCentral hp m a ha hpa) p
        _ ≤ expCentral p G (m + 1 + 1) := by rw [expCentral_succ hP]; exact le_sup_right

/-- In a finite `p`-group a normal subgroup `N` with `N = [N, G] N^p` is trivial. -/
theorem eq_bot_of_eq_commutator_sup_pow [hp : Fact p.Prime] [Finite G] (hG : IsPGroup p G)
    {N : Subgroup G} [N.Normal] (hN : N = ⁅N, ⊤⁆ ⊔ powSubgroup N p) : N = ⊥ := by
  set K : Subgroup G := ⁅N, ⊤⁆ with hK
  let π := QuotientGroup.mk' K
  set M : Subgroup (G ⧸ K) := N.map π with hMdef
  -- `M = M^p`, and `M` is central
  have hM : M = powSubgroup M p := by
    have h2 := congrArg (Subgroup.map π) hN
    rw [Subgroup.map_sup, map_powSubgroup, QuotientGroup.map_mk'_self, bot_sup_eq] at h2
    rw [hMdef]
    exact h2
  have hcent : ∀ y ∈ M, ∀ z : G ⧸ K, Commute y z := by
    rintro _ ⟨x, hx, rfl⟩ z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K z
    have : ⁅x, g⁆ ∈ K := commutator_mem_commutator hx (mem_top g)
    have h1 : π ⁅x, g⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr this
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  -- the `p`-th power map of `M` is onto, hence one-to-one
  have hsurj : Function.Surjective fun z : M => z ^ p := by
    intro y
    have hy : (y : G ⧸ K) ∈ powSubgroup M p := by rw [← hM]; exact y.2
    have key : ∀ w ∈ powSubgroup M p, ∃ h ∈ M, h ^ p = w := by
      intro w hw
      induction hw using Subgroup.closure_induction with
      | mem x hx => exact hx
      | one => exact ⟨1, one_mem _, one_pow p⟩
      | mul x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        exact ⟨a * b, mul_mem ha hb, ((hcent a ha b).mul_pow p)⟩
      | inv x _ hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        exact ⟨a⁻¹, inv_mem ha, inv_pow a p⟩
    obtain ⟨h, hh, hhy⟩ := key _ hy
    exact ⟨⟨h, hh⟩, Subtype.ext (by simpa using hhy)⟩
  have hinj : Function.Injective fun z : M => z ^ p := Finite.injective_iff_surjective.mpr hsurj
  have hMbot : M = ⊥ := by
    by_contra hne
    haveI : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).mpr hne
    have hMp : IsPGroup p M := (hG.to_quotient K).to_subgroup M
    obtain ⟨e, he, hcard⟩ := hMp.nontrivial_iff_card.mp inferInstance
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := M) p
      (by rw [hcard]; exact dvd_pow_self p he.ne')
    have : y = 1 := hinj (show y ^ p = (1 : M) ^ p by rw [← hy, pow_orderOf_eq_one, one_pow])
    rw [this, orderOf_one] at hy
    exact hp.out.one_lt.ne hy
  -- so `N ≤ [N, G]`, and `N` lies in every term of the lower central series
  have hNK : N ≤ K := fun x hx => by
    have : π x ∈ M := mem_map_of_mem π hx
    rw [hMbot, mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).mp this
  have hlcs : ∀ j, N ≤ (⊤ : Subgroup G).lowerCentralSeries j := by
    intro j
    induction j with
    | zero => exact le_top.trans (Subgroup.lowerCentralSeries_zero ⊤).ge
    | succ j ih =>
      exact hNK.trans (by rw [Subgroup.lowerCentralSeries_succ]; exact commutator_mono ih le_rfl)
  obtain ⟨j, hj⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hG.isNilpotent
  exact eq_bot_iff.mpr ((hlcs j).trans hj.le)

/-- In a finite `p`-group the lower exponent-`p` central series reaches `1`. -/
theorem expCentral_eventually_bot [Fact p.Prime] [Finite G] (hG : IsPGroup p G) :
    ∃ c, expCentral p G c = ⊥ := by
  obtain ⟨k, hk1, hk⟩ : ∃ k, 1 ≤ k ∧ expCentral p G (k + 1) = expCentral p G k := by
    by_contra hno
    have hno' : ∀ k, 1 ≤ k → expCentral p G (k + 1) ≠ expCentral p G k :=
      fun k hk h => hno ⟨k, hk, h⟩
    have hcard : ∀ k, Nat.card (expCentral p G (k + 1)) + k ≤ Nat.card G := by
      intro k
      induction k with
      | zero => simp [expCentral_one]
      | succ k ih =>
        have hle : expCentral p G (k + 1 + 1) ≤ expCentral p G (k + 1) :=
          expCentral_antitone (by omega)
        have hlt : Nat.card (expCentral p G (k + 1 + 1)) < Nat.card (expCentral p G (k + 1)) := by
          rcases lt_or_eq_of_le (card_le_of_le hle) with h | h
          · exact h
          · exact absurd (eq_of_le_of_card_ge hle h.ge) (hno' (k + 1) (by omega))
        omega
    have := hcard (Nat.card G)
    have hpos : 0 < Nat.card (expCentral p G (Nat.card G + 1)) := Nat.card_pos
    omega
  refine ⟨k, eq_bot_of_eq_commutator_sup_pow hG ?_⟩
  rw [← expCentral_succ hk1, hk]

/-- In a finite `p`-group `S_n = 1` for large `n`. -/
theorem lazard_eventually_bot [hp : Fact p.Prime] [Finite G] (hG : IsPGroup p G) :
    ∃ n, lazard p G n = ⊥ := by
  obtain ⟨c, hc⟩ := expCentral_eventually_bot hG
  refine ⟨p ^ c, eq_bot_iff.mpr ?_⟩
  calc lazard p G (p ^ c) ≤ expCentral p G (c + 1) :=
      lazard_le_expCentral hp.out.two_le c _ (Nat.one_le_pow _ _ hp.out.pos) le_rfl
    _ ≤ expCentral p G c := expCentral_antitone (by omega)
    _ = ⊥ := hc

end GroupDimension
