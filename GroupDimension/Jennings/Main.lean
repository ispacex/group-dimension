module

public import GroupDimension.Jennings.Layers

@[expose] public section

/-!
# Jennings' theorem: `G ∩ (1 + Δ_{𝔽_p}^n) ≤ S n`

For a restricted N-series `S` of a finite `p`-group `G` ([Jen41], [Laz54]; Passi, LNM 715,
Ch. III): if `g - 1 ∈ Δ_{𝔽_p}(G)^n` with `n ≥ 1`, then `g ∈ S n`
(`RestrictedSeries.mem_of_sub_one_mem`).

**Proof.** Take a frame of `S` (`RestrictedSeries.exists_frame`) and induct on `n`. Let
`g ∈ S k` and `g - 1 ∈ Δ^{k+1}`, with normal form `g = ∏ x_j^{b_j}` (`b_j = 0` for `w_j < k`).
Then `g - 1 ∈ Bsp (k+1)` (`augIdealP_pow_le_Bsp`), and
`g - 1 - ∑ b_j (x_j - 1)` is a combination of basic products `P β`, `β ≤ b`, `|β| ≥ 2`, all of
weight `≥ 2k ≥ k + 1`. So `∑ b_j (x_j - 1) ∈ Bsp (k+1)`; its coordinate at the basic product
`P(e_l) = x_l - 1` is `b_l`, which must vanish when `w_l = k` (`repr_eq_zero_of_mem_Bsp`).
Hence `b_j = 0` for all `w_j ≤ k`, i.e. `g ∈ S (k+1)` (`JFrame.mem_succ`).
-/

namespace GroupDimension

namespace Jennings

open MonoidAlgebra TaharaProof

variable {p : ℕ} {G : Type*} [Group G] {T : RestrictedSeries p G}
variable {ι : Type*} [LinearOrder ι] [Fintype ι]

namespace JFrame

/-- The basic sequence `e_j`. -/
def unit {p : ℕ} (hp : 1 < p) (j : ι) : ι → Fin p :=
  toFin (Pi.single j 1) fun i => by
    classical
    by_cases h : i = j
    · subst h; simp; omega
    · simp [Pi.single_eq_of_ne h]; omega

omit [Fintype ι] in
theorem unit_injective (hp : 1 < p) : Function.Injective (unit (ι := ι) hp) := by
  classical
  intro i j h
  have := congrFun (congrArg bval h) i
  simp only [unit, bval_toFin] at this
  by_contra hij
  simp [Pi.single_eq_of_ne hij] at this

variable [Fact p.Prime] [Fintype G]

/-- **The inductive step.** If `g ∈ S k` and `g - 1 ∈ Δ^{k+1}`, then `g ∈ S (k+1)`. -/
theorem mem_succ (F : JFrame T ι) {g : G} {k : ℕ} (hk : 1 ≤ k) (hg : g ∈ T.S k)
    (h : of (ZMod p) G g - 1 ∈ augIdealP p G ^ (k + 1)) : g ∈ T.S (k + 1) := by
  classical
  have hp := (Fact.out : p.Prime).one_lt
  obtain ⟨b, hb, rfl⟩ := F.nf g
  have h1 := F.augIdealP_pow_le_Bsp (k + 1) h
  have h2 := (F.of_nprod_sub_one b).2
  have hw : ∀ j, b j ≠ 0 → k ≤ F.w j := fun j hj => F.nf_weight hk hg hb rfl hj
  -- the quadratic part has weight `≥ 2k`
  have hlow : F.low b 2 ≤ F.Bsp (k + 1) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨β, hβ, hβn, rfl⟩
    refine F.P_mem_Bsp (fun j => lt_of_le_of_lt (hβ j) (hb j)) ?_
    have : ∑ j, β j * k ≤ F.W β := Finset.sum_le_sum fun j _ => by
      by_cases hj : β j = 0
      · simp [hj]
      · exact Nat.mul_le_mul_left _ (hw j (fun h0 => hj (by have : β j ≤ b j := hβ j; omega)))
    rw [← Finset.sum_mul] at this
    nlinarith
  have hz : ∑ j, (b j : ZMod p) • F.X j ∈ F.Bsp (k + 1) := by
    have := sub_mem h1 (hlow h2)
    rwa [nprod, sub_sub_cancel] at this
  -- the coordinates of `∑ b_j (x_j - 1)`
  have hX : ∀ j, F.X j = F.basis (unit hp j) := by
    intro j; rw [basis_apply, unit, bval_toFin, P_single]
  have hcoord : ∀ l, F.basis.repr (∑ j, (b j : ZMod p) • F.X j) (unit hp l) = b l := by
    intro l
    rw [map_sum, Finsupp.finset_sum_apply, Finset.sum_eq_single l]
    · rw [hX, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
        smul_eq_mul, mul_one]
    · intro j _ hjl
      rw [hX, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
        if_neg (fun e => hjl (unit_injective hp e)), smul_zero]
    · simp
  rw [F.wt b hb (k + 1) (by omega)]
  intro l hl
  by_contra hbl
  have hwl : F.w l = k := by have := hw l hbl; omega
  have h0 := F.repr_eq_zero_of_mem_Bsp hz (unit hp l)
    (by simp only [unit, bval_toFin, W_single]; omega)
  rw [hcoord] at h0
  have h3 := (ZMod.natCast_eq_natCast_iff' (b l) 0 p).mp (by simpa using h0)
  rw [Nat.mod_eq_of_lt (hb l), Nat.zero_mod] at h3
  exact hbl h3

end JFrame

/-- **Jennings' theorem** (the hard inclusion): for a restricted N-series `S` of a finite
`p`-group, `G ∩ (1 + Δ_{𝔽_p}^n) ≤ S n` for `n ≥ 1`. (No `p`-group hypothesis is needed: a finite
group with a restricted N-series is automatically a `p`-group.) -/
theorem RestrictedSeries.mem_of_sub_one_mem {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] (T : RestrictedSeries p G) {g : G} {n : ℕ} (hn : 1 ≤ n)
    (h : MonoidAlgebra.of (ZMod p) G g - 1 ∈ augIdealP p G ^ n) : g ∈ T.S n := by
  classical
  haveI := Fintype.ofFinite G
  obtain ⟨ι, _, _, ⟨F⟩⟩ := T.exists_frame
  induction n, hn using Nat.le_induction with
  | base => exact T.mem_one g
  | succ n hn ih =>
    exact F.mem_succ hn (ih (Ideal.pow_le_pow_right (Nat.le_succ n) h)) h

end Jennings

end GroupDimension
