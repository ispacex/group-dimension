module

public import GroupDimension.TraceReplay.HomExact
public import GroupDimension.TraceReplay.PolyProd

@[expose] public section

/-!
# Exact membership with polynomial maps of any weight (MATH-314, docs §3.2(e))

`TraceReplay/HomExact.lean` handles free columns with maps of weight 1 (homomorphisms `G → ℤ`).
Here the maps have any weights. A certificate (`PolyCert`) lists base maps `(w, λ)`: `λ` gives the
values of a polynomial map `φ` of degree `≤ w` on the monomials `X_u`, `1 ≤ |u| ≤ w`, i.e.
`φ(ψ X_u) = λ(X_u)`. The functionals are products of base maps of total weight `< n`
(Passi's product rule, `TraceReplay/PolyProd.lean`). Their values on the free columns are
computed by the covering sum `covW` (`prodVal`), and an integer matrix `C` with
`C · M = diag(D)` is checked by the kernel (`checkPoly`), as in `checkHom`.

`check_mem_D_poly_lin`: if the trace and the certificate pass, the `g j` generate `G`, the relators
hold, every base map is a polynomial map of `G` with the stated values (`hmaps`), and the test
element has `p`-power order in `Δ/Δ^n`, then the test element lies in `Δ^n`.
-/

namespace GroupDimension.TraceReplay

open MonoidAlgebra

/-- Polynomial maps for a trace with free columns. -/
structure PolyCert where
  /-- base maps `(w, λ)`: `λ[c − 1]` is the value on the monomial at position `c`, degrees `1..w` -/
  maps : List (Nat × List Int)
  /-- the functionals: products of base maps, by index -/
  funcs : List (List Nat)
  /-- one row per free column, in the order of `T.F`: `(C_f, D_f)` with `C_f · (ν(v_{f'})) = D_f δ` -/
  rows : List (List Int × Int)
  deriving Repr

/-- The position of a word with letters `< d` (the first letter most significant). -/
def posN (d : Nat) (u : List Nat) : Nat := off d u.length + u.foldl (fun acc j => acc * d + j) 0

/-- A base map on a word: `λ` at its position for lengths `1..w`, else `0`. -/
def baseVal (d : Nat) (m : Nat × List Int) (u : List Nat) : Int :=
  bif Nat.blt 0 u.length && Nat.ble u.length m.1 then m.2.getD (posN d u - 1) 0 else 0

/-- A product of base maps on a word, by the covering sum. -/
def prodVal (d : Nat) (maps : List (Nat × List Int)) : List Nat → List Nat → Int
  | [], u => bif u.isEmpty then 1 else 0
  | i :: κ, u => covW (baseVal d (maps.getD i (0, []))) (prodVal d maps κ) [] [] u

/-- The weight of a product. -/
def wt (maps : List (Nat × List Int)) (κ : List Nat) : Nat := (κ.map fun i => (maps.getD i (0, [])).1).sum

/-- `ν_κ(ψ(X_f))`. -/
def colValP (d : Nat) [NeZero d] (maps : List (Nat × List Int)) (κ : List Nat) (f : Nat) : Int :=
  prodVal d maps κ ((wordAt d f).toList.map (·.val))

/-- The certificate check: every product uses valid indices and has weight `< n`, and
`C · M = diag(D)` with `D_f ≠ 0`, `M_{κ,f} = ν_κ(ψ(X_f))`. -/
def checkPoly (T : Trace) [NeZero T.d] (P : PolyCert) : Bool :=
  P.funcs.all (fun κ => κ.all (fun i => Nat.blt i P.maps.length) && Nat.blt (wt P.maps κ) T.n) &&
  (List.range T.F.length).all (fun i => decide ((P.rows.getD i ([], 0)).2 ≠ 0) &&
    (List.range T.F.length).all (fun j => decide (
      lsum P.funcs.length (fun k => (P.rows.getD i ([], 0)).1.getD k 0 *
        colValP T.d P.maps (P.funcs.getD k []) (T.F.getD j 0)) =
      if i = j then (P.rows.getD i ([], 0)).2 else 0)))

theorem checkPoly_spec (T : Trace) [NeZero T.d] (P : PolyCert) (h : checkPoly T P = true) :
    (∀ κ ∈ P.funcs, (∀ i ∈ κ, i < P.maps.length) ∧ wt P.maps κ < T.n) ∧
    (∀ i < T.F.length, (P.rows.getD i ([], 0)).2 ≠ 0) ∧
    (∀ i < T.F.length, ∀ j < T.F.length,
      ∑ k ∈ Finset.range P.funcs.length, (P.rows.getD i ([], 0)).1.getD k 0 *
        colValP T.d P.maps (P.funcs.getD k []) (T.F.getD j 0) =
      if i = j then (P.rows.getD i ([], 0)).2 else 0) := by
  simp only [checkPoly, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    Nat.blt_eq] at h
  obtain ⟨hK, hrows⟩ := h
  refine ⟨hK, fun i hi => (hrows i hi).1, fun i hi j hj => ?_⟩
  rw [← lsum_eq]; exact (hrows i hi).2 j hj

section Sem

variable {G : Type*} [Group G] {d : ℕ} [NeZero d] (g : Fin d → G)

/-- Letters as natural numbers: `j ↦ g_j` (reduced modulo `d`). -/
def gN (j : ℕ) : G := g (letter d j)

theorem letter_val (j : Fin d) : letter d j.val = j := Fin.ext (letter_of_lt (d := d) j.2)

/-- `ψ(X_w) = E` of the word's letters. -/
theorem psi_single_eq_E (w : FreeMonoid (Fin d)) :
    psi g (single w 1) = E ((w.toList.map (·.val)).map (gN g)) := by
  rw [psi_single, one_smul, E, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp [gN, letter_val]

/-- The hypothesis on a base map `(w, λ)`: a polynomial map `φ` of `G` of degree `≤ w`, `φ 1 = 0`,
with `φ(ψ X_u) = λ(X_u)` for `1 ≤ |u| ≤ w`. -/
def IsBase (m : ℕ × List ℤ) (φ : G → ℤ) : Prop :=
  φ 1 = 0 ∧ (∀ x ∈ augIdeal G ^ (m.1 + 1), lin φ x = 0) ∧
    ∀ u : List ℕ, (∀ j ∈ u, j < d) → 1 ≤ u.length → u.length ≤ m.1 →
      lin φ (E (u.map (gN g))) = m.2.getD (posN d u - 1) 0

theorem lin_base {m : ℕ × List ℤ} {φ : G → ℤ} (h : IsBase g m φ) (u : List ℕ) (hu : ∀ j ∈ u, j < d) :
    lin φ (E (u.map (gN g))) = baseVal d m u := by
  obtain ⟨h1, hvan, hval⟩ := h
  unfold baseVal
  rcases Nat.eq_zero_or_pos u.length with h0 | h0
  · rw [List.length_eq_zero_iff.mp h0]
    simp [E_nil, lin_one, h1]
  · by_cases hw : u.length ≤ m.1
    · have hb : (Nat.blt 0 u.length && Nat.ble u.length m.1) = true := by
        rw [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq]; exact ⟨h0, hw⟩
      rw [hval u hu h0 hw, hb]; rfl
    · have hE := E_mem (u.map (gN g))
      rw [List.length_map] at hE
      have hb : (Nat.blt 0 u.length && Nat.ble u.length m.1) = false := by
        rw [Bool.and_eq_false_iff, Nat.ble_eq]; right; simpa using hw
      rw [hvan _ (Ideal.pow_le_pow_right (by omega) hE), hb]; rfl

variable (φ : ℕ → G → ℤ)

/-- The pointwise product of the base maps in `κ`. -/
def prodFn (κ : List ℕ) (x : G) : ℤ := (κ.map fun i => φ i x).prod

theorem lin_prodFn_E (maps : List (ℕ × List ℤ)) (hφ : ∀ i < maps.length, IsBase g (maps.getD i (0, [])) (φ i))
    (κ : List ℕ) (hκ : ∀ i ∈ κ, i < maps.length) (u : List ℕ) (hu : ∀ j ∈ u, j < d) :
    lin (prodFn φ κ) (E (u.map (gN g))) = prodVal d maps κ u := by
  induction κ generalizing u with
  | nil =>
    simp only [prodFn, List.map_nil, List.prod_nil, prodVal]
    rw [lin_one_E]
    cases u <;> simp
  | cons i κ ih =>
    have hi := hκ i List.mem_cons_self
    have hκ' : ∀ i ∈ κ, i < maps.length := fun i' h => hκ i' (List.mem_cons_of_mem _ h)
    have e : prodFn φ (i :: κ) = fun x => φ i x * prodFn φ κ x := by
      funext x; simp [prodFn]
    rw [e, prodVal]
    exact lin_mul_E_map (φ i) (prodFn φ κ) (gN g) (fun j => j < d) _ _
      (fun w hw => lin_base g (hφ i hi) w hw) (fun w hw => ih hκ' w hw) u hu

theorem lin_prodFn_eq_zero (maps : List (ℕ × List ℤ))
    (hφ : ∀ i < maps.length, IsBase g (maps.getD i (0, [])) (φ i))
    (κ : List ℕ) (hκ : ∀ i ∈ κ, i < maps.length) :
    ∀ x ∈ augIdeal G ^ (wt maps κ + 1), lin (prodFn φ κ) x = 0 := by
  induction κ with
  | nil =>
    simp only [prodFn, List.map_nil, List.prod_nil, wt, List.sum_nil]
    exact lin_one_eq_zero
  | cons i κ ih =>
    have hi := hκ i List.mem_cons_self
    have hκ' : ∀ i ∈ κ, i < maps.length := fun i' h => hκ i' (List.mem_cons_of_mem _ h)
    have e : prodFn φ (i :: κ) = fun x => φ i x * prodFn φ κ x := by
      funext x; simp [prodFn]
    have ew : wt maps (i :: κ) = (maps.getD i (0, [])).1 + wt maps κ := by simp [wt]
    rw [e, ew]
    exact lin_mul_eq_zero (φ i) (prodFn φ κ) (hφ i hi).2.1 (ih hκ')

end Sem

/-- **Exact membership with polynomial maps of any weight.** Suppose `check` accepts the trace and
`checkPoly` the certificate. Let `G` be a group and `g : Fin d → G` such that the `g j` generate `G`,
the relators listed in the trace hold at `g`, every base map `(w, λ)` of the certificate is a
polynomial map of `G` of degree `≤ w` with the values `λ` on the monomials (`hmaps`, `IsBase`), and
the test element `x_t = linG g (testLin T t)` has `p`-power order in `Δ/Δ^n` (`hord`). Then
`x_t ∈ Δ^n`. -/
theorem check_mem_D_poly_lin (T : Trace) (members : List ℕ) [NeZero T.d] (hc : check T members = true)
    (P : PolyCert) (hP : checkPoly T P = true)
    {G : Type*} [Group G] (g : Fin T.d → G) (hrel : ∀ r ∈ T.rels, gword g r.2 = 1)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hmaps : ∀ i < P.maps.length, ∃ φ : G → ℤ, IsBase g (P.maps.getD i (0, [])) φ)
    (t : ℕ) (ht : t ∈ members)
    (hord : ∃ m : ℕ, ((T.p : ℤ) ^ m) • linG g (testLin T t) ∈ augIdeal G ^ T.n) :
    linG g (testLin T t) ∈ augIdeal G ^ T.n := by
  obtain ⟨hK, hDg, hCM⟩ := checkPoly_spec T P hP
  choose! φ hφ using hmaps
  have hκ : ∀ k < P.funcs.length, (∀ i ∈ P.funcs.getD k [], i < P.maps.length) ∧
      wt P.maps (P.funcs.getD k []) < T.n := fun k hk => by
    apply hK; rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  refine check_mem_D_funcs T members hc g hrel hgen P.funcs.length
    (fun k => (Int.castAddHom ℚ).comp (lin (prodFn φ (P.funcs.getD k []))))
    (fun k hk x hx => ?_)
    (fun k j => colValP T.d P.maps (P.funcs.getD k []) (T.F.getD j 0))
    (fun i k => (P.rows.getD i ([], 0)).1.getD k 0) (fun i => (P.rows.getD i ([], 0)).2)
    (fun k hk j _ => ?_) hDg hCM t ht hord
  · rw [AddMonoidHom.comp_apply,
      lin_prodFn_eq_zero g φ P.maps hφ _ (hκ k hk).1 x (Ideal.pow_le_pow_right (by have := (hκ k hk).2; omega) hx),
      map_zero]
  · rw [AddMonoidHom.comp_apply, show e T.d (T.F.getD j 0) = single (wordAt T.d (T.F.getD j 0)) 1 from rfl,
      psi_single_eq_E, lin_prodFn_E g φ P.maps hφ _ (hκ k hk).1 _ (by simp), colValP]
    rfl

/-- `check_mem_D_poly_lin` for a word test (`hw`): `w_t(g) ∈ D_n(G)`. -/
theorem check_mem_D_poly (T : Trace) (members : List ℕ) [NeZero T.d] (hc : check T members = true)
    (P : PolyCert) (hP : checkPoly T P = true)
    {G : Type*} [Group G] (g : Fin T.d → G) (hrel : ∀ r ∈ T.rels, gword g r.2 = 1)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hmaps : ∀ i < P.maps.length, ∃ φ : G → ℤ, IsBase g (P.maps.getD i (0, [])) φ)
    (t : ℕ) (ht : t ∈ members) (hw : T.tests.any (fun y => y.1 == t) = true)
    (hord : ∃ m : ℕ, ((T.p : ℤ) ^ m) • (of ℤ G (gword g (findWord t T.tests)) - 1) ∈
      augIdeal G ^ T.n) :
    gword g (findWord t T.tests) ∈ GroupDimension.D T.n G := by
  have e : linG g (testLin T t) = of ℤ G (gword g (findWord t T.tests)) - 1 := by
    rw [testLin_of_word T hw, linG_single]
  have h := check_mem_D_poly_lin T members hc P hP g hrel hgen hmaps t ht (by rw [e]; exact hord)
  rw [e] at h
  exact mem_D.2 h

end GroupDimension.TraceReplay
