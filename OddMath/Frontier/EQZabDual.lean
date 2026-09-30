import OddMath.Frontier.EQZabFiltration

/-!
# The dual bimodule `Z_{a,b}^∨` (Ellis–Qi, Definition 4.9, Corollary 4.11)

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2, (4.24), Definition 4.9 and Corollary 4.11 (printed numbering).

`Z_{a,b}^∨ = HOM_{OΛ_{a+b}}(Z_{a,b}, OΛ_{a+b})`: in the model of `EQZabModule` its elements are
the additive maps `f : Z_{a,b} → OΛ_{a+b}` with `f(F · h) = f(F) h` (`IsRightLinear`), where
`F · h = F φ(h)`; the left `OΛ_{a+b}`-action is `(c f)(F) = c f(F)` and the differential is the
Hom-complex differential `(d f)(F) = d(f(F)) - (-1)^{|f|} f(d F)`, written parity-free as
`d(f(F)) - ι(f(ι(d F)))` (`dualD`; for `f` of parity `p`, `ι ∘ f ∘ ι = (-1)^p f`).

* `coeff μ` (`μ ∈ Par(b,a)`): the coefficient of `s̃_μ(y) z` in the basis (4.21) (`zab_span`,
  `zab_indep`); it is right `OΛ_{a+b}`-linear (`coeff_mul_phiAB`), `coeff μ (s̃_ν(y) z) = δ_{μν}`;
* `dual_expansion`, `dual_expansion_unique`: every right-linear `f` is uniquely
  `Σ_μ f(s̃_μ(y) z) · coeff μ`, so `Z_{a,b}^∨` is a free left `OΛ_{a+b}`-module with basis
  `{coeff μ}`, of rank `#Par(b,a) = binom(a+b, a)` (graded rank `[a+b choose a]_q`);
* `dualD_rightLinear`, `dualD_dualD`: `dualD` preserves right-linearity and squares to zero;
* **Corollary 4.11** (`cor_4_11`): `d(coeff μ) = Σ_ν m_{μν} coeff ν` with `m_{μν} ∈ ℤ`,
  `m_{μν} = 0` unless `|ν| + 1 = |μ|`: the `ℤ`-span of the basis is `d`-stable and the cells are
  attached in order of increasing `|μ|`, so `Z_{a,b}^∨` is a finite-cell, hence cofibrant, dg module
  over `OΛ_{a+b}`, of graded rank `[a+b choose a]_q`.

Ellis–Qi identify the dual basis with `{z^∨ ŝ_λ(x)}` using the pairing (4.22); the statements
above do not depend on that identification.
-/

namespace OddMath.Frontier.EQZab

open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open EQSkewDifferential EQSchur
open BoxComplement BoxPartitionCount
open scoped BigOperators

noncomputable section

local instance (priority := high) zabDualNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) zabDualNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {a b : ℕ}

/-- The basis element `s̃_μ(y) z` (in the untwisted model, `s_μ(y)`). -/
abbrev sY (a b : ℕ) (μ : Fin b → ℕ) : SkewPolynomial (a+b) := inclY a b (untwisted b μ)

theorem sY_mem (μ : Fin b → ℕ) : sY a b μ ∈ osymAB a b := inclY_mem (untwisted_mem_osym μ)

open Classical in
/-- The coefficients of `F ∈ Z_{a,b}` in the basis `{s̃_μ(y) z}` (`0` off `Par(b,a)`). -/
def coeffs (a b : ℕ) (F : SkewPolynomial (a+b)) (μ : Fin b → ℕ) : SkewPolynomial (a+b) :=
  if hF : F ∈ osymAB a b then (if μ ∈ box b a then Classical.choose (zab_span hF) μ else 0)
  else 0

theorem coeffs_mem (F : SkewPolynomial (a+b)) (μ : Fin b → ℕ) : coeffs a b F μ ∈ osym (a+b) := by
  unfold coeffs
  split_ifs with hF
  · exact (Classical.choose_spec (zab_span hF)).1 μ
  · exact zero_mem _
  · exact zero_mem _

theorem coeffs_of_not_mem (F : SkewPolynomial (a+b)) {μ : Fin b → ℕ} (hμ : μ ∉ box b a) :
    coeffs a b F μ = 0 := by
  unfold coeffs
  split_ifs <;> rfl

theorem coeffs_spec {F : SkewPolynomial (a+b)} (hF : F ∈ osymAB a b) :
    F = ∑ μ ∈ box b a, sY a b μ * phiAB a b (coeffs a b F μ) := by
  conv_lhs => rw [(Classical.choose_spec (zab_span hF)).2]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  unfold coeffs
  rw [dite_eq_left_of_eq_true (eq_true hF)]
  simp [hμ]

/-- Uniqueness of coefficients. -/
theorem coeffs_unique {F : SkewPolynomial (a+b)} (hF : F ∈ osymAB a b)
    (c : (Fin b → ℕ) → SkewPolynomial (a+b)) (hc : ∀ μ, c μ ∈ osym (a+b))
    (h : F = ∑ μ ∈ box b a, sY a b μ * phiAB a b (c μ)) :
    ∀ μ ∈ box b a, coeffs a b F μ = c μ := by
  intro μ hμ
  have key := zab_indep (fun ν => coeffs a b F ν - c ν)
    (fun ν => sub_mem (coeffs_mem F ν) (hc ν)) (by
      simp only [map_sub, mul_sub, Finset.sum_sub_distrib]
      rw [← coeffs_spec hF, ← h, sub_self]) μ hμ
  exact sub_eq_zero.mp key

theorem coeffs_zero (μ : Fin b → ℕ) : coeffs a b 0 μ = 0 := by
  by_cases hμ : μ ∈ box b a
  · exact coeffs_unique (zero_mem _) (fun _ => 0) (fun _ => zero_mem _)
      (by simp only [map_zero, ThickDecomposition.skew_mul_zero, Finset.sum_const_zero]) μ hμ
  · exact coeffs_of_not_mem _ hμ

theorem coeffs_add {F G : SkewPolynomial (a+b)} (hF : F ∈ osymAB a b) (hG : G ∈ osymAB a b)
    (μ : Fin b → ℕ) : coeffs a b (F + G) μ = coeffs a b F μ + coeffs a b G μ := by
  by_cases hμ : μ ∈ box b a
  · refine coeffs_unique (add_mem hF hG) _
      (fun μ => add_mem (coeffs_mem F μ) (coeffs_mem G μ)) ?_ μ hμ
    conv_lhs => rw [coeffs_spec hF, coeffs_spec hG]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [map_add, mul_add]
  · rw [coeffs_of_not_mem _ hμ, coeffs_of_not_mem _ hμ, coeffs_of_not_mem _ hμ, add_zero]

theorem coeffs_zsmul {F : SkewPolynomial (a+b)} (hF : F ∈ osymAB a b) (k : ℤ) (μ : Fin b → ℕ) :
    coeffs a b (k • F) μ = k • coeffs a b F μ := by
  by_cases hμ : μ ∈ box b a
  · refine coeffs_unique (Subring.zsmul_mem _ hF k) _
      (fun μ => Subring.zsmul_mem _ (coeffs_mem F μ) k) ?_ μ hμ
    conv_lhs => rw [coeffs_spec hF]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [map_zsmul, mul_smul_comm]
  · rw [coeffs_of_not_mem _ hμ, coeffs_of_not_mem _ hμ, smul_zero]

theorem coeffs_sum {ι : Type*} (s : Finset ι) (g : ι → SkewPolynomial (a+b))
    (hg : ∀ i, g i ∈ osymAB a b) (μ : Fin b → ℕ) :
    coeffs a b (∑ i ∈ s, g i) μ = ∑ i ∈ s, coeffs a b (g i) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, coeffs_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      coeffs_add (hg i) (Subring.sum_mem _ fun j _ => hg j), ih]

theorem coeffs_mul_phiAB {F : SkewPolynomial (a+b)} (hF : F ∈ osymAB a b)
    {h : SkewPolynomial (a+b)} (hh : h ∈ osym (a+b)) (μ : Fin b → ℕ) :
    coeffs a b (F * phiAB a b h) μ = coeffs a b F μ * h := by
  by_cases hμ : μ ∈ box b a
  · refine coeffs_unique (mul_mem hF (phiAB_mem hh)) _ (fun μ => mul_mem (coeffs_mem F μ) hh)
      ?_ μ hμ
    conv_lhs => rw [coeffs_spec hF]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [map_mul]
    exact OddMath.SkewPolynomial.mul_assoc _ _ _
  · rw [coeffs_of_not_mem _ hμ, coeffs_of_not_mem _ hμ, ThickDecomposition.skew_zero_mul]

open Classical in
theorem coeffs_sY {ν : Fin b → ℕ} (hν : ν ∈ box b a) (μ : Fin b → ℕ) :
    coeffs a b (sY a b ν) μ = if μ = ν then 1 else 0 := by
  by_cases hμ : μ ∈ box b a
  · refine coeffs_unique (sY_mem ν) (fun μ => if μ = ν then 1 else 0)
      (fun μ => by split_ifs; exacts [one_mem _, zero_mem _]) ?_ μ hμ
    rw [Finset.sum_eq_single_of_mem ν hν, ite_eq_left rfl, map_one, mul_one]
    intro μ _ hne
    rw [ite_eq_right hne, map_zero, ThickDecomposition.skew_mul_zero]
  · rw [coeffs_of_not_mem _ hμ, ite_eq_right]
    rintro rfl
    exact absurd hν hμ

/-! ## `Z_{a,b}^∨` -/

/-- `Z_{a,b}` as an additive group. -/
abbrev ZMod' (a b : ℕ) := ↥(osymAB a b)

/-- The right action `F · h = F φ(h)` on `Z_{a,b}`. -/
def rmul (F : ZMod' a b) {h : SkewPolynomial (a+b)} (hh : h ∈ osym (a+b)) : ZMod' a b :=
  ⟨F.1 * phiAB a b h, mul_mem F.2 (phiAB_mem hh)⟩

/-- An element of `Z_{a,b}^∨ = HOM_{OΛ_{a+b}}(Z_{a,b}, OΛ_{a+b})`. -/
def IsRightLinear (f : ZMod' a b →+ SkewPolynomial (a+b)) : Prop :=
  (∀ F, f F ∈ osym (a+b)) ∧ ∀ F (h : SkewPolynomial (a+b)) (hh : h ∈ osym (a+b)),
    f (rmul F hh) = f F * h

/-- The dual basis element `coeff μ`: the coefficient of `s̃_μ(y) z`. -/
def coeff (a b : ℕ) (μ : Fin b → ℕ) : ZMod' a b →+ SkewPolynomial (a+b) where
  toFun F := coeffs a b F.1 μ
  map_zero' := coeffs_zero μ
  map_add' F G := coeffs_add F.2 G.2 μ

theorem coeff_rightLinear (μ : Fin b → ℕ) : IsRightLinear (coeff a b μ) :=
  ⟨fun F => coeffs_mem F.1 μ, fun F _ hh => coeffs_mul_phiAB F.2 hh μ⟩

/-- `d` and `ι` on `Z_{a,b}`. -/
def dZZ (a b : ℕ) : ZMod' a b →+ ZMod' a b where
  toFun F := ⟨dZ a b F.1, dZ_mem F.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

def iotaZ (a b : ℕ) : ZMod' a b →+ ZMod' a b where
  toFun F := ⟨parityInv (a+b) F.1, parityInv_mem F.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- The Hom-complex differential `d f = d ∘ f - (-1)^{|f|} f ∘ d`, parity-free:
`(d f)(F) = d(f F) - ι(f(ι(d F)))`. -/
def dualD (f : ZMod' a b →+ SkewPolynomial (a+b)) : ZMod' a b →+ SkewPolynomial (a+b) :=
  (d (a+b)).comp f - (parityInv (a+b)).toAddMonoidHom.comp (f.comp ((iotaZ a b).comp (dZZ a b)))

theorem dualD_apply (f : ZMod' a b →+ SkewPolynomial (a+b)) (F : ZMod' a b) :
    dualD f F = d (a+b) (f F) - parityInv (a+b) (f (iotaZ a b (dZZ a b F))) := rfl

theorem parityInv_phiAB (f : SkewPolynomial (a+b)) :
    parityInv (a+b) (phiAB a b f) = phiAB a b (parityInv (a+b) f) := by
  have h : (parityInv (a+b)).comp (phiAB a b) = (phiAB a b).comp (parityInv (a+b)) :=
    ringHom_ext fun j => by simp [phiAB, epsAB]
  exact RingHom.congr_fun h f

theorem dZ_parityInv (F : SkewPolynomial (a+b)) :
    dZ a b (parityInv (a+b) F) = -parityInv (a+b) (dZ a b F) := by
  rw [dAlpha_apply, dAlpha_apply, d_parityInv, parityInv_parityInv, map_add, map_mul,
    parityInv_sAlpha, parityInv_parityInv]
  simp only [mul_neg]
  abel

/-- `d` preserves `Z_{a,b}^∨`. -/
theorem dualD_rightLinear {f : ZMod' a b →+ SkewPolynomial (a+b)} (hf : IsRightLinear f) :
    IsRightLinear (dualD f) := by
  refine ⟨fun F => sub_mem (d_mem_osym (hf.1 F)) (parityInv_mem_osym (hf.1 _)), fun F h hh => ?_⟩
  have e : iotaZ a b (dZZ a b (rmul F hh)) =
      rmul (iotaZ a b (dZZ a b F)) (parityInv_mem_osym hh) +
        rmul F (parityInv_mem_osym (d_mem_osym hh)) := by
    apply Subtype.ext
    change parityInv (a+b) (dZ a b (F.1 * phiAB a b h)) =
      parityInv (a+b) (dZ a b F.1) * phiAB a b (parityInv (a+b) h) +
        F.1 * phiAB a b (parityInv (a+b) (d (a+b) h))
    rw [dZ_mul_phiAB, map_add, map_mul, map_mul, parityInv_parityInv, parityInv_phiAB,
      parityInv_phiAB]
  rw [dualD_apply, dualD_apply, e, map_add, hf.2 _ _ (parityInv_mem_osym hh),
    hf.2 _ _ (parityInv_mem_osym (d_mem_osym hh))]
  change d (a+b) (f (rmul F hh)) - _ = _
  rw [hf.2 _ _ hh, d_mul, map_add, map_mul, map_mul, parityInv_parityInv, parityInv_parityInv,
    sub_mul]
  abel

/-- `d² = 0` on `Z_{a,b}^∨`. -/
theorem dualD_dualD (f : ZMod' a b →+ SkewPolynomial (a+b)) (F : ZMod' a b) :
    dualD (dualD f) F = 0 := by
  have h0 : iotaZ a b (dZZ a b (iotaZ a b (dZZ a b F))) = 0 := by
    apply Subtype.ext
    change parityInv (a+b) (dZ a b (parityInv (a+b) (dZ a b F.1))) = 0
    rw [dZ_parityInv, dZ_dZ, map_zero, neg_zero, map_zero]
  rw [dualD_apply, dualD_apply, dualD_apply, h0, map_zero, map_zero, sub_zero, map_sub, d_d,
    d_parityInv]
  abel

/-! ## The dual basis -/

theorem sum_sY_eq (F : ZMod' a b) :
    F = ∑ μ ∈ box b a, rmul (⟨sY a b μ, sY_mem μ⟩ : ZMod' a b) (coeffs_mem F.1 μ) := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  exact coeffs_spec F.2

/-- Every element of `Z_{a,b}^∨` is `Σ_μ f(s̃_μ(y) z) · coeff μ`. -/
theorem dual_expansion {f : ZMod' a b →+ SkewPolynomial (a+b)} (hf : IsRightLinear f)
    (F : ZMod' a b) :
    f F = ∑ μ ∈ box b a, f ⟨sY a b μ, sY_mem μ⟩ * coeff a b μ F := by
  conv_lhs => rw [sum_sY_eq F]
  rw [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [hf.2]
  rfl

open Classical in
/-- The expansion is unique: `Z_{a,b}^∨` is free on `{coeff μ : μ ∈ Par(b,a)}`. -/
theorem dual_expansion_unique (g : (Fin b → ℕ) → SkewPolynomial (a+b))
    (h0 : ∀ F : ZMod' a b, ∑ μ ∈ box b a, g μ * coeff a b μ F = 0) :
    ∀ μ ∈ box b a, g μ = 0 := by
  intro ν hν
  have := h0 ⟨sY a b ν, sY_mem ν⟩
  change ∑ μ ∈ box b a, g μ * coeffs a b (sY a b ν) μ = 0 at this
  simp only [coeffs_sY hν, mul_ite, mul_one, ThickDecomposition.skew_mul_zero] at this
  rw [Finset.sum_ite_eq'] at this
  simpa [hν] using this


/-! ## Corollary 4.11 -/

open Classical in
theorem coeffs_iota_dZ_sY {ν : Fin b → ℕ} (hν : ν ∈ box b a) (μ : Fin b → ℕ) :
    ∃ k : ℤ, (k ≠ 0 → weight ν + 1 = weight μ) ∧
      coeffs a b (parityInv (a+b) (dZ a b (sY a b ν))) μ = k • 1 := by
  have hb := mem_box.1 hν
  set c : Fin b → ℤ := fun i =>
    (-1 : ℤ) ^ (rowsAbove ν i + i.val) * (((a : ℤ) + content ν i) % 2) with hc
  set P : Fin b → Prop := fun i => Antitone (ν + expSingle i) ∧ ν i < a with hP
  have hterm : ∀ i, coeffs a b (parityInv (a+b)
      (if P i then c i • sY a b (ν + expSingle i) else 0)) μ =
        (if P i ∧ μ = ν + expSingle i then c i * (-1) ^ weight (ν + expSingle i) else 0) •
          (1 : SkewPolynomial (a+b)) := by
    intro i
    by_cases hi : P i
    · have hρ : ν + expSingle i ∈ box b a := mem_box.2 ⟨hi.1, add_box_mem hb.2 hi⟩
      rw [ite_eq_left hi, map_zsmul, sY, parityInv_inclY, parityInv_untwisted, map_zsmul,
        coeffs_zsmul (Subring.zsmul_mem _ (sY_mem _) _), coeffs_zsmul (sY_mem _),
        coeffs_sY hρ, smul_smul]
      by_cases hμ : μ = ν + expSingle i
      · rw [ite_eq_left hμ, ite_eq_left ⟨hi, hμ⟩, weight]
      · rw [ite_eq_right hμ, ite_eq_right (fun h => hμ h.2), smul_zero, zero_smul]
    · rw [ite_eq_right hi, map_zero, coeffs_zero, ite_eq_right (fun h => hi h.1), zero_smul]
  have hmem : ∀ i, parityInv (a+b) (if P i then c i • sY a b (ν + expSingle i) else 0) ∈
      osymAB a b := fun i => by
    split_ifs
    · exact parityInv_mem (Subring.zsmul_mem _ (sY_mem _) _)
    · rw [map_zero]; exact zero_mem _
  refine ⟨∑ i, if P i ∧ μ = ν + expSingle i then c i * (-1) ^ weight (ν + expSingle i) else 0,
    fun hk => ?_, ?_⟩
  · obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
    have h2 : P i ∧ μ = ν + expSingle i := by
      by_contra h
      exact hi (ite_eq_right h)
    rw [h2.2, weight_add_expSingle]
  · rw [lemma_4_7_box ν hb.1 hb.2, map_sum, coeffs_sum _ _ hmem, Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => hterm i

open Classical in
/-- **Ellis–Qi, Corollary 4.11**: the differential of `Z_{a,b}^∨` maps each dual basis element
`coeff μ` to an integer combination of dual basis elements `coeff ν` with `|ν| + 1 = |μ|`. Hence
the `ℤ`-span of the basis `{coeff μ : μ ∈ Par(b,a)}` of the free left `OΛ_{a+b}`-module
`Z_{a,b}^∨` (`dual_expansion`, `dual_expansion_unique`) is `d`-stable, and filtering by `|μ|`
exhibits `Z_{a,b}^∨` as a finite-cell (cofibrant) left dg module over `OΛ_{a+b}` of graded rank
`[a+b choose a]_q` (`card_cells`). -/
theorem cor_4_11 (μ : Fin b → ℕ) :
    ∃ m : (Fin b → ℕ) → ℤ, (∀ ν, m ν ≠ 0 → weight ν + 1 = weight μ) ∧
      ∀ F : ZMod' a b, dualD (coeff a b μ) F = ∑ ν ∈ box b a, m ν • coeff a b ν F := by
  have hk : ∀ ν, ∃ k : ℤ, (k ≠ 0 → weight ν + 1 = weight μ) ∧
      (ν ∈ box b a → dualD (coeff a b μ) ⟨sY a b ν, sY_mem ν⟩ = -k • 1) := by
    intro ν
    by_cases hν : ν ∈ box b a
    · obtain ⟨k, hk1, hk2⟩ := coeffs_iota_dZ_sY (a := a) hν μ
      refine ⟨k, hk1, fun _ => ?_⟩
      rw [dualD_apply]
      change d (a+b) (coeffs a b (sY a b ν) μ) -
        parityInv (a+b) (coeffs a b (parityInv (a+b) (dZ a b (sY a b ν))) μ) = _
      rw [coeffs_sY hν, hk2, map_zsmul, map_one, neg_smul, sub_eq_neg_self]
      split_ifs
      · exact d_one
      · exact map_zero _
    · exact ⟨0, fun h => absurd rfl h, fun h => absurd h hν⟩
  choose k hk1 hk2 using hk
  refine ⟨fun ν => -k ν, fun ν h => hk1 ν (fun h' => h (by simp [h'])), fun F => ?_⟩
  rw [dual_expansion (dualD_rightLinear (coeff_rightLinear μ)) F]
  refine Finset.sum_congr rfl fun ν hν => ?_
  rw [hk2 ν hν, smul_mul_assoc, one_mul]


/-! ## Proposition 4.13 (1) as printed, for two blocks -/

theorem untwisted_zero (N : ℕ) : untwisted N 0 = 1 := by
  apply twistRev_injective
  rw [twistRev_untwisted, map_one, show monomial (0 : Fin N → ℕ) 1 = (1 : SkewPolynomial N) from rfl,
    mul_one, LongestDivided.D_staircase, weight_delta, show EQSchur.weight (0 : Fin N → ℕ) = 0 by
      simp [EQSchur.weight], add_zero, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
    one_pow, one_smul]

/-- **Proposition 4.13 (1) is false as printed.** For the composition `(a, b)` (`r = 2`) the printed
set `{s̃_{λ_1}(x_1, …, x_{a_1})}` with `λ_1` in a `0 × a_1` box is `{z}`, which is not a basis of
`Z_{a,b}` over `OΛ_{a+b}` when `a, b ≥ 1`: `s̃_{(1)}(y) z` is not in `z · OΛ_{a+b}`. (The basis of
`Z_{a,b}` is `{s̃_μ(y) z : μ ∈ Par(b,a)}`, `zab_span`, `zab_indep`, of rank `binom(a+b, a)`.) -/
theorem prop_4_13_one_printed_false (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬ ∀ F ∈ osymAB a b, ∃ c ∈ osym (a+b), F = phiAB a b c := by
  intro h
  let μ₁ : Fin b → ℕ := fun j => if j.val = 0 then 1 else 0
  have hμ₁ : μ₁ ∈ box b a := mem_box.2 ⟨fun i j hij => by
      have := Fin.le_def.1 hij; simp only [μ₁]; split_ifs <;> omega, fun j => by
      simp only [μ₁]; split_ifs <;> omega⟩
  have h0 : (0 : Fin b → ℕ) ∈ box b a := mem_box.2 ⟨fun _ _ _ => le_rfl, fun _ => Nat.zero_le _⟩
  obtain ⟨c, hc, hF⟩ := h (sY a b μ₁) (sY_mem μ₁)
  have e1 := coeffs_sY (a := a) hμ₁ μ₁
  have e2 : sY a b μ₁ = sY a b 0 * phiAB a b c := by
    rw [hF, sY, untwisted_zero, map_one, one_mul]
  rw [e2, coeffs_mul_phiAB (sY_mem 0) hc, coeffs_sY h0, ite_eq_left rfl] at e1
  have hne : μ₁ ≠ 0 := fun e => by
    have := congrFun e ⟨0, by omega⟩
    simp [μ₁] at this
  rw [ite_eq_right hne, ThickDecomposition.skew_zero_mul] at e1
  exact zero_ne_one e1

end

end OddMath.Frontier.EQZab
