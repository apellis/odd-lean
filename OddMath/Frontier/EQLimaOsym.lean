import OddMath.Frontier.EQLimaCohomology
import OddMath.Frontier.EQSchurDifferential
import OddMath.Frontier.OddGrassmannSchur
import OddMath.Frontier.EQZnAction

/-!
# Ellis–Qi, Proposition A.2 (2) for `OΛ_N`, `N ≥ 2`, unconditionally

A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Proposition A.2 (2): `H(OΛ_N)` is a free abelian group with basis the classes of the untwisted
odd Schur polynomials `s_λ`, `λ` a Lima partition with `ℓ(λ) ≤ N`.

The hypotheses `OddSchurData` of `EQLimaCohomology` are discharged for `N = n + 2`:

* `map_theta_osym`: `θ(OΛ_N) = OΛ̃_N`, since `θ(e_k) = ε_k` (`theta_elementary`); hence
  `θ(OΛ_{n+2})` is the ring of odd symmetric polynomials `kernelSubring n` (EKL);
* `kernelSchurBasis`: EKL's odd Schur polynomials `s̃_λ`, `ℓ(λ) ≤ n + 2`, form a `ℤ`-basis of
  `kernelSubring n` (from the basis `s^H_λ` of `OΛ`, EKL Conjecture 5.3 = `conjecture_5_3`, and
  the surjection `OΛ → OΛ_{n+2}`);
* `theta_schurU`: `θ(s_λ) = s̃_λ` (Ellis–Qi (3.27) and Remark 3.10), so the untwisted odd Schur
  polynomials `s_λ`, `ℓ(λ) ≤ n + 2`, form a `ℤ`-basis of `OΛ_{n+2}` (`osymSchurBasis`);
* `prop_3_11_cells`: Proposition 3.11 (`EQSchur.prop_3_11`) rewritten as a sum over the addable
  white boxes in the first `N` rows, with the sign `schurSign`;
* `prop_A_2_two'`: Proposition A.2 (2) for `OΛ_{n+2}`, with the concrete forms
  `cocycle_eq'` and `lima_independent'`.

The ranks `N = 0, 1` are not covered here (the EKL basis results in the library are stated for
`N = n + 2`).
-/

namespace OddMath.Frontier.EQLima

open Finset
open OddMath.SkewPolynomial (SkewPolynomial generator expSingle)
open OddMath.Frontier.EQSkewDifferential (osym d theta elementary)

/-! ### `θ(OΛ_N)` is EKL's `OΛ̃_N` -/

theorem theta_elementary (N k : ℕ) :
    theta N (elementary N k) = FiniteCompleteElementary.elementaryPoly N k := by
  rw [elementary, EQZn.ringHom_strictSum]
  have h : (fun j : Fin N => theta N (generator j)) = PlacticEvaluation.tildeGenerator := by
    funext j
    rw [EQSkewDifferential.theta_generator, PlacticEvaluation.tildeGenerator]
  rw [h, EQZn.strictSum_tilde]

theorem map_theta_osym (N : ℕ) : (osym N).map (theta N) = ElementaryBranching.E N := by
  rw [EQSkewDifferential.osym, RingHom.map_closure, ← Set.range_comp, ElementaryBranching.E]
  congr 2
  funext k
  exact theta_elementary N k

theorem map_theta_osym_kernel (n : ℕ) :
    (osym (n+2)).map (theta (n+2)) = OddSymmetricKernel.kernelSubring n := by
  rw [map_theta_osym, StaircaseIndependence.E_eq_kernel]

theorem theta_mem_kernel {n : ℕ} {f : SkewPolynomial (n+2)} (hf : f ∈ osym (n+2)) :
    theta (n+2) f ∈ OddSymmetricKernel.kernelSubring n := by
  rw [← map_theta_osym_kernel]; exact ⟨f, hf, rfl⟩

theorem theta_mem_osym {n : ℕ} {g : SkewPolynomial (n+2)}
    (hg : g ∈ OddSymmetricKernel.kernelSubring n) : theta (n+2) g ∈ osym (n+2) := by
  rw [← map_theta_osym_kernel] at hg
  obtain ⟨f, hf, rfl⟩ := hg
  rwa [EQSchur.theta_theta]

/-- `θ : OΛ_{n+2} ≅ OΛ̃_{n+2}` as abelian groups. -/
noncomputable def thetaEquiv (n : ℕ) :
    osym (n+2) ≃ₗ[ℤ] OddSymmetricKernel.kernelSubring n :=
  AddEquiv.toIntLinearEquiv
    { toFun := fun f => ⟨theta (n+2) (f : SkewPolynomial (n+2)), theta_mem_kernel f.2⟩
      invFun := fun g => ⟨theta (n+2) (g : SkewPolynomial (n+2)), theta_mem_osym g.2⟩
      left_inv := fun _ => Subtype.ext (EQSchur.theta_theta _)
      right_inv := fun _ => Subtype.ext (EQSchur.theta_theta _)
      map_add' := fun f g => Subtype.ext
        (map_add (theta (n+2)) (f : SkewPolynomial (n+2)) (g : SkewPolynomial (n+2))) }

theorem thetaEquiv_symm_coe (n : ℕ) (g : OddSymmetricKernel.kernelSubring n) :
    ((thetaEquiv n).symm g : SkewPolynomial (n+2)) = theta (n+2) g := rfl

/-! ### The odd Schur basis of `OΛ̃_{n+2}` -/

open OddLREKIdentification (piN sK toExponent)
open OddGrassmannSchur (sBasis)

/-- EKL's odd Schur polynomial `s̃_λ` in `n + 2` variables, as an element of `OΛ̃_{n+2}`. -/
noncomputable def kernelSchur (n : ℕ) (μ : {μ : YoungDiagram // LengthLE (n+2) μ}) :
    OddSymmetricKernel.kernelSubring n :=
  ⟨OddSymmetrizer.schur n (toExponent n μ.1), OddSymmetrizer.schur_mem_kernel n _⟩

theorem piN_sK_of (n : ℕ) (μ : {μ : YoungDiagram // LengthLE (n+2) μ}) :
    piN (n+2) (sK μ.1) = (kernelSchur n μ : SkewPolynomial (n+2)) := by
  have h := (lengthLE_iff _ _).mp μ.2
  rw [OddGrassmannSchur.conjecture_5_3]
  simp only [h, ↓reduceIte]
  rfl

theorem piN_sK_tall (n : ℕ) (μ : YoungDiagram) (h : ¬ LengthLE (n+2) μ) :
    piN (n+2) (sK μ) = 0 := by
  have h' : ¬ μ.colLen 0 ≤ n + 2 := fun h' => h ((lengthLE_iff _ _).mpr h')
  rw [OddGrassmannSchur.conjecture_5_3]
  simp only [h', ↓reduceIte]

theorem coe_linearCombination_kernelSchur (n : ℕ)
    (l : {μ : YoungDiagram // LengthLE (n+2) μ} →₀ ℤ) :
    ((Finsupp.linearCombination ℤ (kernelSchur n) l : OddSymmetricKernel.kernelSubring n) :
      SkewPolynomial (n+2)) =
      piN (n+2) (Finsupp.linearCombination ℤ
        (fun μ : {μ : YoungDiagram // LengthLE (n+2) μ} => sK μ.1) l) := by
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, AddMemClass.coe_add, hf, hg, map_add]
  | single μ a =>
    rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single,
      AddSubgroupClass.coe_zsmul, map_zsmul, piN_sK_of]

theorem kernelSchur_linearIndependent (n : ℕ) : LinearIndependent ℤ (kernelSchur n) := by
  rw [linearIndependent_iff]
  intro l hl
  have h0 : piN (n+2) (Finsupp.linearCombination ℤ
      (fun μ : {μ : YoungDiagram // LengthLE (n+2) μ} => sK μ.1) l) = 0 := by
    rw [← coe_linearCombination_kernelSchur, hl]; rfl
  rw [OddSymmetricLimit.piN_eq_zero_iff_mem_tallSpan, OddSymmetricLimit.tallSpan,
    OddGrassmannSchur.mem_span_sK_iff (fun lam => n + 2 < lam.colLen 0)] at h0
  have e : Finsupp.linearCombination ℤ
      (fun μ : {μ : YoungDiagram // LengthLE (n+2) μ} => sK μ.1) l =
      Finsupp.linearCombination ℤ sBasis (l.mapDomain Subtype.val) := by
    rw [Finsupp.linearCombination_mapDomain]
    congr 2
    funext μ
    simp only [Function.comp_apply, OddGrassmannSchur.sBasis_apply]
  ext μ
  have := h0 μ.1 (fun h => absurd ((lengthLE_iff _ _).mp μ.2) (by omega))
  rw [e, Module.Basis.repr_linearCombination,
    Finsupp.mapDomain_apply_of_injective Subtype.val_injective] at this
  simpa using this

theorem kernelSchur_span (n : ℕ) : ⊤ ≤ Submodule.span ℤ (Set.range (kernelSchur n)) := by
  rintro y -
  obtain ⟨x, rfl⟩ := OddSymmetricLimit.piA_surjective n y
  rw [← sBasis.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun μ _ => ?_
  rw [map_zsmul]
  refine Submodule.smul_mem _ _ ?_
  by_cases h : LengthLE (n+2) μ
  · have : OddSymmetricLimit.piA n (sBasis μ) = kernelSchur n ⟨μ, h⟩ := Subtype.ext (by
      rw [OddSymmetricLimit.piA_coe, OddGrassmannSchur.sBasis_apply, piN_sK_of n ⟨μ, h⟩])
    rw [this]
    exact Submodule.subset_span ⟨_, rfl⟩
  · have : OddSymmetricLimit.piA n (sBasis μ) = 0 := Subtype.ext (by
      rw [OddSymmetricLimit.piA_coe, OddGrassmannSchur.sBasis_apply, piN_sK_tall n μ h]; rfl)
    rw [this]
    exact zero_mem _

/-- EKL's odd Schur polynomials `s̃_λ`, `ℓ(λ) ≤ n + 2`, form a `ℤ`-basis of the odd symmetric
polynomials `OΛ̃_{n+2}`. -/
noncomputable def kernelSchurBasis (n : ℕ) :
    Module.Basis {μ : YoungDiagram // LengthLE (n+2) μ} ℤ (OddSymmetricKernel.kernelSubring n) :=
  Module.Basis.mk (kernelSchur_linearIndependent n) (kernelSchur_span n)

/-! ### The untwisted odd Schur basis of `OΛ_{n+2}` -/

/-- The row lengths of `μ` as an exponent vector in `N` variables. -/
def rowExp (N : ℕ) (μ : YoungDiagram) : Fin N → ℕ := fun i => μ.rowLen i

theorem rowExp_antitone (N : ℕ) (μ : YoungDiagram) : Antitone (rowExp N μ) :=
  fun _ _ h => μ.rowLen_anti _ _ h

/-- The untwisted odd Schur polynomial `s_μ ∈ OPol_N` of Ellis–Qi (3.24). -/
noncomputable def schurU (N : ℕ) (μ : YoungDiagram) : SkewPolynomial N :=
  EQSchur.untwisted N (rowExp N μ)

theorem theta_schurU (n : ℕ) (μ : {μ : YoungDiagram // LengthLE (n+2) μ}) :
    theta (n+2) (schurU (n+2) μ.1) = kernelSchur n μ := by
  rw [schurU, ← EQSchur.twisted_eq_theta_untwisted, EQSchur.twisted_eq_ekl]
  rfl

/-- The untwisted odd Schur polynomials `s_λ`, `ℓ(λ) ≤ n + 2`, form a `ℤ`-basis of `OΛ_{n+2}`. -/
noncomputable def osymSchurBasis (n : ℕ) :
    Module.Basis {μ : YoungDiagram // LengthLE (n+2) μ} ℤ (osym (n+2)) :=
  (kernelSchurBasis n).map (thetaEquiv n).symm

theorem osymSchurBasis_apply (n : ℕ) (μ : {μ : YoungDiagram // LengthLE (n+2) μ}) :
    (osymSchurBasis n μ : SkewPolynomial (n+2)) = schurU (n+2) μ.1 := by
  rw [osymSchurBasis, Module.Basis.map_apply, thetaEquiv_symm_coe, kernelSchurBasis,
    Module.Basis.mk_apply, ← theta_schurU, EQSchur.theta_theta]

/-! ### Proposition 3.11 as a sum over addable white boxes -/

theorem expSingle_self {N : ℕ} (i : Fin N) : expSingle i i = 1 := by
  simp [expSingle]

theorem expSingle_of_ne {N : ℕ} {i j : Fin N} (h : i ≠ j) : expSingle i j = 0 := by
  simp [expSingle, h]

theorem addable_iff_antitone {N : ℕ} (μ : YoungDiagram) (i : Fin N) :
    Addable μ (i.val, μ.rowLen i) ↔ Antitone (rowExp N μ + expSingle i) := by
  rw [addable_iff_rowLen, and_iff_right rfl]
  constructor
  · intro h p q hpq
    have hpq' : p.val ≤ q.val := hpq
    have h1 := μ.rowLen_anti p.val q.val hpq'
    simp only [Pi.add_apply, rowExp]
    rcases eq_or_ne q i with rfl | hq
    · rcases eq_or_ne p q with rfl | hp
      · exact le_rfl
      · rw [expSingle_self, expSingle_of_ne (Ne.symm hp)]
        have hlt : p.val < q.val := lt_of_le_of_ne hpq' (fun e => hp (Fin.ext e))
        have h2 := h (by omega)
        have h3 := μ.rowLen_anti p.val (q.val - 1) (by omega)
        omega
    · rw [expSingle_of_ne (Ne.symm hq)]
      omega
  · intro h h0
    obtain ⟨j, hj⟩ : ∃ j : Fin N, j.val = i.val - 1 := ⟨⟨i.val - 1, by omega⟩, rfl⟩
    have hji : j ≤ i := by change j.val ≤ i.val; omega
    have hne : i ≠ j := fun e => by rw [← e] at hj; omega
    have := h hji
    simp only [Pi.add_apply, rowExp] at this
    rw [expSingle_self, expSingle_of_ne hne, hj] at this
    omega

theorem rowExp_addCell {N : ℕ} {μ : YoungDiagram} {i : Fin N}
    (h : Addable μ (i.val, μ.rowLen i)) :
    rowExp N (addCell μ (i.val, μ.rowLen i)) = rowExp N μ + expSingle i := by
  funext j
  simp only [rowExp, Pi.add_apply, expSingle, rowLen_addCell h]
  congr 1
  by_cases hj : j = i
  · subst hj; simp
  · have : j.val ≠ i.val := fun e => hj (Fin.ext e)
    simp [this, Ne.symm hj]

theorem rowsAbove_rowExp {N : ℕ} (μ : YoungDiagram) (i : Fin N) :
    EQSchur.rowsAbove (rowExp N μ) i = ∑ r ∈ range i.val, μ.rowLen r := by
  rw [EQSchur.rowsAbove_eq]
  simp only [rowExp, Fin.lt_def]
  rw [Fin.sum_univ_eq_sum_range (fun r => if r < i.val then μ.rowLen r else 0) N,
    ← Finset.sum_filter]
  have := i.2
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem content_mod_two {N : ℕ} (μ : YoungDiagram) (i : Fin N) :
    EQSchur.content (rowExp N μ) i % 2 = if IsWhite (i.val, μ.rowLen i) then 1 else 0 := by
  simp only [EQSchur.content, rowExp, IsWhite]
  split_ifs with h <;> omega

theorem addableCells_eq (N : ℕ) (μ : YoungDiagram) :
    addableCells (fun c => IsWhite c ∧ c.1 < N) μ =
      (univ.filter (fun i : Fin N => Addable μ (i.val, μ.rowLen i) ∧
        IsWhite (i.val, μ.rowLen i))).map
        ⟨fun i : Fin N => (i.val, μ.rowLen i), fun _ _ h => Fin.ext (congrArg Prod.fst h)⟩ := by
  ext ⟨a, b⟩
  rw [mem_addableCells, Finset.mem_map]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hw, ha⟩, hadd⟩
    have hb := ((addable_iff_rowLen μ a b).mp hadd).1
    subst hb
    exact ⟨⟨a, ha⟩, ⟨hadd, hw⟩, rfl, rfl⟩
  · rintro ⟨i, ⟨hadd, hw⟩, rfl, rfl⟩
    exact ⟨⟨hw, i.2⟩, hadd⟩

/-- **Proposition 3.11** (Ellis–Qi), in the form used in Appendix A.1:
`d(s_μ) = Σ_{□ addable white, row < N} (-1)^{|μ/i| + i - 1} s_{μ + □}` in `OPol_N`. -/
theorem prop_3_11_cells (N : ℕ) (μ : YoungDiagram) :
    d N (schurU N μ) = ∑ b ∈ addableCells (fun c => IsWhite c ∧ c.1 < N) μ,
      ((schurSign μ b : ℤˣ) : ℤ) • schurU N (addCell μ b) := by
  rw [schurU, EQSchur.prop_3_11 _ (rowExp_antitone N μ), addableCells_eq, Finset.sum_map,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  by_cases hA : Addable μ (i.val, μ.rowLen i)
  · have hA' := (addable_iff_antitone μ i).mp hA
    rw [content_mod_two, rowsAbove_rowExp]
    by_cases hW : IsWhite (i.val, μ.rowLen i)
    · simp only [hA', hW, hA, and_self, ↓reduceIte, mul_one, schurU, rowExp_addCell hA,
        schurSign]
      push_cast
      rfl
    · simp [hA', hW]
  · have hA' : ¬ Antitone (rowExp N μ + expSingle i) := fun h =>
      hA ((addable_iff_antitone μ i).mpr h)
    simp [hA, hA']

/-! ### Proposition A.2 (2) for `OΛ_{n+2}` -/

/-- The hypotheses of `OddSchurData` hold for `OΛ_{n+2}`. -/
noncomputable def oddSchurData (n : ℕ) : OddSchurData (n+2) where
  s := schurU (n+2)
  basis := osymSchurBasis n
  basis_apply := osymSchurBasis_apply n
  prop_3_11 := fun μ _ => prop_3_11_cells (n+2) μ

/-- **Proposition A.2 (2)** (Ellis–Qi), for `N = n + 2`: the cohomology `H(OΛ_N)` is a free
abelian group with basis the classes of the untwisted odd Schur polynomials `s_λ`, `λ` a Lima
partition with at most `N` rows. -/
noncomputable def prop_A_2_two' (n : ℕ) :
    Module.Basis {μ : YoungDiagram // IsLima μ ∧ LengthLE (n+2) μ} ℤ
      (Homology (dOsym (n+2))) :=
  (oddSchurData n).prop_A_2_two

theorem prop_A_2_two'_apply (n : ℕ) (μ : {μ : YoungDiagram // IsLima μ ∧ LengthLE (n+2) μ}) :
    ((prop_A_2_two' n μ : Homology (dOsym (n+2)))) = Submodule.Quotient.mk
      ⟨osymSchurBasis n ⟨μ.1, μ.2.2⟩, LinearMap.mem_ker.mpr (Subtype.ext (by
        rw [dOsym_coe, osymSchurBasis_apply]
        exact (oddSchurData n).lima_cocycle μ.2.1 μ.2.2))⟩ :=
  (oddSchurData n).prop_A_2_two_apply μ

/-- The Lima Schur polynomials `s_λ` (`ℓ(λ) ≤ n + 2`) are cocycles of `OΛ_{n+2}`. -/
theorem lima_cocycle' (n : ℕ) {μ : YoungDiagram} (hμ : IsLima μ) (hn : LengthLE (n+2) μ) :
    d (n+2) (schurU (n+2) μ) = 0 :=
  (oddSchurData n).lima_cocycle hμ hn

/-- Proposition A.2 (2), concretely: every cocycle of `OΛ_{n+2}` is a coboundary plus a
`ℤ`-combination of Lima Schur polynomials. -/
theorem cocycle_eq' (n : ℕ) {f : SkewPolynomial (n+2)} (hf : f ∈ osym (n+2))
    (hdf : d (n+2) f = 0) :
    ∃ g ∈ osym (n+2), ∃ a : {μ : YoungDiagram // IsLima μ ∧ LengthLE (n+2) μ} →₀ ℤ,
      f = d (n+2) g + a.sum (fun μ z => z • schurU (n+2) μ.1) :=
  (oddSchurData n).cocycle_eq hf hdf

/-- Proposition A.2 (2), concretely: a `ℤ`-combination of Lima Schur polynomials which is a
coboundary in `OΛ_{n+2}` is zero. -/
theorem lima_independent' (n : ℕ)
    (a : {μ : YoungDiagram // IsLima μ ∧ LengthLE (n+2) μ} →₀ ℤ)
    {g : SkewPolynomial (n+2)} (hg : g ∈ osym (n+2))
    (h : a.sum (fun μ z => z • schurU (n+2) μ.1) = d (n+2) g) : a = 0 :=
  (oddSchurData n).lima_independent a hg h

end OddMath.Frontier.EQLima
