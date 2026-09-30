import OddMath.Frontier.EQLimaOsym
import OddMath.Frontier.SmallRank

/-!
# Ellis–Qi, Proposition A.2 (2) in every rank

A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Proposition A.2 (2): `H(OΛ_N)` is a free abelian group with basis the classes of the untwisted
odd Schur polynomials `s_λ`, `λ` a Lima partition with at most `N` rows — here for **every**
`N ≥ 0`, including `OΛ_0 = ℤ` and `OΛ_1 = OPol_1 = ℤ[x]` (`d x = x²`), where the only Lima
partition is `∅` and `H(OΛ_N) ≅ ℤ` on the class of `1`.

* `map_theta_osym_OLam`: `θ(OΛ_N) = OΛ̃_N` (EKL's `OΛ_N`, `SmallRank.OLam N`) in every rank;
* `olamSchurBasis N`: EKL's odd Schur polynomials `s̃_λ = SmallRank.schurAll N λ`, `ℓ(λ) ≤ N`,
  form a `ℤ`-basis of `OΛ̃_N` (for `N ≤ 1`, `s̃_(k) = x^k`);
* `osymSchurBasisAll N`: the untwisted `s_λ = θ(s̃_λ)` form a `ℤ`-basis of `OΛ_N`;
* `oddSchurDataAll N`, `prop_A_2_two_all N` and the concrete forms `cocycle_eq_all`,
  `lima_independent_all`.
-/

namespace OddMath.Frontier.EQLima

open Finset
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open OddMath.Frontier.EQSkewDifferential (osym d theta elementary)
open SmallRank (OLam schurAll)

/-! ### `θ(OΛ_N) = OΛ̃_N` in every rank -/

theorem E_eq_OLam (N : ℕ) : ElementaryBranching.E N = OLam N := by
  rcases N with _ | _ | n
  · refine le_antisymm (by rw [SmallRank.OLam_small (by omega)]; exact le_top) ?_
    rw [SmallRank.OLam_eq_elementaryClosure]
    exact Subring.closure_mono (fun _ ⟨k, _, _, hk⟩ => ⟨k, hk.symm⟩)
  · refine le_antisymm (by rw [SmallRank.OLam_small (by omega)]; exact le_top) ?_
    rw [SmallRank.OLam_eq_elementaryClosure]
    exact Subring.closure_mono (fun _ ⟨k, _, _, hk⟩ => ⟨k, hk.symm⟩)
  · exact StaircaseIndependence.E_eq_kernel n

theorem map_theta_osym_OLam (N : ℕ) : (osym N).map (theta N) = OLam N := by
  rw [map_theta_osym, E_eq_OLam]

theorem theta_mem_OLam {N : ℕ} {f : SkewPolynomial N} (hf : f ∈ osym N) :
    theta N f ∈ OLam N := by
  rw [← map_theta_osym_OLam]; exact ⟨f, hf, rfl⟩

theorem theta_mem_osym_of_OLam {N : ℕ} {g : SkewPolynomial N} (hg : g ∈ OLam N) :
    theta N g ∈ osym N := by
  rw [← map_theta_osym_OLam] at hg
  obtain ⟨f, hf, rfl⟩ := hg
  rwa [EQSchur.theta_theta]

/-- `θ : OΛ_N ≅ OΛ̃_N` as abelian groups, in every rank. -/
noncomputable def thetaEquivAll (N : ℕ) : osym N ≃ₗ[ℤ] OLam N :=
  AddEquiv.toIntLinearEquiv
    { toFun := fun f => ⟨theta N (f : SkewPolynomial N), theta_mem_OLam f.2⟩
      invFun := fun g => ⟨theta N (g : SkewPolynomial N), theta_mem_osym_of_OLam g.2⟩
      left_inv := fun _ => Subtype.ext (EQSchur.theta_theta _)
      right_inv := fun _ => Subtype.ext (EQSchur.theta_theta _)
      map_add' := fun f g => Subtype.ext
        (map_add (theta N) (f : SkewPolynomial N) (g : SkewPolynomial N)) }

theorem thetaEquivAll_symm_coe (N : ℕ) (g : OLam N) :
    ((thetaEquivAll N).symm g : SkewPolynomial N) = theta N g := rfl

/-! ### Row diagrams and exponent vectors -/

/-- The one-row partition `(k)`. -/
def rowDiagram (k : ℕ) : YoungDiagram where
  cells := (range 1) ×ˢ (range k)
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at ha ⊢
    exact ⟨lt_of_le_of_lt hba.1 ha.1, lt_of_le_of_lt hba.2 ha.2⟩

theorem mem_rowDiagram (k : ℕ) (c : ℕ × ℕ) : c ∈ rowDiagram k ↔ c.1 = 0 ∧ c.2 < k := by
  change c ∈ (range 1) ×ˢ (range k) ↔ _
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range, Nat.lt_one_iff]

theorem rowExp_injective {N : ℕ} {μ ν : YoungDiagram} (hμ : LengthLE N μ) (hν : LengthLE N ν)
    (h : rowExp N μ = rowExp N ν) : μ = ν := by
  apply YoungDiagram.ext
  ext ⟨i, j⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells]
  by_cases hi : i < N
  · have := congrFun h ⟨i, hi⟩
    simp only [rowExp] at this
    rw [YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen, this]
  · exact ⟨fun hm => absurd (hμ _ hm) hi, fun hm => absurd (hν _ hm) hi⟩

theorem exists_rowExp_small {N : ℕ} (hN : N ≤ 1) (a : Fin N → ℕ) :
    ∃ μ, LengthLE N μ ∧ rowExp N μ = a := by
  rcases (by omega : N = 0 ∨ N = 1) with rfl | rfl
  · refine ⟨⊥, fun c hc => absurd hc (YoungDiagram.notMem_bot c), funext fun i => i.elim0⟩
  · refine ⟨rowDiagram (a 0), fun c hc => ?_, funext fun i => ?_⟩
    · have := ((mem_rowDiagram _ c).mp hc).1; omega
    · have hi : i = 0 := Fin.ext (by have := i.2; omega)
      subst hi
      simp only [rowExp]
      apply rowLen_eq_of
      intro j
      rw [mem_rowDiagram]
      simp

/-! ### The odd Schur basis of `OΛ̃_N` -/

/-- EKL's odd Schur polynomial `s̃_λ ∈ OΛ̃_N`, `ℓ(λ) ≤ N`. -/
noncomputable def olamSchur (N : ℕ) (μ : {μ : YoungDiagram // LengthLE N μ}) : OLam N :=
  ⟨schurAll N (rowExp N μ.1), SmallRank.Sym_mem N _⟩

theorem olamSchur_linearIndependent (N : ℕ) : LinearIndependent ℤ (olamSchur N) := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have hN' : N ≤ 1 := by omega
    apply LinearIndependent.of_comp (OLam N).toAddSubgroup.subtype.toIntLinearMap
    have e : (OLam N).toAddSubgroup.subtype.toIntLinearMap ∘ olamSchur N =
        (Finsupp.basisSingleOne : Module.Basis (Fin N → ℕ) ℤ (SkewPolynomial N)) ∘
          (fun μ : {μ : YoungDiagram // LengthLE N μ} => rowExp N μ.1) := by
      funext μ
      simp only [Function.comp_apply, AddMonoidHom.coe_toIntLinearMap, AddSubgroup.coe_subtype,
        Finsupp.coe_basisSingleOne]
      change schurAll N (rowExp N μ.1) = _
      rw [SmallRank.schurAll_small hN']
    rw [e]
    exact Finsupp.basisSingleOne.linearIndependent.comp _
      (fun μ ν h => Subtype.ext (rowExp_injective μ.2 ν.2 h))
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    exact kernelSchur_linearIndependent n

theorem olamSchur_span (N : ℕ) : ⊤ ≤ Submodule.span ℤ (Set.range (olamSchur N)) := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have hN' : N ≤ 1 := by omega
    rintro ⟨y, hy⟩ -
    have hy' : (⟨y, hy⟩ : OLam N) = ∑ a ∈ y.support, y a • (⟨monomial a 1,
        SmallRank.mem_OLam_small hN' _⟩ : OLam N) := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [AddSubgroupClass.coe_zsmul]
      conv_lhs => rw [← Finsupp.sum_single y]
      rw [Finsupp.sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [monomial, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hy']
    refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
    obtain ⟨μ, hμ, rfl⟩ := exists_rowExp_small hN' a
    refine Submodule.subset_span ⟨⟨μ, hμ⟩, Subtype.ext ?_⟩
    change schurAll N (rowExp N μ) = _
    rw [SmallRank.schurAll_small hN']
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    exact kernelSchur_span n

/-- EKL's odd Schur polynomials `s̃_λ`, `ℓ(λ) ≤ N`, form a `ℤ`-basis of `OΛ̃_N`, every `N`. -/
noncomputable def olamSchurBasis (N : ℕ) :
    Module.Basis {μ : YoungDiagram // LengthLE N μ} ℤ (OLam N) :=
  Module.Basis.mk (olamSchur_linearIndependent N) (olamSchur_span N)

theorem theta_schurU_all (N : ℕ) (μ : YoungDiagram) :
    theta N (schurU N μ) = schurAll N (rowExp N μ) := by
  rw [schurU, ← EQSchur.twisted_eq_theta_untwisted, EQSchur.twisted_eq_schurAll]

/-- The untwisted odd Schur polynomials `s_λ`, `ℓ(λ) ≤ N`, form a `ℤ`-basis of `OΛ_N`, every
`N`. -/
noncomputable def osymSchurBasisAll (N : ℕ) :
    Module.Basis {μ : YoungDiagram // LengthLE N μ} ℤ (osym N) :=
  (olamSchurBasis N).map (thetaEquivAll N).symm

theorem osymSchurBasisAll_apply (N : ℕ) (μ : {μ : YoungDiagram // LengthLE N μ}) :
    (osymSchurBasisAll N μ : SkewPolynomial N) = schurU N μ.1 := by
  rw [osymSchurBasisAll, Module.Basis.map_apply, thetaEquivAll_symm_coe, olamSchurBasis,
    Module.Basis.mk_apply]
  change theta N (schurAll N (rowExp N μ.1)) = _
  rw [← theta_schurU_all, EQSchur.theta_theta]

/-! ### Proposition A.2 (2), every rank -/

/-- The hypotheses of `OddSchurData` hold for `OΛ_N`, every `N`. -/
noncomputable def oddSchurDataAll (N : ℕ) : OddSchurData N where
  s := schurU N
  basis := osymSchurBasisAll N
  basis_apply := osymSchurBasisAll_apply N
  prop_3_11 := fun μ _ => prop_3_11_cells N μ

/-- **Proposition A.2 (2)** (Ellis–Qi), every `N ≥ 0`: `H(OΛ_N)` is a free abelian group with
basis the classes of the untwisted odd Schur polynomials `s_λ`, `λ` a Lima partition with
`ℓ(λ) ≤ N`. -/
noncomputable def prop_A_2_two_all (N : ℕ) :
    Module.Basis {μ : YoungDiagram // IsLima μ ∧ LengthLE N μ} ℤ (Homology (dOsym N)) :=
  (oddSchurDataAll N).prop_A_2_two

theorem prop_A_2_two_all_apply (N : ℕ) (μ : {μ : YoungDiagram // IsLima μ ∧ LengthLE N μ}) :
    prop_A_2_two_all N μ = Submodule.Quotient.mk
      ⟨osymSchurBasisAll N ⟨μ.1, μ.2.2⟩, LinearMap.mem_ker.mpr (Subtype.ext (by
        rw [dOsym_coe, osymSchurBasisAll_apply]
        exact (oddSchurDataAll N).lima_cocycle μ.2.1 μ.2.2))⟩ :=
  (oddSchurDataAll N).prop_A_2_two_apply μ

/-- Proposition A.2 (2), every `N`: every cocycle of `OΛ_N` is a coboundary plus a
`ℤ`-combination of Lima Schur polynomials. -/
theorem cocycle_eq_all (N : ℕ) {f : SkewPolynomial N} (hf : f ∈ osym N) (hdf : d N f = 0) :
    ∃ g ∈ osym N, ∃ a : {μ : YoungDiagram // IsLima μ ∧ LengthLE N μ} →₀ ℤ,
      f = d N g + a.sum (fun μ z => z • schurU N μ.1) :=
  (oddSchurDataAll N).cocycle_eq hf hdf

/-- Proposition A.2 (2), every `N`: a `ℤ`-combination of Lima Schur polynomials which is a
coboundary in `OΛ_N` is zero. -/
theorem lima_independent_all (N : ℕ) (a : {μ : YoungDiagram // IsLima μ ∧ LengthLE N μ} →₀ ℤ)
    {g : SkewPolynomial N} (hg : g ∈ osym N) (h : a.sum (fun μ z => z • schurU N μ.1) = d N g) :
    a = 0 :=
  (oddSchurDataAll N).lima_independent a hg h

/-- In ranks `N ≤ 1` the only Lima partition with at most `N` rows is `∅`. -/
theorem lima_lengthLE_small {N : ℕ} (hN : N ≤ 1) {μ : YoungDiagram} (hμ : IsLima μ)
    (hn : LengthLE N μ) : μ = ⊥ := by
  apply YoungDiagram.ext
  ext ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, YoungDiagram.cells_bot, Finset.notMem_empty, iff_false]
  intro hm
  have hi := hn _ hm
  simp only at hi
  have h0 : (0, 0) ∈ μ := μ.up_left_mem (Nat.zero_le _) (Nat.zero_le _) hm
  have hr := (hμ 0).2
  simp only [Nat.mul_zero, Nat.zero_add] at hr
  have : 0 < μ.rowLen 1 := by rw [hr]; exact YoungDiagram.mem_iff_lt_rowLen.mp h0
  exact absurd (hn (1, 0) (YoungDiagram.mem_iff_lt_rowLen.mpr this)) (by simp only; omega)

end OddMath.Frontier.EQLima
