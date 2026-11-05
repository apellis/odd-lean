import OddMath.SKM.ELVScalarSpecialization
import OddMath.SKM.BubbleSubstitution
import OddMath.SKM.BubbleCoefficientGrading
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientCategory

/-! # Parity of ordinary ELV coefficient specialization

The scalar specialization in `InvertibleDotProbe.md` §1 kills every odd
homogeneous coefficient. This is the input needed to specialize signed
coefficient tensor composition to the ordinary affine Hom category.
It is independent of integer grading or positive-weight truncation.
-/
noncomputable section
open scoped Classical TensorProduct
namespace OddMath.SKM.SYM
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] (D : Datum I X)

theorem scalarEvaluation_oddLinear (values : I × ℕ → k) (x : OddModule D k) :
    scalarEvaluation D values (oddLinear D k x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | single i c => rw [oddLinear_single, map_smul, scalarEvaluation_delta, smul_zero]

theorem scalarEvaluation_exterior_positive (values : I × ℕ → k) (n : ℕ)
    (hn : 0 < n) {x : ExteriorAlgebra k (OddModule D k)}
    (hx : x ∈ ⋀[k]^n (OddModule D k)) :
    scalarEvaluation D values (exteriorInclude D k x) = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    rw [ExteriorAlgebra.exteriorPower, pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun y _ z hz => ?_) (fun y z hy hz => ?_)
    · obtain ⟨v, rfl⟩ := hz
      rw [map_mul, map_mul, exteriorInclude_ι, scalarEvaluation_oddLinear, mul_zero]
    · rw [map_add, map_add, hy, hz, add_zero]

theorem scalarEvaluation_coefficientBasis_exterior (values : I × ℕ → k)
    (a : CoefficientIndex D) (ha : a.2.Nonempty) :
    scalarEvaluation D values (coefficientBasis D k a) = 0 := by
  rw [coefficientBasis_eq_mul, map_mul,
    scalarEvaluation_exterior_positive D values a.2.card (Finset.card_pos.mpr ha)
      (oddExteriorBasis_mem D k a.2), mul_zero]

/-- Scalar evaluation kills the odd part in the actual coefficient grading,
rather than declaring exterior coefficients even in a target module. -/
theorem scalarEvaluation_odd_zero (values : I × ℕ → k) {x : SYM D k}
    (hx : polynomialExteriorEquiv D k x ∈ polynomialExteriorParity D k 1) :
    scalarEvaluation D values x = 0 := by
  let P : SYM D k →ₗ[k] SYM D k :=
    (polynomialExteriorEquiv D k).symm.toLinearMap.comp
      ((GradedAlgebra.proj (polynomialExteriorParity D k) 1).comp
        (polynomialExteriorEquiv D k).toLinearMap)
  have hzero : (scalarEvaluation D values).toLinearMap.comp P = 0 := by
    apply (coefficientBasis D k).ext
    intro a
    change scalarEvaluation D values
      ((polynomialExteriorEquiv D k).symm
        (GradedAlgebra.proj (polynomialExteriorParity D k) 1
          (polynomialExteriorEquiv D k (coefficientBasis D k a)))) = 0
    rw [GradedAlgebra.proj_apply]
    by_cases hp : (a.2.card : ZMod 2) = 1
    · have ha := coefficientBasis_mem_parity D k a
      rw [hp] at ha
      rw [DirectSum.decompose_of_mem_same _ ha, AlgEquiv.symm_apply_apply]
      apply scalarEvaluation_coefficientBasis_exterior
      by_contra h
      have he : a.2 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp [he] at hp
    · rw [DirectSum.decompose_of_mem_ne _ (coefficientBasis_mem_parity D k a) hp,
        map_zero, map_zero]
  have hP : P x = x := by
    change (polynomialExteriorEquiv D k).symm
      (GradedAlgebra.proj (polynomialExteriorParity D k) 1 (polynomialExteriorEquiv D k x)) = x
    rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same _ hx,
      AlgEquiv.symm_apply_apply]
  have h := LinearMap.congr_fun hzero x
  change scalarEvaluation D values (P x) = 0 at h
  rwa [hP] at h

private theorem scalarPolyExterior_proj_sum (x : PolynomialExterior D k) :
    GradedAlgebra.proj (polynomialExteriorParity D k) 0 x +
      GradedAlgebra.proj (polynomialExteriorParity D k) 1 x = x := by
  let G := polynomialExteriorParity D k
  change GradedAlgebra.proj G 0 x + GradedAlgebra.proj G 1 x = x
  refine DirectSum.Decomposition.inductionOn G (by simp) ?_ ?_ x
  · intro p x
    rcases StringDiagrams.Supercategory.parity_eq_zero_or_one p with rfl | rfl
    · simp only [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same G x.property,
        DirectSum.decompose_of_mem_ne G x.property (by decide : (0 : ZMod 2) ≠ 1), add_zero]
    · simp only [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same G x.property,
        DirectSum.decompose_of_mem_ne G x.property (by decide : (1 : ZMod 2) ≠ 0), zero_add]
  · intro x y hx hy
    simp only [map_add]
    calc
      (GradedAlgebra.proj G 0 x + GradedAlgebra.proj G 0 y) +
          (GradedAlgebra.proj G 1 x + GradedAlgebra.proj G 1 y) =
        (GradedAlgebra.proj G 0 x + GradedAlgebra.proj G 1 x) +
          (GradedAlgebra.proj G 0 y + GradedAlgebra.proj G 1 y) :=
        add_add_add_comm _ _ _ _
      _ = x + y := congrArg₂ (· + ·) hx hy

/-- An odd class has an odd representative, using only the public quotient map
and its parity preservation. The central coefficient-category module is unchanged. -/
theorem elvScalarOddRepresentative (cutoff : I → ℕ)
    {b : ELVCoefficientAlgebra (k := k) D cutoff}
    (hb : b ∈ elvCoefficientParity D cutoff 1) :
    ∃ a ∈ polynomialExteriorParity D k 1, elvModelQuotient D cutoff a = b := by
  have hq : Function.Surjective (elvModelQuotient (k := k) D cutoff) :=
    (RingCon.mkₐ_surjective (α := k) (elvCoefficientIdeal D k cutoff).ringCon).comp
      (polynomialExteriorEquiv D k).symm.surjective
  obtain ⟨a, rfl⟩ := hq b
  have h0 := elvModelQuotient_mem (k := k) D (cutoff := cutoff)
    (DirectSum.decompose (polynomialExteriorParity D k) a 0).property
  have h1 := elvModelQuotient_mem (k := k) D (cutoff := cutoff)
    (DirectSum.decompose (polynomialExteriorParity D k) a 1).property
  have hs : elvModelQuotient D cutoff
      (GradedAlgebra.proj (polynomialExteriorParity D k) 0 a) +
      elvModelQuotient D cutoff
        (GradedAlgebra.proj (polynomialExteriorParity D k) 1 a) =
      elvModelQuotient D cutoff a := by
    rw [← map_add, scalarPolyExterior_proj_sum]
  have he := congrArg (GradedAlgebra.proj (elvCoefficientParity D cutoff) 1) hs
  refine ⟨GradedAlgebra.proj (polynomialExteriorParity D k) 1 a,
    (DirectSum.decompose (polynomialExteriorParity D k) a 1).property, ?_⟩
  simpa only [map_add, GradedAlgebra.proj_apply,
    DirectSum.decompose_of_mem_ne _ h0 (by decide : (0 : ZMod 2) ≠ 1),
    DirectSum.decompose_of_mem_same _ h1, DirectSum.decompose_of_mem_same _ hb,
    zero_add] using he

theorem elvScalarEvaluation_odd_zero (cutoff : I → ℕ) (values : I × ℕ → k)
    (hvalues : ∀ i r, elvElementaryRank D cutoff i ≤ r → values (i,r) = 0)
    {x : ELVCoefficientAlgebra (k := k) D cutoff}
    (hx : x ∈ elvCoefficientParity D cutoff 1) :
    elvScalarEvaluation D cutoff values hvalues x = 0 := by
  obtain ⟨y, hy, rfl⟩ := elvScalarOddRepresentative D cutoff hx
  change elvScalarEvaluation D cutoff values hvalues
    (elvCoefficientQuotient D cutoff ((polynomialExteriorEquiv D k).symm y)) = 0
  rw [elvScalarEvaluation_quotient]
  apply scalarEvaluation_odd_zero
  rw [AlgEquiv.apply_symm_apply]
  exact hy

end OddMath.SKM.SYM
