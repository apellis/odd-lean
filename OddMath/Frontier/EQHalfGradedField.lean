import DG.HalfGraded.Field

/-!
# Ellis–Qi §2.2.4 over a field

Ellis–Qi, arXiv:1504.01712v2, §2.2.4, equation (2.17): the compact super
Grothendieck group is the Gaussian integers. Here the parity relation is explicit:
the ordinary even Grothendieck group does not satisfy `(1 + q²)[K] = 0`.
The Gaussian-linear equivalence agrees with the original additive equivalence:
Gaussian scalars act on every class, and actual internal shifts act by powers of `√-1`.
In particular, shifts by `1` and `-1` of the regular object map to `√-1` and `-√-1`.

These statements use dg-lean's weight-category realization of half-graded modules.
The separate `EQDiagonal` consumer equips the existing nilHecke dg ring with the
diagonal half-grading; no derived-category comparison with this field computation
is asserted. The ground ring here is a field, not `ℤ`; tensor-product multiplicativity
and the later categorification headlines are not asserted. The primary-source
paragraph was checked against v2.
-/

noncomputable section

open CategoryTheory LaurentPolynomial DG DG.HalfGradedDGRing

universe u

namespace OddMath.Frontier.EQHalfGraded

variable (K : Type u) [Field K]
  [CatModule.HasDerivedCategory.{u, u} (Field.Cat K 2)]

/-- The compact super Grothendieck group in the field case of (2.17). -/
abbrev superK0EquivGaussian : SuperK0c.{u, u} (degreeZero K (2 : ℤ)) ≃+ GaussianInt :=
  Field.superK0EquivGaussianInt K

/-- The regular module represents `1`. -/
theorem superK0EquivGaussian_regular :
    superK0EquivGaussian K (K0Rel.mk ⟨Field.obj K 2 0, Field.isCompact_obj 0⟩) = 1 :=
  Field.superK0EquivGaussianInt_cls K

/-- The actual internal shift `⟨1⟩` of the regular object represents `√-1`. -/
theorem superK0EquivGaussian_shift_regular :
    superK0EquivGaussian K
      (K0Rel.mk (((CatModule.DerivedCategory.compactInternalShiftAction
        (degreeZero K (2 : ℤ)).Regraded).functor 1).obj
        ⟨Field.obj K 2 0, Field.isCompact_obj 0⟩)) = (⟨0, 1⟩ : GaussianInt) := by
  change GaussianQuot.equivGaussianInt (Field.toSuperQuot K 2
    (K0.mk (((CatModule.DerivedCategory.compactInternalShiftAction
      (degreeZero K (2 : ℤ)).Regraded).functor 1).obj
      ⟨Field.obj K 2 0, Field.isCompact_obj 0⟩))) = _
  rw [← CatModule.DerivedCategory.T_smul_mk_compact]
  change GaussianQuot.equivGaussianInt
    (Field.toSuperQuot K 2 ((T 1 : LaurentPolynomial ℤ) • Field.cls K 2 0)) = _
  rw [Field.toSuperQuot_smul_cls]
  change GaussianQuot.evalI (T 1) = _
  simp [GaussianQuot.evalI, GaussianQuot.unitI]

/-- The field computation is linear for the canonical Gaussian scalars. -/
abbrev superK0GaussianLinearEquiv :
    SuperK0c.{u, u} (degreeZero K (2 : ℤ)) ≃ₗ[GaussianInt] GaussianInt :=
  Field.superK0GaussianLinearEquiv K

/-- Forgetting scalar compatibility recovers the original additive computation. -/
@[simp]
theorem superK0GaussianLinearEquiv_apply (x : SuperK0c.{u, u} (degreeZero K (2 : ℤ))) :
    superK0GaussianLinearEquiv K x = superK0EquivGaussian K x := rfl

/-- The regular class is still the unit under the linear computation. -/
theorem superK0GaussianLinearEquiv_regular :
    superK0GaussianLinearEquiv K (K0Rel.mk ⟨Field.obj K 2 0, Field.isCompact_obj 0⟩) = 1 :=
  Field.superK0GaussianLinearEquiv_cls K

/-- Scalar compatibility holds for every super class, not only the regular class. -/
theorem superK0GaussianLinearEquiv_smul (z : GaussianInt)
    (x : SuperK0c.{u, u} (degreeZero K (2 : ℤ))) :
    superK0GaussianLinearEquiv K (z • x) = z * superK0GaussianLinearEquiv K x :=
  (superK0GaussianLinearEquiv K).map_smul z x

/-- Every actual compact internal shift is multiplication by the corresponding power of `i`. -/
theorem superK0GaussianLinearEquiv_internalShift (n : ℤ)
    (X : (Field.compacts K 2).FullSubcategory) :
    superK0GaussianLinearEquiv K
      (K0Rel.mk (((CatModule.DerivedCategory.compactInternalShiftAction
        (degreeZero K (2 : ℤ)).Regraded).functor n).obj X)) =
      ((GaussianQuot.unitI ^ n : GaussianIntˣ) : GaussianInt) *
        superK0GaussianLinearEquiv K (K0Rel.mk X) :=
  Field.superK0GaussianLinearEquiv_internalShift K n X

/-- The actual positive unit shift of the regular object represents `i`. -/
theorem superK0GaussianLinearEquiv_shift_regular :
    superK0GaussianLinearEquiv K
      (K0Rel.mk (((CatModule.DerivedCategory.compactInternalShiftAction
        (degreeZero K (2 : ℤ)).Regraded).functor 1).obj
        ⟨Field.obj K 2 0, Field.isCompact_obj 0⟩)) = (⟨0, 1⟩ : GaussianInt) := by
  rw [superK0GaussianLinearEquiv_internalShift, superK0GaussianLinearEquiv_regular]
  simp [GaussianQuot.unitI]

/-- The actual negative unit shift of the regular object represents `-i`. -/
theorem superK0GaussianLinearEquiv_negShift_regular :
    superK0GaussianLinearEquiv K
      (K0Rel.mk (((CatModule.DerivedCategory.compactInternalShiftAction
        (degreeZero K (2 : ℤ)).Regraded).functor (-1)).obj
        ⟨Field.obj K 2 0, Field.isCompact_obj 0⟩)) = (⟨0, -1⟩ : GaussianInt) := by
  rw [superK0GaussianLinearEquiv_internalShift, superK0GaussianLinearEquiv_regular]
  simp [GaussianQuot.unitI]

/-- The ordinary even Grothendieck group has four independent shift classes, so the
super relation must not silently be imposed on it. -/
theorem even_super_relation_ne_zero :
    (1 + T 2 : LaurentPolynomial ℤ) • Field.cls K 2 0 ≠ 0 := by
  intro h
  have h' : Field.K0Basis K 2 (0 : Fin 4) + Field.K0Basis K 2 (2 : Fin 4) = 0 := by
    rw [Field.K0Basis_apply, Field.K0Basis_apply]
    change (T 0 : LaurentPolynomial ℤ) • Field.cls K 2 0 +
      (T 2 : LaurentPolynomial ℤ) • Field.cls K 2 0 = 0
    simpa only [T_zero, one_smul, _root_.add_smul] using h
  have hh := congrArg (fun x => (Field.K0Basis K 2).repr x (0 : Fin 4)) h'
  simp at hh

/-- The square of the internal unit shift is the translation up to parity.
This is an odd natural isomorphism, not an even one after deleting `Π`. -/
def internalShiftSquaredOddIso :
    CatModule.DerivedCategory.internalShift.{u, u} (degreeZero K (2 : ℤ)).Regraded 1 ⋙
      CatModule.DerivedCategory.internalShift (degreeZero K (2 : ℤ)).Regraded 1 ≅
    shiftFunctor _ (1 : ℤ) ⋙ parityShiftD (degreeZero K (2 : ℤ)) :=
  internalShiftOneOneOddIso (degreeZero K (2 : ℤ)) rfl

/-- Even isomorphisms cannot identify the twice-internally-shifted regular compact
object with its translation; the parity factor in the odd comparison is essential. -/
theorem no_even_shiftTwo_translation_regular :
    ¬ Nonempty
      ((((CatModule.DerivedCategory.compactInternalShiftAction
        (degreeZero K (2 : ℤ)).Regraded).functor 2).obj
        (⟨Field.obj K 2 0, Field.isCompact_obj 0⟩ : (Field.compacts K 2).FullSubcategory)) ≅
        (⟨Field.obj K 2 0, Field.isCompact_obj 0⟩ :
          (Field.compacts K 2).FullSubcategory)⟦(1 : ℤ)⟧) := by
  rintro ⟨e⟩
  have h := K0.mk_eq_of_iso e
  rw [← CatModule.DerivedCategory.T_smul_mk_compact, K0.mk_shift_one] at h
  change (T 2 : LaurentPolynomial ℤ) • Field.cls K 2 0 = -Field.cls K 2 0 at h
  apply even_super_relation_ne_zero K
  rw [_root_.add_smul, one_smul, h, add_neg_cancel]

end OddMath.Frontier.EQHalfGraded
