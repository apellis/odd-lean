import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerSandwich
import Mathlib.RingTheory.Congruence.Hom

/-! # The literal ELV coefficient power quotient

The coefficient instance of (BC) in `DeformedReservoirBound.md`, §2:
quotienting the actual ELV coefficient algebra by the literal elementary
power ideal agrees with the universal quotient by the sum of its two
defining ideals. All maps are induced by the original coefficient maps.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

abbrev CoefficientPowerQuotient :=
  (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.Quotient

abbrev UniversalCoefficientPowerQuotient :=
  (SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L).ringCon.Quotient

private theorem kernel_mem {A B : Type u} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) (a : A) :
    a ∈ TwoSidedIdeal.ofRingCon (RingCon.ker f.toRingHom) ↔ f a = 0 := by
  change f a = f 0 ↔ _
  rw [map_zero]

/-- The universal coefficient map into the actual quotient A/T. -/
def coefficientPowerQuotientMap : SKM.SYM D k →ₐ[k] CoefficientPowerQuotient (k := k) D cutoff L :=
  ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k).comp
    (SKM.SYM.elvCoefficientQuotient D cutoff)

private theorem universalPower_le_kernel :
    SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L ≤
      TwoSidedIdeal.ofRingCon (RingCon.ker (coefficientPowerQuotientMap (k := k) D cutoff L).toRingHom) := by
  apply sup_le
  · intro a ha
    apply (kernel_mem _ _).mpr
    change (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
      (SKM.SYM.elvCoefficientQuotient D cutoff a) = 0
    rw [SKM.SYM.elvCoefficientQuotient_eq_zero D ha, map_zero]
  · apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    apply (kernel_mem _ _).mpr
    change (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
      (SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.e D k a.1 a.2 ^ L a)) = 0
    rw [map_pow]
    exact Quotient.sound (TwoSidedIdeal.subset_span (Set.mem_range_self a))

/-- The prescribed universal quotient maps to the literal actual quotient. -/
def universalToCoefficientPower : UniversalCoefficientPowerQuotient (k := k) D cutoff L →ₐ[k]
    CoefficientPowerQuotient (k := k) D cutoff L :=
  RingCon.liftₐ _ (coefficientPowerQuotientMap D cutoff L)
    (TwoSidedIdeal.ringCon_le_iff.mp (universalPower_le_kernel D cutoff L))

private def elvToUniversalPower : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₐ[k]
    UniversalCoefficientPowerQuotient (k := k) D cutoff L :=
  RingCon.liftₐ _
    ((SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L).ringCon.mkₐ k)
    (fun _ _ h => Quotient.sound
      ((show (SKM.SYM.elvCoefficientIdeal D k cutoff).ringCon ≤
        (SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L).ringCon from
          TwoSidedIdeal.ringCon_le_iff.mp le_sup_left) h))

private theorem actualPower_le_kernel :
    coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L ≤
      TwoSidedIdeal.ofRingCon (RingCon.ker (elvToUniversalPower (k := k) D cutoff L).toRingHom) := by
  apply TwoSidedIdeal.span_le.mpr
  rintro _ ⟨a, rfl⟩
  apply (kernel_mem _ _).mpr
  change elvToUniversalPower D cutoff L
    ((SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.e D k a.1 a.2)) ^ L a) = 0
  rw [← map_pow]
  change (SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L).ringCon.mkₐ k
    (SKM.SYM.e D k a.1 a.2 ^ L a) = 0
  exact Quotient.sound ((le_sup_right : SKM.SYM.coefficientPowerIdeal D k L ≤
    SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L)
      (TwoSidedIdeal.subset_span ⟨a, rfl⟩))

/-- The actual quotient A/T maps to the universal quotient, on the same
coefficient generators. -/
def coefficientPowerToUniversal : CoefficientPowerQuotient (k := k) D cutoff L →ₐ[k]
    UniversalCoefficientPowerQuotient (k := k) D cutoff L :=
  RingCon.liftₐ _ (elvToUniversalPower D cutoff L)
    (TwoSidedIdeal.ringCon_le_iff.mp (actualPower_le_kernel D cutoff L))

@[simp] theorem coefficientPowerToUniversal_apply (a : SKM.SYM D k) :
    coefficientPowerToUniversal D cutoff L (coefficientPowerQuotientMap D cutoff L a) =
      (SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L).ringCon.mkₐ k a := rfl

private theorem actual_roundtrip :
    (universalToCoefficientPower (k := k) D cutoff L).comp (coefficientPowerToUniversal D cutoff L) =
      AlgHom.id k (CoefficientPowerQuotient (k := k) D cutoff L) := by
  apply AlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := RingCon.mkₐ_surjective (α := k)
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon x
  obtain ⟨b, rfl⟩ := RingCon.mkₐ_surjective (α := k) (SKM.SYM.elvCoefficientIdeal D k cutoff).ringCon a
  rfl

private theorem universal_roundtrip :
    (coefficientPowerToUniversal (k := k) D cutoff L).comp (universalToCoefficientPower D cutoff L) =
      AlgHom.id k (UniversalCoefficientPowerQuotient (k := k) D cutoff L) := by
  apply AlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := RingCon.mkₐ_surjective (α := k)
    (SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L).ringCon x
  rfl

/-- The coefficient instance of (BC): the literal actual power quotient
is algebra-isomorphic to the universal quotient by J plus the powers. -/
def coefficientPowerQuotientEquiv : CoefficientPowerQuotient (k := k) D cutoff L ≃ₐ[k]
    UniversalCoefficientPowerQuotient (k := k) D cutoff L :=
  AlgEquiv.ofAlgHom (coefficientPowerToUniversal D cutoff L) (universalToCoefficientPower D cutoff L)
    (universal_roundtrip D cutoff L) (actual_roundtrip D cutoff L)

/-- The coefficient-algebra presentation kernel is exactly the sum of
the defining ELV ideal and elementary powers. This is not a statement
about the kernel of a vacuum action or diagram evaluation. -/
theorem coefficientPowerQuotientMap_eq_zero_iff (a : SKM.SYM D k) :
    coefficientPowerQuotientMap D cutoff L a = 0 ↔
      a ∈ SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L := by
  constructor
  · intro h
    have hz := congrArg (coefficientPowerToUniversal D cutoff L) h
    rw [coefficientPowerToUniversal_apply, map_zero] at hz
    exact Quotient.exact hz
  · intro ha
    apply (coefficientPowerQuotientEquiv D cutoff L).injective
    exact (show (SKM.SYM.elvCoefficientIdeal D k cutoff ⊔
      SKM.SYM.coefficientPowerIdeal D k L).ringCon.mkₐ k a = 0 from Quotient.sound ha).trans
        (map_zero (coefficientPowerQuotientEquiv (k := k) D cutoff L)).symm

end OddMath.QuiverHecke.ELVOld
