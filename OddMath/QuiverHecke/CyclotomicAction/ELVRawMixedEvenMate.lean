/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVRawMixedMate

/-! # The even dotted mate of the raw coefficient

This is the even raw-coefficient mate input for the distinct-colour inverse
assembly in docs/Nondegeneracy/SwappedActionAssembly.md, §5. The actual
coefficient, chosen transpose and Hom-shift witness remain unchanged.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
universe u
attribute [local instance] elvOddPiQuiver elvOddPiCategoryStruct elvOddHomCategory piSCatHomPi

private theorem sourceNorm_ofProducer {k : Type u} [CommRing k]
    {A B C Q : PiSCat.{u, u, u + 1} k} (F : C ⟶ Q) (t : End F)
    (hNorm : ∀ (G : Superfunctor k A.carrier C.carrier) (b : End G),
      b ∈ parity (R := k) _ _ 0 → IsUnit b →
        IsUnit (show End (G.comp F) from
          Superfunctor.whiskerLeft G t - Superfunctor.whiskerRight b F))
    (E : A ⟶ B) (K : B ⟶ C) (a : End E)
    (ha : a ∈ parity (R := k) _ _ 0) (hu : IsUnit a) :
    IsUnit (show End (E ≫ (K ≫ F)) from
      Superfunctor.whiskerRight a (K.comp F) -
        Superfunctor.whiskerLeft E (Superfunctor.whiskerLeft K t)) := by
  have hv : IsUnit (show End (E.comp K) from Superfunctor.whiskerRight a K) := by
    change IsUnit (show End (E ≫ K) from a ▷ K)
    exact hu.map ((SKM.homPost (k := k) (B := PiSCat.{u, u, u + 1} k)
      (a := A) (b := B) (c := C) K).mapEnd E)
  have hh := hNorm (E.comp K) (Superfunctor.whiskerRight a K)
    (Superfunctor.whiskerRight_mem ha K) hv
  have hh' := hh.neg
  simp only [neg_sub] at hh'
  change IsUnit (show End ((E.comp K).comp F) from
    Superfunctor.whiskerRight (Superfunctor.whiskerRight a K) F -
      Superfunctor.whiskerLeft (E.comp K) t)
  exact hh'

/-- Attach a source norm to its prescribed mixed dots before specializing the categories. -/
private theorem mixedSourceNorm_ofTranspose {k : Type u} [CommRing k]
    {A B C Q : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (κ : ZMod 2) (H : B ⟶ C)
    {E' : Q ⟶ C} {F' : C ⟶ Q} (adj : SKM.SuperAdjunction (k := k) E' F') (d : End E')
    (hNorm : ∀ (G : Superfunctor k A.carrier C.carrier) (b : End G),
      b ∈ parity (R := k) _ _ 0 → IsUnit b →
        IsUnit (show End (G.comp F') from
          Superfunctor.whiskerLeft G (SKM.SuperAdjunction.rightTranspose adj adj d) -
            Superfunctor.whiskerRight b F'))
    (a : End E) (ha : a ∈ parity (R := k) _ _ 0) (hu : IsUnit a) :
    IsUnit (SKM.mixedPostSourcePreDot (k := k) E κ H (F' := F') a -
      SKM.mixedPostSourcePostDot (k := k) E κ H adj d) := by
  let K : B ⟶ C := (SKM.homParityShift (k := k) (C := B ⟶ C) κ).obj H
  exact sourceNorm_ofProducer F' (SKM.SuperAdjunction.rightTranspose adj adj d)
    hNorm E K a ha hu

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ x : X) (i : I) {y : X} (h : x + D.α i = y)
  {A B : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (κ τ : ZMod 2)
  (H : B ⟶ elvWeightSpace D Sc cutoff bound Λ y)

/-- The literal even source norm uses the raw coefficient's Hom-shift witness. -/
theorem elvRawMixedSource_difference_isUnit [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 0)
    (a : End E) (ha : a ∈ parity (R := k) _ _ (D.parity i)) (hu : IsUnit a) :
    IsUnit (SKM.mixedPostSourcePreDot (k := k) E κ H
        (F' := elvF D Sc cutoff bound i Λ h) a -
      SKM.mixedPostSourcePostDot (k := k) E κ H
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h)) := by
  have hNorm : ∀ (G : Superfunctor k A.carrier (ELVWeightProduct D Sc cutoff bound Λ y))
      (b : End G), b ∈ parity (R := k) _ _ 0 → IsUnit b →
      IsUnit (show End (G.comp (elvF D Sc cutoff bound i Λ h)) from
        Superfunctor.whiskerLeft G (elvActionDotTranspose D Sc cutoff bound i Λ h) -
          Superfunctor.whiskerRight b (elvF D Sc cutoff bound i Λ h)) := by
    intro G b hb hu
    have hG := elvRestrictionProbe_difference_isUnit (A := A) D Sc cutoff bound i Λ h G
      sy hc hi b hb hu
    set_option backward.dsimp.instances true in
      dsimp only [elvPostTransposeDot, elvRestrictionProbeDot, elvPostRestriction] at hG
    exact hG
  exact mixedSourceNorm_ofTranspose E κ H
    (elvActionAdjunction D Sc cutoff bound i Λ h) (elvActionDot D Sc cutoff bound i Λ h)
    hNorm a (hi ▸ ha) hu

/-- The raw arbitrary-Z even coefficient has invertible prescribed dotted mate. -/
theorem elvRawMixedEvenMateDot_isIso [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 0)
    (a : End E) (ha : a ∈ parity (R := k) _ _ (D.parity i)) (hu : IsUnit a) :
    IsIso (SKM.homDistinctMixedInverseMateDot
      (C := PiSCat.{u, u, u + 1} k) (a := A) (b := B)
      (c := elvWeightSpace D Sc cutoff bound Λ x)
      (d := elvWeightSpace D Sc cutoff bound Λ y)
      E (elvActionAdjunction D Sc cutoff bound i Λ h) κ τ H
      (elvRawMixedCoefficient D Sc cutoff bound Λ x i h E τ
        ((SKM.homParityShift (k := k) κ).obj H ≫ elvF D Sc cutoff bound i Λ h)
        sy hc a ha hu)) := by
  have hs := elvRawMixedSource_difference_isUnit D Sc cutoff bound Λ x i h E κ H sy hc hi a ha hu
  have he := elvRawMixedCoefficient_even_identities D Sc cutoff bound Λ x i h E τ
    ((SKM.homParityShift (k := k) κ).obj H ≫ elvF D Sc cutoff bound i Λ h)
    sy hc hi a ha hu
  exact SKM.homDistinctMixedMateDot_isIso_of_inverse_units
    (B := PiSCat.{u, u, u + 1} k) (a := A) (b := B)
    (c := elvWeightSpace D Sc cutoff bound Λ x)
    (d := elvWeightSpace D Sc cutoff bound Λ y)
    E (elvActionAdjunction D Sc cutoff bound i Λ h) κ τ H (hi ▸ ha)
    (hi ▸ elvActionDot_mem D Sc cutoff bound i Λ h) _ he.1 he.2 hs

end OddMath.QuiverHecke.ELVOld
