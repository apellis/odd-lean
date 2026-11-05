/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightDotTranspose
import OddMath.QuiverHecke.SwappedAssembly.ProductDenominatorUnits
import OddMath.SKM.RouquierHomPostPowers

/-! # Denominator inverses for the right-transposed ELV dot

The source-content exponent is uniform over input modules but may vary with
the source block. These bounds construct natural denominator inverses on
postrestriction. The postdot is literally the right transpose of the chosen
normalized full-ELV induction dot.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
universe u v w
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C] [Supercategory k C]
  (F : Superfunctor k C (ELVWeightProduct D Sc cutoff bound Λ y))

abbrev elvPostRestriction := F.comp (elvF D Sc cutoff bound i Λ h)
def elvPostTransposeDot : End (elvPostRestriction D Sc cutoff bound i Λ h F) :=
  Superfunctor.whiskerLeft F (elvActionDotTranspose D Sc cutoff bound i Λ h)

theorem elvPostTransposeDot_eq :
    elvPostTransposeDot D Sc cutoff bound i Λ h F =
      Superfunctor.whiskerLeft F (elvActionDotTranspose D Sc cutoff bound i Λ h) := rfl

/-- A typed endomorphism component of the postrestriction functor. -/
abbrev elvRestrictionEndComponent
    (g : End (elvPostRestriction D Sc cutoff bound i Λ h F)) (p : ZMod 2)
    (M : C) (δ : WeightBlocks D Λ x) :
    End (((elvPostRestriction D Sc cutoff bound i Λ h F).obj M) δ) := g.app p M δ

theorem elvPostTransposeDot_mem :
    elvPostTransposeDot D Sc cutoff bound i Λ h F ∈ parity (R := k) _ _ (D.parity i) :=
  Superfunctor.whiskerLeft_mem F (elvActionDotTranspose_mem D Sc cutoff bound i Λ h)

include sy hc in
theorem elvPostTransposeDot_component_isNilpotent [Finite I] (M : C) (δ : WeightBlocks D Λ x) :
    IsNilpotent (elvRestrictionEndComponent D Sc cutoff bound i Λ h F (elvPostTransposeDot D Sc cutoff bound i Λ h F) (D.parity i) M δ) := by
  obtain ⟨e, _, he⟩ := elvActionDotTranspose_component_pow_zero D Sc cutoff bound i Λ h sy hc δ
  exact ⟨e, he (F.obj M)⟩

include sy hc in
theorem elvPostTransposeDot_difference_isUnit [Finite I] (hi : D.parity i = 0)
    (X : End (elvPostRestriction D Sc cutoff bound i Λ h F))
    (hx : X ∈ parity (R := k) _ _ 0)
    (hu : IsUnit X)
    (hcomm : ∀ M δ, Commute
      (elvRestrictionEndComponent D Sc cutoff bound i Λ h F (elvPostTransposeDot D Sc cutoff bound i Λ h F) 0 M δ) (elvRestrictionEndComponent D Sc cutoff bound i Λ h F X 0 M δ)) :
    IsUnit (elvPostTransposeDot D Sc cutoff bound i Λ h F - X) := by
  apply superfunctorEnd_isUnit
  · exact Submodule.sub_mem _
      (hi ▸ elvPostTransposeDot_mem D Sc cutoff bound i Λ h F) hx
  · intro M
    change IsUnit (show End ((elvPostRestriction D Sc cutoff bound i Λ h F).obj M) from
      (elvPostTransposeDot D Sc cutoff bound i Λ h F).app 0 M - X.app 0 M)
    apply product_difference_isUnit
      (fun δ : WeightBlocks D Λ x => ContentModules D Sc cutoff bound δ.1)
    · exact fun δ => superfunctorProductEnd_component_isUnit _ _ X hu 0 hx M δ
    · intro δ
      simpa only [hi] using
        elvPostTransposeDot_component_isNilpotent D Sc cutoff bound sy hc i Λ h F M δ
    · exact hcomm M

section Probe
variable {A : PiSCat.{u, u, u + 1} k}
  (G : A ⟶ elvWeightSpace D Sc cutoff bound Λ y)

/-- The literal postcomposition image of the probe-precomposition dot. -/
def elvRestrictionProbeDot (α : End G) : End (elvPostRestriction D Sc cutoff bound i Λ h G) :=
  Superfunctor.whiskerRight α (elvF D Sc cutoff bound i Λ h)

theorem elvRestrictionProbeDot_isUnit (α : End G) (hu : IsUnit α) :
    IsUnit (elvRestrictionProbeDot D Sc cutoff bound i Λ h G α) :=
  hu.map ((SKM.homPost (k := k) (a := A) (elvF D Sc cutoff bound i Λ h)).mapEnd G)

theorem elvRestrictionProbeDot_mem {p : ZMod 2} (α : End G)
    (hα : α ∈ parity (R := k) _ _ p) :
    elvRestrictionProbeDot D Sc cutoff bound i Λ h G α ∈ parity (R := k) _ _ p :=
  Superfunctor.whiskerRight_mem hα (elvF D Sc cutoff bound i Λ h)

private theorem elvRestrictionProbe_even_comm (t : End (elvF D Sc cutoff bound i Λ h)) (α : End G) (M : A) (δ : WeightBlocks D Λ x) :
    Commute
      (elvRestrictionEndComponent D Sc cutoff bound i Λ h G
        (Superfunctor.whiskerLeft G t) 0 M δ)
      (elvRestrictionEndComponent D Sc cutoff bound i Λ h G
        (elvRestrictionProbeDot D Sc cutoff bound i Λ h G α) 0 M δ) := by
  change
    ((elvF D Sc cutoff bound i Λ h).map (α.app 0 M)) δ ≫
        t.app 0 (G.obj M) δ =
      t.app 0 (G.obj M) δ ≫
        ((elvF D Sc cutoff bound i Λ h).map (α.app 0 M)) δ
  have hh := t.naturality
    0 (α.app 0 M) (α.app_mem 0 M)
  simp only [koszulSign_zero_left, one_smul] at hh
  exact congrArg (fun f => f δ) hh

theorem elvRestrictionProbe_difference_isUnit [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 0)
    (α : End G) (hα : α ∈ parity (R := k) _ _ 0) (hu : IsUnit α) :
    IsUnit (elvPostTransposeDot D Sc cutoff bound i Λ h G -
      elvRestrictionProbeDot D Sc cutoff bound i Λ h G α) := by
  apply elvPostTransposeDot_difference_isUnit D Sc cutoff bound sy hc i Λ h G hi
    (elvRestrictionProbeDot D Sc cutoff bound i Λ h G α)
  · exact elvRestrictionProbeDot_mem D Sc cutoff bound i Λ h G α hα
  · exact elvRestrictionProbeDot_isUnit D Sc cutoff bound i Λ h G α hu
  · rw [elvPostTransposeDot_eq]
    generalize elvActionDotTranspose D Sc cutoff bound i Λ h = t
    intro M δ
    exact elvRestrictionProbe_even_comm D Sc cutoff bound i Λ h G
      t α M δ

end Probe
end OddMath.QuiverHecke.ELVOld

