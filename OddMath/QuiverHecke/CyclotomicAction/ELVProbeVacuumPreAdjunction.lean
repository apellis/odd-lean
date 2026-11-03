import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumLocalCap
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeLocalPreAdjunction

/-! # The normalized precomposition adjunction at the probe vacuum

SwappedHomInversion §1: the constructed empty local record and its adjacent
upper record supply the existing finite-local left-adjunction constructor.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u

private theorem zeroLowerBraid {k : Type u} [CommRing k]
    {A B C R : PiSCat.{u,u,u+1} k} (Z : A ⟶ B) (E : B ⟶ C) (F : C ⟶ R)
    (t : End (E ≫ F)) :
    Z ◁ t ≫ ((associator Z E F).inv ≫ (0 : End (Z ≫ E)) ▷ F ≫ (associator Z E F).hom) ≫ Z ◁ t =
      ((associator Z E F).inv ≫ (0 : End (Z ≫ E)) ▷ F ≫ (associator Z E F).hom) ≫ Z ◁ t ≫
        ((associator Z E F).inv ≫ (0 : End (Z ≫ E)) ▷ F ≫ (associator Z E F).hom) := by
  simp only [TwoSupercategory.zero_whiskerRight (R := k), Limits.comp_zero, Limits.zero_comp]

private def locHeightTransport {k : Type u} [CommRing k]
    {A B C : PiSCat.{u,u,u+1} k}
    {E₀ : A ⟶ B} {F₀ : B ⟶ A} {E₁ : B ⟶ C} {F₁ : C ⟶ B}
    {A₀ : SKM.SuperAdjunction (k := k) E₀ F₀} {A₁ : SKM.SuperAdjunction (k := k) E₁ F₁}
    {x₀ : End E₀} {x₁ : End E₁} {t : End (E₀ ≫ E₁)} {p : ZMod 2} {h h' : ℤ}
    (L : SKM.SuperRouquierLoc A₀ A₁ x₀ x₁ t p h) (he : h = h') :
    SKM.SuperRouquierLoc A₀ A₁ x₀ x₁ t p h' := he ▸ L

private theorem upperVacuumHeight
    {I X : Type u} [AddCommGroup X]
    (D : SKM.Datum I X) (cutoff : I → ℕ) (i : I) :
    -contentCrossingHeight D cutoff i (([i] : List I) : Multiset I) = -(cutoff i : ℤ) + 2 := by
  simp only [contentCrossingHeight_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have hself : D.h i (D.α i) = 2 := D.cd.coroot_root_self i
  rw [hself]
  omega

end OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
