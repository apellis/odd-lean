import OddMath.QuiverHecke.CyclotomicAction.ELVProbeExtensionParity
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOldVacuumPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendRestrictionDot

/-! # Signed probe polynomial on the canonical full-old extension

The concrete probe annihilator required by `SwappedVacuumBubbles.md`, (5),
is retained by the prescribed content-extension append comparison. This
concerns only append from the regular empty probe and its one-letter block.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ProbeExtensionCoefficient
open BalancedInduction CyclotomicCrossingTensor
universe u

private theorem iso_total_surjective
    {k C : Type u} [CommRing k] [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (w : C) :
    Function.Surjective (e.hom.total w) :=
  (moduleIsoLinearEquiv e w).surjective

private theorem polynomial_of_surjective_intertwiner
    {k V W : Type u} [CommRing k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (R : V →ₗ[k] W)
    (x : Module.End k V) (y : Module.End k W) (hd : R.comp x = y.comp R)
    (hR : Function.Surjective R) (n : ℕ) (hx : (x ^ 2 + 1) ^ n = 0) :
    (y ^ 2 + 1) ^ n = 0 := by
  have h2 := intertwine_pow R x y hd 2
  have hs : R.comp (x ^ 2 + 1) = (y ^ 2 + 1).comp R := by
    rw [LinearMap.comp_add, LinearMap.add_comp, h2]
    rfl
  have hn := intertwine_pow R (x ^ 2 + 1) (y ^ 2 + 1) hs n
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := hR w
  have h := LinearMap.congr_fun hn v
  simpa only [LinearMap.comp_apply, hx, LinearMap.zero_apply, map_zero] using h.symm

private theorem induction_polynomial_of_surjective_intertwiner
    {k C A W : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [AddCommGroup W] [Module k W]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (w : A)
    (R : Obj J M.toFunctor w →ₗ[k] W) (y : Module.End k W)
    (hd : R.comp (transformLinear hα M w) = y.comp R)
    (hR : Function.Surjective R) (n : ℕ)
    (hx : ((transformLinear hα M w : Module.End k (Obj J M.toFunctor w)) ^ 2 + 1) ^ n = 0) :
    (y ^ 2 + 1) ^ n = 0 :=
  polynomial_of_surjective_intertwiner R _ y hd hR n hx

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

private theorem contentComparison_surjective (cutoff : I → ℕ) (ν : List I) (i : I)
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (w : OldContentCategory D Sc cutoff (i :: ν)) :
    Function.Surjective (oldContentAppendRestrictionLinear D Sc cutoff ν i N w) := by
  have h := iso_total_surjective (oldContentAppendRestrictionIso D Sc cutoff ν i N) w
  exact h

variable [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "M" => probeOldVacuumRegular D Sc m
local notation "J" => oldContentInclusion D Sc cut []
local notation "L" => induced J M

/-- The original signed full-old induction dot on the canonical regular
probe extension has the plus-one probe annihilator on its one-letter block.
No all-content last-dot exponent is asserted. -/
theorem extensionDot_odd (i : I) (hi : D.parity i = 1)
    (w : OldContentCategory D Sc cut [i]) :
    ((actualInductionDot D Sc cut i L w.obj :
        Module.End k (Obj (append D Sc cut i) (L).toFunctor w.obj)) ^ 2 + 1) ^ m i = 0 := by
  have hd := oldContentAppendRestrictionIso_dot D Sc cut [] i M w
  have hx := probeOldVacuumInductionDot_odd D Sc m M
    (probeOldModule_evaluatesCoefficients D m Sc [] _) i hi w
  have h := induction_polynomial_of_surjective_intertwiner (oldContentAppend D Sc cut [] i)
    (oldContentAppendDot_supernatural D Sc cut [] i) M w _ _ hd
    (contentComparison_surjective D Sc cut [] i M w) (m i) hx
  exact h

end OddMath.QuiverHecke.ELVOld.ProbeExtensionCoefficient
