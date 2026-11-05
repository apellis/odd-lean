import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVOperatorPowerComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations

/-! # The signed vacuum probe polynomial on the old coend

The scalar comparison is the prescribed append isomorphism, and its proved
dot square retains the given signed dot. This attaches the vacuum probe
annihilator of `SwappedVacuumBubbles.md`, (5), to the old module itself.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke
universe u v

private theorem iso_total_injective
    {k C : Type u} [CommRing k] [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (w : C) :
    Function.Injective (e.hom.total w) :=
  (moduleIsoLinearEquiv e w).injective

private theorem intertwine_probe_polynomial
    {k V W : Type u} [CommRing k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (C : V →ₗ[k] W) (hC : Function.Injective C)
    (x : Module.End k V) (y : Module.End k W) (h : C.comp x = y.comp C)
    (m : ℕ) (hy : (y ^ 2 + 1) ^ m = 0) : (x ^ 2 + 1) ^ m = 0 := by
  have h2 := intertwine_pow C x y h 2
  have hs : C.comp (x ^ 2 + 1) = (y ^ 2 + 1).comp C := by
    rw [LinearMap.comp_add, LinearMap.add_comp, h2]
    rfl
  have hm := intertwine_pow C (x ^ 2 + 1) (y ^ 2 + 1) hs m
  apply LinearMap.ext
  intro z
  apply hC
  have hh := LinearMap.congr_fun hm z
  simpa only [LinearMap.comp_apply, hy, LinearMap.zero_apply, map_zero] using hh

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) []) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc [] N)
include hN

/-- The given signed dot on the unchanged old vacuum coend has the plus-one
probe annihilator. Scalar evaluation and the chosen append comparison are proved inputs. -/
theorem probeOldVacuumInductionDot_odd (i : I) (hi : D.parity i = 1)
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) [i]) :
    (probeOldContentInductionDot D Sc m [] i N w ^ 2 + 1) ^ m i = 0 := by
  rcases w with ⟨⟨word⟩, hw⟩
  let w : ELVOld.OldContentCategory D Sc (probeCutoff D m) [i] := ⟨⟨word⟩, hw⟩
  let O := probeOrdinaryModuleSuperfunctor D Sc m [] N hN
  let U := probeOldOrdinaryFunctor D Sc m [i]
  let L := ELVOld.BalancedInduction.induced
    (ELVOld.oldContentAppend D Sc (probeCutoff D m) [] i) N
  let hL := probeOldInduced_evaluatesCoefficients D m Sc [] i N hN
  let S := probeOrdinaryModuleSuperfunctor D Sc m [i] L hL
  let T := ELVOld.BalancedInduction.induced (probeOrdinaryAppend D Sc m [] i) O
  let e : S ≅ T := probeAppendOrdinaryModuleIso D Sc m [] N hN i
  let C := probeAppendComparisonLinear D Sc m [] N hN i w
  let x := probeOldContentInductionDot D Sc m [] i N w
  let y := transformLinear (probeOrdinaryAppendDot_supernatural D Sc m [] i) O (U.obj w)
  have hC : Function.Injective C := by
    dsimp only [C, probeAppendComparisonLinear]
    have hh : Function.Injective (e.hom.total (U.obj w)) :=
      iso_total_injective (F := S) (G := T) e (U.obj w)
    dsimp only [e, S, T, L, O, U, w, probeOrdinaryModuleSuperfunctor,
      probeOrdinaryModuleFunctor, probeOrdinaryOldObject, probeOldOrdinaryFunctor] at hh ⊢
    exact hh
  have hd : C.comp x = y.comp C := probeAppendOrdinaryModuleIso_hom_dot D Sc m [] N hN i w
  exact intertwine_probe_polynomial C hC x y hd (m i)
    (probeOrdinaryVacuumInductionDot_odd D Sc m i hi O (U.obj w))

/-- The literal old vacuum probe satisfies its polynomial as an endomorphism
of the entire old induced supermodule, before scalar descent. -/
theorem probeOldVacuumModuleDot_odd (i : I) (hi : D.parity i = 1) :
    let x : End (ELVOld.BalancedInduction.induced
        (ELVOld.oldContentAppend D Sc (probeCutoff D m) [] i) N) :=
      ELVOld.BalancedInduction.transformComponent
        (probeOldContentAppendDot_supernatural D Sc m [] i) N
    (x ^ 2 + 1) ^ m i = 0 := by
  dsimp only
  apply ELVOld.BalancedInduction.end_eq_zero_of_total
  intro w
  let P := ELVOld.BalancedInduction.induced
    (ELVOld.oldContentAppend D Sc (probeCutoff D m) [] i) N
  let x : End P := ELVOld.BalancedInduction.transformComponent
    (probeOldContentAppendDot_supernatural D Sc m [] i) N
  have hx : x.total w = probeOldContentInductionDot D Sc m [] i N w := by
    dsimp only [probeOldContentInductionDot]
    simp only [x, SuperNatTrans.total, ELVOld.BalancedInduction.transformComponent_app,
      hi, zero_ne_one, ↓reduceIte, zero_add]
  change ((x ^ 2 + 1) ^ m i).total w = 0
  rw [ELVOld.BalancedInduction.end_total_pow]
  have hs : (x ^ 2 + 1).total w = (x ^ 2).total w + (1 : End P).total w := by
    change ((x ^ 2).app 0 w + (1 : End P).app 0 w) +
      ((x ^ 2).app 1 w + (1 : End P).app 1 w) =
      ((x ^ 2).app 0 w + (x ^ 2).app 1 w) +
        ((1 : End P).app 0 w + (1 : End P).app 1 w)
    abel
  have h1 : (1 : End P).total w = (1 : End (P.obj w)) := SuperNatTrans.id_total _ _
  rw [hs, ELVOld.BalancedInduction.end_total_pow, h1, hx]
  exact probeOldVacuumInductionDot_odd D Sc m N hN i hi w

end OddMath.QuiverHecke
