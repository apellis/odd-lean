import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapPreDotSigns
import Mathlib.RingTheory.Nilpotent.Basic
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.CrossCoeff

/-! # The even probe polynomial on the shifted vacuum source

SwappedVacuumBubbles (5) and SwappedVacuumNonpositiveBubbles (8)–(9):
for an even moving colour the selected probe dot satisfies `(x-1)^m=0`.
The balanced induction, old/ordinary comparison and source parity chart
are retained. The datum may contain other odd colours.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u v

private theorem evenDefect_supernatural
    {k C B : Type u} [CommRing k] [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {J : C ⥤ B} [J.Additive] [J.Linear k] {a : ∀ v, End (J.obj v)} (ha : IsSupernatural k 0 a) :
    IsSupernatural k 0 (fun v => a v - 1) := by
  exact SwappedAssembly.IsSupernatural.sub ha (isSupernatural_id (R := k) (F := J))

private theorem transformLinear_even_polynomial
    {k C B : Type u} [CommRing k] [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {J : C ⥤ B} [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {a : ∀ v, End (J.obj v)} (ha : IsSupernatural k p a)
    (hp : p = 0) (n : ℕ) (hn : ∀ v, (a v - 1) ^ n = 0)
    (M : Superfunctor k C (SVec k)) (w : B) :
    (transformLinear ha M w - 1) ^ n = 0 := by
  subst p
  have h : transformLinear ha M w - 1 =
      transformLinear (evenDefect_supernatural ha) M w := by
    apply hom_ext
    intro v f z
    change transformLinear ha M w (tensor J M.toFunctor v f z) - tensor J M.toFunctor v f z = _
    rw [transformLinear_tensor, transformLinear_tensor]
    rw [twist_zero, Preadditive.sub_comp, End.one_def, Category.id_comp]
    simp only [tensor, TensorProduct.sub_tmul, map_sub]
  rw [h]
  exact transformLinear_pow_zero (evenDefect_supernatural ha) n hn M w

private theorem functor_even_polynomial
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] {V : A} (x : End V) (n : ℕ)
    (h : (x - 1) ^ n = 0) : (F.mapEnd V x - 1) ^ n = 0 := by
  let f : End V →+* End (F.obj V) :=
    { toFun := F.mapEnd V
      map_one' := (F.mapEnd V).map_one
      map_mul' := (F.mapEnd V).map_mul
      map_zero' := F.map_zero V V
      map_add' := fun _ _ => F.map_add }
  have hh := congrArg f h
  simp only [map_pow, map_sub, map_one, map_zero] at hh
  change (F.mapEnd V x - 1) ^ n = 0 at hh
  exact hh

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)

/-- The actual signed induction operator for an even colour has the
ordinary minus-one probe annihilator on every vector. -/
theorem probeOrdinaryVacuumInductionDot_even (i : I) (hi : D.parity i = 0)
    (M : Superfunctor k
      (OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) []) (SVec k))
    (w : OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) [i]) :
    (transformLinear (probeOrdinaryAppendDot_supernatural D Sc m [] i) M w - 1) ^ m i = 0 := by
  apply transformLinear_even_polynomial _ hi
  intro v
  have h := probeOrdinaryVacuumDot_polynomial D Sc m i v
  have he : probeDotExponent D i = 1 := by simp [probeDotExponent, hi]
  simpa only [he, pow_one] using h

private theorem iso_total_injective
    {k C : Type u} [CommRing k] [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (w : C) :
    Function.Injective (e.hom.total w) :=
  (moduleIsoLinearEquiv e w).injective

private theorem intertwine_even_polynomial
    {k V W : Type u} [CommRing k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (C : V →ₗ[k] W) (hC : Function.Injective C)
    (x : Module.End k V) (y : Module.End k W) (h : C.comp x = y.comp C)
    (m : ℕ) (hy : (y - 1) ^ m = 0) : (x - 1) ^ m = 0 := by
  have hs : C.comp (x - 1) = (y - 1).comp C := by
    rw [LinearMap.comp_sub, LinearMap.sub_comp, h]
    rfl
  have hm := intertwine_pow C (x - 1) (y - 1) hs m
  apply LinearMap.ext
  intro z
  apply hC
  have hh := LinearMap.congr_fun hm z
  simpa only [LinearMap.comp_apply, hy, LinearMap.zero_apply, map_zero] using hh

section Old
variable (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) []) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc [] N)
include hN

/-- The even annihilator survives the prescribed old/ordinary comparison
on every old vacuum induction vector. -/
theorem probeOldVacuumInductionDot_even (i : I) (hi : D.parity i = 0)
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) [i]) :
    (probeOldContentInductionDot D Sc m [] i N w - 1) ^ m i = 0 := by
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
  exact intertwine_even_polynomial C hC x y hd (m i)
    (probeOrdinaryVacuumInductionDot_even D Sc m i hi O (U.obj w))

/-- The literal old vacuum probe satisfies its polynomial as an endomorphism
of the entire old induced supermodule, before scalar descent. -/
theorem probeOldVacuumModuleDot_even (i : I) (hi : D.parity i = 0) :
    let x : End (ELVOld.BalancedInduction.induced
        (ELVOld.oldContentAppend D Sc (probeCutoff D m) [] i) N) :=
      ELVOld.BalancedInduction.transformComponent
        (probeOldContentAppendDot_supernatural D Sc m [] i) N
    (x - 1) ^ m i = 0 := by
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
      hi, one_ne_zero, ↓reduceIte, add_zero]
  change ((x - 1) ^ m i).total w = 0
  rw [ELVOld.BalancedInduction.end_total_pow]
  have hs : (x - 1).total w = x.total w - (1 : End P).total w := by
    change (x.app 0 w - (1 : End P).app 0 w) +
      (x.app 1 w - (1 : End P).app 1 w) =
      (x.app 0 w + x.app 1 w) - ((1 : End P).app 0 w + (1 : End P).app 1 w)
    abel
  have h1 : (1 : End P).total w = (1 : End (P.obj w)) := SuperNatTrans.id_total _ _
  rw [hs, h1, hx]
  exact probeOldVacuumInductionDot_even D Sc m N hN i hi w

end Old

namespace ELVOld.ProbeVacuumCap

/-- The actual restricted module dot retains the even probe annihilator. -/
theorem moduleDot_even_polynomial (i : I) (hi : D.parity i = 0) :
    (moduleDot D Sc m i - 1) ^ m i = 0 := by
  exact functor_even_polynomial (restriction (oldContentAppend D Sc (probeCutoff D m) [] i))
    (dotEnd (oldContentAppend D Sc (probeCutoff D m) [] i)
      (probeOldContentAppendDot_supernatural D Sc m [] i) (probeOldVacuumRegular D Sc m)) (m i)
    (probeOldVacuumModuleDot_even D Sc m (probeOldVacuumRegular D Sc m)
      (probeOldModule_evaluatesCoefficients D m Sc [] _) i hi)

/-- Evaluated precomposition preserves the same even annihilator. -/
theorem preDot_even_polynomial (R : PiSCat.{u,u,u+1} k) (i : I) (hi : D.parity i = 0)
    (H : modulePiCategory D Sc m ⟶ R) : (preDotEnd D Sc m R i H - 1) ^ m i = 0 := by
  rw [preDotEnd_eq]
  exact functor_even_polynomial H.toFunctor (moduleDot D Sc m i) (m i)
    (moduleDot_even_polynomial D Sc m i hi)

private theorem conjugate_even_polynomial {C : Type*} [Category C] [Preadditive C]
    {V W : C} (e : V ≅ W) (x : End W) (n : ℕ) (h : (x - 1) ^ n = 0) :
    (e.symm.conj x - 1) ^ n = 0 := by
  let c : End W →+* End V :=
    { toFun := e.symm.conj
      map_one' := map_one e.symm.conj
      map_mul' := fun a b => map_mul e.symm.conj a b
      map_zero' := by simp [Iso.conj_apply]
      map_add' := fun a b => by
        change e.hom ≫ (a + b) ≫ e.inv = _
        rw [Preadditive.add_comp, Preadditive.comp_add]
        rfl }
  have hc := congrArg c h
  simp only [map_pow, map_sub, map_one, map_zero] at hc
  exact hc

/-- The source chart retains the ordinary even probe polynomial. -/
theorem coordinatePreDot_even_polynomial (R : PiSCat.{u,u,u+1} k) (i : I) (hi : D.parity i = 0)
    (H : modulePiCategory D Sc m ⟶ R) :
    (coordinatePreDotPower D Sc m R i H 1 - 1) ^ m i = 0 := by
  simpa only [coordinatePreDotPower, pow_one, Iso.conj_apply, Iso.symm_inv, Iso.symm_hom] using
    conjugate_even_polynomial (preSourceComponent D Sc m R i H) (preDotEnd D Sc m R i H) (m i)
      (preDot_even_polynomial D Sc m R i hi H)

/-- An even moving dot has no source-parity sign, including in mixed data. -/
theorem shiftedPreDot_even_polynomial (R : PiSCat.{u,u,u+1} k) (i : I) (hi : D.parity i = 0)
    (H : modulePiCategory D Sc m ⟶ R) :
    (shiftedPreDot D Sc m R i H - 1) ^ m i = 0 := by
  rw [shiftedPreDot_coordinates, hi, koszulSign_zero_left, one_smul]
  exact coordinatePreDot_even_polynomial D Sc m R i hi H

/-- The even probe dot is a unit on its actual shifted regular-probe source. -/
theorem shiftedPreDot_even_isUnit (R : PiSCat.{u,u,u+1} k) (i : I) (hi : D.parity i = 0)
    (H : modulePiCategory D Sc m ⟶ R) : IsUnit (shiftedPreDot D Sc m R i H) := by
  have hn : IsNilpotent (shiftedPreDot D Sc m R i H - 1) :=
    ⟨m i, shiftedPreDot_even_polynomial D Sc m R i hi H⟩
  simpa only [sub_add_cancel] using hn.isUnit_add_one

end ELVOld.ProbeVacuumCap

end OddMath.QuiverHecke
