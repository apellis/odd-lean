import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightCap
import Mathlib.RingTheory.Nilpotent.Basic
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.CrossCoeff
import OddMath.SKM.RouquierHomPreNegativePowers
import OddMath.QuiverHecke.CyclotomicAction.ReservoirLayers

/-!
# Probe vacuum bends

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The even probe polynomial on the shifted vacuum source

SwappedVacuumBubbles (5) and SwappedVacuumNonpositiveBubbles (8)–(9):
for an even moving colour the selected probe dot satisfies `(x-1)^m=0`.
The balanced induction, old/ordinary comparison and source parity chart
are retained. The datum may contain other odd colours.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
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
variable (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) []) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc [] N)
include hN

/-- The even annihilator survives the prescribed old/ordinary comparison
on every old vacuum induction vector. -/
theorem probeOldVacuumInductionDot_even (i : I) (hi : D.parity i = 0)
    (w : ELV.OldContentCategory D Sc (probeCutoff D m) [i]) :
    (probeOldContentInductionDot D Sc m [] i N w - 1) ^ m i = 0 := by
  rcases w with ⟨⟨word⟩, hw⟩
  let w : ELV.OldContentCategory D Sc (probeCutoff D m) [i] := ⟨⟨word⟩, hw⟩
  let O := probeOrdinaryModuleSuperfunctor D Sc m [] N hN
  let U := probeOldOrdinaryFunctor D Sc m [i]
  let L := ELV.BalancedInduction.induced
    (ELV.oldContentAppend D Sc (probeCutoff D m) [] i) N
  let hL := probeOldInduced_evaluatesCoefficients D m Sc [] i N hN
  let S := probeOrdinaryModuleSuperfunctor D Sc m [i] L hL
  let T := ELV.BalancedInduction.induced (probeOrdinaryAppend D Sc m [] i) O
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
    let x : End (ELV.BalancedInduction.induced
        (ELV.oldContentAppend D Sc (probeCutoff D m) [] i) N) :=
      ELV.BalancedInduction.transformComponent
        (probeOldContentAppendDot_supernatural D Sc m [] i) N
    (x - 1) ^ m i = 0 := by
  dsimp only
  apply ELV.BalancedInduction.end_eq_zero_of_total
  intro w
  let P := ELV.BalancedInduction.induced
    (ELV.oldContentAppend D Sc (probeCutoff D m) [] i) N
  let x : End P := ELV.BalancedInduction.transformComponent
    (probeOldContentAppendDot_supernatural D Sc m [] i) N
  have hx : x.total w = probeOldContentInductionDot D Sc m [] i N w := by
    dsimp only [probeOldContentInductionDot]
    simp only [x, SuperNatTrans.total, ELV.BalancedInduction.transformComponent_app,
      hi, one_ne_zero, ↓reduceIte, add_zero]
  change ((x - 1) ^ m i).total w = 0
  rw [ELV.BalancedInduction.end_total_pow]
  have hs : (x - 1).total w = x.total w - (1 : End P).total w := by
    change (x.app 0 w - (1 : End P).app 0 w) +
      (x.app 1 w - (1 : End P).app 1 w) =
      (x.app 0 w + x.app 1 w) - ((1 : End P).app 0 w + (1 : End P).app 1 w)
    abel
  have h1 : (1 : End P).total w = (1 : End (P.obj w)) := SuperNatTrans.id_total _ _
  rw [hs, h1, hx]
  exact probeOldVacuumInductionDot_even D Sc m N hN i hi w

end Old

namespace ELV.ProbeVacuumCap

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

end ELV.ProbeVacuumCap

end OddMath.QuiverHecke
end

end

section

/-! # The actual negative pre-cap at the regular probe

SwappedActionAssembly F2 and SwappedHomInversion §3 (4): evaluate the
chosen raw pre-dot inverse powers before the chosen normalized counit.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open CyclotomicAction
universe u
local instance negativeCapHomPi {k : Type u} [CommRing k] (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

private def totalEvaluation {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A] (N : C) :
    Superfunctor k C A ⥤ A where
  obj F := F.obj N
  map f := f.total N
  map_id F := SuperNatTrans.id_total F.toFunctor N
  map_comp f g := Superfunctor.comp_total f g N

private theorem total_pow {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F : Superfunctor k C A} (f : End F) (n : ℕ) (N : C) :
    (f ^ n).total N = ((totalEvaluation N).mapEnd F f) ^ n :=
  map_pow ((totalEvaluation N).mapEnd F) f n

private theorem inverse_power_square {C : Type*} [Category C] [Preadditive C]
    {A B : C} (a : A ≅ A) (e : A ≅ B) (xi : End A) (hxi : xi = a.inv)
    (y : End B) (hy : IsUnit y) (h : a.hom ≫ e.hom = e.hom ≫ y) (n : ℕ) :
    (xi ^ n) ≫ e.hom = e.hom ≫ Ring.inverse y ^ n := by
  have hi : xi ≫ e.hom = e.hom ≫ Ring.inverse (M₀ := End B) y := by
    obtain ⟨v, rfl⟩ := hy
    let b : B ≅ B := {
      hom := (v : End B)
      inv := ((v⁻¹ : (End B)ˣ) : End B)
      hom_inv_id := v.inv_val
      inv_hom_id := v.val_inv }
    have hh := congrArg (fun f => a.inv ≫ f ≫ b.inv) h
    rw [hxi, Ring.inverse_unit]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc,
      show (v : End B) = b.hom from rfl, Iso.hom_inv_id, Category.comp_id] using hh.symm
  induction n with
  | zero => simp only [pow_zero, End.one_def, Category.id_comp, Category.comp_id]
  | succ n ih =>
    rw [pow_succ', pow_succ', End.mul_def, End.mul_def, Category.assoc,
      hi, ← Category.assoc, ih, Category.assoc]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ) (Λ : X)
  (hc : ∀ i, (probeCutoff D m i : ℤ) = D.h i Λ)
  (W : X → PiSCat.{u,u,u+1} k) (muM : X) (i : I) {muP : X}
  (h : -Λ + D.α i = -muP) (H : ProbeVacuumCap.modulePiCategory D Sc m ⟶ W muM)
local notation "T" => probeOldRouquierFamily D Sc m Λ hc
local notation "N₀" => regularProbe D Sc m Λ
local notation "Z" => preCapInput D Sc m Λ hc W muM H
local instance rawProbeDotIso [Fact Sc.PureNilpotent] : IsIso ((T).dot i h) :=
  (isUnit_iff_isIso _).mp (probeOldRouquierFamily_dot_isUnit D Sc m Λ hc i h)

private def rawPreDotAut [Fact Sc.PureNilpotent] :
    Aut ((SKM.homContentPreE T W i muM h).obj ((SKM.homContentPreF T W i muM h).obj Z)) where
  hom := SKM.homReservoirDot T W i muM h ((SKM.homContentPreF T W i muM h).obj Z)
  inv := SKM.homPreDotInverse T W i muM h ((SKM.homContentPreF T W i muM h).obj Z)
  hom_inv_id := SKM.homPreDot_dotInverse T W i muM h _
  inv_hom_id := SKM.homPreDotInverse_dot T W i muM h _

private theorem shiftedDot_isUnit (hi : D.parity i = 1) :
    IsUnit (ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H) := by
  let x := ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H
  have hn : IsNilpotent (x ^ 2 + 1) :=
    ⟨m i, ProbeVacuumCap.shiftedPreDot_odd_polynomial D Sc m (W muM) i hi H⟩
  have hu : IsUnit (x ^ 2) := by simpa only [add_sub_cancel_right] using hn.isUnit_sub_one
  exact (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp hu

/-- All inverse powers are those of the actual whole-weight raw dot.
The target is the Ring inverse of the native shifted raw pre-dot. -/
theorem vacuumPreInverseDot_source [Fact Sc.PureNilpotent] (hP : 0 < probeCutoff D m i)
    (hi : D.parity i = 1) (n : ℕ) :
    ((SKM.homPreDotInverse T W i muM h ((SKM.homContentPreF T W i muM h).obj Z)) ^ n).total N₀ ≫
      (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom =
    (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom ≫
      Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H) ^ n := by
  let a := (totalEvaluation N₀).mapIso (rawPreDotAut D Sc m Λ hc W muM i h H)
  let xi := (totalEvaluation N₀).mapEnd _
    (SKM.homPreDotInverse T W i muM h ((SKM.homContentPreF T W i muM h).obj Z))
  have hh := inverse_power_square a (vacuumPreSourceIso D Sc m Λ hc W muM i h H)
    xi rfl (ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H)
    (shiftedDot_isUnit D Sc m W muM i H hi)
    (vacuumPreDot_source D Sc m Λ hc W muM i h H hP) n
  rw [total_pow]
  exact hh

/-- Every actual normalized negative pre-cap has the native inverse-dot
and cap coordinates. No moment or cap compatibility hypothesis is used. -/
theorem vacuumPreNegativeCap_eq [Fact Sc.PureNilpotent] (hP : 0 < probeCutoff D m i)
    (hi : D.parity i = 1) (n : ℕ) :
    (SKM.homPreNegativeCap T W i muM h n Z).total N₀ ≫
      H.map (eqToHom (emptyProbe_regular D Sc m Λ)) =
    (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom ≫
      (Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H) ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D Sc m (W muM) i hP H := by
  rw [SKM.homPreNegativeCap, Superfunctor.comp_total, Category.assoc,
    vacuumPreCounit_eq D Sc m Λ hc W muM i h H hP,
    ← Category.assoc, vacuumPreInverseDot_source D Sc m Λ hc W muM i h H hP hi n,
    Category.assoc]

/-- Even colour: all inverse powers are those of the actual whole-weight raw dot. -/
theorem vacuumPreInverseDot_source_even [Fact Sc.PureNilpotent] (hP : 0 < probeCutoff D m i)
    (hi : D.parity i = 0) (n : ℕ) :
    ((SKM.homPreDotInverse T W i muM h ((SKM.homContentPreF T W i muM h).obj Z)) ^ n).total N₀ ≫
      (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom =
    (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom ≫
      Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H) ^ n := by
  let a := (totalEvaluation N₀).mapIso (rawPreDotAut D Sc m Λ hc W muM i h H)
  let xi := (totalEvaluation N₀).mapEnd _
    (SKM.homPreDotInverse T W i muM h ((SKM.homContentPreF T W i muM h).obj Z))
  have hh := inverse_power_square a (vacuumPreSourceIso D Sc m Λ hc W muM i h H)
    xi rfl (ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H)
    (ProbeVacuumCap.shiftedPreDot_even_isUnit D Sc m (W muM) i hi H)
    (vacuumPreDot_source D Sc m Λ hc W muM i h H hP) n
  rw [total_pow]
  exact hh

/-- Even colour: every actual normalized negative pre-cap has the native
inverse-dot and cap coordinates. No moment or cap compatibility hypothesis is used. -/
theorem vacuumPreNegativeCap_even [Fact Sc.PureNilpotent] (hP : 0 < probeCutoff D m i)
    (hi : D.parity i = 0) (n : ℕ) :
    (SKM.homPreNegativeCap T W i muM h n Z).total N₀ ≫
      H.map (eqToHom (emptyProbe_regular D Sc m Λ)) =
    (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom ≫
      (Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H) ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D Sc m (W muM) i hP H := by
  rw [SKM.homPreNegativeCap, Superfunctor.comp_total, Category.assoc,
    vacuumPreCounit_eq D Sc m Λ hc W muM i h H hP,
    ← Category.assoc, vacuumPreInverseDot_source_even D Sc m Λ hc W muM i h H hP hi n,
    Category.assoc]

end OddMath.QuiverHecke.ELV.WeightTensorVacuum
end

end

section

/-! # Vacuum coordinates of the ordered mixed-bend monomials

SwappedHomInversion §3 (4)–(5): compare the prescribed negative pre-cap
and dotted post-unit before summing the finite padded Dx expansion.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
set_option autoImplicit false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open BalancedInduction CyclotomicAction
universe u
local instance bendMonomialHomPi {k : Type u} [CommRing k] (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

private def totalEvaluation_2 {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A] (N : C) :
    Superfunctor k C A ⥤ A where
  obj F := F.obj N
  map f := f.total N
  map_id F := SuperNatTrans.id_total F.toFunctor N
  map_comp f g := Superfunctor.comp_total f g N

private theorem unitColumn_even
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)
    (hf : f ∈ parity (R := k) M N 0) (r : ℕ) :
    unitDotColumn J hα M r ≫ (restriction J).map ((induction J).map f) =
      f ≫ unitDotColumn J hα N r := by
  have hd (n : ℕ) : IsSupernatural k (n • p) (F := induction J) (G := induction J)
      (fun P => dotEnd J hα P ^ n) := by
    induction n with
    | zero => simpa only [zero_nsmul, pow_zero, End.one_def] using
        (isSupernatural_id (R := k) (F := induction J))
    | succ n ih =>
      simpa only [pow_succ, End.mul_def, succ_nsmul, add_comm, dotEnd] using
        (transformComponent_supernatural hα).comp ih
  have hu := isSupernatural_of_natTrans (R := k) (adjunctionUnit J) (adjunctionUnit_mem J)
  have hs : IsSupernatural k (r • p) (F := 𝟭 (Superfunctor k C (SVec k)))
      (G := induction J ⋙ restriction J) (fun P => unitDotColumn J hα P r) := by
    simpa only [zero_add, unitDotColumn, adjunction] using
      hu.comp ((hd r).whiskerRight (restriction J))
  have h := hs.naturality hf
  simp only [mul_zero, sign_zero, one_smul] at h
  convert h.symm using 1 <;> rfl

private def shiftedPreRow {k : Type u} [CommRing k]
    {A B R : PiSCat.{u,u,u+1} k} (E : A ⟶ B) (F : B ⟶ A) (Z : A ⟶ R)
    (σ : ZMod 2) (z : ℤ) (f : E ⟶ E) (g : E ≫ F ⟶ 𝟙 A) :
    (SKM.homPre (k := k) E).obj ((SKM.homParityShift (k := k) (C := B ⟶ R) σ).obj (F ≫ Z)) ⟶ Z :=
  z • (E ◁ ((SKM.homParityShiftDatum (k := k) σ).iso (F ≫ Z)).hom ≫
    f ▷ (F ≫ Z) ≫ g ▷ Z)

private theorem negativeCap_row
    {I X k : Type u} [AddCommGroup X] [CommRing k] {D : SKM.Datum I X}
    (T : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    (W : X → PiSCat.{u,u,u+1} k) (i : I) (x : X) {a b : X}
    (edge : -a + D.α i = -b) [IsIso (T.dot i edge)] (n : ℕ)
    (Z : T.obj (-a) ⟶ W x) :
    SKM.homPreNegativeCap T W i x edge n Z =
      shiftedPreRow (R := W x) (T.E i edge) (T.F i edge) Z
        (SKM.leftAdjParity D i (-a))
        (koszulSign (SKM.leftAdjParity D i (-a)) (1 + (n : ZMod 2) * D.parity i))
        (SKM.rouquierPower (inv (T.dot i edge)) n)
        (((((T.leftAdjScalar i (-a))⁻¹ : kˣ) : k)) • T.leftCap i edge) := by
  rw [SKM.homPreNegativeCap_coordinates]
  unfold shiftedPreRow
  erw [PiSCat.associator_inv, PiSCat.leftUnitor_hom, Category.comp_id, Category.id_comp]

private theorem shiftedPreRow_block
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
    (Λ x : X) (δ : WeightBlocks D Λ x)
    {A B : PiSCat.{u,u,u+1} k} (E : A ⟶ B) (F : B ⟶ A)
    (Z : A ⟶ elvWeightSpace D Sc cutoff bound Λ x) (N : A)
    (σ : ZMod 2) (z : ℤ) (f : E ⟶ E) (g : E ≫ F ⟶ 𝟙 A)
    (hSrc : (((SKM.homPre (k := k) E).obj
        ((SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ x) σ).obj
          (F ≫ Z))).obj N) δ =
      ((SKM.homPre (k := k) E).obj
        ((SKM.homParityShift (k := k) (C := B ⟶ contentModuleTarget D Sc cutoff bound δ.1) σ).obj
          (F ≫ Z.comp (elvBlockEval D Sc cutoff bound Λ δ)))).obj N) :
    ((shiftedPreRow (R := elvWeightSpace D Sc cutoff bound Λ x) E F Z σ z f g).total N) δ =
      eqToHom hSrc ≫ (shiftedPreRow (R := contentModuleTarget D Sc cutoff bound δ.1) E F
        (Z.comp (elvBlockEval D Sc cutoff bound Λ δ)) σ z f g).total N := by
  fin_cases σ
  all_goals
    have hh : hSrc = rfl := Subsingleton.elim _ _
    rw [hh]
    simp only [eqToHom_refl, Category.id_comp]
    rfl

private theorem negativeCap_product
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
    (Λ x : X) (δ : WeightBlocks D Λ x)
    (T : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    (i : I) {a b : X} (edge : -a + D.α i = -b) [IsIso (T.dot i edge)]
    (Z : T.obj (-a) ⟶ elvWeightSpace D Sc cutoff bound Λ x) (N : T.obj (-a))
    (hSrc : (((SKM.homContentPreE T (elvWeightSpace D Sc cutoff bound Λ) i x edge).obj
        ((SKM.homContentPreF T (elvWeightSpace D Sc cutoff bound Λ) i x edge).obj Z)).obj N) δ =
      ((SKM.homContentPreE T (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge).obj
        ((SKM.homContentPreF T (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge).obj
          (Z.comp (elvBlockEval D Sc cutoff bound Λ δ)))).obj N)
    (n : ℕ) :
    (SKM.homPreNegativeCap T (elvWeightSpace D Sc cutoff bound Λ) i x edge n Z).total N δ =
      eqToHom hSrc ≫ (SKM.homPreNegativeCap T
        (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge n
        (Z.comp (elvBlockEval D Sc cutoff bound Λ δ))).total N := by
  rw [negativeCap_row, negativeCap_row]
  exact shiftedPreRow_block D Sc cutoff bound Λ x δ (T.E i edge) (T.F i edge) Z N
    (SKM.leftAdjParity D i (-a))
    (koszulSign (SKM.leftAdjParity D i (-a)) (1 + (n : ZMod 2) * D.parity i))
    (SKM.rouquierPower (inv (T.dot i edge)) n)
    (((((T.leftAdjScalar i (-a))⁻¹ : kˣ) : k)) • T.leftCap i edge) hSrc

private theorem negativeCap_product_input
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
    (Λ x : X) (δ : WeightBlocks D Λ x)
    (T : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    (i : I) {a b : X} (edge : -a + D.α i = -b) [IsIso (T.dot i edge)]
    (Z : T.obj (-a) ⟶ elvWeightSpace D Sc cutoff bound Λ x) (N : T.obj (-a))
    (V : T.obj (-a) ⟶ contentModuleTarget D Sc cutoff bound δ.1)
    (hz : Z.comp (elvBlockEval D Sc cutoff bound Λ δ) = V)
    (hSrc : (((SKM.homContentPreE T (elvWeightSpace D Sc cutoff bound Λ) i x edge).obj
        ((SKM.homContentPreF T (elvWeightSpace D Sc cutoff bound Λ) i x edge).obj Z)).obj N) δ =
      ((SKM.homContentPreE T (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge).obj
        ((SKM.homContentPreF T (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge).obj V)).obj N)
    (n : ℕ) :
    (SKM.homPreNegativeCap T (elvWeightSpace D Sc cutoff bound Λ) i x edge n Z).total N δ =
      eqToHom hSrc ≫ (SKM.homPreNegativeCap T
        (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge n V).total N ≫
        eqToHom (congrArg (fun U : T.obj (-a) ⟶ contentModuleTarget D Sc cutoff bound δ.1 => U.obj N) hz.symm) := by
  subst V
  simpa only [eqToHom_refl, Category.comp_id] using
    negativeCap_product D Sc cutoff bound Λ x δ T i edge Z N hSrc n

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (i : I) {muP nuR : X} (edgeP : -ΛP + D.α i = -muP)
  (edgeR : -ΛR + D.α i = nuR) (β : I →₀ ℕ)
variable (H : ProbeVacuumCap.modulePiCategory D Sc m ⟶ elvWeightSpace D Sc cutoff bound ΛR (-ΛR))

/-- The output block functor retains the entire probe module. -/
def vacuumBendBlock : ProbeVacuumCap.modulePiCategory D Sc m ⟶ (contentModuleTarget D Sc cutoff bound (0 : Multiset I)) :=
  H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR))
/-- The selected module in the prescribed shifted post-pair. -/
def vacuumPostPairModule : ContentModules D Sc cutoff bound (0 : Multiset I) :=
  (((SKM.homContentPostF (probeOldWeightSpace D Sc m ΛP) (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR).obj
    ((SKM.homContentPostE (probeOldWeightSpace D Sc m ΛP) (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR).obj (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H))).obj (regularProbe D Sc m ΛP)) (emptyBlock D ΛR)

/-- The canonical append/restrict target on the native regular probe. -/
def vacuumPostRegularModule : ContentModules D Sc cutoff bound (0 : Multiset I) :=
  (restriction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).obj ((induction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).obj (((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).obj (probeOldVacuumRegular D Sc m)))

/-- The prescribed post-target comparison, stored successor-content
chart, and regular-input comparison, in chronological order. -/
def vacuumPostTarget :
    vacuumPostPairModule D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H ≅
      vacuumPostRegularModule D Sc m cutoff bound ΛR i H := by
  let e₁ := (totalEvaluation_2 (regularProbe D Sc m ΛP) ⋙ Pi.eval
    (fun γ : WeightBlocks D ΛR (-ΛR) => ContentModules D Sc cutoff bound γ.1) (emptyBlock D ΛR)).mapIso
      (SKM.homContentPostTargetIso ((probeOldRouquierFamily D Sc m ΛP hcP)).obj (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H))
  let e₂ := eqToIso (elvWeightFollowing_obj D Sc cutoff bound i ΛR edgeR (emptyBlock D ΛR) (((preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).obj (regularProbe D Sc m ΛP)))
  let e₃ := eqToIso (storedAppendUpper_obj D Sc cutoff bound (emptyBlock D ΛR).1 i
    (blockSucc D ΛR i edgeR (emptyBlock D ΛR)).1 (elvBlockSucc_content_eq D i ΛR edgeR (emptyBlock D ΛR)) ((((preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).obj (regularProbe D Sc m ΛP)) (emptyBlock D ΛR)))
  let e₄ := (induction (contentAppend D Sc cutoff bound (0 : Multiset I) [i]) ⋙ restriction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).mapIso
    (((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).toFunctor.mapIso (eqToIso (emptyProbe_regular D Sc m ΛP)))
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

/-- At the empty reservoir block, the actual shifted post-cup becomes
the raw native unit/dot column, with the regular-input cast retained. -/
theorem vacuumBendPostCup_eq (r : ℕ) :
    ((SKM.homContentPostCup ((probeOldRouquierFamily D Sc m ΛP hcP)).obj (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR r (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR) ≫
      (vacuumPostTarget D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H).hom =
    ((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).map (eqToHom (emptyProbe_regular D Sc m ΛP)) ≫
      unitDotColumn (contentAppend D Sc cutoff bound (0 : Multiset I) [i]) (canonicalAppendDot_supernatural D Sc cutoff bound (0 : Multiset I) i) (((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).obj (probeOldVacuumRegular D Sc m)) r := by
  have hp := reservoirPostCup_canonical D Sc cutoff bound ΛR hcR ((probeOldRouquierFamily D Sc m ΛP hcP)).obj i β ΛP edgeR r (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H) (regularProbe D Sc m ΛP) (emptyBlock D ΛR)
  have hn := unitColumn_even (contentAppend D Sc cutoff bound (0 : Multiset I) [i]) (canonicalAppendDot_supernatural D Sc cutoff bound (0 : Multiset I) i) (((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).map (eqToHom (emptyProbe_regular D Sc m ΛP)))
    (Supercategory.map_mem (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR))).toFunctor (eqToHom_mem_parity_zero (k := k) (emptyProbe_regular D Sc m ΛP))) r
  rw [unitDotColumn_eq_restrictedDotEnd] at hn
  have ht := congrArg (fun f => f ≫
    (restriction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).map ((induction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).map
      (((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).map (eqToHom (emptyProbe_regular D Sc m ΛP))))) hp
  change _ = _ at ht
  simpa only [vacuumPostTarget, Iso.trans_hom, Functor.mapIso_hom,
    eqToIso.hom, Functor.comp_map, totalEvaluation_2, Pi.eval, Category.assoc] using ht.trans hn

/-- Selecting the output block commutes with each branch of the prescribed
precomposition parity shift. -/
private theorem preSourceBlock_eq :
    (((SKM.homContentPreE (probeOldRouquierFamily D Sc m ΛP hcP)
        (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP).obj
      ((SKM.homContentPreF (probeOldRouquierFamily D Sc m ΛP hcP)
        (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP).obj
        (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H))).obj
      (regularProbe D Sc m ΛP)) (emptyBlock D ΛR) =
    ((SKM.homContentPreE (probeOldRouquierFamily D Sc m ΛP hcP)
        (fun _ => contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i (-ΛR) edgeP).obj
      ((SKM.homContentPreF (probeOldRouquierFamily D Sc m ΛP hcP)
        (fun _ => contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i (-ΛR) edgeP).obj
        (preCapInput D Sc m ΛP hcP (fun _ => contentModuleTarget D Sc cutoff bound (0 : Multiset I))
          (-ΛR) (vacuumBendBlock D Sc m cutoff bound ΛR H)))).obj (regularProbe D Sc m ΛP) := by
  simp only [SKM.homContentPreF, Functor.comp_obj, SKM.homParityShift]
  split_ifs <;> rfl

/-- The source chart retains the output-block comparison before the
normalized vacuum pre-cap source chart. -/
def vacuumPreBlockSourceIso [Fact Sc.PureNilpotent] :=
  eqToIso (preSourceBlock_eq D Sc m cutoff bound ΛP ΛR hcP i edgeP H) ≪≫
    vacuumPreSourceIso D Sc m ΛP hcP
      (fun _ => contentModuleTarget D Sc cutoff bound (0 : Multiset I)) (-ΛR) i edgeP
      (vacuumBendBlock D Sc m cutoff bound ΛR H)

local instance bendMonomialProbeDotIso [Fact Sc.PureNilpotent] : IsIso (((probeOldRouquierFamily D Sc m ΛP hcP)).dot i edgeP) :=
  (isUnit_iff_isIso _).mp (probeOldRouquierFamily_dot_isUnit D Sc m ΛP hcP i edgeP)

private theorem negativeCap_block [Fact Sc.PureNilpotent] (n : ℕ) :
    ((SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP)
      (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP n
      (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total
      (regularProbe D Sc m ΛP)) (emptyBlock D ΛR) =
    eqToHom (preSourceBlock_eq D Sc m cutoff bound ΛP ΛR hcP i edgeP H) ≫
      (SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP)
        (fun _ => contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i (-ΛR) edgeP n
        (preCapInput D Sc m ΛP hcP (fun _ => contentModuleTarget D Sc cutoff bound (0 : Multiset I))
          (-ΛR) (vacuumBendBlock D Sc m cutoff bound ΛR H))).total (regularProbe D Sc m ΛP) := by
  have hz : (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H).comp
      (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)) =
    preCapInput D Sc m ΛP hcP (fun _ => contentModuleTarget D Sc cutoff bound (0 : Multiset I))
      (-ΛR) (vacuumBendBlock D Sc m cutoff bound ΛR H) := rfl
  have h := negativeCap_product_input D Sc cutoff bound ΛR (-ΛR) (emptyBlock D ΛR)
    (probeOldRouquierFamily D Sc m ΛP hcP) i edgeP
    (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)
    (regularProbe D Sc m ΛP)
    (preCapInput D Sc m ΛP hcP (fun _ => contentModuleTarget D Sc cutoff bound (0 : Multiset I))
      (-ΛR) (vacuumBendBlock D Sc m cutoff bound ΛR H)) hz
    (preSourceBlock_eq D Sc m cutoff bound ΛP ΛR hcP i edgeP H) n
  have ht : congrArg (fun U : (probeOldRouquierFamily D Sc m ΛP hcP).obj (-ΛP) ⟶
      contentModuleTarget D Sc cutoff bound (0 : Multiset I) => U.obj (regularProbe D Sc m ΛP)) hz.symm = rfl :=
    Subsingleton.elim _ _
  rw [ht, eqToHom_refl, Category.comp_id] at h
  exact h

/-- Each prescribed negative pre-cap followed by a dotted post-unit is
the corresponding raw vacuum bend monomial, with no compatibility premise. -/
theorem vacuumBendMonomial_eq [Fact Sc.PureNilpotent] (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1)
    (n r : ℕ) :
    ((SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP) (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP n (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H) ≫
      SKM.homContentPostCup ((probeOldRouquierFamily D Sc m ΛP hcP)).obj (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR r (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR) ≫
      (vacuumPostTarget D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H).hom =
    (vacuumPreBlockSourceIso D Sc m cutoff bound ΛP ΛR hcP i edgeP H).hom ≫
      (Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc m (contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))) ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D Sc m (contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i hP (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR))) ≫
          (adjunction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).unit.app (((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).obj (probeOldVacuumRegular D Sc m)) ≫
            restrictedDotEnd (contentAppend D Sc cutoff bound (0 : Multiset I) [i]) (canonicalAppendDot_supernatural D Sc cutoff bound (0 : Multiset I) i) (((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).obj (probeOldVacuumRegular D Sc m)) ^ r := by
  have hp := vacuumBendPostCup_eq D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H r
  have hn := vacuumPreNegativeCap_eq D Sc m ΛP hcP (fun _ => (contentModuleTarget D Sc cutoff bound (0 : Multiset I))) (-ΛR) i edgeP (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR))) hP hi n
  have hc : ((SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP) (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP n (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR) ≫
      ((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).map (eqToHom (emptyProbe_regular D Sc m ΛP)) =
      (vacuumPreBlockSourceIso D Sc m cutoff bound ΛP ΛR hcP i edgeP H).hom ≫
        (Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc m (contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))) ^ n) ≫
          ProbeVacuumCap.shiftedPreCap D Sc m (contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i hP (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR))) := by
    rw [negativeCap_block D Sc m cutoff bound ΛP ΛR hcP i edgeP H n]
    dsimp only [vacuumBendBlock]
    rw [Category.assoc, hn]
    simp only [vacuumPreBlockSourceIso, Iso.trans_hom, eqToIso.hom,
      vacuumBendBlock, Category.assoc]
  rw [Superfunctor.comp_total]
  change (((SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP) (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP n (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR) ≫
    ((SKM.homContentPostCup ((probeOldRouquierFamily D Sc m ΛP hcP)).obj (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR r (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR)) ≫ _ = _
  rw [Category.assoc, hp, ← Category.assoc, hc, unitDotColumn_eq_restrictedDotEnd]
  simp only [Category.assoc]

/-- Even colour: each prescribed negative pre-cap followed by a dotted post-unit is
the corresponding raw vacuum bend monomial, with no compatibility premise. -/
theorem vacuumBendMonomial_even [Fact Sc.PureNilpotent] (hP : 0 < probeCutoff D m i) (hi : D.parity i = 0)
    (n r : ℕ) :
    ((SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP) (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP n (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H) ≫
      SKM.homContentPostCup ((probeOldRouquierFamily D Sc m ΛP hcP)).obj (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR r (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR) ≫
      (vacuumPostTarget D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H).hom =
    (vacuumPreBlockSourceIso D Sc m cutoff bound ΛP ΛR hcP i edgeP H).hom ≫
      (Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc m (contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))) ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D Sc m (contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i hP (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR))) ≫
          (adjunction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).unit.app (((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).obj (probeOldVacuumRegular D Sc m)) ≫
            restrictedDotEnd (contentAppend D Sc cutoff bound (0 : Multiset I) [i]) (canonicalAppendDot_supernatural D Sc cutoff bound (0 : Multiset I) i) (((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).obj (probeOldVacuumRegular D Sc m)) ^ r := by
  have hp := vacuumBendPostCup_eq D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H r
  have hn := vacuumPreNegativeCap_even D Sc m ΛP hcP (fun _ => (contentModuleTarget D Sc cutoff bound (0 : Multiset I))) (-ΛR) i edgeP (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR))) hP hi n
  have hc : ((SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP) (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP n (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR) ≫
      ((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).map (eqToHom (emptyProbe_regular D Sc m ΛP)) =
      (vacuumPreBlockSourceIso D Sc m cutoff bound ΛP ΛR hcP i edgeP H).hom ≫
        (Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc m (contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))) ^ n) ≫
          ProbeVacuumCap.shiftedPreCap D Sc m (contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i hP (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR))) := by
    rw [negativeCap_block D Sc m cutoff bound ΛP ΛR hcP i edgeP H n]
    dsimp only [vacuumBendBlock]
    rw [Category.assoc, hn]
    simp only [vacuumPreBlockSourceIso, Iso.trans_hom, eqToIso.hom,
      vacuumBendBlock, Category.assoc]
  rw [Superfunctor.comp_total]
  change (((SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP) (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP n (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR) ≫
    ((SKM.homContentPostCup ((probeOldRouquierFamily D Sc m ΛP hcP)).obj (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR r (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR)) ≫ _ = _
  rw [Category.assoc, hp, ← Category.assoc, hc, unitDotColumn_eq_restrictedDotEnd]
  simp only [Category.assoc]

end OddMath.QuiverHecke.ELV.WeightTensorVacuum
end

end
