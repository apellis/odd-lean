/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Sigma.BWWMixedEntry
import OddMath.SKM.BWWPureNilpotent

/-! # Distinct-colour entries for parameters with nilpotent pure coefficients

BE2 (1.11), in the swapped construction, for the box parameters of Brundan–Wang–Webster,
arXiv:2505.22929v2, §2.2, whose pure coefficients `sᵢⱼ^{p0}` lie in a nilpotent ideal
(`ScalarData.PureNilpotent`). The mixed entry only needs the source polynomial unit
criterion; the pure terms are absorbed by `isIso_homDistinctMixedMateDot_bwwParam_sourceUnits`.
This module is an intermediate reduction.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB vB wB
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{wB, vB} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

/-- Source-unit form of the dotted mixed mate of `Qᵢⱼ`, for parameters whose pure
coefficients lie in a nilpotent ideal (`ScalarData.PureNilpotent`). -/
theorem isIso_homDistinctMixedMateDot_param_sourceUnits_of_pureNilpotent
    (hP : Sc.PureNilpotent) {a b c d : B}
    (E : a ⟶ b) {E' : c ⟶ d}
    {F' : d ⟶ c} (A : SuperAdjunction (k := k) E' F') (κ τ : ZMod 2) (H : b ⟶ d)
    {i j : I} (hij : i ≠ j) {x : E ⟶ E} (hx : x ∈ parity (R := k) E E (D.parity i))
    {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' (D.parity j))
    (hu : MixedPostSourceUnits E A κ H
      (rouquierPower x (if D.parity i = 1 then 2 else 1))
      (rouquierPower y (if D.parity j = 1 then 2 else 1))) :
    IsIso (homDistinctMixedMateDot E A κ τ H
      (if D.d i j = 0 then (Sc.t i j : k) • (1 : End (E ≫ (homParityShift (k := k) κ).obj
          (((homParityShift (k := k) κ).obj H ≫ F') ≫ E'))) else
        (Sc.t i j : k) • mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^
            D.dn i j +
          (Sc.t j i : k) • mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ D.dn j i +
          ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
            Sc.s i j p q • (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ p *
              mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ q))) := by
  split_ifs with hd
  · have hx' : rouquierPower x (if D.parity i = 1 then 2 else 1) ∈ parity (R := k) E E 0 := by
      have h := rouquierPower_mem (k := k) hx (if D.parity i = 1 then 2 else 1)
      rwa [mul_parity_pow_eq_zero] at h
    have hy' : rouquierPower y (if D.parity j = 1 then 2 else 1) ∈ parity (R := k) E' E' 0 := by
      have h := rouquierPower_mem (k := k) hy (if D.parity j = 1 then 2 else 1)
      rwa [mul_parity_pow_eq_zero] at h
    have h := isIso_homDistinctMixedMateDot_of_pow_sourceUnits E A κ τ H hx' hy' hu (Sc.t i j) 0
      (N := 0) (Submodule.zero_mem _)
    rwa [mul_zero, pow_zero, add_zero] at h
  · obtain ⟨J, N, hJ, hpure⟩ := hP
    have h := isIso_homDistinctMixedMateDot_bwwParam_sourceUnits E A κ τ H Sc.toBWW hJ hpure hij
      hx hy hu
    rwa [sum_box_toBWW Sc hij hd (fun p q =>
      mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ p *
        mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ q)] at h

variable (P : ProbeReservoir k B D Sc)

attribute [local irreducible] Finsupp.zipWith Finsupp.single Finsupp.onFinset homContentShift
  contentWeight in
/-- Mixed sideways crossing invertibility from the source-polynomial unit
criterion. The criterion remains an explicit intermediate hypothesis. -/
theorem isIso_sigmaEntry_probe_reservoir_sourceUnits (hP : Sc.PureNilpotent)
    (hu : ∀ (i j : I), i ≠ j →
      ∀ {a b c d : X} (hT : a + D.α i = b) (hW : c + D.α j = d)
        (κ : ZMod 2) (H : P.T.obj b ⟶ P.W.obj d),
      MixedPostSourceUnits (P.T.E i hT) (P.W.adj j hW) κ H
        (rouquierPower (P.T.dot i hT) (if D.parity i = 1 then 2 else 1))
        (rouquierPower (P.W.dot j hW) (if D.parity j = 1 then 2 else 1)))
    (c : P.CrossCoeff) {i j : I} (hij : i ≠ j) (ν : X) (t : Sector I)
    (q : SPath (wd D ν [dn i, up j]) t
      (nextSector (dn i) false (nextSector (up j) true t)))
    (Z : P.H (nextSector (dn i) false (nextSector (up j) true t))) :
    IsIso (P.sigmaEntry c i j ν
      (SPath.cons _ true t trivial (SPath.cons _ false _ trivial (SPath.nil _))) q Z) := by
  have hR : StepValid (up i) false (nextSector (dn i) false t) := by
    simp [StepValid, nextSector]
  have e₀ : nextSector (up i) false (nextSector (dn i) false t) = t := by
    simp only [nextSector]; ext <;> simp
  let cupPath : SPath (wd D (SKM.wt D ν [up j, dn i]) (SKM.Shape.cup i).cod) t t :=
    SPath.two false false trivial hR e₀
  let p : SPath (wd D ν [up j, dn i]) t (nextSector (dn i) false (nextSector (up j) true t)) :=
    SPath.cons _ true t trivial (SPath.cons _ false _ trivial (SPath.nil _))
  let m₁ : SPath (wd D ν [dn i, up i, up j, dn i]) t
      (nextSector (dn i) false (nextSector (up j) true t)) :=
    ((SPath.nil t).append cupPath).append p
  have hR' : StepValid (up i) false (nextSector (up j) true (nextSector (dn i) false t)) := by
    simp [StepValid, nextSector]
  have e₁ : nextSector (up j) true (nextSector (up i) false (nextSector (dn i) false t)) =
      nextSector (up j) true t := by rw [e₀]
  have e₂ : nextSector (up i) false (nextSector (up j) true (nextSector (dn i) false t)) =
      nextSector (up j) true t := by
    simp only [nextSector]; ext <;> simp
  let pu₂ : SPath (wd D (SKM.wt D ν ((SKM.Shape.cross i j).dom ++ [dn i])) [dn i]) t
      (nextSector (dn i) false t) := SPath.cons _ false t trivial (SPath.nil _)
  let pv₂ : SPath (wd D ν [dn i]) (nextSector (up j) true t)
      (nextSector (dn i) false (nextSector (up j) true t)) :=
    SPath.cons _ false _ trivial (SPath.nil _)
  let crossDom : SPath (wd D (SKM.wt D ν [dn i]) (SKM.Shape.cross i j).dom)
      (nextSector (dn i) false t) (nextSector (up j) true t) := SPath.two false true hR trivial e₁
  let crossCod : SPath (wd D (SKM.wt D ν [dn i]) (SKM.Shape.cross i j).cod)
      (nextSector (dn i) false t) (nextSector (up j) true t) := SPath.two true false trivial hR' e₂
  let m₂ : SPath (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]).cod.word t
      (nextSector (dn i) false (nextSector (up j) true t)) := (pu₂.append crossCod).append pv₂
  have hm₁ : m₁ = (pu₂.append crossDom).append pv₂ := SPath.eq_of_sides _ _ (by
    simp only [m₁, cupPath, p, pu₂, pv₂, crossDom, SPath.sides_append, SPath.sides_two]; rfl)
  rw [P.sigmaEntry_eq c hij ν _ q m₁ m₂ Z (a := true) (b := false) rfl (by
      simp only [m₁, cupPath, p, SPath.sides_append, SPath.sides_two]; rfl)
    (by simp only [m₂, pu₂, pv₂, crossCod, SPath.sides_append, SPath.sides_two]; rfl)]
  have h₁ : compLayer (P.upwardGens c) (SKM.lay D ν [] (Shape.cup i) [up j, dn i]) p m₁ Z = _ :=
    P.compLayer_eq (P.upwardGens c) (SKM.lay D ν [] (Shape.cup i) [up j, dn i])
      (SPath.nil t) (SPath.nil t) cupPath p Z
  have h₂ : compLayer (P.upwardGens c) (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i])
      ((pu₂.append crossDom).append pv₂) m₂ Z = _ :=
    P.compLayer_eq (P.upwardGens c) (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i])
      pu₂ crossDom crossCod pv₂ Z
  let t' := nextSector (dn i) false t
  let u := nextSector (dn i) false (nextSector (up j) true t)
  have hR'' : StepValid (up i) false u := by simp [u, StepValid, nextSector]
  have ecap : nextSector (dn i) false (nextSector (up i) false u) = u := by
    simp only [u, nextSector]; ext <;> simp
  let pu₃ : SPath (wd D (SKM.wt D ν ((SKM.Shape.cap i).dom ++ [])) [dn i, up j]) t u :=
    SPath.cons _ false t trivial (SPath.cons _ true t' trivial (SPath.nil _))
  let capPath : SPath (wd D (SKM.wt D ν []) (SKM.Shape.cap i).dom) u u :=
    SPath.two false false hR'' trivial ecap
  have hm₂ : m₂.cast (sigma_cross_cap_word i j ν) = (pu₃.append capPath).append (SPath.nil _) :=
    SPath.eq_of_sides _ _ (by
      simp only [SPath.sides_cast, m₂, pu₂, pv₂, crossCod, pu₃, capPath, SPath.sides_append,
        SPath.sides_two]; rfl)
  have hq : q.cast (sigma_cap_word i j ν) = (pu₃.append (SPath.nil _)).append (SPath.nil _) :=
    SPath.eq_of_sides _ _ (by
      have : Subsingleton (SPath (wd D ν [dn i, up j]) t u) := SPath.subsingleton_dnUp hij _ _ t u
      rw [Subsingleton.elim q (SPath.cons _ false t (by trivial) (SPath.cons _ true t'
        (by trivial) (SPath.nil _)))]
      simp only [SPath.sides_cast, pu₃, SPath.sides_append]; rfl)
  have h₃ := P.compLayer_eq (P.upwardGens c) (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) [])
      pu₃ capPath (SPath.nil _) (SPath.nil _) Z
  conv at h₁ =>
    rhs
    dsimp only [SKM.lay]
    simp only [Generators.image, upwardGens, cupImage]
    rw [P.zeroTwo_two (hZ := eqRec_heq e₀.symm _)]
    simp only [cupEntry]
    unfold postCup
    simp only [pathFunctor_cons, pathFunctor_nil_map, Functor.comp_map, Functor.id_map, dn, up,
      step, homContentPreE_map, Functor.map_comp, Category.assoc]
  conv at h₂ =>
    rhs
    dsimp only [SKM.lay]
    simp only [Generators.image, upwardGens, crossImage, dite_eq_right hij]
    rw [P.twoTwo_two (hZ := eqRec_heq e₂.symm _)]
    simp only [crossNeEntry]
    unfold mixedJ
    simp only [pu₂, pathFunctor_cons, pathFunctor_nil_map, Functor.comp_map, Functor.id_map, dn, up,
      step, homContentPreE_map, Functor.map_comp, Category.assoc]
  conv at h₃ =>
    rhs
    dsimp only [SKM.lay]
    simp only [Generators.image, upwardGens, capImage]
    rw [P.twoZero_two (hZ := eqRec_heq ecap.symm _)]
    simp only [capEntry]
    unfold postCap
    simp only [pu₃, pathFunctor_cons, pathFunctor_nil_map, Functor.comp_map, Functor.id_map, dn, up,
      step, homContentPreE_map, Functor.map_comp, Category.assoc]
  have h₂' := P.compLayer_congr (P.upwardGens c)
    (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]) hm₁ (rfl : m₂ = m₂) Z
  rw [h₂] at h₂'
  have h₃' := P.compLayer_congr (P.upwardGens c) (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) [])
    hm₂ hq Z
  rw [h₃] at h₃'
  refine isIso_comp_layers _ _ h₁ h₂' h₃' ?_
  simp only [Category.assoc]
  refine isIso_postCup_mixedCross_postCap P.T.obj P.W i t.1 u.1 (μ₀ := P.muP t)
    (μ₁ := P.muP u) (P.T.E j (P.muP_preE j t')) (m₀ := P.muM t)
    (m₁ := P.muM (nextSector (true, i) false u)) (n := P.muM u) ?hm (P.muM_postF i t)
    (P.muM_postE i hR'') _ (fun Y => P.mixedQ j i t' hR' Y) ?hiso _ ?hA _ ?hB
    _ _ ?hf2 _ _ ?hf5 _ _ _ _ _ _ _ _ _ _ _ ?hf18 _ _ ?hf21 _ _ _
  case hf2 | hf5 | hf18 | hf21 => eqToHom_witness
  case hm => simp only [muM, u, nextSector, add_tsub_cancel_right]
  case hiso =>
    exact isIso_homDistinctMixedMateDot_param_sourceUnits_of_pureNilpotent hP _ _ _ _ _ hij.symm
      (P.T.dot_mem j _) (P.W.dot_mem i _) (hu j i hij.symm _ _ _ _)
  case hA =>
    apply eq_of_heq
    refine (eqRec_heq _ _).trans ((eqRec_heq _ _).trans ?_)
    refine HEq.trans (HEq.rfl : (P.pathFunctor p).obj Z ≍ P.T.E j (P.muP_preE j t') ≫
      (homContentPostF P.T.obj P.W i u.1 (P.muP u) (P.muM_postF i t)).obj Z) ?_
    apply heq_of_eq
    exact congrArg (fun Y => P.T.E j (P.muP_preE j t') ≫
      (homContentPostF P.T.obj P.W i u.1 (P.muP u) (P.muM_postF i t)).obj Y)
      (eq_of_heq ((eqRec_heq _ _).trans (eqRec_heq _ _))).symm
  case hB =>
    apply eq_of_heq
    refine (eqRec_heq _ _).trans ?_
    exact homContentPostF_obj_heq (Z := Z) P.T.obj P.W i u.1 (P.muP u)
      (by simp only [muM, u, nextSector, add_tsub_cancel_right]) rfl
      (P.muM_postF i (nextSector (up j) true t)) _
      ((eqRec_heq _ _).trans (eqRec_heq _ _)).symm

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
