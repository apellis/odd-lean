/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedVacuumCap

/-! # The padded reservoir unit columns on the regular vacuum probe

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*,
§8. The unit columns of the negative two-sector matrix at the vacuum sector
are the prescribed padded post-cups `centralPaddedUnit false n`. This file
evaluates them on the regular probe: through the cap-target chart
`paddedVacuumCapTargetIso` (the source of every column) and the target chart
of the padded Dx entry (`paddedVacuumTargetIso`), the `n`-th unit column is
the native unit followed by `n` canonical dots (`paddedVacuumUnit_native`).
No parity, moment or unit compatibility is assumed.
-/
noncomputable section
set_option quotPrecheck false
set_option autoImplicit false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly
universe u
local instance paddedVacuumUnitHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

section Pullback

variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : SKM.Datum I X}
  (T W : SKM.RouquierFamily (k := k) (B := B) D)
  {a a' b b' : X} (ha : a = a') (hb : b = b')
  (Z' : SKM.homWeightSector T.obj W.obj a' b')

/-- The dotted post-cup on a pulled-back input is the post-cup on the
normalized input, through the return chart and the target pullback chart. -/
theorem homPostCup_weight_pullback_square (i : I) (β : I →₀ ℕ) {d : X}
    (hr : b + D.α i = d) (n : ℕ) :
    (SKM.homWeightEquivalence T W ha hb).functor.map
        (SKM.homContentPostCup T.obj W i β a hr n
          ((SKM.homWeightEquivalence T W ha hb).inverse.obj Z')) ≫
      (SKM.homPostWeightPullbackIso T W ha hb i hr β Z').hom =
    (capPullbackSelfIso T W ha hb Z').hom ≫
      SKM.homContentPostCup T.obj W i β a' (show b' + D.α i = d from hb ▸ hr) n Z' := by
  subst a'
  subst b'
  change SKM.homContentPostCup T.obj W i β a hr n Z' ≫ 𝟙 _ =
    𝟙 _ ≫ SKM.homContentPostCup T.obj W i β a hr n Z'
  simp only [Category.comp_id, Category.id_comp]

end Pullback

section Padded

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR

omit [Fintype I] in
private theorem unitProbeWeight_zero : (P).muP (((0, 0) : Sector I)) = ΛP := by
  simp [ProbeReservoir.muP, elvProbeReservoir]
omit [Fintype I] in
private theorem unitReservoirWeight_zero : (P).muM (((0, 0) : Sector I)) = -ΛR := by
  simp [ProbeReservoir.muM, elvProbeReservoir]

private def unitVacuumEvaluation :
    SKM.homWeightSector (P).T.obj (P).W.obj ΛP (-ΛR) ⥤
      ContentModules D (parameterTwist D Sc) cutoff bound (0 : Multiset I) :=
  homContentEvaluation D (parameterTwist D Sc) cutoff bound ΛR (-ΛR)
    ((P).T.obj (-ΛP)) (regularProbe D (parameterTwist D Sc) m ΛP) (emptyBlock D ΛR)

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))

/-- **The padded unit column at the vacuum sector.** The prescribed padded
post-cup `n` is the native unit followed by `n` canonical dots, through the
cap-target chart and the target chart of the padded Dx entry. No parity,
moment or unit compatibility is assumed. -/
theorem paddedVacuumUnit_native (i : I) (n : ℕ) :
    (P).centralPaddedUnit i (((0, 0) : Sector I))
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) false n ≫
      (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
    (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom ≫
      unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i])
        (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound
          (0 : Multiset I) i)
        ((vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).obj
          (probeOldVacuumRegular D (parameterTwist D Sc) m)) n := by
  classical
  let PR := elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
  let E₀ := unitVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let Z := vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H
  let E := vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let Z₀ := preCapInput D (parameterTwist D Sc) m ΛP hcP
    (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H
  let ha := unitProbeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let hb := unitReservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let er := PR.muM_postF i (0, 0)
  let er₀ : -ΛR + D.α i = PR.muM (nextSector (false, i) false (((0, 0) : Sector I))) :=
    (congrArg (fun x : X => x + D.α i) hb).symm.trans er
  let tc := PR.centralTargetCornerIso i (0, 0) Z E ⟨false, by trivial⟩
  let cup := SKM.homContentPostCup PR.T.obj PR.W i 0 (PR.muP (0, 0)) er n Z
  let v := E₀.mapIso (SKM.homPostWeightPullbackIso PR.T PR.W ha hb i er 0 Z₀)
  let f := vacuumPostTarget D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR i er₀ 0 H
  let back := E₀.map (capPullbackSelfIso PR.T PR.W ha hb Z₀).hom
  let cup₀ := SKM.homContentPostCup PR.T.obj PR.W i 0 ΛP er₀ n Z₀
  let q := (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).toFunctor.map
    (eqToHom (emptyProbe_regular D (parameterTwist D Sc) m ΛP))
  let col := unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound
      (0 : Multiset I) [i])
    (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound (0 : Multiset I) i)
    ((vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).obj
      (probeOldVacuumRegular D (parameterTwist D Sc) m)) n
  have hunit : PR.centralPaddedUnit i (((0, 0) : Sector I)) Z E false n =
      E.map cup ≫ tc.inv := by
    unfold ProbeReservoir.centralPaddedUnit
    rw [dif_pos (show StepValid (SKM.dn i) false (((0, 0) : Sector I)) from by trivial)]
    rfl
  have htgt : (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      tc.hom ≫ v.hom ≫ f.hom := rfl
  have hcap : (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom =
      back ≫ q := rfl
  have hE : E.map cup = E₀.map ((SKM.homWeightEquivalence PR.T PR.W ha hb).functor.map cup) :=
    rfl
  have hsq : E₀.map ((SKM.homWeightEquivalence PR.T PR.W ha hb).functor.map cup) ≫ v.hom =
      back ≫ E₀.map cup₀ := by
    have h := congrArg E₀.map
      (homPostCup_weight_pullback_square PR.T PR.W ha hb Z₀ i 0 er n)
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h
  have hn : E₀.map cup₀ ≫ f.hom = q ≫ col :=
    vacuumBendPostCup_native D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR i er₀ 0 H n
  rw [hunit, htgt, hcap, Category.assoc, Iso.inv_hom_id_assoc, hE, ← Category.assoc, hsq,
    Category.assoc, hn, Category.assoc]

end Padded

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
