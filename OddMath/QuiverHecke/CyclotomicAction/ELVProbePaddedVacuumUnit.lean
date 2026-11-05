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
the native unit followed by `n` canonical dots (`paddedVacuumUnit_eq`).
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

/-- Attach the target and cap-target charts to a pulled-back unit square. -/
private theorem unit_charts_attach {C : Type*} [Category C]
    {S T₀ T₁ T₂ T₃ S' S'' : C} (a : S ⟶ T₁) (t : T₀ ≅ T₁) (v : T₁ ≅ T₂) (f : T₂ ≅ T₃)
    (b : S ⟶ S') (a₀ : S ⟶ T₁) (c : S' ⟶ T₂) (q : S' ⟶ S'') (col : S'' ⟶ T₃)
    (hE : a = a₀) (hsq : a₀ ≫ v.hom = b ≫ c) (hn : c ≫ f.hom = q ≫ col) :
    (a ≫ t.inv) ≫ (t ≪≫ v ≪≫ f).hom = (b ≫ q) ≫ col := by
  simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [hE, reassoc_of% hsq, hn]

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
theorem paddedVacuumUnit_eq (i : I) (n : ℕ) :
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
    rw [dite_eq_left_of_eq_true (eq_true (show StepValid (SKM.dn i) false
      (((0, 0) : Sector I)) from by trivial))]
    rfl
  have hE : E.map cup = E₀.map ((SKM.homWeightEquivalence PR.T PR.W ha hb).functor.map cup) := by
    simp only [E, vacuumSectorEvaluation, Functor.comp_map]
    rfl
  have hsq : E₀.map ((SKM.homWeightEquivalence PR.T PR.W ha hb).functor.map cup) ≫ v.hom =
      back ≫ E₀.map cup₀ := by
    have h := congrArg E₀.map
      (homPostCup_weight_pullback_square PR.T PR.W ha hb Z₀ i 0 er n)
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h
  have hc₀ : E₀.map cup₀ = cup₀.total (regularProbe D (parameterTwist D Sc) m ΛP)
      (emptyBlock D ΛR) := by
    simp only [cup₀, E₀, unitVacuumEvaluation, homContentEvaluation, Functor.comp_map,
      Pi.eval_map, homTotalEvaluation]
  have hn₁ := vacuumBendPostCup_eq D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR i
    er₀ 0 H n
  have hn : E₀.map cup₀ ≫ f.hom = q ≫ col := by
    rw [hc₀]
    exact hn₁
  have hs := unit_charts_attach (E.map cup) tc v f back
    (E₀.map ((SKM.homWeightEquivalence PR.T PR.W ha hb).functor.map cup)) (E₀.map cup₀) q col
    hE hsq hn
  rw [hunit]
  exact hs

end Padded

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
