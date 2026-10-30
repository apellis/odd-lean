/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentMixedBraid
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.MiddleDistinctProbeSector

/-! # Q-weighted adjacent mixed J rectangle

The `Pᵢ Rᵢ Pⱼ → Pⱼ Rᵢ Pᵢ` comparison rectangle retains its mixed Q
weight. Only mixed comparison isomorphisms are cancelled.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hR : StepValid (true, i) false s)
  (hs₀ : nextSector (true, j) true (nextSector (true, i) true s) =
    nextSector (true, i) true (nextSector (true, j) true s))
  (hs : nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)) =
    nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s))))

/-- The probe crossing with its reservoir spectator, on the raw common grid.
The equality morphism only aligns the terminal sector transport. -/
def adjacentMixedProbeCross :=
  eqToHom (congrArg (fun Y => (P.step (true, i) true s trivial).obj
    ((P.step (true, j) true _ trivial).obj Y))
    (P.reservoirDot_cast i hs₀ hR hR Z).1).symm ≫
  P.preCrossNe i j s hs₀ ((P.step (true, i) false
    (nextSector (true, i) true (nextSector (true, j) true s)) hR).obj Z)

/-- The inner Q factor passes through the probe crossing; this follows from
actual dot slides and spectator supernaturalness, not a transport input. -/
theorem adjacentMixedProbeCross_Q (hij : i ≠ j) :
    (P.step (true, i) true s trivial).map
        (P.mixedQ j i (nextSector (true, i) true s) hR (hs ▸ Z)) ≫
      P.adjacentMixedProbeCross i j s hR hs₀ Z =
    P.adjacentMixedProbeCross i j s hR hs₀ Z ≫
      (P.distinctProbeFirstIso j i i s hR Z).hom ≫
        P.mixedQ j i s hR ((P.step (true, i) true _ trivial).obj Z) ≫
      (P.distinctProbeFirstIso j i i s hR Z).inv := by
  let Y := (P.step (true, i) false (nextSector (true, i) true (nextSector (true, j) true s)) hR).obj Z
  let θ := P.dotDiag i false (nextSector (true, i) true (nextSector (true, j) true s)) hR Z
  have hθ : θ ∈ parity (R := k) _ _ (D.parity i) := by
    have h := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W i
      (nextSector (true, i) true (nextSector (true, j) true s)).1
      (P.muP (nextSector (true, i) true (nextSector (true, j) true s)))
      (P.muM_postE i hR) 1).mem Z
    simpa only [θ, dotDiag, step, Nat.cast_one, one_mul, pow_one] using h
  have hQ := P.preCrossNe_qExpr_inner i j i hij s hs₀ Y θ hθ
  obtain ⟨hY, hd⟩ := P.reservoirDot_cast i hs₀ hR hR Z
  have hw := P.probeInnerQ_heq i j i s hY hd
  have hw' : HEq ((P.step (true, i) true s trivial).map
      (P.mixedQ j i (nextSector (true, i) true s) hR (hs ▸ Z)))
      (P.probeInnerQ i j i s ((P.castH hs₀).obj Y) ((P.castH hs₀).map θ)) :=
    (heq_of_eq (P.distinctProbe_map_mixedQ i j i s hR (hs ▸ Z))).trans hw.symm
  have hA := congrArg (fun Y => (P.step (true, i) true s trivial).obj
    ((P.step (true, j) true _ trivial).obj Y)) hY
  have hf : HEq (P.adjacentMixedProbeCross i j s hR hs₀ Z)
      (P.preCrossNe i j s hs₀ Y) := by
    simpa only [adjacentMixedProbeCross, eqToHom_refl, Category.comp_id] using
      (sandwich_heq hA.symm rfl (P.preCrossNe i j s hs₀ Y))
  apply rectangle_of_heq hA.symm hA.symm hA.symm rfl rfl hw' hf hf
    (heq_of_eq (P.distinctProbeFirstIso_conj_mixedQ j i i s hR Z))
  apply heq_of_eq
  simpa only [probeInnerQ, Category.assoc, Y, θ, dotDiag, distinctProbeOuterDot,
    distinctProbeInnerDot, distinctProbeSpectatorDot, prPreDot, prPostDot, castH] using hQ

/-- The Q-weighted J rectangle on `Pᵢ Rᵢ Pⱼ → Pⱼ Rᵢ Pᵢ`.
No coefficient inputs, braid hypothesis, or reservoir-colour inequality is used. -/
theorem adjacentMixed_J_rectangle (hij : i ≠ j) :
    (P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj (hs ▸ Z))).hom ≫
      P.adjacentMixedMove i j s hR hs Z =
    (P.step (true, i) true s trivial).map
      ((P.mixedJ j i (nextSector (true, i) true s) hR (hs ▸ Z)).inv ≫
        P.mixedQ j i (nextSector (true, i) true s) hR (hs ▸ Z)) ≫
      P.adjacentMixedProbeCross i j s hR hs₀ Z ≫
      (P.step (true, j) true s trivial).map
        (P.mixedJ i i (nextSector (true, j) true s) hR Z).hom := by
  have hp := P.preCrossNe_mixedJ_pair_heq i j i s hR hs₀ hs Z
  have hA := congrArg (fun Y => (P.step (true, i) true s trivial).obj
    ((P.step (true, j) true _ trivial).obj Y))
    (P.reservoirDot_cast i hs₀ hR hR Z).1
  have hp' := eq_of_heq ((sandwich_heq hA.symm rfl _).trans hp)
  simp only [eqToHom_refl, Category.comp_id, ← Category.assoc] at hp'
  change ((P.adjacentMixedProbeCross i j s hR hs₀ Z ≫ _) ≫ _) = _ at hp'
  apply (cancel_epi ((P.step (true, i) true s trivial).mapIso
    (P.mixedJ j i (nextSector (true, i) true s) hR (hs ▸ Z))).hom).1
  simp only [Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((P.step (true, i) true s trivial).map
      (P.mixedJ j i (nextSector (true, i) true s) hR (hs ▸ Z)).hom)
      ((P.step (true, i) true s trivial).map
        (P.mixedJ j i (nextSector (true, i) true s) hR (hs ▸ Z)).inv),
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  dsimp only [adjacentMixedMove]
  rw [← Category.assoc, ← Category.assoc, ← hp']
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc ((P.step (true, i) true s trivial).map
      (P.mixedQ j i (nextSector (true, i) true s) hR (hs ▸ Z))),
    P.adjacentMixedProbeCross_Q i j s hR hs₀ hs Z hij]
  change _ = (_ ≫ (P.distinctProbeFirstIso j i i s hR Z).hom ≫ _ ≫
    (P.distinctProbeFirstIso j i i s hR Z).inv) ≫
    (P.distinctProbeFirstIso j i i s hR Z).hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Raw heterogeneous version of the Q-weighted rectangle. The only endpoint
alignment is the equality morphism in `adjacentMixedProbeCross`. -/
theorem adjacentMixed_J_rectangle_heq (hij : i ≠ j) :
    HEq
      ((P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj (hs ▸ Z))).hom ≫
        P.adjacentMixedMove i j s hR hs Z)
      ((P.step (true, i) true s trivial).map
        ((P.mixedJ j i (nextSector (true, i) true s) hR (hs ▸ Z)).inv ≫
          P.mixedQ j i (nextSector (true, i) true s) hR (hs ▸ Z)) ≫
        P.adjacentMixedProbeCross i j s hR hs₀ Z ≫
        (P.step (true, j) true s trivial).map
          (P.mixedJ i i (nextSector (true, j) true s) hR Z).hom) :=
  heq_of_eq (P.adjacentMixed_J_rectangle i j s hR hs₀ hs Z hij)

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
