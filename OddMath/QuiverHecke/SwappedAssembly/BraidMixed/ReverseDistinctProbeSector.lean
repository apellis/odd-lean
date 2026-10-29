/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctProbeQ
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ReverseDistinctProbeEdges

/-! # Reverse Q-weighted braid with three distinct colours

Both prescribed Q factors are retained. Only the mixed comparison isomorphisms
are cancelled; the probe crossing is not assumed invertible.
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
variable (P : ProbeReservoir k B D Sc)

/-- The Q factors on the two probe orders intertwine the prescribed probe edge. -/
theorem distinctProbeSectorWeight_cross (ν : X) (i j r : I) (s : Sector I)
    (hR : StepValid (true, r) false s) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    (hs : nextSector (true, j) true (nextSector (true, i) true s) =
      nextSector (true, i) true (nextSector (true, j) true s))
    (hsR : nextSector (true, r) false (nextSector (true, j) true (nextSector (true, i) true s)) =
      nextSector (true, r) false (nextSector (true, i) true (nextSector (true, j) true s)))
    (Z : P.H (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, j) true s)))) :
    P.distinctProbeSectorWeight ν i j r s hR hsR Z ≫
        crossEntry (P.swappedGens c L) ν [] i j [up r]
          (distinctProbeSource ν i j r s hR hsR) (distinctProbeSource ν j i r s hR rfl) Z =
      crossEntry (P.swappedGens c L) ν [] i j [up r]
          (distinctProbeSource ν i j r s hR hsR) (distinctProbeSource ν j i r s hR rfl) Z ≫
        P.distinctProbeSectorWeight ν j i r s hR rfl Z := by
  let Y := (P.step (true, r) false (nextSector (true, i) true (nextSector (true, j) true s)) hR).obj Z
  let θ := P.dotDiag r false (nextSector (true, i) true (nextSector (true, j) true s)) hR Z
  have hθ : θ ∈ parity (R := k) _ _ (D.parity r) := by
    have h := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W r
      (nextSector (true, i) true (nextSector (true, j) true s)).1
      (P.muP (nextSector (true, i) true (nextSector (true, j) true s)))
      (P.muM_postE r hR) 1).mem Z
    simpa only [θ, dotDiag, step, Nat.cast_one, one_mul, pow_one] using h
  have hQ := P.preCrossNe_qExpr_pair i j r hij s hs Y θ hθ
  obtain ⟨hA, hf⟩ := P.distinctProbe_left ν i j r s hR hs hsR c L Z hij hir hjr
  obtain ⟨hY, hd⟩ := P.reservoirDot_cast r hs hR hR Z
  have hw := P.probeQPair_heq i j r s hY hd
  have hw' : HEq (P.distinctProbeSectorWeight ν i j r s hR hsR Z)
      (P.probeQPair i j r s ((P.castH hs).obj Y) ((P.castH hs).map θ)) :=
    (P.distinctProbeSectorWeight_heq ν i j r s hR hsR Z).trans hw.symm
  apply rectangle_of_heq hA hA hA rfl rfl hw' hf hf
    (P.distinctProbeSectorWeight_heq ν j i r s hR rfl Z)
  apply heq_of_eq
  simpa only [probeQPair, Category.assoc, Y, θ, dotDiag, distinctProbeOuterDot,
    distinctProbeInnerDot, distinctProbeSpectatorDot, prPreDot, prPostDot, castH] using hQ

/-- Reverse mixed movement equals the inverse comparison followed by both Q factors. -/
theorem reverseDistinctProbe_move_eq (ν : X) (i j r : I) (s : Sector I)
    (hR : StepValid (true, r) false s) {t : Sector I}
    (e : nextSector (true, r) false (nextSector (true, j) true (nextSector (true, i) true s)) = t)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (Z : P.H t)
    (hir : i ≠ r) (hjr : j ≠ r) :
    crossEntry (P.swappedGens c L) ν [] r i [up j]
        (distinctProbeTarget ν i j r s hR e) (distinctProbeMiddle ν i j r s hR e) Z ≫
      crossEntry (P.swappedGens c L) ν [up i] r j []
        (distinctProbeMiddle ν i j r s hR e) (distinctProbeSource ν i j r s hR e) Z =
      (P.distinctProbeMoveIso ν i j r s hR e Z).inv ≫
        P.distinctProbeSectorWeight ν i j r s hR e Z := by
  subst e
  rw [eq_of_heq (P.reverseDistinctProbe_move_heq ν i j r s hR rfl c L Z hir hjr)]
  change _ = ((P.distinctProbeFirstIso i j r s hR Z).trans
    (P.mixedJ i r s hR ((P.step (true, j) true _ trivial).obj Z))).inv ≫
      (𝟙 _ ≫ _ ≫ 𝟙 _)
  rw [Category.id_comp, Category.comp_id]
  rw [← P.distinctProbeFirstIso_conj_mixedQ i j r s hR Z,
    ← P.distinctProbe_map_mixedQ i j r s hR Z]
  simp only [Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc]
  simp only [distinctProbeFirstIso, Functor.mapIso_inv, Functor.map_comp]

/-- The sector `RᵣPᵢPⱼ → PⱼPᵢRᵣ` of the braid relation for pairwise distinct
colours, with arbitrary coefficients and the two prescribed mixed Q weights. -/
theorem reverseDistinctProbe_braid (ν : X) (i j r : I) (s : Sector I)
    (hR : StepValid (true, r) false s) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    (hsR : nextSector (true, r) false (nextSector (true, j) true (nextSector (true, i) true s)) =
      nextSector (true, r) false (nextSector (true, i) true (nextSector (true, j) true s)))
    (Z : P.H (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, j) true s)))) :
    braidLeft (P.swappedGens c L) r i j ν
      (distinctProbeTarget ν i j r s hR hsR) (distinctProbeSource ν j i r s hR rfl) Z =
    braidRight (P.swappedGens c L) r i j ν
      (distinctProbeTarget ν i j r s hR hsR) (distinctProbeSource ν j i r s hR rfl) Z := by
  classical
  have hs : nextSector (true, j) true (nextSector (true, i) true s) =
      nextSector (true, i) true (nextSector (true, j) true s) := by
    simp only [nextSector, add_right_comm]
  let t := nextSector (true, r) false (nextSector (true, i) true (nextSector (true, j) true s))
  let : Subsingleton (SPath (wd D ν [up i, up j, up r]) s t) :=
    ⟨path_eq_three_distinct hij hir hjr⟩
  let := Fintype.ofFinite (SPath (wd D ν [up i, up j, up r]) s t)
  let : Subsingleton (SPath (wd D ν [up j, up i, up r]) s t) :=
    ⟨path_eq_three_distinct hij.symm hjr hir⟩
  let := Fintype.ofFinite (SPath (wd D ν [up j, up i, up r]) s t)
  let : Subsingleton (SPath (wd D ν [up j, up r, up i]) s t) :=
    ⟨path_eq_three_distinct hjr hij.symm hir.symm⟩
  let := Fintype.ofFinite (SPath (wd D ν [up j, up r, up i]) s t)
  let : Subsingleton (SPath (wd D ν [up i, up r, up j]) s t) :=
    ⟨path_eq_three_distinct hir hij hjr.symm⟩
  let := Fintype.ofFinite (SPath (wd D ν [up i, up r, up j]) s t)
  let : Subsingleton (SPath (wd D ν [up r, up i, up j]) s t) :=
    ⟨path_eq_three_distinct hir.symm hjr.symm hij⟩
  let := Fintype.ofFinite (SPath (wd D ν [up r, up i, up j]) s t)
  let : Subsingleton (SPath (wd D ν [up r, up j, up i]) s t) :=
    ⟨path_eq_three_distinct hjr.symm hir.symm hij.symm⟩
  let := Fintype.ofFinite (SPath (wd D ν [up r, up j, up i]) s t)
  have hf := P.distinctProbe_braid ν i j r s hR c L hij hir hjr hsR Z
  unfold braidLeft braidRight at hf
  rw [Fintype.sum_subsingleton _ (distinctProbeMiddle (D := D) ν j i r s hR rfl),
    Fintype.sum_subsingleton _ (distinctProbeSource (D := D) ν j i r s hR rfl),
    Fintype.sum_subsingleton _ (distinctProbeTarget (D := D) ν i j r s hR hsR),
    Fintype.sum_subsingleton _ (distinctProbeMiddle (D := D) ν i j r s hR hsR)] at hf
  rw [Category.assoc,
    ← P.distinctProbeMoveIso_hom_eq ν j i r s hR rfl Z c L hjr hir,
    ← P.distinctProbeMoveIso_hom_eq ν i j r s hR hsR Z c L hir hjr] at hf
  unfold braidLeft braidRight
  rw [Fintype.sum_subsingleton _ (distinctProbeSource (D := D) ν i j r s hR hsR),
    Fintype.sum_subsingleton _ (distinctProbeMiddle (D := D) ν i j r s hR hsR),
    Fintype.sum_subsingleton _ (distinctProbeMiddle (D := D) ν j i r s hR rfl),
    Fintype.sum_subsingleton _ (distinctProbeTarget (D := D) ν j i r s hR rfl)]
  conv_rhs => rw [Category.assoc]
  rw [P.reverseDistinctProbe_move_eq ν i j r s hR hsR c L Z hir hjr,
    P.reverseDistinctProbe_move_eq ν j i r s hR rfl c L Z hjr hir]
  apply (cancel_epi (P.distinctProbeMoveIso ν i j r s hR hsR Z).hom).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [P.distinctProbeSectorWeight_cross ν i j r s hR c L hij hir hjr hs hsR Z]
  rw [← Category.assoc (P.distinctProbeMoveIso ν i j r s hR hsR Z).hom,
    ← hf]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
