/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedVacuumBend

/-! # The padded reservoir cap rows on the regular vacuum probe

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*,
§8. The cap rows of the positive two-sector matrix at the vacuum sector are
the prescribed padded reservoir caps `centralPaddedCap true n`: the raw
reservoir dot `n` times, followed by the normalized pre-Hom counit. This
file evaluates them on the regular probe. Through the same source chart as
the padded Dx entry (`paddedVacuumSourceIso`), and the weight, block and
regular-input charts of the target, the `n`-th cap row is the native
`x ^ n ≫ v`, where `x` is the shifted pre dot and `v` the shifted pre cap
(`paddedVacuumCap_native`). No parity, moment or cap compatibility is
assumed.
-/
noncomputable section
set_option quotPrecheck false
set_option autoImplicit false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly
universe u
local instance paddedVacuumCapHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

section Generic

private def capTotalEvaluation {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A] (N : C) :
    Superfunctor k C A ⥤ A where
  obj F := F.obj N
  map f := f.total N
  map_id F := SuperNatTrans.id_total F.toFunctor N
  map_comp f g := Superfunctor.comp_total f g N

private theorem cap_total_pow {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F : Superfunctor k C A} (f : End F) (n : ℕ) (N : C) :
    (f ^ n).total N = ((capTotalEvaluation N).mapEnd F f) ^ n :=
  map_pow ((capTotalEvaluation N).mapEnd F) f n

private theorem power_square {C : Type*} [Category C] {A B : C}
    (x : End A) (e : A ⟶ B) (y : End B) (h : x ≫ e = e ≫ y) (n : ℕ) :
    (x ^ n) ≫ e = e ≫ (y ^ n) := by
  induction n with
  | zero => simp only [pow_zero, End.one_def, Category.id_comp, Category.comp_id]
  | succ n ih =>
    rw [pow_succ', pow_succ', End.mul_def, End.mul_def, Category.assoc, h,
      ← Category.assoc, ih, Category.assoc]

private def reservoirRow {k : Type u} [CommRing k]
    {A B R : PiSCat.{u,u,u+1} k} (E : A ⟶ B) (F : B ⟶ A) (Z : A ⟶ R)
    (σ : ZMod 2) (z : ℤ) (f : E ⟶ E) (g : E ≫ F ⟶ 𝟙 A) :
    (SKM.homPre (k := k) E).obj ((SKM.homParityShift (k := k) (C := B ⟶ R) σ).obj (F ≫ Z)) ⟶ Z :=
  z • (E ◁ ((SKM.homParityShiftDatum (k := k) σ).iso (F ≫ Z)).hom ≫
    f ▷ (F ≫ Z) ≫ g ▷ Z)

private theorem reservoirCap_row
    {I X k : Type u} [AddCommGroup X] [CommRing k] {D : SKM.Datum I X}
    (T : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    (W : X → PiSCat.{u,u,u+1} k) (i : I) (x : X) {a b : X}
    (edge : -a + D.α i = -b) (n : ℕ) (Z : T.obj (-a) ⟶ W x) :
    SKM.homReservoirCap T W i x edge n Z =
      reservoirRow (R := W x) (T.E i edge) (T.F i edge) Z
        (SKM.leftAdjParity D i (-a))
        (koszulSign (SKM.leftAdjParity D i (-a)) (1 + (n : ZMod 2) * D.parity i))
        (SKM.rouquierPower (T.dot i edge) n)
        (((((T.leftAdjScalar i (-a))⁻¹ : kˣ) : k)) • T.leftCap i edge) := by
  rw [SKM.homReservoirCap_coordinates]
  unfold reservoirRow
  erw [PiSCat.associator_inv, PiSCat.leftUnitor_hom, Category.comp_id, Category.id_comp]

private theorem reservoirRow_block
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
    ((reservoirRow (R := elvWeightSpace D Sc cutoff bound Λ x) E F Z σ z f g).total N) δ =
      eqToHom hSrc ≫ (reservoirRow (R := contentModuleTarget D Sc cutoff bound δ.1) E F
        (Z.comp (elvBlockEval D Sc cutoff bound Λ δ)) σ z f g).total N := by
  fin_cases σ
  all_goals
    have hh : hSrc = rfl := Subsingleton.elim _ _
    rw [hh]
    simp only [eqToHom_refl, Category.id_comp]
    rfl

/-- Selecting an output block of the whole weight space commutes with
every dotted reservoir cap, through the block source chart. -/
theorem reservoirCap_block
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
    (Λ x : X) (δ : WeightBlocks D Λ x)
    (T : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    (i : I) {a b : X} (edge : -a + D.α i = -b)
    (Z : T.obj (-a) ⟶ elvWeightSpace D Sc cutoff bound Λ x) (N : T.obj (-a))
    (hSrc : (((SKM.homContentPreE T (elvWeightSpace D Sc cutoff bound Λ) i x edge).obj
        ((SKM.homContentPreF T (elvWeightSpace D Sc cutoff bound Λ) i x edge).obj Z)).obj N) δ =
      ((SKM.homContentPreE T (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge).obj
        ((SKM.homContentPreF T (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge).obj
          (Z.comp (elvBlockEval D Sc cutoff bound Λ δ)))).obj N)
    (n : ℕ) :
    (SKM.homReservoirCap T (elvWeightSpace D Sc cutoff bound Λ) i x edge n Z).total N δ =
      eqToHom hSrc ≫ (SKM.homReservoirCap T
        (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge n
        (Z.comp (elvBlockEval D Sc cutoff bound Λ δ))).total N := by
  rw [reservoirCap_row, reservoirCap_row]
  exact reservoirRow_block D Sc cutoff bound Λ x δ (T.E i edge) (T.F i edge) Z N
    (SKM.leftAdjParity D i (-a))
    (koszulSign (SKM.leftAdjParity D i (-a)) (1 + (n : ZMod 2) * D.parity i))
    (SKM.rouquierPower (T.dot i edge) n)
    (((((T.leftAdjScalar i (-a))⁻¹ : kˣ) : k)) • T.leftCap i edge) hSrc

end Generic

section Regular

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ) (Λ : X)
  (hc : ∀ i, (probeCutoff D m i : ℤ) = D.h i Λ)
  (W : X → PiSCat.{u,u,u+1} k) (muM : X) (i : I) {muP : X}
  (h : -Λ + D.α i = -muP) (H : ProbeVacuumCap.modulePiCategory D Sc m ⟶ W muM)
local notation "T" => probeOldRouquierFamily D Sc m Λ hc
local notation "N₀" => regularProbe D Sc m Λ
local notation "Z" => preCapInput D Sc m Λ hc W muM H

/-- Every prescribed dotted reservoir cap on the regular probe is the native
`x ^ n ≫ v` through the normalized pre-cap source chart. No parity is used. -/
theorem vacuumPreReservoirCap_native (hP : 0 < probeCutoff D m i) (n : ℕ) :
    (SKM.homReservoirCap T W i muM h n Z).total N₀ ≫
      H.map (eqToHom (emptyProbe_regular D Sc m Λ)) =
    (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom ≫
      (ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D Sc m (W muM) i hP H := by
  have hd := power_square _ _ _ (vacuumPreDot_source D Sc m Λ hc W muM i h H hP) n
  rw [← cap_total_pow] at hd
  rw [SKM.homReservoirCap, Superfunctor.comp_total, Category.assoc,
    vacuumPreCounit_native D Sc m Λ hc W muM i h H hP, ← Category.assoc, hd,
    Category.assoc]

end Regular

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
