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

private theorem total_pow_square {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F : Superfunctor k C A} (f : End F) (N : C) {B : A} (e : F.obj N ⟶ B) (y : End B)
    (h : f.total N ≫ e = e ≫ y) (n : ℕ) :
    (f ^ n).total N ≫ e = e ≫ (y ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, End.one_def, End.one_def]
    change (capTotalEvaluation N).map (𝟙 F) ≫ e = e ≫ 𝟙 B
    rw [Functor.map_id, Category.id_comp, Category.comp_id]
  | succ n ih =>
    rw [pow_succ, pow_succ, End.mul_def, End.mul_def]
    change (capTotalEvaluation N).map (f ≫ f ^ n) ≫ e = e ≫ y ≫ y ^ n
    rw [Functor.map_comp, Category.assoc]
    change f.total N ≫ (f ^ n).total N ≫ e = _
    rw [ih, ← Category.assoc, h, Category.assoc]

/-- Chart bookkeeping for a cap row: a pulled-back square, a block
selection and a normalized native identity compose. -/
private theorem cap_charts_attach {C : Type*} [Category C]
    {A X U U₀ U' Y V V' : C} (s : A ≅ X) (u : X ≅ U) (hU : U = U₀) (e : U₀ ≅ U')
    (c : X ⟶ Y) (p : Y ⟶ V) (q : V ⟶ V') (c₀ : U ⟶ V) (c₁ : U₀ ⟶ V) (d : U' ⟶ V')
    (hsq : c ≫ p = u.hom ≫ c₀) (hE : c₀ = eqToHom hU ≫ c₁) (hn : c₁ ≫ q = e.hom ≫ d) :
    (s.hom ≫ c) ≫ p ≫ q = (s ≪≫ u ≪≫ (eqToIso hU ≪≫ e)).hom ≫ d := by
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc]
  rw [reassoc_of% hsq, hE, Category.assoc, hn]

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
  rw [SKM.homReservoirCap, Superfunctor.comp_total, Category.assoc,
    vacuumPreCounit_native D Sc m Λ hc W muM i h H hP, ← Category.assoc,
    total_pow_square _ _ _ _ (vacuumPreDot_source D Sc m Λ hc W muM i h H hP) n,
    Category.assoc]

end Regular

section Pullback

variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : SKM.Datum I X}
  (T W : SKM.RouquierFamily (k := k) (B := B) D)
  {a a' b b' : X} (ha : a = a') (hb : b = b')
  (Z' : SKM.homWeightSector T.obj W.obj a' b')

/-- A pulled-back input returns to itself under the weight equivalence. -/
def capPullbackSelfIso :
    (SKM.homWeightEquivalence T W ha hb).functor.obj
      ((SKM.homWeightEquivalence T W ha hb).inverse.obj Z') ≅ Z' := by
  subst a'
  subst b'
  exact Iso.refl _

/-- The dotted reservoir cap on a pulled-back input is the cap on the
normalized input, through the source pullback chart and the return chart. -/
theorem homReservoirCap_weight_pullback_square (i : I) {c : X}
    (hp : -a + D.α i = -c) (n : ℕ) :
    (SKM.homWeightEquivalence T W ha hb).functor.map
        (SKM.homReservoirCap T W.obj i b hp n
          ((SKM.homWeightEquivalence T W ha hb).inverse.obj Z')) ≫
      (capPullbackSelfIso T W ha hb Z').hom =
    (SKM.homPreWeightPullbackIso T W ha hb i hp Z').hom ≫
      SKM.homReservoirCap T W.obj i b' (show -a' + D.α i = -c from ha ▸ hp) n Z' := by
  subst a'
  subst b'
  change SKM.homReservoirCap T W.obj i b hp n Z' ≫ 𝟙 _ =
    𝟙 _ ≫ SKM.homReservoirCap T W.obj i b hp n Z'
  simp only [Category.comp_id, Category.id_comp]

end Pullback

section Padded

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

omit [Fintype I] in
private instance paddedCapZero (β : Multiset I) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff bound β) :=
  ⟨⟨elvZeroModule D (parameterTwist D Sc) cutoff bound β,
    elvZeroModule_isZero D (parameterTwist D Sc) cutoff bound β⟩⟩

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR

omit [Fintype I] in
private theorem capProbeWeight_zero : (P).muP (((0, 0) : Sector I)) = ΛP := by
  simp [ProbeReservoir.muP, elvProbeReservoir]
omit [Fintype I] in
private theorem capReservoirWeight_zero : (P).muM (((0, 0) : Sector I)) = -ΛR := by
  simp [ProbeReservoir.muM, elvProbeReservoir]

private def capVacuumEvaluation :
    SKM.homWeightSector (P).T.obj (P).W.obj ΛP (-ΛR) ⥤
      ContentModules D (parameterTwist D Sc) cutoff bound (0 : Multiset I) :=
  homContentEvaluation D (parameterTwist D Sc) cutoff bound ΛR (-ΛR)
    ((P).T.obj (-ΛP)) (regularProbe D (parameterTwist D Sc) m ΛP) (emptyBlock D ΛR)

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))

/-- The cap target comparison: return the pulled-back vacuum input to the
normalized input, then apply the regular-input chart of the output block. -/
def paddedVacuumCapTargetIso :=
  (capVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).mapIso
      (capPullbackSelfIso (P).T (P).W
        (capProbeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR)
        (capReservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR)
        (preCapInput D (parameterTwist D Sc) m ΛP hcP
          (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H)) ≪≫
    (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).toFunctor.mapIso
      (eqToIso (emptyProbe_regular D (parameterTwist D Sc) m ΛP))

/-- The prescribed padded reservoir cap row `n` at the vacuum sector is the
native `x ^ n ≫ v` of the output block, through the same source chart as the
padded Dx entry. No parity, moment or cap compatibility is assumed. -/
theorem paddedVacuumCap_native (i : I) (hP : 0 < probeCutoff D m i) (n : ℕ) :
    (P).centralPaddedCap i (((0, 0) : Sector I))
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true n ≫
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom =
    (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom ≫
      (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := by
  classical
  let E₀ := capVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let Z₀ := preCapInput D (parameterTwist D Sc) m ΛP hcP
    (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H
  let ha := capProbeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let hb := capReservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let ep := (P).muP_preE i (0, 0)
  let ep₀ : -ΛP + D.α i = -(P).muP (nextSector (true, i) true (((0, 0) : Sector I))) :=
    (congrArg (fun x : X => -x + D.α i) ha).symm.trans ep
  have hsq := congrArg E₀.map
    (homReservoirCap_weight_pullback_square (P).T (P).W ha hb Z₀ i ep n)
  rw [Functor.map_comp, Functor.map_comp] at hsq
  have hSrc : (((SKM.homContentPreE (P).T (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR)
        i (-ΛR) ep₀).obj ((SKM.homContentPreF (P).T
          (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) i (-ΛR) ep₀).obj Z₀)).obj
        (regularProbe D (parameterTwist D Sc) m ΛP)) (emptyBlock D ΛR) =
      ((SKM.homContentPreE (P).T
          (fun _ => contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I))
          i (-ΛR) ep₀).obj ((SKM.homContentPreF (P).T
          (fun _ => contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I))
          i (-ΛR) ep₀).obj
            (preCapInput D (parameterTwist D Sc) m ΛP hcP
              (fun _ => contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I))
              (-ΛR) (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H)))).obj
        (regularProbe D (parameterTwist D Sc) m ΛP) := by
    simp only [SKM.homContentPreF, Functor.comp_obj, SKM.homParityShift]
    split_ifs <;> rfl
  have hb₀ := reservoirCap_block D (parameterTwist D Sc) cutoff bound ΛR (-ΛR) (emptyBlock D ΛR)
    (P).T i ep₀ Z₀ (regularProbe D (parameterTwist D Sc) m ΛP) hSrc n
  have hn := vacuumPreReservoirCap_native D (parameterTwist D Sc) m ΛP hcP
    (fun _ => contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I))
    (-ΛR) i ep₀ (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) hP n
  have hE : E₀.map (SKM.homReservoirCap (P).T (P).W.obj i (-ΛR) ep₀ n Z₀) =
      eqToHom hSrc ≫ (SKM.homReservoirCap (probeOldRouquierFamily D (parameterTwist D Sc) m ΛP hcP)
        (fun _ => contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I))
        i (-ΛR) ep₀ n
        (preCapInput D (parameterTwist D Sc) m ΛP hcP
          (fun _ => contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I))
          (-ΛR) (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))).total
          (regularProbe D (parameterTwist D Sc) m ΛP) :=
    hb₀
  have hcap : (P).centralPaddedCap i (((0, 0) : Sector I))
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true n =
      ((P).centralSourceCornerIso i (0, 0)
          (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
          (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) ⟨true, by trivial⟩).hom ≫
        E₀.map ((SKM.homWeightEquivalence (P).T (P).W ha hb).functor.map
          (SKM.homReservoirCap (P).T (P).W.obj i ((P).muM (0, 0)) ep n
            ((SKM.homWeightEquivalence (P).T (P).W ha hb).inverse.obj Z₀))) := by
    unfold ProbeReservoir.centralPaddedCap
    rw [dif_pos (show StepValid (up i) true (((0, 0) : Sector I)) from by trivial)]
    rfl
  rw [hcap]
  exact cap_charts_attach _ _ hSrc _ _ _ _ _ _ _ hsq hE hn
end Padded

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
