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
(`paddedVacuumCap_eq`). No parity, moment or cap compatibility is
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

private theorem total_pow_square {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F : Superfunctor k C A} (f : End F) (N : C) {B : A} (e : F.obj N ⟶ B) (y : End B)
    (h : f.total N ≫ e = e ≫ y) (n : ℕ) :
    (f ^ n).total N ≫ e = e ≫ (y ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, End.one_def, End.one_def]
    exact (congrArg (fun w => w ≫ e) (SuperNatTrans.id_total F.toFunctor N)).trans
      ((Category.id_comp e).trans (Category.comp_id e).symm)
  | succ n ih =>
    rw [pow_succ, pow_succ, End.mul_def, End.mul_def, Superfunctor.comp_total,
      Category.assoc, ih, ← Category.assoc, h, Category.assoc]

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
theorem vacuumPreReservoirCap_eq (hP : 0 < probeCutoff D m i) (n : ℕ) :
    (SKM.homReservoirCap T W i muM h n Z).total N₀ ≫
      H.map (eqToHom (emptyProbe_regular D Sc m Λ)) =
    (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom ≫
      (ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D Sc m (W muM) i hP H := by
  rw [SKM.homReservoirCap, Superfunctor.comp_total, Category.assoc,
    vacuumPreCounit_eq D Sc m Λ hc W muM i h H hP, ← Category.assoc,
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
theorem paddedVacuumCap_eq (i : I) (hP : 0 < probeCutoff D m i) (n : ℕ) :
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
  let PR := elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
  let E₀ := capVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let Z := vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H
  let E := vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let Z₀ := preCapInput D (parameterTwist D Sc) m ΛP hcP
    (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H
  let ha := capProbeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let hb := capReservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let ep := PR.muP_preE i (0, 0)
  let ep₀ : -ΛP + D.α i = -PR.muP (nextSector (true, i) true (((0, 0) : Sector I))) :=
    (congrArg (fun x : X => -x + D.α i) ha).symm.trans ep
  let B₀ := vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H
  let W₀ : X → PiSCat.{u,u,u+1} k :=
    fun _ => contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)
  let N₀ := regularProbe D (parameterTwist D Sc) m ΛP
  let s := PR.centralSourceCornerIso i (0, 0) Z E ⟨true, by trivial⟩
  let u := E₀.mapIso (SKM.homPreWeightPullbackIso PR.T PR.W ha hb i ep Z₀)
  let e := vacuumPreSourceIso D (parameterTwist D Sc) m ΛP hcP W₀ (-ΛR) i ep₀ B₀
  let c := E₀.map ((SKM.homWeightEquivalence PR.T PR.W ha hb).functor.map
    (SKM.homReservoirCap PR.T PR.W.obj i (PR.muM (0, 0)) ep n
      ((SKM.homWeightEquivalence PR.T PR.W ha hb).inverse.obj Z₀)))
  let p := E₀.map (capPullbackSelfIso PR.T PR.W ha hb Z₀).hom
  let q := B₀.toFunctor.map (eqToHom (emptyProbe_regular D (parameterTwist D Sc) m ΛP))
  let c₀ := E₀.map (SKM.homReservoirCap PR.T PR.W.obj i (-ΛR) ep₀ n Z₀)
  let c₁ := (SKM.homReservoirCap (probeOldRouquierFamily D (parameterTwist D Sc) m ΛP hcP)
    W₀ i (-ΛR) ep₀ n (preCapInput D (parameterTwist D Sc) m ΛP hcP W₀ (-ΛR) B₀)).total N₀
  let d := (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
      (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i B₀ ^ n) ≫
    ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
      (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP B₀
  have hsq : c ≫ p = u.hom ≫ c₀ := by
    have h := congrArg E₀.map
      (homReservoirCap_weight_pullback_square PR.T PR.W ha hb Z₀ i ep n)
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h
  have hSrc : (((SKM.homContentPreE PR.T (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR)
        i (-ΛR) ep₀).obj ((SKM.homContentPreF PR.T
          (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) i (-ΛR) ep₀).obj Z₀)).obj
        N₀) (emptyBlock D ΛR) =
      ((SKM.homContentPreE PR.T W₀ i (-ΛR) ep₀).obj ((SKM.homContentPreF PR.T W₀ i (-ΛR) ep₀).obj
            (preCapInput D (parameterTwist D Sc) m ΛP hcP W₀ (-ΛR) B₀))).obj N₀ := by
    simp only [SKM.homContentPreF, Functor.comp_obj, SKM.homParityShift]
    split_ifs <;> rfl
  have hE0 := reservoirCap_block D (parameterTwist D Sc) cutoff bound ΛR (-ΛR) (emptyBlock D ΛR)
      PR.T i ep₀ Z₀ N₀ hSrc n
  have hc₀ : c₀ = (SKM.homReservoirCap PR.T PR.W.obj
      i (-ΛR) ep₀ n Z₀).total N₀ (emptyBlock D ΛR) := by
    simp only [c₀, E₀, N₀, capVacuumEvaluation, homContentEvaluation, Functor.comp_map,
      Pi.eval_map, homTotalEvaluation]
  have hc₁ : (SKM.homReservoirCap PR.T
        (fun _ => contentModuleTarget D (parameterTwist D Sc) cutoff bound (emptyBlock D ΛR).1)
        i (-ΛR) ep₀ n
        (Z₀.comp (elvBlockEval D (parameterTwist D Sc) cutoff bound ΛR (emptyBlock D ΛR)))).total N₀
      = c₁ := rfl
  have hE : c₀ = eqToHom hSrc ≫ c₁ := by
    rw [hc₀, ← hc₁]
    exact hE0
  have hn : c₁ ≫ q = e.hom ≫ d :=
    vacuumPreReservoirCap_eq D (parameterTwist D Sc) m ΛP hcP W₀ (-ΛR) i ep₀ B₀ hP n
  have hs := cap_charts_attach s u hSrc e c p q c₀ c₁ d hsq hE hn
  have hcap : PR.centralPaddedCap i (((0, 0) : Sector I)) Z E true n = s.hom ≫ c := by
    unfold ProbeReservoir.centralPaddedCap
    rw [dite_eq_left_of_eq_true (eq_true (show StepValid (SKM.up i) true (((0, 0) : Sector I)) from
      by trivial))]
    rfl
  have hsrc : (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      (s ≪≫ u ≪≫ (eqToIso hSrc ≪≫ e)).hom := rfl
  have htgt : (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom = p ≫ q := rfl
  rw [hcap, htgt, hsrc]
  exact hs
end Padded

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
