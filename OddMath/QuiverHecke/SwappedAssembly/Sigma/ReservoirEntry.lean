/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SwappingMate
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Cross
import OddMath.SKM.RouquierHomDistinctPostShift

/-! # The sideways crossing on a reservoir/reservoir path

For `i ≠ j`, the entry of the sideways crossing `σ : Eⱼ Fᵢ → Fᵢ Eⱼ` of Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, (1.11), in the swapped Hom construction,
between the summand paths with both letters on the reservoir. It is the unit of the shifted
postcomposition adjunction, the reservoir crossing `postCrossNe` and the counit; up to a sign
and the path transports this is the shifted post/post mate `homShiftedPostCrossMate`, which is
invertible for distinct colours by the multicolour relations of the reservoir.

## Main results

* `homParityShiftAdd_hom_app_comp`: the comparison `S_p S_q ≅ S_{q+p}` through the parity
  comparisons.
* `postPairIso_hom_comp`: the same for `postPairIso`.
* `postCrossCore_eq`: the reservoir crossing core is a sign times `homShiftedPostCrossing`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory

universe u

section ParityShift

variable {k : Type u} [CommRing k] {C : Type*} [Category C] [Preadditive C] [Linear k C]
  [Supercategory k C] [PiSupercategory k C]

/-- The comparison `S_p S_q ≅ S_{q+p}` followed by the parity comparison of `S_{q+p}` is
the parity comparison of `S_q` inside `S_p`, then that of `S_p`. -/
theorem homParityShiftAdd_hom_app_comp (q p : ZMod 2) (Y : C) :
    (homParityShiftAdd (k := k) (C := C) q p).hom.app Y ≫
        ((homParityShiftDatum (k := k) (C := C) (q + p)).iso Y).hom =
      (homParityShift (k := k) p).map ((homParityShiftDatum (k := k) q).iso Y).hom ≫
        ((homParityShiftDatum (k := k) p).iso Y).hom := by
  rcases (show q = 0 ∨ q = 1 by fin_cases q; exact Or.inl rfl; exact Or.inr rfl) with rfl | rfl <;>
  rcases (show p = 0 ∨ p = 1 by fin_cases p; exact Or.inl rfl; exact Or.inr rfl) with rfl | rfl
  · change 𝟙 Y ≫ 𝟙 Y = 𝟙 Y ≫ 𝟙 Y
    rfl
  · change 𝟙 _ ≫ _ = (PiSupercategory.pi (R := k)).map (𝟙 Y) ≫ _
    rw [CategoryTheory.Functor.map_id]
    rfl
  · change 𝟙 _ ≫ ((homParityShiftDatum (k := k) (C := C) 1).iso Y).hom =
      ((homParityShiftDatum (k := k) (C := C) 1).iso Y).hom ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  · change (PiSupercategory.ξ (R := k) Y).hom ≫ 𝟙 Y = _
    rw [Category.comp_id]
    rfl

end ParityShift

section PostPair

variable {k : Type u} [CommRing k] {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {x a b c : B}

/-- `postPairIso` through the parity comparisons. -/
theorem postPairIso_hom_comp (Ei : b ⟶ c) (Z : x ⟶ a) (Ej : a ⟶ b) (κi κj : ZMod 2) :
    (ProbeReservoir.postPairIso (k := k) Ei Z Ej κi κj).hom ≫
        ((homParityShiftDatum (k := k) (κj + κi)).iso ((Z ≫ Ej) ≫ Ei)).hom =
      (homParityShift (k := k) κi).map (((homParityShiftDatum (k := k) κj).iso (Z ≫ Ej)).hom ▷ Ei) ≫
        ((homParityShiftDatum (k := k) κi).iso ((Z ≫ Ej) ≫ Ei)).hom := by
  simp only [ProbeReservoir.postPairIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom, Category.assoc]
  rw [homParityShiftAdd_hom_app_comp, homParityShiftCommute_inv_app, ← Functor.map_comp_assoc,
    Category.assoc]
  erw [Iso.inv_hom_id]
  rw [Category.comp_id]
  rfl

/-- The inverse of `postPairIso` through the parity comparisons. -/
theorem postPairIso_inv_eq (Ei : b ⟶ c) (Z : x ⟶ a) (Ej : a ⟶ b) (κi κj : ZMod 2) :
    (ProbeReservoir.postPairIso (k := k) Ei Z Ej κi κj).inv =
      ((homParityShiftDatum (k := k) (κj + κi)).iso ((Z ≫ Ej) ≫ Ei)).hom ≫
        ((homParityShiftDatum (k := k) κi).iso ((Z ≫ Ej) ≫ Ei)).inv ≫
        (homParityShift (k := k) κi).map
          (((homParityShiftDatum (k := k) κj).iso (Z ≫ Ej)).inv ▷ Ei) := by
  rw [← cancel_epi (ProbeReservoir.postPairIso (k := k) Ei Z Ej κi κj).hom, Iso.hom_inv_id,
    reassoc_of% (postPairIso_hom_comp Ei Z Ej κi κj), Iso.hom_inv_id_assoc, ← Functor.map_comp,
    ← TwoSupercategory.comp_whiskerRight (R := k), Iso.hom_inv_id,
    TwoSupercategory.id_whiskerRight (R := k), CategoryTheory.Functor.map_id]

omit [TwoSupercategory k B] in
/-- Conjugating a homogeneous map by the parity comparison of `S_s`, across an equality of
shifts, gives a sign. -/
theorem datum_conj_assoc {Y Y' Y'' : x ⟶ c} (s s' : ZMod 2) (hs : s = s') {r : ZMod 2}
    (g : Y ⟶ Y') (hg : g ∈ parity (R := k) _ _ r)
    (e : (homParityShift (k := k) s).obj Y' = (homParityShift (k := k) s').obj Y')
    (f : Y' ⟶ Y'') :
    ((homParityShiftDatum (k := k) s).iso Y).inv ≫ (homParityShift (k := k) s).map g ≫
        eqToHom e ≫ ((homParityShiftDatum (k := k) s').iso Y').hom ≫ f =
      sign k (s * r) • (g ≫ f) := by
  subst hs
  rw [eqToHom_refl, Category.id_comp, ← Category.assoc ((homParityShift (k := k) s).map g),
    (homParityShiftDatum (k := k) s).hom_naturality hg, Linear.smul_comp, Linear.comp_smul,
    Category.assoc, Iso.inv_hom_id_assoc]

/-- **The reservoir crossing core** (`postCrossNe` without its path transports) is a sign
times the shifted crossing `homShiftedPostCrossing` of the shifted post/post mate. -/
theorem postCrossCore_eq {b' : B} {Ei : b ⟶ c} {Ej : a ⟶ b} {Ei' : a ⟶ b'} {Ej' : b' ⟶ c}
    (Z : x ⟶ a) (κi κj : ZMod 2) {r : ZMod 2} (t : Ej ≫ Ei ⟶ Ei' ≫ Ej')
    (hg : ((associator Z Ej Ei).hom ≫ Z ◁ t ≫ (associator Z Ei' Ej').inv) ∈
      parity (R := k) _ _ r)
    (e : (homParityShift (k := k) (κj + κi)).obj ((Z ≫ Ei') ≫ Ej') =
      (homParityShift (k := k) (κi + κj)).obj ((Z ≫ Ei') ≫ Ej')) :
    (ProbeReservoir.postPairIso (k := k) Ei Z Ej κi κj).hom ≫
        (homParityShift (k := k) (κj + κi)).map
          ((associator Z Ej Ei).hom ≫ Z ◁ t ≫ (associator Z Ei' Ej').inv) ≫
        eqToHom e ≫ (ProbeReservoir.postPairIso (k := k) Ej' Z Ei' κj κi).inv =
      sign k ((κj + κi) * r) • homShiftedPostCrossing (k := k) κi κj t Z := by
  rw [postPairIso_inv_eq,
    show (ProbeReservoir.postPairIso (k := k) Ei Z Ej κi κj).hom =
      ((ProbeReservoir.postPairIso (k := k) Ei Z Ej κi κj).hom ≫
        ((homParityShiftDatum (k := k) (κj + κi)).iso ((Z ≫ Ej) ≫ Ei)).hom) ≫
        ((homParityShiftDatum (k := k) (κj + κi)).iso ((Z ≫ Ej) ≫ Ei)).inv by simp,
    postPairIso_hom_comp]
  simp only [Category.assoc]
  rw [datum_conj_assoc _ _ (add_comm κj κi) _ hg]
  simp only [homShiftedPostCrossing, Linear.comp_smul, Category.assoc]

end PostPair

section Entry

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir
variable {P : ProbeReservoir k B D Sc}

-- Comparisons of distinct sectors are decided on the sector expressions, not by computing with
-- finitely supported functions.
attribute [local irreducible] Finsupp.zipWith contentWeight

/-- **The sideways crossing entry on a reservoir/reservoir path is invertible.** For `i ≠ j`,
the entry of `σ : Eⱼ Fᵢ → Fᵢ Eⱼ` (Brundan–Ellis, arXiv:1701.04133v2, (1.11)) between the
paths of `Eⱼ Fᵢ` and `Fᵢ Eⱼ` with both letters on the reservoir is, up to a sign and the
path transports, the shifted post/post mate of the reservoir crossing. -/
theorem isIso_sigmaEntry_reservoir_reservoir (c : P.CrossCoeff) {i j : I} (hij : i ≠ j)
    (ν : X) {t s : Sector I} (p : SPath (wd D ν [up j, dn i]) t s)
    (q : SPath (wd D ν [dn i, up j]) t s)
    (hp : p.sides = [false, false]) (hq : q.sides = [false, false]) (Z : P.H s) :
    IsIso (P.sigmaEntry c i j ν p q Z) := by
  obtain ⟨τ₁, τ₂, hv₁, hv₂, ep, rfl⟩ := SPath.exists_eq_two p
  obtain ⟨σ₁, σ₂, hw₁, hw₂, eq, rfl⟩ := SPath.exists_eq_two q
  rw [SPath.sides_two] at hp hq
  simp only [List.cons.injEq, and_true] at hp hq
  obtain ⟨rfl, rfl⟩ := hp
  obtain ⟨rfl, rfl⟩ := hq
  subst eq
  obtain ⟨b₁, b₂⟩ := t
  have hj : 1 ≤ b₂ j := hv₁
  have hji : Finsupp.single j 1 i = 0 := Finsupp.single_eq_of_ne hij
  -- the cup
  have hR : StepValid (up i) false (nextSector (dn i) false (b₁, b₂)) := by
    simp [StepValid, nextSector]
  have e₀ : nextSector (up i) false (nextSector (dn i) false (b₁, b₂)) = (b₁, b₂) := by
    simp only [nextSector, Prod.mk.injEq, true_and]
    exact add_tsub_cancel_right b₂ _
  let qg₁ : SPath ((SKM.sig D).cod (sigL₁ (D := D) i j ν).gen) (b₁, b₂) (b₁, b₂) :=
    SPath.two false false hw₁ hR e₀
  let m₁ : SPath (sigL₁ (D := D) i j ν).cod.word (b₁, b₂) _ :=
    ((SPath.nil _).append qg₁).append (SPath.two false false hv₁ hv₂ ep)
  -- the crossing
  let t' := nextSector (dn i) false (b₁, b₂)
  have hJ : StepValid (up j) false (nextSector (up i) false t') := by
    simpa [t', StepValid, nextSector] using hj
  have hI' : StepValid (up i) false (nextSector (up j) false t') := by
    simp [t', StepValid, nextSector, hji]
  have e' : nextSector (up i) false (nextSector (up j) false t') =
      nextSector (up j) false (nextSector (up i) false t') := by
    simp only [t', nextSector, Prod.mk.injEq, true_and]
    exact tsub_right_comm
  let x := nextSector (up j) false (nextSector (up i) false t')
  have ex : nextSector (dn i) false x = nextSector (up j) false t' := by
    simp only [x, t', nextSector, Prod.mk.injEq, true_and]
    rw [add_tsub_cancel_right]
    ext l
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
    rcases eq_or_ne j l with rfl | h1
    · simp [hij]
    · simp [h1]
  let pu₂ : SPath (sigL₂ (D := D) i j ν).left (b₁, b₂) t' := .cons _ false _ hw₁ (.nil _)
  let pg₂ : SPath ((SKM.sig D).dom (sigL₂ (D := D) i j ν).gen) t' x :=
    SPath.two false false hR hJ rfl
  let qg₂ : SPath ((SKM.sig D).cod (sigL₂ (D := D) i j ν).gen) t' x :=
    SPath.two false false hw₂ hI' e'
  let pv₂ : SPath (sigL₂ (D := D) i j ν).right x (nextSector (up j) false t') :=
    .cons _ false x trivial ((SPath.nil _).castTgt ex)
  let m₂ : SPath (sigL₂ (D := D) i j ν).cod.word (b₁, b₂) _ := (pu₂.append qg₂).append pv₂
  rw [sigmaEntry_eq_sigmaTerm (m₁ := m₁) (m₂ := m₂) (p₁ := false) (p₂ := false)
    (q₁ := false) (q₂ := false) (hp := by rw [SPath.sides_two]) (hq := by rw [SPath.sides_two])
    (hm₁ := by simp [m₁, qg₁, SPath.sides_append, SPath.sides_two, SPath.sides])
    (hm₂ := by simp [m₂, pu₂, qg₂, pv₂, SPath.sides_append, SPath.sides_two, SPath.sides,
      SPath.sides_castTgt])]
  have sd := @SPath.sides_cast.{u}
  -- the cap
  let s₀ := nextSector (up j) false t'
  have hI₀ : StepValid (up i) false s₀ := by
    simp [s₀, t', StepValid, nextSector, hji]
  have e₃ : nextSector (dn i) false (nextSector (up i) false s₀) = s₀ := by
    simp only [s₀, nextSector, Prod.mk.injEq, true_and]
    refine tsub_add_cancel_of_le (Finsupp.single_le_iff.2 ?_)
    exact hI₀
  let pu₃ : SPath (sigL₃ (D := D) i j ν).left (b₁, b₂) s₀ :=
    .cons _ false _ hw₁ (.cons _ false _ hw₂ (.nil _))
  let pg₃ : SPath ((SKM.sig D).dom (sigL₃ (D := D) i j ν).gen) s₀ s₀ :=
    SPath.two false false hI₀ trivial e₃
  rw [sigmaTerm_eq_of_paths _ i j ν _ _ m₁ m₂ (SPath.nil _) (SPath.nil _) qg₁
      (SPath.two false false hv₁ hv₂ ep)
      (SPath.eq_of_sides _ _ (by simp [SPath.sides_append, SPath.sides_two, SPath.sides]))
      (SPath.eq_of_sides _ _ (by simp [m₁, qg₁, SPath.sides_append, SPath.sides_two, SPath.sides]))
      pu₂ pg₂ qg₂ pv₂
      (SPath.eq_of_sides _ _ (by
        simp [m₁, qg₁, pu₂, pg₂, pv₂, SPath.sides_append, SPath.sides_two, SPath.sides,
          SPath.sides_castTgt]))
      (SPath.eq_of_sides _ _ (by
        simp [m₂, pu₂, qg₂, pv₂, SPath.sides_append, SPath.sides_two, SPath.sides,
          SPath.sides_castTgt]))
      pu₃ pg₃ (SPath.nil s₀) (SPath.nil s₀)
      (SPath.eq_of_sides _ _ (by
        simp [m₂, pu₂, qg₂, pv₂, pu₃, pg₃, sd, SPath.sides_append, SPath.sides_two, SPath.sides,
          SPath.sides_castTgt]))
      (SPath.eq_of_sides _ _ (by simp [pu₃, sd, SPath.sides_append, SPath.sides_two, SPath.sides]))]
  simp only [upwardGens, Generators.image, sigL₁, sigL₂, sigL₃, SKM.lay, crossImage,
    dite_eq_right hij, cupImage, capImage]
  rw [twoTwo_two (Z' := e'.symm ▸ _) (hZ := eqRec_heq _ _)]
  rw [zeroTwo_two (Z' := e₀.symm ▸ _) (hZ := eqRec_heq _ _)]
  rw [twoZero_two (Z' := e₃.symm ▸ _) (hZ := eqRec_heq _ _)]
  simp only [cupEntry, capEntry, crossNeEntry, postCup, postCap, postCrossNe]
  simp only [pu₂, pu₃, pathFunctor_cons, pathFunctor_nil, Functor.comp_map, Functor.id_map]
  simp only [Category.assoc, eqToHom_map, Functor.map_comp, eqToHom_trans, eqToHom_trans_assoc]
  done

end ProbeReservoir

end Entry

end OddMath.QuiverHecke.SwappedAssembly
