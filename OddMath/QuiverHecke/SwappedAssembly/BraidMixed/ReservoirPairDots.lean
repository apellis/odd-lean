/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ProbePairQCentrality
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ReservoirPairSector

/-! Signed dots and slides on the two-reservoir path `PᵢRᵣRᵣ`.
These use the prescribed shifted reservoir crossing. -/
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
variable (i r : I) (t : Sector I) (hv : StepValid (true, r) false t)
  (hw : StepValid (true, r) false (nextSector (true, r) false t))
  (Z : P.H (nextSector (true, r) false (nextSector (true, r) false
    (nextSector (true, i) true t))))

/-- The last reservoir letter of the path `PᵢRᵣRᵣ`, applied to `Z`. -/
abbrev reservoirPairRest : P.H (nextSector (true, r) false (nextSector (true, i) true t)) :=
  (P.step (true, r) false (nextSector (true, r) false (nextSector (true, i) true t)) hw).obj Z

/-- The object of the first path `PRR`. -/
abbrev reservoirPairObj : P.H t := P.prObj i r t hv (P.reservoirPairRest i r t hw Z)

/-- The interchange `Φ₁ = J` from the path `PRR` to the path `RPR` of `Eᵢ Eᵣ Eᵣ`. -/
def reservoirPairFirstIso : P.reservoirPairObj i r t hv hw Z ≅ P.rpObj r i t hv (P.reservoirPairRest i r t hw Z) :=
  P.mixedJ i r t hv (P.reservoirPairRest i r t hw Z)

/-- The reservoir dot `z` on the last letter of the path `PRR`. -/
def reservoirPairLastDot : End (P.reservoirPairObj i r t hv hw Z) :=
  (P.step (true, i) true t trivial).map (P.rrRightDot r (nextSector (true, i) true t) hv hw Z)

/-- The reservoir crossing `D` of the two right letters of the path `PRR`. -/
def reservoirPairCross : End (P.reservoirPairObj i r t hv hw Z) :=
  (P.step (true, i) true t trivial).map (P.postCrossSame r (nextSector (true, i) true t) hv hw Z)

/-- The reservoir dot `z` passes through `Φ₁` with the colour sign, by supernaturality of the
mixed interchange. -/
theorem reservoirPairLastDot_comp_reservoirPairFirstIso :
    P.reservoirPairLastDot i r t hv hw Z ≫ (P.reservoirPairFirstIso i r t hv hw Z).hom =
      koszulSign (D.parity i * D.parity r) (D.parity r) • ((P.reservoirPairFirstIso i r t hv hw Z).hom ≫
        (P.step (true, r) false t hv).map
          (P.prPostDot i r (nextSector (true, r) false t) hw Z)) := by
  have hθ := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W r
    (nextSector (true, r) false (nextSector (true, i) true t)).1
    (P.muP (nextSector (true, r) false (nextSector (true, i) true t)))
    (P.muM_postE (t := nextSector (true, r) false (nextSector (true, i) true t)) r hw) 1).mem Z
  simp only [Nat.cast_one, one_mul, pow_one] at hθ
  have h₀ := (P.mixedJ_supernatural i r t hv).naturality hθ
  rw [← koszulSign_smul (R := k)] at h₀
  exact h₀

/-- Conjugation by `Φ₁` carries the last reservoir dot with sign `(-1)^(pᵢpᵣ)`. -/
theorem reservoirPairFirstIso_conj_map_prPostDot :
    (P.reservoirPairFirstIso i r t hv hw Z).hom ≫
        (P.step (true, r) false t hv).map (P.prPostDot i r (nextSector (true, r) false t) hw Z) ≫
        (P.reservoirPairFirstIso i r t hv hw Z).inv =
      koszulSign (D.parity i * D.parity r) (D.parity r) • P.reservoirPairLastDot i r t hv hw Z := by
  have h := congrArg (· ≫ (P.reservoirPairFirstIso i r t hv hw Z).inv)
    (P.reservoirPairLastDot_comp_reservoirPairFirstIso i r t hv hw Z)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Linear.smul_comp] at h
  rw [h, smul_smul, koszulSign_mul_self, one_smul]


private theorem reservoirPair_flip_sign {C : Type*} [Category C] [Preadditive C]
    {A : C} (p q : ZMod 2) {a b : A ⟶ A}
    (h : a = koszulSign p q • b) : b = koszulSign p q • a := by
  rw [h, smul_smul, koszulSign_mul_self, one_smul]

/-- The probe dot of `PRR` supercommutes with any homogeneous endomorphism of parity `p` of
the two right letters. -/
private theorem reservoirPairPreDot_comp_map {Y Y' : P.H (nextSector (true, i) true t)} {p : ZMod 2}
    (θ : Y ⟶ Y') (hθ : θ ∈ parity (R := k) _ _ p) :
    P.T.dot i (P.muP_preE i t) ▷ Y ≫ (P.step (true, i) true t trivial).map θ =
      koszulSign (D.parity i) p •
        ((P.step (true, i) true t trivial).map θ ≫ P.T.dot i (P.muP_preE i t) ▷ Y') :=
  TwoSupercategory.super_interchange (R := k) (P.T.dot_mem i _) hθ

/-- The reservoir dot `y` and the probe dot `x` of `PRR` supercommute. -/
theorem reservoirPairFirstDot_comp_probeDot :
    P.prPostDot i r t hv (P.reservoirPairRest i r t hw Z) ≫ P.prPreDot i r t hv (P.reservoirPairRest i r t hw Z) =
      koszulSign (D.parity i) (D.parity r) •
        (P.prPreDot i r t hv (P.reservoirPairRest i r t hw Z) ≫
          P.prPostDot i r t hv (P.reservoirPairRest i r t hw Z)) := by
  have hθ := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W r
    (nextSector (true, i) true t).1 (P.muP (nextSector (true, i) true t))
    (P.muM_postE (t := nextSector (true, i) true t) r hv) 1).mem (P.reservoirPairRest i r t hw Z)
  simp only [Nat.cast_one, one_mul, pow_one] at hθ
  exact reservoirPair_flip_sign _ _ (P.reservoirPairPreDot_comp_map i t _ hθ)

/-- The reservoir dot `z` and the probe dot `x` of `PRR` supercommute. -/
theorem reservoirPairLastDot_comp_prPreDot :
    P.reservoirPairLastDot i r t hv hw Z ≫ P.prPreDot i r t hv (P.reservoirPairRest i r t hw Z) =
      koszulSign (D.parity i) (D.parity r) •
        (P.prPreDot i r t hv (P.reservoirPairRest i r t hw Z) ≫ P.reservoirPairLastDot i r t hv hw Z) := by
  have hθ := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W r
    (nextSector (true, r) false (nextSector (true, i) true t)).1
    (P.muP (nextSector (true, r) false (nextSector (true, i) true t)))
    (P.muM_postE (t := nextSector (true, r) false (nextSector (true, i) true t)) r hw) 1).mem Z
  simp only [Nat.cast_one, one_mul, pow_one] at hθ
  have hθ' := IsSuperfunctor.map_mem (R := k)
    (F := P.step (true, r) false (nextSector (true, i) true t) hv) hθ
  exact reservoirPair_flip_sign _ _ (P.reservoirPairPreDot_comp_map i t _ hθ')

/-- The reservoir crossing `D` and the probe dot `x` of `PRR` supercommute. -/
theorem reservoirPairCross_comp_prPreDot :
    P.reservoirPairCross i r t hv hw Z ≫ P.prPreDot i r t hv (P.reservoirPairRest i r t hw Z) =
      koszulSign (D.parity i) (D.parity r) •
        (P.prPreDot i r t hv (P.reservoirPairRest i r t hw Z) ≫ P.reservoirPairCross i r t hv hw Z) := by
  have hθ := (P.postCrossSame_supernatural r (nextSector (true, i) true t) hv hw).mem Z
  have h := P.reservoirPairPreDot_comp_map i t _ hθ
  rw [SKM.zmod2_mul_self] at h
  exact reservoirPair_flip_sign _ _ h

/-- The two reservoir dots `z`, `y` of `PRR` supercommute. -/
theorem reservoirPairLastDot_comp_prPostDot :
    P.reservoirPairLastDot i r t hv hw Z ≫ P.prPostDot i r t hv (P.reservoirPairRest i r t hw Z) =
      koszulSign (D.parity r) (D.parity r) •
        (P.prPostDot i r t hv (P.reservoirPairRest i r t hw Z) ≫ P.reservoirPairLastDot i r t hv hw Z) := by
  have hθ := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W r
    (nextSector (true, r) false (nextSector (true, i) true t)).1
    (P.muP (nextSector (true, r) false (nextSector (true, i) true t)))
    (P.muM_postE (t := nextSector (true, r) false (nextSector (true, i) true t)) r hw) 1).mem Z
  simp only [Nat.cast_one, one_mul, pow_one] at hθ
  have hx := homContentPostDot_power_supernatural (k := k) P.T.obj P.W r
    (nextSector (true, i) true t).1 (P.muP (nextSector (true, i) true t))
    (P.muM_postE (t := nextSector (true, i) true t) r hv) 1
  simp only [Nat.cast_one, one_mul, pow_one] at hx
  have h₀ := hx.naturality hθ
  rw [← koszulSign_smul (R := k)] at h₀
  have h' := congrArg (P.step (true, i) true t trivial).map h₀
  simp only [Functor.map_comp, Functor.map_zsmul] at h'
  exact h'

/-- `D² = 0` on `PRR`. -/
theorem reservoirPairCross_sq : P.reservoirPairCross i r t hv hw Z ≫ P.reservoirPairCross i r t hv hw Z = 0 := by
  rw [reservoirPairCross, ← Functor.map_comp, P.postCrossSame_sq, Functor.map_zero]

/-- **The slides of `D` past the reservoir dots** `y`, `z` of `PRR`. -/
theorem reservoirPairCross_slides :
    (P.prPostDot i r t hv (P.reservoirPairRest i r t hw Z) ≫ P.reservoirPairCross i r t hv hw Z -
        koszulSign (D.parity r) (D.parity r) •
          (P.reservoirPairCross i r t hv hw Z ≫ P.reservoirPairLastDot i r t hv hw Z) = 𝟙 _) ∧
    (P.reservoirPairCross i r t hv hw Z ≫ P.prPostDot i r t hv (P.reservoirPairRest i r t hw Z) -
        koszulSign (D.parity r) (D.parity r) •
          (P.reservoirPairLastDot i r t hv hw Z ≫ P.reservoirPairCross i r t hv hw Z) = 𝟙 _) := by
  obtain ⟨h₁, h₂⟩ := P.postCrossSame_slides r (nextSector (true, i) true t) hv hw Z
  have h₁' := congrArg (P.step (true, i) true t trivial).map h₁
  have h₂' := congrArg (P.step (true, i) true t trivial).map h₂
  simp only [Functor.map_sub, Functor.map_comp, Functor.map_zsmul] at h₁' h₂'
  exact ⟨h₁'.trans (CategoryTheory.Functor.map_id _ _),
    h₂'.trans (CategoryTheory.Functor.map_id _ _)⟩


/-- Both signs disappear on the separately supported powers of Q. -/
theorem reservoirPairFirstIso_conj_mixedQ :
    (P.reservoirPairFirstIso i r t hv hw Z).hom ≫
      (P.step (true, r) false t hv).map
        (P.mixedQ i r (nextSector (true, r) false t) hw Z) ≫
      (P.reservoirPairFirstIso i r t hv hw Z).inv =
    qExpr Sc (P.prPreDot i r t hv (P.reservoirPairRest i r t hw Z))
      (P.reservoirPairLastDot i r t hv hw Z) i r := by
  let J := P.reservoirPairFirstIso i r t hv hw Z
  let ε := zsign k (D.parity i * D.parity r)
  have hx := P.prPreDot_comp_mixedJ_ne i r t hv (P.reservoirPairRest i r t hw Z)
  have hx' := congrArg (fun f => ε • f) hx
  simp only [ε, smul_smul, zsign_mul_self', one_smul] at hx'
  have hy := P.reservoirPairLastDot_comp_reservoirPairFirstIso i r t hv hw Z
  rw [koszulSign_smul_eq_zsign (k := k), mul_assoc, SKM.zmod2_mul_self] at hy
  have hy' := congrArg (fun f => ε • f) hy
  simp only [ε, smul_smul, zsign_mul_self', one_smul] at hy'
  have hmap : (P.step (true, r) false t hv).map
      (P.mixedQ i r (nextSector (true, r) false t) hw Z) =
      qExpr Sc ((P.step (true, r) false t hv).map
        (P.prPreDot i r (nextSector (true, r) false t) hw Z))
        ((P.step (true, r) false t hv).map
        (P.prPostDot i r (nextSector (true, r) false t) hw Z)) i r :=
    qExpr_map Sc (functorAlg (k := k) (P.step (true, r) false t hv) _) _ _ i r
  rw [hmap]
  have hQ := comp_qExpr (Sc := Sc) J.hom _ _ _ _ i r ε ε hx'.symm hy'.symm
    (fun n hn => zsign_pow_of_mul_eq_zero _ _ n hn)
    (fun n hn => by
      change zsign k (D.parity i * D.parity r) ^ n = 1
      rw [mul_comm]
      exact zsign_pow_of_mul_eq_zero _ _ n hn)
  have h := congrArg (fun f => f ≫ J.inv) hQ
  have hpre : (P.step (true, r) false t hv).map
      (P.T.dot i (P.muP_preE i t) ▷ P.reservoirPairRest i r t hw Z) =
      (P.step (true, r) false t hv).map
        (P.prPreDot i r (nextSector (true, r) false t) hw Z) := by
    rfl
  rw [hpre] at h
  simpa only [J, Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
