/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterCoordinates
import OddMath.QuiverHecke.SwappedAssembly.QuadNe

/-! # The repeated-outer raw diagonal

For `Rᵢ Pⱼ Pᵢ`, the mixed Q conjugation and the actual two probe crossings
identify the two Q polynomials in the separated coordinates. The coefficient
commutes with the latter polynomial by its inverse identities and the parity
support of Q. Thus the raw three-crossing difference is the two signed sums.
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
  (i j : I) (s : Sector I) (hR : StepValid (true, i) false s)
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

private lemma coefficient_alg_commute (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (t : Sector I) (hv : StepValid (true, i) false t)
    (V : P.H (nextSector (true, i) true (nextSector (true, i) false t)))
    {C : Type u} [Category C] [Preadditive C] [Linear k C] {Y : C}
    (φ : End (P.rpObj i i t hv V) →ₐ[k] End Y) (f : End Y)
    (hx : φ (P.rpPreDot i t hv V) ≫ f = f ≫ φ (P.rpPreDot i t hv V))
    (hy : φ (P.rpPostDot i t hv V) ≫ f = f ≫ φ (P.rpPostDot i t hv V)) :
    φ (c.a i t hv V) ≫ f = f ≫ φ (c.a i t hv V) := by
  have hmap (a b : End (P.rpObj i i t hv V)) : φ (a ≫ b) = φ a ≫ φ b :=
    φ.map_mul b a
  by_cases hi : D.parity i = 0
  · have ha := congrArg φ (hc.even i hi t hv V).1
    have hb := congrArg φ (hc.even i hi t hv V).2
    simp only [hmap, map_sub, show φ (𝟙 _) = 𝟙 _ from φ.map_one] at ha hb
    simpa only [one_smul] using signed_inverse_difference_transport
      _ _ _ _ _ _ f (1 : k) (one_mul _) (hx.trans (one_smul _ _).symm)
      (hy.trans (one_smul _ _).symm) ha hb
  · have hi' := (Supercategory.parity_eq_zero_or_one (D.parity i)).resolve_left hi
    have ha := congrArg φ (hc.odd i hi' t hv V).1
    simp only [hmap, map_sub] at ha
    have hd : (P.crossDenom h i t hv V : End (P.rpObj i i t hv V)) =
        P.rpPreDot i t hv V ≫ P.rpPreDot i t hv V -
          P.rpPostDot i t hv V ≫ P.rpPostDot i t hv V := by
      simp [crossDenom, hi, sub_eq_add_neg, add_comm, pow_two, End.mul_def]
    have hd' := congrArg φ hd
    simp only [hmap, map_sub] at hd'
    simpa only [one_smul] using signed_odd_coefficient_transport
      _ _ _ _ _ _ f (1 : k) (one_mul _) (hx.trans (one_smul _ _).symm)
      (hy.trans (one_smul _ _).symm) ha ha
      (Units.map φ.toMonoidHom (P.crossDenom h i t hv V)) hd'

lemma repeatedOuterX_mul_Y :
    P.repeatedOuterX i j s hR hs Z * P.repeatedOuterY i j s hR hs Z =
      zsign k (D.parity i * D.parity j) •
        (P.repeatedOuterY i j s hR hs Z * P.repeatedOuterX i j s hR hs Z) := by
  have he := homMixedInterchange_dot_exchange (k := k)
    (P.T.E j (P.muP_preE j (nextSector (true, i) false s)))
    (P.W.E i (P.muM_postE i hR)) (homContentShift D i s.1)
    ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))
    (P.T.dot j _) (P.W.dot i _) (P.T.dot_mem j _) (P.W.dot_mem i _)
  rw [koszulSign_smul_eq_zsign (k := k), mul_comm (D.parity j)] at he
  exact he

lemma repeatedOuter_mixedQ :
    (P.mixedJ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).inv ≫
      P.mixedQ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z)) ≫
      (P.mixedJ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).hom =
    qExpr Sc (P.repeatedOuterX i j s hR hs Z) (P.repeatedOuterY i j s hR hs Z) i j := by
  exact P.mixedJ_inv_mixedQ_hom j i s hR _

/-- The crossing in the opposite direction, with its source transported.
This is not the inverse of the forward crossing. -/
def repeatedOuterProbeBackCore :=
    eqToHom (congrArg (fun V => (P.step (true, i) true _ trivial).obj
      ((P.step (true, j) true _ trivial).obj V))
      (eq_of_heq ((P.castH_obj_heq hs.symm ((P.castH hs).obj Z)).trans
        (P.castH_obj_heq hs Z))).symm) ≫
      P.preCrossNe i j (nextSector (true, i) false s) hs.symm ((P.castH hs).obj Z)

def repeatedOuterProbeBack :=
  (P.step (true, i) false s hR).map (P.repeatedOuterProbeBackCore i j s hs Z)

lemma repeatedOuter_probeQuad_base (hij : i ≠ j) :
    P.preCrossNe j i (nextSector (true, i) false s) hs Z ≫
      P.repeatedOuterProbeBackCore i j s hs Z =
      qExpr Sc
        (End.of (P.dotDiag j true _ trivial ((P.step (true, i) true _ trivial).obj
          ((P.castH hs).obj Z))))
        (End.of ((P.step (true, j) true _ trivial).map
          (P.dotDiag i true _ trivial ((P.castH hs).obj Z)))) j i := by
  let t := nextSector (true, i) false s
  have h₄ : -P.muP (nextSector (true, i) true t) + D.α j =
      -P.muP (nextSector (true, i) true (nextSector (true, j) true t)) := by
    rw [hs]; exact P.muP_preE j _
  have h₄' : -P.muP (nextSector (true, j) true t) + D.α i =
      -P.muP (nextSector (true, j) true (nextSector (true, i) true t)) := by
    rw [← hs]; exact P.muP_preE i _
  have hF := P.preCrossNe_heq j i t hs Z h₄
  have hG := (P.preCrossNe_heq i j t hs.symm ((P.castH hs).obj Z) h₄').trans
    (probeCore_heq P.T i j _ _ _ _ h₄ (P.muP_preE i _)
      (congrArg (fun x => -P.muP x) hs.symm)
      (congrArg (fun x => P.W.obj (P.muM x)) hs.symm) _ _
      ((P.sector_heq hs.symm _).trans
        ((P.castH_obj_heq hs Z).trans (P.sector_heq hs Z).symm)))
  have hM := (congrArg (P.step (true, i) true t trivial).obj
    (eq_of_heq (P.preE_obj_heq j hs h₄ (P.muP_preE j _) Z))).symm
  have hcore := probeCore_quad P.T P.probeRel hij.symm
    (P.muP_preE j t) (P.muP_preE i _) (P.muP_preE i t) h₄ (hs ▸ Z)
  let back := eqToHom (congrArg (fun V => (P.step (true, i) true _ trivial).obj
      ((P.step (true, j) true _ trivial).obj V))
      (eq_of_heq ((P.castH_obj_heq hs.symm ((P.castH hs).obj Z)).trans
        (P.castH_obj_heq hs Z))).symm) ≫
      P.preCrossNe i j t hs.symm ((P.castH hs).obj Z)
  have hGb : HEq back (probeCore P.T i j (P.muP_preE i t) h₄
      (P.muP_preE j t) (P.muP_preE i _) (hs ▸ Z)) := by
    exact (eqToHom_comp_heq _ _).trans hG
  have hquad := quad_of_heq Sc rfl hM hF hGb (HEq.rfl) (HEq.rfl) j i hcore
  have hquad' : P.preCrossNe j i t hs Z ≫ back =
      qExpr Sc
        (End.of (P.dotDiag j true t trivial ((P.step (true, i) true _ trivial).obj
          ((P.castH hs).obj Z))))
        (End.of ((P.step (true, j) true t trivial).map
          (P.dotDiag i true _ trivial ((P.castH hs).obj Z)))) j i := hquad
  exact hquad'

lemma repeatedOuter_probeQuad (hij : i ≠ j) :
    (P.step (true, i) false s hR).map
        (P.preCrossNe j i (nextSector (true, i) false s) hs Z) ≫
      P.repeatedOuterProbeBack i j s hR hs Z =
    qExpr Sc (P.repeatedOuterZ i j s hR hs Z) (P.repeatedOuterY i j s hR hs Z) i j := by
  let t := nextSector (true, i) false s
  let back := P.repeatedOuterProbeBackCore i j s hs Z
  have hm := congrArg (P.step (true, i) false s hR).map
    (P.repeatedOuter_probeQuad_base i j s hs Z hij)
  have hmQ := qExpr_map Sc (functorAlg (k := k) (P.step (true, i) false s hR) _)
    (End.of (P.dotDiag j true t trivial ((P.step (true, i) true _ trivial).obj
      ((P.castH hs).obj Z))))
    (End.of ((P.step (true, j) true t trivial).map
      (P.dotDiag i true _ trivial ((P.castH hs).obj Z)))) j i
  have hm' : (P.step (true, i) false s hR).map
        (P.preCrossNe j i (nextSector (true, i) false s) hs Z) ≫
      P.repeatedOuterProbeBack i j s hR hs Z =
      qExpr Sc (P.repeatedOuterY i j s hR hs Z) (P.repeatedOuterZ i j s hR hs Z) j i :=
    ((P.step (true, i) false s hR).map_comp (P.preCrossNe j i t hs Z) back).symm.trans
      (hm.trans hmQ)
  rw [hm']
  exact (qExpr_swap Sc _ _ i j _ (P.repeatedOuterZ_mul_Y i j s hR hs Z)
    (fun n hn => zsign_pow_of_mul_eq_zero _ _ n hn)).symm

lemma repeatedOuterX_comp_Q :
    P.repeatedOuterX i j s hR hs Z ≫
      qExpr Sc (P.repeatedOuterZ i j s hR hs Z) (P.repeatedOuterY i j s hR hs Z) i j =
    qExpr Sc (P.repeatedOuterZ i j s hR hs Z) (P.repeatedOuterY i j s hR hs Z) i j ≫
      P.repeatedOuterX i j s hR hs Z := by
  have hxz := congrArg (fun f => zsign k (D.parity i) • f)
    (P.repeatedOuterX_mul_Z i j s hR hs Z)
  have hxy := congrArg (fun f => zsign k (D.parity i * D.parity j) • f)
    (P.repeatedOuterX_mul_Y i j s hR hs Z)
  simp only [smul_smul, zsign_mul_self', one_smul, End.mul_def] at hxz hxy
  exact comp_qExpr (Sc := Sc) _ _ _ _ _ i j _ _ hxz.symm hxy.symm
    (fun n hn => by
      simpa only [mul_one] using zsign_pow_of_mul_eq_zero (k := k) (D.parity i) 1 n hn)
    (fun n hn => by
      rw [mul_comm (D.parity i)]
      exact zsign_pow_of_mul_eq_zero _ _ n hn)

lemma repeatedOuterZ_comp_Q :
    P.repeatedOuterZ i j s hR hs Z ≫
      qExpr Sc (P.repeatedOuterZ i j s hR hs Z) (P.repeatedOuterY i j s hR hs Z) i j =
    qExpr Sc (P.repeatedOuterZ i j s hR hs Z) (P.repeatedOuterY i j s hR hs Z) i j ≫
      P.repeatedOuterZ i j s hR hs Z := by
  have hzy := congrArg (fun f => zsign k (D.parity i * D.parity j) • f)
    (P.repeatedOuterZ_mul_Y i j s hR hs Z)
  simp only [smul_smul, zsign_mul_self', one_smul, End.mul_def] at hzy
  exact comp_qExpr (Sc := Sc) _ _ _ _ _ i j 1 _ (one_smul _ _).symm hzy.symm
    (fun _ _ => one_pow _)
    (fun n hn => by
      rw [mul_comm (D.parity i)]
      exact zsign_pow_of_mul_eq_zero _ _ n hn)

lemma repeatedOuterCoeff_comp_Q (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) :
    P.repeatedOuterProbeCoeff c i j s hR hs Z ≫
      qExpr Sc (P.repeatedOuterZ i j s hR hs Z) (P.repeatedOuterY i j s hR hs Z) i j =
    qExpr Sc (P.repeatedOuterZ i j s hR hs Z) (P.repeatedOuterY i j s hR hs Z) i j ≫
      P.repeatedOuterProbeCoeff c i j s hR hs Z := by
  have he := coefficient_alg_commute P i c hc h (nextSector (true, j) true s) hR
    ((P.castH hs).obj Z) (P.repeatedOuterAlg i j s hR hs Z)
    (qExpr Sc (P.repeatedOuterZ i j s hR hs Z) (P.repeatedOuterY i j s hR hs Z) i j)
    (by
      rw [P.repeatedOuterAlg_pre i j s hR hs Z, Linear.smul_comp, Linear.comp_smul]
      exact congrArg (fun f => zsign k (D.parity i * D.parity j) • f)
        (P.repeatedOuterZ_comp_Q i j s hR hs Z))
    (by
      rw [P.repeatedOuterAlg_post i j s hR hs Z, Linear.smul_comp, Linear.comp_smul]
      exact congrArg (fun f => zsign k (D.parity i * D.parity j) • f)
        (P.repeatedOuterX_comp_Q i j s hR hs Z))
  have he' := congrArg (fun f => zsign k (D.parity i * D.parity j) • f) he
  rw [repeatedOuterCoeff_alg]
  erw [Linear.smul_comp, Linear.comp_smul]
  exact he'

/-- The raw route through the mixed Q entry and the adjacent coefficient. -/
def repeatedOuterDiagonalLeft (c : P.CrossCoeff Sc) : End (P.rpObj i j s hR
    ((P.step (true, i) true (nextSector (true, i) false (nextSector (true, j) true s))
      trivial).obj ((P.castH hs).obj Z))) :=
  (P.mixedJ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).inv ≫
    P.mixedQ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z)) ≫
    (P.step (true, j) true s trivial).map
      (c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)) ≫
    (P.mixedJ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).hom

/-- The raw route through the two oppositely directed probe crossings. -/
def repeatedOuterDiagonalRight (c : P.CrossCoeff Sc) : End (P.rpObj i j s hR
    ((P.step (true, i) true (nextSector (true, i) false (nextSector (true, j) true s))
      trivial).obj ((P.castH hs).obj Z))) :=
  (P.step (true, i) false s hR).map
      (P.preCrossNe j i (nextSector (true, i) false s) hs Z) ≫
    c.a i s hR ((P.step (true, j) true _ trivial).obj Z) ≫
    P.repeatedOuterProbeBack i j s hR hs Z

lemma repeatedOuterDiagonalLeft_eq (c : P.CrossCoeff Sc) :
    P.repeatedOuterDiagonalLeft i j s hR hs Z c =
      zsign k (D.parity i * D.parity j) •
        (End.of (P.repeatedOuterProbeCoeff c i j s hR hs Z) *
          qExpr Sc (P.repeatedOuterX i j s hR hs Z) (P.repeatedOuterY i j s hR hs Z) i j) := by
  rw [← P.repeatedOuter_mixedQ i j s hR hs Z]
  simp only [End.mul_def, End.of, repeatedOuterProbeCoeff, Linear.comp_smul,
    smul_smul, zsign_mul_self', one_smul, Category.assoc, Iso.hom_inv_id_assoc,
    repeatedOuterDiagonalLeft]

lemma repeatedOuterDiagonalRight_eq (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    P.repeatedOuterDiagonalRight i j s hR hs Z c =
      zsign k (D.parity i * D.parity j) •
        (qExpr Sc (P.repeatedOuterZ i j s hR hs Z) (P.repeatedOuterY i j s hR hs Z) i j *
          End.of (P.repeatedOuterProbeCoeff c i j s hR hs Z)) := by
  have he := congrArg (fun f => f ≫ P.repeatedOuterProbeBack i j s hR hs Z)
    (P.repeatedOuterProbeCross_coeff c i j s hR hs Z hc h hij)
  simp only [Category.assoc] at he
  change P.repeatedOuterDiagonalRight i j s hR hs Z c =
    (zsign k (D.parity i * D.parity j) •
      (P.repeatedOuterProbeCoeff c i j s hR hs Z ≫
        (P.step (true, i) false s hR).map
          (P.preCrossNe j i (nextSector (true, i) false s) hs Z))) ≫
      P.repeatedOuterProbeBack i j s hR hs Z at he
  rw [Linear.smul_comp, Category.assoc] at he
  exact he.trans (congrArg (fun f => zsign k (D.parity i * D.parity j) •
    (P.repeatedOuterProbeCoeff c i j s hR hs Z ≫ f))
      (P.repeatedOuter_probeQuad i j s hR hs Z hij))

/-- Reduction of the two raw routes, with the order of the coefficient retained. -/
theorem repeatedOuterDiagonal_raw (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let x := P.repeatedOuterX i j s hR hs Z
    let y := P.repeatedOuterY i j s hR hs Z
    let z := P.repeatedOuterZ i j s hR hs Z
    let A := End.of (P.repeatedOuterProbeCoeff c i j s hR hs Z)
    P.repeatedOuterDiagonalLeft i j s hR hs Z c -
        P.repeatedOuterDiagonalRight i j s hR hs Z c =
      zsign k (D.parity i * D.parity j) •
        (A * qExpr Sc x y i j - qExpr Sc z y i j * A) := by
  dsimp only
  rw [P.repeatedOuterDiagonalLeft_eq i j s hR hs Z c,
    P.repeatedOuterDiagonalRight_eq i j s hR hs Z c hc h hij]
  exact (smul_sub _ _ _).symm

/-- The actual raw repeated-outer diagonal difference is the two signed
coefficient sums. Neither probe crossing nor the Q polynomial is inverted. -/
theorem repeatedOuterDiagonal_correction (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let x := P.repeatedOuterX i j s hR hs Z
    let y := P.repeatedOuterY i j s hR hs Z
    let z := P.repeatedOuterZ i j s hR hs Z
    P.repeatedOuterDiagonalLeft i j s hR hs Z c -
        P.repeatedOuterDiagonalRight i j s hR hs Z c =
      (∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (x ^ (D.dn i j - 1 - a) * z ^ a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i),
        ∑ a ∈ Finset.range b,
          (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
            (x ^ (b - 1 - a) * y ^ d * z ^ a) := by
  have he := P.repeatedOuterDiagonal_raw i j s hR hs Z c hc h hij
  have hcomm : qExpr Sc (P.repeatedOuterZ i j s hR hs Z)
      (P.repeatedOuterY i j s hR hs Z) i j *
      End.of (P.repeatedOuterProbeCoeff c i j s hR hs Z) =
    End.of (P.repeatedOuterProbeCoeff c i j s hR hs Z) *
      qExpr Sc (P.repeatedOuterZ i j s hR hs Z)
        (P.repeatedOuterY i j s hR hs Z) i j :=
    P.repeatedOuterCoeff_comp_Q i j s hR hs Z c hc h
  dsimp only at he ⊢
  rw [hcomm] at he
  have hdist := mul_sub (End.of (P.repeatedOuterProbeCoeff c i j s hR hs Z))
    (qExpr Sc (P.repeatedOuterX i j s hR hs Z) (P.repeatedOuterY i j s hR hs Z) i j)
    (qExpr Sc (P.repeatedOuterZ i j s hR hs Z) (P.repeatedOuterY i j s hR hs Z) i j)
  exact he.trans ((congrArg (fun f => zsign k (D.parity i * D.parity j) • f)
    hdist.symm).trans (P.repeatedOuter_qExpr_correction i j s hR hs Z c hc))

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
