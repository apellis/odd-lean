/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterCoefficient
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterQCorrection

/-! # Dot coordinates for the repeated-outer diagonal correction

Coordinates on `Rᵢ Pⱼ Pᵢ` supporting `CrossBraid.braidEq_diag`.
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

/-- Reservoir coordinate on the first strand. -/
def repeatedOuterX : End (P.rpObj i j s hR
    ((P.step (true, i) true (nextSector (true, i) false (nextSector (true, j) true s))
      trivial).obj ((P.castH hs).obj Z))) :=
  P.dotDiag i false s hR
    ((P.step (true, j) true _ trivial).obj
      ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z)))

/-- Probe coordinate on the middle strand. -/
def repeatedOuterY : End (P.rpObj i j s hR
    ((P.step (true, i) true (nextSector (true, i) false (nextSector (true, j) true s))
      trivial).obj ((P.castH hs).obj Z))) := End.of <|
  (P.step (true, i) false s hR).map
    (P.dotDiag j true _ trivial
      ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z)))

/-- Probe coordinate on the last strand. -/
def repeatedOuterZ : End (P.rpObj i j s hR
    ((P.step (true, i) true (nextSector (true, i) false (nextSector (true, j) true s))
      trivial).obj ((P.castH hs).obj Z))) := End.of <|
  (P.step (true, i) false s hR).map
    ((P.step (true, j) true _ trivial).map
      (P.dotDiag i true _ trivial ((P.castH hs).obj Z)))

/-- Algebra transport from the adjacent equal pair to the separated pair. -/
def repeatedOuterAlg :=
  (conjAlg (k := k)
    (P.mixedJ j i s hR
      ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z)))).comp
    (functorAlg (k := k) (P.step (true, j) true s trivial)
      (P.rpObj i i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)))

lemma repeatedOuterAlg_post :
    P.repeatedOuterAlg i j s hR hs Z
      (P.rpPostDot i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)) =
    zsign k (D.parity i * D.parity j) • P.repeatedOuterX i j s hR hs Z := by
  have he := P.prPostDot_comp_mixedJ_ne j i s hR
    ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))
  have he' := congrArg (fun f =>
    (P.mixedJ j i s hR
      ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).inv ≫ f) he
  change (P.mixedJ j i s hR
      ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).inv ≫
    (P.step (true, j) true s trivial).map _ ≫
    (P.mixedJ j i s hR
      ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).hom = _
  simpa only [repeatedOuterX, dotDiag, prPostDot, rpPostDot,
    step, homContentPreE, homContentPostE, homPre, homPost, Functor.comp_obj,
    Linear.comp_smul, ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    mul_comm (D.parity j)] using he'

lemma repeatedOuterAlg_pre :
    P.repeatedOuterAlg i j s hR hs Z
      (P.rpPreDot i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)) =
    zsign k (D.parity i * D.parity j) • P.repeatedOuterZ i j s hR hs Z := by
  have he := (P.mixedJ_supernatural j i s hR).naturality
    (P.T.dot_mem i (P.muP_preE i
      (nextSector (true, j) true (nextSector (true, i) false s))) |>
      TwoSupercategory.whiskerRight_mem ((P.castH hs).obj Z))
  have hz (p : ZMod 2) : sign k p = zsign k p := by
    fin_cases p <;> simp [sign, zsign]
  simp only [mul_assoc, SKM.zmod2_mul_self, hz] at he
  have he' := congrArg (fun f =>
    (P.mixedJ j i s hR
      ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).inv ≫ f) he
  change (P.mixedJ j i s hR
      ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).inv ≫
    (P.step (true, j) true s trivial).map _ ≫
    (P.mixedJ j i s hR
      ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).hom = _
  simpa only [repeatedOuterZ, dotDiag, rpPreDot,
    step, homContentPreE, homContentPostE, homPre, homPost, Functor.comp_obj,
    Functor.comp_map, Linear.smul_comp, Linear.comp_smul, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp, mul_comm (D.parity j)] using he'

lemma repeatedOuterX_mul_Z :
    P.repeatedOuterX i j s hR hs Z * P.repeatedOuterZ i j s hR hs Z =
      zsign k (D.parity i) •
        (P.repeatedOuterZ i j s hR hs Z * P.repeatedOuterX i j s hR hs Z) := by
  have he := P.rpPreDot_comp_rpPostDot i (nextSector (true, j) true s) hR
    ((P.castH hs).obj Z)
  rw [koszulSign_smul_eq_zsign (k := k), SKM.zmod2_mul_self] at he
  simp only [← End.mul_def] at he
  have he' := congrArg (P.repeatedOuterAlg i j s hR hs Z) he
  simpa only [map_mul, map_smul, repeatedOuterAlg_post, repeatedOuterAlg_pre,
    smul_mul_assoc, mul_smul_comm, smul_smul, zsign_mul_self', one_smul] using he'

lemma repeatedOuterZ_mul_Y :
    P.repeatedOuterZ i j s hR hs Z * P.repeatedOuterY i j s hR hs Z =
      zsign k (D.parity i * D.parity j) •
        (P.repeatedOuterY i j s hR hs Z * P.repeatedOuterZ i j s hR hs Z) := by
  have he := (P.dotDiag_supernatural j true (nextSector (true, i) false s) trivial).naturality
    (P.T.dot_mem i (P.muP_preE i
      (nextSector (true, j) true (nextSector (true, i) false s))) |>
      TwoSupercategory.whiskerRight_mem ((P.castH hs).obj Z))
  have hz (p : ZMod 2) : sign k p = zsign k p := by
    fin_cases p <;> simp [sign, zsign]
  have he' := congrArg (P.step (true, i) false s hR).map he
  simp only [Functor.map_comp, Functor.map_smul, hz] at he'
  have he'' := congrArg (fun f => zsign k (D.parity i * D.parity j) • f) he'
  simpa only [repeatedOuterZ, repeatedOuterY, End.mul_def, End.of, dotDiag,
    step, homContentPreE, homContentPostE, homPre, homPost, Functor.comp_obj,
    Functor.comp_map, smul_smul, zsign_mul_self', one_smul,
    Functor.map_comp, Functor.map_smul, Linear.smul_comp, hz,
    mul_comm (D.parity j)] using he''.symm

lemma repeatedOuterCoeff_alg (c : P.CrossCoeff Sc) :
    P.repeatedOuterProbeCoeff c i j s hR hs Z =
      zsign k (D.parity i * D.parity j) •
        P.repeatedOuterAlg i j s hR hs Z
          (c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)) := rfl

lemma repeatedOuterCoeff_even (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (hi : D.parity i = 0) :
    End.of (P.repeatedOuterProbeCoeff c i j s hR hs Z) *
      (P.repeatedOuterX i j s hR hs Z - P.repeatedOuterZ i j s hR hs Z) = 1 := by
  have he := (hc.even i hi (nextSector (true, j) true s) hR ((P.castH hs).obj Z)).2
  change c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z) *
    (P.rpPostDot i (nextSector (true, j) true s) hR ((P.castH hs).obj Z) -
      P.rpPreDot i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)) = 1 at he
  have he' := congrArg (P.repeatedOuterAlg i j s hR hs Z) he
  simpa only [map_mul, map_sub, map_one, repeatedOuterAlg_post, repeatedOuterAlg_pre,
    repeatedOuterCoeff_alg, hi, zero_mul, zsign_zero, one_smul] using he'

lemma repeatedOuterCoeff_odd (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (hi : D.parity i = 1) :
    End.of (P.repeatedOuterProbeCoeff c i j s hR hs Z) *
      (P.repeatedOuterX i j s hR hs Z * P.repeatedOuterX i j s hR hs Z -
        P.repeatedOuterZ i j s hR hs Z * P.repeatedOuterZ i j s hR hs Z) =
      P.repeatedOuterX i j s hR hs Z - P.repeatedOuterZ i j s hR hs Z := by
  have he := (hc.odd i hi (nextSector (true, j) true s) hR ((P.castH hs).obj Z)).2
  simp only [← End.mul_def] at he
  have he' := congrArg (P.repeatedOuterAlg i j s hR hs Z) he
  simp only [map_mul, map_sub, repeatedOuterAlg_post, repeatedOuterAlg_pre,
    smul_mul_assoc, mul_smul_comm, smul_smul, zsign_mul_self', one_smul] at he'
  have he'' := congrArg (fun f => zsign k (D.parity i * D.parity j) • f) he'
  simp only [smul_sub, smul_smul, zsign_mul_self', one_smul] at he''
  rw [repeatedOuterCoeff_alg, smul_mul_assoc, ← neg_sub
    (P.repeatedOuterZ i j s hR hs Z * P.repeatedOuterZ i j s hR hs Z)
    (P.repeatedOuterX i j s hR hs Z * P.repeatedOuterX i j s hR hs Z), mul_neg,
    smul_neg, he'', neg_sub]

/-- The two coefficient sums for the separated coordinates, from the inverse
coefficient identities and the dot slides. No braid relation is assumed. -/
theorem repeatedOuter_qExpr_correction (c : P.CrossCoeff Sc) (hc : c.IsInverse) :
    let x := P.repeatedOuterX i j s hR hs Z
    let y := P.repeatedOuterY i j s hR hs Z
    let z := P.repeatedOuterZ i j s hR hs Z
    let A := End.of (P.repeatedOuterProbeCoeff c i j s hR hs Z)
    zsign k (D.parity i * D.parity j) • (A * (qExpr Sc x y i j - qExpr Sc z y i j)) =
      (∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (x ^ (D.dn i j - 1 - a) * z ^ a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i),
        ∑ a ∈ Finset.range b,
          (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
            (x ^ (b - 1 - a) * y ^ d * z ^ a) := by
  exact RepeatedOuterQCorrection.qExpr_correction Sc _ _ _ _ i j
    (P.repeatedOuterX_mul_Z i j s hR hs Z)
    (P.repeatedOuterZ_mul_Y i j s hR hs Z)
    (P.repeatedOuterCoeff_even i j s hR hs Z c hc)
    (P.repeatedOuterCoeff_odd i j s hR hs Z c hc)

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
