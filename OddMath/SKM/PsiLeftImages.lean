/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PsiDescent

/-!
# The left cup and cap under ψ

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Proposition 9.4, using the derived left cup and cap of Definition 2.2.

`etaPDiagram` and `epsPDiagram` are the free linear expressions from the two
weight branches of Definition 2.2. Their images under the existing presentation
map are proved equal to `etaP` and `epsP`, respectively. Applying the seven-shape
`psiLin` evaluator to these expressions gives:

* `psiLin_etaP`: the right cap with coefficient `psiCoeff t (ipar D i μ)`;
* `psiLin_epsP`: the right cup with coefficient
  `psiCoeff t (ipar D i μ) * sign k (ipar D i μ)`.

The boundaries are those of the left cup `1 → EF` and left cap `FE → 1`
in the shifted super-opposite; their underlying target maps run in the reverse
direction. Both identities hold at every weight, including zero. The proofs
calculate the top inverse-matrix entries and the complementary dotted mixed
crossings from the presentation relations, retaining the super-opposite and
whiskering signs. They assume no preservation or desired-image equations.

These are raw evaluation identities supplying the left-generator calculations
needed by the inverse in Proposition 9.4. They do not assert quotient descent,
extension to the Q/Π envelope, or a two-sided inverse functor. The coefficient
ring is the existing arbitrary commutative ring, with `t ^ 2 = -1`; no field or
additional invertibility hypothesis is introduced.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

private theorem cupDual_top (cs : CScalars Sc) (i : I) (μ : X) (hh : 0 < D.h i μ) :
    psiSameCupDual cs i μ (D.h i μ - 1).toNat =
      (↑(cs.c μ i)⁻¹ : k) • cl D Sc μ [up i, dn i] [] (epsL i 0) := by
  rw [psiSameCupDual, sum_eq_single 0]
  · have hr : ((D.h i μ - 1).toNat : ℤ) = D.h i μ - 1 := by omega
    rw [psiSameCupCoeff]
    simp only [Nat.cast_zero, add_zero, neg_zero, zero_sub]
    rw [show -(↑(D.h i μ - 1).toNat : ℤ) - 2 = -D.h i μ - 1 by omega,
      bubR_eq_c]
    have he : D.parity i * ((D.h i μ + (D.h i μ - 1).toNat + 1 : ℤ) : ZMod 2) = 0 := by
      rw [hr]; push_cast; ring_nf
      rw [show (2 : ZMod 2) = 0 from rfl, mul_zero]
    rw [he, zsign_zero, one_smul, Linear.comp_smul, Category.comp_id]
  · intro n hn hn0
    rw [psiSameCupCoeff_zero cs i μ n _ (by omega), Limits.comp_zero]
  · intro h
    exact False.elim (h (mem_range.mpr (by omega)))

private theorem capDual_top (cs : CScalars Sc) (i : I) (μ : X) (hh : D.h i μ < 0) :
    psiSameCapDual cs i μ (-D.h i μ - 1).toNat =
      (cs.c μ i : k) • cl D Sc μ [] [dn i, up i] (etaL i 0) := by
  rw [psiSameCapDual, sum_eq_single 0]
  · have hr : ((-D.h i μ - 1).toNat : ℤ) = -D.h i μ - 1 := by omega
    rw [psiSameCapCoeff]
    simp only [Nat.cast_zero, add_zero, neg_zero, zero_sub]
    rw [show -(↑(-D.h i μ - 1).toNat : ℤ) - 2 = D.h i μ - 1 by omega,
      bubL_eq_c]
    have he : D.parity i * ((D.h i μ + (-D.h i μ - 1).toNat + 1 : ℤ) : ZMod 2) = 0 := by
      rw [hr]; push_cast; ring
    rw [he, zsign_zero, one_smul, Linear.smul_comp, Category.id_comp]
  · intro n hn hn0
    rw [psiSameCapCoeff_zero cs i μ n _ (by omega), Limits.zero_comp]
  · intro h
    exact False.elim (h (mem_range.mpr (by omega)))

private theorem sigma_dots_epsP_top (cs : CScalars Sc) (i : I) (μ : X) (hh : D.h i μ ≤ 0) :
    cl D Sc μ [up i, dn i] [dn i, up i]
      (sigmaL i i ++ dotsL [dn i] i [] (-D.h i μ).toNat) ≫ epsP cs i μ =
      (↑(cs.c μ i)⁻¹ : k) • cl D Sc μ [up i, dn i] [] (epsL i 0) := by
  rcases eq_or_lt_of_le hh with h0 | hn
  · simp only [h0, neg_zero, Int.toNat_zero, dotsL, List.replicate_zero, List.append_nil]
    rw [eq_5_17_a, h0, Int.toNat_zero, zero_add, sum_range_one]
    simp only [Nat.cast_zero, mul_zero, zsign_zero, neg_zero, zero_sub, one_smul]
    rw [show (-1 : ℤ) = -D.h i μ - 1 by omega, bubR_eq_c,
      Linear.comp_smul, Category.comp_id]
  · have E := lemma31_eq3_eq Sc i μ (-D.h i μ).toNat
    rw [sub_eq_iff_eq_add] at E
    rw [E, Preadditive.add_comp, Preadditive.sum_comp, Linear.smul_comp,
      ← cl_comp (sChain_dL i _) (sChain_sigmaL i i), Category.assoc,
      eq_2_14_a cs i μ hn, Limits.comp_zero, smul_zero, add_zero, sum_eq_single 0]
    · rw [Linear.smul_comp, cl_capcup, Category.assoc,
        eq_2_14_c cs i μ _ (by omega), ite_eq_left (by omega),
        Linear.comp_smul, Category.comp_id]
      simp only [Nat.cast_zero, mul_zero, zsign_zero, one_smul]
    · intro q hq hq0
      rw [mem_range] at hq
      rw [Linear.smul_comp, cl_capcup, Category.assoc,
        eq_2_14_c cs i μ _ (by omega), ite_eq_right (by omega), Limits.comp_zero, smul_zero]
    · intro h
      exact False.elim (h (mem_range.mpr (by omega)))

private theorem etaP_dots_sigma_top (cs : CScalars Sc) (i : I) (μ : X) (hh : 0 ≤ D.h i μ) :
    etaP cs i μ ≫ cl D Sc μ [up i, dn i] [dn i, up i]
      (dotsL [] i [dn i] (D.h i μ).toNat ++ sigmaL i i) =
      (-(zsign k (D.parity i)) * (cs.c μ i : k)) •
        cl D Sc μ [] [dn i, up i] (etaL i 0) := by
  rcases eq_or_lt_of_le hh with h0 | hn
  · simp only [← h0, Int.toNat_zero, dotsL, List.replicate_zero, List.nil_append]
    rw [eq_5_17_b, ← h0, neg_zero, Int.toNat_zero, zero_add, sum_range_one]
    simp only [Nat.cast_zero, zero_add, Nat.cast_one, mul_one, neg_zero, zero_sub]
    rw [show (-1 : ℤ) = D.h i μ - 1 by omega, bubL_eq_c,
      Linear.smul_comp, Category.id_comp, smul_smul, ← neg_smul, neg_mul]
  · let N := (D.h i μ).toNat
    have hN : (N : ℤ) = D.h i μ := by dsimp [N]; omega
    have E := congrArg (fun f => etaP cs i μ ≫ f) (lemma31_eq3_eq Sc i μ N)
    rw [Preadditive.comp_sub, Linear.comp_smul,
      ← cl_comp (sChain_sigmaL i i) (sChain_dR i N), ← Category.assoc,
      eq_2_13_a cs i μ hn, Limits.zero_comp, zero_sub, Preadditive.comp_sum,
      sum_eq_single (N - 1)] at E
    · rw [Linear.comp_smul, cl_capcup, ← Category.assoc,
        eq_2_13_c cs i μ _ (by omega), ite_eq_left (by omega),
        Linear.smul_comp, Category.id_comp, smul_smul,
        show N - 1 - (N - 1) = 0 by omega] at E
      have H := congrArg (fun f => -(zsign k (D.parity i * D.parity i * (N : ZMod 2))) • f) E
      simp only [smul_neg, smul_smul, neg_mul,
        zsign_mul_self', neg_smul, one_smul, neg_neg] at H
      have hp : D.parity i * D.parity i * (N : ZMod 2) +
          D.parity i * ((N - 1 : ℕ) : ZMod 2) = D.parity i := by
        rw [Nat.cast_sub (by omega), Nat.cast_one, zmod2_mul_self']
        generalize D.parity i = p
        generalize (N : ZMod 2) = q
        revert p q
        decide
      rw [H]
      rw [← mul_assoc, ← zsign_add, hp, neg_mul, neg_smul]
    · intro q hq hqN
      rw [mem_range] at hq
      rw [Linear.comp_smul, cl_capcup, ← Category.assoc,
        eq_2_13_c cs i μ _ (by omega), ite_eq_right (by omega), Limits.zero_comp, smul_zero]
    · intro h
      exact False.elim (h (mem_range.mpr (by omega)))


open Supercategory BicategoryStruct
variable {sy : Symmetrizer D} {hc : Sc.Homogeneous}
private theorem left_ud (μ : X) (i : I) : wt D μ [up i, dn i] = μ := by simp [wt, sh]
private theorem left_du (μ : X) (i : I) : wt D μ [dn i, up i] = μ := by simp [wt, sh]

private theorem raw_rebase (t : k) (cs : CScalars Sc) (ν ν' μ : X)
    (L : List (LayerData I)) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hL : SChain s L r) (h : ν = ν') :
    psiRaw (sy := sy) (hc := hc) t cs ν' μ L (hs.trans h) (hr.trans h) hL =
      psiRebase h (psiRaw t cs ν μ L hs hr hL) := by subst ν'; rfl

private theorem raw_dots (t : k) (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ) :
    psiRaw (sy := sy) (hc := hc) t cs (wt D μ [up i]) μ (dotsL [] i [] n)
      rfl rfl (sChain_dotsL [] i [] n) = cpow (psiDot t μ i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cpow_succ']
    simp only [dotsL, List.replicate_succ, psiRaw, eqToHom_refl, Category.id_comp] at *
    rw [ih]
    congr 1
    simp [psiLayer, psiGen, psiPrimaryGen, psiPlace, Shape.dom, Shape.cod,
      psiWhiskerLeft_nil, psiWhiskerRight_nil]

private theorem raw_dots_left (t : k) (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ) :
    psiRaw (sy := sy) (hc := hc) t cs μ μ (dotsL [] i [dn i] n)
      (left_ud μ i) (left_ud μ i) (sChain_dL i n) = psiSameDotsLeft t μ i n := by
  rw [raw_rebase t cs (wt D μ [up i, dn i]) μ μ _ rfl rfl _ (left_ud μ i)]
  unfold psiSameDotsLeft
  congr 1
  have E := psiRaw_whisk (sy := sy) (hc := hc) t cs
    (wt D μ [up i, dn i]) (wt D (wt D μ [dn i]) [up i]) (wt D μ [dn i]) μ
    [] [dn i] (dotsL [] i [] n) rfl rfl rfl rfl (sChain_dotsL [] i [] n)
  simp only [dotsL, List.map_replicate, whL, List.nil_append, List.append_nil] at E
  simp only [dotsL]
  erw [E]
  rw [show psiRaw (sy := sy) (hc := hc) t cs (wt D (wt D μ [dn i]) [up i])
      (wt D μ [dn i]) (List.replicate n ([], Shape.dot i, [])) rfl rfl _ =
      cpow (psiDot t (wt D μ [dn i]) i) n from raw_dots t cs _ i n]
  simp [psiPlace, psiWhiskerLeft_nil]

private theorem raw_dots_right (t : k) (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ) :
    psiRaw (sy := sy) (hc := hc) t cs μ μ (dotsL [dn i] i [] n)
      (left_du μ i) (left_du μ i) (sChain_dR i n) = psiSameDotsRight t μ i n := by
  have E := psiRaw_whisk (sy := sy) (hc := hc) t cs
    μ (wt D μ [up i]) μ μ [dn i] [] (dotsL [] i [] n)
    (left_du μ i) rfl rfl rfl (sChain_dotsL [] i [] n)
  simp only [dotsL, List.map_replicate, whL, List.append_nil] at E
  simp only [dotsL]
  erw [E]
  rw [show psiRaw (sy := sy) (hc := hc) t cs (wt D μ [up i]) μ
      (List.replicate n ([], Shape.dot i, [])) rfl rfl _ =
      cpow (psiDot t μ i) n from raw_dots t cs μ i n]
  simp [psiSameDotsRight, psiPlace, psiWhiskerRight_nil]

private theorem raw_epsL (t : k) (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ) :
    psiRaw (sy := sy) (hc := hc) t cs μ μ (epsL i n)
      (left_ud μ i) rfl (sChain_epsL i n) = psiDottedCap cs t μ i n := by
  simp only [epsL]
  rw [psiRaw_append t cs μ μ _ _ (left_ud μ i) (left_ud μ i) rfl
    (sChain_dL i n) (by simp [SChain, Shape.dom, Shape.cod]), raw_dots_left]
  rw [psiRaw_gen]
  rfl

private theorem raw_etaL (t : k) (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ) :
    psiRaw (sy := sy) (hc := hc) t cs μ μ (etaL i n)
      rfl (left_du μ i) (sChain_etaL i n) = psiDottedCup cs t μ i n := by
  change psiRaw t cs μ μ ([([], Shape.cup i, [])] ++ dotsL [dn i] i [] n) _ _ _ = _
  rw [psiRaw_append t cs μ μ _ _ rfl (left_du μ i) (left_du μ i)
    (by simp [SChain, Shape.dom, Shape.cod]) (sChain_dR i n), raw_dots_right,
    psiRaw_gen]
  rfl

private theorem raw_lcross (t : k) (cs : CScalars Sc) (μ : X) (i : I) :
    psiRaw (sy := sy) (hc := hc) t cs μ μ (lcrossL i i)
      (left_du μ i) (left_ud μ i) (sChain_lcrossL i i) = psiSameLCross t μ i := by
  simp only [lcrossL]
  rw [psiRaw_gen]
  rfl


/-- The free linear expression defining the left cup in Definition 2.2. -/
def etaPDiagram (cs : CScalars Sc) (i : I) (μ : X) :
    LinDiagram k (ob D μ []) (ob D μ [up i, dn i]) :=
  if 0 < D.h i μ then (cs.c μ i : k) •
    dg D μ (dcupL i (D.h i μ - 1).toNat) (sChain_dcupL i _)
  else (zsign k (ipar D i μ) * (cs.c μ i : k)) •
    dg D μ (etaL i (-D.h i μ).toNat ++ lcrossL i i)
      ((sChain_etaL i _).append (sChain_lcrossL i i))

/-- The free linear expression defining the left cap in Definition 2.2. -/
def epsPDiagram (cs : CScalars Sc) (i : I) (μ : X) :
    LinDiagram k (ob D μ [dn i, up i]) (ob D μ []) :=
  if D.h i μ < 0 then (↑(cs.c μ i)⁻¹ : k) •
    dg D μ (dcapL i (-D.h i μ - 1).toNat) (sChain_dcapL i _)
  else (-(zsign k (D.parity i * (D.h i μ : ZMod 2)) * (↑(cs.c μ i)⁻¹ : k))) •
    dg D μ (lcrossL i i ++ epsL i (D.h i μ).toNat)
      ((sChain_lcrossL i i).append (sChain_epsL i _))

/-- The left-cup representative maps to the existing derived `etaP`. -/
theorem etaPDiagram_lin (cs : CScalars Sc) (i : I) (μ : X) :
    (pres D Sc).lin (etaPDiagram cs i μ) = etaP cs i μ := by
  unfold etaPDiagram etaP
  split_ifs <;> rw [Presentation.lin_smul, lin_dg]

/-- The left-cap representative maps to the existing derived `epsP`. -/
theorem epsPDiagram_lin (cs : CScalars Sc) (i : I) (μ : X) :
    (pres D Sc).lin (epsPDiagram cs i μ) = epsP cs i μ := by
  unfold epsPDiagram epsP
  split_ifs <;> rw [Presentation.lin_smul, lin_dg]

private theorem parity_top_pos (i : I) (μ : X) (hh : 0 < D.h i μ) :
    ((D.h i μ - 1).toNat : ZMod 2) * D.parity i = ipar D i μ := by
  rw [natCast_toNat_zmod _ (by omega)]
  simp only [Int.cast_sub, Int.cast_one, ipar]
  generalize D.parity i = p
  generalize (D.h i μ : ZMod 2) = q
  revert p q
  decide

private theorem parity_top_neg (i : I) (μ : X) (hh : D.h i μ < 0) :
    ((-D.h i μ - 1).toNat : ZMod 2) * D.parity i = ipar D i μ := by
  rw [natCast_toNat_zmod _ (by omega)]
  simp only [Int.cast_sub, Int.cast_one, Int.cast_neg, ipar]
  generalize D.parity i = p
  generalize (D.h i μ : ZMod 2) = q
  revert p q
  decide

/-- The left cup image, with its shifted super-opposite boundary. -/
def psiLeftCupImage (t : k) (μ : X) (i : I) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) μ μ [] rfl ⟶
      psiAt μ μ [up i, dn i] (left_ud μ i) :=
  SOp.mk' (psiCoeff t (ipar D i μ) • cl D Sc μ [up i, dn i] [] (epsL i 0))

/-- The left cap image, including its parity sign. -/
def psiLeftCapImage (t : k) (μ : X) (i : I) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) μ μ [dn i, up i] (left_du μ i) ⟶
      psiAt μ μ [] rfl :=
  SOp.mk' ((psiCoeff t (ipar D i μ) * sign k (ipar D i μ)) •
    cl D Sc μ [] [dn i, up i] (etaL i 0))

private theorem image_eta_pos (cs : CScalars Sc) (t : k) (μ : X) (i : I) (hh : 0 < D.h i μ) :
    psiLin (sy := sy) (hc := hc) t cs μ μ rfl (left_ud μ i) (etaPDiagram cs i μ) =
      psiLeftCupImage t μ i := by
  rw [etaPDiagram, ite_eq_left hh, map_smul, psiLin_dg]
  simp only [dcupL]
  rw [psiRaw_gen]
  apply SOp.hom_ext
  change (cs.c μ i : k) • SOp.unsop (psiGen t cs μ μ (.dcup i (D.h i μ - 1).toNat) rfl) = _
  rw [psiGen, psiRebase_unsop]
  change (cs.c μ i : k) • ((_ : k) • psiSameCupDual cs i μ (D.h i μ - 1).toNat) = _
  rw [cupDual_top cs i μ hh, parity_top_pos i μ hh]
  have hp : ipar D i μ * (ipar D i μ + 1) = 0 := by generalize ipar D i μ = p; revert p; decide
  rw [hp, sign_zero, mul_one, smul_smul, smul_smul]
  congr 1
  calc
    _ = psiCoeff t (ipar D i μ) * ((cs.c μ i : k) * ↑(cs.c μ i)⁻¹) := by ring
    _ = _ := by rw [Units.mul_inv, mul_one]

private theorem image_eps_neg (cs : CScalars Sc) (t : k) (μ : X) (i : I) (hh : D.h i μ < 0) :
    psiLin (sy := sy) (hc := hc) t cs μ μ (left_du μ i) rfl (epsPDiagram cs i μ) =
      psiLeftCapImage t μ i := by
  rw [epsPDiagram, ite_eq_left hh, map_smul, psiLin_dg]
  simp only [dcapL]
  rw [psiRaw_gen]
  apply SOp.hom_ext
  change (↑(cs.c μ i)⁻¹ : k) • SOp.unsop (psiGen t cs μ μ (.dcap i (-D.h i μ - 1).toNat) (left_du μ i)) = _
  rw [psiGen, psiRebase_unsop]
  change (↑(cs.c μ i)⁻¹ : k) • ((_ : k) • psiSameCapDual cs i μ (-D.h i μ - 1).toNat) = _
  rw [capDual_top cs i μ hh, parity_top_neg i μ hh, zmod2_mul_self', smul_smul, smul_smul]
  congr 1
  calc
    _ = (psiCoeff t (ipar D i μ) * sign k (ipar D i μ)) * ((↑(cs.c μ i)⁻¹ : k) * ↑(cs.c μ i)) := by ring
    _ = _ := by rw [Units.inv_mul, mul_one]

private theorem left_cup_coeff (t : k) (ht : t ^ 2 = -1) (p q : ZMod 2) (c : kˣ) :
    (sign k (p + q) * (c : k)) *
      (sign k (q * p) * ((psiCoeff t p * sign k (p * (p + q))) *
        (psiCoeff t q * sign k ((p + q) * q)) * (↑c⁻¹ : k))) = psiCoeff t (p + q) := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
    simp [psiCoeff, show (1 : ZMod 2) + 1 = 0 from rfl]
  · calc
      _ = t * ((c : k) * ↑c⁻¹) := by ring
      _ = _ := by rw [Units.mul_inv, mul_one]
  · calc
      _ = t * ((c : k) * ↑c⁻¹) := by ring
      _ = _ := by rw [Units.mul_inv, mul_one]
  · calc
      _ = -(t ^ 2) * ((c : k) * ↑c⁻¹) := by ring
      _ = _ := by rw [ht, neg_neg, Units.mul_inv, mul_one]

private theorem left_cap_coeff (t : k) (ht : t ^ 2 = -1) (p q : ZMod 2) (c : kˣ) :
    (-(sign k q * (↑c⁻¹ : k))) *
      (sign k (p * q) * ((psiCoeff t q * sign k ((p + q) * (q + 1))) *
        (psiCoeff t p * sign k (p * (p + q))) * (-(sign k p) * (c : k)))) =
      psiCoeff t (p + q) * sign k (p + q) := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
    simp [psiCoeff, show (1 : ZMod 2) + 1 = 0 from rfl]
  · calc
      _ = t * ((↑c⁻¹ : k) * c) := by ring
      _ = _ := by rw [Units.inv_mul, mul_one]
  · calc
      _ = t * ((↑c⁻¹ : k) * c) := by ring
      _ = _ := by rw [Units.inv_mul, mul_one]
  · calc
      _ = -(t ^ 2) * ((↑c⁻¹ : k) * c) := by ring
      _ = _ := by rw [ht, neg_neg, Units.inv_mul, mul_one]

private theorem image_eta_nonpos (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i : I) (hh : D.h i μ ≤ 0) :
    psiLin (sy := sy) (hc := hc) t cs μ μ rfl (left_ud μ i) (etaPDiagram cs i μ) =
      psiLeftCupImage t μ i := by
  rw [etaPDiagram, ite_eq_right (by omega), map_smul, psiLin_dg,
    psiRaw_append t cs μ μ _ _ rfl (left_du μ i) (left_ud μ i)
      (sChain_etaL i _) (sChain_lcrossL i i), raw_etaL, raw_lcross]
  apply SOp.hom_ext
  rw [SOp.unsop_smul]
  rw [SOp.comp_of_mem (f := psiDottedCup (sy := sy) (hc := hc) cs t μ i (-D.h i μ).toNat)
    (g := psiSameLCross t μ i) (psiDottedCup_mem cs t ht μ i _) (psiSameLCross_mem_parity t μ i)]
  rw [psiDottedCup_raw cs t ht, psiSameLCross, psiRebase_unsop]
  change (_ : k) • ((_ : k) • (((psiCoeff t (D.parity i * D.parity i) *
    sign k (D.parity i * D.parity i * ipar D i μ)) • _) ≫
    ((_ : k) • psiSameCap cs i μ (-D.h i μ).toNat))) = _
  rw [Linear.smul_comp, Linear.comp_smul, psiSameCap, ← Category.assoc,
    cl_comp (sChain_sigmaL i i) (sChain_dR i _), sigma_dots_epsP_top cs i μ hh]
  simp only [smul_smul, zmod2_mul_self']
  change (_ : k) • _ = psiCoeff t (ipar D i μ) • _
  congr 1
  have hp : D.parity i + ((-D.h i μ).toNat : ZMod 2) * D.parity i = ipar D i μ := by
    rw [natCast_toNat_zmod _ (by omega)]
    simp only [Int.cast_neg, ipar]
    generalize D.parity i = p
    generalize (D.h i μ : ZMod 2) = q
    revert p q
    decide
  rw [← hp]
  simpa only [sign_eq_zsign, mul_assoc] using
    left_cup_coeff t ht (D.parity i) (((-D.h i μ).toNat : ZMod 2) * D.parity i) (cs.c μ i)

private theorem image_eps_nonneg (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i : I) (hh : 0 ≤ D.h i μ) :
    psiLin (sy := sy) (hc := hc) t cs μ μ (left_du μ i) rfl (epsPDiagram cs i μ) =
      psiLeftCapImage t μ i := by
  rw [epsPDiagram, ite_eq_right (by omega), map_smul, psiLin_dg,
    psiRaw_append t cs μ μ _ _ (left_du μ i) (left_ud μ i) rfl
      (sChain_lcrossL i i) (sChain_epsL i _), raw_lcross, raw_epsL]
  apply SOp.hom_ext
  rw [SOp.unsop_smul]
  rw [SOp.comp_of_mem (f := psiSameLCross (sy := sy) (hc := hc) t μ i)
    (g := psiDottedCap cs t μ i (D.h i μ).toNat)
    (psiSameLCross_mem_parity t μ i) (psiDottedCap_mem cs t ht μ i _)]
  rw [psiDottedCap_raw cs t ht, psiSameLCross, psiRebase_unsop]
  change (_ : k) • ((_ : k) • (((_ : k) • psiSameCup cs i μ (D.h i μ).toNat) ≫
    ((psiCoeff t (D.parity i * D.parity i) * sign k (D.parity i * D.parity i * ipar D i μ)) • _))) = _
  rw [Linear.smul_comp, Linear.comp_smul, psiSameCup, Category.assoc,
    cl_comp (sChain_dL i _) (sChain_sigmaL i i), etaP_dots_sigma_top cs i μ hh]
  simp only [smul_smul, zmod2_mul_self']
  change (_ : k) • _ = (psiCoeff t (ipar D i μ) * sign k (ipar D i μ)) • _
  congr 1
  have hq : D.parity i * (D.h i μ : ZMod 2) = ((D.h i μ).toNat : ZMod 2) * D.parity i := by
    rw [natCast_toNat_zmod _ hh, mul_comm]
  have hp : D.parity i + ((D.h i μ).toNat : ZMod 2) * D.parity i = ipar D i μ := by
    rw [← hq, ipar]; ring
  rw [hq, ← hp]
  simpa only [sign_eq_zsign, mul_assoc] using
    left_cap_coeff t ht (D.parity i) (((D.h i μ).toNat : ZMod 2) * D.parity i) (cs.c μ i)

/-- **Proposition 9.4, left cup calculation.** The seven-shape evaluation of
Definition 2.2's left cup is the right cap, scaled by `t^{|i,μ|}`. -/
theorem psiLin_etaP (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) :
    psiLin (sy := sy) (hc := hc) t cs μ μ rfl (left_ud μ i) (etaPDiagram cs i μ) =
      psiLeftCupImage t μ i := by
  rcases lt_or_ge 0 (D.h i μ) with hh | hh
  · exact image_eta_pos cs t μ i hh
  · exact image_eta_nonpos cs t ht μ i hh

/-- **Proposition 9.4, left cap calculation.** The seven-shape evaluation of
Definition 2.2's left cap is the right cup, scaled by `(-1)^{|i,μ|}t^{|i,μ|}`. -/
theorem psiLin_epsP (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) :
    psiLin (sy := sy) (hc := hc) t cs μ μ (left_du μ i) rfl (epsPDiagram cs i μ) =
      psiLeftCapImage t μ i := by
  rcases lt_or_ge (D.h i μ) 0 with hh | hh
  · exact image_eps_neg cs t μ i hh
  · exact image_eps_nonneg cs t ht μ i hh

end OddMath.SKM
