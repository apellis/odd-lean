/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyInv
import OddMath.SKM.LeftAdj2

/-!
# The left adjunction on `Fᵢ` (Brundan–Ellis, Proposition 6.2, second relation)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 6.2, the
second relation of (6.6), which the paper deduces from the first one by the Chevalley involution
(Proposition 3.5).

* `Om μ s t f`: the image under `ω` of a 2-morphism `f : E_s 1_μ ⟶ E_t 1_μ`, as a 2-morphism
  `E_{flip t} 1_{-μ} ⟶ E_{flip s} 1_{-μ}` (the two `eqToHom`s of `omega_obj` removed);
  `Om_cl`, `Om_add`, `Om_smul`, `Om_id`.
* `eq_6_6_b`: on `Fᵢ 1_λ`, `η'` (at `λ`) on the right followed by `ε'` (at `λ - αᵢ`) on the left is
  the identity: the image under `ω` of the first relation (`eq_6_6_a`) at `-λ`, computed case by case
  on normal-form diagrams (`eq_6_6_b_m1`, `eq_6_6_b_nonneg`, `eq_6_6_b_le` for `⟨hᵢ,λ⟩ = -1`,
  `≥ 0`, `≤ -2`, stated at `-λ`); the dots produced by `ω` are straightened by (2.3).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation Supercategory Finset

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

variable (D Sc) in
/-- The image under `ω` of a 2-morphism between normal-form objects. -/
def Om (μ : X) (s t : List (Letter I))
    (f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :
    (pres D Sc).obj (ob D (-μ) (flipW t)) ⟶ (pres D Sc).obj (ob D (-μ) (flipW s)) :=
  eqToHom (congrArg (pres D Sc).obj (chevMap_obj D μ t)).symm ≫ SOp.unsop ((omega Sc).map f) ≫
    eqToHom (congrArg (pres D Sc).obj (chevMap_obj D μ s))

theorem Om_cl (μ : X) {s t : List (Letter I)} {L : List (LayerData I)} (h : SChain s L t) :
    Om D Sc μ s t (cl D Sc μ s t L) = omegaC D k L • cl D Sc (-μ) (flipW t) (flipW s) (omegaL L) := by
  rw [Om, omega_cl μ h]
  simp

theorem Om_add (μ : X) (s t : List (Letter I))
    (f g : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :
    Om D Sc μ s t (f + g) = Om D Sc μ s t f + Om D Sc μ s t g := by
  simp [Om, Functor.map_add]

theorem Om_smul (μ : X) (s t : List (Letter I)) (a : k)
    (f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :
    Om D Sc μ s t (a • f) = a • Om D Sc μ s t f := by
  simp [Om, Functor.map_smul]

theorem Om_id (μ : X) (s : List (Letter I)) :
    Om D Sc μ s s (𝟙 _) = 𝟙 _ := by
  rw [← cl_nil μ s, Om_cl μ (SChain.nil' s), omegaC_nil, one_smul]
  exact cl_nil (-μ) (flipW s)


theorem zsign_one' : zsign k (1 : ZMod 2) = -1 := by simp [zsign]

theorem neg_zsign' (a : ZMod 2) : -zsign k a = zsign k (a + 1) := by
  rw [zsign_add, zsign_one', mul_neg_one]

theorem zsign_smul_cancel {A : Type*} [AddCommGroup A] [Module k A] {S T : ZMod 2} {f g : A}
    (h : zsign k S • f = zsign k T • g) : f = zsign k (S + T) • g := by
  rw [zsign_add, mul_smul, ← h, smul_smul, zsign_mul_self', one_smul]

theorem zsign_smul_of {A : Type*} [AddCommGroup A] [Module k A] {S T U : ZMod 2} {f g : A}
    (h : zsign k S • f = zsign k T • g) (hU : U + (S + T) = 0) : zsign k U • f = g := by
  rw [zsign_smul_cancel h, smul_smul, ← zsign_add, hU, zsign_zero, one_smul]

theorem natCast_toNat_zmod2 {a : ℤ} (ha : 0 ≤ a) : ((a.toNat : ℕ) : ZMod 2) = (a : ZMod 2) := by
  conv_rhs => rw [← Int.toNat_of_nonneg ha]
  push_cast; rfl

/-! ## The second relation of (6.6) -/

variable (cs : CScalars Sc)

/-- `η'` (at `λ`) to the right of `Fᵢ 1_λ`. -/
def retaF (i : I) (μ : X) :
    (pres D Sc).obj (ob D μ [dn i]) ⟶ (pres D Sc).obj (ob D μ [dn i, up i, dn i]) :=
  plcL D Sc μ [dn i] [] [] [up i, dn i] (etaP cs i (wt D μ []))

/-- `ε'` (at `λ - αᵢ`) on the two left strands of `Fᵢ Eᵢ Fᵢ 1_λ`. -/
def lepsF (i : I) (μ : X) :
    (pres D Sc).obj (ob D μ [dn i, up i, dn i]) ⟶ (pres D Sc).obj (ob D μ [dn i]) :=
  plcL D Sc μ [] [dn i] [dn i, up i] [] (epsP cs i (wt D μ [dn i]))

theorem c_neg_wt_dn (i : I) (μ : X) : cs.c (wt D (-μ) [dn i]) i = cs.c (-μ) i := by
  have := cs.shift (wt D (-μ) [dn i]) i i
  rw [Sc.t_self, one_mul] at this
  rw [← this]
  congr 1
  simp [wt, sh]

theorem h_wt_dn (i : I) (μ : X) : D.h i (wt D μ [dn i]) = D.h i μ - 2 := by
  simp [wt, sh, Datum.h, Datum.α, map_add, map_neg, D.cd.coroot_root_self]; ring

/-- The second relation of (6.6) at `-μ`, for `⟨hᵢ,μ⟩ = -1`. -/
theorem eq_6_6_b_m1 (i : I) (μ : X) (hh : D.h i μ = -1) :
    retaF cs i (-μ) ≫ lepsF cs i (-μ) = 𝟙 _ := by
  have hν : D.h i (wt D μ [up i]) = 1 := by rw [h_wt_up]; omega
  -- the first relation at `μ`, in normal form
  have E := eq_6_6_a cs i μ
  have e1 : leta cs i μ = (cs.c μ i : k) •
      cl D Sc μ [up i] [up i, dn i, up i] [([], Shape.dcup i 0, [up i])] := by
    rw [leta, etaP_of_pos cs (by omega), map_smul, plcL_cl, c_wt_up, hν]
    rfl
  have e2 : reps cs i μ = (↑(cs.c μ i)⁻¹ : k) •
      cl D Sc μ [up i, dn i, up i] [up i] [([up i], Shape.dcap i 0, [])] := by
    rw [reps, epsP_of_neg cs (show D.h i (wt D μ []) < 0 by simp only [wt_nil]; omega), map_smul,
      plcL_cl, show (-D.h i (wt D μ []) - 1).toNat = 0 by simp only [wt_nil]; omega]
    rfl
  rw [e1, e2, Linear.smul_comp, Linear.comp_smul, smul_smul, Units.mul_inv, one_smul,
    cl_comp (by simp [Shape.dom, Shape.cod]) (by simp [Shape.dom, Shape.cod]),
    ipar, hh, show ((-1 : ℤ) : ZMod 2) + 1 = 0 by push_cast; rfl, mul_zero, zsign_zero,
    one_smul, ← cl_nil μ [up i]] at E
  have E' := congrArg (Om D Sc μ [up i] [up i]) E
  rw [Om_cl μ (by simp [Shape.dom, Shape.cod]), Om_cl μ (SChain.nil' _)] at E'
  simp only [omegaL, omegaC_cons, omegaC_nil, chevL, chevC, dcupL, dcapL, List.map_cons,
    List.map_nil, whL, flipW_cons, flipW_nil, flipL_up, List.nil_append, List.append_nil,
    List.singleton_append, Shape.parity, parsum_cons, parsum_nil, Nat.cast_zero, mul_zero,
    zero_mul, zsign_zero, mul_one, one_smul, cl_nil] at E'
  have h' : D.h i (wt D (-μ) []) = 1 := by simp only [wt_nil, coroot_neg]; omega
  have h'' : D.h i (wt D (-μ) [dn i]) = -1 := by rw [h_wt_dn]; simp only [coroot_neg]; omega
  rw [retaF, lepsF, etaP_of_pos cs (by omega), epsP_of_neg cs (by omega), map_smul, map_smul,
    plcL_cl, plcL_cl, Linear.smul_comp, Linear.comp_smul, smul_smul, c_neg_wt_dn,
    show cs.c (wt D (-μ) []) i = cs.c (-μ) i from rfl, Units.mul_inv, one_smul, h', h'',
    show (-(-1 : ℤ) - 1).toNat = 0 by rfl, show ((1 : ℤ) - 1).toNat = 0 by rfl]
  change cl D Sc (-μ) [dn i] [dn i, up i, dn i] [([dn i], Shape.dcup i 0, [])] ≫
    cl D Sc (-μ) [dn i, up i, dn i] [dn i] [([], Shape.dcap i 0, [dn i])] = _
  rw [cl_comp (by simp [Shape.dom, Shape.cod]) (by simp [Shape.dom, Shape.cod])]
  exact E'

/-- The second relation of (6.6) at `-μ`, for `⟨hᵢ,μ⟩ ≥ 0`. -/
theorem eq_6_6_b_nonneg (i : I) (μ : X) (hh : 0 ≤ D.h i μ) :
    retaF cs i (-μ) ≫ lepsF cs i (-μ) = 𝟙 _ := by
  have hν : 0 < D.h i (wt D μ [up i]) := by rw [h_wt_up]; omega
  set n := (D.h i (wt D μ [up i]) - 1).toNat with hn
  set N := (D.h i μ).toNat with hN
  have E := eq_6_6_a cs i μ
  have e1 : leta cs i μ = (cs.c μ i : k) •
      cl D Sc μ [up i] [up i, dn i, up i] [([], Shape.dcup i n, [up i])] := by
    rw [leta, etaP_of_pos cs hν, map_smul, plcL_cl, c_wt_up]
    rfl
  have e2 : reps cs i μ = (-(zsign k (D.parity i * (D.h i μ : ZMod 2))) * (↑(cs.c μ i)⁻¹ : k)) •
      cl D Sc μ [up i, dn i, up i] [up i] ((lcrossL i i ++ epsL i N).map (whL [up i] [])) := by
    rw [reps, epsP_eq_of_nonneg cs (show 0 ≤ D.h i (wt D μ []) from hh), map_smul, plcL_cl]
    rfl
  have hA : SChain [up i] [([], Shape.dcup i n, [up i])] [up i, dn i, up i] := by
    simp [Shape.dom, Shape.cod]
  have hB : SChain [up i, dn i, up i] ((lcrossL i i ++ epsL i N).map (whL [up i] [])) [up i] := by
    simpa using ((sChain_lcrossL i i).append (sChain_epsL i N)).whisk [up i] []
  rw [e1, e2, Linear.smul_comp, Linear.comp_smul, smul_smul,
    cl_comp hA hB, ← cl_nil μ [up i]] at E
  have E' := congrArg (Om D Sc μ [up i] [up i]) E
  rw [Om_smul, Om_smul, Om_cl μ (hA.append hB), Om_cl μ (SChain.nil' _)] at E'
  simp only [omegaL_append, omegaL_map_whL, omegaL_lcrossL, omegaL_epsL, omegaL_cons, omegaL_nil,
    chevL, List.nil_append, flipW_cons, flipW_nil, flipL_up, omegaC_append,
    omegaC_map_whL, omegaC_lcrossL, omegaC_epsL, omegaC_cons, omegaC_nil, cl_nil] at E'
  -- split off the cup with dots, and straighten the dots by (2.3)
  set Q : List (LayerData I) := (lcrossL i i).map (whL [dn i] []) ++ (dcapL i n).map (whL [] [dn i])
    with hQ
  have hQs : SChain [dn i, dn i, up i] Q [dn i] := by
    simp [hQ, lcrossL, dcapL, whL, Shape.dom, Shape.cod]
  have split : ∀ P : List (LayerData I), SChain [] P [dn i, up i] →
      cl D Sc (-μ) [dn i] [dn i] (P.map (whL [dn i] []) ++ Q) =
        plcL D Sc (-μ) [dn i] [] [] [dn i, up i] (cl D Sc (-μ) [] [dn i, up i] P) ≫
          cl D Sc (-μ) [dn i, dn i, up i] [dn i] Q := by
    intro P hP
    have e := plcL_cl (D := D) (Sc := Sc) (-μ) [dn i] [] [] [dn i, up i] P
    exact (cl_comp (by simpa using hP.whisk [dn i] []) hQs).symm.trans
      (congrArg (· ≫ cl D Sc (-μ) [dn i, dn i, up i] [dn i] Q) e.symm)
  have hL : List.map (whL [dn i] []) ((([], Shape.cup i, []) :: (ddotsL i N).map (whL [] [up i])) ++
      lcrossL i i) ++ (dcapL i n).map (whL [] [dn i]) =
      (([], Shape.cup i, []) :: (ddotsL i N).map (whL [] [up i])).map (whL [dn i] []) ++ Q := by
    rw [hQ, List.map_append, List.append_assoc]
  rw [hL, split _ (sChain_cupDots i N), cl_cupDots,
    map_smul, Linear.smul_comp, ← split _ (sChain_etaL i N)] at E'
  -- the left-hand side at `-μ`
  have h1 : D.h i (wt D (-μ) []) ≤ 0 := by rw [wt_nil, coroot_neg]; omega
  have h2 : D.h i (wt D (-μ) [dn i]) < 0 := by rw [h_wt_dn, coroot_neg]; omega
  have hN' : (-D.h i (wt D (-μ) [])).toNat = N := by rw [wt_nil, coroot_neg, neg_neg]
  have hn' : (-D.h i (wt D (-μ) [dn i]) - 1).toNat = n := by
    rw [hn, h_wt_dn, coroot_neg, h_wt_up]; congr 1; ring
  rw [retaF, lepsF, etaP_eq_of_nonpos cs h1, epsP_of_neg cs h2, map_smul, map_smul,
    Linear.smul_comp, Linear.comp_smul, smul_smul, hN', hn', plcL_cl, plcL_cl]
  change _ • (cl D Sc (-μ) [dn i] [dn i, up i, dn i] _ ≫ cl D Sc (-μ) [dn i, up i, dn i] [dn i] _) = _
  rw [cl_comp (by simpa using ((sChain_etaL i N).append (sChain_lcrossL i i)).whisk [dn i] [])
    (by simp [dcapL, whL, Shape.dom, Shape.cod]),
    show List.map (whL [dn i] []) (etaL i N ++ lcrossL i i) ++ List.map (whL [] [dn i]) (dcapL i n) =
      List.map (whL [dn i] []) (etaL i N) ++ Q by rw [hQ, List.map_append, List.append_assoc]]
  -- the scalars
  rw [c_neg_wt_dn, show cs.c (wt D (-μ) []) i = cs.c (-μ) i from rfl, mul_assoc, Units.mul_inv,
    mul_one]
  rw [show (cs.c μ i : k) * (-zsign k (D.parity i * ↑(D.h i μ)) * ↑(cs.c μ i)⁻¹) =
    -zsign k (D.parity i * ↑(D.h i μ)) by rw [mul_comm, mul_assoc, Units.inv_mul, mul_one],
    smul_smul, smul_smul, one_smul] at E'
  simp only [parsum_cons, parsum_nil, parsum_map_whL, parsum_append, parsum_lcrossL, parsum_epsL,
    Shape.parity, chevC, mul_zero, zsign_zero, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    add_zero] at E'
  simp only [← zsign_add] at E'
  refine zsign_smul_of E' ?_
  have hn2 : (n : ZMod 2) = (D.h i μ : ZMod 2) + 1 := by
    rw [hn, natCast_toNat_zmod2 (by omega), h_wt_up]; push_cast; ring_nf
  have hN2 : (N : ZMod 2) = (D.h i μ : ZMod 2) := by rw [hN, natCast_toNat_zmod2 hh]
  rw [hn2, hN2, ipar, ipar, wt_nil, coroot_neg]
  push_cast
  generalize D.parity i = p
  generalize ((D.h i μ : ℤ) : ZMod 2) = q
  generalize ((N / 2 : ℕ) : ZMod 2) = r
  revert p q r; decide

/-- The second relation of (6.6) at `-μ`, for `⟨hᵢ,μ⟩ ≤ -2`. -/
theorem eq_6_6_b_le (i : I) (μ : X) (hh : D.h i μ ≤ -2) :
    retaF cs i (-μ) ≫ lepsF cs i (-μ) = 𝟙 _ := by
  have hν : D.h i (wt D μ [up i]) ≤ 0 := by rw [h_wt_up]; omega
  set M := (-D.h i (wt D μ [up i])).toNat with hM
  set m := (-D.h i (wt D μ []) - 1).toNat with hm
  have E := eq_6_6_a cs i μ
  have e1 : leta cs i μ = (zsign k (ipar D i (wt D μ [up i])) * (cs.c μ i : k)) •
      cl D Sc μ [up i] [up i, dn i, up i] ((etaL i M ++ lcrossL i i).map (whL [] [up i])) := by
    rw [leta, etaP_eq_of_nonpos cs hν, map_smul, plcL_cl, c_wt_up]
    rfl
  have e2 : reps cs i μ = (↑(cs.c μ i)⁻¹ : k) •
      cl D Sc μ [up i, dn i, up i] [up i] ((dcapL i m).map (whL [up i] [])) := by
    rw [reps, epsP_of_neg cs (show D.h i (wt D μ []) < 0 by rw [wt_nil]; omega), map_smul, plcL_cl]
    rfl
  have hA : SChain [up i] ((etaL i M ++ lcrossL i i).map (whL [] [up i])) [up i, dn i, up i] := by
    simpa using ((sChain_etaL i M).append (sChain_lcrossL i i)).whisk [] [up i]
  have hB : SChain [up i, dn i, up i] ((dcapL i m).map (whL [up i] [])) [up i] := by
    simp [dcapL, whL, Shape.dom, Shape.cod]
  rw [e1, e2, Linear.smul_comp, Linear.comp_smul, smul_smul, cl_comp hA hB, ← cl_nil μ [up i]] at E
  have E' := congrArg (Om D Sc μ [up i] [up i]) E
  rw [Om_smul, Om_smul, Om_cl μ (hA.append hB), Om_cl μ (SChain.nil' _)] at E'
  simp only [omegaL_append, omegaL_map_whL, omegaL_lcrossL, omegaL_etaL, omegaL_dcapL,
    flipW_cons, flipW_nil, flipL_up, omegaC_append, omegaC_map_whL, omegaC_lcrossL, omegaC_etaL,
    omegaC_dcapL, omegaC_nil, omegaL_nil, cl_nil, one_smul] at E'
  -- split off the cap with dots, and straighten the dots by (2.3)
  set R : List (LayerData I) := (dcupL i m).map (whL [dn i] []) ++ (lcrossL i i).map (whL [] [dn i])
    with hR
  have hRs : SChain [dn i] R [up i, dn i, dn i] := by
    simp [hR, lcrossL, dcupL, whL, Shape.dom, Shape.cod]
  have split : ∀ P : List (LayerData I), SChain [up i, dn i] P [] →
      cl D Sc (-μ) [dn i] [dn i] (R ++ P.map (whL [] [dn i])) =
        cl D Sc (-μ) [dn i] [up i, dn i, dn i] R ≫
          plcL D Sc (-μ) [] [dn i] [up i, dn i] [] (cl D Sc (wt D (-μ) [dn i]) [up i, dn i] [] P) := by
    intro P hP
    have e := plcL_cl (D := D) (Sc := Sc) (-μ) [] [dn i] [up i, dn i] [] P
    exact (cl_comp hRs (by simpa using hP.whisk [] [dn i])).symm.trans
      (congrArg (cl D Sc (-μ) [dn i] [up i, dn i, dn i] R ≫ ·) e.symm)
  have hL : (dcupL i m).map (whL [dn i] []) ++ (lcrossL i i ++ ((ddotsL i M).map (whL [up i] []) ++
      [([], Shape.cap i, [])])).map (whL [] [dn i]) =
      R ++ ((ddotsL i M).map (whL [up i] []) ++ [([], Shape.cap i, [])]).map (whL [] [dn i]) := by
    rw [hR, List.map_append, List.append_assoc]
  rw [hL, split _ (sChain_dotsCap i M), cl_dotsCap, map_smul, Linear.comp_smul,
    ← split _ (sChain_epsL i M)] at E'
  -- the left-hand side at `-μ`
  have h1 : 0 < D.h i (wt D (-μ) []) := by rw [wt_nil, coroot_neg]; omega
  have h2 : 0 ≤ D.h i (wt D (-μ) [dn i]) := by rw [h_wt_dn, coroot_neg]; omega
  have hM' : (D.h i (wt D (-μ) [dn i])).toNat = M := by
    rw [hM, h_wt_dn, coroot_neg, h_wt_up]; congr 1; ring
  have hm' : (D.h i (wt D (-μ) []) - 1).toNat = m := by
    rw [hm, wt_nil, wt_nil, coroot_neg]
  rw [retaF, lepsF, etaP_of_pos cs h1, epsP_eq_of_nonneg cs h2, map_smul, map_smul,
    Linear.smul_comp, Linear.comp_smul, smul_smul, hM', hm', plcL_cl, plcL_cl]
  change _ • (cl D Sc (-μ) [dn i] [dn i, up i, dn i] _ ≫ cl D Sc (-μ) [dn i, up i, dn i] [dn i] _) = _
  rw [cl_comp (by simp [dcupL, whL, Shape.dom, Shape.cod])
    (by simpa using ((sChain_lcrossL i i).append (sChain_epsL i M)).whisk [] [dn i]),
    show List.map (whL [dn i] []) (dcupL i m) ++ List.map (whL [] [dn i]) (lcrossL i i ++ epsL i M) =
      R ++ List.map (whL [] [dn i]) (epsL i M) by rw [hR, List.map_append, List.append_assoc]]
  rw [c_neg_wt_dn, show cs.c (wt D (-μ) []) i = cs.c (-μ) i from rfl, mul_comm, mul_assoc,
    Units.inv_mul, mul_one, neg_zsign']
  rw [mul_assoc, Units.mul_inv, mul_one, smul_smul, smul_smul] at E'
  simp only [parsum_map_whL, parsum_append, parsum_lcrossL, parsum_etaL, parsum_dcapL, mul_one,
    neg_mul, mul_neg] at E'
  simp only [← zsign_add] at E'
  simp only [neg_zsign'] at E'
  refine zsign_smul_of E' ?_
  have hM2 : (M : ZMod 2) = (D.h i μ : ZMod 2) := by
    rw [hM, natCast_toNat_zmod2 (by omega), h_wt_up]; push_cast
    generalize ((D.h i μ : ℤ) : ZMod 2) = q; revert q; decide
  have hm2 : (m : ZMod 2) = (D.h i μ : ZMod 2) + 1 := by
    rw [hm, natCast_toNat_zmod2 (by rw [wt_nil]; omega), wt_nil]; push_cast
    generalize ((D.h i μ : ℤ) : ZMod 2) = q; revert q; decide
  rw [hM2, hm2, ipar, ipar, h_wt_dn, h_wt_up, coroot_neg]
  push_cast
  generalize D.parity i = p
  generalize ((D.h i μ : ℤ) : ZMod 2) = q
  generalize ((M / 2 : ℕ) : ZMod 2) = r
  revert p q r; decide

/-- **Brundan–Ellis, Proposition 6.2, second relation of (6.6).** On `Fᵢ 1_λ`, `η'` (at `λ`) on the
right followed by `ε'` (at `λ - αᵢ`) on the left is the identity. -/
theorem eq_6_6_b (i : I) (μ : X) : retaF cs i μ ≫ lepsF cs i μ = 𝟙 _ := by
  have key : retaF cs i (-(-μ)) ≫ lepsF cs i (-(-μ)) = 𝟙 _ := by
    rcases lt_trichotomy (D.h i (-μ)) (-1) with h | h | h
    · exact eq_6_6_b_le cs i (-μ) (by omega)
    · exact eq_6_6_b_m1 cs i (-μ) h
    · exact eq_6_6_b_nonneg cs i (-μ) (by omega)
  rwa [neg_neg] at key

end OddMath.SKM
