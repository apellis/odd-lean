/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.EvenBridge.KLInverse
import Categorification.Diagrams.KL3.SpanningBasic
import Categorification.Diagrams.KL3.Rewriting

/-!
# The cup and cap of an upward strand through the other generators of `U`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`* III, arXiv:0807.3250v1,
Definition 3.1. Write `n = ⟨i, λ⟩`. The cup `1_λ ⟶ E_i F_i 1_λ` and the cap
`F_i E_i 1_λ ⟶ 1_λ` of the upward strand can be written through dots, upward crossings, the cup
and cap of the downward strand, and the components of the inverse of the decomposition of
Proposition 3.25:

* `n ≥ 1`: the cup is `dcupEF (n - 1)` (`cupUp_eq_dcupEF`);
* `n ≤ 0`: the cup is `cupDotFE (-n) · crossr` (`cupUp_eq_cupDotFE_crossr`);
* `n ≤ -1`: the cap is `alphaFE 0` (`capUp_eq_alphaFE`);
* `n ≥ 0`: the cap is `-crossr · dotCapEF n` (`capUp_eq_crossr_dotCapEF`).

For `n ≤ 0` the proof inserts the decomposition `1 = -crossl · crossr` of `E_i F_i 1_λ`; the cup
followed by `crossl` is a right curl, and `curlR` (item iv) of Definition 3.1) expands it into
clockwise bubbles and dots. The bubble of degree zero is `1`; the other terms contain
`cupDotFE m · crossr` with `m < -n`, which vanishes (`cupDotFE_crossr`). The case `n ≥ 0` of the
cap is the mirror argument with the left curl and `crossr_dotCapEF`.

These identities show that the even-colour 2-functor of `OddMath.SKM.EvenBridge.Functor`, whose
images contain only the cups and caps of downward strands, is full.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k] (i : I) (lam : X)

/-! ## The cup of an upward strand -/

theorem cupUp_eq_dcupEF (h : 1 ≤ ip RD i lam) :
    dg RD k lam [] [up i, dn i] [([], .cup (up i), [])] =
      dcupEF RD k i lam ((ip RD i lam).toNat - 1) := by
  rw [dcupEF, show (ip RD i lam).toNat - ((ip RD i lam).toNat - 1) = 1 by omega,
    Finset.sum_range_one, Nat.cast_zero, add_zero, ccwU_deg0, Category.id_comp, add_zero, betaEF,
    show (ip RD i lam).toNat - 1 - ((ip RD i lam).toNat - 1) = 0 by omega]
  simp [cupDotEFLs]

/-- A clockwise bubble to the right of the upward strand of `cupDotFE a · crossr` is harmless:
the term vanishes for `a < -n`. -/
theorem ctx_cupDn_bub_eq_zero (γ : End ((pres RD k).obj (ob RD lam []))) (a : ℕ)
    (ha : a < (-ip RD i lam).toNat) :
    ctxL RD k lam [] [up i, dn i] [([], .cup (dn i), [])] [dn i] [] (crossrL i i) [up i] [up i]
      (bubRU RD k lam (up i) γ ≫ dotsU RD k lam (up i) a) = 0 := by
  have hγ := mem_span_dg RD k lam γ
  induction hγ using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨D, hD, rfl⟩ := hg
    have e₁ : bubRU RD k lam (up i) (dg RD k lam [] [] D) ≫ dotsU RD k lam (up i) a =
        dg RD k lam [up i] [up i]
          (D.map (whL [up i] []) ++ List.replicate a ([], .dot (up i), [])) := by
      rw [bubRU]
      erw [plcL_dg_nil RD k lam [up i] [] [] D]
      exact dg_comp (hD.whisk [up i] []) (by schain)
    rw [e₁, ctxL_dg_nil RD k lam (by schain) (by schain)]
    have e₂ := dg_closed_left (RD := RD) (k := k) lam [] (List.replicate a ([dn i], .dot (up i), []) ++
      crossrL i i) (s := []) (s' := [dn i, up i]) [] (S := []) (T := [up i, dn i])
      (A := [([], .cup (dn i), [])]) hD (by schain)
    simp only [map_whL_whL, whL_mk, List.map_cons, List.map_nil, List.map_append,
      List.cons_append, List.nil_append, List.append_nil,
      List.append_assoc, map_whL_nil_nil, List.map_replicate] at e₂ ⊢
    rw [e₂, ← dg_comp hD (by schain)]
    rw [show (([], Shape.cup (dn i), ([] : List (Letter I))) ::
          (List.replicate a ([dn i], Shape.dot (up i), []) ++ crossrL i i)) =
        cupDotFELs i a ++ crossrL i i by simp [cupDotFELs],
      ← dg_comp (t := [dn i, up i]) (by schain) (by schain)]
    erw [cupDotFE_crossr i lam a ha]
    rw [comp_zero]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [bubRU, map_add, Preadditive.add_comp] at hx hy ⊢
    rw [hx, hy, add_zero]
  | smul r x _ hx =>
    simp only [bubRU, map_smul, Linear.smul_comp] at hx ⊢
    rw [hx, smul_zero]

theorem cupUp_eq_cupDotFE_crossr (h : ip RD i lam ≤ 0) :
    dg RD k lam [] [up i, dn i] [([], .cup (up i), [])] =
      dg RD k lam [] [dn i, up i] (cupDotFELs i (-ip RD i lam).toNat) ≫
        dg RD k lam [dn i, up i] [up i, dn i] (crossrL i i) := by
  have hd := dg_decompEF (RD := RD) (k := k) i lam
  rw [show (ip RD i lam).toNat = 0 by omega, Finset.sum_range_zero, add_zero] at hd
  rw [← Category.comp_id (dg RD k lam [] [up i, dn i] [([], .cup (up i), [])]), ← dg_nil, hd,
    Preadditive.comp_neg, dg_comp (by schain) (by schain)]
  rw [neg_eq_iff_eq_neg]
  simp only [crosslL, crossrL, List.cons_append, List.nil_append]
  dswap 0
  rw [dg_stepL_at _ 1 [dn i] [] (dg_curlR (RD := RD) (k := k) i lam) (by (try dnorm); schain)
    (by (try dnorm); schain) (by dnorm)]
  simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    List.length_cons, List.length_nil]
  rw [show ([([dn i, up i], Shape.cup (up i), ([] : List (Letter I))),
      ([dn i], Shape.cross true i i, [dn i]), ([], Shape.cap (up i), [up i, dn i])] :
        List (LayerData I)) = crossrL i i from rfl]
  rw [map_neg, map_sum, neg_inj,
    show (-ip RD i lam + 1).toNat = (-ip RD i lam).toNat + 1 by omega, Finset.sum_range_succ']
  rw [Finset.sum_eq_zero fun f hf => ctx_cupDn_bub_eq_zero i lam _ _ (by
    rw [Finset.mem_range] at hf; omega), zero_add, Nat.cast_zero, add_zero, cwU_deg0,
    show bubRU RD k lam (up i) (𝟙 _) = 𝟙 _ by rw [bubRU, ← dg_nil]; erw [plcL_dg_nil]; exact dg_nil _ _,
    Category.id_comp, show (-ip RD i lam - 0) = -ip RD i lam by ring,
    ctxL_dg_nil RD k lam (by schain) (by schain), dg_comp (by schain) (by schain)]
  simp [cupDotFELs, crossrL]

/-! ## The cap of an upward strand -/

theorem capUp_eq_alphaFE :
    dg RD k lam [dn i, up i] [] [([], .cap (up i), [])] = alphaFE RD k i lam 0 := by
  rw [alphaFE, Finset.sum_range_one, Nat.cast_zero, add_zero, cwU_deg0, Category.comp_id]
  simp [dotCapFELs]

theorem ip_wt_dn_up (μ : X) : ip RD i (wt RD (wt RD μ [dn i]) [up i]) = ip RD i μ := by
  simp [ip, wt, sh, sgn]

/-- A counterclockwise bubble to the left of the upward strand of `crossr · dotCapEF b` is
harmless: the term vanishes for `b < n`. -/
theorem ctx_capDn_bub_eq_zero
    (β : End ((pres RD k).obj (ob RD (wt RD (wt RD lam [dn i]) [up i]) []))) (b : ℕ)
    (hb : b < (ip RD i lam).toNat) :
    ctxL RD k lam [dn i, up i] [] (crossrL i i) [] [dn i] [([], .cap (dn i), [])] [up i] [up i]
      (bubLU RD k (wt RD lam [dn i]) (up i) β ≫ dotsU RD k (wt RD lam [dn i]) (up i) b) = 0 := by
  have hβ := mem_span_dg RD k _ β
  induction hβ using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨D, hD, rfl⟩ := hg
    have e₁ : bubLU RD k (wt RD lam [dn i]) (up i) (dg RD k _ [] [] D) ≫
        dotsU RD k (wt RD lam [dn i]) (up i) b =
        dg RD k (wt RD lam [dn i]) [up i] [up i]
          (D.map (whL [] [up i]) ++ List.replicate b ([], .dot (up i), [])) := by
      rw [bubLU, plcL_dg]
      exact dg_comp (hD.whisk [] [up i]) (by schain)
    rw [e₁, ctxL_dg RD k lam (by schain) (by schain)]
    have e₂ := dg_closed_right (RD := RD) (k := k) lam (crossrL i i) [] []
      (t := [up i, dn i]) (t' := []) (S := [dn i, up i]) (T := [])
      (A := dotCapEFLs i b) hD (by schain)
    simp only [map_whL_whL, whL_mk, List.map_cons, List.map_nil, List.map_append,
      List.cons_append, List.nil_append, List.append_nil,
      List.append_assoc, map_whL_nil_nil, List.map_replicate, dotCapEFLs] at e₂ ⊢
    rw [e₂, show crossrL i i ++ (List.replicate b ([], Shape.dot (up i), [dn i]) ++
          ([], Shape.cap (dn i), ([] : List (Letter I))) :: D) =
        (crossrL i i ++ dotCapEFLs i b) ++ D by simp [dotCapEFLs],
      ← dg_comp (t := []) (by schain) hD, ← dg_comp (t := [up i, dn i]) (by schain) (by schain)]
    erw [crossr_dotCapEF i lam b hb]
    rw [zero_comp]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [bubLU, map_add, Preadditive.add_comp] at hx hy ⊢
    rw [hx, hy, add_zero]
  | smul r x _ hx =>
    simp only [bubLU, map_smul, Linear.smul_comp] at hx ⊢
    rw [hx, smul_zero]

theorem capUp_eq_crossr_dotCapEF (h : 0 ≤ ip RD i lam) :
    dg RD k lam [dn i, up i] [] [([], .cap (up i), [])] =
      -(dg RD k lam [dn i, up i] [up i, dn i] (crossrL i i) ≫
        dg RD k lam [up i, dn i] [] (dotCapEFLs i (ip RD i lam).toNat)) := by
  have hd := dg_decompFE (RD := RD) (k := k) i lam
  rw [show (-ip RD i lam).toNat = 0 by omega, Finset.sum_range_zero, add_zero] at hd
  rw [← Category.id_comp (dg RD k lam [dn i, up i] [] [([], .cap (up i), [])]), ← dg_nil, hd,
    Preadditive.neg_comp, dg_comp (by schain) (by schain), neg_inj]
  simp only [crosslL, crossrL, List.cons_append, List.nil_append]
  dswap 5
  rw [dg_stepL_at _ 3 [] [dn i] (dg_curlL (RD := RD) (k := k) i (wt RD lam [dn i]))
    (by (try dnorm); schain) (by (try dnorm); schain) (by dnorm)]
  simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    List.length_cons, List.length_nil]
  rw [show ([([dn i, up i], Shape.cup (up i), ([] : List (Letter I))),
      ([dn i], Shape.cross true i i, [dn i]), ([], Shape.cap (up i), [up i, dn i])] :
        List (LayerData I)) = crossrL i i from rfl]
  have hρ := ip_wt_dn_up (RD := RD) i lam
  rw [map_sum, show (ip RD i (wt RD (wt RD lam [dn i]) [up i]) + 1).toNat =
      (ip RD i (wt RD (wt RD lam [dn i]) [up i])).toNat + 1 by omega, Finset.sum_range_succ']
  rw [Finset.sum_eq_zero fun g hg => ctx_capDn_bub_eq_zero i lam _ _ (by
    rw [Finset.mem_range] at hg; omega), zero_add, Nat.cast_zero, add_zero, ccwU_deg0,
    show bubLU RD k (wt RD lam [dn i]) (up i) (𝟙 _) = 𝟙 _ by
      rw [bubLU, ← dg_nil, plcL_dg]; exact dg_nil _ _,
    Category.id_comp, sub_zero, hρ, ctxL_dg RD k lam (by schain) (by schain),
    dg_comp (by schain) (by schain)]
  simp [dotCapEFLs, crossrL]

end Categorification.KL3.Diagram
