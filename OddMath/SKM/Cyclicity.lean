/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.LeftDot
import OddMath.SKM.ChevalleyLeft
import OddMath.SKM.OddBubbleCentrality
import OddMath.SKM.PitchforkRot

/-!
# Cyclicity of dots and crossings (Brundan–Ellis (1.26)–(1.28))

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, (1.26)–(1.28).

The downward dot and crossing of Definition 2.1 are the right mates of the upward ones, taken
with the rightward cups `η` and caps `ε` (`ddotL`, `dcrossL`). The intro equations (1.26)–(1.28)
compare them with the mates taken with the leftward cups `η'` and caps `ε'` of Definition 2.2
(`ldot`, `lcrossMate`). The paper states them in the introduction; they follow from the left
adjunction (6.6), the leftward dot slides (4.3) and the pitchfork relations (7.5), (7.6).

* `eq_1_26`: for even `i` the two downward dots agree;
* `eq_1_27`: for odd `i` the right mate of the dot is twice the odd bubble (2.18), in the region
  to the left of the strand, minus the left mate. As printed.
* `eq_1_28`: the left mate of the upward crossing `τ : Eᵢ Eⱼ → Eⱼ Eᵢ` (cups of colours `i`
  outside and `j` inside, the outer cup lowest and the outer cap highest, as in the picture) is
  `(-1)^{|i||j|(⟨hᵢ,λ⟩ + ⟨hⱼ,λ⟩ + 1)}` times the right mate. The printed relation has no sign:
  it holds when `i` or `j` is even (`eq_1_28_of_even`); for `i = j` the sign is `(-1)^{|i|}`
  (`eq_1_28_self`, the correction recorded in Brundan–Kleshchev, arXiv:2203.14149v3, (13.18));
  as printed it would force `1 = 0` on `Fᵢ Fᵢ 1_λ` for odd `i` (`eq_1_28_printed_self_odd`), and
  for odd `i ≠ j` the downward crossing to vanish where `⟨hᵢ,λ⟩ + ⟨hⱼ,λ⟩` is even
  (`eq_1_28_printed_odd`). See ERRATA [BE2] 3.

For the dots: (4.3) with `n = 1`, the super interchange of the dot with `η'` and the left
adjunction (6.6) on `Fᵢ`; for odd `i` the sign `(-1)^{⟨hᵢ,λ⟩}` of (4.3) and the interchange sign
`(-1)^{|i||i,λ|}` multiply to `-1` at every weight. For the crossing: rotating `τ` by the inner
cup and cap gives `(-1)^{|i||j||j,λ|}` times the leftward crossing (`rot_tau_left`, from (7.5) and
(6.6)); the pitchfork relation (7.6) turns the leftward crossing on the outer cup into
`(-1)^{|i||j|}` times the downward crossing, and the super interchange with the outer cap gives
`(-1)^{|i||j||i,λ|}`.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- The downward dot on `Fᵢ 1_λ` defined by the left adjunction: `η'` (at `λ`) to the right of the
strand, the upward dot on the middle strand of `Fᵢ Eᵢ Fᵢ`, then `ε'` (at `λ - αᵢ`) on the two left
strands. The right-hand pictures of (1.26), (1.27). -/
def ldot (i : I) (μ : X) : (pres D Sc).obj (ob D μ [dn i]) ⟶ (pres D Sc).obj (ob D μ [dn i]) :=
  retaF cs i μ ≫ cl D Sc μ [dn i, up i, dn i] [dn i, up i, dn i] (dotsL [dn i] i [dn i] 1) ≫
    lepsF cs i μ

/-- The odd bubble (2.18) in the region to the left of `Fᵢ 1_λ` (of weight `λ - αᵢ`). -/
def obLeft (i : I) (μ : X) : (pres D Sc).obj (ob D μ [dn i]) ⟶ (pres D Sc).obj (ob D μ [dn i]) :=
  plcL D Sc μ [] [dn i] [] [] (oddBubble cs i (wt D μ [dn i]))

/-- The upward dot on the middle strand followed by `ε'` is `ε'` with the dot on its right leg,
placed to the left of `Fᵢ`. -/
theorem mid_dot_lepsF (i : I) (μ : X) :
    cl D Sc μ [dn i, up i, dn i] [dn i, up i, dn i] (dotsL [dn i] i [dn i] 1) ≫ lepsF cs i μ =
      plcL D Sc μ [] [dn i] [dn i, up i] []
        (uRM D Sc i (wt D μ [dn i]) ≫ epsP cs i (wt D μ [dn i])) := by
  rw [plcL_comp_of_mem μ [] [dn i]
    (cl_mem_homPar (s := [dn i, up i]) (t := [dn i, up i]) (sChain_dotsL [dn i] i [] 1) rfl)
    (epsP_mem cs i _), plcL_cl]
  simp [dotsL, whL, lepsF]

/-- The downward dot on the left leg of `ε'`, placed to the left of `Fᵢ`, followed by `ε'`. -/
theorem plcL_dL_eps (i : I) (μ : X) :
    plcL D Sc μ [] [dn i] [dn i, up i] []
        (dLM D Sc i (wt D μ [dn i]) ≫ epsP cs i (wt D μ [dn i])) =
      cl D Sc μ [dn i, up i, dn i] [dn i, up i, dn i]
          ((ddotL i).map (whL [] [up i, dn i])) ≫ lepsF cs i μ := by
  rw [plcL_comp_of_mem μ [] [dn i] (cl_mem_homPar (sChain_ddotL' i) rfl)
    (epsP_mem cs i _), plcL_cl, map_whL_map_whL]
  rfl

/-- `ε'` followed by the odd bubble, placed to the left of `Fᵢ`. -/
theorem plcL_eps_ob (i : I) (μ : X) :
    plcL D Sc μ [] [dn i] [dn i, up i] []
        (epsP cs i (wt D μ [dn i]) ≫ oddBubble cs i (wt D μ [dn i])) =
      lepsF cs i μ ≫ obLeft cs i μ := by
  rw [plcL_comp_of_mem μ [] [dn i] (epsP_mem cs i _) (oddBubble_mem cs i _)]
  rfl

/-- The super interchange of `η'` (to the right of `Fᵢ`) with the downward dot on `Fᵢ`. -/
theorem retaF_ddot (i : I) (μ : X) :
    retaF cs i μ ≫ cl D Sc μ [dn i, up i, dn i] [dn i, up i, dn i]
        ((ddotL i).map (whL [] [up i, dn i])) =
      zsign k (ipar D i μ * D.parity i) •
        (cl D Sc μ [dn i] [dn i] (ddotL i) ≫ retaF cs i μ) := by
  have hp : parsum D (ddotL i) = D.parity i := by
    rw [← ddotsL_one, parsum_ddotsL, Nat.cast_one, one_mul]
  have E := plcL_right_interchange (D := D) (Sc := Sc) μ [dn i] (s := []) (t := [up i, dn i])
    (etaP_mem cs i (wt D μ [])) (sChain_ddotL i)
  rw [hp] at E
  have h0 : (ddotL i).map (whL [] []) = ddotL i := by simp
  simpa only [List.append_nil, List.nil_append, List.cons_append, h0, wt_nil, retaF] using E

/-- The sign of the odd case: `(-1)^{⟨hᵢ,λ-αᵢ⟩} (-1)^{|i,λ||i|} = -1` for odd `i`. -/
theorem zsign_cyc_odd (i : I) (μ : X) (hi : D.parity i = 1) :
    zsign k (D.h i (wt D μ [dn i]) : ZMod 2) * zsign k (ipar D i μ * D.parity i) = -1 := by
  rw [← zsign_add, h_wt_dn, ipar, hi, one_mul, mul_one]
  push_cast
  rw [show (D.h i μ : ZMod 2) - 2 + ((D.h i μ : ZMod 2) + 1) = 1 by
    generalize (D.h i μ : ZMod 2) = a; revert a; decide]
  exact zsign_one'

/-- **Brundan–Ellis (1.26)**: for even `i` the downward dot (the right mate of the upward dot,
Definition 2.1) equals the downward dot defined with the leftward cup `η'` and cap `ε'`: even
dots are cyclic. -/
theorem eq_1_26 (i : I) (μ : X) (hi : D.parity i = 0) :
    cl D Sc μ [dn i] [dn i] (ddotL i) = ldot cs i μ := by
  rw [ldot, mid_dot_lepsF, lemma41_eq3_one_even cs i _ hi, plcL_dL_eps, ← Category.assoc,
    retaF_ddot, hi, mul_zero, zsign_zero, one_smul, Category.assoc, eq_6_6_b, Category.comp_id]

/-- **Brundan–Ellis (1.27)**: for odd `i` the downward dot (the right mate of the upward dot,
Definition 2.1) is twice the odd bubble (2.18), in the region to the left of `Fᵢ 1_λ`, minus
the downward dot defined with the leftward cup `η'` and cap `ε'`. As printed, at every weight. -/
theorem eq_1_27 (i : I) (μ : X) (hi : D.parity i = 1) :
    cl D Sc μ [dn i] [dn i] (ddotL i) =
      (2 : k) • obLeft cs i μ - ldot cs i μ := by
  rw [ldot, mid_dot_lepsF, lemma41_eq3_one_odd cs i _ hi, map_add, map_smul, map_smul,
    plcL_dL_eps, plcL_eps_ob, Preadditive.comp_add, Linear.comp_smul, Linear.comp_smul,
    ← Category.assoc, retaF_ddot, ← Category.assoc (retaF cs i μ), eq_6_6_b, Category.id_comp,
    Linear.smul_comp, Category.assoc, eq_6_6_b, Category.comp_id, smul_smul,
    zsign_cyc_odd i μ hi]
  module

/-! ## (1.28): the rotation of `τ` by one leftward cup and cap -/

/-- The left adjunction (6.6) on `Fⱼ`, with one spectator on the left. -/
theorem cup_cap_F_left (i j : I) (ν : X) :
    cupAt cs j ν [up i, dn j] [] ≫ capAt cs j ν [up i] [dn j] = 𝟙 _ := by
  have E := congrArg (plcL D Sc ν [up i] [] [dn j] [dn j]) (eq_6_6_b cs j (wt D ν []))
  have hc : retaF cs j (wt D ν []) ∈ homPar D Sc (wt D ν []) [dn j] [dn j, up j, dn j] _ :=
    plcL_mem _ [dn j] [] (etaP_mem cs j _)
  have he : lepsF cs j (wt D ν []) ∈ homPar D Sc (wt D ν []) [dn j, up j, dn j] [dn j] _ :=
    plcL_mem _ [] [dn j] (epsP_mem cs j _)
  rw [plcL_comp_of_mem ν [up i] [] hc he, plcL_id] at E
  unfold retaF lepsF at E
  have hη := plcL_nested ν [up i] [] [dn j] [] (etaP_mem cs j (wt D (wt D ν []) []))
  have hε := plcL_nested ν [up i] [] [] [dn j] (epsP_mem cs j (wt D (wt D ν []) [dn j]))
  simp only [regionCast_family, List.cons_append, List.nil_append, wordCast,
    LinearMap.id_apply] at hη hε
  change _ ≫ _ = _ at E
  erw [hη, hε] at E
  exact E

/-- The upward crossing followed by `ε'` of colour `j`, with `Fⱼ` on the right, is the left side
of the pitchfork relation (7.5) placed to the left of `Fⱼ`. -/
theorem tau_cap_eq_pfL (i j : I) (ν : X) :
    cl D Sc ν [dn j, up i, up j, dn j] [dn j, up j, up i, dn j] (crossL [dn j] i j [dn j]) ≫
        capAt cs j ν [] [up i, dn j] =
      plcL D Sc ν [] [dn j] [dn j, up i, up j] [up i] (pfL cs j i (wt D ν [dn j])) := by
  have ht : SChain [dn j, up i, up j] (crossL [dn j] i j []) [dn j, up j, up i] := by
    simp [crossL, Shape.dom, Shape.cod]
  unfold pfL
  erw [plcL_comp_of_mem ν [] [dn j] (cl_mem_homPar ht rfl)
    (plcL_mem _ [] [up i] (epsP_mem cs j _)), plcL_cl]
  have hε := plcL_nested ν [] [dn j] [] [up i]
    (epsP_mem cs j (wt D (wt D ν [dn j]) [up i]))
  simp only [regionCast_family, List.cons_append, List.nil_append, wordCast,
    LinearMap.id_apply] at hε
  erw [hε]
  rfl

/-- The right side of (7.5) placed to the left of `Fⱼ`. -/
theorem plcL_pfR (i j : I) (ν : X) :
    plcL D Sc ν [] [dn j] [dn j, up i, up j] [up i] (pfR cs j i (wt D ν [dn j])) =
      cl D Sc ν [dn j, up i, up j, dn j] [up i, dn j, up j, dn j]
          ((lcrossL j i).map (whL [] [up j, dn j])) ≫
        capAt cs j ν [up i] [dn j] := by
  unfold pfR
  erw [plcL_comp_of_mem ν [] [dn j]
    (cl_mem_homPar ((sChain_lcrossL j i).wh [] [up j] rfl rfl) rfl)
    (plcL_mem (wt D ν [dn j]) [up i] [] (epsP_mem cs j (wt D (wt D ν [dn j]) []))), plcL_cl,
    map_whL_map_whL]
  have hε := plcL_nested ν [] [dn j] [up i] [] (epsP_mem cs j (wt D (wt D ν [dn j]) []))
  simp only [regionCast_family, List.cons_append, List.nil_append, wordCast,
    LinearMap.id_apply] at hε
  erw [hε]
  rfl

/-- `η'` of colour `j` to the right of a leftward crossing of `j` and `i` (super interchange). -/
theorem cup_lcross_right (i j : I) (ν : X) :
    cupAt cs j ν [dn j, up i] [] ≫
        cl D Sc ν [dn j, up i, up j, dn j] [up i, dn j, up j, dn j]
          ((lcrossL j i).map (whL [] [up j, dn j])) =
      zsign k (D.parity j * D.parity i * ipar D j ν) •
        (cl D Sc ν [dn j, up i] [up i, dn j] (lcrossL j i) ≫ cupAt cs j ν [up i, dn j] []) := by
  have hw : wt D ν [] = wt D ν [up j, dn j] := by simp [wt, sh]
  have E := plcL_interchange_hom ν hw
    (cl_mem_homPar (D := D) (Sc := Sc) (μ := wt D ν []) (sChain_lcrossL j i) rfl)
    (etaP_mem cs j ν)
  simp only [regionCast_cl, plcRight, wordCast] at E
  erw [plcL_cl, plcL_cl] at E
  have E' := congrArg (zsign k (D.parity j * D.parity i * ipar D j ν) • ·) E
  simp only [smul_smul, parsum_lcrossL, zsign_mul_self', one_smul] at E'
  exact E'.symm

/-- **The rotation of the upward crossing by the left adjunction**: `η'` of colour `j` on the
right of `Fⱼ Eᵢ`, then `τ : EᵢEⱼ → EⱼEᵢ` on the middle strands, then `ε'` on the left is
`(-1)^{|i||j||j,λ|}` times the leftward crossing `Fⱼ Eᵢ → Eᵢ Fⱼ`. From (7.5) and (6.6). -/
theorem rot_tau_left (i j : I) (ν : X) :
    cupAt cs j ν [dn j, up i] [] ≫
        cl D Sc ν [dn j, up i, up j, dn j] [dn j, up j, up i, dn j] (crossL [dn j] i j [dn j]) ≫
        capAt cs j ν [] [up i, dn j] =
      zsign k (D.parity j * D.parity i * ipar D j ν) •
        cl D Sc ν [dn j, up i] [up i, dn j] (lcrossL j i) := by
  rw [tau_cap_eq_pfL, eq_7_5_a, plcL_pfR, ← Category.assoc, cup_lcross_right, Linear.smul_comp,
    Category.assoc, cup_cap_F_left]
  erw [Category.comp_id]

/-! ## (1.28): the left mate of the upward crossing -/

/-- The downward crossing `Fᵢ Fⱼ 1_λ → Fⱼ Fᵢ 1_λ` defined with the left adjunction (the
right-hand picture of (1.28)): the leftward cups `η'` of colours `i` (outer, lowest) and `j`
(inner) on the right, the upward crossing `τ : Eᵢ Eⱼ → Eⱼ Eᵢ` on the two middle strands, then the
leftward caps `ε'` of colours `j` (inner) and `i` (outer, highest) on the left. -/
def lcrossMate (i j : I) (μ : X) :
    (pres D Sc).obj (ob D μ [dn i, dn j]) ⟶ (pres D Sc).obj (ob D μ [dn j, dn i]) :=
  cupAt cs i μ [dn i, dn j] [] ≫ cupAt cs j μ [dn i, dn j, up i] [dn i] ≫
    cl D Sc μ [dn i, dn j, up i, up j, dn j, dn i] [dn i, dn j, up j, up i, dn j, dn i]
      (crossL [dn i, dn j] i j [dn j, dn i]) ≫
    capAt cs j μ [dn i] [up i, dn j, dn i] ≫ capAt cs i μ [] [dn j, dn i]

/-- The inner rotation in `lcrossMate`: by `rot_tau_left`, the leftward crossing of `j` and `i`
between the two outer strands. -/
theorem lcrossMate_inner (i j : I) (μ : X) :
    cupAt cs j μ [dn i, dn j, up i] [dn i] ≫
        cl D Sc μ [dn i, dn j, up i, up j, dn j, dn i] [dn i, dn j, up j, up i, dn j, dn i]
          (crossL [dn i, dn j] i j [dn j, dn i]) ≫
        capAt cs j μ [dn i] [up i, dn j, dn i] =
      zsign k (D.parity j * D.parity i * ipar D j (wt D μ [dn i])) •
        cl D Sc μ [dn i, dn j, up i, dn i] [dn i, up i, dn j, dn i]
          ((lcrossL j i).map (whL [dn i] [dn i])) := by
  have E := congrArg (plcL D Sc μ [dn i] [dn i] [dn j, up i] [up i, dn j])
    (rot_tau_left cs i j (wt D μ [dn i]))
  have ht : SChain [dn j, up i, up j, dn j] (crossL [dn j] i j [dn j])
      [dn j, up j, up i, dn j] := by
    simp [crossL, Shape.dom, Shape.cod]
  rw [map_smul, plcL_cl] at E
  erw [plcL_comp_of_mem μ [dn i] [dn i] (plcL_mem _ [dn j, up i] [] (etaP_mem cs j _))
      (comp_mem_homPar (cl_mem_homPar ht rfl) (plcL_mem _ [] [up i, dn j] (epsP_mem cs j _))),
    plcL_comp_of_mem μ [dn i] [dn i] (cl_mem_homPar ht rfl)
      (plcL_mem _ [] [up i, dn j] (epsP_mem cs j _)), plcL_cl] at E
  have hη := plcL_nested μ [dn i] [dn i] [dn j, up i] []
    (etaP_mem cs j (wt D (wt D μ [dn i]) []))
  have hε := plcL_nested μ [dn i] [dn i] [] [up i, dn j]
    (epsP_mem cs j (wt D (wt D μ [dn i]) [up i, dn j]))
  simp only [regionCast_family, List.cons_append, List.nil_append, wordCast,
    LinearMap.id_apply] at hη hε
  erw [hη, hε] at E
  exact E

/-- The pitchfork relation (7.6) with `Fᵢ` on the left: the leftward crossing of `j` and `i` on
the right leg of `η'` of colour `i` is `(-1)^{|i||j|}` times the downward crossing on its left
leg. -/
theorem cup_lcross_eq_cup_dcross (i j : I) (μ : X) :
    cupAt cs i μ [dn i, dn j] [] ≫
        cl D Sc μ [dn i, dn j, up i, dn i] [dn i, up i, dn j, dn i]
          ((lcrossL j i).map (whL [dn i] [dn i])) =
      zsign k (D.parity i * D.parity j) •
        (cupAt cs i μ [dn i] [dn j] ≫
          cl D Sc μ [dn i, up i, dn i, dn j] [dn i, up i, dn j, dn i]
            ((dcrossL i j).map (whL [dn i, up i] []))) := by
  have E := congrArg (plcL D Sc μ [dn i] [] [dn j] [up i, dn j, dn i]) (eq_7_6_a cs i j μ)
  unfold pdcupL pdcupR at E
  rw [map_smul] at E
  erw [plcL_comp_of_mem μ [dn i] [] (plcL_mem _ [] [dn j] (etaP_mem cs i _))
      (cl_mem_homPar ((sChain_dcrossL i j).wh [up i] [] rfl rfl) rfl),
    plcL_comp_of_mem μ [dn i] [] (plcL_mem _ [dn j] [] (etaP_mem cs i _))
      (cl_mem_homPar ((sChain_lcrossL j i).wh [] [dn i] rfl rfl) rfl),
    plcL_cl, plcL_cl] at E
  have hL := plcL_nested μ [dn i] [] [] [dn j] (etaP_mem cs i (wt D (wt D μ []) [dn j]))
  have hR := plcL_nested μ [dn i] [] [dn j] [] (etaP_mem cs i (wt D (wt D μ []) []))
  simp only [regionCast_family, List.cons_append, List.nil_append, wordCast,
    LinearMap.id_apply] at hL hR
  erw [hL, hR] at E
  simp only [map_whL_map_whL, List.cons_append, List.nil_append, List.append_nil] at E
  have E' := congrArg (zsign k (D.parity i * D.parity j) • ·) E
  simp only [smul_smul, zsign_mul_self', one_smul] at E'
  exact E'.symm

theorem parsum_dcrossL (i j : I) : parsum D (dcrossL i j) = D.parity i * D.parity j := by
  simp [parsum, dcrossL, sigmaL, Shape.parity, whL]

/-- The downward crossing on the right of `Fᵢ Eᵢ Fᵢ Fⱼ` past `ε'` of colour `i` on the left
(super interchange). -/
theorem dcross_cap (i j : I) (μ : X) :
    cl D Sc μ [dn i, up i, dn i, dn j] [dn i, up i, dn j, dn i]
        ((dcrossL i j).map (whL [dn i, up i] [])) ≫ capAt cs i μ [] [dn j, dn i] =
      zsign k (ipar D i (wt D μ [dn i, dn j]) * (D.parity i * D.parity j)) •
        (capAt cs i μ [] [dn i, dn j] ≫ cl D Sc μ [dn i, dn j] [dn j, dn i] (dcrossL i j)) := by
  have hw : wt D μ [dn i, dn j] = wt D μ [dn j, dn i] := by
    simp [wt, sh, add_comm, add_left_comm, add_assoc]
  have E := plcL_interchange_hom μ hw (epsP_mem cs i (wt D μ [dn i, dn j]))
    (cl_mem_homPar (D := D) (Sc := Sc) (sChain_dcrossL i j) rfl)
  simp only [plcRight_cl, regionCast_family, parsum_dcrossL] at E
  change capAt cs i μ [] [dn i, dn j] ≫ _ = _ at E
  have EE := congrArg (zsign k (ipar D i (wt D μ [dn i, dn j]) *
    (D.parity i * D.parity j)) • ·) E
  rw [smul_smul, zsign_mul_self', one_smul] at EE
  exact EE.symm

/-- The left adjunction (6.6) on `Fᵢ`, with `Fⱼ` on the right. -/
theorem cup_cap_F_dn (i j : I) (μ : X) :
    cupAt cs i μ [dn i] [dn j] ≫ capAt cs i μ [] [dn i, dn j] = 𝟙 _ := by
  have E := congrArg (plcL D Sc μ [] [dn j] [dn i] [dn i]) (eq_6_6_b cs i (wt D μ [dn j]))
  have hc : retaF cs i (wt D μ [dn j]) ∈
      homPar D Sc (wt D μ [dn j]) [dn i] [dn i, up i, dn i] _ :=
    plcL_mem _ [dn i] [] (etaP_mem cs i _)
  have he : lepsF cs i (wt D μ [dn j]) ∈
      homPar D Sc (wt D μ [dn j]) [dn i, up i, dn i] [dn i] _ :=
    plcL_mem _ [] [dn i] (epsP_mem cs i _)
  rw [plcL_comp_of_mem μ [] [dn j] hc he, plcL_id] at E
  unfold retaF lepsF at E
  have hη := plcL_nested μ [] [dn j] [dn i] [] (etaP_mem cs i (wt D (wt D μ [dn j]) []))
  have hε := plcL_nested μ [] [dn j] [] [dn i] (epsP_mem cs i (wt D (wt D μ [dn j]) [dn i]))
  simp only [regionCast_family, List.cons_append, List.nil_append, wordCast,
    LinearMap.id_apply] at hη hε
  change _ ≫ _ = _ at E
  erw [hη, hε] at E
  exact E

/-- The left mate of the upward crossing in terms of the right mate (Definition 2.1), with the
sign as it comes out of the computation. -/
theorem lcrossMate_eq_ipar (i j : I) (μ : X) :
    lcrossMate cs i j μ =
      (zsign k (D.parity j * D.parity i * ipar D j (wt D μ [dn i])) *
        (zsign k (D.parity i * D.parity j) *
          zsign k (ipar D i (wt D μ [dn i, dn j]) * (D.parity i * D.parity j)))) •
        cl D Sc μ [dn i, dn j] [dn j, dn i] (dcrossL i j) := by
  have e : lcrossMate cs i j μ = cupAt cs i μ [dn i, dn j] [] ≫
      (cupAt cs j μ [dn i, dn j, up i] [dn i] ≫
        cl D Sc μ [dn i, dn j, up i, up j, dn j, dn i] [dn i, dn j, up j, up i, dn j, dn i]
          (crossL [dn i, dn j] i j [dn j, dn i]) ≫
        capAt cs j μ [dn i] [up i, dn j, dn i]) ≫ capAt cs i μ [] [dn j, dn i] := by
    simp only [lcrossMate, Category.assoc]
  rw [e, lcrossMate_inner, Linear.smul_comp, Linear.comp_smul, ← Category.assoc,
    cup_lcross_eq_cup_dcross, Linear.smul_comp, Category.assoc, dcross_cap, Linear.comp_smul,
    ← Category.assoc, cup_cap_F_dn, smul_smul, smul_smul]
  erw [Category.id_comp]
  rw [mul_assoc]

/-- **Brundan–Ellis (1.28), corrected**: the downward crossing defined with the left adjunction
(`lcrossMate`: leftward cups `η'` on the right, the upward crossing `τ`, leftward caps `ε'` on the
left, nested as in the paper's picture) is `(-1)^{|i||j|(⟨hᵢ,λ⟩ + ⟨hⱼ,λ⟩ + 1)}` times the
downward crossing of Definition 2.1 (the right mate of `τ`). The printed relation has no sign;
it holds when `i` or `j` is even (`eq_1_28_of_even`) and fails for `i = j` odd
(`eq_1_28_self`; Brundan–Kleshchev arXiv:2203.14149 (13.18)). See ERRATA [BE2] 3. -/
theorem eq_1_28 (i j : I) (μ : X) :
    lcrossMate cs i j μ =
      zsign k (D.parity i * D.parity j * ((D.h i μ : ZMod 2) + (D.h j μ : ZMod 2) + 1)) •
        cl D Sc μ [dn i, dn j] [dn j, dn i] (dcrossL i j) := by
  rw [lcrossMate_eq_ipar, ← zsign_add, ← zsign_add, ipar_wt_dnj,
    show wt D μ [dn i, dn j] = wt D (wt D μ [dn j]) [dn i] from rfl, ipar_wt_dnj, ipar_wt_dnj,
    ipar, ipar]
  congr 2
  generalize D.parity i = a; generalize D.parity j = b
  generalize (D.h i μ : ZMod 2) = x; generalize (D.h j μ : ZMod 2) = y
  revert a b x y; decide

/-- **Brundan–Ellis (1.28) as printed, when `i` or `j` is even**: the downward crossings defined
with the left and with the right adjunction agree. -/
theorem eq_1_28_of_even (i j : I) (μ : X) (h : D.parity i * D.parity j = 0) :
    lcrossMate cs i j μ = cl D Sc μ [dn i, dn j] [dn j, dn i] (dcrossL i j) := by
  rw [eq_1_28, h, zero_mul, zsign_zero, one_smul]

/-- **Brundan–Ellis (1.28) for `i = j`, corrected** (Brundan–Kleshchev, arXiv:2203.14149v3,
(13.18)): the two downward crossings differ by `(-1)^{|i|}`. -/
theorem eq_1_28_self (i : I) (μ : X) :
    lcrossMate cs i i μ =
      zsign k (D.parity i) • cl D Sc μ [dn i, dn i] [dn i, dn i] (dcrossL i i) := by
  rw [eq_1_28]
  congr 2
  generalize D.parity i = a; generalize (D.h i μ : ZMod 2) = x
  revert a x; decide

/-- **The printed (1.28) fails for odd `i = j`**: if the two downward crossings on `Fᵢ Fᵢ 1_λ`
were equal, the identity of `Fᵢ Fᵢ 1_λ` would vanish. (By (1.28) corrected they differ by a
sign, so the downward crossing would be zero since `2` is invertible, and then the dot slide (3.5)
with one dot gives `1 = 0`.) -/
theorem eq_1_28_printed_self_odd (i : I) (μ : X) (hi : D.parity i = 1)
    (hp : lcrossMate cs i i μ = cl D Sc μ [dn i, dn i] [dn i, dn i] (dcrossL i i)) :
    (𝟙 ((pres D Sc).obj (ob D μ [dn i, dn i])) : _ ⟶ _) = 0 := by
  rw [eq_1_28_self, hi, zsign_one', neg_one_smul, neg_eq_iff_add_eq_zero, ← two_smul k] at hp
  obtain ⟨u, hu⟩ := Sc.two_isUnit ⟨i, hi⟩
  have hz : cl D Sc μ [dn i, dn i] [dn i, dn i] (dcrossL i i) = 0 := by
    have := congrArg (fun x => (↑u⁻¹ : k) • x) hp
    simpa only [smul_zero, smul_smul, ← hu, Units.inv_mul, one_smul] using this
  have E := lemma31_eq5_eq Sc i μ 1
  erw [← cl_comp (sChain_dcrossL i i) ((sChain_ddotsL i 1).wh [dn i] [] rfl rfl),
    ← cl_comp ((sChain_ddotsL i 1).wh [] [dn i] rfl rfl) (sChain_dcrossL i i)] at E
  rw [hz, Limits.zero_comp] at E
  erw [hz, Limits.comp_zero] at E
  simpa [ddotsL, zsign_zero, cl_nil] using E.symm

/-- **The printed (1.28) for odd `i`, `j` at a weight with `⟨hᵢ,λ⟩ + ⟨hⱼ,λ⟩` even** forces the
downward crossing `Fᵢ Fⱼ 1_λ → Fⱼ Fᵢ 1_λ` to vanish, since `2` is invertible. -/
theorem eq_1_28_printed_odd (i j : I) (μ : X) (hi : D.parity i = 1) (hj : D.parity j = 1)
    (hh : (D.h i μ : ZMod 2) + (D.h j μ : ZMod 2) = 0)
    (hp : lcrossMate cs i j μ = cl D Sc μ [dn i, dn j] [dn j, dn i] (dcrossL i j)) :
    cl D Sc μ [dn i, dn j] [dn j, dn i] (dcrossL i j) = 0 := by
  rw [eq_1_28, hi, hj, hh, one_mul, zero_add, one_mul, zsign_one', neg_one_smul,
    neg_eq_iff_add_eq_zero, ← two_smul k] at hp
  obtain ⟨u, hu⟩ := Sc.two_isUnit ⟨i, hi⟩
  have := congrArg (fun x => (↑u⁻¹ : k) • x) hp
  simpa only [smul_zero, smul_smul, ← hu, Units.inv_mul, one_smul] using this

end OddMath.SKM
