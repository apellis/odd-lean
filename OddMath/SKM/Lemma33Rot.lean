/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Lemma33

/-!
# The braid relation with one downward strand (Brundan–Ellis, Lemma 3.3 (3.8))

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Lemma 3.3, relation
(3.8) (TeX label `lurking`): on `Eⱼ Eₖ Fᵢ 1_λ` (bottom), the two composites of two crossings
`σ` (1.11) and one upward crossing ending at `Fᵢ Eₖ Eⱼ`, with the strand `k` passing to the right
(`lemma33_eq8_lhs`) or to the left (`lemma33_eq8_rhs`) of the crossing of `i` and `j`, are equal
unless `i = k ≠ j`, when their difference is
`∑_{r+s=dᵢⱼ-1} (-1)^{|i|s} tᵢⱼ (cap with s dots, then cup with r dots)
 + ∑ (-1)^{|i|s} sᵢⱼ^{pq} (cap with s dots, q dots on the strand j, cup with r dots)`, the
layers ordered as in the paper's picture (`term8`).

The paper proves (3.8) by rotating (1.9) clockwise. Here `rotL i W W' A` is the clockwise rotation
of the leftmost strand `Eᵢ` of `A : Eᵢ E_W → E_{W'} Eᵢ` (cup on the left, cap on the right; so
`σ = rotL τ`), and `cl_rotL_comp` is the rule `rot((A ⊗ 1) ≫ (1 ⊗ B)) = (-1)^{|A||B|}
(1 ⊗ rot B) ≫ (rot A ⊗ 1)`.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

/-! ## Clockwise rotation of the leftmost strand -/

/-- The clockwise rotation `E_W Fᵢ → Fᵢ E_{W'}` of `A : Eᵢ E_W → E_{W'} Eᵢ`. -/
def rotL (i : I) (W W' : List (Letter I)) (A : List (LayerData I)) : List (LayerData I) :=
  [([], Shape.cup i, W ++ [dn i])] ++ A.map (whL [dn i] [dn i]) ++ [([dn i] ++ W', Shape.cap i, [])]

theorem sChain_rotL (i : I) {W W' : List (Letter I)} {A : List (LayerData I)}
    (hA : SChain ([up i] ++ W) A (W' ++ [up i])) : SChain (W ++ [dn i]) (rotL i W W' A) ([dn i] ++ W') :=
  (SChain.append (t' := [dn i] ++ ([up i] ++ W) ++ [dn i])
    (show SChain (W ++ [dn i]) [([], Shape.cup i, W ++ [dn i])] ([dn i] ++ ([up i] ++ W) ++ [dn i])
      from ⟨by simp [Shape.dom], by simp [Shape.cod]⟩)
    (hA.whisk [dn i] [dn i])).append
    (show SChain ([dn i] ++ (W' ++ [up i]) ++ [dn i]) [([dn i] ++ W', Shape.cap i, [])] ([dn i] ++ W')
      from ⟨by simp [Shape.dom], by simp [Shape.cod]⟩)

theorem parsum_rotL (i : I) (W W' : List (Letter I)) (A : List (LayerData I)) :
    parsum D (rotL i W W' A) = parsum D A := by
  simp [rotL, parsum_append, Shape.parity]

theorem sigmaL_eq_rotL (i j : I) : sigmaL i j = rotL i [up j] [up j] (crossL [] i j []) := by
  simp [sigmaL, rotL, crossL, whL]

variable (Sc) in
theorem zigE_cup (a : I) : ZigE D Sc [([], Shape.cup a, [])] [([], Shape.cap a, [])] [up a] := by
  intro μ
  simpa [whL] using cl_zigE Sc a μ

variable (Sc) in
/-- `rot((1_{Eᵢ} ⊗ C) ≫ A) = (C ⊗ 1_{Fᵢ}) ≫ rot(A)`. -/
theorem cl_rotL_pre (μ : X) (i : I) {W W₀ W' : List (Letter I)} {C : List (LayerData I)}
    (A : List (LayerData I)) (hC : SChain W C W₀) :
    cl D Sc μ (W ++ [dn i]) ([dn i] ++ W') (rotL i W W' (C.map (whL [up i] []) ++ A)) =
      cl D Sc μ (W ++ [dn i]) ([dn i] ++ W') (C.map (whL [] [dn i]) ++ rotL i W₀ W' A) := by
  have E := cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := W ++ [dn i]) (T := [dn i] ++ W') []
    (A.map (whL [dn i] [dn i]) ++ [([dn i] ++ W', Shape.cap i, [])]) [] [] [dn i]
    (A := [([], Shape.cup i, [])]) (s := []) (s' := [dn i, up i]) ⟨rfl, rfl⟩ hC
    (Or.inl (by simp [Shape.parity]))
  simp only [List.nil_append] at E
  convert E using 2 <;> simp [rotL, whL, List.append_assoc]

variable (Sc) in
/-- `rot(A ≫ (C ⊗ 1_{Eᵢ})) = rot(A) ≫ (1_{Fᵢ} ⊗ C)`. -/
theorem cl_rotL_post (μ : X) (i : I) {W W' W'' : List (Letter I)} {C : List (LayerData I)}
    (A : List (LayerData I)) (hC : SChain W' C W'') :
    cl D Sc μ (W ++ [dn i]) ([dn i] ++ W'') (rotL i W W'' (A ++ C.map (whL [] [up i]))) =
      cl D Sc μ (W ++ [dn i]) ([dn i] ++ W'') (rotL i W W' A ++ C.map (whL [dn i] [])) := by
  have E := cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := W ++ [dn i]) (T := [dn i] ++ W'')
    ([([], Shape.cup i, W ++ [dn i])] ++ A.map (whL [dn i] [dn i])) [] [dn i] [] []
    (B := [([], Shape.cap i, [])]) (t := [up i, dn i]) (t' := []) hC ⟨rfl, rfl⟩
    (Or.inr (by simp [Shape.parity]))
  simp only [List.append_nil] at E
  convert E using 2 <;> simp [rotL, whL, List.append_assoc]

variable (Sc) in
/-- **Rotation of a composite**: `rot((A ⊗ 1_{E_{W₂}}) ≫ (1_{E_{W₁'}} ⊗ B)) =
(-1)^{|A||B|} (1_{E_{W₁}} ⊗ rot B) ≫ (rot A ⊗ 1_{E_{W₂'}})`. -/
theorem cl_rotL_comp (μ : X) (i : I) {W₁ W₁' W₂ W₂' : List (Letter I)} {A B : List (LayerData I)}
    (hA : SChain ([up i] ++ W₁) A (W₁' ++ [up i])) (hB : SChain ([up i] ++ W₂) B (W₂' ++ [up i])) :
    cl D Sc μ (W₁ ++ W₂ ++ [dn i]) ([dn i] ++ W₁' ++ W₂')
        (rotL i (W₁ ++ W₂) (W₁' ++ W₂') (A.map (whL [] W₂) ++ B.map (whL W₁' []))) =
      zsign k (parsum D A * parsum D B) •
        cl D Sc μ (W₁ ++ W₂ ++ [dn i]) ([dn i] ++ W₁' ++ W₂')
          ((rotL i W₂ W₂' B).map (whL W₁ []) ++ (rotL i W₁ W₁' A).map (whL [] W₂')) := by
  have hc : parsum D [(([] : List (Letter I)), Shape.cup i, ([] : List (Letter I)))] = 0 := by
    simp [Shape.parity]
  have hκ : parsum D [(([] : List (Letter I)), Shape.cap i, ([] : List (Letter I)))] = 0 := by
    simp [Shape.parity]
  have hRB := sChain_rotL i hB
  -- (a) the cup of `rot A` moves to the bottom
  have sa := cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := W₁ ++ W₂ ++ [dn i])
    (T := [dn i] ++ W₁' ++ W₂') []
    ((A.map (whL [dn i] [dn i])).map (whL [] W₂') ++ [([dn i] ++ W₁', Shape.cap i, W₂')]) [] [] []
    (A := [([], Shape.cup i, [])]) (s := []) (s' := [dn i, up i]) (t := W₁ ++ W₂ ++ [dn i])
    (t' := W₁ ++ [dn i] ++ W₂') ⟨rfl, rfl⟩ (hRB.wh W₁ [] (by simp) (by simp)) (Or.inl hc)
  -- (b) `A` moves below `rot B`
  have hY : SChain (W₂ ++ [dn i]) (rotL i W₂ W₂' B) ([dn i] ++ W₂') := hRB
  have sb := cl_ixc' (D := D) (Sc := Sc) (μ := μ) (S := W₁ ++ W₂ ++ [dn i])
    (T := [dn i] ++ W₁' ++ W₂') [([], Shape.cup i, W₁ ++ W₂ ++ [dn i])] [([dn i] ++ W₁', Shape.cap i, W₂')] [dn i] [] []
    hA hY
  rw [parsum_rotL] at sb
  -- (c) the cap of `rot A` moves below `B` and the cap of `rot B`
  have hZ : SChain ([up i] ++ W₂ ++ [dn i]) (B.map (whL [] [dn i]) ++ [(W₂', Shape.cap i, [])]) W₂' :=
    SChain.append (t' := W₂' ++ [up i] ++ [dn i]) (hB.wh [] [dn i] (by simp) rfl)
      (show SChain (W₂' ++ [up i] ++ [dn i]) [(W₂', Shape.cap i, [])] W₂' from
        ⟨by simp [Shape.dom], by simp [Shape.cod]⟩)
  have sc := cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := W₁ ++ W₂ ++ [dn i])
    (T := [dn i] ++ W₁' ++ W₂')
    ([([], Shape.cup i, W₁ ++ W₂ ++ [dn i])] ++ A.map (whL [dn i] (W₂ ++ [dn i])) ++
      [([dn i] ++ W₁' ++ [up i], Shape.cup i, W₂ ++ [dn i])]) [] ([dn i] ++ W₁') [] []
    (A := [([], Shape.cap i, [])]) (s := [up i, dn i]) (s' := []) ⟨rfl, rfl⟩ hZ (Or.inl hκ)
  -- (d) the zigzag relation on the strand `Eᵢ`
  have sd := cl_zigE_ctx (zigE_cup Sc i) μ (s₀ := W₁ ++ W₂ ++ [dn i]) (t₀ := [dn i] ++ W₁' ++ W₂')
    ([([], Shape.cup i, W₁ ++ W₂ ++ [dn i])] ++ A.map (whL [dn i] (W₂ ++ [dn i])))
    ((B.map (whL [] [dn i]) ++ [(W₂', Shape.cap i, [])]).map (whL ([dn i] ++ W₁') []))
    ([dn i] ++ W₁') (W₂ ++ [dn i])
    (SChain.append (t' := [dn i] ++ ([up i] ++ W₁) ++ (W₂ ++ [dn i]))
      ⟨by simp [Shape.dom], by simp [Shape.cod]⟩ (hA.wh [dn i] (W₂ ++ [dn i]) rfl (by simp)))
    (hZ.wh ([dn i] ++ W₁') [] (by simp) (by simp))
  simp only [rotL, List.map_append, List.map_cons, List.map_nil, List.map_map, whL_comp_whL,
    whL, List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at sa sb sc sd ⊢
  rw [← sa, sb, ← sc, sd, smul_smul, zsign_mul_self, one_smul]

/-! ## Rotation as a linear map -/

variable (D Sc) in
/-- The rotation `A ↦ rot(A)` as a `k`-linear map. -/
def rotMap (μ : X) (i : I) (W W' : List (Letter I)) :
    ((pres D Sc).obj (ob D (wt D μ [dn i]) ([up i] ++ W)) ⟶
        (pres D Sc).obj (ob D (wt D μ [dn i]) (W' ++ [up i]))) →ₗ[k]
      ((pres D Sc).obj (ob D μ (W ++ [dn i])) ⟶ (pres D Sc).obj (ob D μ ([dn i] ++ W'))) :=
  ctxL D Sc μ (W ++ [dn i]) ([dn i] ++ W') [([], Shape.cup i, W ++ [dn i])] [dn i] [dn i]
    [([dn i] ++ W', Shape.cap i, [])] ([up i] ++ W) (W' ++ [up i])

theorem rotMap_cl (μ : X) (i : I) (W W' : List (Letter I)) (A : List (LayerData I)) :
    rotMap D Sc μ i W W' (cl D Sc (wt D μ [dn i]) ([up i] ++ W) (W' ++ [up i]) A) =
      cl D Sc μ (W ++ [dn i]) ([dn i] ++ W') (rotL i W W' A) :=
  ctxL_cl (D := D) (Sc := Sc) μ (u := [dn i]) (v := [dn i]) (s := [up i] ++ W)
    (t := W' ++ [up i])
    (show SChain (W ++ [dn i]) [([], Shape.cup i, W ++ [dn i])] ([dn i] ++ ([up i] ++ W) ++ [dn i])
      from ⟨by simp [Shape.dom], by simp [Shape.cod]⟩)
    (show SChain ([dn i] ++ (W' ++ [up i]) ++ [dn i]) [([dn i] ++ W', Shape.cap i, [])]
      ([dn i] ++ W') from ⟨by simp [Shape.dom], by simp [Shape.cod]⟩) A

/-! ## Lemma 3.3 (3.8) -/

/-- The left-hand side of (3.8): the strand `k` passes to the right of the crossing of `i` and
`j`. -/
def lemma33_eq8_lhs (i j k' : I) : List (LayerData I) :=
  (sigmaL i k').map (whL [up j] []) ++ (sigmaL i j).map (whL [] [up k']) ++ crossL [dn i] j k' []

/-- The second term of (3.8): the strand `k` passes to the left of the crossing of `i` and `j`. -/
def lemma33_eq8_rhs (i j k' : I) : List (LayerData I) :=
  crossL [] j k' [dn i] ++ (sigmaL i j).map (whL [up k'] []) ++ (sigmaL i k').map (whL [] [up j])

theorem sChain_sigma_up (i a : I) : SChain ([up i] ++ [up a]) (crossL [] i a []) ([up a] ++ [up i]) := by
  simp [crossL, Shape.dom, Shape.cod]

variable (Sc) in
theorem cl_rot_braid_lhs (μ : X) (i j k' : I) :
    cl D Sc μ ([up j, up k'] ++ [dn i]) ([dn i] ++ [up k', up j])
        (rotL i [up j, up k'] [up k', up j]
          (crossL [] i j [up k'] ++ crossL [up j] i k' [] ++ crossL [] j k' [up i])) =
      zsign k (D.parity i * D.parity j * (D.parity i * D.parity k')) •
        cl D Sc μ ([up j, up k'] ++ [dn i]) ([dn i] ++ [up k', up j]) (lemma33_eq8_lhs i j k') := by
  have e1 : cl D Sc μ ([up j, up k'] ++ [dn i]) ([dn i] ++ [up k', up j])
      (rotL i [up j, up k'] [up k', up j]
        (crossL [] i j [up k'] ++ crossL [up j] i k' [] ++ crossL [] j k' [up i])) =
      cl D Sc μ ([up j, up k'] ++ [dn i]) ([dn i] ++ [up k', up j])
        (rotL i [up j, up k'] [up j, up k'] (crossL [] i j [up k'] ++ crossL [up j] i k' []) ++
          crossL [dn i] j k' []) :=
    cl_rotL_post Sc μ i (W' := [up j, up k']) _ (C := crossL [] j k' [])
      (by simp [crossL, Shape.dom, Shape.cod])
  have e2 : cl D Sc μ ([up j, up k'] ++ [dn i]) ([dn i] ++ [up j, up k'])
      (rotL i [up j, up k'] [up j, up k'] (crossL [] i j [up k'] ++ crossL [up j] i k' [])) =
      zsign k (D.parity i * D.parity j * (D.parity i * D.parity k')) •
        cl D Sc μ ([up j, up k'] ++ [dn i]) ([dn i] ++ [up j, up k'])
          ((sigmaL i k').map (whL [up j] []) ++ (sigmaL i j).map (whL [] [up k'])) := by
    have := cl_rotL_comp Sc μ i (W₁ := [up j]) (W₁' := [up j]) (W₂ := [up k']) (W₂' := [up k'])
      (sChain_sigma_up i j) (sChain_sigma_up i k')
    rw [← sigmaL_eq_rotL, ← sigmaL_eq_rotL] at this
    simpa [crossL, parsum, Shape.parity, whL] using this
  have h₁ : SChain ([up j, up k'] ++ [dn i]) (rotL i [up j, up k'] [up j, up k']
      (crossL [] i j [up k'] ++ crossL [up j] i k' [])) ([dn i] ++ [up j, up k']) :=
    sChain_rotL i (by simp [crossL, Shape.dom, Shape.cod])
  have h₂ : SChain ([dn i] ++ [up j, up k']) (crossL [dn i] j k' []) ([dn i] ++ [up k', up j]) := by
    simp [crossL, Shape.dom, Shape.cod]
  have h₃ : SChain ([up j, up k'] ++ [dn i])
      ((sigmaL i k').map (whL [up j] []) ++ (sigmaL i j).map (whL [] [up k']))
      ([dn i] ++ [up j, up k']) :=
    ((sChain_sigmaL i k').wh [up j] [] rfl rfl).append ((sChain_sigmaL i j).wh [] [up k'] rfl rfl)
  rw [e1, ← cl_comp h₁ h₂, e2, Linear.smul_comp, cl_comp h₃ h₂]
  rfl

variable (Sc) in
theorem cl_rot_braid_rhs (μ : X) (i j k' : I) :
    cl D Sc μ ([up j, up k'] ++ [dn i]) ([dn i] ++ [up k', up j])
        (rotL i [up j, up k'] [up k', up j]
          (crossL [up i] j k' [] ++ crossL [] i k' [up j] ++ crossL [up k'] i j [])) =
      zsign k (D.parity i * D.parity j * (D.parity i * D.parity k')) •
        cl D Sc μ ([up j, up k'] ++ [dn i]) ([dn i] ++ [up k', up j]) (lemma33_eq8_rhs i j k') := by
  have e1 : cl D Sc μ ([up j, up k'] ++ [dn i]) ([dn i] ++ [up k', up j])
      (rotL i [up j, up k'] [up k', up j]
        (crossL [up i] j k' [] ++ (crossL [] i k' [up j] ++ crossL [up k'] i j []))) =
      cl D Sc μ ([up j, up k'] ++ [dn i]) ([dn i] ++ [up k', up j])
        (crossL [] j k' [dn i] ++
          rotL i [up k', up j] [up k', up j] (crossL [] i k' [up j] ++ crossL [up k'] i j [])) :=
    cl_rotL_pre Sc μ i _ (C := crossL [] j k' []) (by simp [crossL, Shape.dom, Shape.cod])
  have e2 : cl D Sc μ ([up k', up j] ++ [dn i]) ([dn i] ++ [up k', up j])
      (rotL i [up k', up j] [up k', up j] (crossL [] i k' [up j] ++ crossL [up k'] i j [])) =
      zsign k (D.parity i * D.parity k' * (D.parity i * D.parity j)) •
        cl D Sc μ ([up k', up j] ++ [dn i]) ([dn i] ++ [up k', up j])
          ((sigmaL i j).map (whL [up k'] []) ++ (sigmaL i k').map (whL [] [up j])) := by
    have := cl_rotL_comp Sc μ i (W₁ := [up k']) (W₁' := [up k']) (W₂ := [up j]) (W₂' := [up j])
      (sChain_sigma_up i k') (sChain_sigma_up i j)
    rw [← sigmaL_eq_rotL, ← sigmaL_eq_rotL] at this
    simpa [crossL, parsum, Shape.parity, whL] using this
  have h₁ : SChain ([up j, up k'] ++ [dn i]) (crossL [] j k' [dn i]) ([up k', up j] ++ [dn i]) := by
    simp [crossL, Shape.dom, Shape.cod]
  have h₂ : SChain ([up k', up j] ++ [dn i]) (rotL i [up k', up j] [up k', up j]
      (crossL [] i k' [up j] ++ crossL [up k'] i j [])) ([dn i] ++ [up k', up j]) :=
    sChain_rotL i (by simp [crossL, Shape.dom, Shape.cod])
  have h₃ : SChain ([up k', up j] ++ [dn i])
      ((sigmaL i j).map (whL [up k'] []) ++ (sigmaL i k').map (whL [] [up j]))
      ([dn i] ++ [up k', up j]) :=
    ((sChain_sigmaL i j).wh [up k'] [] rfl rfl).append ((sChain_sigmaL i k').wh [] [up j] rfl rfl)
  rw [List.append_assoc, e1, ← cl_comp h₁ h₂, e2, Linear.comp_smul, cl_comp h₁ h₃, mul_comm]
  rfl

variable (Sc) in
/-- **Brundan–Ellis, Lemma 3.3 (3.8), unless `i = k ≠ j`.** -/
theorem lemma33_eq8 (i j k' : I) (ν : X) (h : ¬(i = k' ∧ i ≠ j)) :
    cl D Sc ν [up j, up k', dn i] [dn i, up k', up j] (lemma33_eq8_lhs i j k') =
      cl D Sc ν [up j, up k', dn i] [dn i, up k', up j] (lemma33_eq8_rhs i j k') := by
  have hb : cl D Sc (wt D ν [dn i]) ([up i] ++ [up j, up k']) ([up k', up j] ++ [up i])
      (crossL [] i j [up k'] ++ crossL [up j] i k' [] ++ crossL [] j k' [up i]) =
      cl D Sc (wt D ν [dn i]) ([up i] ++ [up j, up k']) ([up k', up j] ++ [up i])
      (crossL [up i] j k' [] ++ crossL [] i k' [up j] ++ crossL [up k'] i j []) :=
    cl_braid Sc i j k' _ h
  have := congrArg (rotMap D Sc ν i [up j, up k'] [up k', up j]) hb
  rw [rotMap_cl, rotMap_cl, cl_rot_braid_lhs, cl_rot_braid_rhs] at this
  have := congrArg (zsign k (D.parity i * D.parity j * (D.parity i * D.parity k')) • ·) this
  simp only [smul_smul, zsign_mul_self, one_smul] at this
  exact this

/-- The correction terms of (3.8) on `Eⱼ Eᵢ Fᵢ → Fᵢ Eᵢ Eⱼ`, in the order of the paper's picture:
`s` dots on the upward leg of the cap, the cap, `q` dots on the strand `j`, the cup, `r` dots on
the upward leg of the cup. -/
def term8 (i j : I) (r q s : ℕ) : List (LayerData I) :=
  dotsL [up j] i [dn i] s ++ [([up j], Shape.cap i, [])] ++ dotsL [] j [] q ++
    [([], Shape.cup i, [up j])] ++ dotsL [dn i] i [up j] r

variable (Sc) in
/-- The rotation of dots on the bent strand. -/
theorem cl_rot_bent_dots (μ : X) (i j : I) (r : ℕ) :
    cl D Sc μ ([up j, up i] ++ [dn i]) ([dn i] ++ [up i, up j])
        (rotL i [up j, up i] [up i, up j] (dotsL [] i [up j, up i] r)) =
      cl D Sc μ ([up j, up i] ++ [dn i]) ([dn i] ++ [up i, up j])
        ([([up j], Shape.cap i, []), ([], Shape.cup i, [up j])] ++ dotsL [dn i] i [up j] r) := by
  have e0 : rotL i [up j, up i] [up i, up j] (dotsL [] i [up j, up i] r) =
      [([], Shape.cup i, [up j, up i, dn i])] ++
        (dotsL [] i [] r).map (whL [dn i] ([up j] ++ [up i, dn i] ++ [])) ++
        [([], Shape.cap i, [])].map (whL ([dn i] ++ ([] ++ [up i] ++ []) ++ [up j]) []) ++ [] := by
    simp [rotL, dotsL, whL]
  have E1 := cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := [up j, up i] ++ [dn i])
    (T := [dn i] ++ [up i, up j]) [([], Shape.cup i, [up j, up i, dn i])] [] [dn i] [up j] []
    (sChain_dotsL [] i [] r) (B := [([], Shape.cap i, [])]) (t := [up i, dn i]) (t' := [])
    ⟨rfl, rfl⟩ (Or.inr (by simp [Shape.parity]))
  have E2 := cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := [up j, up i] ++ [dn i])
    (T := [dn i] ++ [up i, up j]) [] ((dotsL [] i [] r).map (whL [dn i] ([up j] ++ [] ++ [])))
    [] [up j] [] (A := [([], Shape.cup i, [])]) (s := []) (s' := [dn i, up i])
    (B := [([], Shape.cap i, [])]) (t := [up i, dn i]) (t' := []) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    (Or.inl (by simp [Shape.parity]))
  rw [e0, E1]
  simp only [List.map_cons, List.map_nil, whL, List.nil_append, List.append_nil,
    List.cons_append] at E2 ⊢
  rw [E2]
  simp [dotsL, whL]

variable (Sc) in
/-- The rotation of the correction terms of (1.9) with `t`. -/
theorem cl_rot_tterm (μ : X) (i j : I) (r s : ℕ) :
    cl D Sc μ ([up j, up i] ++ [dn i]) ([dn i] ++ [up i, up j])
        (rotL i [up j, up i] [up i, up j]
          (dotsL [up i, up j] i [] s ++ dotsL [] i [up j, up i] r)) =
      cl D Sc μ ([up j, up i] ++ [dn i]) ([dn i] ++ [up i, up j]) (term8 i j r 0 s) := by
  rw [show dotsL [up i, up j] i [] s = (dotsL [up j] i [] s).map (whL [up i] []) by
    simp [dotsL, whL], cl_rotL_pre Sc μ i (W := [up j, up i]) (W₀ := [up j, up i]) _
      (show SChain [up j, up i] (dotsL [up j] i [] s) [up j, up i] from sChain_dotsL [up j] i [] s)]
  have h₁ : SChain ([up j, up i] ++ [dn i]) ((dotsL [up j] i [] s).map (whL [] [dn i]))
      ([up j, up i] ++ [dn i]) := (sChain_dotsL [up j] i [] s).wh [] [dn i] rfl rfl
  have h₂ : SChain ([up j, up i] ++ [dn i])
      (rotL i [up j, up i] [up i, up j] (dotsL [] i [up j, up i] r)) ([dn i] ++ [up i, up j]) :=
    sChain_rotL i (sChain_dotsL [] i [up j, up i] r)
  rw [← cl_comp h₁ h₂, cl_rot_bent_dots, cl_comp h₁ (by
    simp only [dotsL]
    exact ⟨rfl, ⟨rfl, (SChain.replicate r [dn i] i [up j])⟩⟩)]
  simp [term8, dotsL, whL, List.append_assoc]

variable (Sc) in
/-- The rotation of the correction terms of (1.9) with `s`. -/
theorem cl_rot_sterm (μ : X) (i j : I) (r q s : ℕ) :
    cl D Sc μ ([up j, up i] ++ [dn i]) ([dn i] ++ [up i, up j])
        (rotL i [up j, up i] [up i, up j]
          (dotsL [up i, up j] i [] s ++ dotsL [up i] j [up i] q ++ dotsL [] i [up j, up i] r)) =
      cl D Sc μ ([up j, up i] ++ [dn i]) ([dn i] ++ [up i, up j]) (term8 i j r q s) := by
  rw [show dotsL [up i, up j] i [] s ++ dotsL [up i] j [up i] q =
      (dotsL [up j] i [] s ++ dotsL [] j [up i] q).map (whL [up i] []) by
    simp [dotsL, whL], cl_rotL_pre Sc μ i (W := [up j, up i]) (W₀ := [up j, up i]) _
      (show SChain [up j, up i] (dotsL [up j] i [] s ++ dotsL [] j [up i] q) [up j, up i] from
        (sChain_dotsL [up j] i [] s).append (sChain_dotsL [] j [up i] q))]
  have h₁ : SChain ([up j, up i] ++ [dn i])
      ((dotsL [up j] i [] s ++ dotsL [] j [up i] q).map (whL [] [dn i]))
      ([up j, up i] ++ [dn i]) :=
    ((sChain_dotsL [up j] i [] s).append (sChain_dotsL [] j [up i] q)).wh [] [dn i] rfl rfl
  have h₂ : SChain ([up j, up i] ++ [dn i])
      (rotL i [up j, up i] [up i, up j] (dotsL [] i [up j, up i] r)) ([dn i] ++ [up i, up j]) :=
    sChain_rotL i (sChain_dotsL [] i [up j, up i] r)
  rw [← cl_comp h₁ h₂, cl_rot_bent_dots, cl_comp h₁ (by
    simp only [dotsL]
    exact ⟨rfl, ⟨rfl, (SChain.replicate r [dn i] i [up j])⟩⟩)]
  -- the `q` dots move above the cap
  have E := cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := [up j, up i] ++ [dn i])
    (T := [dn i] ++ [up i, up j]) ((dotsL [up j] i [] s).map (whL [] [dn i]))
    ([([], Shape.cup i, [up j])] ++ dotsL [dn i] i [up j] r) [] [] [] (sChain_dotsL [] j [] q)
    (B := [([], Shape.cap i, [])]) (t := [up i, dn i]) (t' := []) ⟨rfl, rfl⟩
    (Or.inr (by simp [Shape.parity]))
  simp only [List.map_cons, List.map_nil, whL, List.nil_append, List.append_nil,
    List.cons_append, List.append_assoc, List.map_append] at E ⊢
  convert E using 2 <;> simp [term8, dotsL, whL]

variable (Sc) in
theorem lemma33_eq8_eq_aux (i j : I) (ν : X) (hij : i ≠ j) :
    cl D Sc ν ([up j, up i] ++ [dn i]) ([dn i] ++ [up i, up j]) (lemma33_eq8_lhs i j i) -
        cl D Sc ν ([up j, up i] ++ [dn i]) ([dn i] ++ [up i, up j]) (lemma33_eq8_rhs i j i) =
      ∑ s ∈ Finset.range (D.dn i j),
          (zsign k (D.parity i * s) * (Sc.t i j : k)) •
            cl D Sc ν ([up j, up i] ++ [dn i]) ([dn i] ++ [up i, up j])
              (term8 i j (D.dn i j - 1 - s) 0 s) +
        ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), ∑ s ∈ Finset.range p,
          (zsign k (D.parity i * s) * Sc.s i j p q) •
            cl D Sc ν ([up j, up i] ++ [dn i]) ([dn i] ++ [up i, up j]) (term8 i j (p - 1 - s) q s) := by
  have hb : cl D Sc (wt D ν [dn i]) ([up i] ++ [up j, up i]) ([up i, up j] ++ [up i])
      (crossL [] i j [up i] ++ crossL [up j] i i [] ++ crossL [] j i [up i]) =
      cl D Sc (wt D ν [dn i]) ([up i] ++ [up j, up i]) ([up i, up j] ++ [up i])
          (crossL [up i] j i [] ++ crossL [] i i [up j] ++ crossL [up i] i j []) +
        ∑ s ∈ Finset.range (D.dn i j),
          (zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
            cl D Sc (wt D ν [dn i]) ([up i] ++ [up j, up i]) ([up i, up j] ++ [up i])
              (dotsL [up i, up j] i [] s ++ dotsL [] i [up j, up i] (D.dn i j - 1 - s)) +
        ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), ∑ s ∈ Finset.range p,
          (zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
            cl D Sc (wt D ν [dn i]) ([up i] ++ [up j, up i]) ([up i, up j] ++ [up i])
              (dotsL [up i, up j] i [] s ++ dotsL [up i] j [up i] q ++
                dotsL [] i [up j, up i] (p - 1 - s)) :=
    cl_braidEq Sc i j _ hij
  have h := congrArg (rotMap D Sc ν i [up j, up i] [up i, up j]) hb
  simp only [map_add, map_smul, map_sum, rotMap_cl] at h
  rw [cl_rot_braid_lhs, cl_rot_braid_rhs] at h
  simp only [cl_rot_tterm, cl_rot_sterm] at h
  set σ : ZMod 2 := D.parity i * D.parity j * (D.parity i * D.parity i) with hσ
  have h' := congrArg (zsign k σ • ·) h
  simp only [smul_add, Finset.smul_sum, smul_smul, zsign_mul_self, one_smul] at h'
  rw [h', add_assoc, add_sub_cancel_left]
  have hz : ∀ x : ℕ, zsign k σ * zsign k (D.parity i * (D.parity j + x)) =
      zsign k (D.parity i * x) := fun x => by
    rw [← zsign_add, hσ]
    congr 1
    generalize D.parity i = a; generalize D.parity j = b; generalize (x : ZMod 2) = c
    revert a b c; decide
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [← mul_assoc, hz]
  · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun s _ => ?_
    rw [← mul_assoc, hz]

variable (Sc) in
/-- **Brundan–Ellis, Lemma 3.3 (3.8), `i = k ≠ j`** (`term8`: the layers in the order of the
paper's picture). -/
theorem lemma33_eq8_eq (i j : I) (ν : X) (hij : i ≠ j) :
    cl D Sc ν [up j, up i, dn i] [dn i, up i, up j] (lemma33_eq8_lhs i j i) -
        cl D Sc ν [up j, up i, dn i] [dn i, up i, up j] (lemma33_eq8_rhs i j i) =
      ∑ s ∈ Finset.range (D.dn i j),
          (zsign k (D.parity i * s) * (Sc.t i j : k)) •
            cl D Sc ν [up j, up i, dn i] [dn i, up i, up j] (term8 i j (D.dn i j - 1 - s) 0 s) +
        ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), ∑ s ∈ Finset.range p,
          (zsign k (D.parity i * s) * Sc.s i j p q) •
            cl D Sc ν [up j, up i, dn i] [dn i, up i, up j] (term8 i j (p - 1 - s) q s) :=
  lemma33_eq8_eq_aux Sc i j ν hij

end OddMath.SKM
