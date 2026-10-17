/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PsiGenerators

/-!
# The reverse crossing assignment for ψ

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Proposition 9.4, the unnumbered generator display in its proof.

The upward crossing is sent to the reversed crossing in the existing
`TwoSOp k (Uqπ D Sc sy hc)`, multiplied by `t` when both colours are odd.
We prove its parity and integer degree, the equal-colour and disconnected-colour
quadratic relations (1.7), and both equal-colour dot-slide relations (1.8).
The latter use the two-strand dot assignments; their comparison with whiskering
of `psiDot`, and horizontal compatibility in general, remain to be proved.

All compositions here are compositions in the target super-opposite, including
its Koszul sign. The hypothesis `t² = -1` cancels that sign. A fixed common left
weight avoids transports between hom categories: `psiWordAt` is the same word
as `psiWord`, with its left boundary specified by an equality of weights.

This is a relation-checking slice, not the strict graded 2-superfunctor or
Proposition 9.4 itself. Connected-colour quadratic relations, distinct-colour
dot slides, braid relations, cups/caps and inversion entries, and their
compatibilities, the envelope extension and literal categorical inverse remain.
The computations work over a purely even commutative ring; a field is not needed.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

/-- A word with a specified common left boundary. -/
def psiWordAt (ν μ : X) (s : List (Letter I)) (h : wt D μ s = ν) :
    (⟨ν⟩ : UGr D Sc sy hc) ⟶ ⟨μ⟩ where
  obj := ob D μ s
  start_eq := h
  wf := ok_wd D μ s
  endR_eq := ob_endR D μ s

/-- The target word, with its parity shift, at specified boundaries. -/
abbrev psiAt (ν μ : X) (s : List (Letter I)) (h : wt D μ s = ν) :=
  psiMap (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ s h)

private theorem wt_swap (μ : X) (i j : I) :
    wt D μ [up j, up i] = wt D μ [up i, up j] := by
  simp only [wt_cons, wt_nil]
  exact add_left_comm _ _ _

/-- The reverse upward crossing, with coefficient t precisely for two odd colours. -/
def psiCross (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i, up j] = ν) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j] h ⟶
      psiAt ν μ [up j, up i] ((wt_swap μ i j).trans h) :=
  SOp.mk' (psiCoeff t (D.parity i * D.parity j) •
    cl D Sc μ [up j, up i] [up i, up j] (crossL [] j i []))

private theorem cross_mem (ν μ : X) (i j : I) (h : wt D μ [up i, up j] = ν) :
    (show SOp.unop (psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up j, up i]
      ((wt_swap μ i j).trans h)) ⟶ SOp.unop (psiAt ν μ [up i, up j] h) from
      cl D Sc μ [up j, up i] [up i, up j] (crossL [] j i [])) ∈
      parity (R := k) _ _ (D.parity i * D.parity j) := by
  change cl D Sc μ [up j, up i] [up i, up j] (crossL [] j i []) ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ (D.parity i * D.parity j + (0 + 0))
  unfold cl
  split_ifs
  · apply Presentation.diag_mem_homDeg'
    rw [degree_parity_mkD]
    simp [crossL, Shape.parity, mul_comm]
  · exact Submodule.zero_mem _

/-- The crossing assignment preserves parity. -/
theorem psiCross_mem_parity (t : k) (ν μ : X) (i j : I)
    (h : wt D μ [up i, up j] = ν) :
    psiCross (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  Submodule.smul_mem _ _ (cross_mem ν μ i j h)

/-- The crossing assignment preserves integer degree. -/
theorem psiCross_mem_degree (t : k) (ν μ : X) (i j : I)
    (h : wt D μ [up i, up j] = ν) :
    psiCross (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ∈
      GradedSupercategory.degree (R := k) _ _ (sy.d i * D.d i j) := by
  change psiCoeff t (D.parity i * D.parity j) •
    cl D Sc μ [up j, up i] [up i, up j] (crossL [] j i []) ∈
    (pres D Sc).homDeg (gdeg D sy) _ _ (sy.d i * D.d i j + (0 - 0))
  apply Submodule.smul_mem
  unfold cl
  split_ifs
  · apply Presentation.diag_mem_homDeg'
    rw [degree_gdeg_mkD]
    simpa using sy.symm j i
  · exact Submodule.zero_mem _

/-- The two square-root coefficients cancel the super-opposite composition sign. -/
theorem psiCross_comp (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (h : wt D μ [up i, up j] = ν) :
    psiCross (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ≫
      psiCross t ν μ j i ((wt_swap μ i j).trans h) =
    (show psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j] h ⟶
      psiAt ν μ [up i, up j] h from
      SOp.mk' (cl D Sc μ [up i, up j] [up i, up j]
        (crossL [] i j [] ++ crossL [] j i []))) := by
  apply SOp.hom_ext
  change SOp.compC (psiCoeff t (D.parity i * D.parity j) •
      (show SOp.unop (psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up j, up i]
        ((wt_swap μ i j).trans h)) ⟶ SOp.unop (psiAt ν μ [up i, up j] h) from
        cl D Sc μ [up j, up i] [up i, up j] (crossL [] j i [])))
    (psiCoeff t (D.parity j * D.parity i) •
      (show SOp.unop (psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j] h) ⟶
        SOp.unop (psiAt ν μ [up j, up i] ((wt_swap μ i j).trans h)) from
        cl D Sc μ [up i, up j] [up j, up i] (crossL [] i j []))) = _
  rw [SOp.smul_compC, SOp.compC_smul,
    SOp.compC_of_mem (cross_mem ν μ i j h)
      (cross_mem ν μ j i ((wt_swap μ i j).trans h)), smul_smul, smul_smul]
  have hs : psiCoeff t (D.parity i * D.parity j) *
      psiCoeff t (D.parity j * D.parity i) *
      sign k (D.parity i * D.parity j * (D.parity j * D.parity i)) = 1 := by
    rw [mul_comm (D.parity j) (D.parity i)]
    rw [mul_comm _ (sign k _), psiCoeff_comp ht]
    rcases parity_eq_zero_or_one (D.parity i * D.parity j) with hp | hp <;>
      simp [hp, show (1 : ZMod 2) + 1 = 0 from rfl]
  rw [hs, one_smul]
  change cl D Sc μ [up i, up j] [up j, up i] (crossL [] i j []) ≫
    cl D Sc μ [up j, up i] [up i, up j] (crossL [] j i []) = _
  exact cl_comp (D := D) (Sc := Sc) (μ := μ)
    (show SChain [up i, up j] (crossL [] i j []) [up j, up i] from ⟨rfl, rfl⟩)
    (show SChain [up j, up i] (crossL [] j i []) [up i, up j] from ⟨rfl, rfl⟩)

/-- The equal-colour quadratic relation (1.7) holds for the assigned crossing. -/
theorem psiCross_sq (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i : I)
    (h : wt D μ [up i, up i] = ν) :
    psiCross (Sc := Sc) (sy := sy) (hc := hc) t ν μ i i h ≫ psiCross t ν μ i i h = 0 := by
  rw [psiCross_comp t ht]
  apply SOp.hom_ext
  exact cl_quadEq Sc i μ

/-- The disconnected-colour quadratic relation (1.7) holds for the assigned crossing. -/
theorem psiCross_quadZero (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (h : wt D μ [up i, up j] = ν) (hij : i ≠ j) (hd : D.d i j = 0) :
    psiCross (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ≫
      psiCross t ν μ j i ((wt_swap μ i j).trans h) = (Sc.t i j : k) • 𝟙 _ := by
  rw [psiCross_comp t ht]
  apply SOp.hom_ext
  change cl D Sc μ [up i, up j] [up i, up j] _ = (Sc.t i j : k) • 𝟙 _
  rw [cl_quadZero Sc i j μ hij hd, cl_nil]
  rfl

/-- The dot on the left strand of a two-strand word. -/
def psiDotLeft (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i, up j] = ν) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j] h ⟶
      psiAt ν μ [up i, up j] h :=
  SOp.mk' (psiCoeff t (D.parity i) • cl D Sc μ [up i, up j] [up i, up j]
    (dotsL [] i [up j] 1))

/-- The dot on the right strand of a two-strand word. -/
def psiDotRight (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i, up j] = ν) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j] h ⟶
      psiAt ν μ [up i, up j] h :=
  SOp.mk' (psiCoeff t (D.parity j) • cl D Sc μ [up i, up j] [up i, up j]
    (dotsL [up i] j [] 1))

private theorem dotLeft_mem (ν μ : X) (i j : I) (h : wt D μ [up i, up j] = ν) :
    (show SOp.unop (psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j] h) ⟶
      SOp.unop (psiAt ν μ [up i, up j] h) from
      cl D Sc μ [up i, up j] [up i, up j] (dotsL [] i [up j] 1)) ∈
      parity (R := k) _ _ (D.parity i) := by
  change cl D Sc μ [up i, up j] [up i, up j] (dotsL [] i [up j] 1) ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ (D.parity i + (0 + 0))
  unfold cl
  split_ifs
  · apply Presentation.diag_mem_homDeg'
    rw [degree_parity_mkD]
    simp
  · exact Submodule.zero_mem _

private theorem dotRight_mem (ν μ : X) (i j : I) (h : wt D μ [up i, up j] = ν) :
    (show SOp.unop (psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j] h) ⟶
      SOp.unop (psiAt ν μ [up i, up j] h) from
      cl D Sc μ [up i, up j] [up i, up j] (dotsL [up i] j [] 1)) ∈
      parity (R := k) _ _ (D.parity j) := by
  change cl D Sc μ [up i, up j] [up i, up j] (dotsL [up i] j [] 1) ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ (D.parity j + (0 + 0))
  unfold cl
  split_ifs
  · apply Presentation.diag_mem_homDeg'
    rw [degree_parity_mkD]
    simp
  · exact Submodule.zero_mem _

private theorem psi_compC {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {A B C' : C} {f : B ⟶ A} {g : C' ⟶ B} {p q : ZMod 2}
    (hf : f ∈ parity (R := k) _ _ p) (hg : g ∈ parity (R := k) _ _ q)
    (t : k) (ht : t ^ 2 = -1) :
    SOp.compC (R := k) (psiCoeff t p • f) (psiCoeff t q • g) = psiCoeff t (p + q) • (g ≫ f) := by
  rw [SOp.smul_compC, SOp.compC_smul, SOp.compC_of_mem hf hg, smul_smul, smul_smul]
  congr 1
  calc
    _ = sign k (p * q) * (psiCoeff t q * psiCoeff t p) := by ring
    _ = _ := psiCoeff_comp ht p q

private theorem parity_square (p : ZMod 2) : p * p = p := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;> rfl

private theorem psiCoeff_double (t : k) (p : ZMod 2) : psiCoeff t (p + p) = 1 := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [show (1 : ZMod 2) + 1 = 0 from rfl]

/-- The first equal-colour dot-slide relation (1.8) holds for the assigned generators. -/
theorem psi_slideLEq (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i : I)
    (h : wt D μ [up i, up i] = ν) :
    psiDotLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i i h ≫ psiCross t ν μ i i h =
      zsign k (D.parity i * D.parity i) •
        (psiCross t ν μ i i h ≫ psiDotRight t ν μ i i h) + 𝟙 _ := by
  apply SOp.hom_ext
  change SOp.compC (psiCoeff t (D.parity i) • _) (psiCoeff t (D.parity i * D.parity i) • _) =
    zsign k (D.parity i * D.parity i) •
      SOp.compC (psiCoeff t (D.parity i * D.parity i) • _) (psiCoeff t (D.parity i) • _) + _
  rw [psi_compC (dotLeft_mem ν μ i i h) (cross_mem ν μ i i h) t ht,
    psi_compC (cross_mem ν μ i i h) (dotRight_mem ν μ i i h) t ht,
    parity_square, psiCoeff_double, one_smul, one_smul]
  change cl D Sc μ [up i, up i] [up i, up i] (crossL [] i i []) ≫
    cl D Sc μ [up i, up i] [up i, up i] (dotsL [] i [up i] 1) =
    zsign k (D.parity i) •
      (cl D Sc μ [up i, up i] [up i, up i] (dotsL [up i] i [] 1) ≫
        cl D Sc μ [up i, up i] [up i, up i] (crossL [] i i [])) + 𝟙 ((pres D Sc).obj (ob D μ [up i, up i]))
  have H := cl_slideREq Sc i μ
  rw [parity_square] at H
  exact (cl_comp (D := D) (Sc := Sc) (μ := μ)
    (show SChain [up i, up i] (crossL [] i i []) [up i, up i] from ⟨rfl, rfl⟩)
    (sChain_dotsL [] i [up i] 1)).trans (H.trans (congrArg₂ (· + ·)
      (congrArg (zsign k (D.parity i) • ·)
        (cl_comp (D := D) (Sc := Sc) (μ := μ) (sChain_dotsL [up i] i [] 1)
          (show SChain [up i, up i] (crossL [] i i []) [up i, up i] from ⟨rfl, rfl⟩)).symm)
      (cl_nil (D := D) (Sc := Sc) μ [up i, up i])))

/-- The second equal-colour dot-slide relation (1.8) holds for the assigned generators. -/
theorem psi_slideREq (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i : I)
    (h : wt D μ [up i, up i] = ν) :
    psiCross (Sc := Sc) (sy := sy) (hc := hc) t ν μ i i h ≫ psiDotLeft t ν μ i i h =
      zsign k (D.parity i * D.parity i) •
        (psiDotRight t ν μ i i h ≫ psiCross t ν μ i i h) + 𝟙 _ := by
  apply SOp.hom_ext
  change SOp.compC (psiCoeff t (D.parity i * D.parity i) • _) (psiCoeff t (D.parity i) • _) =
    zsign k (D.parity i * D.parity i) •
      SOp.compC (psiCoeff t (D.parity i) • _) (psiCoeff t (D.parity i * D.parity i) • _) + _
  rw [psi_compC (cross_mem ν μ i i h) (dotLeft_mem ν μ i i h) t ht,
    psi_compC (dotRight_mem ν μ i i h) (cross_mem ν μ i i h) t ht,
    parity_square, psiCoeff_double, one_smul, one_smul]
  change cl D Sc μ [up i, up i] [up i, up i] (dotsL [] i [up i] 1) ≫
    cl D Sc μ [up i, up i] [up i, up i] (crossL [] i i []) =
    zsign k (D.parity i) •
      (cl D Sc μ [up i, up i] [up i, up i] (crossL [] i i []) ≫
        cl D Sc μ [up i, up i] [up i, up i] (dotsL [up i] i [] 1)) + 𝟙 ((pres D Sc).obj (ob D μ [up i, up i]))
  have H := cl_slideLEq Sc i μ
  rw [parity_square] at H
  exact (cl_comp (D := D) (Sc := Sc) (μ := μ) (sChain_dotsL [] i [up i] 1)
    (show SChain [up i, up i] (crossL [] i i []) [up i, up i] from ⟨rfl, rfl⟩)).trans
    (H.trans (congrArg₂ (· + ·)
      (congrArg (zsign k (D.parity i) • ·)
        (cl_comp (D := D) (Sc := Sc) (μ := μ)
          (show SChain [up i, up i] (crossL [] i i []) [up i, up i] from ⟨rfl, rfl⟩)
          (sChain_dotsL [up i] i [] 1)).symm)
      (cl_nil (D := D) (Sc := Sc) μ [up i, up i])))
end OddMath.SKM
