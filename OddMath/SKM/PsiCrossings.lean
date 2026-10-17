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
We prove its parity and integer degree, every quadratic relation (1.7), and
both dot-slide relations (1.8), including their equal-colour corrections.
The two-strand dot assignments are the left and right whiskerings of `psiDot`;
the connected quadratic polynomial is evaluated in powers of these assignments.
The scalar parity conditions eliminate the potentially odd polynomial terms.

All compositions here are compositions in the target super-opposite, including
its Koszul sign. The hypothesis `t² = -1` cancels that sign. A fixed common left
weight avoids transports between hom categories: `psiWordAt` is the same word
as `psiWord`, with its left boundary specified by an equality of weights.

This is a relation-checking slice, not the strict graded 2-superfunctor or
Proposition 9.4 itself. Braid relations, cups/caps and inversion entries,
global horizontal compatibility, the envelope extension and literal categorical
inverse remain.
The computations work over a purely even commutative ring; a field is not needed.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory
open BicategoryStruct
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

/-- Right whiskering of the assigned dot gives the left two-strand dot. -/
theorem psiDot_whiskerRight (t : k) (μ : X) (i j : I) :
    BicategoryStruct.whiskerRight (B := TwoSOp k (Uqπ D Sc sy hc))
      (psiDot t (wt D μ [up j]) i) (psiE μ j) =
      psiDotLeft (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up i, up j]) μ i j rfl := by
  apply SOp.hom_ext
  rw [TwoSOp.unsop_whiskerRight]
  apply Envelope.hom_ext
  rw [TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl]
  change (pres D Sc).wRAt _
    (psiCoeff t (1 * D.parity i) • cl D Sc (wt D μ [up j]) [up i] [up i] (dotsL [] i [] 1))
    (ob D μ [up j]) rfl rfl =
    psiCoeff t (D.parity i) • cl D Sc μ [up i, up j] [up i, up j] (dotsL [] i [up j] 1)
  rw [Presentation.wRAt_smul]
  simp only [one_mul]
  apply congrArg (psiCoeff t (D.parity i) • ·)
  refine (congrArg (fun f => (pres D Sc).wRAt _ f (ob D μ [up j]) rfl rfl)
    (cl_of (D := D) (Sc := Sc) (μ := wt D μ [up j]) (sChain_dotsL [] i [] 1))).trans ?_
  refine (Presentation.wRAt_diag _ _ _ (Presentation.Bicat.Hom.composable
    (psiWord (Sc := Sc) (wt D μ [up j]) [up i]) (psiWord μ [up j])) _ _).trans ?_
  exact (Presentation.diag_eq_of_layers_eq _ (show _ = _ from rfl)).trans
    (cl_of (D := D) (Sc := Sc) (μ := μ) (sChain_dotsL [] i [up j] 1)).symm

/-- Left whiskering of the assigned dot gives the right two-strand dot. -/
theorem psiDot_whiskerLeft (t : k) (μ : X) (i j : I) :
    BicategoryStruct.whiskerLeft (B := TwoSOp k (Uqπ D Sc sy hc))
      (psiE (wt D μ [up j]) i) (psiDot t μ j) =
      psiDotRight (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up i, up j]) μ i j rfl := by
  apply SOp.hom_ext
  rw [TwoSOp.unsop_whiskerLeft]
  apply Envelope.hom_ext
  rw [TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl]
  change (pres D Sc).wL (ob D (wt D μ [up j]) [up i])
    (psiCoeff t (1 * D.parity j) • cl D Sc μ [up j] [up j] (dotsL [] j [] 1)) =
    psiCoeff t (D.parity j) • cl D Sc μ [up i, up j] [up i, up j] (dotsL [up i] j [] 1)
  rw [Presentation.wL_smul]
  simp only [one_mul]
  apply congrArg (psiCoeff t (D.parity j) • ·)
  refine (congrArg ((pres D Sc).wL (ob D (wt D μ [up j]) [up i]))
    (cl_of (D := D) (Sc := Sc) (μ := μ) (sChain_dotsL [] j [] 1))).trans ?_
  refine (Presentation.wL_diag_of_composable _ _ _ (Presentation.Bicat.Hom.composable
    (psiWord (Sc := Sc) (wt D μ [up j]) [up i]) (psiWord μ [up j]))).trans ?_
  exact (Presentation.diag_eq_of_layers_eq _ (show _ = _ from rfl)).trans
    (cl_of (D := D) (Sc := Sc) (μ := μ) (sChain_dotsL [up i] j [] 1)).symm


/-- The first distinct-colour dot-slide equation (1.8). -/
theorem psi_slideL (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (h : wt D μ [up i, up j] = ν) (hij : i ≠ j) :
    psiDotLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ≫ psiCross t ν μ i j h =
      zsign k (D.parity i * D.parity j) •
        (psiCross t ν μ i j h ≫ psiDotRight t ν μ j i ((wt_swap μ i j).trans h)) := by
  apply SOp.hom_ext
  change SOp.compC (psiCoeff t (D.parity i) • _) (psiCoeff t (D.parity i * D.parity j) • _) =
    zsign k (D.parity i * D.parity j) •
      SOp.compC (psiCoeff t (D.parity i * D.parity j) • _) (psiCoeff t (D.parity i) • _)
  rw [psi_compC (dotLeft_mem ν μ i j h) (cross_mem ν μ i j h) t ht,
    psi_compC (cross_mem ν μ i j h) (dotRight_mem ν μ j i ((wt_swap μ i j).trans h)) t ht,
    add_comm (D.parity i) (D.parity i * D.parity j), smul_comm]
  apply congrArg (psiCoeff t (D.parity i * D.parity j + D.parity i) • ·)
  change cl D Sc μ [up j, up i] [up i, up j] (crossL [] j i []) ≫
    cl D Sc μ [up i, up j] [up i, up j] (dotsL [] i [up j] 1) =
    zsign k (D.parity i * D.parity j) •
      (cl D Sc μ [up j, up i] [up j, up i] (dotsL [up j] i [] 1) ≫
        cl D Sc μ [up j, up i] [up i, up j] (crossL [] j i []))
  have H := cl_slideR Sc j i μ hij.symm
  rw [mul_comm (D.parity j) (D.parity i)] at H
  exact (cl_comp (D := D) (Sc := Sc) (μ := μ)
    (show SChain [up j, up i] (crossL [] j i []) [up i, up j] from ⟨rfl, rfl⟩)
    (sChain_dotsL [] i [up j] 1)).trans (H.trans (congrArg (zsign k (D.parity i * D.parity j) • ·)
      (cl_comp (D := D) (Sc := Sc) (μ := μ) (sChain_dotsL [up j] i [] 1)
        (show SChain [up j, up i] (crossL [] j i []) [up i, up j] from ⟨rfl, rfl⟩)).symm))

/-- The second distinct-colour dot-slide equation (1.8). -/
theorem psi_slideR (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (h : wt D μ [up i, up j] = ν) (hij : i ≠ j) :
    psiCross (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ≫
      psiDotLeft t ν μ j i ((wt_swap μ i j).trans h) =
      zsign k (D.parity i * D.parity j) •
        (psiDotRight t ν μ i j h ≫ psiCross t ν μ i j h) := by
  apply SOp.hom_ext
  change SOp.compC (psiCoeff t (D.parity i * D.parity j) • _) (psiCoeff t (D.parity j) • _) =
    zsign k (D.parity i * D.parity j) •
      SOp.compC (psiCoeff t (D.parity j) • _) (psiCoeff t (D.parity i * D.parity j) • _)
  rw [psi_compC (cross_mem ν μ i j h) (dotLeft_mem ν μ j i ((wt_swap μ i j).trans h)) t ht,
    psi_compC (dotRight_mem ν μ i j h) (cross_mem ν μ i j h) t ht,
    add_comm (D.parity j) (D.parity i * D.parity j), smul_comm]
  apply congrArg (psiCoeff t (D.parity i * D.parity j + D.parity j) • ·)
  change cl D Sc μ [up j, up i] [up j, up i] (dotsL [] j [up i] 1) ≫
    cl D Sc μ [up j, up i] [up i, up j] (crossL [] j i []) =
    zsign k (D.parity i * D.parity j) •
      (cl D Sc μ [up j, up i] [up i, up j] (crossL [] j i []) ≫
        cl D Sc μ [up i, up j] [up i, up j] (dotsL [up i] j [] 1))
  have H := cl_slideL Sc j i μ hij.symm
  rw [mul_comm (D.parity j) (D.parity i)] at H
  exact (cl_comp (D := D) (Sc := Sc) (μ := μ) (sChain_dotsL [] j [up i] 1)
    (show SChain [up j, up i] (crossL [] j i []) [up i, up j] from ⟨rfl, rfl⟩)).trans
    (H.trans (congrArg (zsign k (D.parity i * D.parity j) • ·)
      (cl_comp (D := D) (Sc := Sc) (μ := μ)
        (show SChain [up j, up i] (crossL [] j i []) [up i, up j] from ⟨rfl, rfl⟩)
        (sChain_dotsL [up i] j [] 1)).symm))

/-- Powers of the left assigned dot, computed in the super-opposite. -/
theorem psiDotLeft_power (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (h : wt D μ [up i, up j] = ν) (n : ℕ) :
    cpow (psiDotLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h) n =
      SOp.mk' (X := psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j] h)
        (Y := psiAt ν μ [up i, up j] h) (psiCoeff t (n * D.parity i) •
        cl D Sc μ [up i, up j] [up i, up j] (dotsL [] i [up j] n)) := by
  apply SOp.hom_ext
  refine (psi_cpow (dotLeft_mem (Sc := Sc) (sy := sy) (hc := hc) ν μ i j h) ht n).trans ?_
  apply congrArg (psiCoeff t (n * D.parity i) • ·)
  induction n with
  | zero =>
    change 𝟙 ((pres D Sc).obj (ob D μ [up i, up j])) = _
    exact (cl_nil μ [up i, up j]).symm
  | succ n ih =>
    rw [cpow_succ, ih]
    change cl D Sc μ [up i, up j] [up i, up j] (dotsL [] i [up j] n) ≫
      cl D Sc μ [up i, up j] [up i, up j] (dotsL [] i [up j] 1) = _
    rw [cl_dotsL_eq_pow (D := D) (Sc := Sc) (s := [up i, up j]) μ [] i [up j] n rfl,
      cl_dotsL_eq_pow (D := D) (Sc := Sc) (s := [up i, up j]) μ [] i [up j] (n + 1) rfl]
    rfl

/-- Powers of the right assigned dot, computed in the super-opposite. -/
theorem psiDotRight_power (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (h : wt D μ [up i, up j] = ν) (n : ℕ) :
    cpow (psiDotRight (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h) n =
      SOp.mk' (X := psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j] h)
        (Y := psiAt ν μ [up i, up j] h) (psiCoeff t (n * D.parity j) •
        cl D Sc μ [up i, up j] [up i, up j] (dotsL [up i] j [] n)) := by
  apply SOp.hom_ext
  refine (psi_cpow (dotRight_mem (Sc := Sc) (sy := sy) (hc := hc) ν μ i j h) ht n).trans ?_
  apply congrArg (psiCoeff t (n * D.parity j) • ·)
  induction n with
  | zero =>
    change 𝟙 ((pres D Sc).obj (ob D μ [up i, up j])) = _
    exact (cl_nil μ [up i, up j]).symm
  | succ n ih =>
    rw [cpow_succ, ih]
    change cl D Sc μ [up i, up j] [up i, up j] (dotsL [up i] j [] n) ≫
      cl D Sc μ [up i, up j] [up i, up j] (dotsL [up i] j [] 1) = _
    rw [cl_dotsL_eq_pow (D := D) (Sc := Sc) (s := [up i, up j]) μ [up i] j [] n rfl,
      cl_dotsL_eq_pow (D := D) (Sc := Sc) (s := [up i, up j]) μ [up i] j [] (n + 1) rfl]
    rfl


private theorem dotRight_pow_mem (ν μ : X) (i j : I) (h : wt D μ [up i, up j] = ν) (n : ℕ) :
    (show SOp.unop (psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j] h) ⟶
      SOp.unop (psiAt ν μ [up i, up j] h) from
      cl D Sc μ [up i, up j] [up i, up j] (dotsL [up i] j [] n)) ∈
      parity (R := k) _ _ (n * D.parity j) := by
  change cl D Sc μ [up i, up j] [up i, up j] (dotsL [up i] j [] n) ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ (n * D.parity j + (0 + 0))
  unfold cl
  split_ifs
  · apply Presentation.diag_mem_homDeg'
    rw [degree_parity_mkD]
    simp
  · exact Submodule.zero_mem _

private theorem dotLeft_pow_mem (ν μ : X) (i j : I) (h : wt D μ [up i, up j] = ν) (n : ℕ) :
    (show SOp.unop (psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j] h) ⟶
      SOp.unop (psiAt ν μ [up i, up j] h) from
      cl D Sc μ [up i, up j] [up i, up j] (dotsL [] i [up j] n)) ∈
      parity (R := k) _ _ (n * D.parity i) := by
  change cl D Sc μ [up i, up j] [up i, up j] (dotsL [] i [up j] n) ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ (n * D.parity i + (0 + 0))
  unfold cl
  split_ifs
  · apply Presentation.diag_mem_homDeg'
    rw [degree_parity_mkD]
    simp
  · exact Submodule.zero_mem _

private theorem psiDot_monomial (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (h : wt D μ [up i, up j] = ν) (p q : ℕ)
    (hp : (p : ZMod 2) * D.parity i = 0) (hq : (q : ZMod 2) * D.parity j = 0) :
    cpow (psiDotLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h) p ≫
      cpow (psiDotRight t ν μ i j h) q =
      SOp.mk' (X := psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j] h)
        (Y := psiAt ν μ [up i, up j] h)
        (cl D Sc μ [up i, up j] [up i, up j]
          (dotsL [up i] j [] q ++ dotsL [] i [up j] p)) := by
  rw [psiDotLeft_power t ht, psiDotRight_power t ht]
  apply SOp.hom_ext
  change SOp.compC (psiCoeff t (p * D.parity i) • _) (psiCoeff t (q * D.parity j) • _) = _
  rw [psi_compC (dotLeft_pow_mem ν μ i j h p) (dotRight_pow_mem ν μ i j h q) t ht,
    hp, hq, add_zero, psiCoeff_zero, one_smul]
  exact cl_comp (D := D) (Sc := Sc) (μ := μ) (sChain_dotsL [up i] j [] q) (sChain_dotsL [] i [up j] p)

/-- The connected-colour quadratic relation (1.7), with polynomial in assigned dots. -/
theorem psiCross_quadNe (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (h : wt D μ [up i, up j] = ν) (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    psiCross (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ≫
      psiCross t ν μ j i ((wt_swap μ i j).trans h) =
      (Sc.t i j : k) • cpow (psiDotLeft t ν μ i j h) (D.dn i j) +
      (Sc.t j i : k) • cpow (psiDotRight t ν μ i j h) (D.dn j i) +
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        Sc.s i j p q • (cpow (psiDotLeft t ν μ i j h) p ≫ cpow (psiDotRight t ν μ i j h) q) := by
  classical
  have hs (p q : ℕ) : Sc.s i j p q •
      (cpow (psiDotLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h) p ≫
        cpow (psiDotRight t ν μ i j h) q) =
      Sc.s i j p q • SOp.mk' (X := psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j] h)
        (Y := psiAt ν μ [up i, up j] h)
        (cl D Sc μ [up i, up j] [up i, up j] (dotsL [up i] j [] q ++ dotsL [] i [up j] p)) := by
    by_cases hz : Sc.s i j p q = 0
    · simp [hz]
    · rw [psiDot_monomial t ht ν μ i j h p q (Sc.parity_of_ne_zero hz).1 (Sc.parity_of_ne_zero hz).2]
  simp_rw [hs]
  rw [psiCross_comp t ht, psiDotLeft_power t ht, psiDotRight_power t ht,
    mul_comm (D.dn i j : ZMod 2), mul_comm (D.dn j i : ZMod 2),
    parity_mul_dn, parity_mul_dn, psiCoeff_zero, one_smul, one_smul]
  let L : ((pres D Sc).obj (ob D μ [up i, up j]) ⟶ (pres D Sc).obj (ob D μ [up i, up j])) →ₗ[k]
      (psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j] h ⟶ psiAt ν μ [up i, up j] h) :=
    { toFun := fun f => SOp.mk' (X := psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j] h)
        (Y := psiAt ν μ [up i, up j] h) f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (congrArg L (cl_quadNe Sc i j μ hij hd)).trans (by
    simp only [map_add, map_smul, map_sum]
    rfl)

end OddMath.SKM
