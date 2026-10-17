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
We prove its parity and integer degree, every quadratic relation (1.7), both
dot-slide relations (1.8), and both braid cases (1.9). The two- and three-strand
dots and adjacent crossings are compared with actual whiskerings. The quadratic
and braid corrections are polynomials in powers of the assigned dots. The braid
monomials retain the horizontal order: right strand, middle strand, left strand.
The scalar parity conditions justify reversing this order without an extra sign.

All compositions here are compositions in the target super-opposite, including
its Koszul sign. The hypothesis `t² = -1` cancels that sign. A fixed common left
weight keeps the comparisons in one hom category: `psiWordAt` is the same word
as `psiWord`, with its left boundary specified by an equality of weights.
Left whiskering of a crossing includes the canonical equality of target words.

This is a relation-checking slice, not the strict graded 2-superfunctor or
Proposition 9.4 itself. Cups/caps and inversion entries,
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

/-! ## Three upward strands -/

private theorem wt_three_swap₁ (μ : X) (i j l : I) :
    wt D μ [up j, up i, up l] = wt D μ [up i, up j, up l] := by
  simp only [wt_cons, wt_nil]
  abel

private theorem wt_three_swap₂ (μ : X) (i j l : I) :
    wt D μ [up i, up l, up j] = wt D μ [up i, up j, up l] := by
  simp only [wt_cons, wt_nil]
  abel

/-- Crossing the first two strands of an upward triple. -/
def psiCross₁ (t : k) (ν μ : X) (i j l : I)
    (h : wt D μ [up i, up j, up l] = ν) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j, up l] h ⟶
      psiAt ν μ [up j, up i, up l] ((wt_three_swap₁ μ i j l).trans h) :=
  SOp.mk' (psiCoeff t (D.parity i * D.parity j) •
    cl D Sc μ [up j, up i, up l] [up i, up j, up l] (crossL [] j i [up l]))

/-- Crossing the last two strands of an upward triple. -/
def psiCross₂ (t : k) (ν μ : X) (i j l : I)
    (h : wt D μ [up i, up j, up l] = ν) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j, up l] h ⟶
      psiAt ν μ [up i, up l, up j] ((wt_three_swap₂ μ i j l).trans h) :=
  SOp.mk' (psiCoeff t (D.parity j * D.parity l) •
    cl D Sc μ [up i, up l, up j] [up i, up j, up l] (crossL [up i] l j []))

/-- The first crossing of a triple is right whiskering of `psiCross`. -/
theorem psiCross_whiskerRight (t : k) (μ : X) (i j l : I) :
    BicategoryStruct.whiskerRight (B := TwoSOp k (Uqπ D Sc sy hc))
      (psiCross t (wt D μ [up i, up j, up l]) (wt D μ [up l]) i j rfl)
      (psiE μ l) =
      psiCross₁ (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up i, up j, up l]) μ i j l rfl := by
  apply SOp.hom_ext
  rw [TwoSOp.unsop_whiskerRight]
  apply Envelope.hom_ext
  rw [TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl]
  change (pres D Sc).wRAt _
    (psiCoeff t (D.parity i * D.parity j) •
      cl D Sc (wt D μ [up l]) [up j, up i] [up i, up j] (crossL [] j i []))
    (ob D μ [up l]) (wt_swap (wt D μ [up l]) i j) rfl = _
  rw [Presentation.wRAt_smul]
  apply congrArg (psiCoeff t (D.parity i * D.parity j) • ·)
  have hc : SChain [up j, up i] (crossL [] j i []) [up i, up j] := ⟨rfl, rfl⟩
  refine (congrArg (fun f => (pres D Sc).wRAt _ f (ob D μ [up l]) (wt_swap (wt D μ [up l]) i j) rfl)
    (cl_of (D := D) (Sc := Sc) (μ := wt D μ [up l]) hc)).trans ?_
  refine (Presentation.wRAt_diag _ _ _ (Presentation.Bicat.Hom.composable
    (psiWord (Sc := Sc) (wt D μ [up l]) [up j, up i]) (psiWord μ [up l])) _ _).trans ?_
  exact (Presentation.diag_eq_of_layers_eq _ (show _ = _ from rfl)).trans
    (cl_of (D := D) (Sc := Sc) (μ := μ)
      (show SChain [up j, up i, up l] (crossL [] j i [up l]) [up i, up j, up l] from ⟨rfl, rfl⟩)).symm

/-- The canonical target-word equality for left whiskering of a crossing. -/
theorem psiCross₂_target (μ : X) (i j l : I) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [up i, up j, up l]) μ
      [up i, up l, up j] (wt_three_swap₂ μ i j l) =
      psiE (wt D μ [up j, up l]) i ≫
        psiAt (wt D μ [up j, up l]) μ [up l, up j] (wt_swap μ j l) := by
  apply SOp.ext
  apply Envelope.ext
  · rfl
  apply QEnvelope.ext
  · rfl
  apply Presentation.Bicat.Hom.ext
  apply Obj.ext
  · exact wt_three_swap₂ μ i j l
  · change wd D μ [up i, up l, up j] =
      wd D (wt D μ [up j, up l]) [up i] ++ wd D μ [up l, up j]
    rw [show [up i, up l, up j] = [up i] ++ [up l, up j] from rfl, wd_append, wt_swap μ j l]

private theorem unsop_comp_eqToHom {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {A B C' : SOp k C} (f : A ⟶ B) (h : B = C') :
    SOp.unsop (f ≫ eqToHom h) = eqToHom (congrArg SOp.unop h.symm) ≫ SOp.unsop f := by
  subst h
  simp

private theorem triple_toHom_eqToHom {a b : UGr D Sc sy hc}
    {f g : (⟨⟨a⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨b⟩⟩} (h : f = g) :
    Envelope.toHom (eqToHom h) =
      (show (pres D Sc).obj f.obj.obj.obj ⟶ (pres D Sc).obj g.obj.obj.obj from
        eqToHom (congrArg (fun z => (pres D Sc).obj z.obj.obj.obj) h)) := by
  subst h
  rfl

/-- Left whiskering, with the canonical equality of its target word. -/
theorem psiCross_whiskerLeft (t : k) (μ : X) (i j l : I) :
    BicategoryStruct.whiskerLeft (B := TwoSOp k (Uqπ D Sc sy hc))
      (psiE (wt D μ [up j, up l]) i)
      (psiCross t (wt D μ [up j, up l]) μ j l rfl) =
      psiCross₂ (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up i, up j, up l]) μ i j l rfl ≫
        eqToHom (psiCross₂_target μ i j l) := by
  apply SOp.hom_ext
  rw [TwoSOp.unsop_whiskerLeft, unsop_comp_eqToHom]
  apply Envelope.hom_ext
  rw [TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl]
  change (pres D Sc).wL (ob D (wt D μ [up j, up l]) [up i])
    (psiCoeff t (D.parity j * D.parity l) • cl D Sc μ [up l, up j] [up j, up l] (crossL [] l j [])) = _
  rw [Presentation.wL_smul, Envelope.toHom_comp]
  rw [triple_toHom_eqToHom]
  change _ = eqToHom _ ≫ (psiCoeff t (D.parity j * D.parity l) •
    cl D Sc μ [up i, up l, up j] [up i, up j, up l] (crossL [up i] l j []))
  rw [Linear.comp_smul]
  apply congrArg (psiCoeff t (D.parity j * D.parity l) • ·)
  have hcross : SChain [up l, up j] (crossL [] l j []) [up j, up l] := ⟨rfl, rfl⟩
  rw [cl_of hcross]
  refine (Presentation.wL_diag_of_composable _ _ _
    (Presentation.Bicat.Hom.composable
      (psiWordAt (Sc := Sc) (wt D μ [up i, up j, up l]) (wt D μ [up j, up l]) [up i] rfl)
      (psiWordAt (Sc := Sc) (wt D μ [up j, up l]) μ [up l, up j] (wt_swap μ j l)))).trans ?_
  rw [cl_of (show SChain [up i, up l, up j] (crossL [up i] l j []) [up i, up j, up l] from ⟨rfl, rfl⟩),
    Presentation.eqToHom_obj, ← Presentation.diag_comp]
  apply Presentation.diag_eq_of_layers_eq
  simp only [Diagram.layers_comp, Diagram.layers_eqToHom, List.nil_append,
    Diagram.layers_lwhisker, layers_mkD]
  simp only [crossL, layList, List.map_cons, List.map_nil]
  congr 1
  apply Layer.ext
  · change wt D μ [up i, up j, up l] = wt D μ [up i, up l, up j]
    exact (wt_three_swap₂ μ i j l).symm
  · change wd D (wt D μ [up j, up l]) [up i] = wd D (wt D μ [up l, up j]) [up i]
    rw [wt_swap μ j l]
  · rfl
  · rfl

private theorem triple_cl_mem (ν μ : X) (i j l a b c : I)
    (h : wt D μ [up i, up j, up l] = ν) (h' : wt D μ [up a, up b, up c] = ν)
    (L : List (LayerData I)) (p : ZMod 2)
    (hp : (L.map (fun x => x.2.1.parity D)).sum = p) :
    (show SOp.unop (psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j, up l] h) ⟶
      SOp.unop (psiAt ν μ [up a, up b, up c] h') from
      cl D Sc μ [up i, up j, up l] [up a, up b, up c] L) ∈ parity (R := k) _ _ p := by
  change cl D Sc μ [up i, up j, up l] [up a, up b, up c] L ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ (p + (0 + 0))
  unfold cl
  split_ifs
  · apply Presentation.diag_mem_homDeg'
    rw [degree_parity_mkD]
    simpa using hp
  · exact Submodule.zero_mem _

private theorem psi_compC_three {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {A B C' E : C} {f : B ⟶ A} {g : C' ⟶ B} {e : E ⟶ C'}
    {p q r : ZMod 2} (hf : f ∈ parity (R := k) _ _ p)
    (hg : g ∈ parity (R := k) _ _ q) (he : e ∈ parity (R := k) _ _ r)
    (t : k) (ht : t ^ 2 = -1) :
    SOp.compC (R := k) (psiCoeff t p • f)
      (SOp.compC (R := k) (psiCoeff t q • g) (psiCoeff t r • e)) =
      psiCoeff t (p + (q + r)) • (e ≫ g ≫ f) := by
  rw [psi_compC hg he t ht]
  have heg : e ≫ g ∈ parity (R := k) _ _ (q + r) := by
    simpa only [add_comm] using comp_mem he hg
  rw [psi_compC hf heg t ht, Category.assoc]

/-- The left braid word, formed from the two whiskered crossing assignments. -/
def psiBraidLeft (t : k) (ν μ : X) (i j l : I)
    (h : wt D μ [up i, up j, up l] = ν) :=
  psiCross₁ (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j l h ≫
    psiCross₂ t ν μ j i l ((wt_three_swap₁ μ i j l).trans h) ≫
      psiCross₁ t ν μ j l i ((wt_three_swap₂ μ j i l).trans ((wt_three_swap₁ μ i j l).trans h))

/-- The right braid word, formed from the two whiskered crossing assignments. -/
def psiBraidRight (t : k) (ν μ : X) (i j l : I)
    (h : wt D μ [up i, up j, up l] = ν) :=
  psiCross₂ (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j l h ≫
    psiCross₁ t ν μ i l j ((wt_three_swap₂ μ i j l).trans h) ≫
      psiCross₂ t ν μ l i j ((wt_three_swap₁ μ i l j).trans ((wt_three_swap₂ μ i j l).trans h))

private theorem psiBraidLeft_unsop (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j l : I)
    (h : wt D μ [up i, up j, up l] = ν) :
    SOp.unsop (psiBraidLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j l h) =
      psiCoeff t (D.parity i * D.parity j + (D.parity i * D.parity l + D.parity j * D.parity l)) •
        cl D Sc μ [up l, up j, up i] [up i, up j, up l]
          (crossL [] l j [up i] ++ crossL [up j] l i [] ++ crossL [] j i [up l]) := by
  have h₁ := (wt_three_swap₁ μ i j l).trans h
  have h₂ := (wt_three_swap₂ μ j i l).trans h₁
  have h₃ := (wt_three_swap₁ μ j l i).trans h₂
  change SOp.compC (R := k) (psiCoeff t (D.parity i * D.parity j) • _)
    (SOp.compC (R := k) (psiCoeff t (D.parity i * D.parity l) • _)
      (psiCoeff t (D.parity j * D.parity l) • _)) = _
  rw [psi_compC_three
    (triple_cl_mem ν μ j i l i j l h₁ h
      (crossL [] j i [up l]) (D.parity i * D.parity j) (by simp [crossL, Shape.parity, mul_comm]))
    (triple_cl_mem ν μ j l i j i l h₂ h₁
      (crossL [up j] l i []) (D.parity i * D.parity l) (by simp [crossL, Shape.parity, mul_comm]))
    (triple_cl_mem ν μ l j i j l i h₃ h₂
      (crossL [] l j [up i]) (D.parity j * D.parity l) (by simp [crossL, Shape.parity, mul_comm]))
    t ht]
  apply congrArg (psiCoeff t _ • ·)
  change cl D Sc μ [up l, up j, up i] [up j, up l, up i] (crossL [] l j [up i]) ≫
    cl D Sc μ [up j, up l, up i] [up j, up i, up l] (crossL [up j] l i []) ≫
      cl D Sc μ [up j, up i, up l] [up i, up j, up l] (crossL [] j i [up l]) = _
  rw [← Category.assoc, cl_comp
    (show SChain [up l, up j, up i] (crossL [] l j [up i]) [up j, up l, up i] from ⟨rfl, rfl⟩)
    (show SChain [up j, up l, up i] (crossL [up j] l i []) [up j, up i, up l] from ⟨rfl, rfl⟩),
    cl_comp
    ((show SChain [up l, up j, up i] (crossL [] l j [up i]) [up j, up l, up i] from ⟨rfl, rfl⟩).append
      (show SChain [up j, up l, up i] (crossL [up j] l i []) [up j, up i, up l] from ⟨rfl, rfl⟩))
    (show SChain [up j, up i, up l] (crossL [] j i [up l]) [up i, up j, up l] from ⟨rfl, rfl⟩)]

private theorem psiBraidRight_unsop (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j l : I)
    (h : wt D μ [up i, up j, up l] = ν) :
    SOp.unsop (psiBraidRight (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j l h) =
      psiCoeff t (D.parity i * D.parity j + (D.parity i * D.parity l + D.parity j * D.parity l)) •
        cl D Sc μ [up l, up j, up i] [up i, up j, up l]
          (crossL [up l] j i [] ++ crossL [] l i [up j] ++ crossL [up i] l j []) := by
  have h₁ := (wt_three_swap₂ μ i j l).trans h
  have h₂ := (wt_three_swap₁ μ i l j).trans h₁
  have h₃ := (wt_three_swap₂ μ l i j).trans h₂
  change SOp.compC (R := k) (psiCoeff t (D.parity j * D.parity l) • _)
    (SOp.compC (R := k) (psiCoeff t (D.parity i * D.parity l) • _)
      (psiCoeff t (D.parity i * D.parity j) • _)) = _
  rw [psi_compC_three
    (triple_cl_mem ν μ i l j i j l h₁ h
      (crossL [up i] l j []) (D.parity j * D.parity l) (by simp [crossL, Shape.parity, mul_comm]))
    (triple_cl_mem ν μ l i j i l j h₂ h₁
      (crossL [] l i [up j]) (D.parity i * D.parity l) (by simp [crossL, Shape.parity, mul_comm]))
    (triple_cl_mem ν μ l j i l i j h₃ h₂
      (crossL [up l] j i []) (D.parity i * D.parity j) (by simp [crossL, Shape.parity, mul_comm]))
    t ht]
  rw [show D.parity j * D.parity l + (D.parity i * D.parity l + D.parity i * D.parity j) =
    D.parity i * D.parity j + (D.parity i * D.parity l + D.parity j * D.parity l) by ring]
  apply congrArg (psiCoeff t _ • ·)
  change cl D Sc μ [up l, up j, up i] [up l, up i, up j] (crossL [up l] j i []) ≫
    cl D Sc μ [up l, up i, up j] [up i, up l, up j] (crossL [] l i [up j]) ≫
      cl D Sc μ [up i, up l, up j] [up i, up j, up l] (crossL [up i] l j []) = _
  rw [← Category.assoc, cl_comp
    (show SChain [up l, up j, up i] (crossL [up l] j i []) [up l, up i, up j] from ⟨rfl, rfl⟩)
    (show SChain [up l, up i, up j] (crossL [] l i [up j]) [up i, up l, up j] from ⟨rfl, rfl⟩),
    cl_comp
    ((show SChain [up l, up j, up i] (crossL [up l] j i []) [up l, up i, up j] from ⟨rfl, rfl⟩).append
      (show SChain [up l, up i, up j] (crossL [] l i [up j]) [up i, up l, up j] from ⟨rfl, rfl⟩))
    (show SChain [up i, up l, up j] (crossL [up i] l j []) [up i, up j, up l] from ⟨rfl, rfl⟩)]

/-- The uncorrected upward braid relation (1.9). -/
theorem psi_braid (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j l : I)
    (h : wt D μ [up i, up j, up l] = ν) (hij : ¬(i = l ∧ i ≠ j)) :
    psiBraidLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j l h =
      psiBraidRight t ν μ i j l h := by
  apply SOp.hom_ext
  rw [psiBraidLeft_unsop t ht, psiBraidRight_unsop t ht]
  exact congrArg (psiCoeff t _ • ·) (cl_braid Sc l j i μ (fun ⟨h₁, h₂⟩ =>
    hij ⟨h₁.symm, fun h₃ => h₂ (h₁.trans h₃)⟩))

/-! ## The correction polynomial -/

/-- A dot at a specified position of a three-strand word. -/
private def psiDotOn₃ (t : k) (ν μ : X) (i j l : I)
    (h : wt D μ [up i, up j, up l] = ν) (a : List (Letter I)) (c : I) (b : List (Letter I)) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j, up l] h ⟶
      psiAt ν μ [up i, up j, up l] h :=
  SOp.mk' (psiCoeff t (D.parity c) •
    cl D Sc μ [up i, up j, up l] [up i, up j, up l] (dotsL a c b 1))

/-- The dot on the first strand. -/
abbrev psiDot₁ (t : k) (ν μ : X) (i j l : I) (h : wt D μ [up i, up j, up l] = ν) :=
  psiDotOn₃ (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j l h [] i [up j, up l]

/-- The dot on the middle strand. -/
abbrev psiDot₂ (t : k) (ν μ : X) (i j l : I) (h : wt D μ [up i, up j, up l] = ν) :=
  psiDotOn₃ (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j l h [up i] j [up l]

/-- The dot on the last strand. -/
abbrev psiDot₃ (t : k) (ν μ : X) (i j l : I) (h : wt D μ [up i, up j, up l] = ν) :=
  psiDotOn₃ (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j l h [up i, up j] l []

private theorem psiDotOn₃_power (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j l : I)
    (h : wt D μ [up i, up j, up l] = ν) (a : List (Letter I)) (c : I) (b : List (Letter I))
    (hs : [up i, up j, up l] = a ++ [up c] ++ b) (n : ℕ) :
    cpow (psiDotOn₃ (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j l h a c b) n =
      SOp.mk' (X := psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j, up l] h)
        (Y := psiAt ν μ [up i, up j, up l] h) (psiCoeff t (n * D.parity c) •
          cl D Sc μ [up i, up j, up l] [up i, up j, up l] (dotsL a c b n)) := by
  apply SOp.hom_ext
  refine (psi_cpow (triple_cl_mem ν μ i j l i j l h h (dotsL a c b 1)
    (D.parity c) (by simp)) ht n).trans ?_
  apply congrArg (psiCoeff t (n * D.parity c) • ·)
  induction n with
  | zero =>
    change 𝟙 ((pres D Sc).obj (ob D μ [up i, up j, up l])) = _
    exact (cl_nil μ [up i, up j, up l]).symm
  | succ n ih =>
    rw [cpow_succ, ih]
    change cl D Sc μ [up i, up j, up l] [up i, up j, up l] (dotsL a c b n) ≫
      cl D Sc μ [up i, up j, up l] [up i, up j, up l] (dotsL a c b 1) = _
    rw [cl_dotsL_eq_pow (Sc := Sc) μ a c b n hs,
      cl_dotsL_eq_pow (Sc := Sc) μ a c b (n + 1) hs]
    rfl

private theorem powers_swap {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {A : C} (x y : A ⟶ A) (c : k) (h : x ≫ y = c • (y ≫ x)) (r s : ℕ) :
    cpow x r ≫ cpow y s = (c ^ r) ^ s • (cpow y s ≫ cpow x r) := by
  have hx : cpow x r ≫ y = c ^ r • (y ≫ cpow x r) := by
    simpa using iter_slide x x y 0 c (by simpa using h) r
  simpa using iter_slide' y y (cpow x r) 0 (c ^ r) (by simpa using hx) s

private theorem dots_powers_swap (μ : X) (a m b : List (Letter I)) (i j : I) (r s : ℕ) :
    cl D Sc μ (a ++ [up i] ++ m ++ [up j] ++ b) (a ++ [up i] ++ m ++ [up j] ++ b)
        (dotsL a i (m ++ [up j] ++ b) r) ≫
      cl D Sc μ (a ++ [up i] ++ m ++ [up j] ++ b) (a ++ [up i] ++ m ++ [up j] ++ b)
        (dotsL (a ++ [up i] ++ m) j b s) =
      zsign k ((r : ZMod 2) * D.parity i * (s * D.parity j)) •
        (cl D Sc μ (a ++ [up i] ++ m ++ [up j] ++ b) (a ++ [up i] ++ m ++ [up j] ++ b)
          (dotsL (a ++ [up i] ++ m) j b s) ≫
        cl D Sc μ (a ++ [up i] ++ m ++ [up j] ++ b) (a ++ [up i] ++ m ++ [up j] ++ b)
          (dotsL a i (m ++ [up j] ++ b) r)) := by
  have h : a ++ [up i] ++ m ++ [up j] ++ b = a ++ [up i] ++ (m ++ [up j] ++ b) := by
    simp only [List.append_assoc]
  have h' : a ++ [up i] ++ m ++ [up j] ++ b = (a ++ [up i] ++ m) ++ [up j] ++ b := rfl
  rw [cl_dotsL_eq_pow μ a i _ r h, cl_dotsL_eq_pow μ _ j b s h']
  have H := powers_swap (cl D Sc μ (a ++ [up i] ++ m ++ [up j] ++ b) _
    (dotsL a i (m ++ [up j] ++ b) 1))
    (cl D Sc μ (a ++ [up i] ++ m ++ [up j] ++ b) _ (dotsL (a ++ [up i] ++ m) j b 1))
    (zsign k (D.parity i * D.parity j)) ?_ r s
  · rw [← zsign_natCast_mul, ← zsign_natCast_mul] at H
    convert H using 2
    congr 1
    ring
  · have hi : SChain (a ++ [up i] ++ m ++ [up j] ++ b)
        (dotsL a i (m ++ [up j] ++ b) 1) (a ++ [up i] ++ m ++ [up j] ++ b) := by
      simpa only [List.append_assoc] using sChain_dotsL a i (m ++ [up j] ++ b) 1
    have hj := sChain_dotsL (a ++ [up i] ++ m) j b 1
    rw [cl_comp hi hj, cl_comp hj hi]
    simpa only [dotsL, List.replicate_one, List.singleton_append, Shape.parity, Shape.dom,
      Shape.cod] using
      cl_swap (D := D) (Sc := Sc) μ (a ++ [up i] ++ m ++ [up j] ++ b)
        (a ++ [up i] ++ m ++ [up j] ++ b) a m b (.dot i) (.dot j)

/-- The three-strand dot is the indicated whiskering of the two-strand dot. -/
theorem psiDot₁_whisker (t : k) (μ : X) (i j l : I) :
    BicategoryStruct.whiskerRight (B := TwoSOp k (Uqπ D Sc sy hc))
      (psiDotLeft t (wt D μ [up i, up j, up l]) (wt D μ [up l]) i j rfl) (psiE μ l) =
      psiDot₁ (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up i, up j, up l]) μ i j l rfl := by
  apply SOp.hom_ext
  rw [TwoSOp.unsop_whiskerRight]
  apply Envelope.hom_ext
  rw [TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl]
  change (pres D Sc).wRAt _
    (psiCoeff t (D.parity i) • cl D Sc (wt D μ [up l]) [up i, up j] [up i, up j]
      (dotsL [] i [up j] 1)) (ob D μ [up l]) rfl rfl = _
  rw [Presentation.wRAt_smul]
  apply congrArg (psiCoeff t (D.parity i) • ·)
  refine (congrArg (fun f => (pres D Sc).wRAt _ f (ob D μ [up l]) rfl rfl)
    (cl_of (D := D) (Sc := Sc) (μ := (wt D μ [up l])) (sChain_dotsL [] i [up j] 1))).trans ?_
  refine (Presentation.wRAt_diag _ _ _ (Presentation.Bicat.Hom.composable
    (psiWord (Sc := Sc) (wt D μ [up l]) [up i, up j]) (psiWord μ [up l])) _ _).trans ?_
  exact (Presentation.diag_eq_of_layers_eq _ (show _ = _ from rfl)).trans
    (cl_of (D := D) (Sc := Sc) (μ := μ) (sChain_dotsL [] i [up j, up l] 1)).symm

/-- The three-strand dot is the indicated whiskering of the two-strand dot. -/
theorem psiDot₂_whisker (t : k) (μ : X) (i j l : I) :
    BicategoryStruct.whiskerLeft (B := TwoSOp k (Uqπ D Sc sy hc))
      (psiE (wt D μ [up j, up l]) i) (psiDotLeft t (wt D μ [up j, up l]) μ j l rfl) =
      psiDot₂ (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up i, up j, up l]) μ i j l rfl := by
  apply SOp.hom_ext
  rw [TwoSOp.unsop_whiskerLeft]
  apply Envelope.hom_ext
  rw [TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl]
  change (pres D Sc).wL (ob D (wt D μ [up j, up l]) [up i])
    (psiCoeff t (D.parity j) • cl D Sc μ [up j, up l] [up j, up l] (dotsL [] j [up l] 1)) = _
  rw [Presentation.wL_smul]
  apply congrArg (psiCoeff t (D.parity j) • ·)
  refine (congrArg ((pres D Sc).wL (ob D (wt D μ [up j, up l]) [up i]))
    (cl_of (D := D) (Sc := Sc) (μ := μ) (sChain_dotsL [] j [up l] 1))).trans ?_
  refine (Presentation.wL_diag_of_composable _ _ _ (Presentation.Bicat.Hom.composable
    (psiWord (Sc := Sc) (wt D μ [up j, up l]) [up i]) (psiWord μ [up j, up l]))).trans ?_
  exact (Presentation.diag_eq_of_layers_eq _ (show _ = _ from rfl)).trans
    (cl_of (D := D) (Sc := Sc) (μ := μ) (sChain_dotsL [up i] j [up l] 1)).symm

/-- The three-strand dot is the indicated whiskering of the two-strand dot. -/
theorem psiDot₃_whisker (t : k) (μ : X) (i j l : I) :
    BicategoryStruct.whiskerLeft (B := TwoSOp k (Uqπ D Sc sy hc))
      (psiE (wt D μ [up j, up l]) i) (psiDotRight t (wt D μ [up j, up l]) μ j l rfl) =
      psiDot₃ (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up i, up j, up l]) μ i j l rfl := by
  apply SOp.hom_ext
  rw [TwoSOp.unsop_whiskerLeft]
  apply Envelope.hom_ext
  rw [TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl]
  change (pres D Sc).wL (ob D (wt D μ [up j, up l]) [up i])
    (psiCoeff t (D.parity l) • cl D Sc μ [up j, up l] [up j, up l] (dotsL [up j] l [] 1)) = _
  rw [Presentation.wL_smul]
  apply congrArg (psiCoeff t (D.parity l) • ·)
  refine (congrArg ((pres D Sc).wL (ob D (wt D μ [up j, up l]) [up i]))
    (cl_of (D := D) (Sc := Sc) (μ := μ) (sChain_dotsL [up j] l [] 1))).trans ?_
  refine (Presentation.wL_diag_of_composable _ _ _ (Presentation.Bicat.Hom.composable
    (psiWord (Sc := Sc) (wt D μ [up j, up l]) [up i]) (psiWord μ [up j, up l]))).trans ?_
  exact (Presentation.diag_eq_of_layers_eq _ (show _ = _ from rfl)).trans
    (cl_of (D := D) (Sc := Sc) (μ := μ) (sChain_dotsL [up i, up j] l [] 1)).symm

/-- The horizontal monomial: rightmost dots first, then middle, then leftmost. -/
def psiBraidMonomial (t : k) (ν μ : X) (i j : I)
    (h : wt D μ [up i, up j, up i] = ν) (r q s : ℕ) :=
  cpow (psiDot₃ (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j i h) s ≫
    cpow (psiDot₂ t ν μ i j i h) q ≫ cpow (psiDot₁ t ν μ i j i h) r

private theorem psiBraidMonomial_unsop (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (h : wt D μ [up i, up j, up i] = ν) (r q s : ℕ)
    (hq : (q : ZMod 2) * D.parity j = 0)
    (hn : ((r : ZMod 2) + s + 1) * D.parity i = 0) :
    SOp.unsop (psiBraidMonomial (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h r q s) =
      psiCoeff t (D.parity i) • cl D Sc μ [up i, up j, up i] [up i, up j, up i]
        (dotsL [up i, up j] i [] s ++ dotsL [up i] j [up i] q ++ dotsL [] i [up j, up i] r) := by
  have hp : (s : ZMod 2) * D.parity i + ((q : ZMod 2) * D.parity j + r * D.parity i) = D.parity i := by
    rw [hq, zero_add]
    generalize D.parity i = a at hn ⊢
    generalize (r : ZMod 2) = x at hn ⊢
    generalize (s : ZMod 2) = y at hn ⊢
    revert a x y
    decide
  have hrs : (r : ZMod 2) * D.parity i * (s * D.parity i) = 0 := by
    generalize D.parity i = a at hn ⊢
    generalize (r : ZMod 2) = x at hn ⊢
    generalize (s : ZMod 2) = y at hn ⊢
    revert a x y
    decide
  unfold psiBraidMonomial
  rw [psiDotOn₃_power t ht ν μ i j i h [up i, up j] i [] rfl s,
    psiDotOn₃_power t ht ν μ i j i h [up i] j [up i] rfl q,
    psiDotOn₃_power t ht ν μ i j i h [] i [up j, up i] rfl r]
  change SOp.compC (R := k) (psiCoeff t (s * D.parity i) • _)
    (SOp.compC (R := k) (psiCoeff t (q * D.parity j) • _) (psiCoeff t (r * D.parity i) • _)) = _
  rw [psi_compC_three
    (triple_cl_mem ν μ i j i i j i h h (dotsL [up i, up j] i [] s) _ (by simp))
    (triple_cl_mem ν μ i j i i j i h h (dotsL [up i] j [up i] q) _ (by simp))
    (triple_cl_mem ν μ i j i i j i h h (dotsL [] i [up j, up i] r) _ (by simp)) t ht, hp]
  apply congrArg (psiCoeff t (D.parity i) • ·)
  change cl D Sc μ [up i, up j, up i] [up i, up j, up i] (dotsL [] i [up j, up i] r) ≫
    cl D Sc μ [up i, up j, up i] [up i, up j, up i] (dotsL [up i] j [up i] q) ≫
      cl D Sc μ [up i, up j, up i] [up i, up j, up i] (dotsL [up i, up j] i [] s) = _
  have hLM := dots_powers_swap (Sc := Sc) μ [] [] [up i] i j r q
  have hLR := dots_powers_swap (Sc := Sc) μ [] [up j] [] i i r s
  have hMR := dots_powers_swap (Sc := Sc) μ [up i] [] [] j i q s
  simp only [hq, mul_zero, zero_mul, hrs, zsign_zero, one_smul, List.nil_append,
    List.append_nil, List.cons_append] at hLM hLR hMR
  rw [← Category.assoc, hLM, Category.assoc, hLR, ← Category.assoc, hMR]
  exact (congrArg (· ≫ cl D Sc μ [up i, up j, up i] [up i, up j, up i]
      (dotsL [] i [up j, up i] r))
    (cl_comp (D := D) (Sc := Sc) (μ := μ) (sChain_dotsL [up i, up j] i [] s)
      (sChain_dotsL [up i] j [up i] q))).trans
    (cl_comp ((sChain_dotsL [up i, up j] i [] s).append (sChain_dotsL [up i] j [up i] q))
      (sChain_dotsL [] i [up j, up i] r))

/-- The correction in (1.9), evaluated in the assigned dots. -/
def psiBraidCorrection (t : k) (ν μ : X) (i j : I)
    (h : wt D μ [up i, up j, up i] = ν) :=
  (∑ s ∈ Finset.range (D.dn i j),
    (zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
      psiBraidMonomial (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h (D.dn i j - 1 - s) 0 s) +
  ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), ∑ s ∈ Finset.range p,
    (zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
      psiBraidMonomial (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h (p - 1 - s) q s

/-- The corrected upward braid relation (1.9), with no additional scalar hypotheses. -/
theorem psi_braidEq (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (h : wt D μ [up i, up j, up i] = ν) (hij : i ≠ j) :
    psiBraidLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j i h =
      psiBraidRight t ν μ i j i h + psiBraidCorrection t ν μ i j h := by
  let A := psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [up i, up j, up i] h
  let L : ((pres D Sc).obj (ob D μ [up i, up j, up i]) ⟶ (pres D Sc).obj (ob D μ [up i, up j, up i])) →ₗ[k]
      (A ⟶ A) :=
    { toFun := fun f => SOp.mk' (psiCoeff t (D.parity i) • f)
      map_add' := fun _ _ => SOp.hom_ext (smul_add _ _ _)
      map_smul' := fun _ _ => SOp.hom_ext (smul_comm _ _ _) }
  have hn (n s : ℕ) (hs : s < n) (hp : (n : ZMod 2) * D.parity i = 0) :
      (((n - 1 - s : ℕ) : ZMod 2) + s + 1) * D.parity i = 0 := by
    rw [← Nat.cast_add, ← Nat.cast_add_one, show n - 1 - s + s + 1 = n by omega]
    exact hp
  have H := lin_relation Sc (.braidEq i j μ hij)
  skm_rel_simp H
  have H' := congrArg L H
  simp only [map_sub, map_smul, map_sum, map_zero] at H'
  have hL : L (cl D Sc μ [up i, up j, up i] [up i, up j, up i]
      (crossL [] i j [up i] ++ crossL [up j] i i [] ++ crossL [] j i [up i])) =
      psiBraidLeft t ν μ i j i h := by
    apply SOp.hom_ext
    rw [psiBraidLeft_unsop t ht]
    change psiCoeff t (D.parity i) • _ = psiCoeff t _ • _
    congr 2
    generalize D.parity i = a; generalize D.parity j = b
    revert a b
    decide
  have hR : L (cl D Sc μ [up i, up j, up i] [up i, up j, up i]
      (crossL [up i] j i [] ++ crossL [] i i [up j] ++ crossL [up i] i j [])) =
      psiBraidRight t ν μ i j i h := by
    apply SOp.hom_ext
    rw [psiBraidRight_unsop t ht]
    change psiCoeff t (D.parity i) • _ = psiCoeff t _ • _
    congr 2
    generalize D.parity i = a; generalize D.parity j = b
    revert a b
    decide
  rw [hL, hR] at H'
  have hOuter : ∀ s ∈ Finset.range (D.dn i j),
      L (cl D Sc μ [up i, up j, up i] [up i, up j, up i]
        (dotsL [up i, up j] i [] s ++ dotsL [] i [up j, up i] (D.dn i j - 1 - s))) =
        psiBraidMonomial t ν μ i j h (D.dn i j - 1 - s) 0 s := by
    intro s hs
    apply SOp.hom_ext
    change psiCoeff t (D.parity i) • _ = _
    simpa only [dotsL, List.replicate_zero, List.append_nil, List.nil_append] using
      (psiBraidMonomial_unsop t ht ν μ i j h (D.dn i j - 1 - s) 0 s (by simp)
        (hn _ _ (Finset.mem_range.mp hs) (by simpa [mul_comm] using parity_mul_dn D i j))).symm
  have hPoly : ∀ p ∈ Finset.Ioo 0 (D.dn i j), ∀ q ∈ Finset.Ioo 0 (D.dn j i), ∀ s ∈ Finset.range p,
      (zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
        L (cl D Sc μ [up i, up j, up i] [up i, up j, up i]
          (dotsL [up i, up j] i [] s ++ dotsL [up i] j [up i] q ++ dotsL [] i [up j, up i] (p - 1 - s))) =
      (zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
        psiBraidMonomial t ν μ i j h (p - 1 - s) q s := by
    intro p _ q _ s hs
    by_cases hz : Sc.s i j p q = 0
    · simp [hz]
    · obtain ⟨hp, hq⟩ := Sc.parity_of_ne_zero hz
      apply congrArg (_ • ·)
      apply SOp.hom_ext
      exact (psiBraidMonomial_unsop t ht ν μ i j h (p - 1 - s) q s hq
        (hn _ _ (Finset.mem_range.mp hs) hp)).symm
  have hO := Finset.sum_congr rfl (fun (s : ℕ) hs => congrArg
    ((zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) • ·) (hOuter s hs))
  rw [hO] at H'
  have hP := Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq =>
    Finset.sum_congr rfl (fun s hs => hPoly p hp q hq s hs)))
  rw [hP] at H'
  unfold psiBraidCorrection
  rw [← sub_eq_zero]
  convert H' using 1
  abel

end OddMath.SKM
