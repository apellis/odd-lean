/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Presentation
import StringDiagrams.LayerMap.Generators

/-!
# The relabelling underlying the Chevalley involution

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 3.5: the
Chevalley involution `ω` sends the object `λ` to `-λ`, `Eᵢ 1_λ` to `Fᵢ 1_{-λ}` and `Fᵢ 1_λ` to
`Eᵢ 1_{-λ}`. On normal-form words this is the relabelling `flipW` (each signed letter changes
sign) with all regions negated (`chevColour`, `chevMap`).
-/

noncomputable section

namespace OddMath.SKM

open StringDiagrams

universe u v

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)

/-- The signed letter with the opposite orientation. -/
def flipL (l : Letter I) : Letter I := (!l.1, l.2)

/-- A signed sequence with all orientations reversed. -/
def flipW (t : List (Letter I)) : List (Letter I) := t.map flipL

@[simp] theorem flipW_nil : flipW ([] : List (Letter I)) = [] := rfl
@[simp] theorem flipW_cons (l : Letter I) (t : List (Letter I)) :
    flipW (l :: t) = flipL l :: flipW t := rfl
@[simp] theorem flipW_append (s t : List (Letter I)) : flipW (s ++ t) = flipW s ++ flipW t := by
  simp [flipW]
@[simp] theorem flipL_flipL (l : Letter I) : flipL (flipL l) = l := by
  obtain ⟨b, i⟩ := l; simp [flipL]
@[simp] theorem flipW_flipW (t : List (Letter I)) : flipW (flipW t) = t := by
  induction t <;> simp_all
@[simp] theorem flipL_up (i : I) : flipL (up i) = dn i := rfl
@[simp] theorem flipL_dn (i : I) : flipL (dn i) = up i := rfl

theorem sh_flipL (l : Letter I) : sh D (flipL l) = -sh D l := by
  obtain ⟨b, i⟩ := l; cases b <;> simp [sh, flipL]

theorem wt_flipW (μ : X) (t : List (Letter I)) : wt D (-μ) (flipW t) = -wt D μ t := by
  induction t with
  | nil => rfl
  | cons l t ih => simp [ih, sh_flipL]; abel

/-- The colour map of `ω`: the opposite orientation, the negated region. -/
def chevColour (c : Col I X) : Col I X := ⟨flipL c.l, -c.r⟩

theorem wd_flipW (μ : X) (t : List (Letter I)) :
    (wd D μ t).map chevColour = wd D (-μ) (flipW t) := by
  induction t with
  | nil => rfl
  | cons l t ih => simp [ih, chevColour, wt_flipW]

/-- The relabelling of regions and strands underlying the Chevalley involution: `λ ↦ -λ`,
`Eᵢ ↔ Fᵢ`. -/
def chevMap : ColourMap (sig D) (sig D) where
  region μ := (-(show X from μ) : X)
  colour := chevColour
  colourSrc c := by
    show sh D (flipL c.l) + -c.r = -(sh D c.l + c.r)
    rw [sh_flipL]; abel
  colourTgt _ := rfl

theorem chevMap_obj (μ : X) (t : List (Letter I)) :
    (chevMap D).obj (ob D μ t) = ob D (-μ) (flipW t) := by
  refine Obj.ext ?_ ?_
  · show -wt D μ t = wt D (-μ) (flipW t)
    rw [wt_flipW]
  · show (chevMap D).word (wd D μ t) = wd D (-μ) (flipW t)
    rw [(chevMap D).word_eq]
    exact wd_flipW D μ t

end OddMath.SKM
