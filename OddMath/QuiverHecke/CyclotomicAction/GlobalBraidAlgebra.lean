/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalSlideAlgebra
import OddMath.QuiverHecke.CyclotomicAction.Square
import OddMath.QuiverHecke.MixedRelations

/-!
# The equal-colour braid on the last three strands at every height

The algebra half of the same-colour braid relation of
`Categorification/KLR/CyclotomicAction/GlobalBraid.lean` (`globalCross_sameBraid`). On three
strands of colour `i` appended to an old word, with `c₁ = φ(c)` the appended crossing of the
first two new strands and `c₂` the last-pair crossing,

  `c₁ c₂ c₁ = c₂ c₁ c₂`

on each word (`induction_braid_same`, from the positional braid `braid_ne`), in the affine
algebra (`affineLastCrossing_braid_same`) and at every height of the extended tower
(`heightLastCrossing_braid_same`). No sign appears: for the Rouquier crossings `t = -ψ` both
sides change by `(-1)^3`.
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory

namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- The positional braid with the endpoints given up to equality. -/
theorem braid_ne_of_eq {t t' : List I} (l r : List I) (i j m : I) (hb : ¬(i = m ∧ i ≠ j))
    (ht : t = l ++ [i, j, m] ++ r) (ht' : t' = l ++ [m, j, i] ++ r) {L₁ L₂ : List PG}
    (e₁ : L₁ = [.cross (l.length + 1), .cross l.length, .cross (l.length + 1)])
    (e₂ : L₂ = [.cross l.length, .cross (l.length + 1), .cross l.length])
    (h₁ : SChain t (pl t L₁) t') (h₂ : SChain t (pl t L₂) t') :
    cl D Sc t t' L₁ h₁ = cl D Sc t t' L₂ h₂ := by
  subst ht ht' e₁ e₂
  exact (braid_ne D Sc l r i j m hb _ _).symm

/-- The appended last-pair crossing as a positioned word on the appended words. -/
theorem appendHom_inductionLastCrossing_eq_cl (i j c : I) {n : ℕ} (w : Word I n) :
    appendHom D Sc c _ _ (inductionLastCrossing D Sc i j w) =
      cl D Sc (appendWord c (appendWord j (appendWord i w))).1
        (appendWord c (appendWord i (appendWord j w))).1 [.cross w.1.length] (by
          simp [appendWord, pl, PG.ld, Shape.dom, Shape.cod, List.append_assoc]) := by
  have hfits : Fits (appendWord j (appendWord i w)).1.length [PG.cross w.1.length] := by
    intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    simp [PG.pos, PG.width, appendWord]
  change inductionLastCrossing D Sc i j w ▷ (pres D Sc).obj (ob D [c]) = _
  rw [inductionLastCrossing_eq_cl D Sc i j w, cl_whiskerRight D Sc _ _ [c] hfits]
  rfl

/-- **The equal-colour braid on each word**: `φ(c) c₂ φ(c) = c₂ φ(c) c₂` in diagrammatic
order, for the last three strands of colour `i`. -/
theorem induction_braid_same (i : I) {n : ℕ} (w : Word I n) :
    appendHom D Sc i _ _ (inductionLastCrossing D Sc i i w) ≫
        inductionLastCrossing D Sc i i (appendWord i w) ≫
          appendHom D Sc i _ _ (inductionLastCrossing D Sc i i w) =
      inductionLastCrossing D Sc i i (appendWord i w) ≫
        appendHom D Sc i _ _ (inductionLastCrossing D Sc i i w) ≫
          inductionLastCrossing D Sc i i (appendWord i w) := by
  rw [appendHom_inductionLastCrossing_eq_cl, inductionLastCrossing_eq_cl D Sc i i (appendWord i w),
    cl_comp, cl_comp, cl_comp, cl_comp]
  exact (braid_ne_of_eq D Sc w.1 [] i i i (by simp)
    (by simp [appendWord]) (by simp [appendWord]) (by simp [appendWord])
    (by simp [appendWord]) _ _).symm

section Affine
variable [Fintype I]

omit [Fintype I] in
theorem appendWord₃_injective (i : I) (n : ℕ) :
    Function.Injective fun w : Word I n => appendWord i (appendWord i (appendWord i w)) :=
  fun _ _ h => appendWord_injective i n (appendWord_injective i (n + 1)
    (appendWord_injective i (n + 1 + 1) h))

theorem append_affineLastCrossing_eq_sum (i : I) (n : ℕ) :
    appendAlgebra D Sc i (n + 1 + 1) (affineLastCrossing D Sc i i n) =
      ∑ w : Word I n, FiniteHomMatrix.single (appendWord i (appendWord i (appendWord i w)))
        (appendWord i (appendWord i (appendWord i w)))
        (appendHom D Sc i _ _ (inductionLastCrossing D Sc i i w)) := by
  change appendLinear D Sc i (n + 1 + 1) (affineLastCrossing D Sc i i n) = _
  rw [affineLastCrossing, map_sum]
  exact Finset.sum_congr rfl fun w _ => appendLinear_single D Sc i _ _ _

/-- Left multiplication by the appended crossing on a three-fold appended entry. -/
theorem append_affineLastCrossing_mul_single (i : I) {n : ℕ} (s t : Word I n)
    (g : wordObj D Sc (appendWord i (appendWord i (appendWord i s))) ⟶
      wordObj D Sc (appendWord i (appendWord i (appendWord i t)))) :
    appendAlgebra D Sc i (n + 1 + 1) (affineLastCrossing D Sc i i n) *
        FiniteHomMatrix.single (appendWord i (appendWord i (appendWord i t)))
          (appendWord i (appendWord i (appendWord i s))) g =
      FiniteHomMatrix.single (appendWord i (appendWord i (appendWord i t)))
        (appendWord i (appendWord i (appendWord i s)))
        (g ≫ appendHom D Sc i _ _ (inductionLastCrossing D Sc i i t)) := by
  rw [append_affineLastCrossing_eq_sum, Finset.sum_mul, Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord₃_injective i n h)) _ _
  · simp

/-- The last-pair crossing on a three-fold appended entry, from the left. -/
theorem affineLastCrossing_succ_mul_single (i : I) {n : ℕ} (s t : Word I n)
    (g : wordObj D Sc (appendWord i (appendWord i (appendWord i s))) ⟶
      wordObj D Sc (appendWord i (appendWord i (appendWord i t)))) :
    affineLastCrossing D Sc i i (n + 1) *
        FiniteHomMatrix.single (appendWord i (appendWord i (appendWord i t)))
          (appendWord i (appendWord i (appendWord i s))) g =
      FiniteHomMatrix.single (appendWord i (appendWord i (appendWord i t)))
        (appendWord i (appendWord i (appendWord i s)))
        (g ≫ inductionLastCrossing D Sc i i (appendWord i t)) := by
  rw [affineLastCrossing, Finset.sum_mul, Finset.sum_eq_single (appendWord i t)]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective i (n + 1) (appendWord_injective i (n + 1 + 1) h))) _ _
  · simp

/-- The last-pair crossing on a three-fold appended entry, from the right. -/
theorem single_mul_affineLastCrossing_succ (i : I) {n : ℕ} (s t : Word I n)
    (g : wordObj D Sc (appendWord i (appendWord i (appendWord i s))) ⟶
      wordObj D Sc (appendWord i (appendWord i (appendWord i t)))) :
    FiniteHomMatrix.single (appendWord i (appendWord i (appendWord i t)))
        (appendWord i (appendWord i (appendWord i s))) g *
      affineLastCrossing D Sc i i (n + 1) =
      FiniteHomMatrix.single (appendWord i (appendWord i (appendWord i t)))
        (appendWord i (appendWord i (appendWord i s)))
        (inductionLastCrossing D Sc i i (appendWord i s) ≫ g) := by
  rw [affineLastCrossing, Finset.mul_sum, Finset.sum_eq_single (appendWord i s)]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective i (n + 1)
        (appendWord_injective i (n + 1 + 1) h.symm))) _ _
  · simp

/-- **The equal-colour braid in the affine algebra**: `c₁ c₂ c₁ = c₂ c₁ c₂`. -/
theorem affineLastCrossing_braid_same (i : I) (n : ℕ) :
    appendAlgebra D Sc i (n + 1 + 1) (affineLastCrossing D Sc i i n) *
        (affineLastCrossing D Sc i i (n + 1) *
          appendAlgebra D Sc i (n + 1 + 1) (affineLastCrossing D Sc i i n)) =
      affineLastCrossing D Sc i i (n + 1) *
        (appendAlgebra D Sc i (n + 1 + 1) (affineLastCrossing D Sc i i n) *
          affineLastCrossing D Sc i i (n + 1)) := by
  have hA : affineLastCrossing D Sc i i (n + 1) *
      appendAlgebra D Sc i (n + 1 + 1) (affineLastCrossing D Sc i i n) =
      ∑ w : Word I n, FiniteHomMatrix.single (appendWord i (appendWord i (appendWord i w)))
        (appendWord i (appendWord i (appendWord i w)))
        (appendHom D Sc i _ _ (inductionLastCrossing D Sc i i w) ≫
          inductionLastCrossing D Sc i i (appendWord i w)) := by
    rw [append_affineLastCrossing_eq_sum, Finset.mul_sum]
    simp only [affineLastCrossing_succ_mul_single]
  have hB : appendAlgebra D Sc i (n + 1 + 1) (affineLastCrossing D Sc i i n) *
      affineLastCrossing D Sc i i (n + 1) =
      ∑ w : Word I n, FiniteHomMatrix.single (appendWord i (appendWord i (appendWord i w)))
        (appendWord i (appendWord i (appendWord i w)))
        (inductionLastCrossing D Sc i i (appendWord i w) ≫
          appendHom D Sc i _ _ (inductionLastCrossing D Sc i i w)) := by
    rw [append_affineLastCrossing_eq_sum, Finset.sum_mul]
    simp only [single_mul_affineLastCrossing_succ]
  rw [hA, hB, Finset.mul_sum, Finset.mul_sum]
  simp only [append_affineLastCrossing_mul_single, affineLastCrossing_succ_mul_single,
    Category.assoc, induction_braid_same]

end Affine

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke.CyclotomicAction
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I] (a : I → _root_.Polynomial k) (i : I)

/-- **The equal-colour braid at every height**: with `c₁` the appended crossing and `c₂` the
last-pair crossing in `heightAlgebra (n+3)`, `c₁ c₂ c₁ = c₂ c₁ c₂`. -/
theorem heightLastCrossing_braid_same (n : ℕ) :
    heightAppend D Sc a i (n + 1 + 1) (heightLastCrossing D Sc a i i n) *
        (heightLastCrossing D Sc a i i (n + 1) *
          heightAppend D Sc a i (n + 1 + 1) (heightLastCrossing D Sc a i i n)) =
      heightLastCrossing D Sc a i i (n + 1) *
        (heightAppend D Sc a i (n + 1 + 1) (heightLastCrossing D Sc a i i n) *
          heightLastCrossing D Sc a i i (n + 1)) := by
  have hc : heightLastCrossing D Sc a i i (n + 1) =
      cyclotomicMk D Sc a (n + 1 + 1) (affineLastCrossing D Sc i i (n + 1)) := rfl
  have h₁ : heightAppend D Sc a i (n + 1 + 1) (heightLastCrossing D Sc a i i n) =
      cyclotomicMk D Sc a (n + 1 + 1)
        (appendAlgebra D Sc i (n + 1 + 1) (affineLastCrossing D Sc i i n)) := by
    cases n <;> rfl
  have key := congrArg (cyclotomicMk D Sc a (n + 1 + 1)) (affineLastCrossing_braid_same D Sc i n)
  simp only [map_mul] at key
  rw [hc, h₁]
  exact key

end OddMath.QuiverHecke.CyclotomicAction
