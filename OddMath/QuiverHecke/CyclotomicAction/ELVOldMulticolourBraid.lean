/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOldDistinctSlides
import OddMath.QuiverHecke.CyclotomicAction.BraidCorrection

/-! # Multicolour braids in the untruncated OLD coefficient category

Brundan–Ellis (1.9): retain the independently appended positive crossings,
including the repeated-outer-colour dot correction with all interior scalar
parameters. These coefficient relations precede balanced induction and its
superopposite signs. No source braid or truncation premise is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The independently chosen first-pair crossing, appended by the third colour. -/
abbrev triplePrefix (i j l : I) (s : OldCategory D Sc cutoff) :
    (⟨s.word ++ [i] ++ [j] ++ [l]⟩ : OldCategory D Sc cutoff) ⟶
      (⟨s.word ++ [j] ++ [i] ++ [l]⟩ : OldCategory D Sc cutoff) :=
  (append D Sc cutoff l).map (crossComponent D Sc cutoff j i s)

/-- The independently chosen last-pair crossing after the first append. -/
abbrev tripleSuffix (i j l : I) (s : OldCategory D Sc cutoff) :
    (⟨s.word ++ [i] ++ [j] ++ [l]⟩ : OldCategory D Sc cutoff) ⟶
      (⟨s.word ++ [i] ++ [l] ++ [j]⟩ : OldCategory D Sc cutoff) :=
  crossComponent D Sc cutoff l j ((append D Sc cutoff i).obj s)

private theorem triplePrefix_affine (i j l : I) (s : OldCategory D Sc cutoff) :
    triplePrefix D Sc cutoff i j l s =
      (ideal D Sc cutoff (s.word ++ [i] ++ [j] ++ [l])
        (s.word ++ [j] ++ [i] ++ [l])).mkQ
      (affineUnit D Sc cutoff (s.word ++ [i] ++ [j] ++ [l])
        (s.word ++ [j] ++ [i] ++ [l])
        (crossLast D Sc s.word i j ▷ (pres D Sc).obj (ob D [l]))) := by
  change (ideal D Sc cutoff _ _).mkQ
    (rightContext D Sc cutoff [l] _ _ (affineUnit D Sc cutoff _ _
      (crossLast D Sc s.word i j))) = _
  rw [rightContext_affineUnit]
  rfl

private theorem affineMulticolour_braid (v : List I) (i j l : I)
    (hb : ¬ (i = l ∧ i ≠ j)) :
    (crossLast D Sc v i j ▷ (pres D Sc).obj (ob D [l])) ≫
        crossLast D Sc (v ++ [j]) i l ≫
          (crossLast D Sc v j l ▷ (pres D Sc).obj (ob D [i])) =
      crossLast D Sc (v ++ [i]) j l ≫
        (crossLast D Sc v i l ▷ (pres D Sc).obj (ob D [j])) ≫
          crossLast D Sc (v ++ [l]) i j := by
  rw [crossLast_whiskerRight_cl, crossLast_whiskerRight_cl,
    crossLast_whiskerRight_cl, crossLast, crossLast, crossLast,
    cl_comp_three, cl_comp_three]
  refine (braid_ne_gen D Sc v [] i j l hb ?_ ?_ ?_ ?_ _ _).symm <;>
    simp [List.append_assoc]

/-- The literal independently whiskered OLD crossings satisfy the uncorrected braid. -/
theorem tripleCross_braid (i j l : I) (hb : ¬ (i = l ∧ i ≠ j))
    (s : OldCategory D Sc cutoff) :
    triplePrefix D Sc cutoff i j l s ≫ tripleSuffix D Sc cutoff j i l s ≫
        triplePrefix D Sc cutoff j l i s =
      tripleSuffix D Sc cutoff i j l s ≫ triplePrefix D Sc cutoff i l j s ≫
        tripleSuffix D Sc cutoff l i j s := by
  rw [triplePrefix_affine, triplePrefix_affine, triplePrefix_affine]
  dsimp only [tripleSuffix, crossComponent, append, Functor.comp_obj]
  change oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      (oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
        ((ideal D Sc cutoff _ _).mkQ _)) =
    oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      (oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
        ((ideal D Sc cutoff _ _).mkQ _))
  rw [oldComp_mk, oldComp_mk, oldComp_mk, oldComp_mk,
    ← affineUnit_comp, ← affineUnit_comp, ← affineUnit_comp, ← affineUnit_comp]
  exact congrArg (fun f => (ideal D Sc cutoff _ _).mkQ
    (affineUnit D Sc cutoff _ _ f)) (affineMulticolour_braid D Sc s.word i j l hb)

/-- The affine coefficient correction on the three appended positions. -/
def positionalCorrection (t : List I) (n : ℕ) (i j : I) :
    End ((pres D Sc).obj (ob D t)) :=
  ∑ r ∈ Finset.range (D.dn i j),
      (SKM.zsign k (D.parity i * (D.parity j + r)) * (Sc.t i j : k)) •
        (dotE D Sc t n ^ (D.dn i j - 1 - r) *
          dotE D Sc t (n + 2) ^ r) +
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        ∑ r ∈ Finset.range p,
          (SKM.zsign k (D.parity i * (D.parity j + r)) * Sc.s i j p q) •
            (dotE D Sc t n ^ (p - 1 - r) *
              dotE D Sc t (n + 1) ^ q *
              dotE D Sc t (n + 2) ^ r)

private theorem positionalCorrection_braid (v : List I) (i j : I) (hij : i ≠ j) {t : List I} (ht : t = v ++ [i,j,i] ++ [])
      (h₁ : SChain t (pl t [.cross v.length, .cross (v.length + 1),
        .cross v.length]) t)
      (h₂ : SChain t (pl t [.cross (v.length + 1), .cross v.length,
        .cross (v.length + 1)]) t) :
      cl D Sc t t _ h₁ - cl D Sc t t _ h₂ =
      positionalCorrection D Sc t v.length i j := by
  subst t
  exact braid_iji D Sc v [] hij h₁ h₂

/-- The correction on the three appended positions. -/
abbrev coefficientCorrection (v : List I) (i j : I) :=
  positionalCorrection D Sc (v ++ [i] ++ [j] ++ [i]) v.length i j

private theorem affineMulticolour_braid_correction (v : List I) (i j : I) (hij : i ≠ j) :
    (show End ((pres D Sc).obj (ob D (v ++ [i] ++ [j] ++ [i]))) from
      (crossLast D Sc v i j ▷ (pres D Sc).obj (ob D [i])) ≫
        crossLast D Sc (v ++ [j]) i i ≫
          (crossLast D Sc v j i ▷ (pres D Sc).obj (ob D [i]))) -
      (show End ((pres D Sc).obj (ob D (v ++ [i] ++ [j] ++ [i]))) from
        crossLast D Sc (v ++ [i]) j i ≫
        (crossLast D Sc v i i ▷ (pres D Sc).obj (ob D [j])) ≫
          crossLast D Sc (v ++ [i]) i j) = coefficientCorrection D Sc v i j := by
  rw [crossLast_whiskerRight_cl, crossLast_whiskerRight_cl,
    crossLast_whiskerRight_cl, crossLast, crossLast, crossLast,
    cl_comp_three, cl_comp_three]
  simp only [List.length_append, List.length_singleton]
  exact positionalCorrection_braid D Sc v i j hij
    (t := v ++ [i] ++ [j] ++ [i]) (by simp [List.append_assoc]) _ _

/-- The entire OLD source correction, retaining each interior coefficient. -/
def tripleCorrection (i j : I) (s : OldCategory D Sc cutoff) :
    End (⟨s.word ++ [i] ++ [j] ++ [i]⟩ : OldCategory D Sc cutoff) :=
  (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
    (coefficientCorrection D Sc s.word i j))

/-- The repeated-outer-colour OLD braid has exactly the prescribed dot correction. -/
theorem tripleCross_braid_correction (i j : I) (hij : i ≠ j)
    (s : OldCategory D Sc cutoff) :
    (triplePrefix D Sc cutoff i j i s ≫ tripleSuffix D Sc cutoff j i i s ≫
        triplePrefix D Sc cutoff j i i s) -
      (tripleSuffix D Sc cutoff i j i s ≫ triplePrefix D Sc cutoff i i j s ≫
        tripleSuffix D Sc cutoff i i j s) = tripleCorrection D Sc cutoff i j s := by
  rw [triplePrefix_affine, triplePrefix_affine, triplePrefix_affine]
  dsimp only [tripleSuffix, crossComponent, append, Functor.comp_obj]
  change oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      (oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
        ((ideal D Sc cutoff _ _).mkQ _)) -
    oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      (oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
        ((ideal D Sc cutoff _ _).mkQ _)) = _
  rw [oldComp_mk, oldComp_mk, oldComp_mk, oldComp_mk,
    ← affineUnit_comp, ← affineUnit_comp, ← affineUnit_comp, ← affineUnit_comp,
    ← map_sub, ← map_sub]
  exact congrArg (fun f => (ideal D Sc cutoff _ _).mkQ
    (affineUnit D Sc cutoff _ _ f)) (affineMulticolour_braid_correction D Sc s.word i j hij)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
