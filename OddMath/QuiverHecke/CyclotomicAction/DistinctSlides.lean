import OddMath.QuiverHecke.CyclotomicAction.DistinctCrossing.DistinctModuleMate
import OddMath.QuiverHecke.CyclotomicAction.ParameterUntwist

/-!
# Distinct slides

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Distinct-colour slides in the old quotient

Brundan–Ellis (1.8): the literal old dots and positive distinct crossing
satisfy both signed slides before induction. These are the coefficient
inputs for the canonical-content and weight probe relations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem dot_affine (i : I) (s : OldCategory D Sc cutoff) :
    oldAppendDotComponent D Sc cutoff i s =
      (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
        (dotE D Sc (s.word ++ [i]) s.word.length)) := by
  rw [oldAppendDotComponent_eq, appendMovingPower, pow_one]

private theorem lowerDot_affine (i j : I) (s : OldCategory D Sc cutoff) :
    (append D Sc cutoff j).map (oldAppendDotComponent D Sc cutoff i s) =
      (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
        (dotE D Sc (s.word ++ [i] ++ [j]) s.word.length)) := by
  rw [dot_affine]
  change (ideal D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])).mkQ
    (rightContext D Sc cutoff [j] (s.word ++ [i]) (s.word ++ [i])
      (affineUnit D Sc cutoff (s.word ++ [i]) (s.word ++ [i])
        (dotE D Sc (s.word ++ [i]) s.word.length))) = _
  rw [rightContext_affineUnit]
  change (ideal D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])).mkQ
    (affineUnit D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])
      (dotE D Sc (s.word ++ [i]) s.word.length ▷ (pres D Sc).obj (ob D [j]))) = _
  rw [dotE_whiskerRight D Sc (s.word ++ [i]) [j] s.word.length (by simp)]

private theorem upperDot_affine (i j : I) (s : OldCategory D Sc cutoff) :
    oldAppendDotComponent D Sc cutoff i ((append D Sc cutoff j).obj s) =
      (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
        (dotE D Sc (s.word ++ [j] ++ [i]) (s.word.length + 1))) := by
  simpa only [append, List.length_append, List.length_singleton] using
    dot_affine D Sc cutoff i ((append D Sc cutoff j).obj s)

/-- The source first dot exits on the second strand, retaining its sign. -/
theorem crossComponent_slide_first {i j : I} (hij : i ≠ j)
    (s : OldCategory D Sc cutoff) :
    (append D Sc cutoff i).map (oldAppendDotComponent D Sc cutoff j s) ≫
        crossComponent D Sc cutoff i j s =
      sign k (D.parity j * D.parity i) •
        (crossComponent D Sc cutoff i j s ≫
          oldAppendDotComponent D Sc cutoff j ((append D Sc cutoff i).obj s)) := by
  rw [lowerDot_affine, upperDot_affine]
  change oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _) = sign k (D.parity j * D.parity i) •
    oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _)
  rw [oldComp_mk, oldComp_mk, ← map_smul]
  simp only [append, Functor.comp_obj]
  rw [← affineUnit_comp, ← affineUnit_comp,
    dotE_comp_crossLast_ne D Sc s.word hij.symm, map_smul, ← sign_eq_zsign]

/-- The source second dot exits on the first strand with the same sign. -/
theorem crossComponent_slide_last {i j : I} (hij : i ≠ j)
    (s : OldCategory D Sc cutoff) :
    oldAppendDotComponent D Sc cutoff i ((append D Sc cutoff j).obj s) ≫
        crossComponent D Sc cutoff i j s =
      sign k (D.parity j * D.parity i) •
        (crossComponent D Sc cutoff i j s ≫
          (append D Sc cutoff j).map (oldAppendDotComponent D Sc cutoff i s)) := by
  rw [upperDot_affine, lowerDot_affine]
  change oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _) = sign k (D.parity j * D.parity i) •
    oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _)
  rw [oldComp_mk, oldComp_mk, ← map_smul]
  simp only [append, Functor.comp_obj]
  rw [← affineUnit_comp, ← affineUnit_comp,
    lastDotE_comp_crossLast_ne D Sc s.word hij.symm, map_smul, ← sign_eq_zsign]

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.Distinct
end

end

section

/-! # The distinct-colour quadratic in the untruncated old quotient

Brundan–Ellis (1.7) and DeformedActionAssembly §6 (9): the literal
positive old crossings compose to the prescribed ordered dot polynomial.
On the probe parameter family `parameterTwist D Sc`, the crossing-square
sign recovers the signed evaluation with the original parameters `Sc`.
No truncation, quadratic premise or action premise is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem crossLast_quadratic (v : List I) {i j : I} (hij : i ≠ j) :
    crossLast D Sc v j i ≫ crossLast D Sc v i j =
      pairQuadPoly D Sc j i
        (dotE D Sc (v ++ [j] ++ [i]) v.length)
        (dotE D Sc (v ++ [j] ++ [i]) (v.length + 1)) := by
  rw [crossLast, crossLast, cl_comp]
  have aux {t : List I} (ht : t = v ++ [j,i] ++ [])
      (h : SChain t (pl t [.cross v.length, .cross v.length]) t) :
      cl D Sc t t [.cross v.length, .cross v.length] h =
        pairQuadPoly D Sc j i (dotE D Sc t v.length) (dotE D Sc t (v.length + 1)) := by
    subst t
    unfold pairQuadPoly
    split_ifs with hd
    · exact cross_cross_ne_zero D Sc v [] hij.symm hd h
    · exact cross_cross_ne D Sc v [] hij.symm hd h
  exact aux (by simp [List.append_assoc]) _

/-- The two literal positive distinct crossings satisfy the full source quadratic. -/
theorem crossComponent_quadratic {i j : I} (hij : i ≠ j)
    (s : OldCategory D Sc cutoff) :
    crossComponent D Sc cutoff i j s ≫ crossComponent D Sc cutoff j i s =
      (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
        (pairQuadPoly D Sc (R := End ((pres D Sc).obj (ob D (s.word ++ [j] ++ [i])))) j i
          (dotE D Sc (s.word ++ [j] ++ [i]) s.word.length)
          (dotE D Sc (s.word ++ [j] ++ [i]) (s.word.length + 1)))) := by
  change oldComp D Sc cutoff (s.word ++ [j] ++ [i]) (s.word ++ [i] ++ [j])
    (s.word ++ [j] ++ [i]) ((ideal D Sc cutoff _ _).mkQ _)
    ((ideal D Sc cutoff _ _).mkQ _) = _
  rw [oldComp_mk, ← affineUnit_comp, crossLast_quadratic D Sc s.word hij]
  rfl

/-- The probe's parameter involution leaves exactly the original ordered signed polynomial. -/
theorem crossComponent_parameterUntwist {i j : I} (hij : i ≠ j)
    (s : OldCategory D (parameterTwist D Sc) cutoff) :
    sign k (D.parity i * D.parity j) •
        (crossComponent D (parameterTwist D Sc) cutoff i j s ≫
          crossComponent D (parameterTwist D Sc) cutoff j i s) =
      (ideal D (parameterTwist D Sc) cutoff _ _).mkQ
        (affineUnit D (parameterTwist D Sc) cutoff _ _
          (elvSignedPairQuadEval D Sc
            (R := End ((pres D (parameterTwist D Sc)).obj (ob D (s.word ++ [j] ++ [i])))) j i
            (dotE D (parameterTwist D Sc) (s.word ++ [j] ++ [i]) s.word.length)
            (dotE D (parameterTwist D Sc) (s.word ++ [j] ++ [i]) (s.word.length + 1)))) := by
  rw [crossComponent_quadratic D _ cutoff hij]
  have h := pairQuadPoly_parameterTwist_reversed_eval D Sc
    (R := End ((pres D (parameterTwist D Sc)).obj (ob D (s.word ++ [j] ++ [i])))) hij
    (dotE D (parameterTwist D Sc) (s.word ++ [j] ++ [i]) s.word.length)
    (dotE D (parameterTwist D Sc) (s.word ++ [j] ++ [i]) (s.word.length + 1))
  simpa only [map_smul, sign_eq_zsign] using congrArg
    (fun a => (ideal D (parameterTwist D Sc) cutoff _ _).mkQ
      (affineUnit D (parameterTwist D Sc) cutoff _ _ a)) h

/-- Original-parameter signed polynomial on the two appended source positions. -/
def signedQuadraticComponent (i j : I)
    (s : OldCategory D (parameterTwist D Sc) cutoff) :
    End (((append D (parameterTwist D Sc) cutoff i) ⋙
      (append D (parameterTwist D Sc) cutoff j)).obj s) :=
  (ideal D (parameterTwist D Sc) cutoff _ _).mkQ
    (affineUnit D (parameterTwist D Sc) cutoff _ _
      (elvSignedPairQuadEval D Sc
        (R := End ((pres D (parameterTwist D Sc)).obj (ob D (s.word ++ [i] ++ [j])))) i j
        (dotE D (parameterTwist D Sc) (s.word ++ [i] ++ [j]) s.word.length)
        (dotE D (parameterTwist D Sc) (s.word ++ [i] ++ [j]) (s.word.length + 1))))

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.Distinct
end

end

section

/-! # The literal original-parameter polynomial in the two OLD append dots

DeformedActionAssembly §6 (9): the ordered affine polynomial descends as
exactly the same polynomial in the two independent untruncated OLD dots.
No commutation or action relation is imposed on these dots.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Scalar affine endomorphisms map into the actual old quotient endomorphism algebra. -/
def oldAffineEndAlgHom (s : OldCategory D Sc cutoff) :
    End ((pres D Sc).obj (ob D s.word)) →ₐ[k] End s :=
  AlgHom.ofLinearMap
    ((ideal D Sc cutoff s.word s.word).mkQ.comp (affineUnit D Sc cutoff s.word s.word))
    (by
      change (ideal D Sc cutoff s.word s.word).mkQ (affineUnit D Sc cutoff s.word s.word (𝟙 _)) =
        (ideal D Sc cutoff s.word s.word).mkQ (𝟙 _)
      rw [affineUnit_id])
    (fun f g => by
      change (ideal D Sc cutoff s.word s.word).mkQ (affineUnit D Sc cutoff s.word s.word (g ≫ f)) =
        oldComp D Sc cutoff s.word s.word s.word
          ((ideal D Sc cutoff s.word s.word).mkQ (affineUnit D Sc cutoff s.word s.word g))
          ((ideal D Sc cutoff s.word s.word).mkQ (affineUnit D Sc cutoff s.word s.word f))
      rw [oldComp_mk, ← affineUnit_comp])

/-- Ordered signed source evaluations commute with algebra homomorphisms. -/
theorem elvSignedPairQuadEval_map {R S : Type*} [Ring R] [Algebra k R]
    [Ring S] [Algebra k S] (e : R →ₐ[k] S) (i j : I) (a b : R) :
    e (elvSignedPairQuadEval D Sc i j a b) = elvSignedPairQuadEval D Sc i j (e a) (e b) := by
  unfold elvSignedPairQuadEval
  split_ifs <;> simp only [map_smul, map_one, map_add, map_sum, map_mul, map_pow]

namespace CyclotomicCrossingTensor.Distinct

/-- The independently appended lower dot, whiskered into the two-letter source. -/
def pairFirstDot (i j : I) (s : OldCategory D Sc cutoff) :
    End (((append D Sc cutoff i) ⋙ (append D Sc cutoff j)).obj s) :=
  (append D Sc cutoff j).map (oldAppendDotComponent D Sc cutoff i s)

/-- The independent upper dot in the same source endomorphism algebra. -/
def pairSecondDot (i j : I) (s : OldCategory D Sc cutoff) :
    End (((append D Sc cutoff i) ⋙ (append D Sc cutoff j)).obj s) :=
  oldAppendDotComponent D Sc cutoff j ((append D Sc cutoff i).obj s)

theorem pairFirstDot_affine (i j : I) (s : OldCategory D Sc cutoff) :
    pairFirstDot D Sc cutoff i j s =
      oldAffineEndAlgHom D Sc cutoff (((append D Sc cutoff i) ⋙ (append D Sc cutoff j)).obj s)
        (dotE D Sc (s.word ++ [i] ++ [j]) s.word.length) := by
  rw [pairFirstDot, oldAppendDotComponent_eq, appendMovingPower, pow_one]
  change (ideal D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])).mkQ
    (rightContext D Sc cutoff [j] (s.word ++ [i]) (s.word ++ [i])
      (affineUnit D Sc cutoff (s.word ++ [i]) (s.word ++ [i])
        (dotE D Sc (s.word ++ [i]) s.word.length))) = _
  rw [rightContext_affineUnit]
  change (ideal D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])).mkQ
    (affineUnit D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])
      (dotE D Sc (s.word ++ [i]) s.word.length ▷ (pres D Sc).obj (ob D [j]))) = _
  rw [dotE_whiskerRight D Sc (s.word ++ [i]) [j] s.word.length (by simp)]
  rfl

theorem pairSecondDot_affine (i j : I) (s : OldCategory D Sc cutoff) :
    pairSecondDot D Sc cutoff i j s =
      oldAffineEndAlgHom D Sc cutoff (((append D Sc cutoff i) ⋙ (append D Sc cutoff j)).obj s)
        (dotE D Sc (s.word ++ [i] ++ [j]) (s.word.length + 1)) := by
  rw [pairSecondDot, oldAppendDotComponent_eq, appendMovingPower, pow_one]
  change (ideal D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])).mkQ
    (affineUnit D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])
      (dotE D Sc (s.word ++ [i] ++ [j]) (s.word ++ [i]).length)) =
    (ideal D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])).mkQ
      (affineUnit D Sc cutoff (s.word ++ [i] ++ [j]) (s.word ++ [i] ++ [j])
        (dotE D Sc (s.word ++ [i] ++ [j]) (s.word.length + 1)))
  rw [List.length_append, List.length_singleton]

/-- The source polynomial is literally the polynomial of the two chosen OLD dots. -/
theorem signedQuadraticComponent_pairDots (i j : I)
    (s : OldCategory D (parameterTwist D Sc) cutoff) :
    signedQuadraticComponent D Sc cutoff i j s =
      elvSignedPairQuadEval D Sc
        (R := End (((append D (parameterTwist D Sc) cutoff i) ⋙
          (append D (parameterTwist D Sc) cutoff j)).obj s)) i j
        (pairFirstDot D (parameterTwist D Sc) cutoff i j s)
        (pairSecondDot D (parameterTwist D Sc) cutoff i j s) := by
  rw [pairFirstDot_affine, pairSecondDot_affine, ← elvSignedPairQuadEval_map]
  rfl

end CyclotomicCrossingTensor.Distinct
end OddMath.QuiverHecke.ELV
end

end

section

/-! # Multicolour braids in the untruncated OLD coefficient category

Brundan–Ellis (1.9): retain the independently appended positive crossings,
including the repeated-outer-colour dot correction with all interior scalar
parameters. These coefficient relations precede balanced induction and its
superopposite signs. No source braid or truncation premise is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
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
      ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
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

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Multicolour OLD braids on direct triple induction

Brundan–Ellis (1.9): the independently whiskered positive coefficient
crossings induce the whole direct triple-induction braid. The actual
OLD quotient supplies the source relation; no braid premise is introduced.
The negative equal-colour crossing normalization, rectangular flattening
and repeated-outer ordered correction are separate attachments.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
open BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The append along the prescribed three source colours. -/
abbrev tripleAppend (i j l : I) :=
  (append D Sc cutoff i ⋙ append D Sc cutoff j) ⋙ append D Sc cutoff l

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end
