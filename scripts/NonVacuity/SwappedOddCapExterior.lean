import OddMath.QuiverHecke.SwappedVacuum.InverseCapMoments
import StringDiagrams.Super.SVec
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A signed height-zero cap retaining a nonzero exterior coefficient.
The coefficient module is Q[δ]/δ², the reservoir relation is t²+δt,
and the signed probe dot squares to -1. This is an occupied superspace
model of the cap calculation; it is not an attachment to a factor action. -/
noncomputable section
namespace NonVacuity.SwappedOddCapExterior
open CategoryTheory StringDiagrams Supercategory OddMath.QuiverHecke.SwappedVacuum

private abbrev Coeff : SVec ℚ where
  carrier := ℚ × ℚ
  odd := (0 : (ℚ × ℚ) →ₗ[ℚ] ℚ).prod (LinearMap.snd ℚ ℚ ℚ)
  odd_comp_odd := by ext <;> simp

-- Ordered coordinates are ((1,δt),(δ,t)), with the even part first.
private abbrev Word : SVec ℚ where
  carrier := (ℚ × ℚ) × (ℚ × ℚ)
  odd := (0 : ((ℚ × ℚ) × (ℚ × ℚ)) →ₗ[ℚ] (ℚ × ℚ)).prod
    (LinearMap.snd ℚ (ℚ × ℚ) (ℚ × ℚ))
  odd_comp_odd := by ext <;> simp

private def delta : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ) where
  toFun z := (0, z.1)
  map_add' _ _ := by (apply Prod.ext <;> try apply Prod.ext) <;> simp
  map_smul' _ _ := by (apply Prod.ext <;> try apply Prod.ext) <;> simp

private def wordDelta : ((ℚ × ℚ) × (ℚ × ℚ)) →ₗ[ℚ] ((ℚ × ℚ) × (ℚ × ℚ)) where
  toFun z := ((0, z.2.2), (z.1.1, 0))
  map_add' _ _ := by (apply Prod.ext <;> try apply Prod.ext) <;> simp
  map_smul' _ _ := by (apply Prod.ext <;> try apply Prod.ext) <;> simp

private def probeDot : ((ℚ × ℚ) × (ℚ × ℚ)) →ₗ[ℚ] ((ℚ × ℚ) × (ℚ × ℚ)) where
  toFun z := ((-z.2.2, -z.2.1), (z.1.2, z.1.1))
  map_add' _ _ := by (apply Prod.ext <;> try apply Prod.ext) <;> simp [add_comm]
  map_smul' _ _ := by (apply Prod.ext <;> try apply Prod.ext) <;> simp

private def reservoirDot : ((ℚ × ℚ) × (ℚ × ℚ)) →ₗ[ℚ] ((ℚ × ℚ) × (ℚ × ℚ)) where
  toFun z := ((0, -z.2.1 + z.2.2), (0, z.1.1))
  map_add' _ _ := by (apply Prod.ext <;> try apply Prod.ext) <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' _ _ := by (apply Prod.ext <;> try apply Prod.ext) <;> simp [mul_add]

private def unsignedDot : ((ℚ × ℚ) × (ℚ × ℚ)) →ₗ[ℚ] ((ℚ × ℚ) × (ℚ × ℚ)) where
  toFun z := ((0, z.2.1 - z.2.2), (0, z.1.1))
  map_add' _ _ := by (apply Prod.ext <;> try apply Prod.ext) <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' _ _ := by (apply Prod.ext <;> try apply Prod.ext) <;> simp [mul_sub]

private def unitColumn : (ℚ × ℚ) →ₗ[ℚ] ((ℚ × ℚ) × (ℚ × ℚ)) where
  toFun z := ((z.1, 0), (z.2, 0))
  map_add' _ _ := by (apply Prod.ext <;> try apply Prod.ext) <;> simp
  map_smul' _ _ := by (apply Prod.ext <;> try apply Prod.ext) <;> simp

private def coefficientExtraction : ((ℚ × ℚ) × (ℚ × ℚ)) →ₗ[ℚ] (ℚ × ℚ) where
  toFun z := (z.2.2, -z.1.2)
  map_add' _ _ := by (apply Prod.ext <;> try apply Prod.ext) <;> simp [add_comm]
  map_smul' _ _ := by (apply Prod.ext <;> try apply Prod.ext) <;> simp

private def principalMap : ((ℚ × ℚ) × (ℚ × ℚ)) →ₗ[ℚ] ((ℚ × ℚ) × (ℚ × ℚ)) where
  toFun z := ((-z.1.1, z.1.1 + z.1.2), (-z.2.1, z.2.2))
  map_add' _ _ := by (apply Prod.ext <;> try apply Prod.ext) <;> simp [add_left_comm, add_comm]
  map_smul' _ _ := by (apply Prod.ext <;> try apply Prod.ext) <;> simp [mul_add]

private def principalInverse : Word ≅ Word where
  hom := principalMap
  inv := principalMap
  hom_inv_id := by
    change principalMap.comp principalMap = LinearMap.id
    apply LinearMap.ext
    intro z
    (apply Prod.ext <;> try apply Prod.ext) <;> simp [principalMap]
  inv_hom_id := by
    change principalMap.comp principalMap = LinearMap.id
    apply LinearMap.ext
    intro z
    (apply Prod.ext <;> try apply Prod.ext) <;> simp [principalMap]

private def coefficients (n : ℕ) : ℚ := if n = 0 ∨ n = 2 then 1 else 0

/-- The exterior direction survives. -/
example : delta ≠ 0 := by
  intro h
  have h' := congrArg (fun f : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ) => (f (1, 0)).2) h
  change (1 : ℚ) = 0 at h'
  norm_num at h'

example : delta.comp delta = 0 := by
  apply LinearMap.ext
  intro z
  rfl

/-- The exterior coefficient is odd. -/
example : (delta : Coeff ⟶ Coeff) ∈ SVec.parityHom Coeff Coeff 1 := by
  intro q
  rcases parity_eq_zero_or_one q with rfl | rfl <;>
    apply LinearMap.ext <;> intro z <;>
    (apply Prod.ext <;> try apply Prod.ext) <;>
    simp [SVec.toLinearMap, SVec.proj_zero, SVec.proj_one, delta]

/-- The unsigned reservoir relation t²+δt=0 is retained. -/
example : unsignedDot.comp unsignedDot + wordDelta.comp unsignedDot = 0 := by
  apply LinearMap.ext
  intro z
  (apply Prod.ext <;> try apply Prod.ext) <;> simp [unsignedDot, wordDelta]

example : reservoirDot.comp reservoirDot ≠ 0 := by
  intro h
  have h' := congrArg (fun f : ((ℚ × ℚ) × (ℚ × ℚ)) →ₗ[ℚ] ((ℚ × ℚ) × (ℚ × ℚ)) =>
    (f ((1, 0), (0, 0))).1.2) h
  norm_num [reservoirDot] at h'

/-- The signed dots retain odd A-linearity against the surviving δ. -/
example : reservoirDot.comp wordDelta = -(wordDelta.comp reservoirDot) := by
  apply LinearMap.ext
  intro z
  (apply Prod.ext <;> try apply Prod.ext) <;> simp [wordDelta, reservoirDot]

example : probeDot.comp wordDelta = -(wordDelta.comp probeDot) := by
  apply LinearMap.ext
  intro z
  (apply Prod.ext <;> try apply Prod.ext) <;> simp [wordDelta, probeDot]

/-- Coefficient extraction is odd A-linear; omitting this sign changes K1. -/
example : coefficientExtraction.comp wordDelta = -(delta.comp coefficientExtraction) := by
  apply LinearMap.ext
  intro z
  (apply Prod.ext <;> try apply Prod.ext) <;> simp [wordDelta, coefficientExtraction, delta]

example : unitColumn.comp delta = wordDelta.comp unitColumn := by
  apply LinearMap.ext
  intro z
  (apply Prod.ext <;> try apply Prod.ext) <;> simp [wordDelta, unitColumn, delta]

example : principalMap.comp wordDelta = wordDelta.comp principalMap := by
  apply LinearMap.ext
  intro z
  (apply Prod.ext <;> try apply Prod.ext) <;> simp [wordDelta, principalMap]

example : wordDelta.comp wordDelta = 0 := by
  apply LinearMap.ext
  intro z
  rfl

example : (wordDelta : Word ⟶ Word) ∈ SVec.parityHom Word Word 1 := by
  intro q
  rcases parity_eq_zero_or_one q with rfl | rfl <;>
    apply LinearMap.ext <;> intro z <;>
    (apply Prod.ext <;> try apply Prod.ext) <;>
    simp [SVec.toLinearMap, SVec.proj_zero, SVec.proj_one, wordDelta]

/-- Both dot maps and the coefficient-extraction map are odd in the
displayed superspaces. -/
example : (probeDot : Word ⟶ Word) ∈ SVec.parityHom Word Word 1 := by
  intro q
  rcases parity_eq_zero_or_one q with rfl | rfl <;>
    apply LinearMap.ext <;> intro z <;>
    (apply Prod.ext <;> try apply Prod.ext) <;>
    simp [SVec.toLinearMap, SVec.proj_zero, SVec.proj_one, probeDot]

example : (reservoirDot : Word ⟶ Word) ∈ SVec.parityHom Word Word 1 := by
  intro q
  rcases parity_eq_zero_or_one q with rfl | rfl <;>
    apply LinearMap.ext <;> intro z <;>
    (apply Prod.ext <;> try apply Prod.ext) <;>
    simp [SVec.toLinearMap, SVec.proj_zero, SVec.proj_one, reservoirDot]

example : (coefficientExtraction : Word ⟶ Coeff) ∈ SVec.parityHom Word Coeff 1 := by
  intro q
  rcases parity_eq_zero_or_one q with rfl | rfl <;>
    apply LinearMap.ext <;> intro z <;>
    (apply Prod.ext <;> try apply Prod.ext) <;>
    simp [SVec.toLinearMap, SVec.proj_zero, SVec.proj_one, coefficientExtraction]

/-- The principal inverse and ordinary unit retain even parity. -/
example : (principalMap : Word ⟶ Word) ∈ SVec.parityHom Word Word 0 := by
  intro q
  rcases parity_eq_zero_or_one q with rfl | rfl <;>
    apply LinearMap.ext <;> intro z <;>
    (apply Prod.ext <;> try apply Prod.ext) <;>
    simp [SVec.toLinearMap, SVec.proj_zero, SVec.proj_one, principalMap]

example : (unitColumn : Coeff ⟶ Word) ∈ SVec.parityHom Coeff Word 0 := by
  intro q
  rcases parity_eq_zero_or_one q with rfl | rfl <;>
    apply LinearMap.ext <;> intro z <;>
    (apply Prod.ext <;> try apply Prod.ext) <;>
    simp [SVec.toLinearMap, SVec.proj_zero, SVec.proj_one, unitColumn]

private theorem slide : reservoirDot.comp principalMap + principalMap.comp probeDot =
    unitColumn.comp coefficientExtraction := by
  apply LinearMap.ext
  intro z
  (apply Prod.ext <;> try apply Prod.ext) <;>
    simp [principalMap, probeDot, reservoirDot, coefficientExtraction, unitColumn]

private theorem window (a : ℕ) (ha : a < 2) :
    coefficientExtraction.comp ((reservoirDot ^ a).comp unitColumn) =
      if a + 1 = 2 then LinearMap.id else 0 := by
  interval_cases a <;> apply LinearMap.ext <;> intro z <;>
    (apply Prod.ext <;> try apply Prod.ext) <;>
    simp [unitColumn, reservoirDot, coefficientExtraction]

private theorem probe_relation :
    capPolynomial (C := SVec ℚ) (X := Word) coefficients 2 probeDot = 0 := by
  let x : End Word := SVec.ofHom (V := Word) (W := Word) probeDot
  change capPolynomial coefficients 2 x = 0
  have heval : capPolynomial coefficients 2 x = (1 : End Word) + x * x := by
    simp [capPolynomial, Finset.sum_range_succ, coefficients, pow_two]
  rw [heval]
  change (LinearMap.id : ((ℚ × ℚ) × (ℚ × ℚ)) →ₗ[ℚ] ((ℚ × ℚ) × (ℚ × ℚ))) +
    probeDot.comp probeDot = 0
  apply LinearMap.ext
  intro z
  change z + probeDot (probeDot z) = 0
  (apply Prod.ext <;> try apply Prod.ext) <;> simp [probeDot]

/-- The principal inverse cap follows from the signed slide and extraction
window, while retaining the exterior coefficient. -/
example : coefficientExtraction.comp principalMap =
    coefficientExtraction.comp (capPolynomial (C := SVec ℚ) (X := Word) coefficients 2 reservoirDot) := by
  exact principal_inverse_cap (C := SVec ℚ) (V := Coeff) (X := Word) (Y := Word)
    (-1 : ℚ) probeDot reservoirDot
    principalInverse unitColumn coefficientExtraction coefficientExtraction 2 (by norm_num)
    coefficients (by simp [coefficients])
    (by intro n hn; interval_cases n <;> simp [coefficients])
    (by
      change reservoirDot.comp principalMap - (-1 : ℚ) • (principalMap.comp probeDot) =
        unitColumn.comp coefficientExtraction
      apply LinearMap.ext
      intro z
      (apply Prod.ext <;> try apply Prod.ext) <;>
        simp [reservoirDot, principalMap, probeDot, unitColumn, coefficientExtraction])
    window probe_relation

/-- The first odd moment is -δ, including its nonzero exterior value. -/
example : coefficientExtraction.comp (principalMap.comp unitColumn) = -delta := by
  apply LinearMap.ext
  intro z
  (apply Prod.ext <;> try apply Prod.ext) <;>
    simp [principalMap, unitColumn, coefficientExtraction, delta]

example : coefficientExtraction.comp (principalMap.comp (reservoirDot.comp unitColumn)) =
    LinearMap.id := by
  apply LinearMap.ext
  intro z
  (apply Prod.ext <;> try apply Prod.ext) <;>
    simp [principalMap, unitColumn, coefficientExtraction, reservoirDot]

example : coefficientExtraction.comp
    (principalMap.comp ((reservoirDot.comp reservoirDot).comp unitColumn)) = -delta := by
  apply LinearMap.ext
  intro z
  (apply Prod.ext <;> try apply Prod.ext) <;>
    simp [principalMap, unitColumn, coefficientExtraction, reservoirDot, delta]

end NonVacuity.SwappedOddCapExterior
