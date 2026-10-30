/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputBalancedComparison

/-!
# Compatible long PBW lifts

The section in `DeformedMackeyBoundary.md` §3 is constructed from the normalized
long prepend PBW tails. The source operator preserves this specified summand:
its moving part shifts the tail and its delta part acts on the entire old
coefficient. No section or intertwining identity is assumed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The normalized long tail with an arbitrary full old quotient coefficient. -/
def outputLongLift (p : ZMod 2) (i : I) (v : List I) (m : ℕ) :
    Old D Sc cutoff v v →ₗ[k] Target D Sc cutoff i v (v ++ [i]) :=
  (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m •
    Eq.mp (congrArg (fun t => Old D Sc cutoff v t →ₗ[k]
      Target D Sc cutoff i v (v ++ [i])) (longOutputIndex_oldTarget i v m))
      (pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc (longOutputIndex i v m)))

private theorem cast_pair_coordinate (p : ZMod 2) (i : I) (v : List I) (m : ℕ)
    (b : Old D Sc cutoff v v) :
    outputLongCoordinate D Sc cutoff p i v m (outputLongLift D Sc cutoff p i v m b) = b := by
  have transport {t t' : List I} (e : t = t')
      (f : Target D Sc cutoff i v (v ++ [i]) →ₗ[k] Old D Sc cutoff v t)
      (g : Old D Sc cutoff v t →ₗ[k] Target D Sc cutoff i v (v ++ [i]))
      (h : ∀ b, f (g b) = b) (s : k) (hs : s * s = 1)
      (b : Old D Sc cutoff v t') :
      (Eq.mp (congrArg (fun t => Target D Sc cutoff i v (v ++ [i]) →ₗ[k]
        Old D Sc cutoff v t) e) (s • f))
        (s • (Eq.mp (congrArg (fun t => Old D Sc cutoff v t →ₗ[k]
          Target D Sc cutoff i v (v ++ [i])) e) g) b) = b := by
    subst t'
    change s • f (s • g b) = b
    rw [map_smul, h, smul_smul, hs, one_smul]
  exact transport (longOutputIndex_oldTarget i v m) _ _
    (prependOldCoordinate_pair D Sc cutoff p (longOutputIndex i v m)) _
    (by rw [← mul_pow, SKM.zsign_mul_self', one_pow]) b

private theorem cast_pair_coordinate_off (p : ZMod 2) (i : I) (v : List I)
    (m n : ℕ) (hmn : m ≠ n) (b : Old D Sc cutoff v v) :
    outputLongCoordinate D Sc cutoff p i v m (outputLongLift D Sc cutoff p i v n b) = 0 := by
  have transport {t t' : List I} (e : t = v) (e' : t' = v)
      (f : Target D Sc cutoff i v (v ++ [i]) →ₗ[k] Old D Sc cutoff v t)
      (g : Old D Sc cutoff v t' →ₗ[k] Target D Sc cutoff i v (v ++ [i]))
      (h : ∀ b, f (g b) = 0) (s r : k) (b : Old D Sc cutoff v v) :
      (Eq.mp (congrArg (fun t => Target D Sc cutoff i v (v ++ [i]) →ₗ[k]
        Old D Sc cutoff v t) e) (s • f))
        (r • (Eq.mp (congrArg (fun t => Old D Sc cutoff v t →ₗ[k]
          Target D Sc cutoff i v (v ++ [i])) e') g) b) = 0 := by
    subst t
    subst t'
    change s • f (r • g b) = 0
    rw [map_smul, h, smul_zero, smul_zero]
  exact transport (longOutputIndex_oldTarget i v m) (longOutputIndex_oldTarget i v n) _ _
    (prependOldCoordinate_pair_off D Sc cutoff p (longOutputIndex i v m)
      (longOutputIndex i v n) (fun h => hmn (congrArg Prod.fst h))) _ _ b

/-- Extraction of the prescribed normalized long lift is a single coefficient. -/
@[simp] theorem outputLongExtraction_lift (p : ZMod 2) (i : I) (v : List I)
    (m : ℕ) (b : Old D Sc cutoff v v) :
    outputLongExtraction D Sc cutoff p i v (outputLongLift D Sc cutoff p i v m b) =
      Finsupp.single m b := by
  ext n
  rw [outputLongExtraction_apply]
  by_cases h : n = m
  · subst n
    rw [cast_pair_coordinate, Finsupp.single_eq_same]
  · rw [cast_pair_coordinate_off D Sc cutoff p i v n m h, Finsupp.single_eq_of_ne h]

/-- Finite PBW section, defined by the normalized long tails rather than choice. -/
def outputLongSection (p : ZMod 2) (i : I) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] Target D Sc cutoff i v (v ++ [i]) :=
  Finsupp.lsum k (outputLongLift D Sc cutoff p i v)

@[simp] theorem outputLongSection_single (p : ZMod 2) (i : I) (v : List I)
    (m : ℕ) (b : Old D Sc cutoff v v) :
    outputLongSection D Sc cutoff p i v (Finsupp.single m b) =
      outputLongLift D Sc cutoff p i v m b := by
  simp only [outputLongSection, Finsupp.lsum_single]

/-- The specified section is a right inverse on every finite coefficient row. -/
@[simp] theorem outputLongExtraction_section (p : ZMod 2) (i : I) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    outputLongExtraction D Sc cutoff p i v (outputLongSection D Sc cutoff p i v f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b => rw [outputLongSection_single, outputLongExtraction_lift]

private theorem longOutputIndex_shift (i : I) (v : List I) (m d : ℕ) :
    (longOutputIndex i v m).shift d = longOutputIndex i v (d + m) := by
  apply Subtype.ext
  rfl

/-- Rho preserves the specified long lift summand, with the total old twist
and the signed old delta action of the checked output convention. -/
theorem boundaryRho_outputLongLift (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (m : ℕ)
    (b : Old D Sc cutoff v v) :
    boundaryRho D Sc cutoff j v (v ++ [j.1]) (outputLongLift D Sc cutoff p j.1 v m b) =
      outputLongLift D Sc cutoff p j.1 v (m + 1) (oldTwist D Sc cutoff (D.parity j.1) v v b) +
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        ((2 * (-1 : k) ^ cutoff j.1) • outputLongLift D Sc cutoff p j.1 v m
          (oldPrecomp D Sc cutoff v v (twist k p (boundaryDelta D Sc cutoff j v)) b)) := by
  have transport {t : List I} (e : t = v)
      (f g : Old D Sc cutoff v t →ₗ[k] Target D Sc cutoff j.1 v (v ++ [j.1]))
      (h : ∀ b, boundaryRho D Sc cutoff j v (v ++ [j.1]) (f b) =
        SKM.zsign k (D.parity j.1 * wordSumParity D v) •
          (g (oldTwist D Sc cutoff (D.parity j.1) v t b) +
            (2 * (-1 : k) ^ cutoff j.1) • f
              (oldPrecomp D Sc cutoff v t (twist k p (boundaryDelta D Sc cutoff j v)) b))) :
      ∀ b : Old D Sc cutoff v v,
      boundaryRho D Sc cutoff j v (v ++ [j.1])
        ((SKM.zsign k (D.parity j.1 * wordSumParity D v)) ^ m •
          (Eq.mp (congrArg (fun t => Old D Sc cutoff v t →ₗ[k]
            Target D Sc cutoff j.1 v (v ++ [j.1])) e) f) b) =
      (SKM.zsign k (D.parity j.1 * wordSumParity D v)) ^ (m + 1) •
        (Eq.mp (congrArg (fun t => Old D Sc cutoff v t →ₗ[k]
          Target D Sc cutoff j.1 v (v ++ [j.1])) e) g)
            (oldTwist D Sc cutoff (D.parity j.1) v v b) +
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        ((2 * (-1 : k) ^ cutoff j.1) •
          ((SKM.zsign k (D.parity j.1 * wordSumParity D v)) ^ m •
          (Eq.mp (congrArg (fun t => Old D Sc cutoff v t →ₗ[k]
            Target D Sc cutoff j.1 v (v ++ [j.1])) e) f)
              (oldPrecomp D Sc cutoff v v (twist k p (boundaryDelta D Sc cutoff j v)) b))) := by
    subst t
    intro b
    change boundaryRho D Sc cutoff j v (v ++ [j.1]) (_ • f b) =
      _ • g (oldTwist D Sc cutoff (D.parity j.1) v v b) + _ • (_ • (_ • f _))
    rw [map_smul, h, smul_add, smul_add, pow_succ]
    simp only [smul_smul]
    congr 1
    congr 1
    ring
  apply transport (longOutputIndex_oldTarget j.1 v m)
  intro c
  have h := boundaryRho_pair D Sc cutoff p j (longOutputIndex j.1 v m) c
  have ht : prependTail D Sc ((longOutputIndex j.1 v m).shift 1) =
      prependTail D Sc (longOutputIndex j.1 v (m + 1)) :=
    congrArg (fun n : ℕ => (show (pres D Sc).obj (ob D
      (j.1 :: (longOutputIndex j.1 v m).oldTarget)) ⟶
        (pres D Sc).obj (ob D (v ++ [j.1])) from
          prependTail D Sc (longOutputIndex j.1 v n))) (Nat.add_comm 1 m)
  rw [ht] at h
  exact h

@[simp] theorem outputCoefficientRho_single (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (m : ℕ) (b : Old D Sc cutoff v v) :
    outputCoefficientRho D Sc cutoff p j v (Finsupp.single m b) =
      Finsupp.single (m + 1) (oldTwist D Sc cutoff (D.parity j.1) v v b) +
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        ((2 * (-1 : k) ^ cutoff j.1) • Finsupp.single m
          (oldPrecomp D Sc cutoff v v (twist k p (boundaryDelta D Sc cutoff j v)) b)) := by
  simp only [outputCoefficientRho, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- The explicitly constructed PBW section intertwines the corrected operators. -/
theorem boundaryRho_outputLongSection (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) :
    boundaryRho D Sc cutoff j v (v ++ [j.1]) (outputLongSection D Sc cutoff p j.1 v f) =
      outputLongSection D Sc cutoff p j.1 v (outputCoefficientRho D Sc cutoff p j v f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b =>
    simp only [outputLongSection_single, outputCoefficientRho_single, map_add, map_smul]
    exact boundaryRho_outputLongLift D Sc cutoff p j v m b

/-- Corrected lifts are iterates of the specified bare-long class. -/
def outputCorrectedLift (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (d : ℕ) (b : Old D Sc cutoff v v) :
    Target D Sc cutoff j.1 v (v ++ [j.1]) :=
  (boundaryRho D Sc cutoff j v (v ++ [j.1]))^[d]
    (outputLongLift D Sc cutoff p j.1 v 0 b)

/-- The compatible section lifts every corrected coordinate iterate literally. -/
theorem outputLongSection_rho_iterate (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ) (b : Old D Sc cutoff v v) :
    outputLongSection D Sc cutoff p j.1 v
      ((outputCoefficientRho D Sc cutoff p j v)^[d] (Finsupp.single 0 b)) =
        outputCorrectedLift D Sc cutoff p j v d b := by
  induction d with
  | zero => exact outputLongSection_single D Sc cutoff p j.1 v 0 b
  | succ d ih =>
    rw [Function.iterate_succ_apply', ← boundaryRho_outputLongSection, ih]
    exact (Function.iterate_succ_apply' _ _ _).symm

/-- The extracted corrected lifts are the specified finite coefficient iterates. -/
theorem outputLongExtraction_correctedLift (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ) (b : Old D Sc cutoff v v) :
    outputLongExtraction D Sc cutoff p j.1 v (outputCorrectedLift D Sc cutoff p j v d b) =
      (outputCoefficientRho D Sc cutoff p j v)^[d] (Finsupp.single 0 b) := by
  rw [← outputLongSection_rho_iterate, outputLongExtraction_section]

end OddMath.QuiverHecke.ELVOld
