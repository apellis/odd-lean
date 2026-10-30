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

/-- The signed delta coefficient in the checked normalized output convention. -/
def outputDeltaCoefficient (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    Old D Sc cutoff v v →ₗ[k] Old D Sc cutoff v v :=
  SKM.zsign k (D.parity j.1 * wordSumParity D v) •
    ((2 * (-1 : k) ^ cutoff j.1) •
      oldPrecomp D Sc cutoff v v (twist k p (boundaryDelta D Sc cutoff j v)))

/-- Even corrected iterates are the normalized even long tails. -/
theorem outputCorrectedLift_even (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (q : ℕ) (b : Old D Sc cutoff v v) :
    outputCorrectedLift D Sc cutoff p j v (2 * q) b =
      outputLongLift D Sc cutoff p j.1 v (2 * q) b := by
  have transport {t : List I} (e : t = v)
      (f g : Old D Sc cutoff v t →ₗ[k] Target D Sc cutoff j.1 v (v ++ [j.1]))
      (h : ∀ b, (boundaryRho D Sc cutoff j v (v ++ [j.1]))^[2 * q] (f b) = g b) :
      ∀ b : Old D Sc cutoff v v,
      (boundaryRho D Sc cutoff j v (v ++ [j.1]))^[2 * q]
        ((Eq.mp (congrArg (fun t => Old D Sc cutoff v t →ₗ[k]
          Target D Sc cutoff j.1 v (v ++ [j.1])) e) f) b) =
      (Eq.mp (congrArg (fun t => Old D Sc cutoff v t →ₗ[k]
          Target D Sc cutoff j.1 v (v ++ [j.1])) e) g) b := by
    subst t
    exact h
  have hs : (SKM.zsign k (D.parity j.1 * wordSumParity D v)) ^ (2 * q) = 1 := by
    rw [pow_mul, pow_two, SKM.zsign_mul_self', one_pow]
  unfold outputCorrectedLift outputLongLift
  simp only [pow_zero, one_smul, hs]
  apply transport (longOutputIndex_oldTarget j.1 v 0)
  intro c
  have h := boundaryRho_iterate_even_pair D Sc cutoff p j (longOutputIndex j.1 v 0) q c
  have ht : prependTail D Sc ((longOutputIndex j.1 v 0).shift (2 * q)) =
      prependTail D Sc (longOutputIndex j.1 v (2 * q)) :=
    congrArg (fun n : ℕ => (show (pres D Sc).obj (ob D
      (j.1 :: (longOutputIndex j.1 v 0).oldTarget)) ⟶
        (pres D Sc).obj (ob D (v ++ [j.1])) from
          prependTail D Sc (longOutputIndex j.1 v n))) (Nat.add_zero (2 * q))
  rw [ht] at h
  exact h

/-- Odd corrected iterates have exactly two adjacent normalized long tails. -/
theorem outputCorrectedLift_odd (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (q : ℕ) (b : Old D Sc cutoff v v) :
    outputCorrectedLift D Sc cutoff p j v (2 * q + 1) b =
      outputLongLift D Sc cutoff p j.1 v (2 * q + 1)
        (oldTwist D Sc cutoff (D.parity j.1) v v b) +
      outputLongLift D Sc cutoff p j.1 v (2 * q) (outputDeltaCoefficient D Sc cutoff p j v b) := by
  rw [outputCorrectedLift, Function.iterate_succ_apply']
  change boundaryRho D Sc cutoff j v (v ++ [j.1])
    (outputCorrectedLift D Sc cutoff p j v (2 * q) b) = _
  rw [outputCorrectedLift_even, boundaryRho_outputLongLift]
  simp only [outputDeltaCoefficient, LinearMap.smul_apply, map_smul]

/-- Explicit corrected coordinates, including the full old-coefficient twist. -/
theorem outputCorrectedLift_coordinates (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (q : ℕ) (b : Old D Sc cutoff v v) :
    outputLongExtraction D Sc cutoff p j.1 v (outputCorrectedLift D Sc cutoff p j v (2 * q) b) =
      Finsupp.single (2 * q) b ∧
    outputLongExtraction D Sc cutoff p j.1 v (outputCorrectedLift D Sc cutoff p j v (2 * q + 1) b) =
      Finsupp.single (2 * q + 1) (oldTwist D Sc cutoff (D.parity j.1) v v b) +
      Finsupp.single (2 * q) (outputDeltaCoefficient D Sc cutoff p j v b) := by
  constructor
  · rw [outputCorrectedLift_even, outputLongExtraction_lift]
  · rw [outputCorrectedLift_odd, map_add, outputLongExtraction_lift, outputLongExtraction_lift]

/-- Inverse triangular change on each adjacent even/odd coefficient pair. -/
def outputCorrectedPairEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    (Old D Sc cutoff v v × Old D Sc cutoff v v) ≃ₗ[k]
      (Old D Sc cutoff v v × Old D Sc cutoff v v) where
  toFun b := (b.1 + outputDeltaCoefficient D Sc cutoff p j v b.2,
    oldTwist D Sc cutoff (D.parity j.1) v v b.2)
  invFun a := (a.1 - outputDeltaCoefficient D Sc cutoff p j v
    (oldTwist D Sc cutoff (D.parity j.1) v v a.2),
    oldTwist D Sc cutoff (D.parity j.1) v v a.2)
  left_inv b := by simp only [oldTwist_twice, add_sub_cancel_right]
  right_inv a := by simp only [oldTwist_twice, sub_add_cancel]
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ext <;> simp only [Prod.fst_add, Prod.snd_add]
    abel
  map_smul' c b := by
    apply Prod.ext
    · simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, RingHom.id_apply]
    · simp only [Prod.smul_snd, map_smul, RingHom.id_apply]

/-- Applying the explicit pair change gives exactly the extracted pair of
corrected lifts; it is not an independently postulated coordinate system. -/
theorem outputCorrectedPairEquiv_extract (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (q : ℕ) (b : Old D Sc cutoff v v × Old D Sc cutoff v v) :
    outputLongExtraction D Sc cutoff p j.1 v
      (outputCorrectedLift D Sc cutoff p j v (2 * q) b.1 +
        outputCorrectedLift D Sc cutoff p j v (2 * q + 1) b.2) =
      Finsupp.single (2 * q) (outputCorrectedPairEquiv D Sc cutoff p j v b).1 +
        Finsupp.single (2 * q + 1) (outputCorrectedPairEquiv D Sc cutoff p j v b).2 := by
  rw [map_add, (outputCorrectedLift_coordinates D Sc cutoff p j v q b.1).1,
    (outputCorrectedLift_coordinates D Sc cutoff p j v q b.2).2]
  change _ = Finsupp.single (2 * q) (b.1 + outputDeltaCoefficient D Sc cutoff p j v b.2) +
    Finsupp.single (2 * q + 1) (oldTwist D Sc cutoff (D.parity j.1) v v b.2)
  rw [Finsupp.single_add]
  abel

/-- The inverse triangular formula recovers each odd PBW tail from actual
corrected iterates, without an existence or basis hypothesis. -/
theorem outputLongLift_odd_inverse (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (q : ℕ) (b : Old D Sc cutoff v v) :
    outputLongLift D Sc cutoff p j.1 v (2 * q + 1) b =
      outputCorrectedLift D Sc cutoff p j v (2 * q + 1)
        (oldTwist D Sc cutoff (D.parity j.1) v v b) -
      outputCorrectedLift D Sc cutoff p j v (2 * q)
        (outputDeltaCoefficient D Sc cutoff p j v
          (oldTwist D Sc cutoff (D.parity j.1) v v b)) := by
  rw [outputCorrectedLift_odd, oldTwist_twice, outputCorrectedLift_even, add_sub_cancel_right]

/-- The normalized lift of an arbitrary coordinate pair is obtained by the
explicit inverse triangular change, applied to actual corrected iterates. -/
theorem outputLongSection_pair_inverse (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (q : ℕ) (a : Old D Sc cutoff v v × Old D Sc cutoff v v) :
    outputLongSection D Sc cutoff p j.1 v
      (Finsupp.single (2 * q) a.1 + Finsupp.single (2 * q + 1) a.2) =
    outputCorrectedLift D Sc cutoff p j v (2 * q)
      ((outputCorrectedPairEquiv D Sc cutoff p j v).symm a).1 +
    outputCorrectedLift D Sc cutoff p j v (2 * q + 1)
      ((outputCorrectedPairEquiv D Sc cutoff p j v).symm a).2 := by
  rw [map_add, outputLongSection_single, outputLongSection_single]
  change _ = outputCorrectedLift D Sc cutoff p j v (2 * q)
    (a.1 - outputDeltaCoefficient D Sc cutoff p j v
      (oldTwist D Sc cutoff (D.parity j.1) v v a.2)) +
    outputCorrectedLift D Sc cutoff p j v (2 * q + 1)
      (oldTwist D Sc cutoff (D.parity j.1) v v a.2)
  rw [outputCorrectedLift_even, map_sub, outputCorrectedLift_odd, oldTwist_twice]
  abel

/-- Finite triangular coordinate change on all degrees, with full old coefficients. -/
def outputCorrectedChange (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  Finsupp.lsum k fun m => if m % 2 = 0 then Finsupp.lsingle m else
    (Finsupp.lsingle m).comp (oldTwist D Sc cutoff (D.parity j.1) v v) +
    (Finsupp.lsingle (m - 1)).comp (outputDeltaCoefficient D Sc cutoff p j v)

/-- Explicit inverse triangular coordinate change. -/
def outputCorrectedChangeInv (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  Finsupp.lsum k fun m => if m % 2 = 0 then Finsupp.lsingle m else
    (Finsupp.lsingle m).comp (oldTwist D Sc cutoff (D.parity j.1) v v) -
    ((Finsupp.lsingle (m - 1)).comp (outputDeltaCoefficient D Sc cutoff p j v)).comp
      (oldTwist D Sc cutoff (D.parity j.1) v v)

private theorem corrected_change_single (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (q : ℕ) (b : Old D Sc cutoff v v) :
    outputCorrectedChange D Sc cutoff p j v (Finsupp.single (2 * q) b) = Finsupp.single (2 * q) b ∧
    outputCorrectedChange D Sc cutoff p j v (Finsupp.single (2 * q + 1) b) =
      Finsupp.single (2 * q + 1) (oldTwist D Sc cutoff (D.parity j.1) v v b) +
      Finsupp.single (2 * q) (outputDeltaCoefficient D Sc cutoff p j v b) := by
  have he : 2 * q % 2 = 0 := by omega
  have ho : (2 * q + 1) % 2 ≠ 0 := by omega
  simp only [outputCorrectedChange, Finsupp.lsum_single, he, ite_true, ho, ite_false,
    LinearMap.add_apply, LinearMap.comp_apply, Finsupp.lsingle_apply, Nat.add_sub_cancel]
  exact ⟨trivial, trivial⟩

private theorem corrected_changeInv_single (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (q : ℕ) (b : Old D Sc cutoff v v) :
    outputCorrectedChangeInv D Sc cutoff p j v (Finsupp.single (2 * q) b) = Finsupp.single (2 * q) b ∧
    outputCorrectedChangeInv D Sc cutoff p j v (Finsupp.single (2 * q + 1) b) =
      Finsupp.single (2 * q + 1) (oldTwist D Sc cutoff (D.parity j.1) v v b) -
      Finsupp.single (2 * q) (outputDeltaCoefficient D Sc cutoff p j v
        (oldTwist D Sc cutoff (D.parity j.1) v v b)) := by
  have he : 2 * q % 2 = 0 := by omega
  have ho : (2 * q + 1) % 2 ≠ 0 := by omega
  simp only [outputCorrectedChangeInv, Finsupp.lsum_single, he, ite_true, ho, ite_false,
    LinearMap.sub_apply, LinearMap.comp_apply, Finsupp.lsingle_apply, Nat.add_sub_cancel]
  exact ⟨trivial, trivial⟩

/-- The corrected coordinates give a genuine automorphism of all finite rows. -/
def outputCorrectedCoordinateEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) ≃ₗ[k] (ℕ →₀ Old D Sc cutoff v v) where
  toLinearMap := outputCorrectedChange D Sc cutoff p j v
  invFun := outputCorrectedChangeInv D Sc cutoff p j v
  left_inv f := by
    change outputCorrectedChangeInv D Sc cutoff p j v
      (outputCorrectedChange D Sc cutoff p j v f) = f
    induction f using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add f g hf hg => simp only [map_add, hf, hg]
    | single m b =>
      rcases (show ∃ q, m = 2 * q ∨ m = 2 * q + 1 from ⟨m / 2, by omega⟩) with ⟨q, h | h⟩
      · subst m
        rw [(corrected_change_single D Sc cutoff p j v q b).1,
          (corrected_changeInv_single D Sc cutoff p j v q b).1]
      · subst m
        rw [(corrected_change_single D Sc cutoff p j v q b).2, map_add,
          (corrected_changeInv_single D Sc cutoff p j v q _).2,
          (corrected_changeInv_single D Sc cutoff p j v q _).1, oldTwist_twice, sub_add_cancel]
  right_inv f := by
    change outputCorrectedChange D Sc cutoff p j v
      (outputCorrectedChangeInv D Sc cutoff p j v f) = f
    induction f using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add f g hf hg => simp only [map_add, hf, hg]
    | single m b =>
      rcases (show ∃ q, m = 2 * q ∨ m = 2 * q + 1 from ⟨m / 2, by omega⟩) with ⟨q, h | h⟩
      · subst m
        rw [(corrected_changeInv_single D Sc cutoff p j v q b).1,
          (corrected_change_single D Sc cutoff p j v q b).1]
      · subst m
        rw [(corrected_changeInv_single D Sc cutoff p j v q b).2, map_sub,
          (corrected_change_single D Sc cutoff p j v q _).2,
          (corrected_change_single D Sc cutoff p j v q _).1, oldTwist_twice, add_sub_cancel_right]

/-- The complete corrected coordinate equivalence is extracted from the actual
rho iterates on the bare-long class, at every degree and full old coefficient. -/
theorem outputCorrectedCoordinateEquiv_single (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (m : ℕ) (b : Old D Sc cutoff v v) :
    outputCorrectedCoordinateEquiv D Sc cutoff p j v (Finsupp.single m b) =
      outputLongExtraction D Sc cutoff p j.1 v (outputCorrectedLift D Sc cutoff p j v m b) := by
  change outputCorrectedChange D Sc cutoff p j v (Finsupp.single m b) = _
  rcases (show ∃ q, m = 2 * q ∨ m = 2 * q + 1 from ⟨m / 2, by omega⟩) with ⟨q, h | h⟩
  · subst m
    rw [(corrected_change_single D Sc cutoff p j v q b).1,
      (outputCorrectedLift_coordinates D Sc cutoff p j v q b).1]
  · subst m
    rw [(corrected_change_single D Sc cutoff p j v q b).2,
      (outputCorrectedLift_coordinates D Sc cutoff p j v q b).2]

end OddMath.QuiverHecke.ELVOld
