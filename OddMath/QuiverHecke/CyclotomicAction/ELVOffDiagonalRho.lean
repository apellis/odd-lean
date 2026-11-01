import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalLongCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryRhoCoordinates

/-! # Corrected rho on arbitrary old-Hom long sections

The source-operator comparison in DeformedMackeyBoundary (2)-(3), with
independent old source and target words. The entire old coefficient is
twisted, and delta acts at the old source. No field, action, matrix inverse
or supplied coordinate-intertwining hypothesis is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Corrected coefficient rho retains its full total-parity and source-delta actions. -/
def offDiagonalCoefficientRho (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) : (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  (Finsupp.lmapDomain (Old D Sc cutoff v t) k Nat.succ).comp
      (Finsupp.mapRange.linearMap (oldTwist D Sc cutoff (D.parity j.1) v t)) +
    SKM.zsign k (D.parity j.1 * wordSumParity D v) •
      ((2 * (-1 : k) ^ cutoff j.1) •
        Finsupp.mapRange.linearMap
          (oldPrecomp D Sc cutoff v t (twist k p (boundaryDelta D Sc cutoff j v))))

@[simp] theorem offDiagonalCoefficientRho_single (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ) (b : Old D Sc cutoff v t) :
    offDiagonalCoefficientRho D Sc cutoff p j v t (Finsupp.single m b) =
      Finsupp.single (m + 1) (oldTwist D Sc cutoff (D.parity j.1) v t b) +
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        ((2 * (-1 : k) ^ cutoff j.1) • Finsupp.single m
          (oldPrecomp D Sc cutoff v t (twist k p (boundaryDelta D Sc cutoff j v)) b)) := by
  simp only [offDiagonalCoefficientRho, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- Actual corrected rho acts on each off-diagonal long lift by the specified two terms. -/
theorem boundaryRho_longHomLift (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) {v t : List I} (y : NFIdx v t) (m : ℕ)
    (b : Old D Sc cutoff v t) :
    boundaryRho D Sc cutoff j v (t ++ [j.1]) (longHomLift D Sc cutoff p j.1 y m b) =
      longHomLift D Sc cutoff p j.1 y (m + 1) (oldTwist D Sc cutoff (D.parity j.1) v t b) +
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        ((2 * (-1 : k) ^ cutoff j.1) • longHomLift D Sc cutoff p j.1 y m
          (oldPrecomp D Sc cutoff v t (twist k p (boundaryDelta D Sc cutoff j v)) b)) := by
  have transport {s : List I} (e : s = t)
      (f g : Old D Sc cutoff v s →ₗ[k] Target D Sc cutoff j.1 v (t ++ [j.1]))
      (h : ∀ b, boundaryRho D Sc cutoff j v (t ++ [j.1]) (f b) =
        SKM.zsign k (D.parity j.1 * wordSumParity D v) •
          (g (oldTwist D Sc cutoff (D.parity j.1) v s b) +
            (2 * (-1 : k) ^ cutoff j.1) • f
              (oldPrecomp D Sc cutoff v s (twist k p (boundaryDelta D Sc cutoff j v)) b))) :
      ∀ b : Old D Sc cutoff v t,
      boundaryRho D Sc cutoff j v (t ++ [j.1])
        ((SKM.zsign k (D.parity j.1 * wordSumParity D v)) ^ m •
          (Eq.mp (congrArg (fun s => Old D Sc cutoff v s →ₗ[k]
            Target D Sc cutoff j.1 v (t ++ [j.1])) e) f) b) =
      (SKM.zsign k (D.parity j.1 * wordSumParity D v)) ^ (m + 1) •
        (Eq.mp (congrArg (fun s => Old D Sc cutoff v s →ₗ[k]
          Target D Sc cutoff j.1 v (t ++ [j.1])) e) g)
            (oldTwist D Sc cutoff (D.parity j.1) v t b) +
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        ((2 * (-1 : k) ^ cutoff j.1) •
          ((SKM.zsign k (D.parity j.1 * wordSumParity D v)) ^ m •
          (Eq.mp (congrArg (fun s => Old D Sc cutoff v s →ₗ[k]
            Target D Sc cutoff j.1 v (t ++ [j.1])) e) f)
              (oldPrecomp D Sc cutoff v t (twist k p (boundaryDelta D Sc cutoff j v)) b))) := by
    subst s
    intro b
    change boundaryRho D Sc cutoff j v (t ++ [j.1]) (_ • f b) =
      _ • g (oldTwist D Sc cutoff (D.parity j.1) v t b) + _ • (_ • (_ • f _))
    rw [map_smul, h, smul_add, smul_add, pow_succ]
    simp only [smul_smul]
    congr 1
    congr 1
    ring
  apply transport (longHomIndex_oldTarget j.1 y m)
  intro c
  have h := boundaryRho_pair D Sc cutoff p j (longHomIndex j.1 y m) c
  have ht : prependTail D Sc ((longHomIndex j.1 y m).shift 1) =
      prependTail D Sc (longHomIndex j.1 y (m + 1)) :=
    congrArg (fun n : ℕ => (show (pres D Sc).obj (ob D
      (j.1 :: (longHomIndex j.1 y m).oldTarget)) ⟶
        (pres D Sc).obj (ob D (t ++ [j.1])) from
          prependTail D Sc (longHomIndex j.1 y n))) (Nat.add_comm 1 m)
  rw [ht] at h
  exact h

@[simp] theorem longHomSection_single (p : ZMod 2) (i : I) {v t : List I}
    (y : NFIdx v t) (m : ℕ) (b : Old D Sc cutoff v t) :
    longHomSection D Sc cutoff p i y (Finsupp.single m b) =
      longHomLift D Sc cutoff p i y m b := by
  simp only [longHomSection, Finsupp.lsum_single]

theorem boundaryRho_longHomSection (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) {v t : List I}
    (y : NFIdx v t) (f : ℕ →₀ Old D Sc cutoff v t) :
    boundaryRho D Sc cutoff j v (t ++ [j.1]) (longHomSection D Sc cutoff p j.1 y f) =
      longHomSection D Sc cutoff p j.1 y (offDiagonalCoefficientRho D Sc cutoff p j v t f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b =>
    simp only [longHomSection_single, offDiagonalCoefficientRho_single, map_add, map_smul]
    exact boundaryRho_longHomLift D Sc cutoff p j y m b

/-- The unconditional arbitrary-Hom section intertwines the actual corrected operators. -/
theorem boundaryRho_offDiagonalLongSection (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    boundaryRho D Sc cutoff j v (t ++ [j.1]) (offDiagonalLongSection D Sc cutoff p j.1 v t f) =
      offDiagonalLongSection D Sc cutoff p j.1 v t
        (offDiagonalCoefficientRho D Sc cutoff p j v t f) := by
  by_cases h : Nonempty (NFIdx v t)
  · obtain ⟨y⟩ := h
    simp only [offDiagonalLongSection_eq D Sc cutoff p j.1 y]
    exact boundaryRho_longHomSection D Sc cutoff p j y f
  · have hf : f = 0 := by
      ext n
      exact old_eq_zero_of_no_normal_form D Sc cutoff h (f n)
    rw [hf]
    simp only [map_zero]

/-- Corrected off-diagonal lifts are actual source rho iterates. -/
def offDiagonalCorrectedLift (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (d : ℕ) (b : Old D Sc cutoff v t) :
    Target D Sc cutoff j.1 v (t ++ [j.1]) :=
  (boundaryRho D Sc cutoff j v (t ++ [j.1]))^[d]
    (offDiagonalLongSection D Sc cutoff p j.1 v t (Finsupp.single 0 b))

theorem offDiagonalLongSection_rho_iterate (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (d : ℕ) (b : Old D Sc cutoff v t) :
    offDiagonalLongSection D Sc cutoff p j.1 v t
      ((offDiagonalCoefficientRho D Sc cutoff p j v t)^[d] (Finsupp.single 0 b)) =
        offDiagonalCorrectedLift D Sc cutoff p j v t d b := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', ← boundaryRho_offDiagonalLongSection, ih]
    exact (Function.iterate_succ_apply' _ _ _).symm

/-- Extraction of actual corrected lifts gives the prescribed finite coefficient iterates. -/
theorem offDiagonalLongExtraction_correctedLift (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (d : ℕ) (b : Old D Sc cutoff v t) :
    offDiagonalLongExtraction D Sc cutoff p j.1 v t
      (offDiagonalCorrectedLift D Sc cutoff p j v t d b) =
      (offDiagonalCoefficientRho D Sc cutoff p j v t)^[d] (Finsupp.single 0 b) := by
  rw [← offDiagonalLongSection_rho_iterate, offDiagonalLongExtraction_section]

end OddMath.QuiverHecke.ELVOld
