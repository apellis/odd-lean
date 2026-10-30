/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputRhoCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVOldCategory
/-!
# Balanced coefficients and finite output rho

The coefficient and operator comparisons required by `DeformedMackeyBoundary.md`
(2)–(3). On a fixed old-word summand, extraction of an arbitrary balanced old
coefficient is literal old quotient composition. The finite output operator
intertwines corrected rho on every quotient element, and hence preserves the
chronological short kernel. Output-old factors across the bare long chain and
the ordered polynomial S still require separate comparison.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The balanced coefficient acts by chronological old quotient composition.
The whole coefficient, not merely a scalar representative, is retained. -/
theorem outputLongCoordinate_balanced (p : ZMod 2) (i : I) (v : List I) (m : ℕ)
    (h : hom D Sc cutoff (i :: v) (v ++ [i])) (b : Old D Sc cutoff v v) :
    outputLongCoordinate D Sc cutoff p i v m
      (balancedForward D Sc cutoff p i v (v ++ [i]) (balancedTmul D Sc cutoff p i h b)) =
    oldComp D Sc cutoff v v v b
      (outputLongCoordinate D Sc cutoff p i v m (projection D Sc cutoff i v (v ++ [i]) h)) := by
  rw [balancedForward_tmul]
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
  rw [pair_mk]
  change outputLongCoordinate D Sc cutoff p i v m
    (oldSourceTarget D Sc cutoff i v (v ++ [i]) (twist k p r)
      (projection D Sc cutoff i v (v ++ [i]) h)) = _
  rw [outputLongCoordinate_oldSource, twist_twist]
  obtain ⟨a, ha⟩ := (ideal D Sc cutoff v v).mkQ_surjective
    (outputLongCoordinate D Sc cutoff p i v m (projection D Sc cutoff i v (v ++ [i]) h))
  rw [← ha]
  rfl

/-- The finite coefficient operator induced by corrected rho. -/
def outputCoefficientRho (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  (Finsupp.lmapDomain (Old D Sc cutoff v v) k Nat.succ).comp
      (Finsupp.mapRange.linearMap (oldTwist D Sc cutoff (D.parity j.1) v v)) +
    SKM.zsign k (D.parity j.1 * wordSumParity D v) •
      ((2 * (-1 : k) ^ cutoff j.1) •
        Finsupp.mapRange.linearMap
          (oldPrecomp D Sc cutoff v v (twist k p (boundaryDelta D Sc cutoff j v))))

/-- The literal finite output extraction intertwines the two specified operators. -/
theorem outputLongExtraction_boundaryRho (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (z : Target D Sc cutoff j.1 v (v ++ [j.1])) :
    outputLongExtraction D Sc cutoff p j.1 v (boundaryRho D Sc cutoff j v (v ++ [j.1]) z) =
      outputCoefficientRho D Sc cutoff p j v (outputLongExtraction D Sc cutoff p j.1 v z) := by
  ext m
  cases m with
  | zero =>
    rw [outputLongExtraction_apply, outputLongCoordinate_boundaryRho_zero]
    simp only [outputCoefficientRho, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.lmapDomain_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
      outputLongExtraction_apply]
    rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp), zero_add]
  | succ m =>
    rw [outputLongExtraction_apply]
    have hr := outputLongCoordinate_boundaryRho_succ D Sc cutoff p j v m z
    rw [Nat.add_comm 1 m] at hr
    rw [hr]
    simp only [outputCoefficientRho, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.lmapDomain_apply]
    rw [Finsupp.mapDomain_apply_of_injective Nat.succ_injective]
    rfl

/-- Corrected rho preserves exactly the chronological short submodule. -/
theorem boundaryRho_chronologicalShortSpan (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    {z : Target D Sc cutoff j.1 v (v ++ [j.1])}
    (hz : z ∈ chronologicalShortSpan D Sc cutoff j.1 v v) :
    boundaryRho D Sc cutoff j v (v ++ [j.1]) z ∈ chronologicalShortSpan D Sc cutoff j.1 v v := by
  rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff p j.1 v] at hz ⊢
  change outputLongExtraction D Sc cutoff p j.1 v z = 0 at hz
  change outputLongExtraction D Sc cutoff p j.1 v _ = 0
  rw [outputLongExtraction_boundaryRho, hz, map_zero]

end OddMath.QuiverHecke.ELVOld