/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightTripleDots
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedStoredMixedBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionPairPolynomialMaps

/-! # The ordered correction in the selected OLD weight triple coordinate

Brundan–Ellis (1.9): transport the original-parameter correction in the
three independently prescribed weight dots to the same three evaluated
stored-target dot maps. The acting parameters are parameterTwist Sc.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u v w

private theorem conjugation_polynomial
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (i j : I)
    {V W : C} (e : V = W) (x y z : End W) :
    tripleDotCorrectionPolynomial D Sc (R := End V) i j
      (eqToHom e ≫ x ≫ eqToHom e.symm)
      (eqToHom e ≫ y ≫ eqToHom e.symm)
      (eqToHom e ≫ z ≫ eqToHom e.symm) =
    eqToHom e ≫ tripleDotCorrectionPolynomial D Sc (R := End W) i j x y z ≫ eqToHom e.symm := by
  exact (tripleDotCorrectionPolynomial_map D Sc
    (inductionEndConjugation (eqToIso e)) i j x y z).symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {a b c d : X}
  (hab : a + D.α i = b) (hbc : b + D.α j = c) (hcd : c + D.α i = d)
  (β : WeightBlocks D Λ a)
local notation "Sc'" => parameterTwist D Sc
local notation "δi" => blockSucc D Λ i hab β
local notation "δij" => blockSucc₂ D j i Λ hab hbc β
local notation "ε" => probeOldBlockSucc₃ D i j i Λ hab hbc hcd β
local notation "hI" => probeOldBlockTarget_perm D i Λ hab β δi rfl
local notation "hIJ" => probeOldBlockTarget_perm D j Λ hbc δi δij rfl
local notation "hTopI" => probeOldBlockTarget_perm D i Λ hcd δij ε rfl
local notation "F₀" => probeOldE D Sc' m i Λ hab ≫ probeOldE D Sc' m j Λ hbc ≫ probeOldE D Sc' m i Λ hcd
local notation "eq₃" => probeOldWeightTriple_obj_eq D Sc' m i j i Λ hab hbc hcd β

/-- The correction in the three chosen global dots is the same ordered stored-target polynomial. -/
theorem probeOldWeightTriplePolynomial_component (M : ProbeOldWeightProduct D Sc' m Λ a) :
    tripleDotCorrectionPolynomial D Sc (R := End ((F₀).obj M ε)) i j
      ((probeOldWeightTripleFirstDot D Sc' m i j i Λ hab hbc hcd).total M ε)
      ((probeOldWeightTripleMiddleDot D Sc' m i j i Λ hab hbc hcd).total M ε)
      ((probeOldWeightTripleLastDot D Sc' m i j i Λ hab hbc hcd).total M ε) =
    eqToHom (eq₃ M) ≫ tripleDotCorrectionPolynomial D Sc
      (R := End ((probeOldBlockTripleInd D Sc' m i j i Λ hab hbc hcd β).obj (M β))) i j
      (probeStoredFirstDot D Sc m (Multiset.toList (Subtype.val β)) i j hI hIJ hTopI (M β))
      (probeStoredMiddleDot D Sc m (Multiset.toList (Subtype.val β)) i j hI hIJ hTopI (M β))
      (probeStoredLastDot D Sc m (Multiset.toList (Subtype.val β)) i j hI hIJ hTopI (M β)) ≫ eqToHom (eq₃ M).symm := by
  rw [probeOldWeightTripleFirstDot_component, probeOldWeightTripleMiddleDot_component,
    probeOldWeightTripleLastDot_component]
  exact conjugation_polynomial D Sc i j (eq₃ M) _ _ _

end OddMath.QuiverHecke
