import OddMath.QuiverHecke.CyclotomicAction.ELVProbeSourcePolynomialUnits
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeDenominatorUnits
import OddMath.QuiverHecke.SwappedAssembly.Sigma.Permutation
import OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirProbeEntry
import OddMath.QuiverHecke.SwappedAssembly.Sigma.DistinctPureEntries
import OddMath.QuiverHecke.SwappedAssembly.Sigma.DistinctPureReservoirEntry
import OddMath.SKM.RouquierCanonicalDistinctLeftMate

/-! # The distinct-colour permutation for the ELV probe pair

Brundan–Ellis Definition 1.5, (1.11): distinct colours have unique
summand paths at fixed endpoints. The mixed entries are invertible from
the constructed source polynomial units and the inverse interchange mate.
The canonical factor left-mate theorem supplies the pure probe input.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.CyclotomicAction
open ELVOld SwappedAssembly
universe u
local instance sigmaPermutationHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
variable [Finite I] (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound)
local notation "c" => elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR
    hdot
attribute [local irreducible] elvProbeReservoir ProbeReservoir.sigmaEntry

/-- Intermediate distinct-colour permutation assembly with the two pure
factor-mate inputs explicit. The mixed entries require no extra hypothesis. -/
theorem elvProbeSigmaPermutation_of_pureEntries
    (hpure : ∀ (i j : I), i ≠ j → ∀ (ν : X) (t s : Sector I)
      (p : SPath (wd D ν [up j, dn i]) t s) (q : SPath (wd D ν [dn i, up j]) t s)
      (side : Bool), p.sides = [side, side] → q.sides = [side, side] →
      ∀ Z : (P).H s, IsIso ((P).sigmaEntry c i j ν p q Z))
    (i j : I) (ν : X) (hij : i ≠ j) : (P).SigmaPermutation c i j ν := by
  apply (P).sigmaPermutation_of_isIso hij ν
  intro t s p q Z
  obtain ⟨a, b, hv₁, hv₂, ep, rfl⟩ := SPath.exists_eq_two p
  obtain ⟨a', b', hw₁, hw₂, eq, rfl⟩ := SPath.exists_eq_two q
  obtain ⟨hk₁, hk₂, he⟩ := SPath.exchange_upDn hij a b hv₁ hv₂
  obtain ⟨ha, hb⟩ := SPath.sides_eq_dnUp hij a' b' b a hw₁ hw₂ hk₁ hk₂
    (eq.trans (ep.symm.trans he.symm))
  subst ha hb
  cases a' <;> cases b'
  · exact hpure i j hij ν t s _ _ false (SPath.sides_two ..) (SPath.sides_two ..) Z
  · subst ep
    exact elvProbe_distinct_sigmaEntry_isIso D Sc m cutoff bound ΛP ΛR hP hR
      hdot c hij ν t _ Z
  · exact (P).isIso_sigmaEntry_reservoir_probe c hij ν _ _
      (SPath.sides_two ..) (SPath.sides_two ..) Z
  · exact hpure i j hij ν t s _ _ true (SPath.sides_two ..) (SPath.sides_two ..) Z


/-- Intermediate factor assembly. The reservoir and both mixed entries are
constructed; only the canonical probe left-mate input remains explicit. -/
theorem elvProbeSigmaPermutation_of_leftMateInvertible
    (hL : LeftMateInvertible (P).T (P).T.leftAdjoints)
    (i j : I) (ν : X) (hij : i ≠ j) : (P).SigmaPermutation c i j ν := by
  apply elvProbeSigmaPermutation_of_pureEntries D Sc m cutoff bound ΛP ΛR hP hR hdot
    (i := i) (j := j) (ν := ν) (hij := hij)
  intro a b hab μ t s p q side hp hq Z
  cases side with
  | false => exact (P).isIso_sigmaEntry_pure_reservoir c hab μ p q hp hq Z
  | true => exact (P).isIso_sigmaEntry_pure_probe hL c hab μ p q hp hq Z

/-- The prescribed ELV probe and reservoir have invertible distinct-colour
sideways crossings, with every factor input constructed from their relations. -/
theorem elvProbeSigmaPermutation (i j : I) (ν : X) (hij : i ≠ j) :
    (P).SigmaPermutation c i j ν := by
  refine elvProbeSigmaPermutation_of_leftMateInvertible D Sc m cutoff bound
    ΛP ΛR hP hR hdot ?_ i j ν hij
  with_unfolding_all
    change LeftMateInvertible (probeOldRouquierFamily D (parameterTwist D Sc) m ΛP hP)
      (probeOldRouquierFamily D (parameterTwist D Sc) m ΛP hP).leftAdjoints
  exact RouquierFamily.canonicalLeftMateInvertible _
    (probeOldRouquierMulticolour D Sc m ΛP hP)

end OddMath.QuiverHecke.CyclotomicAction
