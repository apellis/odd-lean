import OddMath.QuiverHecke.DividedPowerModules
import OddMath.QuiverHecke.OddNilHeckeGrading

/-!
# Bidegrees of odd divided-power projectives

BE2, arXiv:1701.04133v2, Lemma 11.1. The integer and parity degrees
are transported to the independent multicolour algebra, without assuming
bar-consistency or injectivity into the weight-labelled category.
-/
noncomputable section
namespace OddMath.QuiverHecke.DividedPowerModules
open CategoryTheory StringDiagrams
open OddMath.Frontier BoxPartitionCount NilHeckeAction
open OddMath.SKM.DividedPowerDecomposition OddMath.SKM.DividedPowerIdempotents
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
variable {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)
variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The odd nilHecke map into `H_n` preserves the two independent degrees. -/
theorem oddNilHecke_mem_bidegree (i : I) (hi : D.parity i = 1)
    {n : ℕ} {d : ℤ} {x : Presented n} (hx : x ∈ EQOnhDG.grading n d) :
    Hn.sameColourInclusion i (n + 2) (oddNilHecke D Sc i hi n x) ∈
      Hn.bidegree D Sc sy hc (n + 2) (2 * sy.d i * d, (d : ZMod 2)) :=
  Hn.single_mem_bidegree D Sc sy hc _ _ _
    (oddNilHecke_mem_integerDegree D Sc sy i hi hx)
    (oddNilHecke_mem_parity D Sc i hi hx)

/-- The all-rank corrected projector in `H_n` is even and has degree zero. -/
theorem oddIdempotent_mem_bidegree (i : I) (hi : D.parity i = 1) (r : ℕ) :
    oddIdempotent D Sc i hi r ∈ Hn.bidegree D Sc sy hc r (0, 0) := by
  match r with
  | 0 => exact Hn.wordIdempotent_mem_bidegree D Sc sy hc _
  | 1 => exact Hn.wordIdempotent_mem_bidegree D Sc sy hc _
  | n + 2 =>
    simpa [oddIdempotent, oddCornerProjector] using
      oddNilHecke_mem_bidegree D Sc sy hc i hi (oppositeProjector_degree n)

/-- The inclusion splitter has the degree prescribed by the reflected EKL basis. -/
theorem sigmaInHn_mem_bidegree (i : I) (hi : D.parity i = 1)
    (n : ℕ) (ℓ : Sq (n + 2)) :
    Hn.sameColourInclusion i (n + 2)
        (oddNilHecke D Sc i hi n ((oddSplitting n).σ ℓ)) ∈
      Hn.bidegree D Sc sy hc (n + 2)
        (2 * sy.d i * shift n ℓ, (shift n ℓ : ZMod 2)) :=
  oddNilHecke_mem_bidegree D Sc sy hc i hi (sigma_degree n ℓ)

/-- The projection splitter has the opposite integer and parity degrees. -/
theorem lamInHn_mem_bidegree (i : I) (hi : D.parity i = 1)
    (n : ℕ) (ℓ : Sq (n + 2)) :
    Hn.sameColourInclusion i (n + 2)
        (oddNilHecke D Sc i hi n ((oddSplitting n).lam ℓ)) ∈
      Hn.bidegree D Sc sy hc (n + 2)
        (2 * sy.d i * (-shift n ℓ), ((-shift n ℓ : ℤ) : ZMod 2)) :=
  oddNilHecke_mem_bidegree D Sc sy hc i hi (lam_degree n ℓ)

#print axioms oddIdempotent_mem_bidegree
#print axioms sigmaInHn_mem_bidegree
#print axioms lamInHn_mem_bidegree
end OddMath.QuiverHecke.DividedPowerModules
