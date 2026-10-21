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

private theorem splitting_cast_sigma {R : Type*} [Ring R] {J : Type*}
    [Fintype J] [DecidableEq J] {P P' e : R} (h : P = P')
    (S : Categorification.Splitting P e J) : (h ▸ S).σ = S.σ := by
  cases h
  rfl

private theorem splitting_cast_lam {R : Type*} [Ring R] {J : Type*}
    [Fintype J] [DecidableEq J] {P P' e : R} (h : P = P')
    (S : Categorification.Splitting P e J) : (h ▸ S).lam = S.lam := by
  cases h
  rfl

private theorem oddSplittingInHn_sigma (i : I) (hi : D.parity i = 1)
    (n : ℕ) (ℓ : Sq (n + 2)) :
    (oddSplittingInHn D Sc i hi n).σ ℓ =
      (Hn.sameColourInclusion i (n + 2)
        (oddNilHecke D Sc i hi n ((oddSplitting n).σ ℓ)) : ModuleRing D Sc (n + 2)) := by
  unfold oddSplittingInHn
  rw [splitting_cast_sigma]
  rfl

private theorem oddSplittingInHn_lam (i : I) (hi : D.parity i = 1)
    (n : ℕ) (ℓ : Sq (n + 2)) :
    (oddSplittingInHn D Sc i hi n).lam ℓ =
      (Hn.sameColourInclusion i (n + 2)
        (oddNilHecke D Sc i hi n ((oddSplitting n).lam ℓ)) : ModuleRing D Sc (n + 2)) := by
  unfold oddSplittingInHn
  rw [splitting_cast_lam]
  rfl

/-- Bidegree of a principal-module vector, measured in `H_n` itself. -/
def PrincipalDegree {r : ℕ} {e : Hn D Sc r} (d : ℤ × ZMod 2)
    (x : principal D Sc e) : Prop :=
  (x : ModuleRing D Sc r).snd ∈ Hn.bidegree D Sc sy hc r d

/-- Both components of the unnormalized splitting shift. -/
def splitterDegree (i : I) (n : ℕ) (ℓ : Sq (n + 2)) : ℤ × ZMod 2 :=
  (2 * sy.d i * shift n ℓ, (shift n ℓ : ZMod 2))

/-- The forward equivalence preserves integer degree and parity after shifting each factor. -/
theorem oddDecompositionInHn_degree (i : I) (hi : D.parity i = 1)
    {n : ℕ} {d : ℤ × ZMod 2} (x : wordProjective D Sc i (n + 2))
    (hx : PrincipalDegree D Sc sy hc d x) (ℓ : Sq (n + 2)) :
    PrincipalDegree D Sc sy hc (d + splitterDegree D sy i n ℓ)
      (oddDecompositionInHn D Sc i hi (n + 2) x ℓ) := by
  have h := Hn.mul_mem_bidegree D Sc sy hc hx
    (sigmaInHn_mem_bidegree D Sc sy hc i hi n ℓ)
  change ((x : ModuleRing D Sc (n + 2)) * (oddSplittingInHn D Sc i hi n).σ ℓ).snd ∈ _
  rw [oddSplittingInHn_sigma, Unitization.snd_mul, Unitization.fst_inr,
    Unitization.snd_inr, principal_fst_zero D Sc x, zero_smul, zero_smul, zero_add, zero_add]
  exact h

private theorem moduleRing_snd_sum {r : ℕ} {J : Type*} [Fintype J]
    (f : J → ModuleRing D Sc r) : (∑ j, f j).snd = ∑ j, (f j).snd :=
  map_sum (Unitization.sndHom k k (Hn D Sc r)) f Finset.univ

/-- The inverse equivalence adds homogeneous tuples in the original degree. -/
theorem oddDecompositionInHn_symm_degree (i : I) (hi : D.parity i = 1)
    {n : ℕ} {d : ℤ × ZMod 2}
    (y : Sq (n + 2) → oddProjective D Sc i hi (n + 2))
    (hy : ∀ ℓ, PrincipalDegree D Sc sy hc (d + splitterDegree D sy i n ℓ) (y ℓ)) :
    PrincipalDegree D Sc sy hc d ((oddDecompositionInHn D Sc i hi (n + 2)).symm y) := by
  have h : (∑ ℓ, (y ℓ : ModuleRing D Sc (n + 2)).snd *
      Hn.sameColourInclusion i (n + 2)
        (oddNilHecke D Sc i hi n ((oddSplitting n).lam ℓ))) ∈
      Hn.bidegree D Sc sy hc (n + 2) d := by
    apply Submodule.sum_mem
    intro ℓ _
    have h := Hn.mul_mem_bidegree D Sc sy hc (hy ℓ)
      (lamInHn_mem_bidegree D Sc sy hc i hi n ℓ)
    have he : (d + splitterDegree D sy i n ℓ) +
        (2 * sy.d i * (-shift n ℓ), ((-shift n ℓ : ℤ) : ZMod 2)) = d := by
      apply Prod.ext <;> simp only [splitterDegree, Prod.fst_add, Prod.snd_add,
        mul_neg, Int.cast_neg, add_neg_cancel_right]
    exact he ▸ h
  change (∑ ℓ, (y ℓ : ModuleRing D Sc (n + 2)) *
    (oddSplittingInHn D Sc i hi n).lam ℓ).snd ∈ _
  rw [moduleRing_snd_sum]
  simpa only [oddSplittingInHn_lam, Unitization.snd_mul, Unitization.fst_inr,
    Unitization.snd_inr, principal_fst_zero D Sc, zero_smul, zero_add] using h

#print axioms oddIdempotent_mem_bidegree
#print axioms sigmaInHn_mem_bidegree
#print axioms lamInHn_mem_bidegree
end OddMath.QuiverHecke.DividedPowerModules
