import OddMath.QuiverHecke.Algebra
import OddMath.QuiverHecke.OddNilHecke
import OddMath.SKM.DividedPowerDecomposition
import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Algebra.Module.Projective

/-!
# Odd divided-power projective modules in the locally unital algebra

The underlying projective-module transport for BE2, arXiv:1701.04133v2,
Lemma 11.1. The source is the independent algebra `H_n`, not its image in
SKM. To use Mathlib's unital module API we take principal left ideals in
`Unitization k H_n`; their elements have zero scalar component and identify
with the usual `H_n e`. This convention does not adjoin elements to `H_n e`.

The splitting is transported from the proved odd nilHecke matrix units
through `QuiverHecke.oddNilHecke` and the same-colour corner inclusion.
No injectivity of the nilHecke map is required. Integer and parity grading
transport and the normalized multiplicity are separate obligations; the
underlying projective-module equivalence alone is not full Lemma 11.1.

For even colours, the required interface from categorification-lean is a
unital classical nilHecke algebra map into the same-colour endomorphism
corner, sending polynomial generators to dots and divided differences to
crossings, together with homogeneous splitting elements `a_l`, `b_l`
satisfying `sum a_l*b_l = 1` and `b_l*a_m = delta(l,m)*e`. The projector
must agree with the BE2 longest Demazure convention. The interface must
include the integer degrees and (even) parities of these elements, and
rank-zero and rank-one cases. This note is not an assumed hypothesis.
-/

noncomputable section
open scoped Classical BigOperators
namespace OddMath.QuiverHecke.DividedPowerModules
open OddMath.Frontier Categorification BoxPartitionCount
open OddMath.SKM.DividedPowerDecomposition OddMath.SKM.DividedPowerIdempotents

section General
variable {R A : Type*} [Ring R] [Ring A] {P e : R}
  {J : Type*} [Fintype J] [DecidableEq J]

/-- A splitting transports through a nonunital map; its source idempotent
becomes the image of the old source, not the unit of the target. -/
def mapSplitting (S : Splitting P e J) (f : R →ₙ+* A) :
    Splitting (f P) (f e) J where
  σ j := f (S.σ j)
  lam j := f (S.lam j)
  sum_eq := by simpa only [map_sum, map_mul] using congrArg f S.sum_eq
  orth j l := by
    simpa only [map_mul, apply_ite, map_zero] using congrArg f (S.orth j l)
  mul_sigma j := by simpa only [map_mul] using congrArg f (S.mul_sigma j)
  lam_mul j := by simpa only [map_mul] using congrArg f (S.lam_mul j)

/-- Every principal ideal of an idempotent is projective. -/
theorem projective_leftIdeal (e : R) (he : e * e = e) : Module.Projective R (leftIdeal e) := by
  let p : R →ₗ[R] leftIdeal e :=
    { toFun := fun x => ⟨x * e, by change x * e * e = x * e; rw [mul_assoc, he]⟩
      map_add' := fun x y => Subtype.ext (add_mul x y e)
      map_smul' := fun r x => Subtype.ext (mul_assoc r x e) }
  apply Module.Projective.of_split (leftIdeal e).subtype p
  apply LinearMap.ext
  intro x
  exact Subtype.ext x.property

end General

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- The unital ring used only to encode modules over the locally unital `H_n`. -/
abbrev ModuleRing (r : ℕ) := Unitization k (Hn D Sc r)

/-- Scalar multiplication commutes with the regular action in the module ring. -/
instance moduleRingTower (r : ℕ) :
    IsScalarTower k (ModuleRing D Sc r) (ModuleRing D Sc r) where
  smul_assoc c x y := by
    change (c • x) * y = c • (x * y)
    apply Unitization.ext
    · change (c * x.fst) * y.fst = c * (x.fst * y.fst)
      exact mul_assoc _ _ _
    · change (c * x.fst) • y.snd + y.fst • (c • x.snd) + (c • x.snd) * y.snd =
        c • (x.fst • y.snd + y.fst • x.snd + x.snd * y.snd)
      simp only [smul_add, smul_smul, smul_mul_assoc, mul_comm y.fst c]

/-- The principal projective with its full left `H_n` action. -/
abbrev principal {r : ℕ} (e : Hn D Sc r) :=
  leftIdeal (e : ModuleRing D Sc r)

/-- The ordinary fixed-point model of the principal left ideal in `H_n` itself. -/
def principalInHn {r : ℕ} (e : Hn D Sc r) : Submodule k (Hn D Sc r) where
  carrier := {x | x * e = x}
  zero_mem' := zero_mul e
  add_mem' {x y} hx hy := by
    change (x + y) * e = x + y
    rw [add_mul, hx, hy]
  smul_mem' c x hx := by
    change (c • x) * e = c • x
    rw [smul_mul_assoc, hx]

theorem principal_fst_zero {r : ℕ} {e : Hn D Sc r} (x : principal D Sc e) :
    (x : ModuleRing D Sc r).fst = 0 := by
  have h := congrArg (fun z : ModuleRing D Sc r => z.fst) x.property
  simpa only [Unitization.fst_mul, Unitization.fst_inr, mul_zero] using h.symm

/-- Unitization adds no vectors to the source's principal projective. -/
def principalEquivHn {r : ℕ} (e : Hn D Sc r) :
    (principal D Sc e).restrictScalars k ≃ₗ[k] principalInHn D Sc e where
  toFun x := ⟨(x : ModuleRing D Sc r).snd, by
    change (x : ModuleRing D Sc r).snd * e = (x : ModuleRing D Sc r).snd
    have h := congrArg (fun z : ModuleRing D Sc r => z.snd) x.property
    simpa only [Unitization.snd_mul, Unitization.snd_inr, Unitization.fst_inr,
      principal_fst_zero D Sc x, zero_smul, zero_add] using h⟩
  invFun x := ⟨(x.1 : ModuleRing D Sc r), by
    change (x.1 : ModuleRing D Sc r) * (e : ModuleRing D Sc r) = (x.1 : ModuleRing D Sc r)
    rw [← Unitization.inr_mul, x.property]⟩
  left_inv x := by
    apply Subtype.ext
    apply Unitization.ext
    · exact (principal_fst_zero D Sc x).symm
    · rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Include the same-colour corner into the module ring, preserving its corner unit. -/
def cornerMap (i : I) (r : ℕ) : Corner D Sc i r →ₙ+* ModuleRing D Sc r :=
  ((Unitization.inrNonUnitalAlgHom k (Hn D Sc r)) : Hn D Sc r →ₙ+* ModuleRing D Sc r).comp
    (Hn.sameColourInclusion i r)

@[simp] theorem cornerMap_one (i : I) (r : ℕ) :
    cornerMap D Sc i r 1 =
      (Hn.wordIdempotent (D := D) (Sc := Sc) (repeatedWord i r) : ModuleRing D Sc r) := rfl

/-- The odd nilHecke map followed by inclusion into the full locally unital algebra. -/
def oddMap (i : I) (hi : D.parity i = 1) (n : ℕ) :
    NilHeckeAction.Presented n →ₙ+* ModuleRing D Sc (n + 2) :=
  (cornerMap D Sc i (n + 2)).comp (oddNilHecke D Sc i hi n).toNonUnitalRingHom

/-- All-rank odd divided-power idempotents in the independent corner. -/
def oddCornerProjector (i : I) (hi : D.parity i = 1) : (r : ℕ) → Corner D Sc i r
  | 0 => 1
  | 1 => 1
  | n + 2 => oddNilHecke D Sc i hi n (oppositeProjector n)

theorem oddCornerProjector_idempotent (i : I) (hi : D.parity i = 1) :
    (r : ℕ) → oddCornerProjector D Sc i hi r * oddCornerProjector D Sc i hi r =
      oddCornerProjector D Sc i hi r
  | 0 => one_mul _
  | 1 => one_mul _
  | n + 2 => by
    change oddNilHecke D Sc i hi n _ * oddNilHecke D Sc i hi n _ = _
    rw [← map_mul, oppositeProjector_idempotent]
    rfl

/-- The actual divided-power idempotent of `H_n`. -/
def oddIdempotent (i : I) (hi : D.parity i = 1) (r : ℕ) : Hn D Sc r :=
  Hn.sameColourInclusion i r (oddCornerProjector D Sc i hi r)

theorem oddIdempotent_idempotent (i : I) (hi : D.parity i = 1) (r : ℕ) :
    oddIdempotent D Sc i hi r * oddIdempotent D Sc i hi r = oddIdempotent D Sc i hi r := by
  simp only [oddIdempotent, ← map_mul, oddCornerProjector_idempotent]

/-- The full principal left module `H_n 1_{i^n}`, not just the corner ring. -/
abbrev wordProjective (i : I) (r : ℕ) :=
  principal D Sc (Hn.wordIdempotent (repeatedWord i r))

/-- The unshifted odd divided-power projective; normalization is not implicit. -/
abbrev oddProjective (i : I) (hi : D.parity i = 1) (r : ℕ) :=
  principal D Sc (oddIdempotent D Sc i hi r)

instance wordProjective_projective (i : I) (r : ℕ) :
    Module.Projective (ModuleRing D Sc r) (wordProjective D Sc i r) :=
  projective_leftIdeal _ (by rw [← Unitization.inr_mul, Hn.wordIdempotent_sq])

instance oddProjective_projective (i : I) (hi : D.parity i = 1) (r : ℕ) :
    Module.Projective (ModuleRing D Sc r) (oddProjective D Sc i hi r) :=
  projective_leftIdeal _ (by rw [← Unitization.inr_mul, oddIdempotent_idempotent])

/-- The nonunital corner transport of all the odd splitting identities. -/
def oddSplittingInHn (i : I) (hi : D.parity i = 1) (n : ℕ) :
    Splitting (Hn.wordIdempotent (D := D) (Sc := Sc) (repeatedWord i (n + 2)) :
      ModuleRing D Sc (n + 2)) (oddIdempotent D Sc i hi (n + 2)) (Sq (n + 2)) := by
  have h : oddMap D Sc i hi n 1 =
      (Hn.wordIdempotent (D := D) (Sc := Sc) (repeatedWord i (n + 2)) :
        ModuleRing D Sc (n + 2)) := by
    change cornerMap D Sc i (n + 2) (oddNilHecke D Sc i hi n 1) = _
    rw [map_one, cornerMap_one]
  exact h ▸ mapSplitting (oddSplitting n) (oddMap D Sc i hi n)

/-- The underlying all-rank projective-module decomposition in `H_n`.
The integer/parity shifts still have to be placed on the factors. -/
def oddDecompositionInHn (i : I) (hi : D.parity i = 1) : (r : ℕ) →
    wordProjective D Sc i r ≃ₗ[ModuleRing D Sc r]
      (Sq r → oddProjective D Sc i hi r)
  | 0 => by
    letI := SmallRank.uniqueOfCardOne (Sq 0) (SmallRank.card_Sq_small (by omega))
    exact (LinearEquiv.funUnique (Sq 0) (ModuleRing D Sc 0) _).symm
  | 1 => by
    letI := SmallRank.uniqueOfCardOne (Sq 1) (SmallRank.card_Sq_small (by omega))
    exact (LinearEquiv.funUnique (Sq 1) (ModuleRing D Sc 1) _).symm
  | n + 2 => (oddSplittingInHn D Sc i hi n).equiv

#print axioms oddDecompositionInHn
#print axioms oddProjective_projective

end OddMath.QuiverHecke.DividedPowerModules
