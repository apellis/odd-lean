/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleAlgebra
import OddMath.SKM.MatchingFamilyChoice
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# The Nondegeneracy Conjecture of BE2 §8

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
the conjecture immediately following Theorem 8.1.

The coefficient algebra is the abstract `SYM`, not its possibly nonfaithful image
`bubbleSpan`. A basis is expressed by unique finite coefficient expansions. The
coordinate map evaluates each coefficient through `betaSYM` in the rightmost
region. Theorem 8.1 supplies surjectivity; injectivity remains a conjecture.

We read the paper's choice of representatives and distinguished points as arbitrary:
`NondegeneracyConjecture` quantifies over every complete unique choice. We do not
assert that the conjecture for a single choice implies it for all choices.
Counts are indexed by strands, avoiding spurious repetitions from unused entries
of a function `ℕ → ℕ`. Representatives must be pairwise inequivalent, unlike the
more general spanning theorem.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation StringDiagrams.Chord

universe u v w

/-- A complete set of reduced representatives with distinguished points and a
serializer for all strand decorations, as chosen before BE2 Theorem 8.1. -/
structure MatchingBasisChoice {I : Type u} (a b : List (Letter I)) where
  members : Set (List (TMove (Letter I)))
  matching : ∀ R ∈ members, IsMatching₂ a b R ∧ StrictReduced₂ a R
  unique : ∀ R ∈ members, ∀ S ∈ members, Iso (pairing₂ a R) (pairing₂ a S) → R = S
  complete : ∀ R, IsMatching₂ a b R → StrictReduced₂ a R →
    ∃ S ∈ members, Iso (pairing₂ a S) (pairing₂ a R)
  points : members → ℕ → ℕ × ℕ
  onStrand : ∀ R j, j ∈ leftEnds₂ a R.val → OnStrand₂ a R.val j (points R j)
  serialize : ∀ R : members, (MatchingStrand a R.val → ℕ) → List (DTMove I)
  decorates : ∀ R c, Decorates₂ a R.val (points R) (strandCounts c) (serialize R c)

namespace MatchingBasisChoice
variable {I : Type u} {a b : List (Letter I)}

/-- Complete unique decorated choices exist for every pair of boundary words.
Thus the universal quantifier in the conjecture is not an empty one. -/
theorem nonempty (a b : List (Letter I)) : Nonempty (MatchingBasisChoice a b) := by
  classical
  obtain ⟨M, hM, hu, hc⟩ := exists_unique_matching_representatives a b
  have hp (R : M) := matching_bounded_points (hM R R.property).1
  choose q hq using hp
  have hd (R : M) (c : MatchingStrand a R.val → ℕ) :=
    exists_decorates₂_of_bounded_points a R.val (q R)
      (fun j hj => (hq R j hj).2) (fun j hj => (hq R j hj).1) c
  choose τ hτ using hd
  exact ⟨⟨M, hM, hu, hc, q, fun R j hj => (hq R j hj).2,
    τ, fun R c => (hτ R c).1⟩⟩

/-- The decorated matching index, with precisely one natural count per strand. -/
abbrev Labels (F : MatchingBasisChoice a b) :=
  Σ R : F.members, MatchingStrand a R.val → ℕ

/-- The unweighted diagram belonging to a labelled representative. -/
def layers (F : MatchingBasisChoice a b) (t : F.Labels) : List (XLayer I) :=
  dLay a (F.serialize t.1 t.2)

/-- Extend a chosen serializer to the ambient arguments used by Theorem 8.1. -/
def ambientSerializer (F : MatchingBasisChoice a b) (R : List (TMove (Letter I)))
    (n : ℕ → ℕ) : List (DTMove I) := by
  classical
  exact if h : R ∈ F.members then F.serialize ⟨R, h⟩ (fun j => n j) else []

/-- Extend distinguished points off the chosen family; these extra values are unused. -/
def ambientPoints (F : MatchingBasisChoice a b) (R : List (TMove (Letter I))) : ℕ → ℕ × ℕ := by
  classical
  exact if h : R ∈ F.members then F.points ⟨R, h⟩ else fun _ => (0, 0)

theorem ambient_decorates (F : MatchingBasisChoice a b) (R) (hR : R ∈ F.members) (n) :
    Decorates₂ a R (F.ambientPoints R) n (F.ambientSerializer R n) := by
  simp only [ambientPoints, ambientSerializer, dite_eq_left hR]
  exact (decorates₂_strandCounts_iff _ n _).mp (F.decorates ⟨R, hR⟩ _)

theorem decoratedFamily_eq (F : MatchingBasisChoice a b) :
    decoratedFamily₂ a F.members F.ambientSerializer = Set.range F.layers := by
  classical
  ext L
  constructor
  · rintro ⟨R, hR, n, rfl⟩
    exact ⟨⟨⟨R, hR⟩, fun j => n j⟩, by simp [layers, ambientSerializer, hR]⟩
  · rintro ⟨⟨R, c⟩, rfl⟩
    refine ⟨R.val, R.property, strandCounts c, ?_⟩
    simp [layers, ambientSerializer, R.property]

variable {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc) (μ : X)

/-- Move a rightmost coefficient past a homogeneous diagram. This only asserts
existence of the new coefficient, not faithfulness of the bubble map. -/
theorem bubble_swap {p : ZMod 2}
    {f : (pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)}
    (hf : f ∈ homPar D Sc μ a b p)
    {β : End ((pres D Sc).obj (ob D μ []))} (hβ : IsBub cs μ β) :
    ∃ γ, IsBub cs μ γ ∧ f ≫ bubAt D Sc μ b β = bubAt D Sc μ a γ ≫ f := by
  induction hβ using Algebra.adjoin_induction with
  | mem β hβ =>
    obtain ⟨i, n, rfl⟩ := hβ
    let q : ZMod 2 := D.parity i * (((n + D.h i μ - 1) + D.h i μ + 1 : ℤ) : ZMod 2)
    have hgen : bubLs cs i μ n ∈ closedPar D Sc μ q :=
      bubL_mem cs i μ (n + D.h i μ - 1)
    refine ⟨zsign k (p * q) • bubLs cs i μ n,
      (isBub_bubLs cs i μ n).smul _, ?_⟩
    rw [map_smul, Linear.smul_comp]
    exact comp_bubAt hf hgen
  | algebraMap r =>
    refine ⟨r • 𝟙 _, IsBub.id.smul r, ?_⟩
    change f ≫ bubAt D Sc μ b (r • 𝟙 _) = _
    simp only [map_smul, bubAt_id, Linear.comp_smul, Linear.smul_comp,
      Category.comp_id, Category.id_comp]
  | add β δ _ _ ihβ ihδ =>
    obtain ⟨γ, hγ, eγ⟩ := ihβ
    obtain ⟨ε, hε, eε⟩ := ihδ
    exact ⟨γ + ε, hγ.add hε, by simp only [map_add, Preadditive.comp_add,
      Preadditive.add_comp, eγ, eε]⟩
  | mul β δ _ _ ihβ ihδ =>
    obtain ⟨γ, hγ, eγ⟩ := ihβ
    obtain ⟨ε, hε, eε⟩ := ihδ
    refine ⟨ε ≫ γ, hε.comp hγ, ?_⟩
    change f ≫ bubAt D Sc μ b (δ ≫ β) = _
    rw [bubAt_comp, bubAt_comp, ← Category.assoc, eε, Category.assoc, eγ,
      Category.assoc]

/-- Right multiplication by an abstract bubble coefficient. The placement is at
the source, so `End`'s convention `x * y = y ≫ x` gives a right action. -/
def rightAction (f : (pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b))
    (p : SYM D k) := bubAt D Sc μ a (betaSYM cs μ p) ≫ f

theorem rightAction_one (f : (pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) :
    rightAction cs μ f 1 = f := by
  simp only [rightAction, map_one]
  rw [show (1 : End _) = 𝟙 _ from rfl, bubAt_id, Category.id_comp]

theorem rightAction_mul (f : (pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b))
    (p q : SYM D k) :
    rightAction cs μ (rightAction cs μ f p) q = rightAction cs μ f (p * q) := by
  simp only [rightAction, map_mul]
  change _ = bubAt D Sc μ a (betaSYM cs μ q ≫ betaSYM cs μ p) ≫ f
  rw [bubAt_comp, Category.assoc]

/-- The coefficient map for one diagram: horizontal composition on the right
with `β_μ(p)`, in the source-placement convention of `rightAction`. -/
def coefficientMap (F : MatchingBasisChoice a b) (t : F.Labels) :
    SYM D k →ₗ[k] ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) where
  toFun p := bubAt D Sc μ a (betaSYM cs μ p) ≫ xev cs μ a b (F.layers t)
  map_add' p q := by simp only [map_add, Preadditive.add_comp]
  map_smul' r p := by simp only [map_smul, Linear.smul_comp, RingHom.id_apply]

/-- The induced map from finite `SYM`-linear combinations of decorated matchings.
Only its underlying `k`-linear map is needed to express unique coefficients. -/
def expansion (F : MatchingBasisChoice a b) :
    (F.Labels →₀ SYM D k) →ₗ[k]
      ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) :=
  Finsupp.lsum k (F.coefficientMap cs μ)

@[simp] theorem expansion_single (F : MatchingBasisChoice a b) (t : F.Labels) (p : SYM D k) :
    F.expansion cs μ (Finsupp.single t p) =
      bubAt D Sc μ a (betaSYM cs μ p) ≫ xev cs μ a b (F.layers t) := by
  exact Finsupp.lsum_single k (F.coefficientMap cs μ) t p

/-- Theorem 8.1, with abstract coefficients: every Hom has a finite expansion. -/
theorem expansion_surjective (F : MatchingBasisChoice a b) :
    Function.Surjective (F.expansion cs μ) := by
  classical
  have hspan : diagBubSpan D Sc cs μ a b (Set.range F.layers) = ⊤ := by
    rw [← F.decoratedFamily_eq]
    exact theorem_8_1 μ a b F.members F.matching F.complete F.ambientPoints
      (fun R hR j hj => by
        simpa only [ambientPoints, dite_eq_left hR] using F.onStrand ⟨R, hR⟩ j hj)
      F.ambientSerializer F.ambient_decorates
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro g ⟨L, ⟨t, rfl⟩, β, hβ, rfl⟩
  obtain ⟨γ, hγ, eγ⟩ := bubble_swap cs μ (xev_mem_homPar cs μ a b (F.layers t)) hβ
  rw [eγ]
  have hγ' : (γ : End _) ∈ (betaSYM cs μ).range := by
    rw [betaSYM_range]
    exact hγ
  obtain ⟨p, rfl⟩ := hγ'
  exact ⟨Finsupp.single t p, F.expansion_single cs μ t p⟩

/-- A morphism below a crossing ceiling has a finite expansion supported on chosen matchings
below the same ceiling. The coefficients lie in the abstract `SYM` and use source placement.
No coefficient uniqueness or matching independence is asserted. -/
theorem exists_expansion_of_mem_ltL (F : MatchingBasisChoice a b) {N : ℕ}
    {f : (pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)}
    (hf : f ∈ LtL D Sc cs μ a b N) :
    ∃ z : F.Labels →₀ SYM D k, F.expansion cs μ z = f ∧
      ∀ t ∈ z.support, ncr₂ t.1.val < N := by
  classical
  let S := Finsupp.supported (SYM D k) k {t : F.Labels | ncr₂ t.1.val < N}
  have hspan : LtL D Sc cs μ a b N ≤ diagBubSpan D Sc cs μ a b
      (decoratedFamily₂ a {R | R ∈ F.members ∧ ncr₂ R < N} F.ambientSerializer) :=
    ltL_le_diagBubSpan_decoratedFamily₂ μ a b F.members
      (fun R hR => ⟨(F.matching R hR).1, (F.matching R hR).2.1⟩)
      (fun s hv hl hs => by
        obtain ⟨R', hR', hred, hiso⟩ := exists_strictReduced_matching hv hl hs
        obtain ⟨R, hRM, hR⟩ := F.complete R' hR' hred
        exact ⟨R, hRM, hR.trans hiso⟩)
      F.ambientPoints
      (fun R hR j hj => by
        simpa only [ambientPoints, dite_eq_left hR] using F.onStrand ⟨R, hR⟩ j hj)
      F.ambientSerializer F.ambient_decorates N
  have hmap : diagBubSpan D Sc cs μ a b
      (decoratedFamily₂ a {R | R ∈ F.members ∧ ncr₂ R < N} F.ambientSerializer) ≤
      S.map (F.expansion cs μ) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨R, ⟨hRM, hRN⟩, n, rfl⟩, β, hβ, rfl⟩
    let t : F.Labels := ⟨⟨R, hRM⟩, fun j => n j⟩
    have heq : dLay a (F.ambientSerializer R n) = F.layers t := by
      simp [t, layers, ambientSerializer, hRM]
    rw [heq]
    obtain ⟨γ, hγ, eγ⟩ := bubble_swap cs μ (xev_mem_homPar cs μ a b (F.layers t)) hβ
    rw [eγ]
    have hγ' : (γ : End _) ∈ (betaSYM cs μ).range := by
      rw [betaSYM_range]
      exact hγ
    obtain ⟨p, rfl⟩ := hγ'
    exact ⟨Finsupp.single t p, Finsupp.single_mem_supported k p hRN,
      F.expansion_single cs μ t p⟩
  obtain ⟨z, hz, heq⟩ := hmap (hspan hf)
  exact ⟨z, heq, fun t ht => (Finsupp.mem_supported k z).1 hz ht⟩

/-- The selected decorated family is a free coefficient basis: every Hom has a
unique finite expansion with coefficients in the abstract all-colour `SYM`.
This is a proposition, not a theorem asserting the conjecture. -/
def IsBasis (F : MatchingBasisChoice a b) : Prop :=
  Function.Bijective (F.expansion cs μ)

/-- **BE2 §8 basis/independence bridge.** The spanning half is Theorem 8.1;
the remaining assertion is injectivity of the induced free coefficient map. -/
theorem isBasis_iff_injective (F : MatchingBasisChoice a b) :
    F.IsBasis cs μ ↔ Function.Injective (F.expansion cs μ) :=
  ⟨fun h => h.1, fun h => ⟨h, F.expansion_surjective cs μ⟩⟩

end MatchingBasisChoice

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- **The Nondegeneracy Conjecture, BE2 §8 after Theorem 8.1.** For every
pair of equal-weight words, every external weight and every complete unique
choice of reduced representatives and distinguished points, the decorated
family has unique finite `SYM` coefficients. The coefficient ring is concentrated
in even parity, as throughout the SKM library. This declaration is only a `Prop`;
it neither assumes nor proves the conjecture. -/
def NondegeneracyConjecture (cs : CScalars Sc) : Prop :=
  ∀ (a b : List (Letter I)), wt D 0 a = wt D 0 b →
    ∀ (μ : X) (F : MatchingBasisChoice a b), F.IsBasis cs μ

/-- The conjecture is equivalent to independence of all its chosen families,
with surjectivity discharged by Theorem 8.1 rather than added as a hypothesis. -/
theorem nondegeneracyConjecture_iff_injective (cs : CScalars Sc) :
    NondegeneracyConjecture cs ↔
      ∀ (a b : List (Letter I)), wt D 0 a = wt D 0 b →
        ∀ (μ : X) (F : MatchingBasisChoice a b), Function.Injective (F.expansion cs μ) := by
  simp only [NondegeneracyConjecture, MatchingBasisChoice.isBasis_iff_injective]

end OddMath.SKM
