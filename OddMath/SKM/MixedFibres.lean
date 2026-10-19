import OddMath.SKM.MixedDotGrading
import OddMath.SKM.BoundedPointSerialization

/-!
# Finite degree fibers of mixed strand-labelled matchings

Supporting BE2, arXiv:1701.04133v2, §8 and the degree series of Theorem 10.3.
Fixed endpoint letters and the existing `Chord.matchingOf` classification make
any geometrically unique representative family finite, even for infinitely many
colours. The established mixed dot grading then bounds each natural strand label.
No enumeration, coefficient identity, or pre-assumed finiteness enters the proof.
-/

noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators

/-- Uniqueness up to the endpoint pairing makes a family finite. Neither reducedness,
coverage, nor finiteness of the colour type is needed. -/
theorem matching_representatives_finite {I : Type*} (a b : List (Letter I))
    (M : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ a b R)
    (huniq : ∀ R ∈ M, ∀ S ∈ M, Iso (pairing₂ a R) (pairing₂ a S) → R = S) :
    M.Finite := by
  classical
  have hv (R : M) := (hM R R.property).pairing_properties.1
  have hl (R : M) := (hM R R.property).pairing_properties.2.2
  have hn (R : M) : (pairing₂ a R).length = a.length + b.length := by
    have h := congrArg List.length (hl R)
    simpa only [List.length_map, List.length_append, length_dualW] using h
  let f : M → Equiv.Perm (Fin (a.length + b.length)) := fun R => matchingOf (hv R) (hn R)
  have hf : Function.Injective f := by
    intro R S he
    apply Subtype.ext
    apply huniq R R.property S S.property
    apply (iso_iff (hv R) (hn R) (hv S) (hn S)).2
    refine ⟨he, ?_⟩
    apply List.ofFn_injective
    rw [← map_snd_eq_ofFn_lettersOf, ← map_snd_eq_ofFn_lettersOf, hl R, hl S]
  let : Finite M := Finite.of_injective f hf
  exact Set.finite_coe_iff.mp inferInstance

/-- A finite vector of natural labels with strictly positive integral weights has
finite fibers, including when its indexing type is empty. -/
theorem finite_positive_weight_fiber {J : Type*} [Fintype J]
    (w : J → ℤ) (hw : ∀ j, 0 < w j) (z : ℤ) :
    Set.Finite {c : J → ℕ | ∑ j, (c j : ℤ) * w j = z} := by
  classical
  apply (Set.Finite.pi (fun _ : J => Set.finite_Iic z.toNat)).subset
  intro c hc j _
  change c j ≤ z.toNat
  have hs : (c j : ℤ) * w j ≤ ∑ k, (c k : ℤ) * w k :=
    Finset.single_le_sum (fun k _ => mul_nonneg (Nat.cast_nonneg _) (le_of_lt (hw k)))
      (Finset.mem_univ j)
  have hb : (c j : ℤ) ≤ (c j : ℤ) * w j := by
    have hj := hw j
    nlinarith [show (0 : ℤ) ≤ c j from Nat.cast_nonneg _]
  have hz : (c j : ℤ) ≤ z := hb.trans (hs.trans_eq hc)
  omega

/-- The fixed-serializer mixed strand-labelled degree fiber is finite. The degree
is the existing generator table, not an assumed enumeration or coefficient formula.
Matching and geometric uniqueness suffice; there is no coverage, reducedness,
finite-colour, root-separation, or bar-consistency premise. -/
theorem mixed_labelled_degree_finite {I X : Type*} [AddCommGroup X]
    (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    (a b : List (Letter I)) (M : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ a b R)
    (huniq : ∀ R ∈ M, ∀ S ∈ M, Iso (pairing₂ a R) (pairing₂ a S) → R = S)
    (q : {R // R ∈ M} → ℕ → ℕ × ℕ)
    (hq : ∀ R j, j ∈ leftEnds₂ a R.val → OnStrand₂ a R.val j (q R j))
    (τ : ∀ R : {R // R ∈ M}, (MatchingStrand a R.val → ℕ) → List (DTMove I))
    (hτ : ∀ R c, Decorates₂ a R.val (q R) (strandCounts c) (τ R c)) (z : ℤ) :
    Set.Finite {t : Σ R : {R // R ∈ M}, MatchingStrand a R.val → ℕ |
      tableDegree D sy μ (dLay a (τ t.1 t.2)) = z} := by
  classical
  let : Finite M := (matching_representatives_finite a b M hM huniq).to_subtype
  have hf (R : M) : Set.Finite {c : MatchingStrand a R.val → ℕ |
      ∑ j, (c j : ℤ) * (2 * sy.d (matchingStrandColour a R.val j)) =
        z - tableDegree D sy μ (tLay a R.val)} :=
    finite_positive_weight_fiber _ (fun j => mul_pos (by omega) (sy.pos _)) _
  apply (Set.finite_univ.sigma (fun R _ => hf R)).subset
  intro t ht
  refine ⟨Set.mem_univ _, ?_⟩
  have hd := (mixed_decorated_degree_parity D sy μ (hM t.1 t.1.property)
    (q t.1) (hq t.1) t.2 (τ t.1 t.2) (hτ t.1 t.2)).1
  change tableDegree D sy μ (dLay a (τ t.1 t.2)) = z at ht
  change _ = z - tableDegree D sy μ (tLay a t.1.val)
  omega

end OddMath.SKM
