/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.PositiveFormCoefficients
import OddMath.SKM.PositivePointGrading
import OddMath.SKM.BoundedPointSerialization
/-!
# Positive strand-labelled families and the modified form

For Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.3, proof of Claim 1,
index a decoration by a representative and one natural-number label per strand.
The fixed-serializer comparison allows arbitrary valid point placements and serializers.
The bounded-point corollary constructs a serializer from strand membership and bounded
heights. Serializers and ordinary layers are chosen before both sign specializations
and every integer degree. Their finite degree fibers compute the existing modified form.

The comparison reindexes the established canonical family; it does not change
`decoratedFamily₂` or identify different literal layer lists. Serializer existence
is constructed for bounded points, not asserted from `OnStrand₂` alone. The colour
type may be infinite, and bar consistency is not required. Mixed boundaries and
the remaining claims of Theorem 10.3 are not addressed here.
-/

noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators

private theorem layers_injective {I : Type*} :
    Function.Injective (List.map (@ofL I)) := by
  apply List.map_injective_iff.mpr
  rintro ⟨u, s, v⟩ ⟨u', s', v'⟩ h
  cases h
  rfl

private theorem point_weights {I X : Type*} [AddCommGroup X]
    (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    {n : ℕ} (a b : Fin n → I) {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (List.ofFn fun r => (true, a r)) (List.ofFn fun r => (true, b r)) R)
    (hred : StrictReduced₂ (List.ofFn fun r => (true, a r)) R)
    (e : Equiv.Perm (Fin n))
    (he : ∀ r, Same (pairing₂ (List.ofFn fun r => (true, a r)) R)
      (n - 1 - r.val) (n + (e r).val))
    (p : MatchingStrand (List.ofFn fun r => (true, a r)) R ≃ Fin n)
    (hp : ∀ j : MatchingStrand (List.ofFn fun r => (true, a r)) R,
      OnStrand₂ (List.ofFn fun r => (true, a r)) R j.val (R.length, (p j).val))
    (q : ℕ → ℕ × ℕ)
    (hq : ∀ j ∈ leftEnds₂ (List.ofFn fun r => (true, a r)) R,
      OnStrand₂ (List.ofFn fun r => (true, a r)) R j (q j))
    (c : Fin n → ℕ) (ds : List (DTMove I))
    (hds : Decorates₂ (List.ofFn fun r => (true, a r)) R q
      (strandCounts (fun j => c (p j))) ds)
    (L : List (LayerData I))
    (hL : SChain (List.ofFn fun r => (true, a r)) L (List.ofFn fun r => (true, b r)))
    (hm : L.map ofL = dLay (List.ofFn fun r => (true, a r)) ds) :
    Diagram.degree (gdeg D sy) (mkD D μ L hL) =
      (∑ r, ∑ s with r < s ∧ e s < e r, sy.d (a r) * D.d (a r) (a s)) +
      ∑ t, (c t : ℤ) * (2 * sy.d (b t)) ∧
    xpar D μ (dLay (List.ofFn fun r => (true, a r)) ds) =
      (∑ r, ∑ s with r < s ∧ e s < e r, D.parity (a r) * D.parity (a s)) +
      ∑ t, (c t : ZMod 2) * D.parity (b t) := by
  obtain ⟨K, hK, hKm, hd, hp⟩ := positive_point_decorated_degree_parity
    D sy μ a b hR hred e he p hp q hq c ds hds
  have hKL : K = L := layers_injective (hKm.trans hm.symm)
  subst K
  exact ⟨hd, hp⟩

private theorem sum_fiber_transport {T G k : Type*} [AddCommMonoid k]
    (E : T ≃ G) (d : T → ℤ) (d' : G → ℤ) (v : T → k) (v' : G → k)
    (hd : ∀ t, d t = d' (E t)) (hv : ∀ t, v t = v' (E t))
    (z : ℤ) (hg : Set.Finite {g | d' g = z}) :
    ∃ hf : Set.Finite {t | d t = z},
      (∑ t ∈ hf.toFinset, v t) = ∑ g ∈ hg.toFinset, v' g := by
  classical
  have hf : Set.Finite {t | d t = z} := by
    have h := hg.preimage E.injective.injOn
    simpa only [Set.preimage_ofPred_eq, ← hd] using h
  refine ⟨hf, ?_⟩
  apply Finset.sum_bij (fun t _ => E t)
  · intro t ht
    exact hg.mem_toFinset.mpr ((hd t).symm.trans (hf.mem_toFinset.mp ht))
  · intro t _ u _ h
    exact E.injective h
  · intro g hg'
    refine ⟨E.symm g, hf.mem_toFinset.mpr ?_, E.apply_symm_apply g⟩
    change d (E.symm g) = z
    rw [hd, E.apply_symm_apply]
    exact hg.mem_toFinset.mp hg'
  · intro t _
    exact hv t

attribute [local instance] Classical.propDecidable
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (Q : CoveringQuantum.RootDatum I X)
variable (μ : X) {m n : ℕ} (a : Fin m → I) (b : Fin n → I)
local notation "A" => (List.ofFn fun r => (true, a r))
local notation "B" => (List.ofFn fun r => (true, b r))

/-- The finite-strand-labelled positive family computes the Laurent coefficients of
 the existing modified form, at any certified placement and fixed valid serializer.
 Representative coverage and uniqueness are explicit; colours may be infinite
 without bar consistency. The ordinary realizations precede all signs and integer degrees; unequal
 boundary lengths give an empty index. This conditional comparison does not construct
 serializers or identify the full range of the raw natural-number selector API. -/
theorem positive_labelled_family_form_coeff
    (M : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ A B R ∧ StrictReduced₂ A R)
    (hrep : ∀ R', IsMatching₂ A B R' → StrictReduced₂ A R' →
      ∃ R ∈ M, Iso (pairing₂ A R) (pairing₂ A R'))
    (huniq : ∀ R ∈ M, ∀ S ∈ M,
      Iso (pairing₂ A R) (pairing₂ A S) → R = S)
    (q : {R // R ∈ M} → ℕ → ℕ × ℕ)
    (hq : ∀ R j, j ∈ leftEnds₂ A R.val → OnStrand₂ A R.val j (q R j))
    (τ : ∀ R : {R // R ∈ M}, (MatchingStrand A R.val → ℕ) → List (DTMove I))
    (hτ : ∀ R c, Decorates₂ A R.val (q R) (strandCounts c) (τ R c)) :
  let T := Σ R : {R // R ∈ M}, MatchingStrand A R.val → ℕ
  ∃ (L : T → List (LayerData I)) (hL : ∀ t, SChain A (L t) B),
    (∀ t, (L t).map ofL = dLay A (τ t.1 t.2)) ∧
    ∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
      ∃ hf : Set.Finite {t : T |
        Diagram.degree (gdeg Q.toSKM Q.skmSymmetrizer)
          (mkD Q.toSKM μ (L t) (hL t)) = z},
        (∑ t ∈ hf.toFinset, σ ^ (xpar Q.toSKM μ (dLay A (τ t.1 t.2))).val) =
           (CoveringQuantum.signLaurent σ hσ
             (CoveringQuantum.UDot.GenericTensor.sesquilinearForm Q
               (CoveringQuantum.UDot.positiveHalf Q CoveringQuantum.Coefficients.q
                 CoveringQuantum.Coefficients.pi μ
                 (Q.toSerreF CoveringQuantum.Coefficients.q CoveringQuantum.Coefficients.pi
                   (CoveringQuantum.PreF.monomial CoveringQuantum.Coefficients.Ring
                     (List.ofFn a).reverse)))
               (CoveringQuantum.UDot.positiveHalf Q CoveringQuantum.Coefficients.q
                 CoveringQuantum.Coefficients.pi μ
                 (Q.toSerreF CoveringQuantum.Coefficients.q CoveringQuantum.Coefficients.pi
                   (CoveringQuantum.PreF.monomial CoveringQuantum.Coefficients.Ring
                     (List.ofFn b).reverse))))).coeff z := by
  classical
  let T := Σ R : {R // R ∈ M}, MatchingStrand (List.ofFn fun r => (true, a r)) R.val → ℕ
  by_cases hmn : m = n
  · subst m
    obtain ⟨E, hE⟩ := positive_representatives_equiv a b M hM hrep huniq
    have hg (t : T) : ∃ (L : List (LayerData I)) (hL : SChain (List.ofFn fun r => (true, a r)) L
      (List.ofFn fun r => (true, b r))),
        L.map ofL = dLay (List.ofFn fun r => (true, a r)) (τ t.1 t.2) := by
      obtain ⟨p, hp, hpt⟩ := positive_top_points a b (hM t.1 t.1.property).1
      let P := Equiv.ofBijective p hp
      have hd := positive_point_decorated_degree_parity Q.toSKM Q.skmSymmetrizer μ a b
        (hM t.1 t.1.property).1 (hM t.1 t.1.property).2 (E t.1).val (hE t.1)
        P hpt (q t.1) (hq t.1) (fun i => t.2 (P.symm i)) (τ t.1 t.2)
        (by simpa using hτ t.1 t.2)
      obtain ⟨L, hL, hm, -, -⟩ := hd
      exact ⟨L, hL, hm⟩
    choose L hL hm using hg
    refine ⟨L, hL, hm, ?_⟩
    intro σ hσ z
    obtain ⟨p, hp, K, hK, hKm, hc⟩ := positive_decorated_family_form_coeff
      Q μ σ hσ a b M hM hrep huniq
    obtain ⟨F, hF⟩ := positive_topDotMoves_family_equiv a b M hM p
    let J : T ≃ ({R // R ∈ M} × (Fin n → ℕ)) :=
      { toFun := fun t => (t.1, fun i => t.2 ((p t.1).symm i))
        invFun := fun u => ⟨u.1, fun j => u.2 (p u.1 j)⟩
        left_inv := by rintro ⟨R, c⟩; simp
        right_inv := by rintro ⟨R, c⟩; simp }
    let G := J.trans F
    have hw (t : T) :
        Diagram.degree (gdeg Q.toSKM Q.skmSymmetrizer) (mkD Q.toSKM μ (L t) (hL t)) =
          Diagram.degree (gdeg Q.toSKM Q.skmSymmetrizer)
            (mkD Q.toSKM μ (K (G t)) (hK (G t))) ∧
        xpar Q.toSKM μ (dLay (List.ofFn fun r => (true, a r)) (τ t.1 t.2)) =
          xpar Q.toSKM μ (G t).val := by
      let c : Fin n → ℕ := fun i => t.2 ((p t.1).symm i)
      have h₁ := point_weights Q.toSKM Q.skmSymmetrizer μ a b
        (hM t.1 t.1.property).1 (hM t.1 t.1.property).2 (E t.1).val (hE t.1)
        (p t.1) (hp t.1) (q t.1) (hq t.1) c (τ t.1 t.2)
        (by simpa [c] using hτ t.1 t.2) (L t) (hL t) (hm t)
      have hmap : (K (G t)).map ofL = dLay (List.ofFn fun r => (true, a r))
          (topDotMoves (List.ofFn fun r => (true, a r)) t.1.val
            (fun j => (p t.1 j).val) (fun j => c (p t.1 j))) :=
        (hKm (G t)).trans (hF (J t))
      have h₂ := point_weights Q.toSKM Q.skmSymmetrizer μ a b
        (hM t.1 t.1.property).1 (hM t.1 t.1.property).2 (E t.1).val (hE t.1)
        (p t.1) (hp t.1)
        (fun j => (t.1.val.length, strandPosition (fun j => (p t.1 j).val) j))
        (by intro j hj; simpa [strandPosition, hj] using hp t.1 (⟨j, hj⟩ : MatchingStrand
          (List.ofFn fun r => (true, a r)) t.1.val))
        c _ (topDotMoves_decorates (List.ofFn fun r => (true, a r)) t.1.val _ _)
          (K (G t)) (hK (G t)) hmap
      refine ⟨h₁.1.trans h₂.1.symm, ?_⟩
      rw [show (G t).val = _ from hF (J t)]
      exact h₁.2.trans h₂.2.symm
    obtain ⟨hf, hfc⟩ := hc z
    obtain ⟨ht, hs⟩ := sum_fiber_transport G
      (fun t => Diagram.degree (gdeg Q.toSKM Q.skmSymmetrizer) (mkD Q.toSKM μ (L t) (hL t)))
      (fun d => Diagram.degree (gdeg Q.toSKM Q.skmSymmetrizer) (mkD Q.toSKM μ (K d) (hK d)))
      (fun t => σ ^ (xpar Q.toSKM μ (dLay (List.ofFn fun r => (true, a r)) (τ t.1 t.2))).val)
      (fun d => σ ^ (xpar Q.toSKM μ d.val).val)
      (fun t => (hw t).1) (fun t => congrArg (fun v : ZMod 2 => σ ^ v.val) (hw t).2) z hf
    exact ⟨ht, hs.trans hfc⟩
  · have : IsEmpty T := ⟨fun t => hmn ((hM t.1 t.1.property).1.positive_length_eq a b)⟩
    let L : T → List (LayerData I) := isEmptyElim
    let hL : ∀ t, SChain (List.ofFn fun r => (true, a r)) (L t) (List.ofFn fun r => (true, b r)) :=
      isEmptyElim
    refine ⟨L, hL, (fun t => isEmptyElim t), ?_⟩
    intro σ hσ z
    have hf : Set.Finite {t : T | Diagram.degree (gdeg Q.toSKM Q.skmSymmetrizer)
        (mkD Q.toSKM μ (L t) (hL t)) = z} := Set.toFinite _
    refine ⟨hf, ?_⟩
    rw [CoveringQuantum.UDot.GenericTensor.sesquilinearForm_positive_words_eq_zero_of_length_ne
      Q μ a b hmn, map_zero]
    rw [show hf.toFinset = ∅ from Finset.eq_empty_of_forall_notMem (fun t => isEmptyElim t)]
    simp

/-- For the distinguished-point family of BE2, arXiv:1701.04133v2, §8 and
Theorem 10.3, proof of Claim 1, bounded strand points determine a valid serializer
and ordinary realizations before all signs and integer degrees. Their finite degree
fibers compute the modified-form coefficients. Representative coverage and uniqueness
remain explicit, without finite-colour or bar-consistency restrictions; this does not establish the
mixed-boundary claims or a comparison with the full raw selector range. -/
theorem positive_bounded_points_family_form_coeff
    (M : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ A B R ∧ StrictReduced₂ A R)
    (hrep : ∀ R', IsMatching₂ A B R' → StrictReduced₂ A R' →
      ∃ R ∈ M, Iso (pairing₂ A R) (pairing₂ A R'))
    (huniq : ∀ R ∈ M, ∀ S ∈ M,
      Iso (pairing₂ A R) (pairing₂ A S) → R = S)
    (q : {R // R ∈ M} → ℕ → ℕ × ℕ)
    (hq : ∀ R j, j ∈ leftEnds₂ A R.val → OnStrand₂ A R.val j (q R j))
    (hh : ∀ R j, j ∈ leftEnds₂ A R.val → (q R j).1 ≤ R.val.length) :
  ∃ τ : ∀ R : {R // R ∈ M}, (MatchingStrand A R.val → ℕ) → List (DTMove I),
    (∀ R c, Decorates₂ A R.val (q R) (strandCounts c) (τ R c)) ∧
  let T := Σ R : {R // R ∈ M}, MatchingStrand A R.val → ℕ
  ∃ (L : T → List (LayerData I)) (hL : ∀ t, SChain A (L t) B),
    (∀ t, (L t).map ofL = dLay A (τ t.1 t.2)) ∧
    ∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
      ∃ hf : Set.Finite {t : T |
        Diagram.degree (gdeg Q.toSKM Q.skmSymmetrizer)
          (mkD Q.toSKM μ (L t) (hL t)) = z},
        (∑ t ∈ hf.toFinset, σ ^ (xpar Q.toSKM μ (dLay A (τ t.1 t.2))).val) =
           (CoveringQuantum.signLaurent σ hσ
             (CoveringQuantum.UDot.GenericTensor.sesquilinearForm Q
               (CoveringQuantum.UDot.positiveHalf Q CoveringQuantum.Coefficients.q
                 CoveringQuantum.Coefficients.pi μ
                 (Q.toSerreF CoveringQuantum.Coefficients.q CoveringQuantum.Coefficients.pi
                   (CoveringQuantum.PreF.monomial CoveringQuantum.Coefficients.Ring
                     (List.ofFn a).reverse)))
               (CoveringQuantum.UDot.positiveHalf Q CoveringQuantum.Coefficients.q
                 CoveringQuantum.Coefficients.pi μ
                 (Q.toSerreF CoveringQuantum.Coefficients.q CoveringQuantum.Coefficients.pi
                   (CoveringQuantum.PreF.monomial CoveringQuantum.Coefficients.Ring
                     (List.ofFn b).reverse))))).coeff z := by
  classical
  have hs (R : {R // R ∈ M}) (c : MatchingStrand A R.val → ℕ) :
      ∃ ds : List (DTMove I), Decorates₂ A R.val (q R) (strandCounts c) ds := by
    obtain ⟨ds, hd, -⟩ := exists_decorates₂_of_bounded_points A R.val (q R) (hq R) (hh R) c
    exact ⟨ds, hd⟩
  choose τ hτ using hs
  exact ⟨τ, hτ, positive_labelled_family_form_coeff Q μ a b M hM hrep huniq q hq τ hτ⟩

end OddMath.SKM
