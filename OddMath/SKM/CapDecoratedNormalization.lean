/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.CapStrands
import OddMath.SKM.CapNormalization
import OddMath.SKM.MixedFibres

/-! Decorated cap normalization for BE2, arXiv:1701.04133v2,
Theorem 10.3 Claim 5. The cap and surviving dots are separated by the
constructed strand equivalence, with independently chosen valid decorations. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators
variable {I X : Type*} [AddCommGroup X]

/-- Reindex strand contributions into the cap and the shorter matching.
Both colours are proved from the boundary pairings. -/
theorem matchingStrand_cap_sum (a b : List (Letter I)) (ε : Bool) (i : I)
    {R S : List (TMove (Letter I))}
    (hR : IsMatching₂ (a ++ (ε, i) :: (!ε, i) :: b) [] R)
    (hc : Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1))
    (hi : Iso (pairing₂ (a ++ b) S)
      (rmAt (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length))
    (c : MatchingStrand (a ++ (ε, i) :: (!ε, i) :: b) R → ℕ)
    {V : Type*} [AddCommMonoid V] (f : ℕ → I → V) :
    (∑ j, f (c j) (matchingStrandColour _ R j)) =
      f (capLabelEquiv hR.pairing_properties.1 hc hi c).1 i +
        ∑ j, f ((capLabelEquiv hR.pairing_properties.1 hc hi c).2 j)
          (matchingStrandColour (a ++ b) S j) := by
  classical
  rw [← (matchingStrandEquivOfCap hR.pairing_properties.1 hc hi).symm.sum_comp]
  rw [Fintype.sum_sum_type]
  simp only [matchingStrandEquivOfCap, Equiv.coe_fn_symm_mk, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_unique, matchingStrandColour_cap a b ε i hR hc,
    matchingStrandColour_capRemaining, capLabelEquiv_cap, capLabelEquiv_remaining]

/-- Actual decorated degree and parity for either cap orientation.
The cap factor uses the physical suffix weight. Neither point choices nor
serializations need to be related across the cap deletion. -/
theorem cap_normalized_decorated_degree_parity
    (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    (a b : List (Letter I)) (ε : Bool) (i : I)
    {R S : List (TMove (Letter I))}
    (hR : IsMatching₂ (a ++ (ε, i) :: (!ε, i) :: b) [] R)
    (hrR : Reduced₂ (a ++ (ε, i) :: (!ε, i) :: b) R)
    (hS : IsMatching₂ (a ++ b) [] S) (hrS : Reduced₂ (a ++ b) S)
    (hc : Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1))
    (hi : Iso (pairing₂ (a ++ b) S)
      (rmAt (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length))
    (q r : ℕ → ℕ × ℕ)
    (hq : ∀ j ∈ leftEnds₂ (a ++ (ε, i) :: (!ε, i) :: b) R,
      OnStrand₂ (a ++ (ε, i) :: (!ε, i) :: b) R j (q j))
    (hr : ∀ j ∈ leftEnds₂ (a ++ b) S, OnStrand₂ (a ++ b) S j (r j))
    (c : MatchingStrand (a ++ (ε, i) :: (!ε, i) :: b) R → ℕ)
    (ds es : List (DTMove I))
    (hd : Decorates₂ (a ++ (ε, i) :: (!ε, i) :: b) R q (strandCounts c) ds)
    (he : Decorates₂ (a ++ b) S r
      (strandCounts (capLabelEquiv hR.pairing_properties.1 hc hi c).2) es) :
    tableDegree D sy μ (dLay (a ++ (ε, i) :: (!ε, i) :: b) ds) =
      tableDegree D sy μ (dLay (a ++ b) es) +
        sy.d i * (1 + if !ε then D.h i (wt D μ b) else -D.h i (wt D μ b)) +
        2 * sy.d i * (capLabelEquiv hR.pairing_properties.1 hc hi c).1 ∧
    xpar D μ (dLay (a ++ (ε, i) :: (!ε, i) :: b) ds) =
      xpar D μ (dLay (a ++ b) es) + cupPar D (wt D μ b) (!ε, i) +
        (capLabelEquiv hR.pairing_properties.1 hc hi c).1 * D.parity i := by
  obtain ⟨hdR, hpR⟩ := mixed_decorated_degree_parity D sy μ hR q hq c ds hd
  obtain ⟨hdS, hpS⟩ := mixed_decorated_degree_parity D sy μ hS r hr _ es he
  obtain ⟨hb, hp⟩ := reduced₂_cap_degree_parity D sy μ a b ε i hR hrR hS hrS hc hi
  rw [matchingStrand_cap_sum a b ε i hR hc hi c (fun n j => (n : ℤ) * (2 * sy.d j))] at hdR
  rw [matchingStrand_cap_sum a b ε i hR hc hi c (fun n j => (n : ZMod 2) * D.parity j)] at hpR
  constructor
  · rw [hdR, hdS, hb]
    ring
  · rw [hpR, hpS, hp]
    abel

section Family
variable {a b : List (Letter I)} {ε : Bool} {i : I}
variable {M N : Set (List (TMove (Letter I)))}
variable (hM : ∀ R ∈ M, IsMatching₂ (a ++ (ε, i) :: (!ε, i) :: b) [] R ∧
  StrictReduced₂ (a ++ (ε, i) :: (!ε, i) :: b) R)
variable (hN : ∀ S ∈ N, IsMatching₂ (a ++ b) [] S ∧ StrictReduced₂ (a ++ b) S)
variable (q : {R : List (TMove (Letter I)) | R ∈ M ∧
  Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)} → ℕ → ℕ × ℕ)
variable (r : N → ℕ → ℕ × ℕ)
variable (hq : ∀ R j, j ∈ leftEnds₂ (a ++ (ε, i) :: (!ε, i) :: b) R.val →
  OnStrand₂ (a ++ (ε, i) :: (!ε, i) :: b) R.val j (q R j))
variable (hr : ∀ S j, j ∈ leftEnds₂ (a ++ b) S.val → OnStrand₂ (a ++ b) S.val j (r S j))
variable (τ : ∀ R : ({R : List (TMove (Letter I)) | R ∈ M ∧
      Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)}), (MatchingStrand (a
        ++ (ε, i) :: (!ε, i) :: b) R.val → ℕ) → List (DTMove I))
variable (υ : ∀ S : N, (MatchingStrand (a ++ b) S.val → ℕ) → List (DTMove I))
variable (hτ : ∀ R c, Decorates₂ (a ++ (ε, i) :: (!ε, i) :: b) R.val (q R) (strandCounts c) (τ R
  c))
variable (hυ : ∀ S c, Decorates₂ (a ++ b) S.val (r S) (strandCounts c) (υ S c))

include hM hN hq hr hτ hυ

/-- Complete unique strict families and independent valid serializers give a
cap-count/shorter-family equivalence before choosing any grading. Its restriction
is an equivalence of finite integer-degree fibers, with the cap parity recorded.
This is not a coefficient or series identity. -/
theorem cap_labelled_family_degree_fibres
    (hMrep : ∀ R, IsMatching₂ (a ++ (ε, i) :: (!ε, i) :: b) [] R → StrictReduced₂ (a ++ (ε, i) ::
      (!ε, i) :: b) R →
      ∃ S ∈ M, Iso (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) S) (pairing₂ (a ++ (ε, i) :: (!ε, i) ::
        b) R))
    (hNrep : ∀ R, IsMatching₂ (a ++ b) [] R → StrictReduced₂ (a ++ b) R →
      ∃ S ∈ N, Iso (pairing₂ (a ++ b) S) (pairing₂ (a ++ b) R))
    (hMuniq : ∀ R ∈ M, ∀ S ∈ M, Iso (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) (pairing₂ (a ++ (ε,
      i) :: (!ε, i) :: b) S) → R = S)
    (hNuniq : ∀ R ∈ N, ∀ S ∈ N,
      Iso (pairing₂ (a ++ b) R) (pairing₂ (a ++ b) S) → R = S) :
    ∃ F : (Σ R : ({R : List (TMove (Letter I)) | R ∈ M ∧
      Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)}), MatchingStrand (a
        ++ (ε, i) :: (!ε, i) :: b) R.val → ℕ) ≃ ℕ × (Σ S : N, MatchingStrand (a ++ b) S.val → ℕ),
      (∀ t, (F t).1 =
        t.2 (capStrand (hM t.1 t.1.property.1).1.pairing_properties.1 t.1.property.2)) ∧
      ∀ (D : Datum I X) (sy : Symmetrizer D) (μ : X),
      let d := fun t : (Σ R : ({R : List (TMove (Letter I)) | R ∈ M ∧
      Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)}), MatchingStrand (a
        ++ (ε, i) :: (!ε, i) :: b) R.val → ℕ) => tableDegree D sy μ (dLay (a ++ (ε, i) :: (!ε, i)
        :: b) (τ t.1 t.2))
      let e := fun u : (Σ S : N, MatchingStrand (a ++ b) S.val → ℕ) => tableDegree D sy μ (dLay (a
        ++ b) (υ u.1 u.2))
      let p := fun t : (Σ R : ({R : List (TMove (Letter I)) | R ∈ M ∧
      Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)}), MatchingStrand (a
        ++ (ε, i) :: (!ε, i) :: b) R.val → ℕ) => xpar D μ (dLay (a ++ (ε, i) :: (!ε, i) :: b) (τ
        t.1 t.2))
      let p' := fun u : (Σ S : N, MatchingStrand (a ++ b) S.val → ℕ) => xpar D μ (dLay (a ++ b) (υ
        u.1 u.2))
      let δ := sy.d i * (1 + if !ε then D.h i (wt D μ b) else -D.h i (wt D μ b))
      (∀ t, d t = e (F t).2 + δ + 2 * sy.d i * (F t).1 ∧
        p t = p' (F t).2 + cupPar D (wt D μ b) (!ε, i) + (F t).1 * D.parity i) ∧
      ∀ z : ℤ, Set.Finite {t | d t = z} ∧
        Set.Finite {u : ℕ × (Σ S : N, MatchingStrand (a ++ b) S.val → ℕ) | e u.2 + δ + 2 * sy.d i *
          u.1 = z} ∧
        ∃ G : {t // d t = z} ≃
          {u : ℕ × (Σ S : N, MatchingStrand (a ++ b) S.val → ℕ) //
            e u.2 + δ + 2 * sy.d i * u.1 = z},
          ∀ t, (G t).val = F t.val := by
  obtain ⟨E, hE, _⟩ := cap_representatives_equiv a b ε i M N hM hN hMrep hNrep hMuniq hNuniq
  let F := capFamilyLabelEquiv (fun R h => (hM R h).1) E hE
  refine ⟨F, fun _ => rfl, ?_⟩
  intro D sy μ
  dsimp only
  have h (t : (Σ R : ({R : List (TMove (Letter I)) | R ∈ M ∧
      Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)}), MatchingStrand (a
        ++ (ε, i) :: (!ε, i) :: b) R.val → ℕ)) := cap_normalized_decorated_degree_parity D sy μ a b
        ε i
    (hM t.1 t.1.property.1).1 (hM t.1 t.1.property.1).2.1
    (hN (E t.1) (E t.1).property).1 (hN (E t.1) (E t.1).property).2.1
    t.1.property.2 (hE t.1) (q t.1) (r (E t.1)) (hq t.1) (hr (E t.1))
    t.2 _ _ (hτ _ _) (hυ _ _)
  refine ⟨h, ?_⟩
  intro z
  have hf := mixed_labelled_degree_finite D sy μ (a ++ (ε, i) :: (!ε, i) :: b) [] ({R : List (TMove
    (Letter I)) | R ∈ M ∧
      Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)})
    (fun R h => (hM R h.1).1)
    (fun R hR S hS hi => hMuniq R hR.1 S hS.1 hi) q hq τ hτ z
  let G := F.subtypeEquiv (p := fun t => tableDegree D sy μ (dLay (a ++ (ε, i) :: (!ε, i) :: b) (τ
    t.1 t.2)) = z)
    (q := fun u => tableDegree D sy μ (dLay (a ++ b) (υ u.2.1 u.2.2)) +
      sy.d i * (1 + if !ε then D.h i (wt D μ b) else -D.h i (wt D μ b)) +
      2 * sy.d i * u.1 = z) (fun t => by rw [(h t).1]; rfl)
  have hg : Set.Finite {u : ℕ × (Σ S : N, MatchingStrand (a ++ b) S.val → ℕ) |
      tableDegree D sy μ (dLay (a ++ b) (υ u.2.1 u.2.2)) +
        sy.d i * (1 + if !ε then D.h i (wt D μ b) else -D.h i (wt D μ b)) +
        2 * sy.d i * u.1 = z} := by
    exact Set.finite_coe_iff.mp (Finite.of_equiv (h := hf.to_subtype) _ G)
  exact ⟨hf, hg, G, fun _ => rfl⟩

end Family
end OddMath.SKM
