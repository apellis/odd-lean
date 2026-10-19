/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.BoundaryExchange

/-! Non-cap decorated matching coefficients in Brundan–Ellis,
arXiv:1701.04133v2, Theorem 10.3 Claim 5. The complete representative
correspondence is restricted before strand labels or gradings are introduced.
The two non-cap classes are exchanged; the cap class is not included. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators
variable {I : Type*}

/-- The union of the two distinct-strand classes, excluding the cap class. -/
def noncapFamily (A : List (Letter I)) (p : ℕ)
    (M : Set (List (TMove (Letter I)))) : Set (List (TMove (Letter I))) :=
  {R | R ∈ M ∧ ¬ Same (pairing₂ A R) p (p + 1)}

/-- The distinguished endpoints are in the matching boundary. -/
theorem boundary_pairing_bound (a b : List (Letter I)) (x y : Letter I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (a ++ x :: y :: b) [] R) :
    b.length + 1 < (pairing₂ (a ++ x :: y :: b) R).length := by
  have h := congrArg List.length hR.pairing_properties.2.2
  simp only [List.length_map, List.length_append, length_dualW,
    List.length_cons, List.length_nil] at h
  omega

/-- Same-strand membership is preserved by the representative exchange. -/
theorem boundary_swap_same_iff {A B : List (Letter I)}
    {R S : List (TMove (Letter I))} {p : ℕ}
    (hp : p + 1 < (pairing₂ A R).length)
    (hi : Iso (pairing₂ B S) (swapAt (pairing₂ A R) p)) :
    Same (pairing₂ B S) p (p + 1) ↔ Same (pairing₂ A R) p (p + 1) := by
  rw [hi.2, same_swapAt hp, tau_left, tau_right]
  exact ⟨Same.symm, Same.symm⟩

/-- Restrict a complete-family exchange to the union of the non-cap classes. -/
def noncapRepresentativeEquiv {a b : List (Letter I)} {x y : Letter I}
    {M N : Set (List (TMove (Letter I)))}
    (hM : ∀ R ∈ M, IsMatching₂ (a ++ x :: y :: b) [] R)
    (E : {R // R ∈ M} ≃ {S // S ∈ N})
    (hE : ∀ R, Iso (pairing₂ (a ++ y :: x :: b) (E R).val)
      (swapAt (pairing₂ (a ++ x :: y :: b) R.val) b.length)) :
    {R // R ∈ noncapFamily (a ++ x :: y :: b) b.length M} ≃
      {S // S ∈ noncapFamily (a ++ y :: x :: b) b.length N} where
  toFun R := ⟨(E ⟨R.val, R.property.1⟩).val,
    (E ⟨R.val, R.property.1⟩).property, fun h => R.property.2
      ((boundary_swap_same_iff (boundary_pairing_bound a b x y (hM _ R.property.1))
        (hE ⟨R.val, R.property.1⟩)).mp h)⟩
  invFun S := ⟨(E.symm ⟨S.val, S.property.1⟩).val,
    (E.symm ⟨S.val, S.property.1⟩).property, fun h => S.property.2 (by
      have hh := (boundary_swap_same_iff
        (boundary_pairing_bound a b x y (hM _ (E.symm ⟨S.val, S.property.1⟩).property))
        (hE (E.symm ⟨S.val, S.property.1⟩))).mpr h
      simpa using hh)⟩
  left_inv R := Subtype.ext (congrArg (fun t : {R // R ∈ M} => t.val)
    (E.symm_apply_apply ⟨R.val, R.property.1⟩))
  right_inv S := Subtype.ext (congrArg (fun t : {S // S ∈ N} => t.val)
    (E.apply_symm_apply ⟨S.val, S.property.1⟩))

/-- On the non-cap restriction, class one and class two are exchanged. -/
theorem noncap_exchange_interleaving {A B : List (Letter I)}
    {R S : List (TMove (Letter I))} {p : ℕ}
    (hR : IsMatching₂ A [] R) (hp : p + 1 < (pairing₂ A R).length)
    (hn : ¬ Same (pairing₂ A R) p (p + 1))
    (hi : Iso (pairing₂ B S) (swapAt (pairing₂ A R) p)) :
    Ilv (pairing₂ B S) p ↔ ¬ Ilv (pairing₂ A R) p := by
  rw [ilv_iff_of_iso hi]
  exact ilv_swapAt_iff hR.pairing_properties.1 hp hn

/-- All natural strand labels are transported by inverse endpoint precomposition. -/
def noncapLabelledEquiv {a b : List (Letter I)} {x y : Letter I}
    {M N : Set (List (TMove (Letter I)))}
    (hM : ∀ R ∈ M, IsMatching₂ (a ++ x :: y :: b) [] R)
    (E : {R // R ∈ noncapFamily (a ++ x :: y :: b) b.length M} ≃
      {S // S ∈ noncapFamily (a ++ y :: x :: b) b.length N})
    (hE : ∀ R, Iso (pairing₂ (a ++ y :: x :: b) (E R).val)
      (swapAt (pairing₂ (a ++ x :: y :: b) R.val) b.length)) :
    (Σ R : {R // R ∈ noncapFamily (a ++ x :: y :: b) b.length M},
      MatchingStrand (a ++ x :: y :: b) R.val → ℕ) ≃
    (Σ S : {S // S ∈ noncapFamily (a ++ y :: x :: b) b.length N},
      MatchingStrand (a ++ y :: x :: b) S.val → ℕ) :=
  Equiv.sigmaCongr E (fun R => Equiv.arrowCongr
    (matchingStrandEquivOfSwap (boundary_pairing_bound a b x y (hM _ R.property.1))
      R.property.2 (hE R)) (Equiv.refl ℕ))

/-- Coverage and uniqueness construct the representative equivalence. -/
theorem noncap_representatives_equiv (a b : List (Letter I)) (x y : Letter I)
    (M N : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ (a ++ x :: y :: b) [] R ∧ StrictReduced₂ (a ++ x :: y :: b) R)
    (hN : ∀ S ∈ N, IsMatching₂ (a ++ y :: x :: b) [] S ∧ StrictReduced₂ (a ++ y :: x :: b) S)
    (hMrep : ∀ R, IsMatching₂ (a ++ x :: y :: b) [] R → StrictReduced₂ (a ++ x :: y :: b) R →
      ∃ S ∈ M, Iso (pairing₂ (a ++ x :: y :: b) S) (pairing₂ (a ++ x :: y :: b) R))
    (hNrep : ∀ R, IsMatching₂ (a ++ y :: x :: b) [] R → StrictReduced₂ (a ++ y :: x :: b) R →
      ∃ S ∈ N, Iso (pairing₂ (a ++ y :: x :: b) S) (pairing₂ (a ++ y :: x :: b) R))
    (hMuniq : ∀ R ∈ M, ∀ S ∈ M,
      Iso (pairing₂ (a ++ x :: y :: b) R) (pairing₂ (a ++ x :: y :: b) S) → R = S)
    (hNuniq : ∀ R ∈ N, ∀ S ∈ N,
      Iso (pairing₂ (a ++ y :: x :: b) R) (pairing₂ (a ++ y :: x :: b) S) → R = S) :
    ∃ E : {R // R ∈ noncapFamily (a ++ x :: y :: b) b.length M} ≃
      {S // S ∈ noncapFamily (a ++ y :: x :: b) b.length N}, ∀ R,
      Iso (pairing₂ (a ++ y :: x :: b) (E R).val)
        (swapAt (pairing₂ (a ++ x :: y :: b) R.val) b.length) := by
  obtain ⟨E, hE⟩ := boundary_swap_representatives_equiv a b x y M N
    hM hN hMrep hNrep hMuniq hNuniq
  exact ⟨noncapRepresentativeEquiv (fun R hR => (hM R hR).1) E hE,
    fun R => hE ⟨R.val, R.property.1⟩⟩

/-- Restrict the non-cap correspondence separately to class one and class two. -/
theorem noncap_class_restrictions {a b : List (Letter I)} {x y : Letter I}
    {M N : Set (List (TMove (Letter I)))}
    (hM : ∀ R ∈ M, IsMatching₂ (a ++ x :: y :: b) [] R)
    (E : {R // R ∈ noncapFamily (a ++ x :: y :: b) b.length M} ≃
      {S // S ∈ noncapFamily (a ++ y :: x :: b) b.length N})
    (hE : ∀ R, Iso (pairing₂ (a ++ y :: x :: b) (E R).val)
      (swapAt (pairing₂ (a ++ x :: y :: b) R.val) b.length)) :
    Nonempty ({R : {R // R ∈ noncapFamily (a ++ x :: y :: b) b.length M} //
        ¬ Ilv (pairing₂ (a ++ x :: y :: b) R.val) b.length} ≃
      {S : {S // S ∈ noncapFamily (a ++ y :: x :: b) b.length N} //
        Ilv (pairing₂ (a ++ y :: x :: b) S.val) b.length}) ∧
    Nonempty ({R : {R // R ∈ noncapFamily (a ++ x :: y :: b) b.length M} //
        Ilv (pairing₂ (a ++ x :: y :: b) R.val) b.length} ≃
      {S : {S // S ∈ noncapFamily (a ++ y :: x :: b) b.length N} //
        ¬ Ilv (pairing₂ (a ++ y :: x :: b) S.val) b.length}) := by
  have h (R : {R // R ∈ noncapFamily (a ++ x :: y :: b) b.length M}) :=
    noncap_exchange_interleaving (hM _ R.property.1)
    (boundary_pairing_bound a b x y (hM _ R.property.1)) R.property.2 (hE R)
  constructor
  · exact ⟨E.subtypeEquiv (fun R => (h R).symm)⟩
  · exact ⟨E.subtypeEquiv (fun R => by rw [h R, not_not])⟩

variable {X : Type*} [AddCommGroup X]

/-- Decorated normalization, using the endpoint-reindexed strand counts. -/
theorem noncap_decorated_degree_parity
    (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    (a b : List (Letter I)) (i j : I)
    {R S : List (TMove (Letter I))}
    (hR : IsMatching₂ (a ++ (true, i) :: (false, j) :: b) [] R)
    (hrR : Reduced₂ (a ++ (true, i) :: (false, j) :: b) R)
    (hS : IsMatching₂ (a ++ (false, j) :: (true, i) :: b) [] S)
    (hrS : Reduced₂ (a ++ (false, j) :: (true, i) :: b) S)
    (hn : ¬ Same (pairing₂ (a ++ (true, i) :: (false, j) :: b) R) b.length (b.length + 1))
    (hi : Iso (pairing₂ (a ++ (false, j) :: (true, i) :: b) S)
      (swapAt (pairing₂ (a ++ (true, i) :: (false, j) :: b) R) b.length))
    (q r : ℕ → ℕ × ℕ)
    (hq : ∀ k ∈ leftEnds₂ (a ++ (true, i) :: (false, j) :: b) R,
      OnStrand₂ (a ++ (true, i) :: (false, j) :: b) R k (q k))
    (hr : ∀ k ∈ leftEnds₂ (a ++ (false, j) :: (true, i) :: b) S,
      OnStrand₂ (a ++ (false, j) :: (true, i) :: b) S k (r k))
    (c : MatchingStrand (a ++ (true, i) :: (false, j) :: b) R → ℕ)
    (ds es : List (DTMove I))
    (hd : Decorates₂ (a ++ (true, i) :: (false, j) :: b) R q (strandCounts c) ds)
    (he : Decorates₂ (a ++ (false, j) :: (true, i) :: b) S r
      (strandCounts (c ∘ (matchingStrandEquivOfSwap
        (boundary_pairing_bound a b (true, i) (false, j) hR)
        hn hi).symm)) es) :
    tableDegree D sy μ (dLay (a ++ (false, j) :: (true, i) :: b) es) =
      tableDegree D sy μ (dLay (a ++ (true, i) :: (false, j) :: b) ds) ∧
    xpar D μ (dLay (a ++ (false, j) :: (true, i) :: b) es) =
      xpar D μ (dLay (a ++ (true, i) :: (false, j) :: b) ds) + D.parity i * D.parity j := by
  obtain ⟨hdR, hpR⟩ := mixed_decorated_degree_parity D sy μ hR q hq c ds hd
  obtain ⟨hdS, hpS⟩ := mixed_decorated_degree_parity D sy μ hS r hr _ es he
  obtain ⟨hb, hp⟩ := reduced₂_opposite_boundary_degree_parity_of_not_same
    D sy μ a b i j hR hrR hS hrS hn hi
  have hbnd := boundary_pairing_bound a b (true, i) (false, j) hR
  rw [matchingStrand_swap_sum hbnd hn hi c (fun n k => (n : ℤ) * (2 * sy.d k))] at hdS
  rw [matchingStrand_swap_sum hbnd hn hi c (fun n k => (n : ZMod 2) * D.parity k)] at hpS
  constructor
  · rw [hdR, hdS, hb]
  · rw [hpR, hpS, hp]
    ac_rfl

section Family
variable {i : I} {a b : List (Letter I)}
variable {M N : Set (List (TMove (Letter I)))}
variable (hM : ∀ R ∈ M, IsMatching₂ (a ++ (true, i) :: (false, i) :: b) [] R ∧
  StrictReduced₂ (a ++ (true, i) :: (false, i) :: b) R)
variable (hN : ∀ S ∈ N, IsMatching₂ (a ++ (false, i) :: (true, i) :: b) [] S ∧
  StrictReduced₂ (a ++ (false, i) :: (true, i) :: b) S)
variable (q : {R // R ∈ noncapFamily (a ++ (true, i) :: (false, i) :: b) b.length M} → ℕ → ℕ × ℕ)
    (r : {S // S ∈ noncapFamily (a ++ (false, i) :: (true, i) :: b) b.length N} → ℕ → ℕ × ℕ)
variable (hq : ∀ R k, k ∈ leftEnds₂ (a ++ (true, i) :: (false, i) :: b) R.val →
  OnStrand₂ (a ++ (true, i) :: (false, i) :: b) R.val k (q R k))
variable (hr : ∀ S k, k ∈ leftEnds₂ (a ++ (false, i) :: (true, i) :: b) S.val →
  OnStrand₂ (a ++ (false, i) :: (true, i) :: b) S.val k (r S k))
variable (τ : ∀ R : {R // R ∈ noncapFamily (a ++ (true, i) :: (false, i) :: b) b.length M},
  (MatchingStrand (a ++ (true, i) :: (false, i) :: b) R.val → ℕ) → List (DTMove I))
variable (υ : ∀ S : {S // S ∈ noncapFamily (a ++ (false, i) :: (true, i) :: b) b.length N},
  (MatchingStrand (a ++ (false, i) :: (true, i) :: b) S.val → ℕ) → List (DTMove I))
variable (hτ : ∀ R c, Decorates₂ (a ++ (true, i) :: (false, i) :: b) R.val
  (q R) (strandCounts c) (τ R c))
variable (hυ : ∀ S c, Decorates₂ (a ++ (false, i) :: (true, i) :: b) S.val
  (r S) (strandCounts c) (υ S c))

include hM hN hq hr hτ hυ

/-- Non-cap cancellation in Claim 5: the finite coefficients differ by the crossing parity.
No equivalence, colour map, finite fiber, grading or enumeration identity is assumed.
The result includes both directions at every square-one rational specialization. -/
theorem noncap_labelled_family_coefficients
    (hMrep : ∀ R, IsMatching₂ (a ++ (true, i) :: (false, i) :: b) [] R →
      StrictReduced₂ (a ++ (true, i) :: (false, i) :: b) R →
      ∃ S ∈ M, Iso (pairing₂ (a ++ (true, i) :: (false, i) :: b) S)
        (pairing₂ (a ++ (true, i) :: (false, i) :: b) R))
    (hNrep : ∀ R, IsMatching₂ (a ++ (false, i) :: (true, i) :: b) [] R →
      StrictReduced₂ (a ++ (false, i) :: (true, i) :: b) R →
      ∃ S ∈ N, Iso (pairing₂ (a ++ (false, i) :: (true, i) :: b) S)
        (pairing₂ (a ++ (false, i) :: (true, i) :: b) R))
    (hMuniq : ∀ R ∈ M, ∀ S ∈ M, Iso (pairing₂ (a ++ (true, i) :: (false, i) :: b) R)
      (pairing₂ (a ++ (true, i) :: (false, i) :: b) S) → R = S)
    (hNuniq : ∀ R ∈ N, ∀ S ∈ N, Iso (pairing₂ (a ++ (false, i) :: (true, i) :: b) R)
      (pairing₂ (a ++ (false, i) :: (true, i) :: b) S) → R = S) :
    ∃ F : (Σ R : {R // R ∈ noncapFamily (a ++ (true, i) :: (false, i) :: b) b.length M},
        MatchingStrand (a ++ (true, i) :: (false, i) :: b) R.val → ℕ) ≃
        (Σ S : {S // S ∈ noncapFamily (a ++ (false, i) :: (true, i) :: b) b.length N},
          MatchingStrand (a ++ (false, i) :: (true, i) :: b) S.val → ℕ),
      ∀ (D : Datum I X) (sy : Symmetrizer D) (μ : X),
      let d := fun t :
          (Σ R : {R // R ∈ noncapFamily (a ++ (true, i) :: (false, i) :: b) b.length M},
        MatchingStrand (a ++ (true, i) :: (false, i) :: b) R.val → ℕ) =>
        tableDegree D sy μ (dLay (a ++ (true, i) :: (false, i) :: b) (τ t.1 t.2))
      let e := fun u :
          (Σ S : {S // S ∈ noncapFamily (a ++ (false, i) :: (true, i) :: b) b.length N},
          MatchingStrand (a ++ (false, i) :: (true, i) :: b) S.val → ℕ) =>
        tableDegree D sy μ (dLay (a ++ (false, i) :: (true, i) :: b) (υ u.1 u.2))
      let p := fun t :
          (Σ R : {R // R ∈ noncapFamily (a ++ (true, i) :: (false, i) :: b) b.length M},
        MatchingStrand (a ++ (true, i) :: (false, i) :: b) R.val → ℕ) =>
        xpar D μ (dLay (a ++ (true, i) :: (false, i) :: b) (τ t.1 t.2))
      let p' := fun u :
          (Σ S : {S // S ∈ noncapFamily (a ++ (false, i) :: (true, i) :: b) b.length N},
          MatchingStrand (a ++ (false, i) :: (true, i) :: b) S.val → ℕ) =>
        xpar D μ (dLay (a ++ (false, i) :: (true, i) :: b) (υ u.1 u.2))
      let p₀ := D.parity i
      ∃ (hf : ∀ z : ℤ, Set.Finite {t | d t = z})
        (hg : ∀ z : ℤ, Set.Finite {u | e u = z}),
        (∀ t, e (F t) = d t ∧ p' (F t) = p t + p₀) ∧
        (∀ z, Nonempty ({t // d t = z} ≃ {u // e u = z})) ∧
        ∀ (σ : ℚ), σ ^ 2 = 1 → ∀ (z : ℤ),
          (∑ u ∈ (hg z).toFinset, σ ^ (p' u).val) =
            σ ^ p₀.val * ∑ t ∈ (hf z).toFinset, σ ^ (p t).val ∧
          (∑ t ∈ (hf z).toFinset, σ ^ (p t).val) =
            σ ^ p₀.val * ∑ u ∈ (hg z).toFinset, σ ^ (p' u).val := by
  obtain ⟨E, hE⟩ := noncap_representatives_equiv a b (true, i) (false, i) M N
    hM hN hMrep hNrep hMuniq hNuniq
  let F := noncapLabelledEquiv (fun R hR => (hM R hR).1) E hE
  refine ⟨F, ?_⟩
  intro D sy μ
  dsimp only
  have h (t : Σ R : {R // R ∈ noncapFamily (a ++ (true, i) :: (false, i) :: b) b.length M},
        MatchingStrand (a ++ (true, i) :: (false, i) :: b) R.val → ℕ) :
      tableDegree D sy μ (dLay (a ++ (false, i) :: (true, i) :: b) (υ (F t).1 (F t).2)) =
        tableDegree D sy μ (dLay (a ++ (true, i) :: (false, i) :: b) (τ t.1 t.2)) ∧
      xpar D μ (dLay (a ++ (false, i) :: (true, i) :: b) (υ (F t).1 (F t).2)) =
        xpar D μ (dLay (a ++ (true, i) :: (false, i) :: b) (τ t.1 t.2)) + D.parity i :=
    by
      have hh := noncap_decorated_degree_parity D sy μ a b i i
        (hM t.1 t.1.property.1).1 (hM t.1 t.1.property.1).2.1
        (hN (E t.1) (E t.1).property.1).1 (hN (E t.1) (E t.1).property.1).2.1
        t.1.property.2 (hE t.1) (q t.1) (r (E t.1)) (hq t.1) (hr (E t.1)) t.2 _ _ (hτ _ _) (hυ _ _)
      have hs : D.parity i * D.parity i = D.parity i := by
        generalize D.parity i = v
        fin_cases v <;> rfl
      rw [hs] at hh
      exact hh
  have hf := mixed_labelled_degree_finite D sy μ _ []
    (noncapFamily (a ++ (true, i) :: (false, i) :: b) b.length M)
    (fun R hR => (hM R hR.1).1)
    (fun R hR S hS => hMuniq R hR.1 S hS.1) q hq τ hτ
  have hg := mixed_labelled_degree_finite D sy μ _ []
    (noncapFamily (a ++ (false, i) :: (true, i) :: b) b.length N)
    (fun S hS => (hN S hS.1).1)
    (fun R hR S hS => hNuniq R hR.1 S hS.1) r hr υ hυ
  refine ⟨hf, hg, h, ?_, ?_⟩
  · intro z
    exact ⟨F.subtypeEquiv (fun t => by rw [(h t).1])⟩
  · intro σ hσ z
    obtain ⟨_, heq⟩ := degreeShift_finite_sum F
      (fun t => tableDegree D sy μ (dLay (a ++ (true, i) :: (false, i) :: b) (τ t.1 t.2)))
      (fun u => tableDegree D sy μ (dLay (a ++ (false, i) :: (true, i) :: b) (υ u.1 u.2)))
      (fun t => σ ^ (D.parity i).val *
        σ ^ (xpar D μ (dLay (a ++ (true, i) :: (false, i) :: b) (τ t.1 t.2))).val)
      (fun u => σ ^ (xpar D μ (dLay (a ++ (false, i) :: (true, i) :: b) (υ u.1 u.2))).val)
      0 (fun t => by simpa using (h t).1) (fun t => by
        rw [(h t).2, parity_pow_add σ hσ, mul_comm]) z (by simpa using hf z)
    simp only [sub_zero] at heq
    have heq' := heq.trans (Finset.mul_sum _ _ _).symm
    refine ⟨heq', ?_⟩
    rw [heq', ← mul_assoc]
    have hs : σ ^ (D.parity i).val * σ ^ (D.parity i).val = 1 := by
      rw [← parity_pow_add σ hσ, ← two_mul, show (2 : ZMod 2) = 0 from rfl,
        zero_mul, ZMod.val_zero, pow_zero]
    rw [hs, one_mul]
end Family
end OddMath.SKM
