/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PositiveMatchings

/-!
# Boundary bending of matching representatives

The matching-class correspondence used in the proof of Claims 2–3 of Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Theorem 10.3; compare Khovanov–Lauda,
*A categorification of quantum sl(n)*, arXiv:0807.3250v1, Lemma 2.9.

The boundary convention is `dualW a ++ b`. Moving the first bottom letter `x` to the
first top position as `flipL x` leaves this list unchanged. Existing strict realization
therefore gives the bent matching class, without asserting that attaching a cup preserves
strictly reduced syntax. `bending_representatives_equiv` constructs the bijection between
any two representative families with explicit coverage and uniqueness, as chosen in §8.
`exists_bent_matching_layers` realizes the correspondence by the existing diagram layers.

These results concern undecorated matching classes only. They do not identify cup attachment
with a normalized diagram in the category, compute degrees or parities, transport dot labels,
or establish the graphical-series identities or the equivalences asserted in Claims 2–3.
-/

namespace OddMath.SKM

open StringDiagrams.Chord (TMove Iso)

variable {I : Type*}

/-- Bending the first bottom endpoint preserves the ordered, dualized boundary. -/
theorem dualW_bend_boundary (x : Letter I) (a b : List (Letter I)) :
    dualW (x :: a) ++ b = dualW a ++ (flipL x :: b) := by
  simp

private theorem exists_strictReduced_same_boundary {a b c d : List (Letter I)}
    (h : dualW a ++ b = dualW c ++ d) {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a b R) :
    ∃ S, IsMatching₂ c d S ∧ StrictReduced₂ c S ∧ Iso (pairing₂ c S) (pairing₂ a R) := by
  obtain ⟨hv, hl, hs⟩ := hR.pairing_properties
  exact exists_strictReduced_matching hv hl (hs.trans h)

/-- The undecorated matching-class step of [BE2, Theorem 10.3, Claims 2–3].
The input need not be reduced; the output is strictly reduced by existing realization.
Both orientations of `x` are allowed, with no finiteness assumption on colours. -/
theorem exists_strictReduced_bend {x : Letter I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (x :: a) b R) :
    ∃ S, IsMatching₂ a (flipL x :: b) S ∧ StrictReduced₂ a S ∧
      Iso (pairing₂ a S) (pairing₂ (x :: a) R) :=
  exists_strictReduced_same_boundary (dualW_bend_boundary x a b) hR

/-- Concrete diagram consumer of boundary bending: the normalized matching gives existing
`XLayer`s with the required source and target, and retains the same endpoint pairing. -/
theorem exists_bent_matching_layers {x : Letter I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (x :: a) b R) :
    ∃ S, StrictReduced₂ a S ∧ XChain a (tLay a S) (flipL x :: b) ∧
      Iso (pairing₂ a S) (pairing₂ (x :: a) R) := by
  obtain ⟨S, hS, hred, hiso⟩ := exists_strictReduced_bend hR
  exact ⟨S, hred, (matching_bent_spec hS).2.2.2.1, hiso⟩

/-- The bijection of undecorated representative families underlying [BE2, Theorem 10.3,
Claims 2–3]. The hypotheses are exactly membership in the strictly reduced families,
coverage of every strictly reduced class, and uniqueness up to `Iso` from the choice in §8.
The displayed `Iso` specifies the endpoint correspondence, not just equinumerosity. -/
theorem bending_representatives_equiv (x : Letter I) (a b : List (Letter I))
    (M N : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ (x :: a) b R ∧ StrictReduced₂ (x :: a) R)
    (hN : ∀ S ∈ N, IsMatching₂ a (flipL x :: b) S ∧ StrictReduced₂ a S)
    (hMrep : ∀ R, IsMatching₂ (x :: a) b R → StrictReduced₂ (x :: a) R →
      ∃ S ∈ M, Iso (pairing₂ (x :: a) S) (pairing₂ (x :: a) R))
    (hNrep : ∀ R, IsMatching₂ a (flipL x :: b) R → StrictReduced₂ a R →
      ∃ S ∈ N, Iso (pairing₂ a S) (pairing₂ a R))
    (hMuniq : ∀ R ∈ M, ∀ S ∈ M,
      Iso (pairing₂ (x :: a) R) (pairing₂ (x :: a) S) → R = S)
    (hNuniq : ∀ R ∈ N, ∀ S ∈ N, Iso (pairing₂ a R) (pairing₂ a S) → R = S) :
    ∃ E : {R // R ∈ M} ≃ {S // S ∈ N},
      ∀ R, Iso (pairing₂ a (E R).val) (pairing₂ (x :: a) R.val) := by
  classical
  have hex (R : {R // R ∈ M}) :
      ∃ S : {S // S ∈ N}, Iso (pairing₂ a S.val) (pairing₂ (x :: a) R.val) := by
    obtain ⟨S, hS, hred, hiso⟩ := exists_strictReduced_bend (hM R R.property).1
    obtain ⟨T, hT, hTS⟩ := hNrep S hS hred
    exact ⟨⟨T, hT⟩, hTS.trans hiso⟩
  let f : {R // R ∈ M} → {S // S ∈ N} := fun R => (hex R).choose
  have hf (R : {R // R ∈ M}) :
      Iso (pairing₂ a (f R).val) (pairing₂ (x :: a) R.val) := (hex R).choose_spec
  have hinj : Function.Injective f := by
    intro R S h
    apply Subtype.ext
    apply hMuniq R R.property S S.property
    exact (hf R).symm.trans (h ▸ hf S)
  have hsurj : Function.Surjective f := by
    intro S
    obtain ⟨R, hR, hred, hiso⟩ := exists_strictReduced_same_boundary
      (dualW_bend_boundary x a b).symm (hN S S.property).1
    obtain ⟨T, hT, hTR⟩ := hMrep R hR hred
    refine ⟨⟨T, hT⟩, Subtype.ext ?_⟩
    exact hNuniq _ (f ⟨T, hT⟩).property S S.property
      ((hf ⟨T, hT⟩).trans (hTR.trans hiso))
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

end OddMath.SKM
