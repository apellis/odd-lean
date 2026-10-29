/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Sigma.Permutation
import OddMath.QuiverHecke.SwappedAssembly.LeftwardInverse

/-! # The sector blocks of the equal-colour augmented maps

The augmented maps (1.13), (1.14) of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Definition 1.5, in the swapped Hom construction
(`docs/Nondegeneracy/SwappedActionAssembly.md`, (A7)) are stated entrywise between summand
paths with fixed outer sectors `t` (left) and `s` (right) (`PosInverse`, `NegInverse`).

For a single colour `i` the four summand paths of `Eᵢ Fᵢ` change the sector by `0` (probe then
probe, reservoir then reservoir), by `+(i, i)` (probe then reservoir) and by `-(i, i)`
(reservoir then probe); those of `Fᵢ Eᵢ` likewise, with the sides of the two non-diagonal paths
exchanged; the empty word changes nothing. Hence, for `s ≠ t`, the empty word has no path and
`Eᵢ Fᵢ`, `Fᵢ Eᵢ` have at most one path each, existing together. These are the two *swapping
blocks* of `docs/Nondegeneracy/SwappedHomInversion.md`, §7: the augmented map between sectors
`s ≠ t` is the single sideways-crossing entry, and its inverse is minus (for (1.13)) or plus
(for (1.14)) the inverse of that entry, with no dotted window. All the dotted windows lie in
the *central block* `s = t`. See `docs/Nondegeneracy/AugmentedSectorBlocks.md`.

## Main results

* `SPath.isEmpty_nil_of_ne`, `SPath.subsingleton_upDn_self`, `SPath.subsingleton_dnUp_self`,
  `SPath.nonempty_dnUp_self_iff`: the path structure between distinct sectors.
* `ProbeReservoir.posInverse_of_ne`, `ProbeReservoir.negInverse_of_ne`: the swapping blocks are
  inverted by the inverse of the sideways-crossing entry.
* `ProbeReservoir.augmentedInvertible_of_central_of_swapping`: `AugmentedInvertible c` follows
  from `CentralInvertible c` (inverses of the central blocks) and `SwappingInvertible c`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u

variable {I X : Type u}

namespace SPath

/-- The empty word has no path between distinct sectors. -/
theorem isEmpty_nil_of_ne {t s : Sector I} (h : t ≠ s) :
    IsEmpty (SPath ([] : List (Col I X)) t s) :=
  ⟨fun p => by cases p; exact h rfl⟩

variable {i : I}

private theorem single_le_of_one_le {b : I →₀ ℕ} (hb : 1 ≤ b i) : Finsupp.single i 1 ≤ b := by
  rw [Finsupp.single_le_iff]; exact hb

/-- The sector after a probe strand `Eᵢ` followed by a probe strand `Fᵢ` is unchanged. -/
theorem next_upDn_true_true (t : Sector I) :
    nextSector (dn i) true (nextSector (up i) true t) = t := by
  simp only [nextSector, add_tsub_cancel_right]

/-- The sector after a reservoir strand `Eᵢ` followed by a reservoir strand `Fᵢ` is
unchanged. -/
theorem next_upDn_false_false {t : Sector I} (h : 1 ≤ t.2 i) :
    nextSector (dn i) false (nextSector (up i) false t) = t := by
  simp only [nextSector, tsub_add_cancel_of_le (single_le_of_one_le h)]

/-- The sector after a probe strand `Fᵢ` followed by a probe strand `Eᵢ` is unchanged. -/
theorem next_dnUp_true_true {t : Sector I} (h : 1 ≤ t.1 i) :
    nextSector (up i) true (nextSector (dn i) true t) = t := by
  simp only [nextSector, tsub_add_cancel_of_le (single_le_of_one_le h)]

/-- The sector after a reservoir strand `Fᵢ` followed by a reservoir strand `Eᵢ` is
unchanged. -/
theorem next_dnUp_false_false (t : Sector I) :
    nextSector (up i) false (nextSector (dn i) false t) = t := by
  simp only [nextSector, add_tsub_cancel_right]

/-- Between distinct sectors, a path of `Eᵢ Fᵢ` goes through the probe then the reservoir
(content `+(i, i)`) or through the reservoir then the probe (content `-(i, i)`). -/
theorem upDn_sides_of_ne {t s : Sector I} (hts : t ≠ s) (a b : Bool)
    (hv₁ : StepValid (up i) a t) (hv₂ : StepValid (dn i) b (nextSector (up i) a t))
    (hs : nextSector (dn i) b (nextSector (up i) a t) = s) :
    (a = true ∧ b = false) ∨ (a = false ∧ b = true) := by
  cases a <;> cases b
  · exact absurd ((next_upDn_false_false hv₁).symm.trans hs) hts
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact absurd ((next_upDn_true_true t).symm.trans hs) hts

/-- Between distinct sectors, a path of `Fᵢ Eᵢ` goes through the probe then the reservoir
(content `-(i, i)`) or through the reservoir then the probe (content `+(i, i)`). -/
theorem dnUp_sides_of_ne {t s : Sector I} (hts : t ≠ s) (a b : Bool)
    (hv₁ : StepValid (dn i) a t) (hv₂ : StepValid (up i) b (nextSector (dn i) a t))
    (hs : nextSector (up i) b (nextSector (dn i) a t) = s) :
    (a = true ∧ b = false) ∨ (a = false ∧ b = true) := by
  cases a <;> cases b
  · exact absurd ((next_dnUp_false_false t).symm.trans hs) hts
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact absurd ((next_dnUp_true_true hv₁).symm.trans hs) hts

/-- The two sides of a probe-reservoir and a reservoir-probe path end at different sectors. -/
private theorem ne_of_cross {t : Sector I} :
    ((t.1 + Finsupp.single i 1, t.2 + Finsupp.single i 1) : Sector I) ≠
      (t.1 - Finsupp.single i 1, t.2 - Finsupp.single i 1) := by
  intro h
  have := congrArg (fun x : Sector I => x.1 i) h
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
    Finsupp.single_eq_same] at this
  omega

/-- Between distinct sectors there is at most one path of `Eᵢ Fᵢ`. -/
theorem subsingleton_upDn_self {t s : Sector I} (hts : t ≠ s) (r r' : X) :
    Subsingleton (SPath [⟨up i, r⟩, ⟨dn i, r'⟩] t s) := by
  refine ⟨fun p p' => ?_⟩
  obtain ⟨a, b, hv₁, hv₂, hs, rfl⟩ := exists_eq_pair p
  obtain ⟨a', b', hv₁', hv₂', hs', rfl⟩ := exists_eq_pair p'
  have hab : a = a' ∧ b = b' := by
    rcases upDn_sides_of_ne hts a b hv₁ hv₂ hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases upDn_sides_of_ne hts a' b' hv₁' hv₂' hs' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact absurd (hs.trans hs'.symm) (ne_of_cross (t := t) (i := i))
    · exact absurd (hs'.trans hs.symm) (ne_of_cross (t := t) (i := i))
    · exact ⟨rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := hab
  subst hs
  rfl

/-- Between distinct sectors there is at most one path of `Fᵢ Eᵢ`. -/
theorem subsingleton_dnUp_self {t s : Sector I} (hts : t ≠ s) (r r' : X) :
    Subsingleton (SPath [⟨dn i, r⟩, ⟨up i, r'⟩] t s) := by
  refine ⟨fun p p' => ?_⟩
  obtain ⟨a, b, hv₁, hv₂, hs, rfl⟩ := exists_eq_pair p
  obtain ⟨a', b', hv₁', hv₂', hs', rfl⟩ := exists_eq_pair p'
  have hab : a = a' ∧ b = b' := by
    rcases dnUp_sides_of_ne hts a b hv₁ hv₂ hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases dnUp_sides_of_ne hts a' b' hv₁' hv₂' hs' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact absurd (hs'.trans hs.symm) (ne_of_cross (t := t) (i := i))
    · exact absurd (hs.trans hs'.symm) (ne_of_cross (t := t) (i := i))
    · exact ⟨rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := hab
  subst hs
  rfl

/-- Between distinct sectors, paths of `Eᵢ Fᵢ` and of `Fᵢ Eᵢ` exist together: the sides of
the two letters are exchanged. -/
theorem nonempty_dnUp_self_iff {t s : Sector I} (hts : t ≠ s) (r₁ r₂ r₁' r₂' : X) :
    Nonempty (SPath [⟨up i, r₁⟩, ⟨dn i, r₂⟩] t s) ↔
      Nonempty (SPath [⟨dn i, r₁'⟩, ⟨up i, r₂'⟩] t s) := by
  constructor
  · rintro ⟨p⟩
    obtain ⟨a, b, hv₁, hv₂, hs, -⟩ := exists_eq_pair p
    rcases upDn_sides_of_ne hts a b hv₁ hv₂ hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · subst hs
      exact ⟨SPath.cons ⟨dn i, r₁'⟩ false t trivial
        (SPath.cons ⟨up i, r₂'⟩ true _ trivial (SPath.nil _))⟩
    · subst hs
      exact ⟨SPath.cons ⟨dn i, r₁'⟩ true t (show 1 ≤ t.1 i from hv₂)
        (SPath.cons ⟨up i, r₂'⟩ false _ (show 1 ≤ t.2 i from hv₁) (SPath.nil _))⟩
  · rintro ⟨p⟩
    obtain ⟨a, b, hv₁, hv₂, hs, -⟩ := exists_eq_pair p
    rcases dnUp_sides_of_ne hts a b hv₁ hv₂ hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · subst hs
      exact ⟨SPath.cons ⟨up i, r₁⟩ false t (show 1 ≤ t.2 i from hv₂)
        (SPath.cons ⟨dn i, r₂⟩ true _ (show 1 ≤ t.1 i from hv₁) (SPath.nil _))⟩
    · subst hs
      exact ⟨SPath.cons ⟨up i, r₁⟩ true t trivial
        (SPath.cons ⟨dn i, r₂⟩ false _ trivial (SPath.nil _))⟩

end SPath

variable [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable {P : ProbeReservoir k B D Sc}

/-- **The swapping blocks of (1.13).** Between distinct sectors the augmented map (1.13) is
the single sideways-crossing entry (there is no dotted window), and minus its inverse is the
leftward crossing of the inverse. -/
theorem posInverse_of_ne (c : P.CrossCoeff) (i : I) (ν : X) {t s : Sector I} (hts : t ≠ s)
    (h : ∀ (p : SPath (wd D ν [up i, dn i]) t s) (q : SPath (wd D ν [dn i, up i]) t s)
      (Z : P.H s), IsIso (P.sigmaEntry c i i ν p q Z)) :
    ∃ lc dc, P.PosInverse c i ν t s lc dc := by
  have : Subsingleton (SPath (wd D ν [up i, dn i]) t s) := SPath.subsingleton_upDn_self hts _ _
  have : Subsingleton (SPath (wd D ν [dn i, up i]) t s) := SPath.subsingleton_dnUp_self hts _ _
  have : IsEmpty (SPath (wd D ν []) t s) := SPath.isEmpty_nil_of_ne hts
  have hne : Nonempty (SPath (wd D ν [up i, dn i]) t s) ↔
      Nonempty (SPath (wd D ν [dn i, up i]) t s) := SPath.nonempty_dnUp_self_iff hts _ _ _ _
  refine ⟨fun q p Z => -inv (P.sigmaEntry c i i ν p q Z), fun _ r => isEmptyElim r, ?_⟩
  let _ := Fintype.ofFinite (SPath (wd D ν [up i, dn i]) t s)
  let _ := Fintype.ofFinite (SPath (wd D ν [dn i, up i]) t s)
  let _ := Fintype.ofFinite (SPath (wd D ν []) t s)
  refine ⟨fun p p' Z => ?_, fun q q' Z => ?_, fun _ _ _ r => isEmptyElim r,
    fun _ _ r => isEmptyElim r, fun _ _ _ _ r => isEmptyElim r⟩
  · obtain rfl := Subsingleton.elim p p'
    obtain ⟨q⟩ := hne.1 ⟨p⟩
    rw [Fintype.sum_subsingleton _ q, Finset.sum_eq_zero fun _ _ => Fintype.sum_empty _,
      add_zero]
    unfold famDelta
    simp
  · obtain rfl := Subsingleton.elim q q'
    obtain ⟨p⟩ := hne.2 ⟨q⟩
    rw [Fintype.sum_subsingleton _ p]
    unfold famDelta
    simp

/-- **The swapping blocks of (1.14).** Between distinct sectors the augmented map (1.14) is
minus the single sideways-crossing entry, and the inverse of that entry is the leftward
crossing of the inverse. -/
theorem negInverse_of_ne (c : P.CrossCoeff) (i : I) (ν : X) {t s : Sector I} (hts : t ≠ s)
    (h : ∀ (p : SPath (wd D ν [up i, dn i]) t s) (q : SPath (wd D ν [dn i, up i]) t s)
      (Z : P.H s), IsIso (P.sigmaEntry c i i ν p q Z)) :
    ∃ lc dc, P.NegInverse c i ν t s lc dc := by
  have : Subsingleton (SPath (wd D ν [up i, dn i]) t s) := SPath.subsingleton_upDn_self hts _ _
  have : Subsingleton (SPath (wd D ν [dn i, up i]) t s) := SPath.subsingleton_dnUp_self hts _ _
  have : IsEmpty (SPath (wd D ν []) t s) := SPath.isEmpty_nil_of_ne hts
  have hne : Nonempty (SPath (wd D ν [up i, dn i]) t s) ↔
      Nonempty (SPath (wd D ν [dn i, up i]) t s) := SPath.nonempty_dnUp_self_iff hts _ _ _ _
  refine ⟨fun q p Z => -inv (P.sigmaEntry c i i ν p q Z), fun _ _ r => isEmptyElim r, ?_⟩
  let _ := Fintype.ofFinite (SPath (wd D ν [up i, dn i]) t s)
  let _ := Fintype.ofFinite (SPath (wd D ν [dn i, up i]) t s)
  let _ := Fintype.ofFinite (SPath (wd D ν []) t s)
  refine ⟨fun q q' Z => ?_, fun p p' Z => ?_, fun _ _ r => isEmptyElim r,
    fun _ _ _ r => isEmptyElim r, fun _ _ _ _ r => isEmptyElim r⟩
  · obtain rfl := Subsingleton.elim q q'
    obtain ⟨p⟩ := hne.2 ⟨q⟩
    rw [Fintype.sum_subsingleton _ p, Finset.sum_eq_zero fun _ _ => Fintype.sum_empty _,
      add_zero]
    unfold famDelta
    simp
  · obtain rfl := Subsingleton.elim p p'
    obtain ⟨q⟩ := hne.1 ⟨p⟩
    rw [Fintype.sum_subsingleton _ q]
    unfold famDelta
    simp

/-- **The central blocks are invertible**: at every colour `i` and sector `t` of weight `ν`,
the augmented map between the sectors `t` and `t` (which carries all the dotted windows) has an
inverse. The weight restriction is essential: the summands at `t` do not depend on `ν`, while
the number of dotted windows `|⟨hᵢ, ν⟩|` does. -/
def CentralInvertible (P : ProbeReservoir k B D Sc) (c : P.CrossCoeff) : Prop :=
  ∀ (i : I) (ν : X) (t : Sector I), P.wt t = ν →
    (0 ≤ D.h i ν → ∃ lc dc, P.PosInverse c i ν t t lc dc) ∧
    (D.h i ν < 0 → ∃ lc dc, P.NegInverse c i ν t t lc dc)

/-- **The swapping entries are invertible**: every equal-colour sideways-crossing entry
between distinct sectors is an isomorphism. -/
def SwappingInvertible (P : ProbeReservoir k B D Sc) (c : P.CrossCoeff) : Prop :=
  ∀ (i : I) (ν : X) (t s : Sector I), t ≠ s →
    ∀ (p : SPath (wd D ν [up i, dn i]) t s) (q : SPath (wd D ν [dn i, up i]) t s)
      (Z : P.H s), IsIso (P.sigmaEntry c i i ν p q Z)

/-- **Reduction of `AugmentedInvertible` to the sector blocks.** If the augmented maps of the
central blocks (`s = t`, where all the dotted windows lie) have inverses and the
sideways-crossing entries between distinct sectors (the swapping blocks) are invertible, then
the augmented maps are invertible. -/
theorem augmentedInvertible_of_central_of_swapping (c : P.CrossCoeff)
    (hcentral : P.CentralInvertible c) (hswap : P.SwappingInvertible c) :
    P.AugmentedInvertible c := by
  intro i ν t s hw
  by_cases hts : t = s
  · subst hts
    exact hcentral i ν t hw
  · exact ⟨fun _ => posInverse_of_ne c i ν hts (hswap i ν t s hts),
      fun _ => negInverse_of_ne c i ν hts (hswap i ν t s hts)⟩

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
