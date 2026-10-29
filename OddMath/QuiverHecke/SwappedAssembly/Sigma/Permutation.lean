/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Inversion

/-! # The permutation structure of the sideways crossing for distinct colours

For `i ≠ j`, the matrix of the sideways crossing `σ : Eⱼ Fᵢ → Fᵢ Eⱼ` of Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5, (1.11), in the swapped
Hom construction (`docs/Nondegeneracy/SwappedActionAssembly.md` §5) is a block permutation of
the four summand supports. In the sector bookkeeping this is a statement about paths: a summand
path of a two-letter word of distinct colours is determined by its endpoint sectors, since the
probe and reservoir contents record the side of each letter. Hence between two given sectors
each of the words `Eⱼ Fᵢ` and `Fᵢ Eⱼ` has at most one path, and one exists if and only if the
other does (the sides are exchanged).

## Main results

* `SPath.subsingleton_upDn`, `SPath.subsingleton_dnUp`: at most one path between two sectors.
* `SPath.nonempty_dnUp_iff`: paths of `Eⱼ Fᵢ` and `Fᵢ Eⱼ` exist between the same sectors.
* `ProbeReservoir.sigmaPermutation_of_isIso`: `SigmaPermutation` holds as soon as every entry
  of `σ` is invertible; the permutation is forced and the off-diagonal condition is vacuous.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u uB v w

variable {I X : Type u}

namespace SPath

/-- A path of a two-letter word is its two sides, with the endpoint sector as computed. -/
theorem exists_eq_pair {c₁ c₂ : Col I X} {t s : Sector I} (p : SPath [c₁, c₂] t s) :
    ∃ (a b : Bool) (hv₁ : StepValid c₁.l a t) (hv₂ : StepValid c₂.l b (nextSector c₁.l a t))
      (h : nextSector c₂.l b (nextSector c₁.l a t) = s),
      p = h ▸ SPath.cons c₁ a t hv₁ (SPath.cons c₂ b _ hv₂ (SPath.nil _)) := by
  rcases p with _ | ⟨_, a, _, hv₁, p⟩
  rcases p with _ | ⟨_, b, _, hv₂, p⟩
  rcases p with _ | _
  exact ⟨a, b, hv₁, hv₂, rfl, rfl⟩

/-- Two paths of a two-letter word with the same sides are equal. -/
theorem eq_of_pair_sides {c₁ c₂ : Col I X} {t s : Sector I} (p p' : SPath [c₁, c₂] t s)
    (h : ∀ (a b a' b' : Bool), StepValid c₁.l a t →
      StepValid c₂.l b (nextSector c₁.l a t) → StepValid c₁.l a' t →
      StepValid c₂.l b' (nextSector c₁.l a' t) →
      nextSector c₂.l b (nextSector c₁.l a t) = nextSector c₂.l b' (nextSector c₁.l a' t) →
        a = a' ∧ b = b') : p = p' := by
  obtain ⟨a, b, hv₁, hv₂, hs, rfl⟩ := exists_eq_pair p
  obtain ⟨a', b', hv₁', hv₂', hs', rfl⟩ := exists_eq_pair p'
  obtain ⟨rfl, rfl⟩ := h a b a' b' hv₁ hv₂ hv₁' hv₂' (hs.trans hs'.symm)
  subst hs
  rfl

variable {i j : I}

private theorem single_apply_ne' (hij : i ≠ j) : (Finsupp.single i 1 : I →₀ ℕ) j = 0 :=
  Finsupp.single_eq_of_ne hij.symm

/-- The four sides of `Eⱼ Fᵢ`, `i ≠ j`, change the sector differently. -/
theorem sides_eq_upDn (hij : i ≠ j) {t : Sector I} {r r' : X} (a b a' b' : Bool)
    (hv₁ : StepValid (up j) a t) (hv₂ : StepValid (dn i) b (nextSector (up j) a t))
    (hv₁' : StepValid (up j) a' t) (hv₂' : StepValid (dn i) b' (nextSector (up j) a' t))
    (h : nextSector (Col.l ⟨dn i, r'⟩) b (nextSector (Col.l ⟨up j, r⟩) a t) =
      nextSector (Col.l ⟨dn i, r'⟩) b' (nextSector (Col.l ⟨up j, r⟩) a' t)) :
    a = a' ∧ b = b' := by
  have h1i := congrArg (fun x : Sector I => x.1 i) h
  have h1j := congrArg (fun x : Sector I => x.1 j) h
  have h2i := congrArg (fun x : Sector I => x.2 i) h
  have h2j := congrArg (fun x : Sector I => x.2 j) h
  have hji : (Finsupp.single j 1 : I →₀ ℕ) i = 0 := Finsupp.single_eq_of_ne hij
  have hij' : (Finsupp.single i 1 : I →₀ ℕ) j = 0 := single_apply_ne' hij
  clear h
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp only [nextSector, StepValid, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
      Pi.sub_apply, Finsupp.single_eq_same, hji, hij', and_true, and_self,
      reduceCtorEq, and_false] at h1i h1j h2i h2j hv₁ hv₂ hv₁' hv₂' ⊢ <;> omega

/-- The four sides of `Fᵢ Eⱼ`, `i ≠ j`, change the sector differently. -/
theorem sides_eq_dnUp (hij : i ≠ j) {t : Sector I} {r r' : X} (a b a' b' : Bool)
    (hv₁ : StepValid (dn i) a t) (hv₂ : StepValid (up j) b (nextSector (dn i) a t))
    (hv₁' : StepValid (dn i) a' t) (hv₂' : StepValid (up j) b' (nextSector (dn i) a' t))
    (h : nextSector (Col.l ⟨up j, r'⟩) b (nextSector (Col.l ⟨dn i, r⟩) a t) =
      nextSector (Col.l ⟨up j, r'⟩) b' (nextSector (Col.l ⟨dn i, r⟩) a' t)) :
    a = a' ∧ b = b' := by
  have h1i := congrArg (fun x : Sector I => x.1 i) h
  have h1j := congrArg (fun x : Sector I => x.1 j) h
  have h2i := congrArg (fun x : Sector I => x.2 i) h
  have h2j := congrArg (fun x : Sector I => x.2 j) h
  have hji : (Finsupp.single j 1 : I →₀ ℕ) i = 0 := Finsupp.single_eq_of_ne hij
  have hij' : (Finsupp.single i 1 : I →₀ ℕ) j = 0 := single_apply_ne' hij
  clear h
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp only [nextSector, StepValid, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
      Pi.sub_apply, Finsupp.single_eq_same, hji, hij', and_true, and_self,
      reduceCtorEq, and_false] at h1i h1j h2i h2j hv₁ hv₂ hv₁' hv₂' ⊢ <;> omega

/-- For `i ≠ j` there is at most one path of `Eⱼ Fᵢ` between two sectors. -/
theorem subsingleton_upDn (hij : i ≠ j) (r r' : X) (t s : Sector I) :
    Subsingleton (SPath [⟨up j, r⟩, ⟨dn i, r'⟩] t s) :=
  ⟨fun p p' => eq_of_pair_sides p p' fun a b a' b' hv₁ hv₂ hv₁' hv₂' h =>
    sides_eq_upDn hij a b a' b' hv₁ hv₂ hv₁' hv₂' h⟩

/-- For `i ≠ j` there is at most one path of `Fᵢ Eⱼ` between two sectors. -/
theorem subsingleton_dnUp (hij : i ≠ j) (r r' : X) (t s : Sector I) :
    Subsingleton (SPath [⟨dn i, r⟩, ⟨up j, r'⟩] t s) :=
  ⟨fun p p' => eq_of_pair_sides p p' fun a b a' b' hv₁ hv₂ hv₁' hv₂' h =>
    sides_eq_dnUp hij a b a' b' hv₁ hv₂ hv₁' hv₂' h⟩

/-- Exchanging the order of the letters `Eⱼ` and `Fᵢ`, `i ≠ j`, with their sides, preserves
validity and the endpoint sector. -/
theorem exchange_upDn (hij : i ≠ j) {t : Sector I} (a b : Bool)
    (hv₁ : StepValid (up j) a t) (hv₂ : StepValid (dn i) b (nextSector (up j) a t)) :
    StepValid (dn i) b t ∧ StepValid (up j) a (nextSector (dn i) b t) ∧
      nextSector (up j) a (nextSector (dn i) b t) =
        nextSector (dn i) b (nextSector (up j) a t) := by
  have hji : (Finsupp.single j 1 : I →₀ ℕ) i = 0 := Finsupp.single_eq_of_ne hij
  have hij' : (Finsupp.single i 1 : I →₀ ℕ) j = 0 := single_apply_ne' hij
  refine ⟨?_, ?_, ?_⟩
  · cases a <;> cases b <;> simp_all [nextSector, StepValid]
  · cases a <;> cases b <;> simp_all [nextSector, StepValid]
  · cases a <;> cases b <;> simp only [nextSector] <;>
      first
      | rfl
      | (ext x <;> by_cases hx : x = i <;> by_cases hy : x = j <;> subst_vars <;>
          simp_all [StepValid, nextSector])

/-- Exchanging the order of the letters `Fᵢ` and `Eⱼ`, `i ≠ j`, with their sides, preserves
validity and the endpoint sector. -/
theorem exchange_dnUp (hij : i ≠ j) {t : Sector I} (a b : Bool)
    (hv₁ : StepValid (dn i) a t) (hv₂ : StepValid (up j) b (nextSector (dn i) a t)) :
    StepValid (up j) b t ∧ StepValid (dn i) a (nextSector (up j) b t) ∧
      nextSector (dn i) a (nextSector (up j) b t) =
        nextSector (up j) b (nextSector (dn i) a t) := by
  have hji : (Finsupp.single j 1 : I →₀ ℕ) i = 0 := Finsupp.single_eq_of_ne hij
  have hij' : (Finsupp.single i 1 : I →₀ ℕ) j = 0 := single_apply_ne' hij
  have hw₁ : StepValid (up j) b t := by
    cases a <;> cases b <;> simp_all [nextSector, StepValid]
  have hw₂ : StepValid (dn i) a (nextSector (up j) b t) := by
    cases a <;> cases b <;> simp_all [nextSector, StepValid]
  obtain ⟨_, _, h⟩ := exchange_upDn hij b a hw₁ hw₂
  exact ⟨hw₁, hw₂, h.symm⟩

/-- Paths of `Eⱼ Fᵢ` and `Fᵢ Eⱼ`, `i ≠ j`, exist between the same sectors. -/
theorem nonempty_dnUp_iff (hij : i ≠ j) (r₁ r₂ r₁' r₂' : X) (t s : Sector I) :
    Nonempty (SPath [⟨up j, r₁⟩, ⟨dn i, r₂⟩] t s) ↔
      Nonempty (SPath [⟨dn i, r₁'⟩, ⟨up j, r₂'⟩] t s) := by
  constructor
  · rintro ⟨p⟩
    obtain ⟨a, b, hv₁, hv₂, rfl, -⟩ := exists_eq_pair p
    obtain ⟨hw₁, hw₂, h⟩ := exchange_upDn hij a b hv₁ hv₂
    exact ⟨h ▸ SPath.cons ⟨dn i, r₁'⟩ b t hw₁ (SPath.cons ⟨up j, r₂'⟩ a _ hw₂ (SPath.nil _))⟩
  · rintro ⟨p⟩
    obtain ⟨a, b, hv₁, hv₂, rfl, -⟩ := exists_eq_pair p
    obtain ⟨hw₁, hw₂, h⟩ := exchange_dnUp hij a b hv₁ hv₂
    exact ⟨h ▸ SPath.cons ⟨up j, r₁⟩ b t hw₁ (SPath.cons ⟨dn i, r₂⟩ a _ hw₂ (SPath.nil _))⟩

end SPath

variable [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable {P : ProbeReservoir k B D Sc}

/-- **The sideways crossing is a permutation matrix as soon as its entries are invertible.**
For `i ≠ j` the summand paths of `Eⱼ Fᵢ` and of `Fᵢ Eⱼ` between two sectors are unique and
exist simultaneously, so the permutation is forced and the off-diagonal condition is vacuous. -/
theorem sigmaPermutation_of_isIso {c : P.CrossCoeff} {i j : I} (hij : i ≠ j) (ν : X)
    (h : ∀ (t s : Sector I) (p : SPath (wd D ν [up j, dn i]) t s)
      (q : SPath (wd D ν [dn i, up j]) t s) (Z : P.H s), IsIso (P.sigmaEntry c i j ν p q Z)) :
    P.SigmaPermutation c i j ν := by
  intro t s
  have : Subsingleton (SPath (wd D ν [up j, dn i]) t s) := SPath.subsingleton_upDn hij _ _ t s
  have : Subsingleton (SPath (wd D ν [dn i, up j]) t s) := SPath.subsingleton_dnUp hij _ _ t s
  have hne : Nonempty (SPath (wd D ν [up j, dn i]) t s) ↔
      Nonempty (SPath (wd D ν [dn i, up j]) t s) :=
    SPath.nonempty_dnUp_iff hij _ _ _ _ t s
  refine ⟨equivOfSubsingletonOfSubsingleton (fun p => (hne.1 ⟨p⟩).some)
    (fun q => (hne.2 ⟨q⟩).some), fun p q Z hq => absurd (Subsingleton.elim _ _) hq,
    fun p Z => h t s p _ Z⟩

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
