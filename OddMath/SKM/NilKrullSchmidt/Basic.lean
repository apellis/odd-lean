/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.KrullSchmidtLaurent
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.Congruence.Basic

/-!
# Krull–Schmidt modulo nil ideals

The first preliminary fact of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, §11, used in Theorems 11.3 and 11.7, under a hypothesis weaker
than finite-dimensionality of Hom-spaces: every endomorphism algebra has a two-sided
ideal of nilpotent elements with finite-dimensional quotient (`NilFinite`).

This is the situation of a graded category whose degree-zero endomorphism algebras
are finite-dimensional modulo a nil ideal, for example a category of 1-morphisms of a
super Kac–Moody 2-category with infinitely many colours, where products of bubbles of
colours not occurring in a given object span an infinite-dimensional nil ideal.

Fitting's lemma is proved in the finite-dimensional quotient and lifted along the nil
ideal; decompositions exist by induction on the codimension of a nil ideal, and the
multiplicity functionals are the dimensions of `Hom(Z, X)` modulo the radical.
-/

noncomputable section

namespace OddMath.KrullSchmidtNil

open CategoryTheory CategoryTheory.Limits Module StringDiagrams StringDiagrams.KrullSchmidt

universe v u

variable {𝒞 : Type u} [Category.{v} 𝒞] [Preadditive 𝒞]
variable (k : Type*) [Field k] [Linear k 𝒞]

/-- A morphism `X ⟶ X` viewed in the endomorphism monoid `End X`. -/
abbrev toEnd {X : 𝒞} (f : X ⟶ X) : End X := f

/-- A two-sided ideal of `End X` consisting of nilpotent endomorphisms and of finite
codimension. -/
structure IsNilIdeal {X : 𝒞} (N : Submodule k (X ⟶ X)) : Prop where
  comp_left : ∀ f g : X ⟶ X, g ∈ N → f ≫ g ∈ N
  comp_right : ∀ f g : X ⟶ X, f ∈ N → f ≫ g ∈ N
  isNilpotent : ∀ f ∈ N, IsNilpotent (toEnd f)
  finiteDimensional : FiniteDimensional k ((X ⟶ X) ⧸ N)

/-- Every endomorphism algebra is finite-dimensional modulo a nil ideal. -/
class NilFinite (k : Type*) [Field k] (𝒞 : Type u) [Category.{v} 𝒞] [Preadditive 𝒞]
    [Linear k 𝒞] : Prop where
  exists_isNilIdeal : ∀ X : 𝒞, ∃ N : Submodule k (X ⟶ X), IsNilIdeal k N

/-- Hom-finite categories satisfy `NilFinite`, with the zero ideal. -/
instance [HomFinite k 𝒞] : NilFinite k 𝒞 where
  exists_isNilIdeal X := ⟨⊥,
    { comp_left := fun f g hg => by
        rw [Submodule.mem_bot] at hg ⊢; rw [hg, Limits.comp_zero]
      comp_right := fun f g hf => by
        rw [Submodule.mem_bot] at hf ⊢; rw [hf, Limits.zero_comp]
      isNilpotent := fun f hf => by
        rw [Submodule.mem_bot] at hf; rw [hf]; exact IsNilpotent.zero
      finiteDimensional := inferInstance }⟩

/-! ## Retracts -/

/-- Conjugation `a ↦ p ≫ a ≫ i` by a retraction. -/
def conj {X Y : 𝒞} (i : Y ⟶ X) (p : X ⟶ Y) : (Y ⟶ Y) →ₗ[k] (X ⟶ X) :=
  Linear.leftComp k X p ∘ₗ Linear.rightComp k Y i

theorem conj_apply {X Y : 𝒞} (i : Y ⟶ X) (p : X ⟶ Y) (a : Y ⟶ Y) :
    conj k i p a = p ≫ a ≫ i := rfl

theorem conj_comp {X Y : 𝒞} {i : Y ⟶ X} {p : X ⟶ Y} (h : i ≫ p = 𝟙 Y) (a b : Y ⟶ Y) :
    conj k i p (a ≫ b) = conj k i p a ≫ conj k i p b := by
  simp only [conj_apply, Category.assoc, reassoc_of% h]

theorem conj_pow {X Y : 𝒞} {i : Y ⟶ X} {p : X ⟶ Y} (h : i ≫ p = 𝟙 Y) (a : End Y) (m : ℕ) :
    conj k i p (a ^ (m + 1)) = toEnd (conj k i p a) ^ (m + 1) := by
  induction m with
  | zero => simp only [zero_add, pow_one]
  | succ m ih =>
    rw [pow_succ, End.mul_def, conj_comp k h, ih, pow_succ (toEnd (conj k i p a)) (m + 1),
      End.mul_def]

/-- The pullback of a nil ideal along a retraction is a nil ideal. -/
theorem isNilIdeal_comap {X Y : 𝒞} {i : Y ⟶ X} {p : X ⟶ Y} (h : i ≫ p = 𝟙 Y)
    {N : Submodule k (X ⟶ X)} (hN : IsNilIdeal k N) (hfin :
      FiniteDimensional k ((Y ⟶ Y) ⧸ N.comap (conj k i p))) :
    IsNilIdeal k (N.comap (conj k i p)) where
  comp_left f g hg := by
    rw [Submodule.mem_comap, conj_comp k h]
    exact hN.comp_left _ _ hg
  comp_right f g hf := by
    rw [Submodule.mem_comap, conj_comp k h]
    exact hN.comp_right _ _ hf
  isNilpotent a ha := by
    obtain ⟨n, hn⟩ := hN.isNilpotent _ ha
    refine ⟨n + 1, ?_⟩
    have h0 : toEnd (conj k i p a) ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
    have : conj k i p (toEnd a ^ (n + 1)) = 0 := by rw [conj_pow k h, h0]
    have e : toEnd a ^ (n + 1) = i ≫ conj k i p (toEnd a ^ (n + 1)) ≫ p := by
      simp only [conj_apply, ← Category.assoc, h, Category.id_comp]
      simp only [Category.assoc, h, Category.comp_id]
    rw [e, this, Limits.zero_comp, Limits.comp_zero]
  finiteDimensional := hfin

omit [Linear k 𝒞] in
theorem eq_zero_of_idem_isNilpotent {X : 𝒞} {e : X ⟶ X} (he : e ≫ e = e)
    (hn : IsNilpotent (toEnd e)) : e = 0 :=
  IsIdempotentElem.eq_zero_of_isNilpotent (R := End X) (by rw [IsIdempotentElem, End.mul_def, he]) hn

/-- A proper summand admits a nil ideal of strictly smaller codimension. -/
theorem exists_lt {X Y Z : 𝒞} (i : Y ⟶ X) (p : X ⟶ Y) (i' : Z ⟶ X) (p' : X ⟶ Z)
    (h₁ : i ≫ p = 𝟙 Y) (h₂ : i' ≫ p' = 𝟙 Z) (h₃ : i ≫ p' = 0) (h₄ : i' ≫ p = 0)
    (hZ : ¬ IsZero Z) {N : Submodule k (X ⟶ X)} (hN : IsNilIdeal k N) :
    ∃ N' : Submodule k (Y ⟶ Y), IsNilIdeal k N' ∧
      finrank k ((Y ⟶ Y) ⧸ N') < finrank k ((X ⟶ X) ⧸ N) := by
  have := hN.finiteDimensional
  set NY := N.comap (conj k i p)
  set NZ := N.comap (conj k i' p')
  let Φ : ((Y ⟶ Y) ⧸ NY) × ((Z ⟶ Z) ⧸ NZ) →ₗ[k] (X ⟶ X) ⧸ N :=
    (NY.mapQ N (conj k i p) le_rfl) ∘ₗ LinearMap.fst k _ _ +
      (NZ.mapQ N (conj k i' p') le_rfl) ∘ₗ LinearMap.snd k _ _
  have key : ∀ a b, p ≫ a ≫ i + p' ≫ b ≫ i' ∈ N → a ∈ NY ∧ b ∈ NZ := by
    intro a b hab
    constructor
    · have := hN.comp_right _ (p ≫ i) (hN.comp_left (p ≫ i) _ hab)
      show p ≫ a ≫ i ∈ N
      convert this using 1
      simp only [Preadditive.comp_add, Category.assoc, reassoc_of% h₁, reassoc_of% h₃,
        Limits.zero_comp, Limits.comp_zero, add_zero]
    · have := hN.comp_right _ (p' ≫ i') (hN.comp_left (p' ≫ i') _ hab)
      show p' ≫ b ≫ i' ∈ N
      convert this using 1
      simp only [Preadditive.comp_add, Category.assoc, reassoc_of% h₂, reassoc_of% h₄,
        Limits.zero_comp, Limits.comp_zero, zero_add]
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, y⟩ hxy
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    induction y using Submodule.Quotient.induction_on with | H b => ?_
    have hm : p ≫ a ≫ i + p' ≫ b ≫ i' ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero]
      exact hxy
    obtain ⟨ha, hb⟩ := key a b hm
    rw [Prod.mk_eq_zero, Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero]
    exact ⟨ha, hb⟩
  have hfY : FiniteDimensional k ((Y ⟶ Y) ⧸ NY) :=
    FiniteDimensional.of_injective (Φ ∘ₗ LinearMap.inl k _ _)
      (hΦ.comp (LinearMap.inl_injective))
  have hfZ : FiniteDimensional k ((Z ⟶ Z) ⧸ NZ) :=
    FiniteDimensional.of_injective (Φ ∘ₗ LinearMap.inr k _ _)
      (hΦ.comp (LinearMap.inr_injective))
  refine ⟨NY, isNilIdeal_comap k h₁ hN hfY, ?_⟩
  have hle := LinearMap.finrank_le_finrank_of_injective hΦ
  rw [Module.finrank_prod] at hle
  have hpos : 0 < finrank k ((Z ⟶ Z) ⧸ NZ) := by
    refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨Submodule.Quotient.mk (𝟙 Z), fun h => hZ ?_⟩
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, conj_apply, Category.id_comp] at h
    have he : (p' ≫ i') ≫ (p' ≫ i') = p' ≫ i' := by simp [reassoc_of% h₂]
    have h0 := eq_zero_of_idem_isNilpotent he (hN.isNilpotent _ h)
    rw [IsZero.iff_id_eq_zero]
    calc 𝟙 Z = (i' ≫ p') ≫ (i' ≫ p') := by rw [h₂, Category.id_comp]
      _ = i' ≫ (p' ≫ i') ≫ p' := by simp only [Category.assoc]
      _ = 0 := by rw [h0]; simp
  omega

variable [NilFinite k 𝒞]

/-- The least codimension of a nil ideal of `End X`. -/
def nilRank (X : 𝒞) : ℕ := by
  classical
  exact Nat.find (show ∃ n, ∃ N : Submodule k (X ⟶ X), IsNilIdeal k N ∧
    finrank k ((X ⟶ X) ⧸ N) = n from
    (NilFinite.exists_isNilIdeal (k := k) X).elim fun N hN => ⟨_, N, hN, rfl⟩)

theorem exists_nilRank (X : 𝒞) : ∃ N : Submodule k (X ⟶ X), IsNilIdeal k N ∧
    finrank k ((X ⟶ X) ⧸ N) = nilRank k X := by
  classical
  unfold nilRank
  exact Nat.find_spec (p := fun n => ∃ N : Submodule k (X ⟶ X), IsNilIdeal k N ∧
    finrank k ((X ⟶ X) ⧸ N) = n) _

theorem nilRank_le {X : 𝒞} {N : Submodule k (X ⟶ X)} (hN : IsNilIdeal k N) :
    nilRank k X ≤ finrank k ((X ⟶ X) ⧸ N) := by
  classical
  unfold nilRank
  exact Nat.find_min' _ ⟨N, hN, rfl⟩

theorem nilRank_lt {X Y Z : 𝒞} (i : Y ⟶ X) (p : X ⟶ Y) (i' : Z ⟶ X) (p' : X ⟶ Z)
    (h₁ : i ≫ p = 𝟙 Y) (h₂ : i' ≫ p' = 𝟙 Z) (h₃ : i ≫ p' = 0) (h₄ : i' ≫ p = 0)
    (hZ : ¬ IsZero Z) : nilRank k Y < nilRank k X := by
  obtain ⟨N, hN, hr⟩ := exists_nilRank k X
  obtain ⟨N', hN', hlt⟩ := exists_lt k i p i' p' h₁ h₂ h₃ h₄ hZ hN
  exact (nilRank_le k hN').trans_lt (hr ▸ hlt)

/-! ## Existence of decompositions -/

/-- Splitting an object with a nontrivial idempotent into two nonzero summands. -/
theorem exists_proper_split [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] {X : 𝒞}
    (h0 : ¬ IsZero X) (hi : ¬ IsIndec X) :
    ∃ (Y Z : 𝒞) (i : Y ⟶ X) (p : X ⟶ Y) (i' : Z ⟶ X) (p' : X ⟶ Z), i ≫ p = 𝟙 Y ∧
      i' ≫ p' = 𝟙 Z ∧ i ≫ p' = 0 ∧ i' ≫ p = 0 ∧ p ≫ i + p' ≫ i' = 𝟙 X ∧
      ¬ IsZero Y ∧ ¬ IsZero Z := by
  obtain ⟨e, he, he0, he1⟩ : ∃ e : X ⟶ X, e ≫ e = e ∧ e ≠ 0 ∧ e ≠ 𝟙 X := by
    by_contra hne
    push Not at hne
    exact hi ⟨h0, fun e he => by
      by_cases h' : e = 0
      · exact Or.inl h'
      · exact Or.inr (hne e he h')⟩
  obtain ⟨Y, Z, i, p, i', p', h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_split e he
  refine ⟨Y, Z, i, p, i', p', h₁, h₂, h₃, h₄, by rw [h₅, h₆, add_sub_cancel], ?_, ?_⟩
  · exact fun hY => he0 (by rw [← h₅, hY.eq_of_src i, Limits.comp_zero])
  · exact fun hZ => he1 (by
      have : 𝟙 X - e = 0 := by rw [← h₆, hZ.eq_of_src i', Limits.comp_zero]
      exact (sub_eq_zero.1 this).symm)

include k in
/-- **Existence of Krull–Schmidt decompositions** in an idempotent-complete category
satisfying `NilFinite`. -/
theorem of_mem_closure_indec [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] (X : 𝒞) :
    K₀.mk X ∈ AddSubmonoid.closure {x | ∃ Z : 𝒞, IsIndec Z ∧ x = K₀.mk Z} := by
  induction h : nilRank k X using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    by_cases h0 : IsZero X
    · rw [mk_isZero h0]; exact AddSubmonoid.zero_mem _
    by_cases hi : IsIndec X
    · exact AddSubmonoid.subset_closure ⟨X, hi, rfl⟩
    obtain ⟨Y, Z, i, p, i', p', h₁, h₂, h₃, h₄, h₅, hY, hZ⟩ := exists_proper_split h0 hi
    rw [mk_eq_add_of_iso (isoOfData i p i' p' h₁ h₂ h₃ h₄ h₅)]
    refine AddSubmonoid.add_mem _ (ih _ ?_ Y rfl) (ih _ ?_ Z rfl)
    · rw [← h]; exact nilRank_lt k i p i' p' h₁ h₂ h₃ h₄ hZ
    · rw [← h]; exact nilRank_lt k i' p' i p h₂ h₁ h₄ h₃ hY

/-! ## Fitting's lemma -/

theorem isUnit_of_isUnit_mul {R : Type*} [Monoid R] {f g : R} (h₁ : IsUnit (f * g))
    (h₂ : IsUnit (g * f)) : IsUnit f := by
  obtain ⟨u, hu⟩ := h₁
  obtain ⟨w, hw⟩ := h₂
  have hr : f * (g * ↑u⁻¹) = 1 := by rw [← mul_assoc, ← hu, Units.mul_inv]
  have hl : (↑w⁻¹ * g) * f = 1 := by rw [mul_assoc, ← hw, Units.inv_mul]
  have he : ↑w⁻¹ * g = g * ↑u⁻¹ := by
    calc ↑w⁻¹ * g = (↑w⁻¹ * g) * (f * (g * ↑u⁻¹)) := by rw [hr, mul_one]
      _ = ((↑w⁻¹ * g) * f) * (g * ↑u⁻¹) := by simp only [mul_assoc]
      _ = g * ↑u⁻¹ := by rw [hl, one_mul]
  exact ⟨⟨f, g * ↑u⁻¹, hr, he ▸ hl⟩, rfl⟩

include k in
/-- **Fitting's lemma**: an endomorphism of an indecomposable object is nilpotent or
invertible. -/
theorem isNilpotent_or_isUnit_of_isIndec {X : 𝒞} (hX : IsIndec X) (f : End X) :
    IsNilpotent f ∨ IsUnit f := by
  obtain ⟨N, hN⟩ := NilFinite.exists_isNilIdeal (k := k) X
  have := hN.finiteDimensional
  let I : TwoSidedIdeal (End X) := TwoSidedIdeal.mk' (N : Set (X ⟶ X)) N.zero_mem
    (fun hx hy => N.add_mem hx hy) (fun hx => N.neg_mem hx)
    (fun {x y} hy => by rw [End.mul_def]; exact hN.comp_right y x hy)
    (fun {x y} hx => by rw [End.mul_def]; exact hN.comp_left y x hx)
  have hI : ∀ x : End X, x ∈ I ↔ x ∈ N := fun x => TwoSidedIdeal.mem_mk' _ _ _ _ _ _ x
  let c := I.ringCon
  let π : End X →+* c.Quotient := c.mk'
  have hπ : ∀ x, π x = 0 ↔ x ∈ N := by
    intro x
    rw [← hI, TwoSidedIdeal.mem_iff, ← RingCon.eq]
    rfl
  have hsurj : Function.Surjective π := RingCon.mk'_surjective c
  let πₗ : (X ⟶ X) →ₗ[k] c.Quotient := (c.mkₐ k).toLinearMap
  have hfin : FiniteDimensional k c.Quotient := by
    let L : ((X ⟶ X) ⧸ N) →ₗ[k] c.Quotient := N.liftQ πₗ (fun x hx => (hπ x).2 hx)
    refine Module.Finite.of_surjective L fun y => ?_
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hker : ∀ x ∈ RingHom.ker π, IsNilpotent x := fun x hx =>
    hN.isNilpotent x ((hπ x).1 hx)
  have hidem : ∀ e : c.Quotient, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    obtain ⟨e', he', rfl⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent π hker e
      (hsurj e) he
    have he'' : e' ≫ e' = e' := by rw [← End.mul_def]; exact he'.eq
    rcases hX.2 e' he'' with h | h
    · left; rw [show (e' : End X) = 0 from h, map_zero]
    · right; rw [show (e' : End X) = 1 from h, map_one]
  rcases StringDiagrams.FiniteDimensionalAlgebra.isNilpotent_or_isUnit_of_idempotent k
    hidem (π f) with ⟨n, hn⟩ | hu
  · left
    rw [← map_pow, hπ] at hn
    obtain ⟨m, hm⟩ := hN.isNilpotent _ hn
    exact ⟨n * m, by rw [pow_mul]; exact hm⟩
  · right
    obtain ⟨u, hu⟩ := hu
    obtain ⟨g, hg⟩ := hsurj ↑u⁻¹
    have h1 : IsNilpotent (f * g - 1) := hker _ (by
      rw [RingHom.mem_ker, map_sub, map_mul, hg, ← hu, Units.mul_inv, map_one, sub_self])
    have h2 : IsNilpotent (g * f - 1) := hker _ (by
      rw [RingHom.mem_ker, map_sub, map_mul, hg, ← hu, Units.inv_mul, map_one, sub_self])
    refine isUnit_of_isUnit_mul (g := g) ?_ ?_
    · simpa using h1.isUnit_one_add
    · simpa using h2.isUnit_one_add

omit [NilFinite k 𝒞] [Linear k 𝒞] in
theorem nontrivial_of_isIndec {X : 𝒞} (hX : IsIndec X) : Nontrivial (End X) :=
  ⟨⟨0, 1, fun h => hX.1 ((IsZero.iff_id_eq_zero _).2 h.symm)⟩⟩

include k in
/-- The endomorphism ring of an indecomposable object is local. -/
theorem isLocalRing_of_isIndec {X : 𝒞} (hX : IsIndec X) : IsLocalRing (End X) :=
  have := nontrivial_of_isIndec hX
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a =>
    (isNilpotent_or_isUnit_of_isIndec k hX a).elim (fun h => Or.inr h.isUnit_one_sub) Or.inl

/-! ## Radicals and multiplicities -/

/-- The radical `rad(Z, X)`: the morphisms `f : Z → X` such that `f ≫ g` is never invertible. -/
def rad {Z : 𝒞} (hZ : IsIndec Z) (X : 𝒞) : Submodule k (Z ⟶ X) where
  carrier := {f | ∀ g : X ⟶ Z, ¬ IsUnit (M := End Z) (f ≫ g)}
  zero_mem' g h := by
    have := nontrivial_of_isIndec hZ
    rw [Limits.zero_comp] at h
    exact not_isUnit_zero h
  add_mem' {f f'} hf hf' g := by
    have := isLocalRing_of_isIndec k hZ
    rw [Preadditive.add_comp]
    exact nonunits_add' (R := End Z) (hf g) (hf' g)
  smul_mem' c f hf g h := by
    rw [Linear.smul_comp] at h
    have hi : IsIso (c • (f ≫ g)) := (isUnit_iff_isIso (X := Z) _).1 h
    refine hf g ⟨⟨f ≫ g, c • inv (c • (f ≫ g)), ?_, ?_⟩, rfl⟩
    · rw [End.mul_def, Linear.smul_comp, ← Linear.comp_smul, IsIso.inv_hom_id]; rfl
    · rw [End.mul_def, Linear.comp_smul, ← Linear.smul_comp, IsIso.hom_inv_id]; rfl

variable {k} in
theorem mem_rad {Z X : 𝒞} {hZ : IsIndec Z} {f : Z ⟶ X} :
    f ∈ rad k hZ X ↔ ∀ g : X ⟶ Z, ¬ IsUnit (M := End Z) (f ≫ g) := Iff.rfl

theorem rad_map_postIso {Z : 𝒞} (hZ : IsIndec Z) {X X' : 𝒞} (φ : X ≅ X') :
    (rad k hZ X).map (postIso k Z φ).toLinearMap = rad k hZ X' := by
  ext f
  constructor
  · rintro ⟨f₀, hf₀, rfl⟩ g
    simpa using hf₀ (φ.hom ≫ g)
  · intro hf
    refine ⟨f ≫ φ.inv, fun g => ?_, by simp⟩
    simpa using hf (φ.inv ≫ g)

/-- The quotient `Hom(Z, X) / rad(Z, X)`. -/
abbrev Top {Z : 𝒞} (hZ : IsIndec Z) (X : 𝒞) := (Z ⟶ X) ⧸ rad k hZ X

/-- Isomorphism invariance of `Hom(Z, -) / rad(Z, -)`. -/
def topIso {Z : 𝒞} (hZ : IsIndec Z) {X X' : 𝒞} (φ : X ≅ X') : Top k hZ X ≃ₗ[k] Top k hZ X' :=
  Submodule.Quotient.equiv _ _ (postIso k Z φ) (rad_map_postIso k hZ φ)

/-- Between non-isomorphic indecomposables, the radical is everything. -/
theorem rad_eq_top {Z Z' : 𝒞} (hZ : IsIndec Z) (hZ' : IsIndec Z')
    (h : ¬ Nonempty (Z ≅ Z')) : rad k hZ Z' = ⊤ := by
  refine eq_top_iff.2 fun f _ g hfg => h ?_
  obtain ⟨u, hu⟩ := hfg
  have hv : f ≫ g ≫ (↑u⁻¹ : End Z) = 𝟙 Z := by
    have := u.inv_mul
    rw [End.mul_def, hu] at this
    rw [← Category.assoc]; exact this
  set g' : Z' ⟶ Z := g ≫ (↑u⁻¹ : End Z)
  have he : (g' ≫ f) ≫ (g' ≫ f) = g' ≫ f := by
    rw [Category.assoc, ← Category.assoc f, hv, Category.id_comp]
  rcases hZ'.2 _ he with h0 | h1
  · exfalso
    apply hZ.1
    rw [IsZero.iff_id_eq_zero]
    calc 𝟙 Z = (f ≫ g') ≫ (f ≫ g') := by rw [hv, Category.id_comp]
      _ = f ≫ (g' ≫ f) ≫ g' := by simp only [Category.assoc]
      _ = 0 := by rw [h0]; simp
  · exact ⟨⟨f, g', hv, h1⟩⟩

theorem rad_eq_top_of_isZero {Z X : 𝒞} (hZ : IsIndec Z) (hX : IsZero X) : rad k hZ X = ⊤ := by
  refine eq_top_iff.2 fun f _ g hfg => ?_
  have := nontrivial_of_isIndec hZ
  rw [hX.eq_of_tgt f 0, Limits.zero_comp] at hfg
  exact not_isUnit_zero hfg

theorem finiteDimensional_of_rad_eq_top {Z X : 𝒞} (hZ : IsIndec Z) (h : rad k hZ X = ⊤) :
    FiniteDimensional k (Top k hZ X) := by
  have : Subsingleton (Top k hZ X) := Submodule.Quotient.subsingleton_iff.2 h
  infer_instance

/-- `Hom(Z, Z) / rad` is finite-dimensional: the radical contains every nil ideal. -/
theorem finiteDimensional_top_self {Z : 𝒞} (hZ : IsIndec Z) : FiniteDimensional k (Top k hZ Z) := by
  obtain ⟨N, hN⟩ := NilFinite.exists_isNilIdeal (k := k) Z
  have := hN.finiteDimensional
  have hle : N ≤ LinearMap.ker (rad k hZ Z).mkQ := by
    intro f hf
    rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    intro g hg
    have := nontrivial_of_isIndec hZ
    exact (hN.isNilpotent _ (hN.comp_right f g hf)).not_isUnit hg
  refine Module.Finite.of_surjective (N.liftQ (rad k hZ Z).mkQ hle) fun y => ?_
  obtain ⟨x, rfl⟩ := (rad k hZ Z).mkQ_surjective y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

section Biprod

variable [HasBinaryBiproducts 𝒞]

theorem mem_rad_biprod {Z : 𝒞} (hZ : IsIndec Z) {X Y : 𝒞} (f : Z ⟶ X ⊞ Y) :
    f ∈ rad k hZ (X ⊞ Y) ↔ f ≫ biprod.fst ∈ rad k hZ X ∧ f ≫ biprod.snd ∈ rad k hZ Y := by
  constructor
  · intro hf
    exact ⟨fun g => by simpa using hf (biprod.fst ≫ g), fun g => by simpa using hf (biprod.snd ≫ g)⟩
  · rintro ⟨ha, hb⟩ g
    have := isLocalRing_of_isIndec k hZ
    have : f ≫ g = (f ≫ biprod.fst) ≫ (biprod.inl ≫ g) + (f ≫ biprod.snd) ≫ (biprod.inr ≫ g) := by
      conv_lhs => rw [← Category.id_comp g, ← biprod.total]
      simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
    rw [this]
    exact nonunits_add' (R := End Z) (ha _) (hb _)

/-- `Hom(Z, X ⊞ Y) / rad ≅ Hom(Z, X) / rad × Hom(Z, Y) / rad`. -/
def topBiprod {Z : 𝒞} (hZ : IsIndec Z) (X Y : 𝒞) :
    Top k hZ (X ⊞ Y) ≃ₗ[k] Top k hZ X × Top k hZ Y := by
  let L : (Z ⟶ X ⊞ Y) →ₗ[k] Top k hZ X × Top k hZ Y :=
    LinearMap.prod ((rad k hZ X).mkQ ∘ₗ Linear.rightComp k Z biprod.fst)
      ((rad k hZ Y).mkQ ∘ₗ Linear.rightComp k Z biprod.snd)
  have hL : Function.Surjective L := by
    rintro ⟨x, y⟩
    obtain ⟨a, rfl⟩ := (rad k hZ X).mkQ_surjective x
    obtain ⟨b, rfl⟩ := (rad k hZ Y).mkQ_surjective y
    exact ⟨biprod.lift a b, by simp [L]⟩
  have hker : LinearMap.ker L = rad k hZ (X ⊞ Y) := by
    ext f
    rw [mem_rad_biprod]
    simp [L, LinearMap.mem_ker, Submodule.Quotient.mk_eq_zero]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (L.quotKerEquivOfSurjective hL)

variable [IsIdempotentComplete 𝒞]

/-- `Hom(Z, X) / rad(Z, X)` is finite-dimensional for every `X`. -/
theorem finiteDimensional_top {Z : 𝒞} (hZ : IsIndec Z) (X : 𝒞) :
    FiniteDimensional k (Top k hZ X) := by
  induction h : nilRank k X using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    by_cases h0 : IsZero X
    · exact finiteDimensional_of_rad_eq_top k hZ (rad_eq_top_of_isZero k hZ h0)
    by_cases hi : IsIndec X
    · by_cases hiso : Nonempty (Z ≅ X)
      · obtain ⟨e⟩ := hiso
        have := finiteDimensional_top_self k hZ
        exact LinearEquiv.finiteDimensional (topIso k hZ e)
      · exact finiteDimensional_of_rad_eq_top k hZ (rad_eq_top k hZ hi hiso)
    obtain ⟨Y, W, i, p, i', p', h₁, h₂, h₃, h₄, h₅, hY, hW⟩ := exists_proper_split h0 hi
    have := ih _ (h ▸ nilRank_lt k i p i' p' h₁ h₂ h₃ h₄ hW) Y rfl
    have := ih _ (h ▸ nilRank_lt k i' p' i p h₂ h₁ h₄ h₃ hY) W rfl
    exact LinearEquiv.finiteDimensional
      ((topBiprod k hZ Y W).symm.trans (topIso k hZ (isoOfData i p i' p' h₁ h₂ h₃ h₄ h₅).symm))

/-- The multiplicity invariant `dim (Hom(Z, X) / rad(Z, X))`. -/
def mult {Z : 𝒞} (hZ : IsIndec Z) (X : 𝒞) : ℤ := finrank k (Top k hZ X)

omit [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] in
theorem mult_iso {Z : 𝒞} (hZ : IsIndec Z) {X X' : 𝒞} (φ : X ≅ X') :
    mult k hZ X = mult k hZ X' := by
  unfold mult; rw [(topIso k hZ φ).finrank_eq]

theorem mult_biprod {Z : 𝒞} (hZ : IsIndec Z) (X Y : 𝒞) :
    mult k hZ (X ⊞ Y) = mult k hZ X + mult k hZ Y := by
  have := finiteDimensional_top k hZ X
  have := finiteDimensional_top k hZ Y
  unfold mult
  rw [(topBiprod k hZ X Y).finrank_eq, Module.finrank_prod]
  push_cast; ring

/-- The multiplicity functional `K₀(𝒞) → ℤ` of an indecomposable object `Z`. -/
def multK {Z : 𝒞} (hZ : IsIndec Z) : K₀ 𝒞 →+ ℤ :=
  K₀.lift (mult k hZ) (fun _ _ e => mult_iso k hZ e) (mult_biprod k hZ)

@[simp] theorem multK_of {Z : 𝒞} (hZ : IsIndec Z) (X : 𝒞) :
    multK k hZ (K₀.mk X) = mult k hZ X := K₀.lift_mk _ _ _ _

theorem multK_self_pos {Z : 𝒞} (hZ : IsIndec Z) : 0 < multK k hZ (K₀.mk Z) := by
  have := finiteDimensional_top_self k hZ
  rw [multK_of, mult, Nat.cast_pos]
  refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨Submodule.Quotient.mk (𝟙 Z), fun h => ?_⟩
  rw [Submodule.Quotient.mk_eq_zero] at h
  exact h (𝟙 Z) (by rw [Category.comp_id]; exact isUnit_one)

theorem multK_of_not_iso {Z Z' : 𝒞} (hZ : IsIndec Z) (hZ' : IsIndec Z')
    (h : ¬ Nonempty (Z ≅ Z')) : multK k hZ (K₀.mk Z') = 0 := by
  have : Subsingleton (Top k hZ Z') :=
    Submodule.Quotient.subsingleton_iff.2 (rad_eq_top k hZ hZ' h)
  rw [multK_of, mult, finrank_zero_of_subsingleton, Nat.cast_zero]

include k in
/-- If `K₀.mk Z = K₀.mk S` with `Z` indecomposable, then `Z` is a retract of `S`. -/
theorem exists_retract_of_mk_eq {Z S : 𝒞} (hZ : IsIndec Z) (h : K₀.mk Z = K₀.mk S) :
    ∃ (f : Z ⟶ S) (g : S ⟶ Z), f ≫ g = 𝟙 Z := by
  have hpos := multK_self_pos k hZ
  have := finiteDimensional_top k hZ S
  rw [h, multK_of, mult, Nat.cast_pos] at hpos
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  obtain ⟨f, rfl⟩ := (rad k hZ S).mkQ_surjective x
  rw [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero] at hx
  simp only [mem_rad, not_forall, not_not] at hx
  obtain ⟨g, u, hu⟩ := hx
  refine ⟨f, g ≫ (↑u⁻¹ : End Z), ?_⟩
  have := u.inv_mul
  rw [End.mul_def, hu] at this
  rw [← Category.assoc]; exact this

end Biprod

/-! ## The integral basis -/

section Basis
variable [HasBinaryBiproducts 𝒞]

include k in
theorem linearIndependent_indec [IsIdempotentComplete 𝒞] :
    LinearIndependent ℤ (fun b : IndecClass 𝒞 => K₀.mk b.rep) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg b₀ hb₀
  have key := congrArg (multK k b₀.isIndec_rep) hg
  rw [map_sum, map_zero] at key
  simp only [map_zsmul, zsmul_eq_mul] at key
  rw [Finset.sum_eq_single b₀] at key
  · exact (mul_eq_zero.1 key).resolve_right (ne_of_gt (multK_self_pos k b₀.isIndec_rep))
  · intro b _ hb
    rw [multK_of_not_iso k b₀.isIndec_rep b.isIndec_rep
      (fun ⟨e⟩ => hb (IndecClass.eq_of_iso e).symm), mul_zero]
  · exact fun h => (h hb₀).elim

variable [IsIdempotentComplete 𝒞]

include k in
theorem mk_mem_span (X : 𝒞) :
    K₀.mk X ∈ Submodule.span ℤ (Set.range fun b : IndecClass 𝒞 => K₀.mk b.rep) := by
  have h := of_mem_closure_indec k X
  refine (AddSubmonoid.closure_le (S := (Submodule.span ℤ
    (Set.range fun b : IndecClass 𝒞 => K₀.mk b.rep)).toAddSubmonoid)).2 ?_ h
  rintro _ ⟨Z, hZ, rfl⟩
  obtain ⟨e⟩ := IndecClass.exists_iso_rep hZ
  change K₀.mk Z ∈ Submodule.span _ _
  rw [K₀.mk_eq_mk_of_iso e]
  exact Submodule.subset_span ⟨_, rfl⟩

include k in
theorem mem_span_indec (x : K₀ 𝒞) :
    x ∈ Submodule.span ℤ (Set.range fun b : IndecClass 𝒞 => K₀.mk b.rep) := by
  induction x using K₀.induction_on with
  | mk X => exact mk_mem_span k X
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | neg x hx => exact Submodule.neg_mem _ hx

include k in
/-- The integral Krull–Schmidt basis of split `K₀` of an idempotent-complete category
satisfying `NilFinite`. -/
def indecBasis : Basis (IndecClass 𝒞) ℤ (K₀ 𝒞) :=
  Basis.mk (linearIndependent_indec k) fun x _ => mem_span_indec k x

@[simp] theorem indecBasis_apply (b : IndecClass 𝒞) : indecBasis k b = K₀.mk b.rep := by
  simp [indecBasis]

include k in
theorem free : Module.Free ℤ (K₀ 𝒞) := Module.Free.of_basis (indecBasis k)

end Basis

end OddMath.KrullSchmidtNil
