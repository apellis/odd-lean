/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.IdempotentSummands

/-!
# Retracts and maps between shifted summands

Two pieces of Krull–Schmidt bookkeeping used in the surjectivity half of Brundan–Ellis,
arXiv:1701.04133v2, Theorem 11.3 (Khovanov–Lauda, arXiv:0803.4121v2, §3.2, in the even case).

* In a `k`-linear Hom-finite category over a field: if `1_Y = ∑_j u_j v_j` with `Y`
  indecomposable, then `Y` is a retract of one of the objects the sum passes through
  (`exists_retract_of_sum`, the endomorphism ring of `Y` being local); every object is a finite
  direct sum of indecomposable retracts (`exists_decomposition`); so a subgroup of `K₀`
  containing the classes of the indecomposable retracts of `X` contains `[X]`
  (`mk_mem_of_indec_retracts`).
* In the completed category `Kar(Mat(A̲_{q,π}))` of a graded supercategory `A`: morphisms
  between summands `Q^m Π^p (f, e) → Q^n Π^{p'} (g, e')` are the homogeneous maps `x : f → g`
  of degree `m - n` and parity `p + p'` with `e x e' = x` (`homR`, `evR`), and every object is a
  retract of a finite sum of shifted objects `Q^n Π^p f` (`sum_unitRaw`).
-/

noncomputable section

namespace OddMath.SKM.Summands

open CategoryTheory StringDiagrams GradedSupercategory KrullSchmidt
open CategoryTheory.Idempotents CategoryTheory.Limits

universe u v w

/-! ### Generic Krull–Schmidt facts -/

section Generic

variable {C : Type*} [Category C] [Preadditive C]

/-- **Indecomposables are retracts of a summand.** If `Y` is indecomposable and
`1_Y = ∑_{j ∈ s} u_j v_j`, then `Y` is a retract of one of the `X_j`, through `u_j`. -/
theorem exists_retract_of_sum (k : Type*) [Field k] [Linear k C] [HomFinite k C] {Y : C}
    (hY : IsIndec Y) {J : Type*} (s : Finset J) {X : J → C} (u : ∀ j, Y ⟶ X j)
    (v : ∀ j, X j ⟶ Y) (h : ∑ j ∈ s, u j ≫ v j = 𝟙 Y) :
    ∃ j ∈ s, ∃ v' : X j ⟶ Y, u j ≫ v' = 𝟙 Y := by
  classical
  have := hY.isLocalRing k
  have := hY.nontrivial
  by_contra hne
  let α : J → End Y := fun j => u j ≫ v j
  have hnu : ∀ j ∈ s, ¬ IsUnit (α j) := by
    rintro j hj ⟨w, hw⟩
    refine hne ⟨j, hj, v j ≫ w.inv, ?_⟩
    rw [← Category.assoc]
    change α j ≫ w.inv = 𝟙 Y
    rw [← hw]
    exact w.inv_mul
  have key : ∀ t ⊆ s, ¬ IsUnit (∑ j ∈ t, α j) := by
    intro t ht
    induction t using Finset.induction_on with
    | empty => rw [Finset.sum_empty]; exact not_isUnit_zero
    | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact nonunits_add' (hnu a (ht (Finset.mem_insert_self a t)))
        (ih ((Finset.subset_insert a t).trans ht))
  exact key s le_rfl (h ▸ isUnit_one)

/-- **Krull–Schmidt decompositions as orthogonal families of retractions.** -/
theorem exists_decomposition (k : Type*) [Field k] [Linear k C] [HomFinite k C]
    [IsIdempotentComplete C] (X : C) :
    ∃ (J : Type) (_ : Fintype J) (Z : J → C) (ι : ∀ a, Z a ⟶ X) (π : ∀ a, X ⟶ Z a),
      (∀ a, IsIndec (Z a)) ∧ (∀ a, ι a ≫ π a = 𝟙 (Z a)) ∧
      (∀ a b, a ≠ b → ι a ≫ π b = 0) ∧ ∑ a, π a ≫ ι a = 𝟙 X := by
  induction h : Module.finrank k (X ⟶ X) using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    by_cases h0 : IsZero X
    · refine ⟨Empty, inferInstance, Empty.elim, fun a => a.elim, fun a => a.elim,
        fun a => a.elim, fun a => a.elim, fun a => a.elim, ?_⟩
      rw [Finset.univ_eq_empty, Finset.sum_empty]
      exact h0.eq_of_src _ _
    by_cases hi : IsIndec X
    · refine ⟨Unit, inferInstance, fun _ => X, fun _ => 𝟙 X, fun _ => 𝟙 X, fun _ => hi,
        fun _ => Category.comp_id _, fun a b hab => absurd (Subsingleton.elim a b) hab, ?_⟩
      rw [Fintype.sum_unique, Category.comp_id]
    obtain ⟨e, he, he0, he1⟩ : ∃ e : X ⟶ X, e ≫ e = e ∧ e ≠ 0 ∧ e ≠ 𝟙 X := by
      by_contra hne
      exact hi ⟨h0, fun e he => by
        by_cases h' : e = 0
        · exact Or.inl h'
        · by_cases h'' : e = 𝟙 X
          · exact Or.inr h''
          · exact absurd ⟨e, he, h', h''⟩ hne⟩
    obtain ⟨Y, Z, i, p, i', p', h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_split e he
    have hY : ¬ IsZero Y := fun hY => he0 (by rw [← h₅, hY.eq_of_src i, Limits.comp_zero])
    have hZ : ¬ IsZero Z := fun hZ => he1 (by
      have : 𝟙 X - e = 0 := by rw [← h₆, hZ.eq_of_src i', Limits.comp_zero]
      exact (sub_eq_zero.1 this).symm)
    obtain ⟨J₁, _, Z₁, ι₁, π₁, hi₁, hs₁, ho₁, ht₁⟩ :=
      ih _ (by rw [← h]; exact finrank_end_lt k i p i' p' h₁ h₂ h₃ h₄ hZ) Y rfl
    obtain ⟨J₂, _, Z₂, ι₂, π₂, hi₂, hs₂, ho₂, ht₂⟩ :=
      ih _ (by rw [← h]; exact finrank_end_lt k i' p' i p h₂ h₁ h₄ h₃ hY) Z rfl
    refine ⟨J₁ ⊕ J₂, inferInstance, Sum.elim Z₁ Z₂,
      fun a => match a with
        | .inl a => ι₁ a ≫ i
        | .inr b => ι₂ b ≫ i',
      fun a => match a with
        | .inl a => p ≫ π₁ a
        | .inr b => p' ≫ π₂ b, ?_, ?_, ?_, ?_⟩
    · rintro (a | b)
      · exact hi₁ a
      · exact hi₂ b
    · rintro (a | b)
      · change (ι₁ a ≫ i) ≫ p ≫ π₁ a = _
        rw [Category.assoc, reassoc_of% h₁, hs₁]; rfl
      · change (ι₂ b ≫ i') ≫ p' ≫ π₂ b = _
        rw [Category.assoc, reassoc_of% h₂, hs₂]; rfl
    · rintro (a | b) (a' | b') hab
      · change (ι₁ a ≫ i) ≫ p ≫ π₁ a' = 0
        rw [Category.assoc, reassoc_of% h₁]
        exact ho₁ a a' (fun h' => hab (congrArg Sum.inl h'))
      · change (ι₁ a ≫ i) ≫ p' ≫ π₂ b' = 0
        rw [Category.assoc, reassoc_of% h₃, zero_comp, comp_zero]
      · change (ι₂ b ≫ i') ≫ p ≫ π₁ a' = 0
        rw [Category.assoc, reassoc_of% h₄, zero_comp, comp_zero]
      · change (ι₂ b ≫ i') ≫ p' ≫ π₂ b' = 0
        rw [Category.assoc, reassoc_of% h₂]
        exact ho₂ b b' (fun h' => hab (congrArg Sum.inr h'))
    · rw [Fintype.sum_sum_type]
      change ∑ a, (p ≫ π₁ a) ≫ ι₁ a ≫ i + ∑ b, (p' ≫ π₂ b) ≫ ι₂ b ≫ i' = 𝟙 X
      simp only [Category.assoc]
      rw [← Preadditive.comp_sum, ← Preadditive.comp_sum]
      simp only [← Category.assoc]
      rw [← Preadditive.sum_comp, ← Preadditive.sum_comp, ht₁, ht₂, Category.id_comp,
        Category.id_comp, h₅, h₆, add_sub_cancel]

theorem IsIndec.of_iso {Y Y' : C} (φ : Y ≅ Y') (h : IsIndec Y) : IsIndec Y' := by
  refine ⟨fun hz => h.1 (hz.of_iso φ), fun e he => ?_⟩
  rcases h.2 (φ.hom ≫ e ≫ φ.inv) (by simp [reassoc_of% he]) with h0 | h1
  · left
    have := congrArg (fun x => φ.inv ≫ x ≫ φ.hom) h0
    simpa using this
  · right
    have := congrArg (fun x => φ.inv ≫ x ≫ φ.hom) h1
    simpa using this

/-- A subgroup of `K₀` containing the classes of the indecomposable retracts of `X` contains
`[X]`. -/
theorem mk_mem_of_indec_retracts (k : Type*) [Field k] [Linear k C] [HomFinite k C]
    [IsIdempotentComplete C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
    (S : AddSubgroup (K₀ C)) (X : C)
    (h : ∀ Y : C, IsIndec Y → ∀ (u : Y ⟶ X) (v : X ⟶ Y), u ≫ v = 𝟙 Y → K₀.mk Y ∈ S) :
    K₀.mk X ∈ S := by
  classical
  obtain ⟨J, _, Z, ι, π, hi, hs, ho, ht⟩ := exists_decomposition k X
  rw [mk_of_total Z π ι hs ho ht]
  exact S.sum_mem fun a _ => h (Z a) (hi a) (ι a) (π a) (hs a)

end Generic

/-! ### Maps between shifted summands -/

variable {k : Type w} [CommRing k] {A : Type u} [Category.{v} A] [Preadditive A] [Linear k A]
  [Supercategory k A] [GradedSupercategory k A]

section Shifted

variable {f g h : A} {m n l : ℤ} {p p' p'' : ZMod 2}

/-- A homogeneous map `x : f → g` of degree `m - n` and parity `p + p'`, as an even
degree-zero morphism `Q^m Π^p f → Q^n Π^{p'} g`. -/
def liftH (x : f ⟶ g) (hd : x ∈ degree (R := k) f g (m - n))
    (hp : x ∈ Supercategory.parity (R := k) f g (p + p')) :
    shifted (k := k) f m p ⟶ shifted (k := k) g n p' :=
  ⟨⟨x, by change x ∈ degree (R := k) _ _ (0 + (m - n)); simpa using hd⟩,
    by change x ∈ Supercategory.parity (R := k) _ _ (0 + (p + p')); simpa using hp⟩

/-- The underlying map of a morphism of shifts. -/
def valH (x : shifted (k := k) f m p ⟶ shifted (k := k) g n p') : f ⟶ g := x.1.1

@[simp] theorem valH_liftH (x : f ⟶ g) (hd hp) :
    valH (liftH (k := k) (m := m) (n := n) (p := p) (p' := p') x hd hp) = x := rfl

theorem valH_comp (x : shifted (k := k) f m p ⟶ shifted (k := k) g n p')
    (y : shifted (k := k) g n p' ⟶ shifted (k := k) h l p'') :
    valH (x ≫ y) = valH x ≫ valH y := rfl

theorem valH_id : valH (𝟙 (shifted (k := k) f m p)) = 𝟙 f := rfl

theorem valH_add (x y : shifted (k := k) f m p ⟶ shifted (k := k) g n p') :
    valH (x + y) = valH x + valH y := rfl

theorem valH_zero : valH (0 : shifted (k := k) f m p ⟶ shifted (k := k) g n p') = 0 := rfl

theorem valH_injective :
    Function.Injective (valH (k := k) (f := f) (g := g) (m := m) (n := n) (p := p) (p' := p')) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem valH_mem_degree (x : shifted (k := k) f m p ⟶ shifted (k := k) g n p') :
    valH x ∈ degree (R := k) f g (m - n) := by
  have h := x.1.2
  change x.1.1 ∈ degree (R := k) f g (0 + (m - n)) at h
  rw [zero_add] at h
  exact h

theorem valH_mem_parity (x : shifted (k := k) f m p ⟶ shifted (k := k) g n p') :
    valH x ∈ Supercategory.parity (R := k) f g (p + p') := by
  have h := x.2
  change x.1.1 ∈ Supercategory.parity (R := k) f g (0 + (p + p')) at h
  rw [zero_add] at h
  exact h

end Shifted

section Raw

variable {f g h : A} {e : f ⟶ f} {e' : g ⟶ g} {e'' : h ⟶ h}
  {he : e ≫ e = e} {hd0 : e ∈ degree (R := k) f f 0}
  {hp0 : e ∈ Supercategory.parity (R := k) f f 0}
  {he' : e' ≫ e' = e'} {hd0' : e' ∈ degree (R := k) g g 0}
  {hp0' : e' ∈ Supercategory.parity (R := k) g g 0}
  {he'' : e'' ≫ e'' = e''} {hd0'' : e'' ∈ degree (R := k) h h 0}
  {hp0'' : e'' ∈ Supercategory.parity (R := k) h h 0}
  {m n l : ℤ} {p p' p'' : ZMod 2}

/-- The map `Q^m Π^p (f, e) → Q^n Π^{p'} (g, e')` given by a homogeneous `x : f → g` of degree
`m - n` and parity `p + p'` with `e x e' = x`. -/
def homR (x : f ⟶ g) (hd : x ∈ degree (R := k) f g (m - n))
    (hp : x ∈ Supercategory.parity (R := k) f g (p + p')) (hx : e ≫ x ≫ e' = x) :
    raw he hd0 hp0 m p ⟶ raw he' hd0' hp0' n p' where
  f := (Mat_.embedding _).map (liftH x hd hp)
  comm := by
    change (Mat_.embedding _).map (projector hd0 hp0 m p) ≫ (Mat_.embedding _).map _ ≫
      (Mat_.embedding _).map (projector hd0' hp0' n p') = _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (valH_injective hx)

/-- The underlying map of a morphism of summands. -/
def evR (φ : raw he hd0 hp0 m p ⟶ raw he' hd0' hp0' n p') : f ⟶ g :=
  valH (k := k) (m := m) (n := n) (p := p) (p' := p') (φ.f PUnit.unit PUnit.unit)

theorem evR_homR (x : f ⟶ g) (hd hp hx) :
    evR (homR (he := he) (hd0 := hd0) (hp0 := hp0) (he' := he') (hd0' := hd0') (hp0' := hp0')
      (m := m) (n := n) (p := p) (p' := p') x hd hp hx) = x := rfl

theorem evR_comp (φ : raw he hd0 hp0 m p ⟶ raw he' hd0' hp0' n p')
    (ψ : raw he' hd0' hp0' n p' ⟶ raw he'' hd0'' hp0'' l p'') :
    evR (φ ≫ ψ) = evR φ ≫ evR ψ := by
  have : Unique (raw he' hd0' hp0' n p').X.ι := inferInstanceAs (Unique PUnit)
  change valH ((φ.f ≫ ψ.f) PUnit.unit PUnit.unit) = _
  rw [Mat_.comp_apply, Fintype.sum_unique]
  rfl

theorem evR_id : evR (𝟙 (raw he hd0 hp0 m p)) = e := rfl

theorem evR_add (φ ψ : raw he hd0 hp0 m p ⟶ raw he' hd0' hp0' n p') :
    evR (φ + ψ) = evR φ + evR ψ := rfl

theorem evR_zero : evR (0 : raw he hd0 hp0 m p ⟶ raw he' hd0' hp0' n p') = 0 := rfl

/-- `evR` as an additive map. -/
def evRHom : (raw he hd0 hp0 m p ⟶ raw he' hd0' hp0' n p') →+ (f ⟶ g) where
  toFun := evR
  map_zero' := evR_zero
  map_add' := evR_add

theorem evR_sum {J : Type*} (s : Finset J) (φ : J → (raw he hd0 hp0 m p ⟶ raw he' hd0' hp0' n p')) :
    evR (∑ j ∈ s, φ j) = ∑ j ∈ s, evR (φ j) :=
  map_sum (evRHom (he := he) (hd0 := hd0) (hp0 := hp0) (he' := he') (hd0' := hd0')
    (hp0' := hp0') (m := m) (n := n) (p := p) (p' := p')) φ s

theorem evR_injective :
    Function.Injective (evR (he := he) (hd0 := hd0) (hp0 := hp0) (he' := he') (hd0' := hd0')
      (hp0' := hp0') (m := m) (n := n) (p := p) (p' := p')) := by
  intro φ ψ hφψ
  apply Karoubi.hom_ext
  funext a b
  cases a; cases b
  exact valH_injective hφψ

theorem evR_mem_degree (φ : raw he hd0 hp0 m p ⟶ raw he' hd0' hp0' n p') :
    evR φ ∈ degree (R := k) f g (m - n) :=
  valH_mem_degree _

theorem evR_mem_parity (φ : raw he hd0 hp0 m p ⟶ raw he' hd0' hp0' n p') :
    evR φ ∈ Supercategory.parity (R := k) f g (p + p') :=
  valH_mem_parity _

theorem evR_corner (φ : raw he hd0 hp0 m p ⟶ raw he' hd0' hp0' n p') :
    e ≫ evR φ ≫ e' = evR φ := by
  have h := congrArg evR (show 𝟙 _ ≫ φ ≫ 𝟙 _ = φ by simp)
  rwa [evR_comp, evR_comp, evR_id, evR_id] at h

theorem homR_evR (φ : raw he hd0 hp0 m p ⟶ raw he' hd0' hp0' n p') :
    homR (evR φ) (evR_mem_degree φ) (evR_mem_parity φ) (evR_corner φ) = φ :=
  evR_injective rfl

theorem homR_zero (hd hp hx) :
    (homR (0 : f ⟶ g) hd hp hx : raw he hd0 hp0 m p ⟶ raw he' hd0' hp0' n p') = 0 :=
  evR_injective rfl

/-! #### Retracts of a summand -/

section Retract

variable {Z : Karoubi (Mat_ (Base k A))} (ι : Z ⟶ raw he hd0 hp0 m p)
  (π : raw he hd0 hp0 m p ⟶ Z)

theorem retract_idem (h : ι ≫ π = 𝟙 Z) : evR (π ≫ ι) ≫ evR (π ≫ ι) = evR (π ≫ ι) := by
  rw [← evR_comp]
  congr 1
  simp only [Category.assoc]
  rw [reassoc_of% h]

theorem retract_degree : evR (π ≫ ι) ∈ degree (R := k) f f 0 := by
  simpa using evR_mem_degree (π ≫ ι)

theorem retract_parity : evR (π ≫ ι) ∈ Supercategory.parity (R := k) f f 0 := by
  have := evR_mem_parity (π ≫ ι)
  rwa [Supercategory.zmod2_add_self] at this

theorem retract_left : e ≫ evR (π ≫ ι) = evR (π ≫ ι) := by
  conv_lhs => rw [← evR_corner (π ≫ ι)]
  rw [← Category.assoc, he]
  exact evR_corner (π ≫ ι)

theorem retract_right : evR (π ≫ ι) ≫ e = evR (π ≫ ι) := by
  conv_lhs => rw [← evR_corner (π ≫ ι)]
  simp only [Category.assoc, he]
  exact evR_corner (π ≫ ι)

/-- A retract `Z` of `Q^m Π^p (f, e)` is `Q^m Π^p (f, g)`, `g = π ι`. -/
def retractIso (h : ι ≫ π = 𝟙 Z) :
    Z ≅ raw (retract_idem ι π h) (retract_degree ι π) (retract_parity ι π) m p where
  hom := ι ≫ homR (evR (π ≫ ι)) (by simpa using retract_degree ι π)
    (by rw [Supercategory.zmod2_add_self]; exact retract_parity ι π)
    (by rw [retract_idem ι π h, retract_left ι π])
  inv := homR (evR (π ≫ ι)) (by simpa using retract_degree ι π)
    (by rw [Supercategory.zmod2_add_self]; exact retract_parity ι π)
    (by rw [reassoc_of% retract_idem ι π h, retract_right ι π]) ≫ π
  hom_inv_id := by
    have e : homR (evR (π ≫ ι)) (by simpa using retract_degree ι π)
        (by rw [Supercategory.zmod2_add_self]; exact retract_parity ι π)
        (by rw [retract_idem ι π h, retract_left ι π]) ≫
        (homR (evR (π ≫ ι)) (by simpa using retract_degree ι π)
          (by rw [Supercategory.zmod2_add_self]; exact retract_parity ι π)
          (by rw [reassoc_of% retract_idem ι π h, retract_right ι π]) :
          raw (retract_idem ι π h) (retract_degree ι π) (retract_parity ι π) m p ⟶ _) =
        π ≫ ι :=
      evR_injective (by rw [evR_comp, evR_homR, evR_homR, retract_idem ι π h])
    simp only [Category.assoc]
    rw [reassoc_of% e, reassoc_of% h, h]
  inv_hom_id := by
    apply evR_injective
    rw [Category.assoc, ← Category.assoc π, evR_comp, evR_comp]
    change evR (π ≫ ι) ≫ evR (π ≫ ι) ≫ evR (π ≫ ι) = evR (π ≫ ι)
    rw [retract_idem ι π h, retract_idem ι π h]

end Retract

/-- An orthogonal decomposition `e = f₁ + f₂` of idempotents splits the summand. -/
theorem mk_raw_eq_add [Limits.HasBinaryBiproducts (Karoubi (Mat_ (Base k A)))] {f₁ f₂ : f ⟶ f}
    (h₁ : f₁ ≫ f₁ = f₁) (h₂ : f₂ ≫ f₂ = f₂) (h₁₂ : f₁ ≫ f₂ = 0) (h₂₁ : f₂ ≫ f₁ = 0)
    (hs : f₁ + f₂ = e) (hd₁ : f₁ ∈ degree (R := k) f f 0)
    (hp₁ : f₁ ∈ Supercategory.parity (R := k) f f 0) (hd₂ : f₂ ∈ degree (R := k) f f 0)
    (hp₂ : f₂ ∈ Supercategory.parity (R := k) f f 0) :
    K₀.mk (raw he hd0 hp0 m p) = K₀.mk (raw h₁ hd₁ hp₁ m p) + K₀.mk (raw h₂ hd₂ hp₂ m p) := by
  have l₁ : e ≫ f₁ = f₁ := by rw [← hs, Preadditive.add_comp, h₁, h₂₁, add_zero]
  have r₁ : f₁ ≫ e = f₁ := by rw [← hs, Preadditive.comp_add, h₁, h₁₂, add_zero]
  have l₂ : e ≫ f₂ = f₂ := by rw [← hs, Preadditive.add_comp, h₂, h₁₂, zero_add]
  have r₂ : f₂ ≫ e = f₂ := by rw [← hs, Preadditive.comp_add, h₂, h₂₁, zero_add]
  have hd₁' : f₁ ∈ degree (R := k) f f (m - m) := by simpa using hd₁
  have hd₂' : f₂ ∈ degree (R := k) f f (m - m) := by simpa using hd₂
  have hp₁' : f₁ ∈ Supercategory.parity (R := k) f f (p + p) := by
    rwa [Supercategory.zmod2_add_self]
  have hp₂' : f₂ ∈ Supercategory.parity (R := k) f f (p + p) := by
    rwa [Supercategory.zmod2_add_self]
  let i : raw h₁ hd₁ hp₁ m p ⟶ raw he hd0 hp0 m p :=
    homR f₁ hd₁' hp₁' (by rw [reassoc_of% h₁, r₁])
  let q : raw he hd0 hp0 m p ⟶ raw h₁ hd₁ hp₁ m p :=
    homR f₁ hd₁' hp₁' (by rw [h₁, l₁])
  let i' : raw h₂ hd₂ hp₂ m p ⟶ raw he hd0 hp0 m p :=
    homR f₂ hd₂' hp₂' (by rw [reassoc_of% h₂, r₂])
  let q' : raw he hd0 hp0 m p ⟶ raw h₂ hd₂ hp₂ m p :=
    homR f₂ hd₂' hp₂' (by rw [h₂, l₂])
  rw [K₀.mk_eq_mk_of_iso (isoOfData i q i' q' (evR_injective (by rw [evR_comp]; exact h₁))
    (evR_injective (by rw [evR_comp]; exact h₂)) (evR_injective (by rw [evR_comp]; exact h₁₂))
    (evR_injective (by rw [evR_comp]; exact h₂₁))
    (evR_injective (by
      rw [evR_add, evR_comp, evR_comp]; exact (congrArg₂ (· + ·) h₁ h₂).trans hs))),
    K₀.mk_biprod]

end Raw

/-! ### Every object is a retract of shifted objects -/

section Unit

variable (f : A)

/-- The shifted object `Q^n Π^p f` as a summand with the identity idempotent. -/
abbrev unitRaw (n : ℤ) (p : ZMod 2) : Karoubi (Mat_ (Base k A)) :=
  raw (Category.id_comp (𝟙 f)) (GradedSupercategory.id_mem_degree (R := k) f)
    (Supercategory.id_mem (R := k) f) n p

end Unit

theorem unitRaw_p (f : A) (n : ℤ) (p : ZMod 2) :
    (unitRaw (k := k) f n p).p = 𝟙 _ := by
  change (Mat_.embedding _).map (𝟙 _) = _
  exact (Mat_.embedding _).map_id _

/-- The projection of a matrix object onto a summand. -/
def matπ {C : Type*} [Category C] [Preadditive C] (M : Mat_ C) (j : M.ι) :
    M ⟶ (Mat_.embedding C).obj (M.X j) := fun a _ => (𝟙 M : M ⟶ M) a j

/-- The inclusion of a summand into a matrix object. -/
def matι {C : Type*} [Category C] [Preadditive C] (M : Mat_ C) (j : M.ι) :
    (Mat_.embedding C).obj (M.X j) ⟶ M := fun _ b => (𝟙 M : M ⟶ M) j b

theorem sum_matπ_matι {C : Type*} [Category C] [Preadditive C] (M : Mat_ C) :
    ∑ j, matπ M j ≫ matι M j = 𝟙 M := by
  have : ∀ j, Unique ((Mat_.embedding C).obj (M.X j)).ι := fun _ => inferInstanceAs (Unique PUnit)
  funext a b
  rw [← Category.comp_id (𝟙 M), Mat_.comp_apply, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Mat_.comp_apply, Fintype.sum_unique]
  rfl

/-- **Every object is a retract of a finite sum of shifted objects**: for `Y` in
`Kar(Mat(A̲_{q,π}))` there are maps `u_j : Y → Q^{n_j} Π^{p_j} f_j`, `v_j` back, with
`1_Y = ∑_j u_j v_j`. -/
theorem sum_unitRaw (Y : Karoubi (Mat_ (Base k A))) :
    ∃ (J : Type) (_ : Fintype J) (f : J → A) (n : J → ℤ) (p : J → ZMod 2)
      (u : ∀ j, Y ⟶ unitRaw (f j) (n j) (p j)) (v : ∀ j, unitRaw (f j) (n j) (p j) ⟶ Y),
      ∑ j, u j ≫ v j = 𝟙 Y := by
  classical
  let B := Y.X.X
  refine ⟨Y.X.ι, inferInstance, fun j => (B j).obj.obj.obj.obj, fun j => (B j).obj.obj.obj.shift,
    fun j => (B j).obj.obj.par, fun j => ⟨Y.p ≫ matπ Y.X j, ?_⟩,
    fun j => ⟨matι Y.X j ≫ Y.p, ?_⟩, ?_⟩
  · rw [unitRaw_p, Category.comp_id, ← Category.assoc, Y.idem]
  · rw [unitRaw_p, Category.id_comp, Category.assoc, Y.idem]
  · apply Karoubi.hom_ext
    rw [Karoubi.sum_hom, Karoubi.id_f]
    simp only [Karoubi.comp_f, Category.assoc]
    rw [← Preadditive.comp_sum]
    simp only [← Category.assoc]
    rw [← Preadditive.sum_comp, sum_matπ_matι, Category.id_comp, Y.idem]

end OddMath.SKM.Summands
