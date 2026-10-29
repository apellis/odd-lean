/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Preadditive.Mat
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SameColourBlocks

/-! # The augmented maps as morphisms of matrices

The augmented maps (1.13) and (1.14) of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Definition 1.5, are matrices of natural maps between the summand-path
functors. `PosInverse` and `NegInverse` (`SwappedAssembly/LeftwardInverse.lean`) state entry by
entry that given families invert them. Here the augmented maps are packaged as morphisms of the
additive envelope `Mat_ (P.H t)`, and an inverse there gives the families: this is the form in
which the block eliminations of `SwappedAssembly/CentralInverse/` produce inverses
(`docs/Nondegeneracy/AugmentedSectorBlocks.md` §3).

The summand paths form a finite type in the universe of the sectors, while `Mat_` indexes by
`Type`; the families are reindexed by `Fin` (`famObj`, `famHom`).

## Main results

* `exists_famInverse_of_isIso`: an inverse of `famHom a` in `Mat_ C` gives a family `b` with
  `Σ a b = δ` and `Σ b a = δ`.
* `ProbeReservoir.augPosMat`, `ProbeReservoir.augNegMat`: the augmented maps (1.13), (1.14).
* `ProbeReservoir.posInverse_of_isIso`, `ProbeReservoir.negInverse_of_isIso`: if they are
  isomorphisms at every object, `PosInverse`, resp. `NegInverse`, holds.
* `ProbeReservoir.centralInvertible_of_isIso`: `CentralInvertible` from the invertibility of
  the augmented maps at weight-matched equal sectors.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory

section FamilyMatrix

variable {C : Type*} [Category C] [Preadditive C]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The Kronecker family `δ_{x x'} : Xa x ⟶ Xa x'`. -/
def famId (Xa : α → C) (x x' : α) : Xa x ⟶ Xa x' :=
  if h : x = x' then eqToHom (congrArg Xa h) else 0

omit [Fintype α] in
@[simp] theorem famId_self (Xa : α → C) (x : α) : famId Xa x x = 𝟙 _ := by
  simp [famId]

omit [Fintype α] in
theorem famId_of_ne (Xa : α → C) {x x' : α} (h : x ≠ x') : famId Xa x x' = 0 := by
  simp [famId, h]

/-- A finite family of objects as an object of `Mat_ C`, indexed by `Fin (card α)`. -/
abbrev famObj (Xa : α → C) : Mat_ C where
  ι := Fin (Fintype.card α)
  X i := Xa ((Fintype.equivFin α).symm i)

/-- A matrix of morphisms between finite families as a morphism of `Mat_ C`. -/
def famHom {Xa : α → C} {Yb : β → C} (a : ∀ x y, Xa x ⟶ Yb y) : famObj Xa ⟶ famObj Yb :=
  fun _ _ => a _ _

omit [Preadditive C] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
private theorem conj_eq {Xa : α → C} {Yb : β → C} (a : ∀ x y, Xa x ⟶ Yb y) {x x₀ : α}
    {y y₀ : β} (hx : x₀ = x) (hy : y₀ = y) :
    a x y = eqToHom (congrArg Xa hx.symm) ≫ a x₀ y₀ ≫ eqToHom (congrArg Yb hy) := by
  subst hx hy; simp

/-- **Inverse families from an inverse in `Mat_ C`.** -/
theorem exists_famInverse_of_isIso {Xa : α → C} {Yb : β → C} (a : ∀ x y, Xa x ⟶ Yb y)
    [IsIso (famHom a)] :
    ∃ b : ∀ y x, Yb y ⟶ Xa x, (∀ x x', ∑ y, a x y ≫ b y x' = famId Xa x x') ∧
      (∀ y y', ∑ x, b y x ≫ a x y' = famId Yb y y') := by
  set eα := Fintype.equivFin α
  set eβ := Fintype.equivFin β
  set N := inv (famHom a)
  have hMN : famHom a ≫ N = 𝟙 _ := IsIso.hom_inv_id _
  have hNM : N ≫ famHom a = 𝟙 _ := IsIso.inv_hom_id _
  refine ⟨fun y x => eqToHom (congrArg Yb (eβ.symm_apply_apply y).symm) ≫ N (eβ y) (eα x) ≫
    eqToHom (congrArg Xa (eα.symm_apply_apply x)), fun x x' => ?_, fun y y' => ?_⟩
  · have e1 : ∀ y, a x y ≫ (eqToHom (congrArg Yb (eβ.symm_apply_apply y).symm) ≫
        N (eβ y) (eα x') ≫ eqToHom (congrArg Xa (eα.symm_apply_apply x'))) =
        eqToHom (congrArg Xa (eα.symm_apply_apply x).symm) ≫
          (famHom a (eα x) (eβ y) ≫ N (eβ y) (eα x')) ≫
          eqToHom (congrArg Xa (eα.symm_apply_apply x')) := by
      intro y
      rw [conj_eq a (eα.symm_apply_apply x) (eβ.symm_apply_apply y)]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rfl
    have hc : ∑ j, famHom a (eα x) j ≫ N j (eα x') = (𝟙 (famObj Xa) : _) (eα x) (eα x') := by
      rw [← hMN]; rfl
    rw [Finset.sum_congr rfl fun y _ => e1 y, ← Preadditive.comp_sum, ← Preadditive.sum_comp,
      Equiv.sum_comp eβ (fun j => famHom a (eα x) j ≫ N j (eα x')), hc, Mat_.id_apply]
    by_cases h : x = x'
    · subst h
      simp only [dite_true, eqToHom_refl, famId_self]
      erw [Category.id_comp, eqToHom_trans, eqToHom_refl]
    · have h' : eα x ≠ eα x' := fun e => h (eα.injective e)
      simp only [h', dite_false, Limits.zero_comp, Limits.comp_zero, famId_of_ne _ h]
  · have e1 : ∀ x, (eqToHom (congrArg Yb (eβ.symm_apply_apply y).symm) ≫ N (eβ y) (eα x) ≫
        eqToHom (congrArg Xa (eα.symm_apply_apply x))) ≫ a x y' =
        eqToHom (congrArg Yb (eβ.symm_apply_apply y).symm) ≫
          (N (eβ y) (eα x) ≫ famHom a (eα x) (eβ y')) ≫
          eqToHom (congrArg Yb (eβ.symm_apply_apply y')) := by
      intro x
      rw [conj_eq a (eα.symm_apply_apply x) (eβ.symm_apply_apply y')]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rfl
    have hc : ∑ j, N (eβ y) j ≫ famHom a j (eβ y') = (𝟙 (famObj Yb) : _) (eβ y) (eβ y') := by
      rw [← hNM]; rfl
    rw [Finset.sum_congr rfl fun x _ => e1 x, ← Preadditive.comp_sum, ← Preadditive.sum_comp,
      Equiv.sum_comp eα (fun j => N (eβ y) j ≫ famHom a j (eβ y')), hc, Mat_.id_apply]
    by_cases h : y = y'
    · subst h
      simp only [dite_true, eqToHom_refl, famId_self]
      erw [Category.id_comp, eqToHom_trans, eqToHom_refl]
    · have h' : eβ y ≠ eβ y' := fun e => h (eβ.injective e)
      simp only [h', dite_false, Limits.zero_comp, Limits.comp_zero, famId_of_ne _ h]

omit [Fintype α] [Fintype β] in
theorem famId_inl {Xa : α → C} {Yb : β → C} (x x' : α) :
    famId (Sum.elim Xa Yb) (Sum.inl x) (Sum.inl x') = famId Xa x x' := by
  by_cases h : x = x'
  · subst h; simp
  · rw [famId_of_ne _ h, famId_of_ne _ (by simpa using h)]

omit [Fintype α] [Fintype β] in
theorem famId_inr {Xa : α → C} {Yb : β → C} (y y' : β) :
    famId (Sum.elim Xa Yb) (Sum.inr y) (Sum.inr y') = famId Yb y y' := by
  by_cases h : y = y'
  · subst h; simp
  · rw [famId_of_ne _ h, famId_of_ne _ (by simpa using h)]

omit [Fintype α] [Fintype β] in
theorem famId_inl_inr {Xa : α → C} {Yb : β → C} (x : α) (y : β) :
    famId (Sum.elim Xa Yb) (Sum.inl x) (Sum.inr y) = 0 :=
  famId_of_ne _ (by simp)

omit [Fintype α] [Fintype β] in
theorem famId_inr_inl {Xa : α → C} {Yb : β → C} (x : α) (y : β) :
    famId (Sum.elim Xa Yb) (Sum.inr y) (Sum.inl x) = 0 :=
  famId_of_ne _ (by simp)

omit [Fintype α] [Fintype β] in
/-- The Kronecker family of copies of a family indexed by a second factor. -/
theorem famId_prod {Yb : β → C} (n n' : α) (y y' : β) :
    famId (fun ny : α × β => Yb ny.2) (n, y) (n', y') =
      if n = n' then famId Yb y y' else 0 := by
  by_cases hn : n = n'
  · subst hn
    by_cases hy : y = y'
    · subst hy; simp
    · rw [famId_of_ne _ (by simpa using hy), famId_of_ne _ hy]; simp
  · rw [famId_of_ne _ (by simp [hn])]; simp [hn]

end FamilyMatrix

open StringDiagrams OddMath.SKM

universe u

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

open Classical

variable (P : ProbeReservoir k B D Sc)

/-- **The augmented map (1.13)** `(σ, ε, ε x, …) : Eᵢ Fᵢ → Fᵢ Eᵢ ⊕ 1^{⟨hᵢ,ν⟩}` at the
object `Z`, as a morphism of `Mat_ (P.H t)` between the summand paths. -/
def augPosMat (c : P.CrossCoeff) (i : I) (ν : X) (t s : Sector I) (Z : P.H s) :
    letI := Fintype.ofFinite (SPath (wd D ν [up i, dn i]) t s)
    letI := Fintype.ofFinite (SPath (wd D ν [dn i, up i]) t s)
    letI := Fintype.ofFinite (SPath (wd D ν []) t s)
    famObj (fun p : SPath (wd D ν [up i, dn i]) t s => (P.pathFunctor p).obj Z) ⟶
      famObj (Sum.elim (fun q : SPath (wd D ν [dn i, up i]) t s => (P.pathFunctor q).obj Z)
        (fun nr : Fin (D.h i ν).toNat × SPath (wd D ν []) t s => (P.pathFunctor nr.2).obj Z)) :=
  letI := Fintype.ofFinite (SPath (wd D ν [up i, dn i]) t s)
  letI := Fintype.ofFinite (SPath (wd D ν [dn i, up i]) t s)
  letI := Fintype.ofFinite (SPath (wd D ν []) t s)
  famHom fun p y => match y with
    | .inl q => P.sigmaEntry c i i ν p q Z
    | .inr nr => P.epsEntry c i nr.1 ν p nr.2 Z

/-- **The augmented map (1.14)** `(-σ, η, x η, …) : Eᵢ Fᵢ ⊕ 1^{-⟨hᵢ,ν⟩} → Fᵢ Eᵢ` at the
object `Z`, as a morphism of `Mat_ (P.H t)` between the summand paths. -/
def augNegMat (c : P.CrossCoeff) (i : I) (ν : X) (t s : Sector I) (Z : P.H s) :
    letI := Fintype.ofFinite (SPath (wd D ν [up i, dn i]) t s)
    letI := Fintype.ofFinite (SPath (wd D ν [dn i, up i]) t s)
    letI := Fintype.ofFinite (SPath (wd D ν []) t s)
    famObj (Sum.elim (fun p : SPath (wd D ν [up i, dn i]) t s => (P.pathFunctor p).obj Z)
        (fun nr : Fin (-D.h i ν).toNat × SPath (wd D ν []) t s => (P.pathFunctor nr.2).obj Z)) ⟶
      famObj (fun q : SPath (wd D ν [dn i, up i]) t s => (P.pathFunctor q).obj Z) :=
  letI := Fintype.ofFinite (SPath (wd D ν [up i, dn i]) t s)
  letI := Fintype.ofFinite (SPath (wd D ν [dn i, up i]) t s)
  letI := Fintype.ofFinite (SPath (wd D ν []) t s)
  famHom fun y q => match y with
    | .inl p => -P.sigmaEntry c i i ν p q Z
    | .inr nr => P.etaEntry c i nr.1 ν nr.2 q Z

theorem famId_path {w : List (Col I X)} {t s : Sector I} (Z : P.H s) (p p' : SPath w t s) :
    famId (fun x : SPath w t s => (P.pathFunctor x).obj Z) p p' =
      famDelta (fun x => P.pathFunctor x) p p' Z := rfl

/-- **(1.13) invertible gives `PosInverse`.** -/
theorem posInverse_of_isIso (c : P.CrossCoeff) (i : I) (ν : X) (t s : Sector I)
    (h : ∀ Z, IsIso (P.augPosMat c i ν t s Z)) : ∃ lc dc, P.PosInverse c i ν t s lc dc := by
  let := Fintype.ofFinite (SPath (wd D ν [up i, dn i]) t s)
  let := Fintype.ofFinite (SPath (wd D ν [dn i, up i]) t s)
  let := Fintype.ofFinite (SPath (wd D ν []) t s)
  have key := fun Z => @exists_famInverse_of_isIso _ _ _ _ _ _ _ _ _ _ _ _ (h Z)
  choose b hb₁ hb₂ using key
  refine ⟨fun q p Z => -b Z (.inl q) p,
    fun n r p Z => if hn : n < (D.h i ν).toNat then b Z (.inr (⟨n, hn⟩, r)) p else 0,
    fun p p' Z => ?_, fun q q' Z => ?_, fun m hm q r Z => ?_, fun n hn r q Z => ?_,
    fun m n hm hn r r' Z => ?_⟩
  · have e := hb₁ Z p p'
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at e
    dsimp only at e
    rw [← famId_path, ← e, Finset.sum_range]
    simp only [Preadditive.comp_neg, Finset.sum_neg_distrib, neg_neg, Fin.is_lt,
      ↓reduceDIte, Fin.eta]
  · have e := hb₂ Z (.inl q) (.inl q')
    dsimp only at e
    rw [famId_inl] at e
    simp only [Preadditive.neg_comp, Finset.sum_neg_distrib, e, famId_path]
  · have e := hb₂ Z (.inl q) (.inr (⟨m, by omega⟩, r))
    dsimp only at e
    rw [famId_inl_inr] at e
    simp only [Preadditive.neg_comp, Finset.sum_neg_distrib, neg_eq_zero]
    exact e
  · have e := hb₂ Z (.inr (⟨n, by omega⟩, r)) (.inl q)
    dsimp only at e
    rw [famId_inr_inl] at e
    simp only [show n < (D.h i ν).toNat by omega, ↓reduceDIte]
    exact e
  · have e := hb₂ Z (.inr (⟨n, by omega⟩, r)) (.inr (⟨m, by omega⟩, r'))
    dsimp only at e
    rw [famId_inr, famId_prod (Yb := fun r => (P.pathFunctor r).obj Z)] at e
    simp only [show n < (D.h i ν).toNat by omega, ↓reduceDIte]
    rw [e]
    by_cases hmn : m = n
    · subst hmn; simp [famId_path]
    · simp only [Fin.mk.injEq, Ne.symm hmn, hmn, ite_false]

/-- **(1.14) invertible gives `NegInverse`.** -/
theorem negInverse_of_isIso (c : P.CrossCoeff) (i : I) (ν : X) (t s : Sector I)
    (h : ∀ Z, IsIso (P.augNegMat c i ν t s Z)) : ∃ lc dc, P.NegInverse c i ν t s lc dc := by
  let := Fintype.ofFinite (SPath (wd D ν [up i, dn i]) t s)
  let := Fintype.ofFinite (SPath (wd D ν [dn i, up i]) t s)
  let := Fintype.ofFinite (SPath (wd D ν []) t s)
  have key := fun Z => @exists_famInverse_of_isIso _ _ _ _ _ _ _ _ _ _ _ _ (h Z)
  choose b hb₁ hb₂ using key
  refine ⟨fun q p Z => b Z q (.inl p),
    fun n q r Z => if hn : n < (-D.h i ν).toNat then b Z q (.inr (⟨n, hn⟩, r)) else 0,
    fun q q' Z => ?_, fun p p' Z => ?_, fun m hm r p Z => ?_, fun n hn p r Z => ?_,
    fun m n hm hn r r' Z => ?_⟩
  · have e := hb₂ Z q q'
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at e
    dsimp only at e
    rw [← famId_path, ← e, Finset.sum_range]
    simp only [Preadditive.comp_neg, Finset.sum_neg_distrib, Fin.is_lt, ↓reduceDIte, Fin.eta]
  · have e := hb₁ Z (.inl p) (.inl p')
    dsimp only at e
    rw [famId_inl] at e
    simp only [Preadditive.neg_comp, Finset.sum_neg_distrib] at e
    rw [← famId_path, ← e, neg_neg]
  · have e := hb₁ Z (.inr (⟨m, by omega⟩, r)) (.inl p)
    dsimp only at e
    rw [famId_inr_inl] at e
    exact e
  · have e := hb₁ Z (.inl p) (.inr (⟨n, by omega⟩, r))
    dsimp only at e
    rw [famId_inl_inr] at e
    simp only [Preadditive.neg_comp, Finset.sum_neg_distrib, neg_eq_zero] at e
    simp only [show n < (-D.h i ν).toNat by omega, ↓reduceDIte]
    exact e
  · have e := hb₁ Z (.inr (⟨m, by omega⟩, r)) (.inr (⟨n, by omega⟩, r'))
    dsimp only at e
    rw [famId_inr, famId_prod (Yb := fun r => (P.pathFunctor r).obj Z)] at e
    simp only [show n < (-D.h i ν).toNat by omega, ↓reduceDIte]
    rw [e]
    by_cases hmn : m = n
    · subst hmn; simp [famId_path]
    · simp only [Fin.mk.injEq, hmn, ite_false]

/-- **`CentralInvertible` from invertible augmented matrices** at weight-matched equal
sectors. -/
theorem centralInvertible_of_isIso (c : P.CrossCoeff)
    (h : ∀ (i : I) (ν : X) (t : Sector I), P.wt t = ν →
      (0 ≤ D.h i ν → ∀ Z, IsIso (P.augPosMat c i ν t t Z)) ∧
      (D.h i ν < 0 → ∀ Z, IsIso (P.augNegMat c i ν t t Z))) :
    P.CentralInvertible c := fun i ν t ht =>
  ⟨fun hh => P.posInverse_of_isIso c i ν t t ((h i ν t ht).1 hh),
    fun hh => P.negInverse_of_isIso c i ν t t ((h i ν t ht).2 hh)⟩

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
