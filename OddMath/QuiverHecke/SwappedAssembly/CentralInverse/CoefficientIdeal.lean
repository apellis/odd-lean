/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.NilpotentLifting
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.BlockMaps

/-! # Lifting along a jointly nilpotent coefficient ideal

`docs/Nondegeneracy/SwappedHomInversion.md` §4 works modulo the two-sided ideal `J` generated
by the positive-degree closed reservoir coefficients: products of more than `M_β` of them vanish
(after moving them past probe words), so `J` is a jointly nilpotent *matrix* ideal on the
finitely many probe objects, not merely entrywise nilpotent. This file records that structure
abstractly and proves the lifting step used with it ((12) there): a matrix of probe morphisms
which differs from an invertible one by a matrix with entries in `J` is invertible.

## Main definitions and results

* `ProbeWindow.CoefficientIdeal`: a decreasing filtration `J₀ ⊇ J₁ ⊇ …` of morphisms of `C`
  by additive subgroups with `Jₘ ≫ Jₙ ⊆ Jₘ₊ₙ` and `J_bound = 0`. Nothing is assumed about
  `J₀`: membership in `J₀` is an explicit hypothesis on exactly the morphisms the lifting step
  multiplies by (the entries of the inverse of the comparison map).
* `ProbeWindow.CoefficientIdeal.isNilpotent`: an endomorphism in `Mat_ C` with entries in `J₁`
  is nilpotent.
* `ProbeWindow.CoefficientIdeal.isIso_of_sub_mem`: if `G` is invertible, `G⁻¹` has entries in
  `J₀` and `F - G` has entries in `J₁`, then `F` is invertible.
* `ProbeWindow.CoefficientIdeal.isIso_gMap_of_sub_mem`: the same for the block maps
  `ProbeWindow.gMap`, blockwise.
-/

namespace OddMath.QuiverHecke.SwappedAssembly.ProbeWindow

open CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

/-- A jointly nilpotent filtration of morphisms (`SwappedHomInversion.md` §4): `mem n f` says
that `f` is a sum of terms with at least `n` positive-degree reservoir coefficients. -/
structure CoefficientIdeal (C : Type*) [Category C] [Preadditive C] where
  /-- `f` lies in filtration level `n`; equality with a literal ideal power is not required. -/
  mem : ℕ → ∀ {X Y : C}, (X ⟶ Y) → Prop
  zero_mem : ∀ (n : ℕ) {X Y : C}, mem n (0 : X ⟶ Y)
  add_mem : ∀ {n : ℕ} {X Y : C} {f g : X ⟶ Y}, mem n f → mem n g → mem n (f + g)
  neg_mem : ∀ {n : ℕ} {X Y : C} {f : X ⟶ Y}, mem n f → mem n (-f)
  /-- The filtration is decreasing. -/
  mono : ∀ {n : ℕ} {X Y : C} {f : X ⟶ Y}, mem (n + 1) f → mem n f
  comp_mem : ∀ {m n : ℕ} {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}, mem m f → mem n g →
    mem (m + n) (f ≫ g)
  /-- The nilpotence bound (`M_β + 1` there). -/
  bound : ℕ
  eq_zero : ∀ {X Y : C} {f : X ⟶ Y}, mem bound f → f = 0

namespace CoefficientIdeal

variable (J : CoefficientIdeal C)

lemma sum_mem {n : ℕ} {X Y : C} {ι : Type*} (s : Finset ι) {f : ι → (X ⟶ Y)}
    (h : ∀ i ∈ s, J.mem n (f i)) : J.mem n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using J.zero_mem n
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact J.add_mem (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma zsmul_mem {n : ℕ} {X Y : C} {f : X ⟶ Y} (hf : J.mem n f) (c : ℤ) : J.mem n (c • f) := by
  induction c using Int.induction_on with
  | zero => simpa using J.zero_mem n
  | succ c ih => rw [add_smul, one_smul]; exact J.add_mem ih hf
  | pred c ih => rw [sub_smul, one_smul, sub_eq_add_neg]; exact J.add_mem ih (J.neg_mem hf)

lemma sub_mem {n : ℕ} {X Y : C} {f g : X ⟶ Y} (hf : J.mem n f) (hg : J.mem n g) :
    J.mem n (f - g) := by
  rw [sub_eq_add_neg]; exact J.add_mem hf (J.neg_mem hg)

lemma mono_le {m n : ℕ} (h : m ≤ n) {X Y : C} {f : X ⟶ Y} (hf : J.mem n f) : J.mem m f := by
  induction n, h using Nat.le_induction with
  | base => exact hf
  | succ n _ ih => exact ih (J.mono hf)

lemma matSub_apply {M N : Mat_ C} (f g : M ⟶ N) (i j) : (f - g) i j = f i j - g i j := by
  rw [eq_sub_iff_add_eq, ← Mat_.add_apply, sub_add_cancel]

lemma matNeg_apply {M N : Mat_ C} (f : M ⟶ N) (i j) : (-f) i j = -(f i j) := by
  rw [eq_neg_iff_add_eq_zero, ← Mat_.add_apply, neg_add_cancel]
  rfl

lemma mem_comp_apply {m n : ℕ} {L M N : Mat_ C} (f : L ⟶ M) (g : M ⟶ N)
    (hf : ∀ i j, J.mem m (f i j)) (hg : ∀ i j, J.mem n (g i j)) (i k) :
    J.mem (m + n) ((f ≫ g) i k) := by
  rw [Mat_.comp_apply]
  exact J.sum_mem _ fun j _ => J.comp_mem (hf i j) (hg j k)

/-- An endomorphism in `Mat_ C` with entries in `J₁` is nilpotent. -/
theorem isNilpotent {M : Mat_ C} (e : M ⟶ M) (he : ∀ i j, J.mem 1 (e i j)) :
    IsNilpotent (show End M from e) := by
  have key : ∀ n : ℕ, ∀ i j, J.mem (n + 1) (((show End M from e) ^ (n + 1) : M ⟶ M) i j) := by
    intro n
    induction n with
    | zero => simpa using he
    | succ n ih =>
      intro i j
      rw [pow_succ', End.mul_def]
      exact J.mem_comp_apply _ _ ih he i j
  exact ⟨J.bound + 1, Mat_.hom_ext _ _ fun i j => J.eq_zero (J.mono (key _ i j))⟩

/-- **Lifting along the coefficient ideal** (`SwappedHomInversion.md` (12)). If `G` is
invertible with inverse entries in `J₀` and `F - G` has entries in `J₁`, then `F` is
invertible. -/
theorem isIso_of_sub_mem {M N : Mat_ C} (F G : M ⟶ N) [IsIso G]
    (hi : ∀ i j, J.mem 0 ((inv G) i j)) (hFG : ∀ i j, J.mem 1 ((F - G) i j)) : IsIso F := by
  have hGF : ∀ i j, J.mem 1 ((G - F) i j) := fun i j => by
    rw [← neg_sub, matNeg_apply]
    exact J.neg_mem (hFG i j)
  refine isIso_of_isNilpotent_sub F (inv G) (J.isNilpotent _ fun i j => ?_)
    (J.isNilpotent _ fun i j => ?_)
  · have : 𝟙 M - F ≫ inv G = (G - F) ≫ inv G := by
      rw [Preadditive.sub_comp, IsIso.hom_inv_id]
    rw [this]
    simpa using J.mem_comp_apply _ _ hGF hi i j
  · have : 𝟙 N - inv G ≫ F = inv G ≫ (G - F) := by
      rw [Preadditive.comp_sub, IsIso.inv_hom_id]
    rw [this]
    simpa using J.mem_comp_apply _ _ hi hGF i j

/-- Blockwise form of `isIso_of_sub_mem` for the block maps `X ⊕ Oᶥ ⟶ Y ⊕ Oᵏ`. -/
theorem isIso_gMap_of_sub_mem {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {X Y O : C}
    {a a' : X ⟶ Y} {B B' : ι → (O ⟶ Y)} {Cc Cc' : κ → (X ⟶ O)} {E E' : ι → κ → (O ⟶ O)}
    [IsIso (gMap a' B' Cc' E')] (hi : ∀ i j, J.mem 0 ((inv (gMap a' B' Cc' E')) i j))
    (ha : J.mem 1 (a - a')) (hB : ∀ i, J.mem 1 (B i - B' i))
    (hC : ∀ r, J.mem 1 (Cc r - Cc' r)) (hE : ∀ i r, J.mem 1 (E i r - E' i r)) :
    IsIso (gMap a B Cc E) := by
  refine J.isIso_of_sub_mem _ (gMap a' B' Cc' E') hi fun o o' => ?_
  rw [matSub_apply]
  rcases o with _ | i <;> rcases o' with _ | r
  · exact ha
  · exact hC r
  · exact hB i
  · exact hE i r

end CoefficientIdeal

end OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
