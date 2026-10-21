/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Finite-support matrices of morphisms

The algebra underlying BE2, arXiv:1701.04133v2, §11's definition of `H_n`.
Rows are targets and columns are sources. No finiteness of the object index
is needed: multiplication is the bilinear extension of composition on matrix
entries, with zero for incompatible middle indices.
-/
noncomputable section
open scoped Classical
open CategoryTheory
namespace OddMath.FiniteHomMatrix
universe u v w t
variable {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
  [Preadditive C] [Linear k C] {J : Type t} (obj : J → C)

/-- Finite-support matrices with entry `(i,j)` in `Hom(obj j, obj i)`. -/
abbrev Mat := Π₀ p : J × J, (obj p.2 ⟶ obj p.1)

variable {obj}
/-- Insert one morphism into a matrix. -/
abbrev single (i j : J) (f : obj j ⟶ obj i) : Mat obj := DFinsupp.single (i,j) f

/-- Bilinear multiplication of individual entries. -/
def entryMul (p q : J × J) :
    (obj p.2 ⟶ obj p.1) →ₗ[k] (obj q.2 ⟶ obj q.1) →ₗ[k] Mat obj := by
  classical
  exact if h : p.2 = q.1 then
    { toFun := fun f =>
        { toFun := fun g => single p.1 q.2 (g ≫ eqToHom (congrArg obj h.symm) ≫ f)
          map_add' := by intros; simp [single, Preadditive.add_comp, DFinsupp.single_add]
          map_smul' := by intros; simp [single, Linear.smul_comp, DFinsupp.single_smul] }
      map_add' := by intros; ext g; simp [single, Preadditive.comp_add, DFinsupp.single_add]
      map_smul' := by intros; ext g; simp [single, Linear.comp_smul, DFinsupp.single_smul] }
    else 0

/-- Matrix multiplication as a bilinear map. -/
def mulLinear : Mat obj →ₗ[k] Mat obj →ₗ[k] Mat obj :=
  DFinsupp.lsum k fun p =>
    { toFun := fun f => DFinsupp.lsum k fun q => entryMul (k := k) p q f
      map_add' := by intros; ext q g; simp
      map_smul' := by intros; ext q g; simp }

instance : Mul (Mat obj) := ⟨fun a b => mulLinear (k := ℤ) a b⟩

@[simp] theorem single_mul_single (i j l : J) (f : obj j ⟶ obj i)
    (g : obj l ⟶ obj j) : single i j f * single j l g = single i l (g ≫ f) := by
  classical
  simp [HMul.hMul, Mul.mul, mulLinear, single, entryMul]

@[simp] theorem single_mul_single_of_ne (i j l m : J) (h : j ≠ l)
    (f : obj j ⟶ obj i) (g : obj m ⟶ obj l) :
    single i j f * single l m g = 0 := by
  classical
  simp [HMul.hMul, Mul.mul, mulLinear, single, entryMul, h]

theorem matrix_zero_mul (a : Mat obj) : 0 * a = 0 := by
  change mulLinear (k := ℤ) 0 a = 0
  simp

theorem matrix_mul_zero (a : Mat obj) : a * 0 = 0 := (mulLinear (k := ℤ) a).map_zero

theorem matrix_add_mul (a b c : Mat obj) : (a + b) * c = a * c + b * c := by
  change mulLinear (k := ℤ) (a + b) c = mulLinear (k := ℤ) a c + mulLinear (k := ℤ) b c
  simp

theorem matrix_mul_add (a b c : Mat obj) : a * (b + c) = a * b + a * c :=
  (mulLinear (k := ℤ) a).map_add b c

/-- Induction by matrix entries and addition. -/
@[elab_as_elim] theorem induction {P : Mat obj → Prop} (a : Mat obj)
    (hz : P 0) (hs : ∀ i j f, P (single i j f))
    (ha : ∀ a b, P a → P b → P (a + b)) : P a := by
  apply DFinsupp.induction a hz
  rintro ⟨i,j⟩ f b _ _ hb
  exact ha _ _ (hs i j f) hb

theorem matrix_mul_assoc (a b c : Mat obj) : (a * b) * c = a * (b * c) := by
  classical
  induction a using induction with
  | hz => simp [matrix_zero_mul]
  | ha a b ha hb => simp [matrix_add_mul, ha, hb]
  | hs i j f =>
    induction b using induction with
    | hz => simp [matrix_zero_mul, matrix_mul_zero]
    | ha a b ha hb => simp [matrix_add_mul, matrix_mul_add, ha, hb]
    | hs l m g =>
      induction c using induction with
      | hz => simp [matrix_mul_zero]
      | ha a b ha hb => simp [matrix_mul_add, ha, hb]
      | hs r s h =>
        by_cases hj : j = l <;> by_cases hm : m = r
        · subst l; subst r; simp [Category.assoc]
        · subst l; simp [hm, matrix_mul_zero]
        · subst r; simp [hj, matrix_zero_mul]
        · simp [hj, hm, matrix_zero_mul, matrix_mul_zero]

instance : NonUnitalRing (Mat obj) where
  __ : AddCommGroup (Mat obj) := inferInstance
  mul := (· * ·)
  mul_assoc := matrix_mul_assoc
  zero_mul := matrix_zero_mul
  mul_zero := matrix_mul_zero
  left_distrib := matrix_mul_add
  right_distrib := matrix_add_mul

/-- Scalar-linear and additive definitions give the same matrix product. -/
theorem mulLinear_apply (a b : Mat obj) : mulLinear (k := k) a b = a * b := by
  induction a using induction with
  | hz => simp
  | ha a b ha hb => simp [ha, hb, add_mul]
  | hs i j f =>
    induction b using induction with
    | hz => simp
    | ha a b ha hb => simp [ha, hb, mul_add]
    | hs l m g =>
      by_cases h : j = l
      · subst l; simp [HMul.hMul, Mul.mul, mulLinear, single, entryMul]
      · simp [HMul.hMul, Mul.mul, mulLinear, single, entryMul, h]

instance : IsScalarTower k (Mat obj) (Mat obj) where
  smul_assoc r a b := by
    change (r • a) * b = r • (a * b)
    rw [← mulLinear_apply (k := k), map_smul]
    exact congrArg (r • ·) (mulLinear_apply a b)

instance : SMulCommClass k (Mat obj) (Mat obj) where
  smul_comm r a b := by
    change r • (a * b) = a * (r • b)
    rw [← mulLinear_apply (k := k) a (r • b), map_smul, mulLinear_apply]

/-- The identity of a single word, not a global identity for an infinite index type. -/
def idem (i : J) : Mat obj := single i i (𝟙 (obj i))

@[simp] theorem idem_sq (i : J) : idem (obj := obj) i * idem i = idem i := by
  simp [idem]

@[simp] theorem idem_orthogonal (i j : J) (h : i ≠ j) :
    idem (obj := obj) i * idem j = 0 := by simp [idem, h]

@[simp] theorem idem_mul_single (i j : J) (f : obj j ⟶ obj i) :
    idem i * single i j f = single i j f := by simp [idem]

@[simp] theorem single_mul_idem (i j : J) (f : obj j ⟶ obj i) :
    single i j f * idem j = single i j f := by simp [idem]

/-- A finite diagonal sum of word identities. -/
def localUnit (s : Finset J) : Mat obj := ∑ i ∈ s, idem i

@[simp] theorem localUnit_mul_single (s : Finset J) (i j : J)
    (f : obj j ⟶ obj i) (hi : i ∈ s) :
    localUnit s * single i j f = single i j f := by
  rw [localUnit, Finset.sum_mul, Finset.sum_eq_single i]
  · exact idem_mul_single i j f
  · intro b _ hb
    exact single_mul_single_of_ne b b i j hb _ _
  · exact fun h => (h hi).elim

@[simp] theorem single_mul_localUnit (s : Finset J) (i j : J)
    (f : obj j ⟶ obj i) (hj : j ∈ s) :
    single i j f * localUnit s = single i j f := by
  rw [localUnit, Finset.mul_sum, Finset.sum_eq_single j]
  · exact single_mul_idem i j f
  · intro b _ hb
    exact single_mul_single_of_ne i j b b hb.symm _ _
  · exact fun h => (h hj).elim

@[simp] theorem localUnit_sq (s : Finset J) :
    localUnit (obj := obj) s * localUnit s = localUnit s := by
  conv_lhs => rw [localUnit, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => localUnit_mul_single s i i _ hi

/-- Every matrix has a two-sided local unit, still valid after enlarging its support. -/
theorem exists_localUnit (a : Mat obj) :
    ∃ s : Finset J, ∀ t : Finset J, s ⊆ t → localUnit t * a = a ∧ a * localUnit t = a := by
  induction a using induction with
  | hz => exact ⟨∅, fun _ _ => ⟨mul_zero _, zero_mul _⟩⟩
  | hs i j f =>
    refine ⟨{i,j}, fun t ht => ⟨?_, ?_⟩⟩
    · exact localUnit_mul_single t i j f (ht (by simp))
    · exact single_mul_localUnit t i j f (ht (by simp))
  | ha a b ha hb =>
    obtain ⟨s, hs⟩ := ha
    obtain ⟨r, hr⟩ := hb
    refine ⟨s ∪ r, fun t ht => ?_⟩
    obtain ⟨ha₁, ha₂⟩ := hs t (Finset.Subset.trans Finset.subset_union_left ht)
    obtain ⟨hb₁, hb₂⟩ := hr t (Finset.Subset.trans Finset.subset_union_right ht)
    exact ⟨by rw [mul_add, ha₁, hb₁], by rw [add_mul, ha₂, hb₂]⟩

/-- A common idempotent local unit for any finite collection of matrices. -/
theorem exists_common_localUnit (s : Finset (Mat obj)) :
    ∃ t : Finset J, ∀ a ∈ s, localUnit t * a = a ∧ a * localUnit t = a := by
  have h : ∀ a : Mat obj, ∃ t : Finset J, ∀ u, t ⊆ u →
      localUnit u * a = a ∧ a * localUnit u = a := exists_localUnit
  choose t ht using h
  refine ⟨s.biUnion t, fun a ha => ht a _ ?_⟩
  exact Finset.subset_biUnion_of_mem t ha

/-- Inserting an endomorphism is a nonunital ring homomorphism onto its corner. -/
def cornerMap (i : J) : CategoryTheory.End (obj i) →ₙ+* Mat obj where
  toFun f := single (obj := obj) i i f
  map_zero' := by simp [single]
  map_add' f g := by simp [single, DFinsupp.single_add]
  map_mul' f g := (single_mul_single (obj := obj) i i i f g).symm

@[simp] theorem cornerMap_one (i : J) : cornerMap (obj := obj) i 1 = idem i := rfl

/-- The corner inclusion does not identify distinct endomorphisms. -/
theorem cornerMap_injective (i : J) : Function.Injective (cornerMap (obj := obj) i) := by
  intro f g h
  have he := congrArg (fun a : Mat obj => a (i,i)) h
  change (single (obj := obj) i i f) (i,i) = (single (obj := obj) i i g) (i,i) at he
  simpa [single] using he

/-- The image of the endomorphism ring is exactly the idempotent corner. -/
theorem mem_range_cornerMap_iff (i : J) (a : Mat obj) :
    (∃ f, cornerMap i f = a) ↔ idem i * a * idem i = a := by
  constructor
  · rintro ⟨f, rfl⟩
    change idem i * single i i f * idem i = single i i f
    simp
  · intro ha
    have h : ∀ b : Mat obj, ∃ f, cornerMap i f = idem i * b * idem i := by
      intro b
      induction b using induction with
      | hz => exact ⟨0, by change single i i 0 = _; simp [single]⟩
      | ha b c hb hc =>
        obtain ⟨f, hf⟩ := hb
        obtain ⟨g, hg⟩ := hc
        exact ⟨f + g, by rw [map_add, hf, hg, mul_add, add_mul]⟩
      | hs j l f =>
        by_cases hij : i = j
        · subst j
          by_cases hli : l = i
          · subst l; exact ⟨f, by change single i i f = _; simp⟩
          · refine ⟨0, ?_⟩
            change single i i 0 = _
            simp [idem, hli, single]
        · refine ⟨0, ?_⟩
          change single i i 0 = _
          simp [idem, hij, single]
    obtain ⟨f, hf⟩ := h a
    exact ⟨f, hf.trans ha⟩

end OddMath.FiniteHomMatrix
