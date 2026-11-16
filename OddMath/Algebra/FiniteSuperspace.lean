import StringDiagrams.Super.SVec
import Mathlib.Algebra.BigOperators.Pi

/-! # Finite superspace coordinates for matrix sums
The finite direct-sum matrices of Brundan--Ellis (1.13)--(1.14)
use pointwise superspace grading on their finite coordinate families.
This construction assembles their specified even rows and columns.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.FiniteSuperspace
universe u
variable {k : Type u} {ι : Type} [CommRing k]

/-- Pointwise grading on a family of superspaces. -/
def product (V : ι → SVec k) : SVec k where
  carrier := (a : ι) → V a
  odd := LinearMap.pi fun a => (V a).odd.comp (LinearMap.proj a)
  odd_comp_odd := by
    ext x a
    exact (V a).odd_apply_odd (x a)

@[simp] theorem product_proj (V : ι → SVec k) (p : ZMod 2)
    (x : product V) (a : ι) : (product V).proj p x a = (V a).proj p (x a) := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;> rfl

theorem mem_product_part (V : ι → SVec k) (p : ZMod 2) (x : product V) :
    x ∈ (product V).part p ↔ ∀ a, x a ∈ (V a).part p := by
  simp only [SVec.mem_part_iff]
  constructor
  · intro h a
    simpa only [product_proj] using congrFun h a
  · intro h
    exact funext fun a => (product_proj V p x a).trans (h a)

/-- The finite column assembly. -/
def assembleColumns [Fintype ι] (V : ι → SVec k) (W : SVec k) (f : ∀ a, V a ⟶ W) :
    product V ⟶ W where
  toFun x := ∑ a, f a (x a)
  map_add' x y := by
    change (∑ a, f a (x a + y a)) = (∑ a, f a (x a)) + ∑ a, f a (y a)
    simp only [map_add, Finset.sum_add_distrib]
  map_smul' r x := by
    change (∑ a, f a (r • x a)) = r • ∑ a, f a (x a)
    simp only [map_smul, Finset.smul_sum]

/-- The row assembly with pointwise output coordinates. -/
def assembleRows (V : SVec k) (W : ι → SVec k) (f : ∀ a, V ⟶ W a) :
    V ⟶ product W := LinearMap.pi f

@[simp] theorem assembleColumns_apply [Fintype ι] (V : ι → SVec k) (W : SVec k)
    (f : ∀ a, V a ⟶ W) (x : product V) : assembleColumns V W f x = ∑ a, f a (x a) := rfl

@[simp] theorem assembleRows_apply (V : SVec k) (W : ι → SVec k)
    (f : ∀ a, V ⟶ W a) (x : V) (a : ι) : assembleRows V W f x a = f a x := rfl

/-- Even finite columns assemble to an even map. -/
theorem assembleColumns_even [Fintype ι] (V : ι → SVec k) (W : SVec k)
    (f : ∀ a, V a ⟶ W) (hf : ∀ a, f a ∈ parity (R := k) (V a) W 0) :
    assembleColumns V W f ∈ parity (R := k) (product V) W 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro q x hx
  rw [add_zero]
  apply Submodule.sum_mem
  intro a _
  simpa only [add_zero] using SVec.apply_mem_part (hf a) ((mem_product_part V q x).mp hx a)

/-- Even rows assemble to an even map into the finite coordinate family. -/
theorem assembleRows_even (V : SVec k) (W : ι → SVec k) (f : ∀ a, V ⟶ W a)
    (hf : ∀ a, f a ∈ parity (R := k) V (W a) 0) :
    assembleRows V W f ∈ parity (R := k) V (product W) 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro q x hx
  rw [add_zero, mem_product_part]
  intro a
  simpa only [add_zero, assembleRows_apply] using SVec.apply_mem_part (hf a) hx

end OddMath.FiniteSuperspace

