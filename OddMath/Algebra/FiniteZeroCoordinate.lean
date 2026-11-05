import OddMath.Algebra.FiniteSuperspace
import Mathlib.LinearAlgebra.Pi

/-! # Dropping the zero principal coordinate of a finite matrix family

Brundan--Ellis (1.13), at a missing-colour output block, has zero lower
E/F summand. These coordinate maps remove exactly that zero summand,
keeping every remaining coordinate and its actual superspace grading.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.FiniteSuperspace
universe u
variable {k : Type u} [CommRing k] {ι : Type} (V : Option ι → SVec k)

/-- The actual finite family after dropping the principal coordinate. -/
def withoutPrincipal : SVec k := product fun a => V (some a)

/-- Forget a principal coordinate which is proved zero, and insert zero as
its inverse. The other coordinates are unchanged. -/
def dropZeroPrincipalEquiv (h₀ : Subsingleton (V none)) :
    product V ≃ₗ[k] withoutPrincipal V where
  toFun x a := x (some a)
  invFun y a := match a with
    | none => 0
    | some r => y r
  left_inv x := by
    funext a
    cases a with
    | none => exact h₀.elim _ _
    | some r => rfl
  right_inv y := by funext a; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem dropZeroPrincipalEquiv_apply (h₀ : Subsingleton (V none))
    (x : product V) (a : ι) : dropZeroPrincipalEquiv V h₀ x a = x (some a) := rfl

@[simp] theorem dropZeroPrincipalEquiv_symm_none (h₀ : Subsingleton (V none))
    (x : withoutPrincipal V) : (dropZeroPrincipalEquiv V h₀).symm x none = 0 := rfl

@[simp] theorem dropZeroPrincipalEquiv_symm_some (h₀ : Subsingleton (V none))
    (x : withoutPrincipal V) (a : ι) : (dropZeroPrincipalEquiv V h₀).symm x (some a) = x a := rfl

/-- Removing a zero principal coordinate leaves precisely the remaining
columns of the prescribed finite matrix. -/
theorem dropZeroPrincipalEquiv_columns [Fintype ι]
    (h₀ : Subsingleton (V none)) (W : SVec k) (f : ∀ a, V a ⟶ W) :
    (SVec.isoOfLinearEquiv (dropZeroPrincipalEquiv V h₀)).inv ≫
      assembleColumns V W f =
    assembleColumns (fun a => V (some a)) W (fun a => f (some a)) := by
  apply SVec.hom_ext
  intro x
  change (∑ a, f a ((dropZeroPrincipalEquiv V h₀).symm x a)) =
    ∑ a, f (some a) (x a)
  rw [Fintype.sum_option]
  simp only [dropZeroPrincipalEquiv_symm_none, dropZeroPrincipalEquiv_symm_some,
    map_zero, zero_add]

end OddMath.FiniteSuperspace
