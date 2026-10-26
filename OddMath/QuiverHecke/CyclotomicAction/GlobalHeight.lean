/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.Vacuum
import OddMath.QuiverHecke.CyclotomicAction.GlobalSupport

/-!
# The height-zero boundary of cyclotomic content categories

Ports the all-content indexing used in
`Categorification/KLR/CyclotomicAction/Global.lean`. At positive height the
algebra, parity and module categories are the existing cyclotomic quotients;
at height zero they are the affine empty-word algebra and its supermodules.
The first strand map is `vacuumAppend`; all later maps are `cyclotomicAppend`.
No quotient presentation or crossing is replaced by a parallel construction.
-/

noncomputable section
open CategoryTheory StringDiagrams
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k)

/-- The cyclotomic tower including its empty-word algebra. -/
def heightAlgebra : ℕ → Type u
  | 0 => Hn D Sc 0
  | n + 1 => CyclotomicAlgebra D Sc a n

instance (n : ℕ) : Ring (heightAlgebra D Sc a n) := by
  cases n with
  | zero => exact inferInstanceAs (Ring (Hn D Sc 0))
  | succ n => exact inferInstanceAs (Ring (CyclotomicAlgebra D Sc a n))

instance (n : ℕ) : Algebra k (heightAlgebra D Sc a n) := by
  cases n with
  | zero => exact inferInstanceAs (Algebra k (Hn D Sc 0))
  | succ n => exact inferInstanceAs (Algebra k (CyclotomicAlgebra D Sc a n))

variable (ha : CyclotomicPolynomialParity D a)

/-- The grading is the existing affine or quotient grading at each height. -/
def heightParity : (n : ℕ) → ZMod 2 → Submodule k (heightAlgebra D Sc a n)
  | 0 => affineParity D Sc 0
  | n + 1 => cyclotomicParity D Sc a ha n

instance (n : ℕ) : GradedAlgebra (heightParity D Sc a ha n) := by
  cases n with
  | zero => exact inferInstanceAs (GradedAlgebra (affineParity D Sc 0))
  | succ n => exact inferInstanceAs (GradedAlgebra (cyclotomicParity D Sc a ha n))

/-- The module supercategory at an arbitrary height, including zero. -/
abbrev HeightModules (n : ℕ) :=
  SuperBimodule (heightParity D Sc a ha n) (trivialGrading k)

/-- No comparison is needed at positive height: the superspaces are identical. -/
theorem heightModules_succ (n : ℕ) :
    HeightModules D Sc a ha (n + 1) = CyclotomicSupermodules D Sc a ha n := rfl

/-- The first strand uses the vacuum inclusion, subsequent strands the quotient inclusion. -/
def heightAppend (i : I) : (n : ℕ) →
    heightAlgebra D Sc a n →ₙₐ[k] heightAlgebra D Sc a (n + 1)
  | 0 => vacuumAppend D Sc i a
  | n + 1 => cyclotomicAppend D Sc i a n

@[simp] theorem heightAppend_zero (i : I) :
    heightAppend D Sc a i 0 = vacuumAppend D Sc i a := rfl

@[simp] theorem heightAppend_succ (i : I) (n : ℕ) :
    heightAppend D Sc a i (n + 1) = cyclotomicAppend D Sc i a n := rfl

/-- Every strand map in the extended tower is even. -/
theorem heightAppend_parity (i : I) (n : ℕ) {p : ZMod 2}
    {x : heightAlgebra D Sc a n} (hx : x ∈ heightParity D Sc a ha n p) :
    heightAppend D Sc a i n x ∈ heightParity D Sc a ha (n + 1) p := by
  cases n with
  | zero => exact vacuumAppend_parity D Sc i a ha hx
  | succ n => exact cyclotomicAppend_parity D Sc i a ha n hx

/-- Content support at positive height, and all empty-word modules at height zero. -/
def heightContentSupported : (n : ℕ) → Multiset I → HeightModules D Sc a ha n → Prop
  | 0, β, _ => β = 0
  | n + 1, β, M => ContentSupported D Sc a ha n β M

/-- The supercategory of a content, now with its correct height including the vacuum. -/
abbrev GlobalContentModules (β : Multiset I) :=
  ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha β.card β)

/-- Content zero is genuinely at height zero, not at the one-strand quotient. -/
theorem globalContentModules_zero :
    GlobalContentModules D Sc a ha 0 =
      ObjectProperty.FullSubcategory (fun _ : HeightModules D Sc a ha 0 => (0 : Multiset I) = 0) := rfl

end OddMath.QuiverHecke.CyclotomicAction
