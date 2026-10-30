/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.Quotient
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Ordinary right modules over finite Hom matrices

An additive presheaf `F : Cᵒᵖ ⥤ ModuleCat k` gives a right module over
`FiniteHomMatrix.Mat obj` by matrix precomposition. The underlying type is
`∀ j, F.obj (op (obj j))`, with a type alias to keep the new scalar action
separate from the ordinary pointwise Pi module instances.

Only additivity of `F` is needed; in particular the construction applies to
any `k`-linear presheaf. No commutativity of the matrix ring is assumed.
The unit and ring structure are the existing ones from `CyclotomicAction.Quotient`.
Natural transformations give linear maps over the opposite matrix ring.
-/

noncomputable section
open scoped Classical
open CategoryTheory Opposite
namespace OddMath.FiniteHomMatrix
universe u v w t s
variable {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
  {J : Type t} (obj : J → C) (F : Cᵒᵖ ⥤ ModuleCat.{s} k)

/-- The finite family of values of a presheaf, carrying matrix right precomposition. -/
def RightModule := ∀ j, F.obj (op (obj j))

namespace RightModule
instance : AddCommGroup (RightModule obj F) :=
  inferInstanceAs (AddCommGroup (∀ j, F.obj (op (obj j))))
instance : Module k (RightModule obj F) :=
  inferInstanceAs (Module k (∀ j, F.obj (op (obj j))))

@[simp] theorem zero_apply (j : J) : (0 : RightModule obj F) j = 0 := rfl
@[simp] theorem add_apply (z z' : RightModule obj F) (j : J) :
    (z + z') j = z j + z' j := rfl

@[simp] theorem sum_apply {ι : Type*} (s : Finset ι) (z : ι → RightModule obj F)
    (j : J) : (∑ i ∈ s, z i) j = ∑ i ∈ s, z i j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, ih]

/-- A vector supported at one object index. -/
def singleVec (j : J) (x : F.obj (op (obj j))) : RightModule obj F := Pi.single j x

@[simp] theorem singleVec_same (j : J) (x : F.obj (op (obj j))) :
    singleVec obj F j x j = x := by simp [singleVec]
@[simp] theorem singleVec_ne (j l : J) (h : l ≠ j) (x : F.obj (op (obj j))) :
    singleVec obj F j x l = 0 := by simp [singleVec, h]

variable [Preadditive C] [Fintype J]

/-- Contravariant transport, with explicit endpoint types. -/
def precomp (i j : J) (f : obj j ⟶ obj i) :
    F.obj (op (obj i)) →ₗ[k] F.obj (op (obj j)) := (F.map f.op).hom

/-- The unopposed notation `act b z` means the right action `z ⋅ b`. -/
def act (b : Mat obj) (z : RightModule obj F) : RightModule obj F :=
  fun j => ∑ i, precomp obj F i j (b (i, j)) (z i)

variable [F.Additive]

@[simp] theorem act_zero (z : RightModule obj F) : act obj F 0 z = 0 := by
  funext j
  simp [act, precomp]

@[simp] theorem act_add (a b : Mat obj) (z : RightModule obj F) :
    act obj F (a + b) z = act obj F a z + act obj F b z := by
  funext j
  simp [act, precomp, Finset.sum_add_distrib]

@[simp] theorem act_single (i j : J) (f : obj j ⟶ obj i) (z : RightModule obj F) :
    act obj F (single i j f) z = singleVec obj F j ((F.map f.op) (z i)) := by
  funext l
  by_cases h : j = l
  · subst l
    rw [singleVec_same]
    change (∑ x : J, precomp obj F x j ((single i j f) (x, j)) (z x)) = _
    rw [Finset.sum_eq_single i]
    · simp [single, precomp]
    · intro b _ hb
      simp [single, DFinsupp.single_apply, Ne.symm hb, precomp]
    · simp
  · simp [act, precomp, single, DFinsupp.single_apply, h, singleVec, Ne.symm h]

omit [F.Additive] in
@[simp] theorem act_zero_vec (a : Mat obj) : act obj F a 0 = 0 := by
  funext j
  simp [act, precomp]

omit [F.Additive] in
@[simp] theorem act_add_vec (a : Mat obj) (z z' : RightModule obj F) :
    act obj F a (z + z') = act obj F a z + act obj F a z' := by
  funext j
  simp [act, precomp, Finset.sum_add_distrib]

/-- Matrix multiplication acts in reverse order, as required for a right module. -/
theorem act_mul (a b : Mat obj) (z : RightModule obj F) :
    act obj F (a * b) z = act obj F b (act obj F a z) := by
  induction a using induction with
  | hz => simp
  | ha a a' ha ha' => simp [add_mul, ha, ha']
  | hs i j f =>
    induction b using induction with
    | hz => simp
    | ha b b' hb hb' => simp [mul_add, hb, hb']
    | hs l m g =>
      by_cases h : j = l
      · subst l
        simp [act_single, Functor.map_comp]
      · rw [single_mul_single_of_ne _ _ _ _ h, act_zero, act_single, act_single]
        funext r
        simp [singleVec, Ne.symm h]

theorem act_sum {ι : Type*} (s : Finset ι) (b : ι → Mat obj)
    (z : RightModule obj F) :
    act obj F (∑ i ∈ s, b i) z = ∑ i ∈ s, act obj F (b i) z := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, ih]

@[simp] theorem act_one (z : RightModule obj F) : act obj F 1 z = z := by
  change act obj F (∑ i : J, single i i (𝟙 (obj i))) z = z
  rw [act_sum]
  funext j
  rw [sum_apply]
  simp only [act_single, op_id, F.map_id, ModuleCat.id_apply]
  rw [Finset.sum_eq_single j]
  · exact singleVec_same obj F j (z j)
  · intro i _ hi
    exact singleVec_ne obj F i j (Ne.symm hi) (z i)
  · simp

/-- The ordinary unital right matrix module, encoded using the opposite ring. -/
instance : Module (Mat obj)ᵐᵒᵖ (RightModule obj F) where
  smul b z := act obj F b.unop z
  one_smul := act_one obj F
  mul_smul a b z := act_mul obj F b.unop a.unop z
  smul_zero b := act_zero_vec obj F b.unop
  smul_add b := act_add_vec obj F b.unop
  add_smul a b z := act_add obj F a.unop b.unop z
  zero_smul := act_zero obj F

/-- Right precomposition, viewed as a left action of the opposite matrix ring. -/
theorem smul_apply (b : (Mat obj)ᵐᵒᵖ) (z : RightModule obj F) (j : J) :
    (b • z) j = ∑ i, (F.map (b.unop (i, j)).op) (z i) := rfl

variable {F} {G : Cᵒᵖ ⥤ ModuleCat.{s} k} [G.Additive]

/-- Natural transformations act componentwise as ordinary right-linear maps. -/
def map (η : F ⟶ G) : RightModule obj F →ₗ[(Mat obj)ᵐᵒᵖ] RightModule obj G where
  toFun z j := η.app (op (obj j)) (z j)
  map_add' z z' := by
    funext j
    change η.app (op (obj j)) (z j + z' j) =
      η.app (op (obj j)) (z j) + η.app (op (obj j)) (z' j)
    exact map_add _ _ _
  map_smul' b z := by
    funext j
    change η.app (op (obj j)) ((b • z) j) =
      (b • (show RightModule obj G from fun i => η.app (op (obj i)) (z i))) j
    rw [smul_apply, smul_apply]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun f => f (z i)) (η.naturality (b.unop (i, j)).op)

@[simp] theorem map_apply (η : F ⟶ G) (z : RightModule obj F) (j : J) :
    map obj η z j = η.app (op (obj j)) (z j) := rfl

end RightModule
end OddMath.FiniteHomMatrix
