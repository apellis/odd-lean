import OddMath.Frontier.EQOnhDGPoly
import DG.Derived.Basic

/-!
# `ONH_{n+2}` is acyclic and its derived category vanishes

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Proposition 3.16(2): for `n ≥ 2`, `(ONH_n, d)` is acyclic, since `1 = d(∂_1)`; consequently
its derived category is zero.

* `isAcyclic_of_d_eq_one`: if a dg ring `A` has an element `h` of degree `-1` with `d(h) = 1`,
  every dg `A`-module is acyclic (a cocycle `m` is `d(h m)`); `isAcyclic_self_of_d_eq_one`: so is
  `A` itself.
* `ONH.isAcyclic`: `H(ONH_{n+2}) = 0`; `ONH.isAcyclic_module`: every dg `ONH_{n+2}`-module is
  acyclic; `ONH.isZero_Q_obj`, `ONH.isZero_derivedCategory`: every object of the derived
  category `D(ONH_{n+2})` is zero.
-/

noncomputable section

universe w v

namespace OddMath.Frontier.EQOnhDG

open CategoryTheory Limits

section General

variable {A : Type*} [Ring A] [DG.DGAddCommGroup A] [DG.DGRing A] {h : A}
  (hh : h ∈ DG.grading (M := A) (-1)) (hd : DG.d h = 1)
include hh hd

omit [DG.DGRing A] in
/-- If `d(h) = 1` for some `h` of degree `-1`, every dg `A`-module is acyclic: a cocycle `m`
equals `d(h m)`. -/
theorem isAcyclic_of_d_eq_one (M : Type*) [AddCommGroup M] [DG.DGAddCommGroup M] [Module A M]
    [DG.DGModule A M] : DG.IsAcyclic M := by
  refine DG.isAcyclic_iff.mpr fun k m hm hdm => ⟨h • m, ?_, ?_⟩
  · have := DG.smul_mem_grading hh hm
    rwa [neg_add_eq_sub] at this
  · rw [DG.d_smul hh, hd, one_smul, hdm, smul_zero, smul_zero, add_zero]

/-- If `d(h) = 1` for some `h` of degree `-1`, the dg ring `A` is acyclic. -/
theorem isAcyclic_self_of_d_eq_one : DG.IsAcyclic A :=
  isAcyclic_of_d_eq_one hh hd A

end General

namespace ONH

variable {n : ℕ}

/-- **Ellis–Qi, Proposition 3.16(2)**: `(ONH_{n+2}, d)` is acyclic, `H(ONH_{n+2}) = 0`, since
`1 = d(∂_1)`. -/
theorem isAcyclic : DG.IsAcyclic (ONH n) :=
  isAcyclic_self_of_d_eq_one (del_mem_grading (n := n) 0) (d_del 0)

/-- Every cohomology group of `ONH_{n+2}` vanishes. -/
theorem subsingleton_cohomology (k : ℤ) : Subsingleton (DG.cohomology (ONH n) k) :=
  isAcyclic k

/-- Every dg module over `ONH_{n+2}` is acyclic. -/
theorem isAcyclic_module (M : Type*) [AddCommGroup M] [DG.DGAddCommGroup M] [Module (ONH n) M]
    [DG.DGModule (ONH n) M] : DG.IsAcyclic M :=
  isAcyclic_of_d_eq_one (del_mem_grading (n := n) 0) (d_del 0) M

variable [DG.HasDerivedCategory.{w, v} (ONH n)]

/-- Every dg `ONH_{n+2}`-module becomes zero in the derived category `D(ONH_{n+2})`. -/
theorem isZero_Q_obj (M : DG.DGModuleCat.{v} (ONH n)) : IsZero (DG.DerivedCategory.Q.obj M) :=
  (DG.DerivedCategory.isZero_Q_obj_iff M).mpr (isAcyclic_module (n := n) M)

/-- **The derived category `D(ONH_{n+2})` is zero** (Ellis–Qi, Proposition 3.16(2)): every
object is a zero object. -/
theorem isZero_derivedCategory (X : DG.DerivedCategory.{w, v} (ONH n)) : IsZero X := by
  have := Localization.essSurj (DG.DerivedCategory.Q (A := ONH n)) (DG.DGModuleCat.quasiIso (ONH n))
  exact (isZero_Q_obj _).of_iso (DG.DerivedCategory.Q.objObjPreimageIso X).symm

end ONH

end OddMath.Frontier.EQOnhDG

end
