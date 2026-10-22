/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.MatrixGrading

/-!
# Graded supermodules over a finite-support Hom-matrix algebra

Brundan–Ellis, arXiv:1701.04133v2, §11, first paragraph: for a graded superalgebra `A`,
`A-GSMod` is the category of graded `A`-supermodules with morphisms that preserve degree and
parity, and `Q`, `Π` are the grading and parity shifts, `(QV)_n = V_{n-1}`, `(ΠV)_a = V_{a+1}`.
Here `A` is the algebra `Mat obj` of finite-support matrices of morphisms between the objects
`obj j` of a graded supercategory (`OddMath.FiniteHomMatrix`); `H_n` of (11.1) is of this form.

**Side.** In `Mat obj` the product is composition with the right factor applied first, so the
`(i, j)` entry is a morphism `obj j ⟶ obj i`. For this product the covariant, shift-preserving
functor from objects to projective modules is `j ↦ 1_j · Mat obj`, a *right* module:
`Hom(1_j A, 1_i A) = 1_i A 1_j = Hom(obj j, obj i)`. BE2 speak of left modules, which is the same
statement for the opposite product convention (`ab = b ∘ a`). We use right modules over
`Mat obj`; a right module is a left module over the opposite algebra.

`Mat obj` has local units rather than a unit when the index type is infinite, so modules are
required to be locally unital: every vector is fixed by some local unit. For a finite index
type this is the usual unital condition.

## Main definitions

* `GSMod k obj`: graded right `Mat obj`-supermodules, graded by `ℤ × ℤ/2`, with morphisms the
  `k`-linear maps commuting with the action and preserving degree and parity.
* `GSMod.shift`: the shift by `(n, a)`, so that `Q = shift (1, 0)` and `Π = shift (0, 1)`.
* `GSMod.FG`: finitely generated modules; `GSMod.IsProjective`: the lifting property along
  surjective morphisms.
-/

noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams

namespace OddMath.FiniteHomMatrix

universe u v w t z

variable (k : Type u) [CommRing k] {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
  [Supercategory k C] [GradedSupercategory k C] {J : Type t} (obj : J → C)

/-- **BE2 §11.** A graded right supermodule over `Mat obj`, locally unital (see the module
docstring for the choice of side). -/
structure GSMod where
  /-- The underlying type. -/
  carrier : Type z
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module k carrier]
  /-- The homogeneous pieces, indexed by degree and parity. -/
  piece : ℤ × ZMod 2 → Submodule k carrier
  isInternal_piece : DirectSum.IsInternal piece
  /-- The right action of `Mat obj`: `act a m` is `m · a`. -/
  act : Mat obj →ₗ[k] carrier →ₗ[k] carrier
  act_mul : ∀ a b m, act (a * b) m = act b (act a m)
  exists_localUnit : ∀ m, ∃ s : Finset J, act (localUnit s) m = m
  act_mem : ∀ {d e : ℤ × ZMod 2} {a : Mat obj} {m : carrier},
    a ∈ bidegree (k := k) d → m ∈ piece e → act a m ∈ piece (d + e)

namespace GSMod

attribute [instance] isAddCommGroup isModule

variable {k obj}

instance : CoeSort (GSMod.{u, v, w, t, z} k obj) (Type z) := ⟨carrier⟩

/-- A morphism of graded supermodules: linear, `Mat obj`-equivariant, preserving degree and
parity. -/
@[ext]
structure Hom (M N : GSMod.{u, v, w, t, z} k obj) where
  /-- The underlying linear map. -/
  toLinearMap : M →ₗ[k] N
  map_act : ∀ a m, toLinearMap (M.act a m) = N.act a (toLinearMap m)
  map_piece : ∀ d m, m ∈ M.piece d → toLinearMap m ∈ N.piece d

instance : Category (GSMod.{u, v, w, t, z} k obj) where
  Hom := Hom
  id M := ⟨LinearMap.id, fun _ _ => rfl, fun _ _ h => h⟩
  comp f g := ⟨g.toLinearMap ∘ₗ f.toLinearMap, fun a m => by simp [f.map_act, g.map_act],
    fun d m h => g.map_piece d _ (f.map_piece d m h)⟩

variable {M N L : GSMod.{u, v, w, t, z} k obj}

@[ext] theorem hom_ext {f g : M ⟶ N} (h : ∀ m, f.toLinearMap m = g.toLinearMap m) : f = g :=
  Hom.ext (LinearMap.ext h)

@[simp] theorem id_apply (m : M) : (𝟙 M : M ⟶ M).toLinearMap m = m := rfl

@[simp] theorem comp_apply (f : M ⟶ N) (g : N ⟶ L) (m : M) :
    (f ≫ g).toLinearMap m = g.toLinearMap (f.toLinearMap m) := rfl

/-! ## Shifts -/

/-- The shift of a module by `(n, a)`: the piece of degree `e` is the old piece of degree
`e - (n, a)`. `Q = shift (1, 0)` and `Π = shift (0, 1)` (BE2 §11). -/
@[simps]
def shift (s : ℤ × ZMod 2) (M : GSMod.{u, v, w, t, z} k obj) :
    GSMod.{u, v, w, t, z} k obj where
  carrier := M
  piece e := M.piece (e - s)
  isInternal_piece := by
    have h := M.isInternal_piece
    exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨iSupIndep.comp
          (((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp h).1 :
            iSupIndep M.piece) (sub_left_injective (b := s)),
        by
          rw [← ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp h).2]
          exact (Equiv.subRight s).iSup_comp (g := M.piece)⟩
  act := M.act
  act_mul := M.act_mul
  exists_localUnit := M.exists_localUnit
  act_mem {d e a m} ha hm := by
    have := M.act_mem ha hm
    rwa [← add_sub_assoc] at this

/-- The shift on morphisms. -/
@[simps]
def shiftMap (s : ℤ × ZMod 2) (f : M ⟶ N) : shift s M ⟶ shift s N where
  toLinearMap := f.toLinearMap
  map_act := f.map_act
  map_piece d m h := f.map_piece (d - s) m h

/-- The shift functor. -/
@[simps]
def shiftFunctor (s : ℤ × ZMod 2) :
    GSMod.{u, v, w, t, z} k obj ⥤ GSMod.{u, v, w, t, z} k obj where
  obj := shift s
  map := shiftMap s

/-! ## Homogeneous components -/

/-- The homogeneous component of degree and parity `d`. -/
def proj (M : GSMod.{u, v, w, t, z} k obj) (d : ℤ × ZMod 2) : M →ₗ[k] M :=
  letI := M.isInternal_piece.chooseDecomposition
  (M.piece d).subtype ∘ₗ (DirectSum.component k _ (fun e => M.piece e) d) ∘ₗ
    (DirectSum.decomposeLinearEquiv M.piece).toLinearMap

theorem proj_mem (M : GSMod.{u, v, w, t, z} k obj) (d : ℤ × ZMod 2) (x : M) :
    M.proj d x ∈ M.piece d := by
  simp only [proj, LinearMap.comp_apply]; exact Submodule.coe_mem _

theorem proj_apply (M : GSMod.{u, v, w, t, z} k obj) (d : ℤ × ZMod 2) (x : M) :
    let := M.isInternal_piece.chooseDecomposition
    M.proj d x = (DirectSum.decompose M.piece x d : M) := rfl

theorem proj_of_mem_same (M : GSMod.{u, v, w, t, z} k obj) {d : ℤ × ZMod 2} {x : M}
    (hx : x ∈ M.piece d) : M.proj d x = x := by
  let := M.isInternal_piece.chooseDecomposition
  rw [proj_apply, DirectSum.decompose_of_mem_same M.piece hx]

theorem proj_of_mem_ne (M : GSMod.{u, v, w, t, z} k obj) {d e : ℤ × ZMod 2} {x : M}
    (hx : x ∈ M.piece e) (h : e ≠ d) : M.proj d x = 0 := by
  let := M.isInternal_piece.chooseDecomposition
  rw [proj_apply, DirectSum.decompose_of_mem_ne M.piece hx h]

/-- Every vector is the finite sum of its homogeneous components. -/
theorem exists_finset_sum_proj (M : GSMod.{u, v, w, t, z} k obj) (x : M) :
    ∃ S : Finset (ℤ × ZMod 2), ∑ d ∈ S, M.proj d x = x := by
  let := M.isInternal_piece.chooseDecomposition
  exact ⟨(DirectSum.decompose M.piece x).support, DirectSum.sum_support_decompose M.piece x⟩

/-- A linear map preserving degree and parity commutes with the homogeneous components. -/
theorem proj_map {M N : GSMod.{u, v, w, t, z} k obj} (f : M →ₗ[k] N)
    (hf : ∀ d m, m ∈ M.piece d → f m ∈ N.piece d) (d : ℤ × ZMod 2) (x : M) :
    f (M.proj d x) = N.proj d (f x) := by
  obtain ⟨S, hS⟩ := M.exists_finset_sum_proj x
  conv_rhs => rw [← hS, map_sum, map_sum]
  by_cases hd : d ∈ S
  · rw [Finset.sum_eq_single d]
    · rw [N.proj_of_mem_same (hf d _ (M.proj_mem d x))]
    · intro b _ hb
      exact N.proj_of_mem_ne (hf b _ (M.proj_mem b x)) hb
    · exact fun h => (h hd).elim
  · rw [Finset.sum_eq_zero fun b hb => N.proj_of_mem_ne (hf b _ (M.proj_mem b x))
      (by rintro rfl; exact hd hb)]
    have : M.proj d x = 0 := by
      rw [← hS, map_sum]
      exact Finset.sum_eq_zero fun b hb => M.proj_of_mem_ne (M.proj_mem b x)
        (by rintro rfl; exact hd hb)
    rw [this, map_zero]

/-- The action of a degree-zero even element commutes with the homogeneous components. -/
theorem act_proj (M : GSMod.{u, v, w, t, z} k obj) {a : Mat obj}
    (ha : a ∈ bidegree (k := k) 0) (d : ℤ × ZMod 2) (x : M) :
    M.act a (M.proj d x) = M.proj d (M.act a x) :=
  proj_map (M := M) (N := M) (M.act a) (fun e m hm => by simpa using M.act_mem ha hm) d x

/-! ## Finite generation and projectivity -/

/-- The `Mat obj`-submodule generated by a set of vectors. -/
def span (S : Set M) : Submodule k M :=
  Submodule.span k {x | ∃ a m, m ∈ S ∧ x = M.act a m}

theorem subset_span (S : Set M) : S ⊆ span S := by
  intro m hm
  obtain ⟨s, hs⟩ := M.exists_localUnit m
  exact Submodule.subset_span ⟨_, m, hm, hs.symm⟩

theorem act_mem_span {S : Set M} (a : Mat obj) {m : M} (hm : m ∈ span S) : M.act a m ∈ span S := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, n, hn, rfl⟩ := hx
    exact Submodule.subset_span ⟨b * a, n, hn, (M.act_mul b a n).symm⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- **BE2 §11.** A finitely generated module: generated by finitely many vectors. -/
def FG (M : GSMod.{u, v, w, t, z} k obj) : Prop :=
  ∃ S : Finset M, span (S : Set M) = ⊤

/-- **BE2 §11.** A projective module: morphisms from it lift along surjective morphisms. -/
def IsProjective (P : GSMod.{u, v, w, t, z} k obj) : Prop :=
  ∀ ⦃E X : GSMod.{u, v, w, t, z} k obj⦄ (e : E ⟶ X), Function.Surjective e.toLinearMap →
    ∀ f : P ⟶ X, ∃ g : P ⟶ E, g ≫ e = f

/-- Projectivity is invariant under isomorphism. -/
theorem IsProjective.of_iso {P P' : GSMod.{u, v, w, t, z} k obj} (h : IsProjective P)
    (i : P ≅ P') : IsProjective P' := by
  intro E X e he f
  obtain ⟨g, hg⟩ := h e he (i.hom ≫ f)
  exact ⟨i.inv ≫ g, by rw [Category.assoc, hg, Iso.inv_hom_id_assoc]⟩

/-- A retract of a projective module is projective. -/
theorem IsProjective.of_retract {P P' : GSMod.{u, v, w, t, z} k obj} (h : IsProjective P)
    (s : P' ⟶ P) (r : P ⟶ P') (hsr : s ≫ r = 𝟙 P') : IsProjective P' := by
  intro E X e he f
  obtain ⟨g, hg⟩ := h e he (r ≫ f)
  exact ⟨s ≫ g, by rw [Category.assoc, hg, ← Category.assoc, hsr, Category.id_comp]⟩

end GSMod

end OddMath.FiniteHomMatrix
