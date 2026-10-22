/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.GSKar
import OddMath.QuiverHecke.GradedModulesAdditive

/-!
# The row-module functor on the `(Q, Π)`-envelope

Brundan–Ellis, arXiv:1701.04133v2, §11: for a graded supercategory `C`, the object
`Q^m Π^a λ` of the underlying category of the `(Q, Π)`-envelope goes to the graded projective
supermodule `Q^m Π^a (1_λ · Mat)` over the finite-support Hom-matrix algebra `Mat` of all
objects of `C` (`rowFunctor`). A morphism `Q^m Π^a λ ⟶ Q^n Π^b μ` of the underlying category
is a morphism `λ ⟶ μ` of `C` of degree `m - n` and parity `a + b` (`qpiHomEquiv`), and the
functor sends it to the module map determined by the image of `1_λ`. By the Yoneda bijection for row
modules (`GSMod.rowModuleHomEquiv`) the functor is fully faithful (`rowFunctorFullyFaithful`);
it is `k`-linear.
-/

noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams GradedSupercategory

namespace OddMath.FiniteHomMatrix

universe u v w

variable {k : Type u} [CommRing k] {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

/-! ## Rows and their matrices -/

section Rows

variable {J : Type*} {obj : J → C}

theorem matToRow_single (j l : J) (f : obj l ⟶ obj j) :
    matToRow (k := k) j (single j l f) = DFinsupp.single l f := by
  ext l'
  by_cases h : l' = l
  · subst l'; simp [single]
  · simp [single, DFinsupp.single_apply, Ne.symm h]

/-- Right multiplication of a one-entry row by a one-entry matrix. -/
theorem rowAct_single_single (j l m : J) (f : obj l ⟶ obj j) (g : obj m ⟶ obj l) :
    rowAct (k := k) j (single l m g) (DFinsupp.single l f) =
      (DFinsupp.single m (g ≫ f) : Row obj j) := by
  rw [rowAct_apply, rowToMat_single, single_mul_single, matToRow_single]

end Rows

namespace GSMod

variable [Supercategory k C] [GradedSupercategory k C] {J : Type*} {obj : J → C}

/-- A morphism out of a shifted row module is right multiplication of its value on `1_j`. -/
theorem apply_eq_act_rowGen {M : GSMod k obj} {s : ℤ × ZMod 2} {j : J}
    (φ : GSMod.shift s (rowModule (k := k) j) ⟶ M) (v : Row obj j) :
    φ.toLinearMap v = M.act (rowToMat (k := k) j v) (φ.toLinearMap (rowGen j)) :=
  (congrArg (fun ψ : GSMod.shift s (rowModule (k := k) j) ⟶ M => ψ.toLinearMap v)
    ((rowHomEquiv s j).left_inv φ)).symm

/-- The morphism corresponding to a homogeneous morphism `f : obj j ⟶ obj i` sends `1_j` to the
one-entry row `f`. -/
theorem rowModuleHomEquiv_symm_rowGen (s t : ℤ × ZMod 2) (i j : J)
    (f : GradedSupercategory.bidegree (R := k) (obj j) (obj i) (s - t)) :
    ((rowModuleHomEquiv s t i j).symm f).toLinearMap (rowGen j) =
      (DFinsupp.single j (f : obj j ⟶ obj i) : Row obj i) := by
  rw [rowModuleHomEquiv, Equiv.symm_trans_apply]
  exact congrArg Subtype.val ((rowHomEquiv s j).apply_symm_apply _)

end GSMod

/-! ## Morphisms of the underlying category of the `(Q, Π)`-envelope -/

variable [Supercategory k C] [GradedSupercategory k C]

variable (k C) in
/-- The underlying category of the `(Q, Π)`-envelope `C_{q,π}`: objects `Q^m Π^a λ`, morphisms
the even morphisms of degree zero. -/
abbrev QPiUnderlying := GUnderlying k (QPiEnvelope k C)

/-- The shift `(m, a)` of `Q^m Π^a λ`. -/
def qpiShift (X : QPiUnderlying k C) : ℤ × ZMod 2 := (X.obj.obj.obj.shift, X.obj.obj.par)

/-- The object `λ` of `Q^m Π^a λ`. -/
def qpiBase (X : QPiUnderlying k C) : C := X.obj.obj.obj.obj

omit [Preadditive C] [Linear k C] [Supercategory k C] [GradedSupercategory k C] in
theorem zmod2_sub (a b : ZMod 2) : a - b = a + b := by
  rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

/-- **BE2 Definition 6.8.** The even degree-zero morphisms `Q^m Π^a λ ⟶ Q^n Π^b μ` are the
morphisms `λ ⟶ μ` of degree `m - n` and parity `a + b = a - b`. -/
def qpiHomEquiv (X Y : QPiUnderlying k C) :
    (X ⟶ Y) ≃
      GradedSupercategory.bidegree (R := k) (qpiBase X) (qpiBase Y) (qpiShift X - qpiShift Y)
      where
  toFun f := ⟨QPiEnvelope.toHom f.1.1, by
    refine ⟨?_, ?_⟩
    · have h := f.1.2
      change QPiEnvelope.toHom f.1.1 ∈
        GradedSupercategory.degree (R := k) (qpiBase X) (qpiBase Y)
        (0 + (X.obj.obj.obj.shift - Y.obj.obj.obj.shift)) at h
      simpa [qpiShift] using h
    · have h := f.2
      change QPiEnvelope.toHom f.1.1 ∈ Supercategory.parity (R := k) (qpiBase X) (qpiBase Y)
        (0 + (X.obj.obj.par + Y.obj.obj.par)) at h
      simpa [qpiShift, zmod2_sub] using h⟩
  invFun f := ⟨⟨QPiEnvelope.ofHom f.1, by
      change f.1 ∈ GradedSupercategory.degree (R := k) (qpiBase X) (qpiBase Y)
        (0 + (X.obj.obj.obj.shift - Y.obj.obj.obj.shift))
      simpa [qpiShift] using f.2.1⟩, by
    change f.1 ∈ Supercategory.parity (R := k) (qpiBase X) (qpiBase Y)
      (0 + (X.obj.obj.par + Y.obj.obj.par))
    simpa [qpiShift, zmod2_sub] using f.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem qpiHomEquiv_apply {X Y : QPiUnderlying k C} (f : X ⟶ Y) :
    (qpiHomEquiv X Y f : qpiBase X ⟶ qpiBase Y) = QPiEnvelope.toHom f.1.1 := rfl

theorem qpiHomEquiv_id (X : QPiUnderlying k C) :
    (qpiHomEquiv X X (𝟙 X) : qpiBase X ⟶ qpiBase X) = 𝟙 (qpiBase X) := rfl

theorem qpiHomEquiv_comp {X Y Z : QPiUnderlying k C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (qpiHomEquiv X Z (f ≫ g) : qpiBase X ⟶ qpiBase Z) =
      (qpiHomEquiv X Y f : qpiBase X ⟶ qpiBase Y) ≫ (qpiHomEquiv Y Z g : _) := rfl

theorem qpiHomEquiv_add {X Y : QPiUnderlying k C} (f g : X ⟶ Y) :
    (qpiHomEquiv X Y (f + g) : qpiBase X ⟶ qpiBase Y) =
      (qpiHomEquiv X Y f : qpiBase X ⟶ qpiBase Y) + (qpiHomEquiv X Y g : _) := rfl

theorem qpiHomEquiv_smul {X Y : QPiUnderlying k C} (r : k) (f : X ⟶ Y) :
    (qpiHomEquiv X Y (r • f) : qpiBase X ⟶ qpiBase Y) =
      r • (qpiHomEquiv X Y f : qpiBase X ⟶ qpiBase Y) := rfl

/-! ## The functor -/

variable (k C) in
/-- **BE2 §11.** The functor `Q^m Π^a λ ↦ Q^m Π^a (1_λ · Mat)` from the underlying category
of the `(Q, Π)`-envelope to graded right supermodules over the Hom-matrix algebra of all objects of
`C`. -/
def rowFunctor : QPiUnderlying k C ⥤ GSMod.{u, v, w, v, max v w} k (fun X : C => X) where
  obj X := GSMod.shift (qpiShift X) (rowModule (k := k) (qpiBase X))
  map {X Y} f := (GSMod.rowModuleHomEquiv _ _ _ _).symm (qpiHomEquiv X Y f)
  map_id X := GSMod.rowHom_ext (by
    rw [GSMod.rowModuleHomEquiv_symm_rowGen, qpiHomEquiv_id]; rfl)
  map_comp {X Y Z} f g := GSMod.rowHom_ext (by
    rw [GSMod.rowModuleHomEquiv_symm_rowGen, GSMod.comp_apply,
      GSMod.rowModuleHomEquiv_symm_rowGen, GSMod.apply_eq_act_rowGen,
      GSMod.rowModuleHomEquiv_symm_rowGen, qpiHomEquiv_comp, rowToMat_single]
    exact (rowAct_single_single (k := k) (obj := fun X : C => X) (qpiBase Z) (qpiBase Y)
      (qpiBase X) _ _).symm)

theorem rowFunctor_map_rowGen {X Y : QPiUnderlying k C} (f : X ⟶ Y) :
    ((rowFunctor k C).map f).toLinearMap (rowGen (qpiBase X)) =
      (DFinsupp.single (qpiBase X) (QPiEnvelope.toHom f.1.1) :
        Row (fun X : C => X) (qpiBase Y)) :=
  GSMod.rowModuleHomEquiv_symm_rowGen _ _ _ _ _

/-- The Yoneda bijection for the row modules underlying `X` and `Y`. -/
abbrev qpiRowHomEquiv (X Y : QPiUnderlying k C) :=
  GSMod.rowModuleHomEquiv (k := k) (obj := fun X : C => X) (qpiShift X) (qpiShift Y)
    (qpiBase Y) (qpiBase X)

/-- **BE2 §11.** The row-module functor is fully faithful. -/
def rowFunctorFullyFaithful : (rowFunctor k C).FullyFaithful where
  preimage {X Y} φ := (qpiHomEquiv X Y).symm (qpiRowHomEquiv X Y φ)
  map_preimage {X Y} φ := by
    change (qpiRowHomEquiv X Y).symm (qpiHomEquiv X Y
      ((qpiHomEquiv X Y).symm (qpiRowHomEquiv X Y φ))) = φ
    simp
  preimage_map {X Y} f := by
    change (qpiHomEquiv X Y).symm (qpiRowHomEquiv X Y
      ((qpiRowHomEquiv X Y).symm (qpiHomEquiv X Y f))) = f
    simp

instance : (rowFunctor k C).Full := rowFunctorFullyFaithful.full

instance : (rowFunctor k C).Faithful := rowFunctorFullyFaithful.faithful

theorem rowFunctor_map_eq {X Y : QPiUnderlying k C} (f : X ⟶ Y) :
    (rowFunctor k C).map f = (qpiRowHomEquiv X Y).symm (qpiHomEquiv X Y f) := rfl

instance : (rowFunctor k C).Additive where
  map_add {X Y f g} := by
    simp only [rowFunctor_map_eq]
    refine GSMod.rowHom_ext ?_
    rw [GSMod.add_toLinearMap, LinearMap.add_apply, GSMod.rowModuleHomEquiv_symm_rowGen,
      GSMod.rowModuleHomEquiv_symm_rowGen, GSMod.rowModuleHomEquiv_symm_rowGen, qpiHomEquiv_add]
    exact DFinsupp.single_add _ _ _

instance : (rowFunctor k C).Linear k where
  map_smul {X Y} f r := by
    simp only [rowFunctor_map_eq]
    refine GSMod.rowHom_ext ?_
    rw [GSMod.smul_toLinearMap, LinearMap.smul_apply, GSMod.rowModuleHomEquiv_symm_rowGen,
      GSMod.rowModuleHomEquiv_symm_rowGen, qpiHomEquiv_smul]
    exact DFinsupp.single_smul _ _

end OddMath.FiniteHomMatrix
