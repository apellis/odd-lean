/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.MatrixGrading
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! Entrywise functoriality of the finite-support Hom algebras, for BE2 (11.7)–(11.8). -/
noncomputable section
open scoped Classical
open CategoryTheory
namespace OddMath.FiniteHomMatrix
universe u v w t v' w'
variable {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
  [Preadditive C] [Linear k C] {C' : Type v'} [Category.{w'} C']
  [Preadditive C'] [Linear k C'] {J : Type t} {obj : J → C}
  (F : C ⥤ C') [F.Additive] [F.Linear k]

/-- Apply a linear functor to each matrix entry. -/
def mapLinear : Mat obj →ₗ[k] Mat (fun i => F.obj (obj i)) :=
  DFinsupp.mapRange.linearMap fun _ => F.mapLinearMap k

@[simp] theorem mapLinear_apply (a : Mat obj) (p : J × J) :
    mapLinear (k := k) F a p = F.map (a p) := rfl

@[simp] theorem mapLinear_single (i j : J) (f : obj j ⟶ obj i) :
    mapLinear (k := k) F (single i j f) = single i j (F.map f) := by
  simp [mapLinear, single, DFinsupp.mapRange.linearMap]

/-- Composition is respected, including products with incompatible middle indices. -/
theorem mapLinear_mul (a b : Mat obj) :
    mapLinear (k := k) F (a * b) = mapLinear (k := k) F a * mapLinear (k := k) F b := by
  induction a using induction with
  | hz => simp
  | ha a b ha hb => simp [add_mul, ha, hb]
  | hs i j f =>
    induction b using induction with
    | hz => simp
    | ha a b ha hb => simp [mul_add, ha, hb]
    | hs l m g =>
      by_cases h : j = l
      · subst l; simp
      · simp [h]

/-- The induced nonunital algebra homomorphism. Scalar compatibility is `map_smul`. -/
def map : Mat obj →ₙ+* Mat (fun i => F.obj (obj i)) where
  toFun := mapLinear (k := k) F
  map_zero' := (mapLinear F).map_zero
  map_add' := (mapLinear F).map_add
  map_mul' := mapLinear_mul F

@[simp] theorem map_single (i j : J) (f : obj j ⟶ obj i) :
    map (k := k) F (single i j f) = single i j (F.map f) := mapLinear_single F i j f

@[simp] theorem map_smul (r : k) (a : Mat obj) :
    map (k := k) F (r • a) = r • map (k := k) F a := (mapLinear F).map_smul r a

/-- Entrywise homogeneous functors preserve every simultaneous homogeneous piece. -/
theorem map_mem_component {Γ : Type*}
    (G : (p : J × J) → Γ → Submodule k (obj p.2 ⟶ obj p.1))
    (G' : (p : J × J) → Γ → Submodule k (F.obj (obj p.2) ⟶ F.obj (obj p.1)))
    (hF : ∀ p d f, f ∈ G p d → F.map f ∈ G' p d)
    {d : Γ} {a : Mat obj} (ha : a ∈ component G d) :
    map (k := k) F a ∈ component G' d := fun p => hF p d (a p) (ha p)

end OddMath.FiniteHomMatrix
