/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.OddNilHeckeGrading
import Categorification.Diagrams.NilHecke.Comparison

/-!
# The even same-colour map

BE2, arXiv:1701.04133v2, §11, the same-colour corner preceding Lemma 11.1, for an even colour.
The dot and crossing of one fixed even colour satisfy the relations of the diagrammatic nilHecke
category `Categorification.NilHecke.Diagram.NH` of categorification-lean, so it maps to the
quiver Hecke supercategory, and the integral nilHecke ring `NH_m` (presented by
`Categorification.KLR.NilHecke.lift`) maps to the corner `End(i^m)`. Positions are counted from the
left; BE2 numbers the same strands from right to left.

## Main declarations

* `evenFunctor`, `evenCorner`: the functor from the presented nilHecke category and the
  algebra map on endomorphisms of `m` strands.
* `evenNilHecke D Sc i hi m : nilHecke ℤ m →ₐ[ℤ] Corner D Sc i m`, with `evenNilHecke_mulX`
  and `evenNilHecke_dd` on the generators.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
variable {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Colour the nilHecke signature with one colour. -/
def evenColour (i : I) : SigMap Categorification.NilHecke.Diagram.sig (sig D) where
  region _ := ()
  colour _ := i
  colourSrc _ := rfl
  colourTgt _ := rfl
  gen g := match g with | .dot => .dot i | .cross => .cross i i
  dom g := by cases g <;> rfl
  cod g := by cases g <;> rfl
  left _ := rfl
  right _ := rfl

theorem evenColour_odd (i : I) (hi : D.parity i = 0) (g : Categorification.NilHecke.Diagram.Gen) :
    (sig D).odd ((evenColour D i).gen g) = Categorification.NilHecke.Diagram.sig.odd g := by
  cases g <;> simp [sig, evenColour, Shape.parity, hi, Categorification.NilHecke.Diagram.sig]

/-- The four local nilHecke relations become the corresponding BE2 relations. -/
theorem evenColour_rel (i : I) (hi : D.parity i = 0) (r : Categorification.NilHecke.Diagram.Rel) :
    (freeLift k ((evenColour D i).toLayerMap.toPresented (pres D Sc) fun _ => 1)).map
      ((Categorification.NilHecke.Diagram.pres k).rel r) = 0 := by
  rw [LayerMap.freeLift_toPresented_one]
  cases r <;> simp only [Categorification.NilHecke.Diagram.pres,
    Categorification.NilHecke.Diagram.relation,
    LayerMap.lin_sub, LayerMap.lin_of, LayerMap.map_id]
  case crossSq =>
    exact (pres D Sc).lin_rel_self (.quadEq i)
  case braid =>
    exact (pres D Sc).lin_rel_self (.braid i i i (by simp))
  case slideA =>
    have h := (pres D Sc).lin_rel_self (.slideREq i)
    simp only [pres, relation, hi, mul_zero, SKM.zsign, zero_ne_one, ite_false, one_smul] at h
    convert h using 1 <;> congr 3
  case slideB =>
    have h := (pres D Sc).lin_rel_self (.slideLEq i)
    simp only [pres, relation, hi, mul_zero, SKM.zsign, zero_ne_one, ite_false, one_smul] at h
    convert h using 1 <;> congr 3

/-- The same-colour functor from the nilHecke category over `k`. -/
def evenFunctor (i : I) (hi : D.parity i = 0) : Categorification.NilHecke.Diagram.NH k ⥤ H D Sc :=
  (evenColour D i).lift (Categorification.NilHecke.Diagram.pres k) (evenColour_odd D i hi)
    (evenColour_rel D Sc i hi)

instance evenFunctor_additive (i : I) (hi : D.parity i = 0) :
    (evenFunctor D Sc i hi).Additive := by unfold evenFunctor; infer_instance

instance evenFunctor_linear (i : I) (hi : D.parity i = 0) :
    (evenFunctor D Sc i hi).Linear k := by unfold evenFunctor; infer_instance

/-- The same-colour algebra homomorphism on endomorphisms of `n` strands. -/
def evenCorner (i : I) (hi : D.parity i = 0) (n : ℕ) :
    End ((Categorification.NilHecke.Diagram.pres k).obj
      (Categorification.NilHecke.Diagram.strands n)) →ₐ[k] Corner D Sc i n := by
  let F := evenFunctor D Sc i hi
  have he : F.obj ((Categorification.NilHecke.Diagram.pres k).obj
      (Categorification.NilHecke.Diagram.strands n)) =
        (pres D Sc).obj (ob D (List.replicate n i)) := by
    change (pres D Sc).obj ⟨(), (List.replicate n ()).map (fun _ => i)⟩ = _
    simp only [List.map_replicate]
    rfl
  exact
    { toFun := fun f => eqToHom he.symm ≫ F.map f ≫ eqToHom he
      map_zero' := by simp
      map_one' := by simp
      map_add' := by
        intro a b
        change eqToHom he.symm ≫ F.map (a + b) ≫ eqToHom he =
          (eqToHom he.symm ≫ F.map a ≫ eqToHom he) +
            (eqToHom he.symm ≫ F.map b ≫ eqToHom he)
        rw [F.map_add, Preadditive.add_comp, Preadditive.comp_add]
      map_mul' := by
        intro a b
        change eqToHom he.symm ≫ F.map (b ≫ a) ≫ eqToHom he =
          (eqToHom he.symm ≫ F.map b ≫ eqToHom he) ≫
            (eqToHom he.symm ≫ F.map a ≫ eqToHom he)
        simp [Category.assoc]
      commutes' := fun r => by
        change eqToHom he.symm ≫ F.map (r • 𝟙 _) ≫ eqToHom he = r • 𝟙 _
        simp }

/-- The integral nilHecke ring `NH_m` maps to the even same-colour corner. -/
def evenNilHecke (i : I) (hi : D.parity i = 0) (m : ℕ) :
    Categorification.NilHecke.nilHecke ℤ m →ₐ[ℤ] Corner D Sc i m :=
  ((evenCorner D Sc i hi m).restrictScalars ℤ).comp
    (Categorification.KLR.NilHecke.lift (Categorification.NilHecke.Diagram.isNilHeckeFamily k m))

theorem evenNilHecke_mulX (i : I) (hi : D.parity i = 0) (m : ℕ) (a : Fin m) :
    evenNilHecke D Sc i hi m ⟨Categorification.NilHecke.mulX ℤ m a,
      Categorification.NilHecke.mulX_mem a⟩ =
      evenCorner D Sc i hi m (Categorification.NilHecke.Diagram.x k m a) := by
  simp [evenNilHecke]

theorem evenNilHecke_dd (i : I) (hi : D.parity i = 0) (m j : ℕ) :
    evenNilHecke D Sc i hi m ⟨Categorification.NilHecke.dd ℤ m j,
      Categorification.NilHecke.dd_mem j⟩ =
      evenCorner D Sc i hi m (Categorification.NilHecke.Diagram.ψ k m j) := by
  simp [evenNilHecke]

end OddMath.QuiverHecke
