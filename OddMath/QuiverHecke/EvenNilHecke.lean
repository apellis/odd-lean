/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.OddNilHeckeGrading
import OddMath.Diagrams.EvenNilHecke.Relations
import Categorification.KLR.Examples.NilHecke

/-!
# The even same-colour map

BE2, arXiv:1701.04133v2, §11, the same-colour corner preceding Lemma 11.1, for an even colour.
The dot and crossing of one fixed even colour satisfy the nilHecke relations, so the nilHecke
ring `NH_m` of categorification-lean (over `ℤ`, presented by `Categorification.KLR.NilHecke.lift`)
maps to the corner `End(i^m)` of the quiver Hecke supercategory. Positions are counted from the
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
def evenColour (i : I) : SigMap Diagrams.EvenNilHecke.sig (sig D) where
  region _ := ()
  colour _ := i
  colourSrc _ := rfl
  colourTgt _ := rfl
  gen g := match g with | .dot => .dot i | .cross => .cross i i
  dom g := by cases g <;> rfl
  cod g := by cases g <;> rfl
  left _ := rfl
  right _ := rfl

theorem evenColour_odd (i : I) (hi : D.parity i = 0) (g : Diagrams.EvenNilHecke.Gen) :
    (sig D).odd ((evenColour D i).gen g) = Diagrams.EvenNilHecke.sig.odd g := by
  cases g <;> simp [sig, evenColour, Shape.parity, hi, Diagrams.EvenNilHecke.sig]

/-- The four local nilHecke relations become the corresponding BE2 relations. -/
theorem evenColour_rel (i : I) (hi : D.parity i = 0) (r : Diagrams.EvenNilHecke.Rel) :
    (freeLift k ((evenColour D i).toLayerMap.toPresented (pres D Sc) fun _ => 1)).map
      ((Diagrams.EvenNilHecke.pres k).rel r) = 0 := by
  rw [LayerMap.freeLift_toPresented_one]
  cases r <;> simp only [Diagrams.EvenNilHecke.pres, Diagrams.EvenNilHecke.relation,
    LayerMap.lin_sub, LayerMap.lin_of, LayerMap.map_id]
  case square =>
    exact (pres D Sc).lin_rel_self (.quadEq i)
  case braid =>
    exact (pres D Sc).lin_rel_self (.braid i i i (by simp))
  case mixedRight =>
    have h := (pres D Sc).lin_rel_self (.slideREq i)
    simp only [pres, relation, hi, mul_zero, SKM.zsign, zero_ne_one, ite_false, one_smul] at h
    convert h using 1 <;> congr 3
  case mixedLeft =>
    have h := (pres D Sc).lin_rel_self (.slideLEq i)
    simp only [pres, relation, hi, mul_zero, SKM.zsign, zero_ne_one, ite_false, one_smul] at h
    convert h using 1 <;> congr 3

/-- The same-colour functor from the nilHecke category over `k`. -/
def evenFunctor (i : I) (hi : D.parity i = 0) : Diagrams.EvenNilHecke.NH k ⥤ H D Sc :=
  (evenColour D i).lift (Diagrams.EvenNilHecke.pres k) (evenColour_odd D i hi)
    (evenColour_rel D Sc i hi)

instance evenFunctor_additive (i : I) (hi : D.parity i = 0) :
    (evenFunctor D Sc i hi).Additive := by unfold evenFunctor; infer_instance

instance evenFunctor_linear (i : I) (hi : D.parity i = 0) :
    (evenFunctor D Sc i hi).Linear k := by unfold evenFunctor; infer_instance

/-- The same-colour algebra homomorphism on endomorphisms of `n` strands. -/
def evenCorner (i : I) (hi : D.parity i = 0) (n : ℕ) :
    End ((Diagrams.EvenNilHecke.pres k).obj (Diagrams.EvenNilHecke.strands n)) →ₐ[k]
      Corner D Sc i n := by
  let F := evenFunctor D Sc i hi
  have he : F.obj ((Diagrams.EvenNilHecke.pres k).obj (Diagrams.EvenNilHecke.strands n)) =
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

namespace EvenNilHecke

open Diagrams.EvenNilHecke

/-- Dots and crossings of the presented nilHecke category form a nilHecke family in the sense
of categorification-lean (KL I §2.2, Example 3). -/
theorem isNilHeckeFamily (m : ℕ) :
    Categorification.KLR.NilHecke.IsNilHeckeFamily
      (B := End ((Diagrams.EvenNilHecke.pres k).obj (strands m))) m
      (fun a => x k m a) (fun j => ψ k m j) where
  x_comm _ _ := x_mul_x k
  d_x_comm _ _ h₁ h₂ := ψ_mul_x_of_ne k h₁ h₂
  d_comm _ _ h := ψ_mul_ψ_of_lt k h
  d_sq j := ψ_mul_ψ k m j
  braid j := ψ_braid k m j
  x_d_sub _ h := x_mul_ψ_sub_ψ_mul_x k h
  d_x_sub _ h := ψ_mul_x_sub_x_mul_ψ k h
  d_zero _ h := ψ_of_le k h

end EvenNilHecke

/-- The integral nilHecke ring `NH_m` maps to the even same-colour corner. -/
def evenNilHecke (i : I) (hi : D.parity i = 0) (m : ℕ) :
    Categorification.NilHecke.nilHecke ℤ m →ₐ[ℤ] Corner D Sc i m :=
  ((evenCorner D Sc i hi m).restrictScalars ℤ).comp
    (Categorification.KLR.NilHecke.lift (EvenNilHecke.isNilHeckeFamily (k := k) m))

theorem evenNilHecke_mulX (i : I) (hi : D.parity i = 0) (m : ℕ) (a : Fin m) :
    evenNilHecke D Sc i hi m ⟨Categorification.NilHecke.mulX ℤ m a,
      Categorification.NilHecke.mulX_mem a⟩ =
      evenCorner D Sc i hi m (Diagrams.EvenNilHecke.x k m a) := by
  simp [evenNilHecke]

theorem evenNilHecke_dd (i : I) (hi : D.parity i = 0) (m j : ℕ) :
    evenNilHecke D Sc i hi m ⟨Categorification.NilHecke.dd ℤ m j,
      Categorification.NilHecke.dd_mem j⟩ =
      evenCorner D Sc i hi m (Diagrams.EvenNilHecke.ψ k m j) := by
  simp [evenNilHecke]

end OddMath.QuiverHecke
