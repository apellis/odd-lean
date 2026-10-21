/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Grading
import OddMath.Diagrams.OddNilHecke.Coefficients
import StringDiagrams.LayerMap.Generators
import StringDiagrams.Biadjunction.Zigzag

/-!
# The odd same-colour map

BE2, arXiv:1701.04133v2, §11, the same-colour corner preceding Lemma 11.1.
The odd nilHecke generators are sent to the dot and crossing of one fixed
odd colour. Positions here follow the existing odd nilHecke library
(left to right); BE2 numbers these same strands from right to left.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
variable {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Colour the odd nilHecke signature with one colour. -/
def oddColour (i : I) : SigMap Diagrams.OddNilHecke.sig (sig D) where
  region _ := ()
  colour _ := i
  colourSrc _ := rfl
  colourTgt _ := rfl
  gen g := match g with | .dot => .dot i | .cross => .cross i i
  dom g := by cases g <;> rfl
  cod g := by cases g <;> rfl
  left _ := rfl
  right _ := rfl

theorem oddColour_odd (i : I) (hi : D.parity i = 1) (g : Diagrams.OddNilHecke.Gen) :
    (sig D).odd ((oddColour D i).gen g) = Diagrams.OddNilHecke.sig.odd g := by
  cases g <;> simp [sig, oddColour, Shape.parity, hi, Diagrams.OddNilHecke.sig]

/-- The four local odd nilHecke relations become the corresponding BE2 relations. -/
theorem oddColour_rel (i : I) (hi : D.parity i = 1) (r : Diagrams.OddNilHecke.Rel) :
    (freeLift k ((oddColour D i).toLayerMap.toPresented (pres D Sc) fun _ => 1)).map
      ((Diagrams.OddNilHecke.pres k).rel r) = 0 := by
  rw [LayerMap.freeLift_toPresented_one]
  cases r <;> simp only [Diagrams.OddNilHecke.pres, Diagrams.OddNilHecke.relation,
    LayerMap.lin_sub, LayerMap.lin_add, LayerMap.lin_of, LayerMap.map_id]
  case square =>
    exact (pres D Sc).lin_rel_self (.quadEq i)
  case braid =>
    exact (pres D Sc).lin_rel_self (.braid i i i (by simp))
  case mixedRight =>
    have h := (pres D Sc).lin_rel_self (.slideREq i)
    simp only [pres, relation, hi, mul_one, SKM.zsign, ite_true, neg_smul,
      one_smul, sub_neg_eq_add] at h
    convert h using 1 <;> congr 3
  case mixedLeft =>
    have h := (pres D Sc).lin_rel_self (.slideLEq i)
    simp only [pres, relation, hi, mul_one, SKM.zsign, ite_true, neg_smul,
      one_smul, sub_neg_eq_add] at h
    convert h using 1 <;> congr 3

/-- The same-colour functor from the odd nilHecke category over `k`. -/
def oddFunctor (i : I) (hi : D.parity i = 1) : Diagrams.OddNilHecke.ONH k ⥤ H D Sc :=
  (oddColour D i).lift (Diagrams.OddNilHecke.pres k) (oddColour_odd D i hi) (oddColour_rel D Sc i hi)

instance oddFunctor_additive (i : I) (hi : D.parity i = 1) :
    (oddFunctor D Sc i hi).Additive := by unfold oddFunctor; infer_instance

instance oddFunctor_linear (i : I) (hi : D.parity i = 1) :
    (oddFunctor D Sc i hi).Linear k := by unfold oddFunctor; infer_instance

/-- The same-colour algebra homomorphism on endomorphisms of `n` odd strands. -/
def oddCorner (i : I) (hi : D.parity i = 1) (n : ℕ) :
    End ((Diagrams.OddNilHecke.pres k).obj (Diagrams.OddNilHecke.strands n)) →ₐ[k]
      Corner D Sc i n := by
  let F := oddFunctor D Sc i hi
  have he : F.obj ((Diagrams.OddNilHecke.pres k).obj (Diagrams.OddNilHecke.strands n)) =
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

/-- The integral presented odd nilHecke ring maps to the odd same-colour corner.
The library parameter `n` denotes `n + 2` strands. -/
def oddNilHecke (i : I) (hi : D.parity i = 1) (n : ℕ) :
    Frontier.NilHeckeAction.Presented n →+* Corner D Sc i (n + 2) :=
  (oddCorner D Sc i hi (n + 2)).toRingHom.comp
    (Diagrams.OddNilHecke.toDiagramsOver k n)

end OddMath.QuiverHecke
