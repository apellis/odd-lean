/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Module.AEval
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendMovingSlide
import OddMath.QuiverHecke.CyclotomicAction.ELVPDescent
import OddMath.QuiverHecke.CyclotomicAction.ELVRelationRegularity

/-!
# Central moving-variable linearity of ELV P

`DeformedSquareResolution.md` §§1,3: the prescribed P intertwines the moving
dot for even colour and moving square for odd colour. Decorated deletion
slides are combined with even-power commutation with the full ELV relation.
Both actions preserve their old relation spaces, including zero cutoffs.
No unchanged odd-dot intertwining or centrality of the odd relation is used.

The polynomial map is over the ground polynomial ring k[s], with commuting
twisted old operators annihilating the old ideal. Assembly into a content-level
right B[s]-module, and projectivity, are separate obligations.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem movingPower_comp_movingPower (i : I) (v : List I) (d e : ℕ) :
    movingPower D Sc cutoff i v d ≫ movingPower D Sc cutoff i v e =
      movingPower D Sc cutoff i v (d + e) := by
  change affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0 ^ d) ≫
    affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0 ^ e) = _
  rw [← affineUnit_comp]
  change affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0 ^ e * dotE D Sc (i :: v) 0 ^ d) = _
  rw [← pow_add, Nat.add_comm]
  rfl

theorem movingPower_deformedCyclotomic (i : I) (v : List I) (d : ℕ)
    (hd : d • D.parity i = 0) (N : ℕ) (c : Fin (N + 1) → SKM.SYM D k) :
    movingPower D Sc cutoff i v d ≫
        (elvQuotientFunctor D Sc cutoff).map (deformedCyclotomic D Sc (i :: v) N c) =
      (elvQuotientFunctor D Sc cutoff).map (deformedCyclotomic D Sc (i :: v) N c) ≫
        movingPower D Sc cutoff i v d := by
  rw [deformedCyclotomic_expansion, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [Category.assoc, ← movingPower_insert D Sc cutoff i d hd, ← Category.assoc,
    ← Category.assoc, movingPower_comp_movingPower, movingPower_comp_movingPower,
    Nat.add_comm d j.val]

theorem movingPower_relation (i : I) (v : List I) (d : ℕ)
    (hd : d • D.parity i = 0) :
    movingPower D Sc cutoff i v d ≫ relation D Sc cutoff i v =
      relation D Sc cutoff i v ≫ movingPower D Sc cutoff i v d := by
  unfold relation
  split_ifs <;> apply movingPower_deformedCyclotomic D Sc cutoff i v d hd

theorem appendDecoratedW_even (i : I) (v : List I) (d : ℕ)
    (hd : d • D.parity i = 0) :
    appendDecoratedW D Sc cutoff i v d =
      appendW D Sc cutoff i v ≫ movingPower D Sc cutoff i v d := by
  rw [appendDecoratedW, movingPower_relation D Sc cutoff i v d hd, ← Category.assoc]
  rfl

def appendMovingPower (i : I) (v : List I) (d : ℕ) :
    hom D Sc cutoff (v ++ [i]) (v ++ [i]) :=
  affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) v.length ^ d)

theorem appendMovingPower_relations (i : I) {v w : List I} (d : ℕ)
    {h : hom D Sc cutoff (v ++ [i]) w} (hh : h ∈ appendRelations D Sc cutoff i v w) :
    appendMovingPower D Sc cutoff i v d ≫ h ∈ appendRelations D Sc cutoff i v w := by
  induction d with
  | zero => simpa [appendMovingPower, affineUnit_id, End.one_def] using hh
  | succ d ih =>
    have he : appendMovingPower D Sc cutoff i v (d + 1) =
        affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) v.length) ≫
          appendMovingPower D Sc cutoff i v d := by
      simp only [appendMovingPower, pow_succ, End.mul_def, affineUnit_comp]
    rw [he, Category.assoc]
    exact lastDot_comp_mem_appendRelations D Sc cutoff i ih

def appendMovingPowerTarget (i : I) (v w : List I) (d : ℕ) :
    AppendTarget D Sc cutoff i v w →ₗ[k] AppendTarget D Sc cutoff i v w :=
  (appendRelations D Sc cutoff i v w).mapQ (appendRelations D Sc cutoff i v w)
    (Linear.leftComp k _ (appendMovingPower D Sc cutoff i v d))
    (fun _ hh => appendMovingPower_relations D Sc cutoff i d hh)

@[simp] theorem appendMovingPowerTarget_projection (i : I) (v w : List I) (d : ℕ)
    (h : hom D Sc cutoff (v ++ [i]) w) :
    appendMovingPowerTarget D Sc cutoff i v w d (appendProjection D Sc cutoff i v w h) =
      appendProjection D Sc cutoff i v w (appendMovingPower D Sc cutoff i v d ≫ h) := rfl

theorem pMap_movingSquare (i : I) (v w : List I) (z : Target D Sc cutoff i v w) :
    pMap D Sc cutoff i v w
        (movingPowerTarget D Sc cutoff i v w 2
          ((by decide : ∀ q : ZMod 2, (2 : ℕ) • q = 0) (D.parity i)) z) =
      appendMovingPowerTarget D Sc cutoff i v w 2 (pMap D Sc cutoff i v w z) := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  change appendProjection D Sc cutoff i v w (appendW D Sc cutoff i v ≫
      (movingPower D Sc cutoff i v 2 ≫ h)) =
    appendProjection D Sc cutoff i v w (appendMovingPower D Sc cutoff i v 2 ≫
      (appendW D Sc cutoff i v ≫ h))
  have he := lastDotSquare_comp_appendDecoratedW_mem D Sc cutoff i v 0
  rw [appendDecoratedW_zero, zero_add, appendDecoratedW_even D Sc cutoff i v 2
    ((by decide : ∀ q : ZMod 2, (2 : ℕ) • q = 0) (D.parity i))] at he
  have hz := (appendProjection_eq_zero_iff D Sc cutoff i v w _).mpr
    (appendRelations_comp D Sc cutoff i he h)
  rw [Preadditive.sub_comp, map_sub, sub_eq_zero] at hz
  simpa only [Category.assoc, appendMovingPower] using hz.symm

theorem pMap_movingEvenDot (i : I) (hi : D.parity i = 0) (v w : List I)
    (z : Target D Sc cutoff i v w) :
    pMap D Sc cutoff i v w (movingPowerTarget D Sc cutoff i v w 1 (by simp [hi]) z) =
      appendMovingPowerTarget D Sc cutoff i v w 1 (pMap D Sc cutoff i v w z) := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  change appendProjection D Sc cutoff i v w (appendW D Sc cutoff i v ≫
      (movingPower D Sc cutoff i v 1 ≫ h)) =
    appendProjection D Sc cutoff i v w (appendMovingPower D Sc cutoff i v 1 ≫
      (appendW D Sc cutoff i v ≫ h))
  have he := lastDot_comp_appendDecoratedW_mem D Sc cutoff i v 0
  rw [appendDecoratedW_zero, zero_add, appendDecoratedW_even D Sc cutoff i v 1 (by simp [hi])] at he
  simp only [hi, zero_mul, SKM.zsign, zero_ne_one, ite_false, one_smul] at he
  have hz := (appendProjection_eq_zero_iff D Sc cutoff i v w _).mpr
    (appendRelations_comp D Sc cutoff i he h)
  rw [Preadditive.sub_comp, map_sub, sub_eq_zero] at hz
  simpa only [Category.assoc, appendMovingPower, pow_one] using hz.symm

def appendOldSourceTarget (i : I) (v w : List I) (c : hom D Sc cutoff v v) :
    AppendTarget D Sc cutoff i v w →ₗ[k] AppendTarget D Sc cutoff i v w :=
  (appendRelations D Sc cutoff i v w).mapQ (appendRelations D Sc cutoff i v w)
    (Linear.leftComp k _ (rightContext D Sc cutoff [i] v v c))
    (fun _ hh => comp_appendRelations D Sc cutoff i c hh)

/-- The parity-shifted source action and the unchanged append action intertwine.
This reuses the proved old balance; no balance hypothesis is supplied. -/
theorem pMap_twistedOldSource (i : I) (v w : List I) (c : hom D Sc cutoff v v)
    (z : Target D Sc cutoff i v w) :
    pMap D Sc cutoff i v w
        (oldSourceTarget D Sc cutoff i v w (twist k (appendQ D cutoff i v) c) z) =
      appendOldSourceTarget D Sc cutoff i v w c (pMap D Sc cutoff i v w z) := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  have he := appendRelations_comp D Sc cutoff i
    (appendError_mem_appendRelations D Sc cutoff i c) h
  have hz := (appendProjection_eq_zero_iff D Sc cutoff i v w _).mpr he
  rw [appendError_apply, Preadditive.sub_comp, map_sub, sub_eq_zero] at hz
  change appendProjection D Sc cutoff i v w (appendW D Sc cutoff i v ≫
      (insert D Sc cutoff i v v (twist k (appendQ D cutoff i v) c) ≫ h)) =
    appendProjection D Sc cutoff i v w (rightContext D Sc cutoff [i] v v c ≫
      (appendW D Sc cutoff i v ≫ h))
  simpa only [Category.assoc] using hz.symm

/-- The prescribed central exponent is one at even colour, two at odd colour. -/
def centralDegree (i : I) : ℕ := if D.parity i = 0 then 1 else 2

theorem centralDegree_even (i : I) : centralDegree D i • D.parity i = 0 := by
  unfold centralDegree
  split_ifs with hi
  · simp [hi]
  · exact (by decide : ∀ q : ZMod 2, (2 : ℕ) • q = 0) (D.parity i)

abbrev centralSource (i : I) (v w : List I) :=
  movingPowerTarget D Sc cutoff i v w (centralDegree D i) (centralDegree_even D i)

abbrev centralAppend (i : I) (v w : List I) :=
  appendMovingPowerTarget D Sc cutoff i v w (centralDegree D i)

theorem pMap_central (i : I) (v w : List I) (z : Target D Sc cutoff i v w) :
    pMap D Sc cutoff i v w (centralSource D Sc cutoff i v w z) =
      centralAppend D Sc cutoff i v w (pMap D Sc cutoff i v w z) := by
  unfold centralSource centralAppend centralDegree
  split_ifs with hi
  · exact pMap_movingEvenDot D Sc cutoff i hi v w z
  · exact pMap_movingSquare D Sc cutoff i v w z

theorem centralSource_oldSource (i : I) (v w : List I) (c : hom D Sc cutoff v v)
    (z : Target D Sc cutoff i v w) :
    centralSource D Sc cutoff i v w (oldSourceTarget D Sc cutoff i v w c z) =
      oldSourceTarget D Sc cutoff i v w c (centralSource D Sc cutoff i v w z) := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  change projection D Sc cutoff i v w (movingPower D Sc cutoff i v _ ≫
    (insert D Sc cutoff i v v c ≫ h)) =
    projection D Sc cutoff i v w (insert D Sc cutoff i v v c ≫
      (movingPower D Sc cutoff i v _ ≫ h))
  rw [← Category.assoc, movingPower_insert D Sc cutoff i _ (centralDegree_even D i),
    Category.assoc]

theorem appendMovingPower_whisker (i : I) (v : List I) (d : ℕ) :
    appendMovingPower D Sc cutoff i v d =
      affineUnit D Sc cutoff (v ++ [i]) (v ++ [i]) ((pres D Sc).obj (ob D v) ◁ (dotE D Sc [i] 0 ^ d)) := by
  have he : (pres D Sc).obj (ob D v) ◁ (dotE D Sc [i] 0 ^ d) =
      dotE D Sc (v ++ [i]) v.length ^ d := by
    induction d with
    | zero => exact MonoidalSupercategory.whiskerLeft_id (R := k) _ _
    | succ d ih =>
      simp only [pow_succ, End.mul_def]
      rw [MonoidalSupercategory.whiskerLeft_comp (R := k), ih, whiskerLeft_dotE D Sc v i rfl]
  rw [he]
  rfl

theorem appendMovingPower_rightContext (i : I) (v : List I) (d : ℕ)
    (hd : d • D.parity i = 0) (c : hom D Sc cutoff v v) :
    appendMovingPower D Sc cutoff i v d ≫ rightContext D Sc cutoff [i] v v c =
      rightContext D Sc cutoff [i] v v c ≫ appendMovingPower D Sc cutoff i v d := by
  rw [appendMovingPower_whisker, trailing_comp_rightContext D Sc cutoff (v := v) (w := v)
    (hd ▸ firstDot_pow_parity D Sc i [] d)]
  simp only [twist_zero]

theorem centralAppend_oldSource (i : I) (v w : List I) (c : hom D Sc cutoff v v)
    (z : AppendTarget D Sc cutoff i v w) :
    centralAppend D Sc cutoff i v w (appendOldSourceTarget D Sc cutoff i v w c z) =
      appendOldSourceTarget D Sc cutoff i v w c (centralAppend D Sc cutoff i v w z) := by
  obtain ⟨h, rfl⟩ := appendProjection_surjective D Sc cutoff i v w z
  change appendProjection D Sc cutoff i v w (appendMovingPower D Sc cutoff i v _ ≫
    (rightContext D Sc cutoff [i] v v c ≫ h)) =
    appendProjection D Sc cutoff i v w (rightContext D Sc cutoff [i] v v c ≫
      (appendMovingPower D Sc cutoff i v _ ≫ h))
  rw [← Category.assoc, appendMovingPower_rightContext D Sc cutoff i v _ (centralDegree_even D i),
    Category.assoc]

/-- The old-only source with the prescribed central polynomial action. -/
abbrev CentralTarget (i : I) (v w : List I) :=
  Module.AEval' (centralSource D Sc cutoff i v w)

/-- The append-old target with the prescribed central polynomial action. -/
abbrev CentralAppendTarget (i : I) (v w : List I) :=
  Module.AEval' (centralAppend D Sc cutoff i v w)

/-- P is polynomial-linear for the dot at even colour and square at odd colour.
The intertwining proof is `pMap_central`, not an input assumption. -/
def pCentralMap (i : I) (v w : List I) :
    CentralTarget D Sc cutoff i v w →ₗ[Polynomial k] CentralAppendTarget D Sc cutoff i v w :=
  LinearMap.ofAEval (centralSource D Sc cutoff i v w)
    ((Module.AEval'.of (centralAppend D Sc cutoff i v w)).toLinearMap.comp
      (pMap D Sc cutoff i v w)) (fun z => by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [Module.AEval'.X_smul_of]
        exact congrArg (Module.AEval'.of (centralAppend D Sc cutoff i v w))
          (pMap_central D Sc cutoff i v w z))

@[simp] theorem pCentralMap_of (i : I) (v w : List I) (z : Target D Sc cutoff i v w) :
    pCentralMap D Sc cutoff i v w (Module.AEval'.of (centralSource D Sc cutoff i v w) z) =
      Module.AEval'.of (centralAppend D Sc cutoff i v w) (pMap D Sc cutoff i v w z) := rfl

/-- Each twisted old source operator is linear for the central polynomial action. -/
def centralOldSource (i : I) (v w : List I) (c : hom D Sc cutoff v v) :
    CentralTarget D Sc cutoff i v w →ₗ[Polynomial k] CentralTarget D Sc cutoff i v w :=
  LinearMap.ofAEval (centralSource D Sc cutoff i v w)
    ((Module.AEval'.of (centralSource D Sc cutoff i v w)).toLinearMap.comp
      (oldSourceTarget D Sc cutoff i v w (twist k (appendQ D cutoff i v) c))) (fun z => by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [Module.AEval'.X_smul_of]
        exact congrArg (Module.AEval'.of (centralSource D Sc cutoff i v w))
          (centralSource_oldSource D Sc cutoff i v w _ z).symm)

/-- Each append old operator is linear for the same central polynomial action. -/
def centralOldAppend (i : I) (v w : List I) (c : hom D Sc cutoff v v) :
    CentralAppendTarget D Sc cutoff i v w →ₗ[Polynomial k] CentralAppendTarget D Sc cutoff i v w :=
  LinearMap.ofAEval (centralAppend D Sc cutoff i v w)
    ((Module.AEval'.of (centralAppend D Sc cutoff i v w)).toLinearMap.comp
      (appendOldSourceTarget D Sc cutoff i v w c)) (fun z => by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [Module.AEval'.X_smul_of]
        exact congrArg (Module.AEval'.of (centralAppend D Sc cutoff i v w))
          (centralAppend_oldSource D Sc cutoff i v w c z).symm)

theorem pCentralMap_oldSource (i : I) (v w : List I) (c : hom D Sc cutoff v v)
    (z : CentralTarget D Sc cutoff i v w) :
    pCentralMap D Sc cutoff i v w (centralOldSource D Sc cutoff i v w c z) =
      centralOldAppend D Sc cutoff i v w c (pCentralMap D Sc cutoff i v w z) :=
  pMap_twistedOldSource D Sc cutoff i v w c z

/-- Twisted old action factors through the old cyclotomic quotient. -/
theorem centralOldSource_ideal (i : I) (v w : List I) {c : hom D Sc cutoff v v}
    (hc : c ∈ ideal D Sc cutoff v v) (z : CentralTarget D Sc cutoff i v w) :
    centralOldSource D Sc cutoff i v w c z = 0 := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  exact projection_old_ideal D Sc cutoff i (twist_ideal D Sc cutoff _ hc) h

/-- The append action also factors through the old cyclotomic quotient. -/
theorem centralOldAppend_ideal (i : I) (v w : List I) {c : hom D Sc cutoff v v}
    (hc : c ∈ ideal D Sc cutoff v v) (z : CentralAppendTarget D Sc cutoff i v w) :
    centralOldAppend D Sc cutoff i v w c z = 0 := by
  obtain ⟨h, rfl⟩ := appendProjection_surjective D Sc cutoff i v w z
  exact appendProjection_old_ideal D Sc cutoff i hc h

end OddMath.QuiverHecke.ELVOld
