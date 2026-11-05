/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendContentCorner
import OddMath.QuiverHecke.CyclotomicAction.AppendMackeyRho

/-!
# The append Mackey map on a cyclotomic content corner

This instantiates the source coefficient module of `AppendMackeySource.md` §4 and
restricts the map to the left append idempotent, as required by
`DeformedMackeyBoundary.md` (1). The cyclotomic annihilation and constant-parity
conditions are proved for the content corner, not supplied as hypotheses.
The unchanged right coefficient action satisfies the source transport field `P_r`.
These are ordinary cyclotomic polynomial coefficients; no exterior deformation is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Categorification.InductionAlong Supercategory
open scoped Classical
namespace OddMath.QuiverHecke
open SKM (zsign)
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (n : ℕ) (β : Multiset I) (i : I)

/-- The parity of the moving cyclotomic crossing on content `β`. -/
def appendContentParity : ZMod 2 :=
  (a i).natDegree • D.parity i + D.parity i * (β.map D.parity).sum

omit [Fintype I] in

local notation "B" => CyclotomicContentCorner D Sc a n β
local notation "eps" => appendContentParity D a β i
local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
local notation "L" => Ind B (prependTwist D Sc i n eps)

/-- The left append-idempotent part of twisted prepend induction. -/
def appendContentSource : AddSubgroup L where
  carrier := {z | (ψ 1 : Hn D Sc (n + 1 + 1)) • z = z}
  zero_mem' := smul_zero _
  add_mem' hz hw := (smul_add _ _ _).trans (congrArg₂ (· + ·) hz hw)
  neg_mem' hz := (smul_neg _ _).trans (congrArg Neg.neg hz)

variable (ha : CyclotomicPolynomialParity D a)

/-- The first-dot operator with the constant content sign. -/
def appendContentRho : appendContentSource D Sc a n β i →+
    appendContentSource D Sc a n β i :=
  zsign ℤ (appendSourceSign D a i eps) • AddMonoidHom.codRestrict
    ((appendSourceDot D Sc i n eps (contentCornerParity D Sc a n β i ha).toAddMonoidHom
      (contentCornerParity_smul D Sc a n β i ha)).toAddMonoidHom.comp
        (appendContentSource D Sc a n β i).subtype) (appendContentSource D Sc a n β i) fun z => by
    change (ψ 1 : Hn D Sc (n + 1 + 1)) • _ = _
    let R := appendSourceDot D Sc i n eps (contentCornerParity D Sc a n β i ha).toAddMonoidHom
      (contentCornerParity_smul D Sc a n β i ha)
    exact (R.map_smul (ψ 1) z.1).symm.trans (congrArg R z.2)

end OddMath.QuiverHecke
