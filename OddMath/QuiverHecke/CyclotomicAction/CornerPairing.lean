/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.SuperRestriction

/-!
# The cyclotomic corner pairing

Ports the multiplication pairing underlying
`Categorification/TwoRep/CyclotomicRouqAdjunction.lean` to the actual
cyclotomic superbimodules. The evaluation is an even superbimodule map;
its balanced-tensor source retains the signs of odd morphisms.
-/

noncomputable section
open CategoryTheory StringDiagrams
open SuperBimodule
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "A" => CyclotomicAlgebra D Sc a n
local notation "B" => CyclotomicAlgebra D Sc a (n + 1)
local notation "GA" => cyclotomicParity D Sc a ha n
local notation "GB" => cyclotomicParity D Sc a ha (n + 1)
local notation "φ" => cyclotomicAppend D Sc i a n
local notation "P" => inductionCorner D Sc i a ha n
local notation "Q" => restrictionCorner D Sc i a ha n

/-- Homogeneity in the induction corner is inherited from the algebra. -/
theorem inductionCorner_mem_part_iff {p : ZMod 2} {x : (P).toSVec} :
    x ∈ (P).toSVec.part p ↔ x.1 ∈ GB p := by
  change x ∈ (SVec.sub _ _ _).part p ↔ _
  rw [SVec.mem_sub_part_iff, mem_regularSVec_part_iff]

/-- The even colour-cut idempotent in the induction bimodule. -/
def inductionCornerIdempotent : (P).toSVec :=
  ⟨φ 1, by change φ 1 * φ 1 = φ 1; rw [← map_mul, mul_one]⟩

/-- The lower algebra maps into the restriction bimodule. -/
def restrictionCornerOf : A →ₗ[k] (Q).toSVec where
  toFun r := ⟨φ r, by change φ 1 * φ r = φ r; rw [← map_mul, one_mul]⟩
  map_add' r s := Subtype.ext (map_add φ r s)
  map_smul' c r := Subtype.ext (map_smul φ c r)

theorem inductionCornerIdempotent_mem :
    inductionCornerIdempotent D Sc i a ha n ∈ (P).toSVec.part 0 :=
  (inductionCorner_mem_part_iff D Sc i a ha n).mpr
    (cyclotomicAppend_parity D Sc i a ha n (SetLike.one_mem_graded GA))

end OddMath.QuiverHecke
