/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendContentCosets

/-!
# Corrected-rho coordinates of the moving source coset

The ordinary-polynomial specialization of `DeformedMackeyBoundary.md` (6)–(7).
The prescribed full moving shuffle is normalized by the content sign in each
input-dot degree. This supplies compatible lifts for the source of the Mackey
boundary, without assuming an identification of the short image with crossings.
The content corner has old height `n + 1`; `n = 0` is not old height zero.
No restriction on the cyclotomic cutoff is imposed.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Categorification.InductionAlong Supercategory
open scoped Classical
namespace OddMath.QuiverHecke
open SKM (zsign)

/-- Degreewise sign normalization, leaving the right coefficient in its original order. -/
def movingSignNormalize {M : Type*} [AddCommGroup M] (p : ZMod 2) :
    (ℕ →₀ M) →+ (ℕ →₀ M) where
  toFun f := Finsupp.onFinset f.support (fun m => (zsign ℤ p) ^ m • f m)
    (fun m h => Finsupp.mem_support_iff.mpr (fun hz => h (by rw [hz, smul_zero])))
  map_zero' := by ext m; simp
  map_add' f g := by ext m; simp [smul_add]

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

variable (a : I → _root_.Polynomial k) (n : ℕ) (β : Multiset I) (i : I)
local notation "B" => CyclotomicContentCorner D Sc a n β
local notation "eps" => appendContentParity D a β i
local notation "p" => D.parity i * Multiset.sum (Multiset.map D.parity β)
local notation "coord" => prependTwistCoordinates D Sc i n eps B

/-- Extraction in the corrected-rho normalization. -/
def appendContentRhoExtract : appendContentSource D Sc a n β i →+ (ℕ →₀ B) :=
  (movingSignNormalize p).comp (appendContentLongExtract D Sc a n β i)

variable (ha : CyclotomicPolynomialParity D a)
local notation "θ" => RingHom.toAddMonoidHom (contentCornerParity D Sc a n β i ha)

end OddMath.QuiverHecke
