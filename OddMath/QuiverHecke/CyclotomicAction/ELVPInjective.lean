/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVQDescent
import OddMath.QuiverHecke.CyclotomicAction.ELVQPRegularity

/-!
# Injectivity of the full ELV P map

The actual quotient composite QP is regular in moving PBW coordinates.
Consequently the prescribed P map is injective, supplying the injectivity
step of the deformed square resolution. Polynomial-module linearity,
identification of the cokernel and projectivity are separate obligations.
-/

noncomputable section
open CategoryTheory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The descended signed QP operation is injective on the actual old-only quotient. -/
theorem signedQPMap_injective (i : I) (v w : List I) :
    Function.Injective (signedQPMap D Sc cutoff i v w) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  simp only [signedQPMap_projection, Category.assoc] at hz
  exact projection_qp_relation_regular D Sc cutoff i v w h hz

/-- The prescribed P map is injective for all words, cutoffs and full exterior coefficients. -/
theorem pMap_injective (i : I) (v w : List I) :
    Function.Injective (pMap D Sc cutoff i v w) := by
  intro x y hxy
  apply signedQPMap_injective D Sc cutoff i v w
  have h := congrArg (qMap D Sc cutoff i v w) hxy
  change ((qMap D Sc cutoff i v w).comp (pMap D Sc cutoff i v w)) x =
    ((qMap D Sc cutoff i v w).comp (pMap D Sc cutoff i v w)) y at h
  simpa only [qMap_comp_pMap] using h

end OddMath.QuiverHecke.ELVOld
