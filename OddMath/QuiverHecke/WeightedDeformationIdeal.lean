/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.WeightedCoefficientSeparation
import OddMath.SKM.BubbleCoefficientGenerators

/-! # Actual ideal closure and coefficient relations for weighted separation -/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical TensorProduct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

theorem coefficient_cl_nil (t : List I) : cl D Sc t t [] (sChain_pl t []) = 𝟙 _ := by
  rw [cl, ← Presentation.diag_id]
  exact Presentation.diag_eq_of_layers_eq _ (by simp [pl, layList])

end OddMath.QuiverHecke
