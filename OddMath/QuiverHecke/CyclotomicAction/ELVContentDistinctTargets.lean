/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockDistinctInverse

/-! # Distinct mates with prescribed successor contents

Brundan–Ellis (1.12) on original weight blocks uses their stored lower
and upper successor contents. This transports the proved canonical
content inverse to arbitrary certificates of the same four sums, while
retaining the literal append functors and the positive crossing.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (β : Multiset I) (i j : I) (δj δi γ : Multiset I)
  (hj : β + ([j] : Multiset I) = δj) (hi : β + ([i] : Multiset I) = δi)
  (hL : δj + ([i] : Multiset I) = γ) (hU : δi + ([j] : Multiset I) = γ)
local notation "J" => contentAppendTo D Sc cutoff bound β [j] δj hj
local notation "K" => contentAppendTo D Sc cutoff bound β [i] δi hi
local notation "L" => contentAppendTo D Sc cutoff bound δj [i] γ hL
local notation "U" => contentAppendTo D Sc cutoff bound δi [j] γ hU

/-- The literal positive crossing with all four prescribed content certificates retained. -/
def contentDistinctTargetsCross (s : ContentCategory D Sc cutoff bound β) :
    (J ⋙ L).obj s ⟶ (K ⋙ U).obj s :=
  truncatedDistinctCrossComponent D Sc cutoff bound i j s.obj

theorem contentDistinctTargetsCross_supernatural :
    IsSupernatural k (D.parity i * D.parity j)
      (contentDistinctTargetsCross D Sc cutoff bound β i j δj δi γ hj hi hL hU) where
  mem s := (truncatedDistinctCross_supernatural D Sc cutoff bound i j).mem s.obj
  naturality := by
    intro s t p f hf
    exact (truncatedDistinctCross_supernatural D Sc cutoff bound i j).naturality hf

local notation "hα" => contentDistinctTargetsCross_supernatural D Sc cutoff bound β i j δj δi γ hj hi hL hU

/-- The actual positive module mate remains invertible for every choice of successor certificates. -/
theorem contentDistinctTargetsMate_isIso (hij : i ≠ j) (M : ContentModules D Sc cutoff bound δj) :
    IsIso (BalancedInduction.orderedRectangularMateComponent J K L U hα M) := by
  subst δj
  subst δi
  subst γ
  exact contentBlockDistinctMate_isIso D Sc cutoff bound β i j hij M

end OddMath.QuiverHecke.ELVOld
