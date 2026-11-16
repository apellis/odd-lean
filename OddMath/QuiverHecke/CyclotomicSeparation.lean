/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.WeightedSeparation
import OddMath.QuiverHecke.Basis
import Mathlib.Data.Finset.Prod

/-!
# Bounded cyclotomic separation

Supporting the affine-algebra separation step toward Brundan–Ellis §8,
Nondegeneracy Conjecture (research issue #345). These arguments use affine
PBW independence, not independence of its image in SKM.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification.TypeA

theorem permutation_length_le_choose_two (n : ℕ) (w : Equiv.Perm (Fin n)) :
    length n w ≤ n.choose 2 := by
  classical
  rw [length_eq_invCount]
  unfold invCount invSet
  calc
    _ ≤ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card :=
      Finset.card_le_card (by
        intro p hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2.1⟩)
    _ = n.choose 2 := by
      simpa using (Finset.card_product_filter_lt (s := Finset.univ (α := Fin n)))

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- The power of the dot on the first strand; the separation theorem assumes
the strand word is nonempty, so this is never an out-of-range dot. -/
def firstDotPower (t : List I) (N : ℕ) :
    (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t) :=
  cl D Sc t t ((List.replicate N 0).map PG.dot)
    (by simpa only [tgt_map_dot] using sChain_pl t ((List.replicate N 0).map PG.dot))

end OddMath.QuiverHecke
