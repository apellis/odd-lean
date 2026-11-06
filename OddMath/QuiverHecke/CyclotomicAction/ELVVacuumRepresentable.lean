/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionRepresentable
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform

/-! # Representable vacuum words

The initial vacuum is the actual empty-word representable of the
coefficient-truncated full ELV category. Iterating the constructed one-colour
induction functors represents the appended word, without a local inverse.
Lists of induction operators are written with the outermost operator first;
the represented word is therefore their reversal.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Rank-zero object; its endomorphisms retain the full coefficient truncation. -/
def vacuumObject : ContentCategory D Sc cutoff N 0 := ⟨⟨[]⟩, rfl⟩

/-- The actual rank-zero representable, not a prescribed polynomial quotient. -/
def vacuumModule : ContentModules D Sc cutoff N 0 :=
  contentRepresentable D Sc cutoff N 0 (vacuumObject D Sc cutoff N)

namespace VacuumRepresentable

/-- Exact content after applying operators from right to left. -/
def content : List I → Multiset I
  | [] => 0
  | i :: σ => content σ + ([i] : List I)

/-- The represented object of an iterated induction word. -/
def wordObject : (σ : List I) → ContentCategory D Sc cutoff N (content σ)
  | [] => vacuumObject D Sc cutoff N
  | i :: σ => (contentAppend D Sc cutoff N (content σ) [i]).obj (wordObject σ)

theorem wordObject_word (σ : List I) : (wordObject D Sc cutoff N σ).obj.word = σ.reverse := by
  induction σ with
  | nil => rfl
  | cons i σ ih =>
    change (wordObject D Sc cutoff N σ).obj.word ++ [i] = (i :: σ).reverse
    rw [ih, List.reverse_cons]

/-- Iteration uses the actual balanced one-colour raising functors. -/
def wordModule : (σ : List I) → ContentModules D Sc cutoff N (content σ)
  | [] => vacuumModule D Sc cutoff N
  | i :: σ => (contentE D Sc cutoff N (content σ) i).obj (wordModule σ)

end VacuumRepresentable
end OddMath.QuiverHecke.ELVOld
