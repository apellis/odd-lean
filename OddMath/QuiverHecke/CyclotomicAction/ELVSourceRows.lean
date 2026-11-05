/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModule
import OddMath.QuiverHecke.CentreFinite

/-! # Common-source rows for the prepend endpoint

The reconstruction maps below use representable old rows, rather than separate
scalar coordinates at each old source. Their naturality includes arbitrary
word-to-word old arrows and retains the total parity twist in `pair`.
The intended application is the source endpoint of the deformed square resolution.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory Opposite MonoidalCategory
open scoped Classical TensorProduct DirectSum
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The representable old presheaf at an arbitrary target word. -/
def oldRowPresheaf (t : List I) : (OldCategory D Sc cutoff)ᵒᵖ ⥤ ModuleCat k where
  obj v := ModuleCat.of k (Old D Sc cutoff v.unop.word t)
  map f := ModuleCat.ofHom (oldComp D Sc cutoff _ _ t f.unop)
  map_id v := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    exact Category.id_comp (X := (⟨v.unop.word⟩ : OldCategory D Sc cutoff))
      (Y := ⟨t⟩) b
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    exact Category.assoc (Z := (⟨t⟩ : OldCategory D Sc cutoff)) g.unop f.unop b

instance oldRowPresheaf_additive (t : List I) :
    (oldRowPresheaf D Sc cutoff t).Additive where
  map_add := by
    intro a b f g
    apply ModuleCat.hom_ext
    exact (oldComp D Sc cutoff _ _ t).map_add f.unop g.unop

/-- All old columns of a single representable old row. No corner is assumed nonzero. -/
abbrev OldContentRow (ν t : List I) :=
  OddMath.FiniteHomMatrix.RightModule (contentObject D Sc cutoff ν)
    (oldRowPresheaf D Sc cutoff t)

/-- The finite part of the common tail index: an old target and an input shuffle. -/
abbrev SourceTailIndex (ν : List I) := Σ t : ContentWords ν, PrependShuffle t.val.length

instance sourceTailIndexFintype (ν : List I) : Fintype (SourceTailIndex ν) := inferInstance

/-- Finitely supported common tails, each carrying an entire old idempotent row. -/
abbrev SourceRows (ν : List I) :=
  ⨁ q : SourceTailIndex ν × ℕ, OldContentRow D Sc cutoff ν q.1.1.val

/-- Exponent translation on the finite-tail-index times natural-number direct sum. -/
def sourceRowsShift (ν : List I) (d : ℕ) :
    SourceRows D Sc cutoff ν →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      SourceRows D Sc cutoff ν :=
  DirectSum.toModule _ _ _ fun q =>
    DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ (SourceTailIndex ν × ℕ)
      (fun r => OldContentRow D Sc cutoff ν r.1.1.val) (q.1, d + q.2)

end OddMath.QuiverHecke.ELVOld
