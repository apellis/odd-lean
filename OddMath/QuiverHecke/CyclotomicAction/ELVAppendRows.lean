/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVSourceRows
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendDescent

/-! # Common old rows for the append endpoint

The old-only append quotient is reconstructed from representable old rows.
Naturality includes all word-to-word old arrows. The append action is untwisted,
so its reconstruction uses `appendPair` at parity zero; the signed ELV tensor
composition and the old cyclotomic quotient are unchanged. These rows supply
coordinates for the underlying old-ring module of K₀ in the deformed square.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory Opposite MonoidalCategory
open scoped Classical TensorProduct DirectSum
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- An old target and the input shuffle of its appended strand. -/
abbrev AppendTailIndex (i : I) (ν : List I) :=
  Σ t : ContentWords ν, AppendShuffle (appendLen t.val i)

instance appendTailIndexFintype (i : I) (ν : List I) :
    Fintype (AppendTailIndex i ν) := inferInstance

/-- Finitely supported common tails carrying full old idempotent rows. -/
abbrev AppendRows (i : I) (ν : List I) :=
  ⨁ q : AppendTailIndex i ν × ℕ, OldContentRow D Sc cutoff ν q.1.1.val

/-- Exponent translation preserves the common target and the full old row. -/
def appendRowsShift (i : I) (ν : List I) (d : ℕ) :
    AppendRows D Sc cutoff i ν →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      AppendRows D Sc cutoff i ν :=
  DirectSum.toModule _ _ _ fun q =>
    DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ (AppendTailIndex i ν × ℕ)
      (fun r => OldContentRow D Sc cutoff ν r.1.1.val) (q.1, d + q.2)

end OddMath.QuiverHecke.ELVOld
