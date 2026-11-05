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

/-- Untwisted old precomposition acts on the whole old coefficient row. -/
theorem appendPull_pair (i : I) {u v t w : List I}
    (c : Old D Sc cutoff u v) (h : hom D Sc cutoff (t ++ [i]) w)
    (b : Old D Sc cutoff v t) :
    appendPull D Sc cutoff i u v w c (appendPair D Sc cutoff 0 i h b) =
      appendPair D Sc cutoff 0 i h (oldComp D Sc cutoff u v t c b) := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff u v).mkQ_surjective c
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  simp only [appendPair_mk, appendPull_mk, oldComp_mk, twist_zero,
    rightContext_comp, Category.assoc]

/-- A positioned append tail gives a map of representable old presheaves. -/
def appendPairNat (i : I) {t w : List I}
    (h : hom D Sc cutoff (t ++ [i]) w) :
    oldRowPresheaf D Sc cutoff t ⟶ appendPresheaf D Sc cutoff i w where
  app v := ModuleCat.ofHom (appendPair D Sc cutoff 0 i h)
  naturality a b f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (appendPull_pair D Sc cutoff i f.unop h z).symm

/-- Reconstruction is linear over the full opposite old content ring. -/
def appendPairRow (i : I) (ν : List I) {t w : List I}
    (h : hom D Sc cutoff (t ++ [i]) w) :
    OldContentRow D Sc cutoff ν t →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      AppendRow D Sc cutoff i ν w :=
  OddMath.FiniteHomMatrix.RightModule.map (contentObject D Sc cutoff ν)
    (appendPairNat D Sc cutoff i h)

@[simp] theorem appendPairRow_apply (i : I) (ν : List I)
    {t w : List I} (h : hom D Sc cutoff (t ++ [i]) w)
    (b : OldContentRow D Sc cutoff ν t) (v : ContentWords ν) :
    appendPairRow D Sc cutoff i ν h b v = appendPair D Sc cutoff 0 i h (b v) := rfl

/-- An old target and the input shuffle of its appended strand. -/
abbrev AppendTailIndex (i : I) (ν : List I) :=
  Σ t : ContentWords ν, AppendShuffle (appendLen t.val i)

instance appendTailIndexFintype (i : I) (ν : List I) :
    Fintype (AppendTailIndex i ν) := inferInstance

/-- The ambient target depends on the common old target and shuffle only. -/
def appendTailWord (i : I) {ν : List I} (q : AppendTailIndex i ν) :
    ContentWords (i :: ν) :=
  ⟨tgt (q.1.val ++ [i])
      (cw (Categorification.TypeA.canWord (q.1.val ++ [i]).length q.2.val⁻¹)),
    (tgt_perm _ _).trans
      ((List.perm_append_comm).trans (q.1.property.cons i))⟩

private theorem append_rows_canWord_one (n : ℕ) :
    Categorification.TypeA.canWord n 1 = [] := by
  apply List.length_eq_zero_iff.mp
  rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]

/-- The common tail with identity old normal form. -/
def appendTailPBW (i : I) {ν : List I} (q : AppendTailIndex i ν) (m : ℕ) :
    AppendIdx i q.1.val (appendTailWord i q).val :=
  ⟨(m, [], 1, q.2), by simp, by simp, by
    simp [appendCrossingWord, append_rows_canWord_one, cw, appendTailWord]⟩

@[simp] theorem appendTailPBW_oldTarget (i : I) {ν : List I}
    (q : AppendTailIndex i ν) (m : ℕ) : (appendTailPBW i q m).oldTarget = q.1.val := by
  simp [appendTailPBW, AppendIdx.oldTarget, append_rows_canWord_one, cw]

/-- The tail with its coefficient source replaced by the common old target. -/
def appendCommonTail (i : I) {ν : List I} (q : AppendTailIndex i ν) (m : ℕ) :
    hom D Sc cutoff (q.1.val ++ [i]) (appendTailWord i q).val :=
  appendTailPBW_oldTarget i q m ▸
    ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
      appendTail D Sc (appendTailPBW i q m))

/-- Embed a whole representable old row along its common append tail. -/
def appendTailRow (i : I) (ν : List I) (q : AppendTailIndex i ν) (m : ℕ) :
    OldContentRow D Sc cutoff ν q.1.val →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      AppendContent D Sc cutoff i ν :=
  (LinearMap.single (R := (ContentRing D Sc cutoff ν)ᵐᵒᵖ)
    (φ := fun w : ContentWords (i :: ν) => AppendRow D Sc cutoff i ν w.val)
    (appendTailWord i q)).comp
      (appendPairRow D Sc cutoff i ν (appendCommonTail D Sc cutoff i q m))

/-- Finitely supported common tails carrying full old idempotent rows. -/
abbrev AppendRows (i : I) (ν : List I) :=
  ⨁ q : AppendTailIndex i ν × ℕ, OldContentRow D Sc cutoff ν q.1.1.val

/-- Common-row reconstruction of the old-ring module underlying K₀. -/
def appendRowsReconstruct (i : I) (ν : List I) :
    AppendRows D Sc cutoff i ν →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      AppendContent D Sc cutoff i ν :=
  DirectSum.toModule _ _ _ fun q => appendTailRow D Sc cutoff i ν q.1 q.2

@[simp] theorem appendRowsReconstruct_lof (i : I) (ν : List I)
    (q : AppendTailIndex i ν × ℕ) (b : OldContentRow D Sc cutoff ν q.1.1.val) :
    appendRowsReconstruct D Sc cutoff i ν
      (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b) =
      appendTailRow D Sc cutoff i ν q.1 q.2 b :=
  DirectSum.toModule_lof _ _ _

/-- Exponent translation preserves the common target and the full old row. -/
def appendRowsShift (i : I) (ν : List I) (d : ℕ) :
    AppendRows D Sc cutoff i ν →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      AppendRows D Sc cutoff i ν :=
  DirectSum.toModule _ _ _ fun q =>
    DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ (AppendTailIndex i ν × ℕ)
      (fun r => OldContentRow D Sc cutoff ν r.1.1.val) (q.1, d + q.2)

end OddMath.QuiverHecke.ELVOld
