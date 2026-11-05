/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVPrependOldExtraction

/-!
# Cross-tail ELV extraction

The off-tail step of `ELVPrependCoordinates.md`, needed for the old-only
coordinate comparison in `DeformedGlobalQP.md` §1. The existing `PrependIdx`
is regrouped by moving exponent and shuffle, with both index inverse laws.
`prependExtractOld_insert_off_tail` proves vanishing on every different tail,
for arbitrary full-ELV old coefficients and total parity. No finite-colour
hypothesis, flatness, or independence assumption is added.

The index equivalence is not yet an old-quotient coordinate equivalence.
Vanishing on all old-only relation generators, simultaneous quotient inversion,
and the moving-square shift and cancellation remain open.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

namespace PrependIdx
variable {i : I} {v w : List I}
/-- The moving exponent and inverse-shuffle index, without the old normal form. -/
def tailKey (x : PrependIdx i v w) : ℕ × PrependShuffle v.length :=
  (x.1.1, x.1.2.2.2)

@[simp] theorem tailKey_replaceOld (x : PrependIdx i v w) (y : NFIdx v x.oldTarget) :
    (x.replaceOld y).tailKey = x.tailKey := rfl

/-- Different moving tails have disjoint sets of old normal-form replacements. -/
theorem replaceOld_ne_of_tailKey_ne (x z : PrependIdx i v w)
    (h : x.tailKey ≠ z.tailKey) (y : NFIdx v x.oldTarget) (b : NFIdx v z.oldTarget) :
    x.replaceOld y ≠ z.replaceOld b := by
  intro he
  exact h (show (x.replaceOld y).tailKey = (z.replaceOld b).tailKey from congrArg tailKey he)

/-- The target word and shuffle recover the intermediate old target uniquely. -/
theorem oldTarget_eq_of_tailKey_eq (x z : PrependIdx i v w)
    (h : x.tailKey = z.tailKey) : x.oldTarget = z.oldTarget := by
  have hd : x.1.2.2.2 = z.1.2.2.2 :=
    congrArg (fun a : ℕ × PrependShuffle v.length => a.2) h
  have he := x.moving_target.trans z.moving_target.symm
  rw [hd] at he
  have hs : (i :: x.oldTarget).length = v.length + 1 := by
    simp [oldTarget]
  have ht : (i :: z.oldTarget).length = v.length + 1 := by
    simp [oldTarget]
  have hh : i :: x.oldTarget = i :: z.oldTarget := by
    refine List.ext_getElem (hs.trans ht.symm) fun a ha hb => ?_
    let q : Fin (v.length + 1) :=
      Categorification.TypeA.wordProd (v.length + 1)
        (Categorification.TypeA.canWord (v.length + 1) z.1.2.2.2.1⁻¹)
        ⟨a, by omega⟩
    have hc := List.getElem_of_eq he (i := q.val) (by simpa only [length_tgt, hs] using q.isLt)
    rw [tgt_cw_getElem (Categorification.TypeA.validWord_canWord _ _) hs q,
      tgt_cw_getElem (Categorification.TypeA.validWord_canWord _ _) ht q] at hc
    simpa [q] using hc
  exact List.cons.inj hh |>.2

/-- A representative for the same tail is obtained by replacing only its old index. -/
theorem eq_replaceOld_of_tailKey_eq (x z : PrependIdx i v w)
    (h : x.tailKey = z.tailKey) :
    z = x.replaceOld ((x.oldTarget_eq_of_tailKey_eq z h).symm ▸ z.old) := by
  apply Subtype.ext
  have hn := congrArg Prod.fst h
  have hd := congrArg Prod.snd h
  have hv {t t' : List I} (e : t = t') (b : NFIdx v t) :
      (e ▸ b : NFIdx v t').val = b.val := by cases e; rfl
  simp only [replaceOld, hv]
  exact Prod.ext hn.symm (Prod.ext rfl (Prod.ext rfl hd.symm))

/-- Moving tails that occur in the existing prepend basis, forgetting the old index. -/
def Tail (i : I) (v w : List I) : Type :=
  ↥(Set.range (tailKey (i := i) (v := v) (w := w)))

namespace Tail
/-- Choose an existing prepend index over a tail; no new basis is chosen. -/
def representative (q : Tail i v w) : PrependIdx i v w := q.property.choose

@[simp] theorem representative_tailKey (q : Tail i v w) :
    q.representative.tailKey = q.val := q.property.choose_spec
end Tail

/-- Regroup existing prepend indices by their moving tail and old normal form. -/
def regroupEquiv : PrependIdx i v w ≃
    Σ q : Tail i v w, NFIdx v q.representative.oldTarget where
  toFun x := ⟨⟨x.tailKey, ⟨x, rfl⟩⟩,
    (oldTarget_eq_of_tailKey_eq
      (Tail.representative ⟨x.tailKey, ⟨x, rfl⟩⟩) x
      (Tail.representative_tailKey ⟨x.tailKey, ⟨x, rfl⟩⟩)).symm ▸ x.old⟩
  invFun x := x.1.representative.replaceOld x.2
  left_inv x := (eq_replaceOld_of_tailKey_eq _ x (Tail.representative_tailKey _)).symm
  right_inv q := by
    rcases q with ⟨q, y⟩
    apply Sigma.ext
    · apply Subtype.ext
      exact q.representative_tailKey
    · have ht (x : PrependIdx i v w) (y : NFIdx v x.oldTarget) :
          HEq ((x.replaceOld y).old) y := by
        apply (Subtype.heq_iff_coe_eq (by
          intro b
          rw [x.replaceOld_target y])).mpr
        rfl
      exact (eqRec_heq _ _).trans (ht _ _)
end PrependIdx
namespace ELVOld

/-- Off-tail restriction vanishes before either parity normalization. -/
theorem prependTailCoefficients_comap_off_tail {i : I} {v w : List I}
    (x z : PrependIdx i v w) (h : x.tailKey ≠ z.tailKey)
    (f : NFIdx v z.oldTarget →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    Finsupp.lcomapDomain (R := k) x.replaceOld x.replaceOld_injective
      (prependTailCoefficients D cutoff z f) = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | single y a =>
    simp only [prependTailCoefficients, Finsupp.lsum_single, LinearMap.comp_apply,
      Finsupp.lsingle_apply]
    ext b
    simp only [Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply, Finsupp.zero_apply]
    exact Finsupp.single_eq_of_ne (x.replaceOld_ne_of_tailKey_ne z h b y)

/-- Every old coefficient on a different moving tail extracts to zero. -/
theorem prependExtractOld_insert_off_tail (p : ZMod 2) {i : I} {v w : List I}
    (x z : PrependIdx i v w) (h : x.tailKey ≠ z.tailKey)
    (r : hom D Sc cutoff v z.oldTarget) :
    prependExtractOld D Sc cutoff p x
      (insert D Sc cutoff i v z.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc z : hom D Sc cutoff (i :: z.oldTarget) w)) = 0 := by
  unfold prependExtractOld
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [prependAffineEquiv_insert_tail, prependTailCoefficients_comap_off_tail D cutoff x z h]
  simp only [map_zero]

/-- Off-tail extraction also vanishes in the old cyclotomic quotient. -/
theorem prependExtractOldQuotient_insert_off_tail (p : ZMod 2) {i : I} {v w : List I}
    (x z : PrependIdx i v w) (h : x.tailKey ≠ z.tailKey)
    (r : hom D Sc cutoff v z.oldTarget) :
    prependExtractOldQuotient D Sc cutoff p x
      (insert D Sc cutoff i v z.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc z : hom D Sc cutoff (i :: z.oldTarget) w)) = 0 := by
  change (ideal D Sc cutoff v x.oldTarget).mkQ
    (prependExtractOld D Sc cutoff p x _) = 0
  rw [prependExtractOld_insert_off_tail D Sc cutoff p x z h, map_zero]
end ELVOld
end OddMath.QuiverHecke
