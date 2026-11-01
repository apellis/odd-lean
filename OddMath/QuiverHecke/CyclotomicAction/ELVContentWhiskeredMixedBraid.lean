/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleCrossingNormalization
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleDots

/-! # The mixed braid on independently whiskered induction crossings

Brundan–Ellis, Definition 1.5, mixed braid relation: compose the existing
single-pair crossings with their literal induction whiskerings. The comparison
with the source-positioned triple maps is used only in the proof. The correction
is formed from the three independently induced single-letter dots.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- The independent prefix pair crossing, induced by the final letter and
recast at its prescribed common intermediate content. Its type is the SVec
Hom between the evaluated triple functors, keeping their inherited carrier
instances identical to those of the independent natural transformations. -/
def contentWhiskeredPrefixCross (β : Multiset I) (i j l : I) (δ γ : Multiset I)
    (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
    (hδ' : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δ)
    (h : β + ([i,j,l] : Multiset I) = γ) (ht : β + ([j,i,l] : Multiset I) = γ)
    (hγ : δ + ([l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ((contentETripleTo D Sc cutoff N β j i l γ ht).obj M).obj z ⟶
      ((contentETripleTo D Sc cutoff N β i j l γ h).obj M).obj z :=
  ((contentETripleMiddleIso D Sc cutoff N β i j l δ γ hδ h hγ).inv.app M).total z ∘ₗ
    ((contentInductionTo D Sc cutoff N δ [l] γ hγ).map
      ((contentEPairCrossTransform D Sc cutoff N β i j δ
        ((contentPair_sum β i j).trans hδ) ((contentPair_sum β j i).trans hδ')).app
        (D.parity i * D.parity j) M)).total z ∘ₗ
    ((contentETripleMiddleIso D Sc cutoff N β j i l δ γ hδ' ht hγ).hom.app M).total z



/-- Expose the literal independent map once, before applying a relation theorem.
This separates carrier conversion from the large dependent comparison. -/
theorem contentWhiskeredPrefixCross_eq (β : Multiset I) (i j l : I) (δ γ : Multiset I)
    (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
    (hδ' : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δ)
    (h : β + ([i,j,l] : Multiset I) = γ) (ht : β + ([j,i,l] : Multiset I) = γ)
    (hγ : δ + ([l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentWhiskeredPrefixCross D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ M z =
      ((contentETripleMiddleIso D Sc cutoff N β i j l δ γ hδ h hγ).inv.app M).total z ∘ₗ
        ((contentInductionTo D Sc cutoff N δ [l] γ hγ).map
          ((contentEPairCrossTransform D Sc cutoff N β i j δ
            ((contentPair_sum β i j).trans hδ) ((contentPair_sum β j i).trans hδ')).app
            (D.parity i * D.parity j) M)).total z ∘ₗ
        ((contentETripleMiddleIso D Sc cutoff N β j i l δ γ hδ' ht hγ).hom.app M).total z := rfl

/-- Compare the typed prefix wrapper without unfolding its carrier transports
inside a larger linear-map expression. -/
theorem contentWhiskeredPrefixCross_map_of_ne (β : Multiset I) {i j : I} (hij : i ≠ j)
    (l : I) (δ γ : Multiset I)
    (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
    (hδ' : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δ)
    (h : β + ([i,j,l] : Multiset I) = γ) (ht : β + ([j,i,l] : Multiset I) = γ)
    (hγ : δ + ([l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentWhiskeredPrefixCross D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ M z =
      contentETripleMap D Sc cutoff N h ht (contentTripleLeft_parity D Sc i j l) M z :=
  (contentWhiskeredPrefixCross_eq D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ M z).trans
    (contentWhiskeredPrefixCross_distinct D Sc cutoff N β hij l δ γ hδ hδ' h ht hγ M z)

theorem contentWhiskeredPrefixCross_map_equal (β : Multiset I) (i l : I)
    (δ γ : Multiset I)
    (hδ : (β + ([i] : Multiset I)) + ([i] : Multiset I) = δ)
    (h : β + ([i,i,l] : Multiset I) = γ) (hγ : δ + ([l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentWhiskeredPrefixCross D Sc cutoff N β i i l δ γ hδ hδ h h hγ M z =
      -contentETripleMap D Sc cutoff N h h (contentTripleLeft_parity D Sc i i l) M z :=
  (contentWhiskeredPrefixCross_eq D Sc cutoff N β i i l δ γ hδ hδ h h hγ M z).trans
    (contentWhiskeredPrefixCross_equal D Sc cutoff N β i l δ γ hδ h hγ M z)

private theorem middle_swap (β : Multiset I) (i j : I) :
    (β + ([j] : Multiset I)) + ([i] : Multiset I) =
      (β + ([i] : Multiset I)) + ([j] : Multiset I) := by ac_rfl

/-- The path through the word i,i,j uses only existing pair crossings and
induction maps; its equal-colour crossing retains its minus normalization. -/
def contentWhiskeredPathIij (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (ContentETripleSpace D Sc cutoff N β i j i _ rfl M z) :=
  let h := content_triple_iij β i j
  let A := contentWhiskeredSuffixCross D Sc cutoff N β i j i _ rfl h M z
  let B := contentWhiskeredPrefixCross D Sc cutoff N β i i j
    ((β + ([i] : Multiset I)) + ([i] : Multiset I)) _ rfl rfl h h
    (by rw [add_assoc, add_assoc]; exact h) M z
  let C := contentWhiskeredSuffixCross D Sc cutoff N β i i j _ h rfl M z
  A.comp (B.comp C)

/-- The other path uses the independently induced prefix and suffix crossings. -/
def contentWhiskeredPathJii (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (ContentETripleSpace D Sc cutoff N β i j i _ rfl M z) :=
  let h := content_triple_jii β i j
  let δ := (β + ([i] : Multiset I)) + ([j] : Multiset I)
  let hγ : δ + ([i] : Multiset I) = β + ([i,j,i] : Multiset I) := by
    rw [add_assoc, add_assoc]; rfl
  let A := contentWhiskeredPrefixCross D Sc cutoff N β i j i δ _
    rfl (middle_swap β i j) rfl h hγ M z
  let B := contentWhiskeredSuffixCross D Sc cutoff N β j i i _ h h M z
  let C := contentWhiskeredPrefixCross D Sc cutoff N β j i i δ _
    (middle_swap β i j) rfl h rfl hγ M z
  A.comp (B.comp C)

theorem contentWhiskeredPathIij_eq (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    contentWhiskeredPathIij D Sc cutoff N β i j M z =
      contentETriplePathIij D Sc cutoff N β i j M z := by
  dsimp only [contentWhiskeredPathIij]
  rw [contentWhiskeredSuffixCross_distinct D Sc cutoff N β i hij.symm,
    contentWhiskeredPrefixCross_map_equal,
    contentWhiskeredSuffixCross_distinct D Sc cutoff N β i hij]
  rfl

theorem contentWhiskeredPathJii_eq (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    contentWhiskeredPathJii D Sc cutoff N β i j M z =
      contentETriplePathJii D Sc cutoff N β i j M z := by
  dsimp only [contentWhiskeredPathJii]
  rw [contentWhiskeredPrefixCross_map_of_ne D Sc cutoff N β hij,
    contentWhiskeredSuffixCross_equal,
    contentWhiskeredPrefixCross_map_of_ne D Sc cutoff N β hij.symm]
  rfl

/-- Full original-Sc mixed correction on the independently whiskered crossings
and single-letter dots, over the actual parameter-twisted content categories. -/
theorem contentWhiskered_mixedBraid (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (z : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I))) :
    contentWhiskeredPathIij D (parameterTwist D Sc) cutoff N β i j M z -
        contentWhiskeredPathJii D (parameterTwist D Sc) cutoff N β i j M z =
      contentWhiskeredPolynomial D Sc cutoff N β i j M z := by
  rw [contentWhiskeredPathIij_eq D _ cutoff N β hij,
    contentWhiskeredPathJii_eq D _ cutoff N β hij,
    ← contentETripleMixedBraid, contentETriple_mixedBraid D Sc cutoff N β hij,
    contentETriplePolynomial_whiskered]
end OddMath.QuiverHecke.ELVOld
