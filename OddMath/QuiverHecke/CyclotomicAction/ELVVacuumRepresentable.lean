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

/-- Iterated induction from the empty-content vacuum is represented by the
actual reversed operator word. No comparison with an untruncated corner is assumed. -/
def wordIso : (σ : List I) →
    wordModule D Sc cutoff N σ ≅
      contentRepresentable D Sc cutoff N (content σ) (wordObject D Sc cutoff N σ)
  | [] => Iso.refl _
  | i :: σ => (contentE D Sc cutoff N (content σ) i).mapIso (wordIso σ) ≪≫
      InductionRepresentable.iso D Sc cutoff N (content σ) [i] (wordObject D Sc cutoff N σ)

def appendEndComponent (β : Multiset I) (σ : List I)
    (a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D σ))
    (v : ContentCategory D Sc cutoff N β) :
    (contentAppend D Sc cutoff N β σ).obj v ⟶ (contentAppend D Sc cutoff N β σ).obj v :=
  truncatedAppendComponent D Sc cutoff N a v.obj

/-- Restrict an appended homogeneous endomorphism to its actual exact-content
append functor. The same proof handles dots and equal-colour crossings. -/
theorem appendEnd_supernatural (β : Multiset I) (σ : List I) {p : ZMod 2}
    {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D σ)}
    (ha : a ∈ parity (R := k) _ _ p) :
    IsSupernatural k p (F := contentAppend D Sc cutoff N β σ)
      (G := contentAppend D Sc cutoff N β σ)
      (appendEndComponent D Sc cutoff N β σ a) where
  mem v := (truncatedAppendComponent_supernatural D Sc cutoff N ha).mem v.obj
  naturality := by
    intro v w q f hf
    exact (truncatedAppendComponent_supernatural D Sc cutoff N ha).naturality hf

/-- The concrete contravariant mate of an appended endomorphism on an actual
induced representable, expressed in represented coordinates. -/
theorem appendEnd_coordinates (β : Multiset I) (σ : List I)
    (v : ContentCategory D Sc cutoff N β) {p : ZMod 2}
    {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D σ)}
    (ha : a ∈ parity (R := k) _ _ p)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (h : (contentAppend D Sc cutoff N β σ).obj v ⟶ w) :
    InductionRepresentable.forward D Sc cutoff N β σ v w
      (BalancedInduction.transformLinear (appendEnd_supernatural D Sc cutoff N β σ ha)
        (contentRepresentable D Sc cutoff N β v) w
        (InductionRepresentable.backward D Sc cutoff N β σ v w h)) =
      appendEndComponent D Sc cutoff N β σ a v ≫ twist k p h := by
  rw [InductionRepresentable.backward_apply]
  have ht := BalancedInduction.transformLinear_tensor
    (appendEnd_supernatural D Sc cutoff N β σ ha)
    (contentRepresentable D Sc cutoff N β v) w v h (𝟙 v)
  calc
    _ = InductionRepresentable.forward D Sc cutoff N β σ v w
        (BalancedInduction.tensor (contentAppend D Sc cutoff N β σ)
          (contentRepresentableFunctor D Sc cutoff N β v) v
          (appendEndComponent D Sc cutoff N β σ a v ≫ twist k p h) (𝟙 v)) :=
      congrArg (InductionRepresentable.forward D Sc cutoff N β σ v w) ht
    _ = _ := by rw [InductionRepresentable.forward_tensor, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The sign uses total source Hom parity, including exterior coefficients. -/
theorem appendEnd_coordinates_of_mem (β : Multiset I) (σ : List I)
    (v : ContentCategory D Sc cutoff N β) {p r : ZMod 2}
    {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D σ)}
    (ha : a ∈ parity (R := k) _ _ p)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (h : (contentAppend D Sc cutoff N β σ).obj v ⟶ w)
    (hh : h ∈ parity (R := k) ((contentAppend D Sc cutoff N β σ).obj v) w r) :
    InductionRepresentable.forward D Sc cutoff N β σ v w
      (BalancedInduction.transformLinear (appendEnd_supernatural D Sc cutoff N β σ ha)
        (contentRepresentable D Sc cutoff N β v) w
        (InductionRepresentable.backward D Sc cutoff N β σ v w h)) =
      sign k (p * r) • (appendEndComponent D Sc cutoff N β σ a v ≫ h) := by
  rw [appendEnd_coordinates D Sc cutoff N β σ v ha]
  have ht := twist_of_mem p hh
  rw [ht, Linear.comp_smul]

/-- At the identity, evaluation recovers the actual appended quotient morphism,
not a same-direction Yoneda arrow. -/
theorem appendEnd_identity (β : Multiset I) (σ : List I)
    (v : ContentCategory D Sc cutoff N β) {p : ZMod 2}
    {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D σ)}
    (ha : a ∈ parity (R := k) _ _ p) :
    InductionRepresentable.forward D Sc cutoff N β σ v
      ((contentAppend D Sc cutoff N β σ).obj v)
      (BalancedInduction.transformLinear (appendEnd_supernatural D Sc cutoff N β σ ha)
        (contentRepresentable D Sc cutoff N β v) _
        (InductionRepresentable.backward D Sc cutoff N β σ v _ (𝟙 _))) =
      (truncatedIdeal D Sc cutoff N _ _).mkQ (appendComponent D Sc cutoff a v.obj.word) := by
  rw [appendEnd_coordinates D Sc cutoff N β σ v ha, twist_id, Category.comp_id]
  rfl

/-- Actual dot comparison at any represented prefix (hence at every iterated
vacuum prefix). This is precomposition twisted by the full parity of `h`. -/
theorem dot_coordinates (β : Multiset I) (v : ContentCategory D Sc cutoff N β) (i : I)
    (w : ContentCategory D Sc cutoff N (β + ([i] : List I)))
    (h : (contentAppend D Sc cutoff N β [i]).obj v ⟶ w) :
    InductionRepresentable.forward D Sc cutoff N β [i] v w
      (BalancedInduction.transformLinear
        (appendEnd_supernatural D Sc cutoff N β [i]
          (show dotE D Sc [i] 0 ∈ parity (R := k) _ _ (D.parity i) from by
            simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1))
        (contentRepresentable D Sc cutoff N β v) w
        (InductionRepresentable.backward D Sc cutoff N β [i] v w h)) =
      appendEndComponent D Sc cutoff N β [i] (dotE D Sc [i] 0) v ≫
        twist k (D.parity i) h :=
  appendEnd_coordinates D Sc cutoff N β [i] v
    (by simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1) w h

/-- Raw equal-colour crossing comparison. The separate normalized generator
has an additional minus; it is not silently included in this raw formula. -/
theorem equalCross_coordinates (β : Multiset I)
    (v : ContentCategory D Sc cutoff N β) (i : I)
    (w : ContentCategory D Sc cutoff N (β + ([i, i] : List I)))
    (h : (contentAppend D Sc cutoff N β [i, i]).obj v ⟶ w) :
    InductionRepresentable.forward D Sc cutoff N β [i, i] v w
      (BalancedInduction.transformLinear
        (appendEnd_supernatural D Sc cutoff N β [i, i] (crossTwo_mem D Sc i i))
        (contentRepresentable D Sc cutoff N β v) w
        (InductionRepresentable.backward D Sc cutoff N β [i, i] v w h)) =
      appendEndComponent D Sc cutoff N β [i, i] (crossTwo D Sc i i) v ≫
        twist k (D.parity i * D.parity i) h :=
  appendEnd_coordinates D Sc cutoff N β [i, i] v (crossTwo_mem D Sc i i) w h

end VacuumRepresentable
end OddMath.QuiverHecke.ELVOld
