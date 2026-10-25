import OddMath.SKM.RightMateMatchings
import OddMath.SKM.BubbleAlgebra

/-!
# Rightmost coefficients and source-prefix adjunction

Native linear maps for the source-prefix part of the right-mate reduction of
Brundan–Ellis, *Super Kac–Moody 2-categories*, §8. The maps retain the actual
rightmost coefficient algebra; there is no bubble specialization.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- Bend an upward source prefix using the even right-cup block. -/
def cupPrefixMap (D : Datum I X) (Sc : Scalars D k) (μ : X)
    (l : List I) (a b : List (Letter I)) :
    ((pres D Sc).obj (ob D μ (ups l ++ a)) ⟶ (pres D Sc).obj (ob D μ b)) →ₗ[k]
    ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ (dns l ++ b))) :=
  ctxL D Sc μ a (dns l ++ b) ((cupN l).map (whL [] a)) (dns l) [] [] (ups l ++ a) b

/-- Straighten a downward target prefix using the even right-cap block. -/
def capPrefixMap (D : Datum I X) (Sc : Scalars D k) (μ : X)
    (l : List I) (a b : List (Letter I)) :
    ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ (dns l ++ b))) →ₗ[k]
    ((pres D Sc).obj (ob D μ (ups l ++ a)) ⟶ (pres D Sc).obj (ob D μ b)) :=
  ctxL D Sc μ (ups l ++ a) b [] (ups l) []
    ((capN l).map (whL [] b)) a (dns l ++ b)

theorem cupPrefixMap_cl (μ : X) (l : List I) (a b : List (Letter I))
    (L : List (LayerData I)) :
    cupPrefixMap D Sc μ l a b (cl D Sc μ (ups l ++ a) b L) =
    cl D Sc μ a (dns l ++ b) (cupPrefixLayers l a L) := by
  have H := ctxL_cl (D := D) (Sc := Sc) μ
    (s₀ := a) (t₀ := dns l ++ b)
    (u := dns l) (v := []) (s := ups l ++ a) (t := b)
    (pre := (cupN l).map (whL [] a)) (post := [])
    ((sChain_cupN l).wh [] a (by simp) (by simp [List.append_assoc]))
    (show SChain (dns l ++ b ++ []) [] (dns l ++ b) by simp [SChain]) L
  simpa only [cupPrefixMap, cupPrefixLayers_eq, List.append_nil, wt_nil] using H

theorem capPrefixMap_cl (μ : X) (l : List I) (a b : List (Letter I))
    (L : List (LayerData I)) :
    capPrefixMap D Sc μ l a b (cl D Sc μ a (dns l ++ b) L) =
    cl D Sc μ (ups l ++ a) b
      (L.map (whL (ups l) []) ++ (capN l).map (whL [] b)) := by
  have H := ctxL_cl (D := D) (Sc := Sc) μ
    (s₀ := ups l ++ a) (t₀ := b)
    (u := ups l) (v := []) (s := a) (t := dns l ++ b)
    (pre := []) (post := (capN l).map (whL [] b))
    (show SChain (ups l ++ a) [] (ups l ++ a ++ []) by simp [SChain])
    ((sChain_capN l).wh [] b (by simp [List.append_assoc]) (by simp)) L
  simpa only [capPrefixMap, List.nil_append, wt_nil] using H

theorem capPrefixMap_cupPrefixMap_cl (μ : X) (l : List I) {a b : List (Letter I)}
    {L : List (LayerData I)} (hL : SChain (ups l ++ a) L b) :
    capPrefixMap D Sc μ l a b (cupPrefixMap D Sc μ l a b (cl D Sc μ (ups l ++ a) b L)) =
    cl D Sc μ (ups l ++ a) b L := by
  rw [cupPrefixMap_cl, capPrefixMap_cl]
  have H := cl_rightClosure_cupPrefix Sc μ l hL
  have H' := congrArg (wordCast (D := D) (Sc := Sc) μ (s' := ups l ++ a) rfl
    (show b ++ ups [] = b by simp [ups])) H
  rw [wordCast_cl, wordCast_cl] at H'
  simpa [rightClosureL, cupN, capN, ups] using H'

theorem capPrefixMap_cupPrefixMap (μ : X) (l : List I) (a b : List (Letter I))
    (f : (pres D Sc).obj (ob D μ (ups l ++ a)) ⟶ (pres D Sc).obj (ob D μ b)) :
    capPrefixMap D Sc μ l a b (cupPrefixMap D Sc μ l a b f) = f := by
  induction mem_span_cl μ f using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl⟩ := hf
    exact capPrefixMap_cupPrefixMap_cl μ l hL
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smul, hx]

theorem cupPrefixMap_injective (μ : X) (l : List I) (a b : List (Letter I)) :
    Function.Injective (cupPrefixMap D Sc μ l a b) := by
  intro f g h
  have H := congrArg (capPrefixMap D Sc μ l a b) h
  simpa only [capPrefixMap_cupPrefixMap] using H

private theorem cupPrefixMap_bubAt_cl (μ : X) (l : List I) {a b : List (Letter I)}
    {M L : List (LayerData I)} (hM : SChain [] M []) (hL : SChain (ups l ++ a) L b) :
    cupPrefixMap D Sc μ l a b
      (bubAt D Sc μ (ups l ++ a) (cl D Sc μ [] [] M) ≫ cl D Sc μ (ups l ++ a) b L) =
    bubAt D Sc μ a (cl D Sc μ [] [] M) ≫
      cupPrefixMap D Sc μ l a b (cl D Sc μ (ups l ++ a) b L) := by
  rw [bubAt_cl, bubAt_cl,
    cl_comp (hM.wh (ups l ++ a) [] (by simp) (by simp)) hL,
    cupPrefixMap_cl, cupPrefixMap_cl,
    cl_comp (hM.wh a [] (by simp) (by simp)) (sChain_cupPrefixLayers l hL)]
  have E := cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := a) (T := dns l ++ b)
    [] (L.map (whL (dns l) [])) [] a [] (sChain_cupN l) hM
    (Or.inl (parsum_cupN l))
  simpa [cupPrefixLayers_eq, List.append_assoc] using E

/-- Source-prefix bending commutes with every rightmost closed coefficient,
including arbitrary inhomogeneous products of odd bubbles. -/
theorem cupPrefixMap_bubAt (μ : X) (l : List I) (a b : List (Letter I))
    (β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ []))
    (f : (pres D Sc).obj (ob D μ (ups l ++ a)) ⟶ (pres D Sc).obj (ob D μ b)) :
    cupPrefixMap D Sc μ l a b (bubAt D Sc μ (ups l ++ a) β ≫ f) =
    bubAt D Sc μ a β ≫ cupPrefixMap D Sc μ l a b f := by
  induction mem_span_cl μ β using Submodule.span_induction with
  | mem β hβ =>
    obtain ⟨M, hM, rfl⟩ := hβ
    induction mem_span_cl μ f using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨L, hL, rfl⟩ := hf
      exact cupPrefixMap_bubAt_cl μ l hM hL
    | zero => simp only [Limits.comp_zero, map_zero]
    | add x y _ _ hx hy => simp only [Preadditive.comp_add, map_add, hx, hy]
    | smul r x _ hx => simp only [Linear.comp_smul, map_smul, hx]
  | zero => simp only [map_zero, Limits.zero_comp]
  | add x y _ _ hx hy => simp only [map_add, Preadditive.add_comp, hx, hy]
  | smul r x _ hx => simp only [map_smul, Linear.smul_comp, hx]

end OddMath.SKM
