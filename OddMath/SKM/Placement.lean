/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.GrassmannianOdd

/-!
# Placement of homogeneous 2-morphisms and the super interchange law

Tools for manipulating 2-morphisms of `𝔘(𝔤)` that are linear combinations of normal-form
diagrams (such as `η'`, `ε'` and the dotted bubbles) when they are placed next to other strands:

* `homPar μ s t p`: the span of the normal-form diagrams from `E_s 1_μ` to `E_t 1_μ` of parity `p`;
  `cl_mem_homPar`, `comp_mem_homPar`; `closedPar = homPar μ [] [] p` (`closedPar_eq`);
  `etaP_mem`, `epsP_mem`;
* `plcL_comp_of_mem`: placement is compatible with composition;
* `plcL_left_interchange`, `plcL_right_interchange`: the super interchange law (1.3) between a
  homogeneous 2-morphism placed on the left (resp. right) and a diagram on the other strands.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation Finset

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

variable (D Sc) in
/-- The span of the normal-form diagrams `E_s 1_μ ⟶ E_t 1_μ` whose generators have parities
summing to `p`. -/
def homPar (μ : X) (s t : List (Letter I)) (p : ZMod 2) :
    Submodule k ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :=
  Submodule.span k {f | ∃ L, SChain s L t ∧ parsum D L = p ∧ f = cl D Sc μ s t L}

theorem cl_mem_homPar {μ : X} {s t : List (Letter I)} {L : List (LayerData I)}
    (hL : SChain s L t) {p : ZMod 2} (hp : parsum D L = p) :
    cl D Sc μ s t L ∈ homPar D Sc μ s t p :=
  Submodule.subset_span ⟨L, hL, hp, rfl⟩

theorem closedPar_eq (μ : X) (p : ZMod 2) : closedPar D Sc μ p = homPar D Sc μ [] [] p := rfl

/-- Bilinear induction over two `homPar` spans. -/
theorem homPar_induction₂ {μ μ' : X} {s t s' t' : List (Letter I)} {p q : ZMod 2}
    {P : ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) →
      ((pres D Sc).obj (ob D μ' s') ⟶ (pres D Sc).obj (ob D μ' t')) → Prop}
    (hmem : ∀ L M, SChain s L t → parsum D L = p → SChain s' M t' → parsum D M = q →
      P (cl D Sc μ s t L) (cl D Sc μ' s' t' M))
    (hzero₁ : ∀ g, P 0 g) (hzero₂ : ∀ f, P f 0)
    (hadd₁ : ∀ f₁ f₂ g, P f₁ g → P f₂ g → P (f₁ + f₂) g)
    (hadd₂ : ∀ f g₁ g₂, P f g₁ → P f g₂ → P f (g₁ + g₂))
    (hsmul₁ : ∀ (a : k) f g, P f g → P (a • f) g) (hsmul₂ : ∀ (a : k) f g, P f g → P f (a • g))
    {f g} (hf : f ∈ homPar D Sc μ s t p) (hg : g ∈ homPar D Sc μ' s' t' q) : P f g := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, hp, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨M, hM, hq, rfl⟩ := hg
      exact hmem L M hL hp hM hq
    | zero => exact hzero₂ _
    | add x y _ _ hx hy => exact hadd₂ _ _ _ hx hy
    | smul a x _ hx => exact hsmul₂ _ _ _ hx
  | zero => exact hzero₁ _
  | add x y _ _ hx hy => exact hadd₁ _ _ _ hx hy
  | smul a x _ hx => exact hsmul₁ _ _ _ hx

theorem comp_mem_homPar {μ : X} {s t r : List (Letter I)} {p q : ZMod 2}
    {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    {g : (pres D Sc).obj (ob D μ t) ⟶ (pres D Sc).obj (ob D μ r)}
    (hf : f ∈ homPar D Sc μ s t p) (hg : g ∈ homPar D Sc μ t r q) :
    f ≫ g ∈ homPar D Sc μ s r (p + q) := by
  refine homPar_induction₂ (P := fun f g => f ≫ g ∈ homPar D Sc μ s r (p + q))
    (fun L M hL hp hM hq => ?_) (fun g => by simp) (fun f => by simp)
    (fun f₁ f₂ g h₁ h₂ => by rw [Preadditive.add_comp]; exact Submodule.add_mem _ h₁ h₂)
    (fun f g₁ g₂ h₁ h₂ => by rw [Preadditive.comp_add]; exact Submodule.add_mem _ h₁ h₂)
    (fun a f g h => by rw [Linear.smul_comp]; exact Submodule.smul_mem _ _ h)
    (fun a f g h => by rw [Linear.comp_smul]; exact Submodule.smul_mem _ _ h) hf hg
  rw [cl_comp hL hM]
  exact cl_mem_homPar (hL.append hM) (by rw [parsum_append, hp, hq])

/-! ## Composition of placements -/

theorem plcL_cl_comp (μ : X) (u v : List (Letter I)) {s t r : List (Letter I)}
    (L M : List (LayerData I)) (hL : SChain s L t) (hM : SChain t M r) :
    plcL D Sc μ u v s r (cl D Sc (wt D μ v) s t L ≫ cl D Sc (wt D μ v) t r M) =
      plcL D Sc μ u v s t (cl D Sc (wt D μ v) s t L) ≫
        plcL D Sc μ u v t r (cl D Sc (wt D μ v) t r M) := by
  rw [cl_comp hL hM, plcL_cl, plcL_cl, plcL_cl, cl_comp (hL.whisk u v) (hM.whisk u v),
    List.map_append]

/-- Placement is compatible with composition (for homogeneous linear combinations of normal-form
diagrams). -/
theorem plcL_comp_of_mem (μ : X) (u v : List (Letter I)) {s t r : List (Letter I)} {p q : ZMod 2}
    {f : (pres D Sc).obj (ob D (wt D μ v) s) ⟶ (pres D Sc).obj (ob D (wt D μ v) t)}
    {g : (pres D Sc).obj (ob D (wt D μ v) t) ⟶ (pres D Sc).obj (ob D (wt D μ v) r)}
    (hf : f ∈ homPar D Sc (wt D μ v) s t p) (hg : g ∈ homPar D Sc (wt D μ v) t r q) :
    plcL D Sc μ u v s r (f ≫ g) = plcL D Sc μ u v s t f ≫ plcL D Sc μ u v t r g := by
  refine homPar_induction₂ (P := fun f g =>
    plcL D Sc μ u v s r (f ≫ g) = plcL D Sc μ u v s t f ≫ plcL D Sc μ u v t r g)
    (fun L M hL _ hM _ => plcL_cl_comp μ u v L M hL hM) (fun g => by simp) (fun f => by simp)
    (fun f₁ f₂ g h₁ h₂ => by
      rw [Preadditive.add_comp, map_add, map_add, h₁, h₂, Preadditive.add_comp])
    (fun f g₁ g₂ h₁ h₂ => by
      rw [Preadditive.comp_add, map_add, map_add, h₁, h₂, Preadditive.comp_add])
    (fun a f g h => by rw [Linear.smul_comp, map_smul, map_smul, h, Linear.smul_comp])
    (fun a f g h => by rw [Linear.comp_smul, map_smul, map_smul, h, Linear.comp_smul]) hf hg

/-! ## The super interchange law for placed 2-morphisms -/

/-- A homogeneous 2-morphism `f` of parity `p` placed on the left and an endomorphism diagram `B`
of the strands `w` on its right can be exchanged with the sign `(-1)^{p|B|}`. -/
theorem plcL_left_interchange (μ : X) (w : List (Letter I)) {s t : List (Letter I)} {p : ZMod 2}
    {f : (pres D Sc).obj (ob D (wt D μ w) s) ⟶ (pres D Sc).obj (ob D (wt D μ w) t)}
    (hf : f ∈ homPar D Sc (wt D μ w) s t p) {B : List (LayerData I)} (hB : SChain w B w) :
    plcL D Sc μ [] w s t f ≫ cl D Sc μ (t ++ w) (t ++ w) (B.map (whL t [])) =
      zsign k (p * parsum D B) •
        (cl D Sc μ (s ++ w) (s ++ w) (B.map (whL s [])) ≫ plcL D Sc μ [] w s t f) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl, rfl⟩ := hf
    have h1 : plcL D Sc μ [] w s t (cl D Sc (wt D μ w) s t L) =
        cl D Sc μ (s ++ w) (t ++ w) (L.map (whL [] w)) := plcL_cl D Sc μ [] w s t L
    have hLw : SChain (s ++ w) (L.map (whL [] w)) (t ++ w) := by simpa using hL.whisk [] w
    have hBt : SChain (t ++ w) (B.map (whL t [])) (t ++ w) := by simpa using hB.whisk t []
    have hBs : SChain (s ++ w) (B.map (whL s [])) (s ++ w) := by simpa using hB.whisk s []
    rw [h1, cl_comp hLw hBt, cl_comp hBs hLw]
    have E := cl_interchange (D := D) (Sc := Sc) (μ := μ) (S := s ++ w) (T := t ++ w) [] [] hL hB
    simp only [List.nil_append, List.append_nil] at E
    exact E
  | zero => rw [map_zero, Limits.zero_comp, Limits.comp_zero, smul_zero]
  | add x y _ _ hx hy =>
    rw [map_add, Preadditive.add_comp, Preadditive.comp_add, hx, hy, smul_add]
  | smul a x _ hx =>
    rw [map_smul, Linear.smul_comp, Linear.comp_smul, hx, smul_comm]

/-- A homogeneous 2-morphism `f` of parity `p` placed on the right and an endomorphism diagram `B`
of the strands `w` on its left can be exchanged with the sign `(-1)^{p|B|}`. -/
theorem plcL_right_interchange (μ : X) (w : List (Letter I)) {s t : List (Letter I)} {p : ZMod 2}
    {f : (pres D Sc).obj (ob D (wt D μ []) s) ⟶ (pres D Sc).obj (ob D (wt D μ []) t)}
    (hf : f ∈ homPar D Sc (wt D μ []) s t p) {B : List (LayerData I)} (hB : SChain w B w) :
    plcL D Sc μ w [] s t f ≫ cl D Sc μ (w ++ t ++ []) (w ++ t ++ []) (B.map (whL [] t)) =
      zsign k (p * parsum D B) •
        (cl D Sc μ (w ++ s ++ []) (w ++ s ++ []) (B.map (whL [] s)) ≫ plcL D Sc μ w [] s t f) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl, rfl⟩ := hf
    have h1 : plcL D Sc μ w [] s t (cl D Sc (wt D μ []) s t L) =
        cl D Sc μ (w ++ s ++ []) (w ++ t ++ []) (L.map (whL w [])) := plcL_cl D Sc μ w [] s t L
    have hLw : SChain (w ++ s ++ []) (L.map (whL w [])) (w ++ t ++ []) := by
      simpa using hL.whisk w []
    have hBt : SChain (w ++ t ++ []) (B.map (whL [] t)) (w ++ t ++ []) := by
      simpa using hB.whisk [] t
    have hBs : SChain (w ++ s ++ []) (B.map (whL [] s)) (w ++ s ++ []) := by
      simpa using hB.whisk [] s
    rw [h1, cl_comp hLw hBt, cl_comp hBs hLw]
    have E := cl_interchange (D := D) (Sc := Sc) (μ := μ) (S := w ++ s ++ []) (T := w ++ t ++ [])
      [] [] hB hL
    simp only [List.nil_append, List.append_nil] at E
    rw [E, smul_smul, mul_comm (parsum D L), zsign_mul_self', one_smul]
  | zero => rw [map_zero, Limits.zero_comp, Limits.comp_zero, smul_zero]
  | add x y _ _ hx hy =>
    rw [map_add, Preadditive.add_comp, Preadditive.comp_add, hx, hy, smul_add]
  | smul a x _ hx =>
    rw [map_smul, Linear.smul_comp, Linear.comp_smul, hx, smul_comm]

/-! ## Parities of `η'` and `ε'` -/

variable (cs : CScalars Sc)

/-- `η'` has parity `|i, λ| = |i|(⟨hᵢ,λ⟩ + 1)`. -/
theorem etaP_mem (i : I) (μ : X) : etaP cs i μ ∈ homPar D Sc μ [] [up i, dn i] (ipar D i μ) := by
  rcases lt_or_ge 0 (D.h i μ) with hp | hp
  · rw [etaP_of_pos cs hp]
    refine Submodule.smul_mem _ _ (cl_mem_homPar (sChain_dcupL i _) ?_)
    simp only [parsum, parity_dcupL, ipar, natCast_toNat_zmod _ (show 0 ≤ D.h i μ - 1 by omega)]
    push_cast
    generalize D.parity i = a; generalize (D.h i μ : ZMod 2) = y
    revert a y; decide
  · rw [etaP_eq_of_nonpos cs hp]
    refine Submodule.smul_mem _ _ (cl_mem_homPar ((sChain_etaL i _).append (sChain_lcrossL i i)) ?_)
    simp only [parsum, parity_sum_append, parity_etaL, parity_lcrossL, ipar,
      natCast_toNat_zmod _ (show 0 ≤ -D.h i μ by omega)]
    push_cast
    generalize D.parity i = a; generalize (D.h i μ : ZMod 2) = y
    revert a y; decide

/-- `ε'` has parity `|i, λ| = |i|(⟨hᵢ,λ⟩ + 1)`. -/
theorem epsP_mem (i : I) (μ : X) : epsP cs i μ ∈ homPar D Sc μ [dn i, up i] [] (ipar D i μ) := by
  rcases lt_or_ge (D.h i μ) 0 with hp | hp
  · rw [epsP_of_neg cs hp]
    refine Submodule.smul_mem _ _ (cl_mem_homPar (sChain_dcapL i _) ?_)
    simp only [parsum, parity_dcapL, ipar, natCast_toNat_zmod _ (show 0 ≤ -D.h i μ - 1 by omega)]
    push_cast
    generalize D.parity i = a; generalize (D.h i μ : ZMod 2) = y
    revert a y; decide
  · rw [epsP_eq_of_nonneg cs hp]
    refine Submodule.smul_mem _ _ (cl_mem_homPar ((sChain_lcrossL i i).append (sChain_epsL i _)) ?_)
    simp only [parsum, parity_sum_append, parity_epsL, parity_lcrossL, ipar,
      natCast_toNat_zmod _ hp]
    generalize D.parity i = a; generalize (D.h i μ : ZMod 2) = y
    revert a y; decide

end OddMath.SKM
