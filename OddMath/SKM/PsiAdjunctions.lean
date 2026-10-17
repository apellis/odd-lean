/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PsiCrossings
import OddMath.SKM.ChevalleyLeft
import OddMath.SKM.PlacementHom

/-!
# The cup and cap images of ψ

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Proposition 9.4 (the cup/cap assignments in its proof) and adjunction relations (1.10).

The target is `TwoSOp k (Uqπ D Sc sy hc)`, with the object and strand assignments
`psiObj` and `psiMap`. The right cup is sent to `epsP`; the right cap is sent to
`sign k (ipar D i μ) • etaP`. Both maps are even in the shifted super-opposite,
with degrees `sy.d i * (1 + D.h i μ)` and `sy.d i * (1 - D.h i μ)`, respectively.

`psiCupRight`, `psiCapLeft`, `psiCupLeft`, and `psiCapRight` are their normalized
whiskerings on an upward or downward strand. The four `psiCup_whisker*` and
`psiCap_whisker*` lemmas identify them with the actual target whiskerings. These
comparisons are heterogeneous only because concatenated boundary words have to be
normalized. The final `psiAdjunction_up_whisker` and `psiAdjunction_dn_whisker`
are ordinary equalities of the actual whiskered composites, with the boundary
transports displayed. Their proofs use the established left adjunction (6.6),
including its sign, rather than assuming preservation of (1.10).

The downward Π-shift is essential: in `psiF ◁ psiCap` its whiskering sign cancels
the cap coefficient. The square-root parameter used by the dot/crossing assignments
does not occur in this slice. The scalar compatibility `CScalars Sc` and homogeneous
parameters are retained. This is not yet the strict graded 2-superfunctor, its
extension to the envelope, or the two-sided inverse asserted in Proposition 9.4.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

private theorem wt_du (μ : X) (i : I) : wt D μ [dn i, up i] = μ := by
  simp [wt_cons, sh, dn, up]
private theorem wt_ud (μ : X) (i : I) : wt D μ [up i, dn i] = μ := by
  simp [wt_cons, sh, dn, up]

/-- The printed cup image, as a morphism in the actual shifted super-opposite. -/
def psiCup (cs : CScalars Sc) (μ : X) (i : I) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) μ μ [] rfl ⟶
      psiAt μ μ [dn i, up i] (wt_du μ i) := SOp.mk' (epsP cs i μ)

/-- The printed cap image, including the coefficient `(-1)^|i,μ|`. -/
def psiCap (cs : CScalars Sc) (μ : X) (i : I) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) μ μ [up i, dn i] (wt_ud μ i) ⟶
      psiAt μ μ [] rfl := SOp.mk' (sign k (ipar D i μ) • etaP cs i μ)

private theorem homPar_mem {μ : X} {s t : List (Letter I)} {p : ZMod 2}
    {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    (hf : f ∈ homPar D Sc μ s t p) :
    f ∈ (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ p := by
  refine Submodule.span_le.mpr ?_ hf
  rintro f ⟨L, hL, hp, rfl⟩
  rw [cl_of hL]
  apply Presentation.diag_mem_homDeg'
  rw [degree_parity_mkD]
  exact hp

private theorem psiParity_du (μ : X) (i : I) :
    psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) μ μ [dn i, up i] (wt_du μ i)) =
      ipar D i μ := by
  simpa [psiParity, psiWordAt, ob, wd] using ipar_wt_up (D := D) i μ

private theorem psiParity_ud (μ : X) (i : I) :
    psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) μ μ [up i, dn i] (wt_ud μ i)) =
      ipar D i μ := by
  simp [psiParity, psiWordAt, ob, wd]

/-- The parity shift on the downward strand makes the cup image even. -/
theorem psiCup_mem_parity (cs : CScalars Sc) (μ : X) (i : I) :
    psiCup (sy := sy) (hc := hc) cs μ i ∈ parity (R := k) _ _ 0 := by
  change epsP cs i μ ∈ (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _
    (0 + (psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) μ μ [dn i, up i] (wt_du μ i)) + 0))
  simpa only [psiParity_du, zero_add, add_zero] using homPar_mem (epsP_mem cs i μ)

/-- The cap image is even in the shifted target. -/
theorem psiCap_mem_parity (cs : CScalars Sc) (μ : X) (i : I) :
    psiCap (sy := sy) (hc := hc) cs μ i ∈ parity (R := k) _ _ 0 := by
  change sign k (ipar D i μ) • etaP cs i μ ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _
      (0 + (0 + psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) μ μ [up i, dn i] (wt_ud μ i))))
  simp only [psiParity_ud, zero_add]
  exact Submodule.smul_mem _ _ (homPar_mem (etaP_mem cs i μ))

private theorem cl_degree {μ : X} {s t : List (Letter I)} {L : List (LayerData I)} {d : ℤ}
    (h : SChain s L t) (hd : gsum D sy μ L = d) :
    cl D Sc μ s t L ∈ (pres D Sc).homDeg (gdeg D sy) _ _ d := by
  rw [cl_of h]
  apply Presentation.diag_mem_homDeg'
  rwa [degree_gdeg_mkD]

private theorem epsP_degree (cs : CScalars Sc) (μ : X) (i : I) :
    epsP cs i μ ∈ (pres D Sc).homDeg (gdeg D sy) _ _ (sy.d i * (1 + D.h i μ)) := by
  rcases lt_or_ge (D.h i μ) 0 with h | h
  · rw [epsP_of_neg cs h]
    apply Submodule.smul_mem
    apply cl_degree (sChain_dcapL i _)
    rw [gsum_dcapL, Int.toNat_of_nonneg (show 0 ≤ -D.h i μ - 1 by omega)]
    ring
  · rw [epsP_eq_of_nonneg cs h]
    apply Submodule.smul_mem
    apply cl_degree ((sChain_lcrossL i i).append (sChain_epsL i _))
    rw [gsum_append, gsum_lcrossL, gsum_epsL, Int.toNat_of_nonneg h]
    ring

private theorem etaP_degree (cs : CScalars Sc) (μ : X) (i : I) :
    etaP cs i μ ∈ (pres D Sc).homDeg (gdeg D sy) _ _ (sy.d i * (1 - D.h i μ)) := by
  rcases lt_or_ge 0 (D.h i μ) with h | h
  · rw [etaP_of_pos cs h]
    apply Submodule.smul_mem
    apply cl_degree (sChain_dcupL i _)
    rw [gsum_dcupL, Int.toNat_of_nonneg (show 0 ≤ D.h i μ - 1 by omega)]
    ring
  · rw [etaP_eq_of_nonpos cs h]
    apply Submodule.smul_mem
    apply cl_degree ((sChain_etaL i _).append (sChain_lcrossL i i))
    rw [gsum_append, gsum_lcrossL, gsum_etaL,
      Int.toNat_of_nonneg (show 0 ≤ -D.h i μ by omega)]
    ring

/-- The cup image has the degree of the source cup. -/
theorem psiCup_mem_degree (cs : CScalars Sc) (μ : X) (i : I) :
    psiCup (sy := sy) (hc := hc) cs μ i ∈
      GradedSupercategory.degree (R := k) _ _ (sy.d i * (1 + D.h i μ)) := by
  change epsP cs i μ ∈ (pres D Sc).homDeg (gdeg D sy) _ _ (sy.d i * (1 + D.h i μ) + (0 - 0))
  simpa only [sub_self, add_zero] using epsP_degree (sy := sy) cs μ i

/-- The cap image has the degree of the source cap. -/
theorem psiCap_mem_degree (cs : CScalars Sc) (μ : X) (i : I) :
    psiCap (sy := sy) (hc := hc) cs μ i ∈
      GradedSupercategory.degree (R := k) _ _ (sy.d i * (1 - D.h i μ)) := by
  change sign k (ipar D i μ) • etaP cs i μ ∈
    (pres D Sc).homDeg (gdeg D sy) _ _ (sy.d i * (1 - D.h i μ) + (0 - 0))
  simpa only [sub_self, add_zero] using
    Submodule.smul_mem _ (sign k (ipar D i μ)) (etaP_degree (sy := sy) cs μ i)

private theorem wt_udu (μ : X) (i : I) : wt D μ [up i, dn i, up i] = wt D μ [up i] := by
  simp only [wt_cons, wt_nil]
  simp [sh]
private theorem wt_dud (μ : X) (i : I) : wt D μ [dn i, up i, dn i] = wt D μ [dn i] := by
  simp only [wt_cons, wt_nil]
  simp [sh]

/-- The downward strand with the weight-dependent parity shift prescribed by ψ. -/
abbrev psiF (μ : X) (i : I) :=
  psiMap (sy := sy) (hc := hc) (psiWord (Sc := Sc) μ [dn i])

/-- The cup on the right of `psiE`, in normalized boundary coordinates. -/
def psiCupRight (cs : CScalars Sc) (μ : X) (i : I) :
    psiE (sy := sy) (hc := hc) μ i ⟶
      psiAt (wt D μ [up i]) μ [up i, dn i, up i] (wt_udu μ i) :=
  SOp.mk' (reps cs i μ)
/-- The cap on the left of `psiE`, in normalized boundary coordinates. -/
def psiCapLeft (cs : CScalars Sc) (μ : X) (i : I) :
    psiAt (sy := sy) (hc := hc) (wt D μ [up i]) μ [up i, dn i, up i] (wt_udu μ i) ⟶
      psiE μ i := SOp.mk' (sign k (ipar D i μ) • leta cs i μ)
/-- The cup on the left of `psiF`, in normalized boundary coordinates. -/
def psiCupLeft (cs : CScalars Sc) (μ : X) (i : I) :
    psiF (sy := sy) (hc := hc) μ i ⟶
      psiAt (wt D μ [dn i]) μ [dn i, up i, dn i] (wt_dud μ i) :=
  SOp.mk' (lepsF cs i μ)
/-- The cap on the right of `psiF`; its two signs cancel. -/
def psiCapRight (cs : CScalars Sc) (μ : X) (i : I) :
    psiAt (sy := sy) (hc := hc) (wt D μ [dn i]) μ [dn i, up i, dn i] (wt_dud μ i) ⟶
      psiF μ i := SOp.mk' (retaF cs i μ)

private theorem ipar_wt_dn (i : I) (μ : X) : ipar D i (wt D μ [dn i]) = ipar D i μ := by
  rw [ipar, ipar, h_wt_dn]
  push_cast
  rw [show (2 : ZMod 2) = 0 from rfl, sub_zero]

private theorem parity_udu (μ : X) (i : I) :
    psiParity (sy := sy) (hc := hc)
      (psiWordAt (Sc := Sc) (wt D μ [up i]) μ [up i, dn i, up i] (wt_udu μ i)) = ipar D i μ := by
  simpa [psiParity, psiWordAt, ob, wd] using ipar_wt_up (D := D) i μ
private theorem parity_dud (μ : X) (i : I) :
    psiParity (sy := sy) (hc := hc)
      (psiWordAt (Sc := Sc) (wt D μ [dn i]) μ [dn i, up i, dn i] (wt_dud μ i)) = 0 := by
  simp only [psiParity, psiWordAt, ob, wd, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Bool.false_eq_true, reduceIte, add_zero, ipar_wt_dn]
  rw [wt_ud, wt_nil, zero_add, zmod2_add_self]

private theorem cupRight_even (cs : CScalars Sc) (μ : X) (i : I) :
    SOp.unsop (psiCupRight (sy := sy) (hc := hc) cs μ i) ∈ parity (R := k) _ _ 0 := by
  change reps cs i μ ∈ (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _
    (0 + (psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) _ μ _ _) + 0))
  simp only [parity_udu, zero_add, add_zero]
  exact homPar_mem (plcL_mem μ [up i] [] (epsP_mem cs i (wt D μ [])))
private theorem capLeft_even (cs : CScalars Sc) (μ : X) (i : I) :
    SOp.unsop (psiCapLeft (sy := sy) (hc := hc) cs μ i) ∈ parity (R := k) _ _ 0 := by
  change sign k (ipar D i μ) • leta cs i μ ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _
      (0 + (0 + psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) _ μ _ _)))
  simp only [parity_udu, zero_add]
  apply Submodule.smul_mem
  have h := homPar_mem (plcL_mem μ [] [up i] (etaP_mem cs i (wt D μ [up i])))
  change leta cs i μ ∈ (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _
    (ipar D i (wt D μ [up i])) at h
  rwa [ipar_wt_up] at h
private theorem cupLeft_even (cs : CScalars Sc) (μ : X) (i : I) :
    SOp.unsop (psiCupLeft (sy := sy) (hc := hc) cs μ i) ∈ parity (R := k) _ _ 0 := by
  change lepsF cs i μ ∈ (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _
    (0 + (psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) _ μ _ _) +
      psiParity (sy := sy) (hc := hc) (psiWord (Sc := Sc) μ [dn i])))
  simp only [parity_dud, zero_add, psiParity_dn]
  have h := homPar_mem (plcL_mem μ [] [dn i] (epsP_mem cs i (wt D μ [dn i])))
  change lepsF cs i μ ∈ (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _
    (ipar D i (wt D μ [dn i])) at h
  rwa [ipar_wt_dn] at h
private theorem capRight_even (cs : CScalars Sc) (μ : X) (i : I) :
    SOp.unsop (psiCapRight (sy := sy) (hc := hc) cs μ i) ∈ parity (R := k) _ _ 0 := by
  change retaF cs i μ ∈ (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _
    (0 + (psiParity (sy := sy) (hc := hc) (psiWord (Sc := Sc) μ [dn i]) +
      psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) _ μ _ _)))
  simp only [parity_dud, zero_add, add_zero, psiParity_dn]
  exact homPar_mem (plcL_mem μ [dn i] [] (etaP_mem cs i (wt D μ [])))

/-- The upward zigzag in normalized coordinates. -/
theorem psiAdjunction_up (cs : CScalars Sc) (μ : X) (i : I) :
    psiCupRight (sy := sy) (hc := hc) cs μ i ≫ psiCapLeft cs μ i = 𝟙 (psiE μ i) := by
  apply SOp.hom_ext
  rw [SOp.comp_of_mem (cupRight_even cs μ i) (capLeft_even cs μ i)]
  simp only [zero_mul, sign_zero, one_smul]
  change (sign k (ipar D i μ) • leta cs i μ) ≫ reps cs i μ = 𝟙 _
  rw [Linear.smul_comp, eq_6_6_a, smul_smul]
  rw [sign_eq_zsign, zsign_mul_self', one_smul]

/-- The downward zigzag in normalized coordinates. -/
theorem psiAdjunction_dn (cs : CScalars Sc) (μ : X) (i : I) :
    psiCupLeft (sy := sy) (hc := hc) cs μ i ≫ psiCapRight cs μ i = 𝟙 (psiF μ i) := by
  apply SOp.hom_ext
  rw [SOp.comp_of_mem (cupLeft_even cs μ i) (capRight_even cs μ i)]
  simp only [zero_mul, sign_zero, one_smul]
  exact eq_6_6_b cs i μ

private theorem psiWordAt_comp (ν ξ μ : X) (s t : List (Letter I))
    (hs : wt D ξ s = ν) (ht : wt D μ t = ξ) :
    psiWordAt (Sc := Sc) ν ξ s hs ≫ psiWordAt ξ μ t ht =
      psiWordAt ν μ (s ++ t) (by rw [wt_append, ht, hs]) := by
  apply Presentation.Bicat.Hom.ext
  apply Obj.ext
  · change wt D ξ s = wt D μ (s ++ t)
    rw [wt_append, ht]
  · change wd D ξ s ++ wd D μ t = wd D μ (s ++ t)
    rw [wd_append, ht]

private theorem psiAt_comp (ν ξ μ : X) (s t : List (Letter I))
    (hs : wt D ξ s = ν) (ht : wt D μ t = ξ) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ν ξ s hs ≫ psiAt ξ μ t ht =
      psiAt ν μ (s ++ t) (by rw [wt_append, ht, hs]) := by
  rw [← psiMap_comp, psiWordAt_comp]

private theorem target_heq {a b : UGr D Sc sy hc}
    {f g f' g' : psiObj a ⟶ psiObj b} (hf : f = f') (hg : g = g')
    {α : f ⟶ g} {β : f' ⟶ g'} (h : HEq (SOp.unsop α) (SOp.unsop β)) : HEq α β := by
  subst hf; subst hg
  exact heq_of_eq (SOp.hom_ext (eq_of_heq h))

private theorem ob_tensor (ν μ : X) (u s : List (Letter I)) (h : wt D μ s = ν) :
    (ob D ν u).tensor (ob D μ s) = ob D μ (u ++ s ++ []) := by
  apply Obj.ext
  · change wt D ν u = wt D μ (u ++ s ++ [])
    simp only [List.append_nil, wt_append, h]
  · change wd D ν u ++ wd D μ s = wd D μ (u ++ s ++ [])
    simp only [List.append_nil, wd_append, h]

private theorem raw_heq {C : Type*} [Category C] {a b a' b' : C}
    (ha : a = a') (hb : b = b') {f : a ⟶ b} {g : a' ⟶ b'}
    (h : f = eqToHom ha ≫ g ≫ eqToHom hb.symm) : HEq f g := by
  subst ha; subst hb
  exact heq_of_eq (by simpa using h)

private theorem wL_plcL (ν μ : X) (u s t : List (Letter I))
    (hs : wt D μ s = ν) (ht : wt D μ t = ν) {p : ZMod 2}
    {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    (hf : f ∈ homPar D Sc μ s t p) :
    HEq ((pres D Sc).wL (ob D ν u) f) (plcL D Sc μ u [] s t f) := by
  apply raw_heq (congrArg (pres D Sc).obj (ob_tensor ν μ u s hs))
    (congrArg (pres D Sc).obj (ob_tensor ν μ u t ht))
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, _, rfl⟩ := hf
    erw [plcL_cl]
    rw [cl_of hL]
    have hcomp : (ob D ν u).Composable (ob D μ s) :=
      Presentation.Bicat.Hom.composable
        (psiWordAt (Sc := Sc) (wt D ν u) ν u rfl) (psiWordAt ν μ s hs)
    rw [Presentation.wL_diag_of_composable _ _ _ hcomp]
    rw [cl_of (hL.whisk u [])]
    refine Presentation.diag_eq_of_layers_eq' _ _ _ (ob_tensor ν μ u s hs)
      (ob_tensor ν μ u t ht) ?_
    simp only [Diagram.layers_lwhisker, layers_mkD]
    rw [← layList_whisker D μ u [] hL]
    simp only [wt_nil, hs, wd, Layer.wl, Layer.whisker, List.append_nil]
  | zero => simp only [Presentation.wL_zero, map_zero, Limits.comp_zero, Limits.zero_comp]
  | add f g _ _ ihf ihg =>
    simp only [Presentation.wL_add, map_add, Preadditive.comp_add, Preadditive.add_comp, ihf, ihg]
  | smul a f _ ih =>
    simp only [Presentation.wL_smul, map_smul, Linear.comp_smul, Linear.smul_comp, ih]

/-- Comparison with the actual cup whiskered on the left by `psiE`. -/
theorem psiCup_whiskerLeft (cs : CScalars Sc) (μ : X) (i : I) :
    HEq (BicategoryStruct.whiskerLeft (B := TwoSOp k (Uqπ D Sc sy hc))
      (psiE μ i) (psiCup cs μ i)) (psiCupRight (sy := sy) (hc := hc) cs μ i) := by
  apply target_heq
  · exact psiAt_comp _ _ _ _ _ _ _
  · exact psiAt_comp _ _ _ _ _ _ _
  rw [TwoSOp.unsop_whiskerLeft]
  change HEq (Envelope.toHom ((SOp.unop (psiE (Sc := Sc) (sy := sy) (hc := hc) μ i)) ◁
    SOp.unsop (psiCup cs μ i))) (reps cs i μ)
  rw [TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl]
  change HEq ((pres D Sc).wL (ob D μ [up i]) (epsP cs i μ)) (reps cs i μ)
  exact wL_plcL μ μ [up i] [dn i, up i] [] (wt_du μ i) rfl (epsP_mem cs i μ)

private theorem ob_tensor_right (μ : X) (s v : List (Letter I)) :
    (ob D (wt D μ v) s).tensor (ob D μ v) = ob D μ ([] ++ s ++ v) := by
  simpa only [List.append_nil, List.nil_append] using ob_tensor (wt D μ v) μ s v rfl

private theorem wR_plcL (ν μ : X) (s t v : List (Letter I))
    (hs : wt D (wt D μ v) s = ν) (ht : wt D (wt D μ v) t = ν) {p : ZMod 2}
    {f : (pres D Sc).obj (ob D (wt D μ v) s) ⟶ (pres D Sc).obj (ob D (wt D μ v) t)}
    (hf : f ∈ homPar D Sc (wt D μ v) s t p) :
    HEq ((pres D Sc).wRAt ν f (ob D μ v) hs ht) (plcL D Sc μ [] v s t f) := by
  apply raw_heq (congrArg (pres D Sc).obj (ob_tensor_right μ s v))
    (congrArg (pres D Sc).obj (ob_tensor_right μ t v))
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, _, rfl⟩ := hf
    rw [plcL_cl, cl_of hL]
    have hcomp : (ob D (wt D μ v) s).Composable (ob D μ v) :=
      Presentation.Bicat.Hom.composable
        (psiWordAt (Sc := Sc) ν (wt D μ v) s hs) (psiWordAt (wt D μ v) μ v rfl)
    rw [Presentation.wRAt_diag _ _ _ hcomp]
    rw [cl_of (hL.whisk [] v)]
    refine Presentation.diag_eq_of_layers_eq' _ _ _ (ob_tensor_right μ s v)
      (ob_tensor_right μ t v) ?_
    simp only [Diagram.layers_rwhisker, layers_mkD]
    rw [← layList_whisker D μ [] v hL]
    simp only [ob, wd, Layer.wr, Layer.whisker, List.nil_append]
    apply List.map_congr_left
    intro l hl
    apply Layer.ext
    · exact (Diagram.chain (mkD D (wt D μ v) L hL)).start_of_mem (L := l) hl
    all_goals rfl
  | zero => simp only [Presentation.wRAt_zero, map_zero, Limits.comp_zero, Limits.zero_comp]
  | add f g _ _ ihf ihg =>
    simp only [Presentation.wRAt_add, map_add, Preadditive.comp_add, Preadditive.add_comp, ihf, ihg]
  | smul a f _ ih =>
    simp only [Presentation.wRAt_smul, map_smul, Linear.comp_smul, Linear.smul_comp, ih]

private theorem raw_smul_heq {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {a b a' b' : C} {f : a ⟶ b} {g : a' ⟶ b'} (ha : a = a') (hb : b = b')
    (h : HEq f g) (c : k) : HEq (c • f) (c • g) := by
  subst ha; subst hb
  cases h
  rfl

/-- Comparison with the actual cap whiskered on the right by `psiE`. -/
theorem psiCap_whiskerRight (cs : CScalars Sc) (μ : X) (i : I) :
    HEq (BicategoryStruct.whiskerRight (B := TwoSOp k (Uqπ D Sc sy hc))
      (psiCap cs (wt D μ [up i]) i) (psiE μ i))
      (psiCapLeft (sy := sy) (hc := hc) cs μ i) := by
  apply target_heq
  · exact psiAt_comp _ _ _ _ _ _ _
  · exact psiAt_comp _ _ _ _ _ _ _
  rw [TwoSOp.unsop_whiskerRight]
  change HEq (Envelope.toHom (SOp.unsop (psiCap (sy := sy) (hc := hc) cs (wt D μ [up i]) i) ▷
    SOp.unop (psiE μ i))) (sign k (ipar D i μ) • leta cs i μ)
  rw [TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl]
  change HEq ((pres D Sc).wRAt (wt D μ [up i] : X)
    (sign k (ipar D i (wt D μ [up i])) • etaP cs i (wt D μ [up i]))
    (ob D μ [up i]) rfl (wt_ud (D := D) _ i)) (sign k (ipar D i μ) • leta cs i μ)
  rw [Presentation.wRAt_smul, ipar_wt_up]
  apply raw_smul_heq
  · exact congrArg (pres D Sc).obj (ob_tensor (D := D) _ μ [] [up i] rfl)
  · exact congrArg (pres D Sc).obj (ob_tensor (D := D) _ μ [up i, dn i] [up i] rfl)
  exact wR_plcL _ μ [] [up i, dn i] [up i] rfl (wt_ud _ i) (etaP_mem cs i _)

/-- Comparison with the actual cup whiskered on the right by the shifted `psiF`. -/
theorem psiCup_whiskerRight (cs : CScalars Sc) (μ : X) (i : I) :
    HEq (BicategoryStruct.whiskerRight (B := TwoSOp k (Uqπ D Sc sy hc))
      (psiCup cs (wt D μ [dn i]) i) (psiF μ i))
      (psiCupLeft (sy := sy) (hc := hc) cs μ i) := by
  apply target_heq
  · exact psiAt_comp _ _ _ _ _ _ _
  · exact psiAt_comp _ _ _ _ _ _ _
  rw [TwoSOp.unsop_whiskerRight]
  change HEq (Envelope.toHom (SOp.unsop (psiCup (sy := sy) (hc := hc) cs (wt D μ [dn i]) i) ▷
    SOp.unop (psiF μ i))) (lepsF cs i μ)
  rw [TwoEnvelope.toHom_whiskerRight_of_mem
    (show Envelope.toHom (SOp.unsop (psiCup (sy := sy) (hc := hc) cs (wt D μ [dn i]) i)) ∈
      parity (R := k) _ _ (ipar D i (wt D μ [dn i])) from homPar_mem (epsP_mem cs i _))]
  simp only [psiCup, psiAt, psiMap, SOp.unsop_mk', psiParity_du,
    show psiParity (sy := sy) (hc := hc)
      (psiWordAt (Sc := Sc) (wt D μ [dn i]) (wt D μ [dn i]) [] rfl) = 0 from rfl,
    add_zero, zmod2_add_self, mul_zero, sign_zero, one_smul]
  exact wR_plcL _ μ [dn i, up i] [] [dn i] (wt_du _ i) rfl (epsP_mem cs i _)

/-- Comparison with the actual cap whiskered on the left by the shifted `psiF`. -/
theorem psiCap_whiskerLeft (cs : CScalars Sc) (μ : X) (i : I) :
    HEq (BicategoryStruct.whiskerLeft (B := TwoSOp k (Uqπ D Sc sy hc))
      (psiF μ i) (psiCap cs μ i)) (psiCapRight (sy := sy) (hc := hc) cs μ i) := by
  apply target_heq
  · exact psiAt_comp _ _ _ _ _ _ _
  · exact psiAt_comp _ _ _ _ _ _ _
  rw [TwoSOp.unsop_whiskerLeft]
  change HEq (Envelope.toHom ((SOp.unop (psiF (Sc := Sc) (sy := sy) (hc := hc) μ i)) ◁
    SOp.unsop (psiCap cs μ i))) (retaF cs i μ)
  rw [TwoEnvelope.toHom_whiskerLeft_of_mem _
    (show Envelope.toHom (SOp.unsop (psiCap (sy := sy) (hc := hc) cs μ i)) ∈
      parity (R := k) _ _ (ipar D i μ) from
        Submodule.smul_mem _ _ (homPar_mem (etaP_mem cs i μ)))]
  change HEq (sign k (psiParity (sy := sy) (hc := hc) (psiWord (Sc := Sc) μ [dn i]) * ipar D i μ) •
    (pres D Sc).wL (ob D μ [dn i]) (sign k (ipar D i μ) • etaP cs i μ)) (retaF cs i μ)
  rw [psiParity_dn, Presentation.wL_smul, smul_smul]
  have h : sign k (ipar D i μ * ipar D i μ) * sign k (ipar D i μ) = 1 := by
    rcases parity_eq_zero_or_one (ipar D i μ) with h | h <;> simp [h]
  rw [h, one_smul]
  exact wL_plcL μ μ [dn i] [] [up i, dn i] rfl (wt_ud μ i) (etaP_mem cs i μ)

private theorem reindex_of_heq {C : Type*} [Category C] {a b a' b' : C}
    (ha : a = a') (hb : b = b') {f : a ⟶ b} {g : a' ⟶ b'} (h : HEq f g) :
    eqToHom ha.symm ≫ f ≫ eqToHom hb = g := by
  subst ha; subst hb
  cases h
  simp

/-- The upward zigzag (1.10) for the actual cup/cap whiskerings. The equality transports
only normalize the concatenated boundary words; no relation is assumed. -/
theorem psiAdjunction_up_whisker (cs : CScalars Sc) (μ : X) (i : I) :
    (eqToHom (psiAt_comp (Sc := Sc) (sy := sy) (hc := hc)
        (wt D μ [up i]) μ μ [up i] [] rfl rfl).symm ≫
      (psiE μ i ◁ psiCup cs μ i) ≫
      eqToHom (psiAt_comp (wt D μ [up i]) μ μ [up i] [dn i, up i] rfl (wt_du μ i))) ≫
    (eqToHom (psiAt_comp (wt D μ [up i]) (wt D μ [up i]) μ [up i, dn i] [up i]
        (wt_ud _ i) rfl).symm ≫
      (psiCap cs (wt D μ [up i]) i ▷ psiE μ i) ≫
      eqToHom (psiAt_comp (wt D μ [up i]) (wt D μ [up i]) μ [] [up i] rfl rfl)) =
      𝟙 (psiE μ i) := by
  rw [reindex_of_heq _ _ (psiCup_whiskerLeft cs μ i),
    reindex_of_heq _ _ (psiCap_whiskerRight cs μ i)]
  exact psiAdjunction_up cs μ i
  all_goals exact psiAt_comp _ _ _ _ _ _ _

/-- The downward zigzag (1.10), including the weight-dependent Π-shift of `Fᵢ`. -/
theorem psiAdjunction_dn_whisker (cs : CScalars Sc) (μ : X) (i : I) :
    (eqToHom (psiAt_comp (Sc := Sc) (sy := sy) (hc := hc)
        (wt D μ [dn i]) (wt D μ [dn i]) μ [] [dn i] rfl rfl).symm ≫
      (psiCup cs (wt D μ [dn i]) i ▷ psiF μ i) ≫
      eqToHom (psiAt_comp (wt D μ [dn i]) (wt D μ [dn i]) μ [dn i, up i] [dn i]
        (wt_du _ i) rfl)) ≫
    (eqToHom (psiAt_comp (wt D μ [dn i]) μ μ [dn i] [up i, dn i] rfl (wt_ud μ i)).symm ≫
      (psiF μ i ◁ psiCap cs μ i) ≫
      eqToHom (psiAt_comp (wt D μ [dn i]) μ μ [dn i] [] rfl rfl)) =
      𝟙 (psiF μ i) := by
  rw [reindex_of_heq _ _ (psiCup_whiskerRight cs μ i),
    reindex_of_heq _ _ (psiCap_whiskerLeft cs μ i)]
  exact psiAdjunction_dn cs μ i
  all_goals exact psiAt_comp _ _ _ _ _ _ _

/-- Normalize a left whiskering in the ψ target, retaining its parity sign.
Used to evaluate the mixed crossing and the dotted inversion entries. -/
theorem psiWhiskerLeft_heq (ξ ν μ : X) (u s t : List (Letter I))
    (hu : wt D ν u = ξ) (hs : wt D μ s = ν) (ht : wt D μ t = ν)
    {p : ZMod 2} {f : (pres D Sc).obj (ob D μ t) ⟶ (pres D Sc).obj (ob D μ s)}
    (hf : f ∈ homPar D Sc μ t s p) :
    HEq (psiAt (Sc := Sc) (sy := sy) (hc := hc) ξ ν u hu ◁
      (show psiAt ν μ s hs ⟶ psiAt ν μ t ht from SOp.mk' f))
      (show psiAt (Sc := Sc) (sy := sy) (hc := hc) ξ μ (u ++ s ++ [])
          (by simp only [List.append_nil, wt_append, hs, hu]) ⟶
        psiAt ξ μ (u ++ t ++ []) (by simp only [List.append_nil, wt_append, ht, hu]) from
        SOp.mk' (sign k (psiParity (sy := sy) (hc := hc)
          (psiWordAt (Sc := Sc) ξ ν u hu) * p) • plcL D Sc μ u [] t s f)) := by
  apply target_heq
    (by simpa only [List.append_nil] using psiAt_comp (Sc := Sc) (sy := sy) (hc := hc) _ _ _ _ _ _ _)
    (by simpa only [List.append_nil] using psiAt_comp (Sc := Sc) (sy := sy) (hc := hc) _ _ _ _ _ _ _)
  rw [TwoSOp.unsop_whiskerLeft]
  change HEq (Envelope.toHom ((SOp.unop (psiAt (Sc := Sc) (sy := sy) (hc := hc) ξ ν u hu)) ◁
    (show SOp.unop (psiAt ν μ t ht) ⟶ SOp.unop (psiAt ν μ s hs) from f))) _
  rw [TwoEnvelope.toHom_whiskerLeft_of_mem _ (homPar_mem hf)]
  change HEq (sign k (psiParity (sy := sy) (hc := hc)
    (psiWordAt (Sc := Sc) ξ ν u hu) * p) • (pres D Sc).wL (ob D ν u) f) _
  apply raw_smul_heq (congrArg (pres D Sc).obj (ob_tensor ν μ u t ht))
    (congrArg (pres D Sc).obj (ob_tensor ν μ u s hs))
  exact wL_plcL ν μ u t s ht hs hf

/-- Normalize a right whiskering in the ψ target, retaining its parity sign. -/
theorem psiWhiskerRight_heq (ν μ : X) (s t v : List (Letter I))
    (hs : wt D (wt D μ v) s = ν) (ht : wt D (wt D μ v) t = ν)
    {p : ZMod 2}
    {f : (pres D Sc).obj (ob D (wt D μ v) t) ⟶ (pres D Sc).obj (ob D (wt D μ v) s)}
    (hf : f ∈ homPar D Sc (wt D μ v) t s p) :
    HEq ((show psiAt (Sc := Sc) (sy := sy) (hc := hc) ν (wt D μ v) s hs ⟶
        psiAt ν (wt D μ v) t ht from SOp.mk' f) ▷
      psiAt (wt D μ v) μ v rfl)
      (show psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ (s ++ v) (by rw [wt_append, hs]) ⟶
        psiAt ν μ (t ++ v) (by rw [wt_append, ht]) from
        SOp.mk' (sign k (psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) (wt D μ v) μ v rfl) *
          (p + (psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν (wt D μ v) t ht) +
            psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν (wt D μ v) s hs)))) •
          plcL D Sc μ [] v t s f)) := by
  apply target_heq
    (by simpa only [List.append_nil] using psiAt_comp (Sc := Sc) (sy := sy) (hc := hc) _ _ _ _ _ _ _)
    (by simpa only [List.append_nil] using psiAt_comp (Sc := Sc) (sy := sy) (hc := hc) _ _ _ _ _ _ _)
  rw [TwoSOp.unsop_whiskerRight]
  change HEq (Envelope.toHom ((show SOp.unop (psiAt (Sc := Sc) (sy := sy) (hc := hc)
      ν (wt D μ v) t ht) ⟶ SOp.unop (psiAt ν (wt D μ v) s hs) from f) ▷
    SOp.unop (psiAt (wt D μ v) μ v rfl))) _
  rw [TwoEnvelope.toHom_whiskerRight_of_mem (homPar_mem hf)]
  change HEq (_ • (pres D Sc).wRAt ν f (ob D μ v) ht hs) _
  apply raw_smul_heq (congrArg (pres D Sc).obj (ob_tensor_right μ t v))
    (congrArg (pres D Sc).obj (ob_tensor_right μ s v))
  exact wR_plcL ν μ t s v ht hs hf

/-- Left whiskering, with concatenated words normalized. -/
def psiWhiskerLeft (ξ ν μ : X) (u s t : List (Letter I))
    (hu : wt D ν u = ξ) (hs : wt D μ s = ν) (ht : wt D μ t = ν)
    (f : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ psiAt ν μ t ht) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ξ μ (u ++ s ++ [])
        (by simp only [List.append_nil, wt_append, hs, hu]) ⟶
      psiAt ξ μ (u ++ t ++ []) (by simp only [List.append_nil, wt_append, ht, hu]) :=
  eqToHom (by simpa only [List.append_nil] using
    (psiAt_comp (Sc := Sc) (sy := sy) (hc := hc) ξ ν μ u s hu hs).symm) ≫
    (psiAt ξ ν u hu ◁ f) ≫
  eqToHom (by simpa only [List.append_nil] using psiAt_comp ξ ν μ u t hu ht)

/-- Right whiskering, with concatenated words normalized. -/
def psiWhiskerRight (ν μ : X) (s t v : List (Letter I))
    (hs : wt D (wt D μ v) s = ν) (ht : wt D (wt D μ v) t = ν)
    (f : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν (wt D μ v) s hs ⟶
      psiAt ν (wt D μ v) t ht) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ (s ++ v) (by rw [wt_append, hs]) ⟶
      psiAt ν μ (t ++ v) (by rw [wt_append, ht]) :=
  eqToHom (psiAt_comp (Sc := Sc) (sy := sy) (hc := hc) ν (wt D μ v) μ s v hs rfl).symm ≫
    (f ▷ psiAt (wt D μ v) μ v rfl) ≫
  eqToHom (psiAt_comp ν (wt D μ v) μ t v ht rfl)

/-- Raw formula for normalized left whiskering. -/
theorem psiWhiskerLeft_mk (ξ ν μ : X) (u s t : List (Letter I))
    (hu : wt D ν u = ξ) (hs : wt D μ s = ν) (ht : wt D μ t = ν)
    {p : ZMod 2} {f : (pres D Sc).obj (ob D μ t) ⟶ (pres D Sc).obj (ob D μ s)}
    (hf : f ∈ homPar D Sc μ t s p) :
    psiWhiskerLeft (sy := sy) (hc := hc) ξ ν μ u s t hu hs ht (SOp.mk' f) =
      (show psiAt (Sc := Sc) (sy := sy) (hc := hc) ξ μ (u ++ s ++ [])
          (by simp only [List.append_nil, wt_append, hs, hu]) ⟶
        psiAt ξ μ (u ++ t ++ []) (by simp only [List.append_nil, wt_append, ht, hu]) from
        SOp.mk' (sign k (psiParity (sy := sy) (hc := hc)
          (psiWordAt (Sc := Sc) ξ ν u hu) * p) • plcL D Sc μ u [] t s f)) :=
  reindex_of_heq
    (by simpa only [List.append_nil] using psiAt_comp ξ ν μ u s hu hs)
    (by simpa only [List.append_nil] using psiAt_comp ξ ν μ u t hu ht)
    (psiWhiskerLeft_heq ξ ν μ u s t hu hs ht hf)

/-- Raw formula for normalized right whiskering. -/
theorem psiWhiskerRight_mk (ν μ : X) (s t v : List (Letter I))
    (hs : wt D (wt D μ v) s = ν) (ht : wt D (wt D μ v) t = ν)
    {p : ZMod 2}
    {f : (pres D Sc).obj (ob D (wt D μ v) t) ⟶ (pres D Sc).obj (ob D (wt D μ v) s)}
    (hf : f ∈ homPar D Sc (wt D μ v) t s p) :
    psiWhiskerRight (sy := sy) (hc := hc) ν μ s t v hs ht (SOp.mk' f) =
      (show psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ (s ++ v) (by rw [wt_append, hs]) ⟶
        psiAt ν μ (t ++ v) (by rw [wt_append, ht]) from SOp.mk' (sign k (psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) (wt D μ v) μ v rfl) *
        (p + (psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν (wt D μ v) t ht) +
          psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν (wt D μ v) s hs)))) •
        plcL D Sc μ [] v t s f)) :=
  reindex_of_heq (psiAt_comp ν (wt D μ v) μ s v hs rfl)
    (psiAt_comp ν (wt D μ v) μ t v ht rfl) (psiWhiskerRight_heq ν μ s t v hs ht hf)

private theorem reindex_mem {C : Type*} [Category* C] [Preadditive C] [Linear k C]
    [Supercategory k C] {a a' b b' : C} (ha : a = a') (hb : b = b')
    {f : a ⟶ b} {p : ZMod 2} (hf : f ∈ parity (R := k) _ _ p) :
    eqToHom ha.symm ≫ f ≫ eqToHom hb ∈ parity (R := k) _ _ p := by
  subst ha; subst hb
  simpa using hf

/-- Normalizing a left whiskering preserves parity. -/
theorem psiWhiskerLeft_mem (ξ ν μ : X) (u s t : List (Letter I))
    (hu : wt D ν u = ξ) (hs : wt D μ s = ν) (ht : wt D μ t = ν)
    {f : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ psiAt ν μ t ht} {p : ZMod 2}
    (hf : f ∈ parity (R := k) _ _ p) :
    psiWhiskerLeft ξ ν μ u s t hu hs ht f ∈ parity (R := k) _ _ p := by
  exact reindex_mem
    (by simpa only [List.append_nil] using psiAt_comp ξ ν μ u s hu hs)
    (by simpa only [List.append_nil] using psiAt_comp ξ ν μ u t hu ht)
    (TwoSupercategory.whiskerLeft_mem (psiAt ξ ν u hu) hf)

/-- Normalizing a right whiskering preserves parity. -/
theorem psiWhiskerRight_mem (ν μ : X) (s t v : List (Letter I))
    (hs : wt D (wt D μ v) s = ν) (ht : wt D (wt D μ v) t = ν)
    {f : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν (wt D μ v) s hs ⟶
      psiAt ν (wt D μ v) t ht} {p : ZMod 2} (hf : f ∈ parity (R := k) _ _ p) :
    psiWhiskerRight ν μ s t v hs ht f ∈ parity (R := k) _ _ p := by
  exact reindex_mem (psiAt_comp ν (wt D μ v) μ s v hs rfl)
    (psiAt_comp ν (wt D μ v) μ t v ht rfl)
    (TwoSupercategory.whiskerRight_mem (psiAt (wt D μ v) μ v rfl) hf)

end OddMath.SKM
