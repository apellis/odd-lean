/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PsiDescent

/-!
# ψ and the inversion relations

Brundan–Ellis, *Super Kac–Moody 2-categories*, Proposition 9.4, inversion
relations (1.12)–(1.14). The seven-shape linear evaluator annihilates each
inversion relation in `Presentation.relation`: both unequal-colour equations,
the five matrix equations at either sign of the weight, and the zero conventions
for diamond entries outside the specified ranges.

The proofs evaluate the source layer lists, including dotted right cups and
caps, and use the target equations from `PsiInversionSame`. They retain the
source coefficients, matrix-entry order, finite sums and weight guards. In
particular, the target off-diagonal theorem numbering is not the ordering of
the source relation constructors.

`psiLin_inversion` packages this family at arbitrary valid left weights;
`psiLin_inversion_context` permits arbitrary linear vertical contexts. This is
an inversion-family slice of the relation-kernel proof, not full quotient
descent or the isomorphism asserted in Proposition 9.4. No relation-preservation,
field or flatness hypothesis is imposed.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}
/-- The complete evaluator sends the primary mixed-crossing word to the verified image. -/
private theorem invRaw_sigma (t : k) (cs : CScalars Sc) (μ : X) (i j : I) :
    psiRaw (sy := sy) (hc := hc) t cs (wt D μ [up j, dn i]) μ (sigmaL i j)
      rfl ((sChain_sigmaL i j).wt_eq D μ) (sChain_sigmaL i j) = psiSigma t μ i j := by
  rw [psiRaw_eq_primary t cs _ μ _ _ _ _ (primaryLayers_sigmaL i j)]
  exact psiPrimaryRaw_sigma_eq t cs μ i j

/-- The adjoined mixed crossing evaluates to its independently verified target image. -/
private theorem invRaw_lcross (t : k) (cs : CScalars Sc) (μ : X) (i j : I) :
    psiRaw (sy := sy) (hc := hc) t cs (wt D μ [up j, dn i]) μ (lcrossL i j)
      ((sChain_sigmaL i j).wt_eq D μ) rfl (sChain_lcrossL i j) = psiLCross t μ i j := by
  change psiRaw t cs _ μ [([], Shape.lcross i j, [])] _ _ _ = _
  rw [psiRaw_gen]
  rfl

/-- The totalized diamond-cup zero relation is killed by the actual evaluation. -/
theorem psiLin_dcupZero (t : k) (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ)
    (hn : D.h i μ ≤ n) :
    psiLin (sy := sy) (hc := hc) t cs μ μ rfl (by simp [wt, sh])
      (relation D Sc (.dcupZero i μ n hn)) = 0 := by
  change psiLin t cs μ μ _ _ (dg D μ _ _) = 0
  rw [psiLin_dg]
  change psiRaw t cs μ μ [([], Shape.dcup i n, [])] _ _ _ = 0
  rw [psiRaw_gen]
  exact psiDiamondCup_zero cs t μ i n hn

/-- The totalized diamond-cap zero relation is killed by the actual evaluation. -/
theorem psiLin_dcapZero (t : k) (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ)
    (hn : -D.h i μ ≤ n) :
    psiLin (sy := sy) (hc := hc) t cs μ μ (by simp [wt, sh]) rfl
      (relation D Sc (.dcapZero i μ n hn)) = 0 := by
  change psiLin t cs μ μ _ _ (dg D μ _ _) = 0
  rw [psiLin_dg]
  change psiRaw t cs μ μ [([], Shape.dcap i n, [])] _ _ _ = 0
  rw [psiRaw_gen]
  exact psiDiamondCap_zero cs t μ i n hn

/-- The first distinct-colour inversion relation is killed in the original linear presentation. -/
theorem psiLin_invNe₁ (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i j : I) (hij : i ≠ j) :
    psiLin (sy := sy) (hc := hc) t cs (wt D μ [up j, dn i]) μ rfl rfl
      (relation D Sc (.invNe₁ i j μ hij)) = 0 := by
  change psiLin t cs _ μ rfl rfl (dg D μ _ _ - idg D μ _) = 0
  rw [map_sub, psiLin_dg, psiLin_idg,
    psiRaw_append t cs _ μ (sigmaL i j) (lcrossL i j) rfl
      ((sChain_sigmaL i j).wt_eq D μ) rfl (sChain_sigmaL i j) (sChain_lcrossL i j),
    invRaw_sigma, invRaw_lcross]
  exact sub_eq_zero.mpr (psi_invNe₁ t ht μ i j hij)

/-- The second distinct-colour inversion relation is killed in the same hom category. -/
theorem psiLin_invNe₂ (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i j : I) (hij : i ≠ j) :
    psiLin (sy := sy) (hc := hc) t cs (wt D μ [up j, dn i]) μ
      ((sChain_sigmaL i j).wt_eq D μ) ((sChain_sigmaL i j).wt_eq D μ)
      (relation D Sc (.invNe₂ i j μ hij)) = 0 := by
  change psiLin t cs _ μ _ _ (dg D μ _ _ - idg D μ _) = 0
  rw [map_sub, psiLin_dg, psiLin_idg,
    psiRaw_append t cs _ μ (lcrossL i j) (sigmaL i j)
      ((sChain_sigmaL i j).wt_eq D μ) rfl ((sChain_sigmaL i j).wt_eq D μ)
      (sChain_lcrossL i j) (sChain_sigmaL i j), invRaw_lcross, invRaw_sigma]
  exact sub_eq_zero.mpr (psi_invNe₂ t ht μ i j hij)

private theorem inv_ud (μ : X) (i : I) : wt D μ [up i, dn i] = μ := by simp [wt, sh]
private theorem inv_du (μ : X) (i : I) : wt D μ [dn i, up i] = μ := by simp [wt, sh]

private theorem invRaw_rebase (t : k) (cs : CScalars Sc) (ν ν' μ : X)
    (L : List (LayerData I)) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (h : SChain s L r) (e : ν = ν') :
    psiRaw (sy := sy) (hc := hc) t cs ν' μ L (hs.trans e) (hr.trans e) h =
      psiRebase e (psiRaw t cs ν μ L hs hr h) := by
  subst ν'
  rfl

private theorem invRaw_sameSigma (t : k) (cs : CScalars Sc) (μ : X) (i : I) :
    psiRaw (sy := sy) (hc := hc) t cs μ μ (sigmaL i i) (inv_ud μ i) (inv_du μ i)
      (sChain_sigmaL i i) = psiSameSigma t μ i := by
  rw [invRaw_rebase t cs (wt D μ [up i, dn i]) μ μ (sigmaL i i) rfl
    ((sChain_sigmaL i i).wt_eq D μ) (sChain_sigmaL i i) (inv_ud μ i), invRaw_sigma]
  rfl

private theorem invRaw_sameLCross (t : k) (cs : CScalars Sc) (μ : X) (i : I) :
    psiRaw (sy := sy) (hc := hc) t cs μ μ (lcrossL i i) (inv_du μ i) (inv_ud μ i)
      (sChain_lcrossL i i) = psiSameLCross t μ i := by
  change psiRaw t cs μ μ [([], Shape.lcross i i, [])] _ _ _ = _
  rw [psiRaw_gen]
  rfl

private theorem invRaw_dcup (t : k) (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ) :
    psiRaw (sy := sy) (hc := hc) t cs μ μ (dcupL i n) rfl (inv_ud μ i)
      (sChain_dcupL i n) = psiDiamondCup cs t μ i n := by
  change psiRaw t cs μ μ [([], Shape.dcup i n, [])] _ _ _ = _
  rw [psiRaw_gen]
  rfl

private theorem invRaw_dcap (t : k) (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ) :
    psiRaw (sy := sy) (hc := hc) t cs μ μ (dcapL i n) (inv_du μ i) rfl
      (sChain_dcapL i n) = psiDiamondCap cs t μ i n := by
  change psiRaw t cs μ μ [([], Shape.dcap i n, [])] _ _ _ = _
  rw [psiRaw_gen]
  rfl

private theorem invRaw_dots (t : k) (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ) :
    psiRaw (sy := sy) (hc := hc) t cs (wt D μ [up i]) μ (dotsL [] i [] n) rfl rfl
      (sChain_dotsL [] i [] n) = cpow (psiDot t μ i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [dotsL, List.replicate_succ, psiRaw, eqToHom_refl, Category.id_comp] at *
    rw [ih]
    rw [cpow_succ']
    congr 1
    simp [psiLayer, psiGen, psiPrimaryGen, psiPlace, Shape.dom, Shape.cod,
      psiWhiskerLeft_nil, psiWhiskerRight_nil]

private theorem invRaw_dotsLeft (t : k) (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ) :
    psiRaw (sy := sy) (hc := hc) t cs μ μ (dotsL [] i [dn i] n) (inv_ud μ i) (inv_ud μ i)
      (sChain_dotsL [] i [dn i] n) = psiSameDotsLeft t μ i n := by
  rw [invRaw_rebase t cs (wt D μ [up i, dn i]) μ μ _ rfl rfl _ (inv_ud μ i)]
  unfold psiSameDotsLeft
  congr 1
  have h := psiRaw_whisk (sy := sy) (hc := hc) t cs
    (wt D μ [up i, dn i]) (wt D μ [up i, dn i]) (wt D μ [dn i]) μ
    [] [dn i] (dotsL [] i [] n) rfl rfl rfl rfl (sChain_dotsL [] i [] n)
  erw [invRaw_dots t cs (wt D μ [dn i]) i n] at h
  simp only [dotsL, List.map_replicate, whL, List.nil_append, List.append_nil] at h
  refine h.trans ?_
  dsimp only [psiPlace]
  rw [psiWhiskerLeft_nil]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

private theorem invRaw_dotsRight (t : k) (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ) :
    psiRaw (sy := sy) (hc := hc) t cs μ μ (dotsL [dn i] i [] n) (inv_du μ i) (inv_du μ i)
      (sChain_dotsL [dn i] i [] n) = psiSameDotsRight t μ i n := by
  have h := psiRaw_whisk (sy := sy) (hc := hc) t cs μ (wt D μ [up i]) μ μ
    [dn i] [] (dotsL [] i [] n) (inv_du μ i) rfl rfl rfl (sChain_dotsL [] i [] n)
  rw [invRaw_dots t cs μ i n] at h
  simp only [dotsL, List.map_replicate, whL, List.append_nil] at h
  refine h.trans ?_
  dsimp only [psiPlace]
  rw [psiWhiskerRight_nil]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

private theorem invRaw_eps (t : k) (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ) :
    psiRaw (sy := sy) (hc := hc) t cs μ μ (epsL i n) (inv_ud μ i) rfl
      (sChain_epsL i n) = psiDottedCap cs t μ i n := by
  dsimp only [epsL]
  rw [psiRaw_append t cs μ μ _ _ (inv_ud μ i) (inv_ud μ i) rfl
    (sChain_dotsL [] i [dn i] n) (by simp [SChain, Shape.dom, Shape.cod]),
    invRaw_dotsLeft, psiRaw_gen]
  rfl

private theorem invRaw_eta (t : k) (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ) :
    psiRaw (sy := sy) (hc := hc) t cs μ μ (etaL i n) rfl (inv_du μ i)
      (sChain_etaL i n) = psiDottedCup cs t μ i n := by
  dsimp only [etaL]
  rw [psiRaw_append t cs μ μ _ _ rfl (inv_du μ i) (inv_du μ i)
    (by simp [SChain, Shape.dom, Shape.cod]) (sChain_dotsL [dn i] i [] n),
    psiRaw_gen, invRaw_dotsRight]
  rfl

/-- The `invP₁` matrix relation belongs to the kernel of the linear evaluation. -/
theorem psiLin_invP₁ (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) (hh : 0 ≤ D.h i μ) :
    psiLin (sy := sy) (hc := hc) t cs μ μ (inv_ud μ i) (inv_ud μ i)
      (relation D Sc (.invP₁ i μ hh)) = 0 := by
  classical
  simp only [relation, map_sub, map_add, map_neg, map_sum, psiLin_dg, psiLin_idg]
  rw [psiRaw_append t cs μ μ (sigmaL i i) (lcrossL i i) (inv_ud μ i) (inv_du μ i)
    (inv_ud μ i) (sChain_sigmaL i i) (sChain_lcrossL i i)]
  simp only [invRaw_sameSigma, invRaw_sameLCross]
  have hj (r : ℕ) := psiRaw_append (sy := sy) (hc := hc) t cs μ μ (epsL i r) (dcupL i r)
    (inv_ud μ i) rfl (inv_ud μ i) (sChain_epsL i r) (sChain_dcupL i r)
  simp_rw [hj]
  simp only [invRaw_eps, invRaw_dcup]
  exact sub_eq_zero.mpr (psi_invP₁ cs t ht μ i hh)

/-- The `invP₂` matrix relation belongs to the kernel of the linear evaluation. -/
theorem psiLin_invP₂ (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) (hh : 0 ≤ D.h i μ) :
    psiLin (sy := sy) (hc := hc) t cs μ μ (inv_du μ i) (inv_du μ i)
      (relation D Sc (.invP₂ i μ hh)) = 0 := by
  classical
  simp only [relation, map_add, psiLin_dg, psiLin_idg]
  rw [psiRaw_append t cs μ μ (lcrossL i i) (sigmaL i i) (inv_du μ i) (inv_ud μ i)
    (inv_du μ i) (sChain_lcrossL i i) (sChain_sigmaL i i)]
  simp only [invRaw_sameLCross, invRaw_sameSigma]
  rw [psi_invP₂ t ht μ i hh, neg_add_cancel]

/-- The `invP₃` matrix relation belongs to the kernel of the linear evaluation. -/
theorem psiLin_invP₃ (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) (m : ℕ) (hm : (m : ℤ) < D.h i μ) :
    psiLin (sy := sy) (hc := hc) t cs μ μ (inv_du μ i) rfl
      (relation D Sc (.invP₃ i μ m hm)) = 0 := by
  classical
  simp only [relation, psiLin_dg]
  rw [psiRaw_append t cs μ μ (lcrossL i i) (epsL i m) (inv_du μ i) (inv_ud μ i) rfl (sChain_lcrossL i i)
    (sChain_epsL i m)]
  simp only [invRaw_sameLCross, invRaw_eps]
  exact psi_invP₄ cs t ht μ i m hm

/-- The `invP₄` matrix relation belongs to the kernel of the linear evaluation. -/
theorem psiLin_invP₄ (t : k) (cs : CScalars Sc)
    (μ : X) (i : I) (n : ℕ) (hn : (n : ℤ) < D.h i μ) :
    psiLin (sy := sy) (hc := hc) t cs μ μ rfl (inv_du μ i)
      (relation D Sc (.invP₄ i μ n hn)) = 0 := by
  classical
  simp only [relation, psiLin_dg]
  rw [psiRaw_append t cs μ μ (dcupL i n) (sigmaL i i) rfl (inv_ud μ i) (inv_du μ i) (sChain_dcupL i n)
    (sChain_sigmaL i i)]
  simp only [invRaw_dcup, invRaw_sameSigma]
  exact psi_invP₃ cs t μ i n

/-- The `invP₅` matrix relation belongs to the kernel of the linear evaluation. -/
theorem psiLin_invP₅ (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) (m n : ℕ) (hm : (m : ℤ) < D.h i μ) (hn : (n : ℤ) < D.h i μ) :
    psiLin (sy := sy) (hc := hc) t cs μ μ rfl rfl
      (relation D Sc (.invP₅ i μ m n hm hn)) = 0 := by
  classical
  simp only [relation, map_sub, psiLin_dg]
  rw [psiRaw_append t cs μ μ (dcupL i n) (epsL i m) rfl (inv_ud μ i) rfl (sChain_dcupL i n) (sChain_epsL i m)]
  simp only [invRaw_dcup, invRaw_eps]
  rw [psi_invP₅ cs t ht μ i m n hm hn]
  split_ifs
  · erw [psiLin_idg t cs μ μ [] rfl]
    exact sub_self _
  · rw [map_zero, sub_self]

/-- The `invM₁` matrix relation belongs to the kernel of the linear evaluation. -/
theorem psiLin_invM₁ (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) (hh : D.h i μ ≤ 0) :
    psiLin (sy := sy) (hc := hc) t cs μ μ (inv_du μ i) (inv_du μ i)
      (relation D Sc (.invM₁ i μ hh)) = 0 := by
  classical
  simp only [relation, map_sub, map_add, map_neg, map_sum, psiLin_dg, psiLin_idg]
  rw [psiRaw_append t cs μ μ (lcrossL i i) (sigmaL i i) (inv_du μ i) (inv_ud μ i)
    (inv_du μ i) (sChain_lcrossL i i) (sChain_sigmaL i i)]
  simp only [invRaw_sameLCross, invRaw_sameSigma]
  have hj (r : ℕ) := psiRaw_append (sy := sy) (hc := hc) t cs μ μ (dcapL i r) (etaL i r)
    (inv_du μ i) rfl (inv_du μ i) (sChain_dcapL i r) (sChain_etaL i r)
  simp_rw [hj]
  simp only [invRaw_dcap, invRaw_eta]
  exact sub_eq_zero.mpr (psi_invM₁ cs t ht μ i hh)

/-- The `invM₂` matrix relation belongs to the kernel of the linear evaluation. -/
theorem psiLin_invM₂ (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) (hh : D.h i μ ≤ 0) :
    psiLin (sy := sy) (hc := hc) t cs μ μ (inv_ud μ i) (inv_ud μ i)
      (relation D Sc (.invM₂ i μ hh)) = 0 := by
  classical
  simp only [relation, map_add, psiLin_dg, psiLin_idg]
  rw [psiRaw_append t cs μ μ (sigmaL i i) (lcrossL i i) (inv_ud μ i) (inv_du μ i)
    (inv_ud μ i) (sChain_sigmaL i i) (sChain_lcrossL i i)]
  simp only [invRaw_sameSigma, invRaw_sameLCross]
  rw [psi_invM₂ t ht μ i hh, neg_add_cancel]

/-- The `invM₃` matrix relation belongs to the kernel of the linear evaluation. -/
theorem psiLin_invM₃ (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) (m : ℕ) (hm : (m : ℤ) < -D.h i μ) :
    psiLin (sy := sy) (hc := hc) t cs μ μ rfl (inv_ud μ i)
      (relation D Sc (.invM₃ i μ m hm)) = 0 := by
  classical
  simp only [relation, psiLin_dg]
  rw [psiRaw_append t cs μ μ (etaL i m) (lcrossL i i) rfl (inv_du μ i) (inv_ud μ i) (sChain_etaL i m)
    (sChain_lcrossL i i)]
  simp only [invRaw_eta, invRaw_sameLCross]
  exact psi_invM₄ cs t ht μ i m hm

/-- The `invM₄` matrix relation belongs to the kernel of the linear evaluation. -/
theorem psiLin_invM₄ (t : k) (cs : CScalars Sc)
    (μ : X) (i : I) (n : ℕ) (hn : (n : ℤ) < -D.h i μ) :
    psiLin (sy := sy) (hc := hc) t cs μ μ (inv_ud μ i) rfl
      (relation D Sc (.invM₄ i μ n hn)) = 0 := by
  classical
  simp only [relation, psiLin_dg]
  rw [psiRaw_append t cs μ μ (sigmaL i i) (dcapL i n) (inv_ud μ i) (inv_du μ i) rfl (sChain_sigmaL i i)
    (sChain_dcapL i n)]
  simp only [invRaw_sameSigma, invRaw_dcap]
  exact psi_invM₃ cs t μ i n

/-- The `invM₅` matrix relation belongs to the kernel of the linear evaluation. -/
theorem psiLin_invM₅ (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) (m n : ℕ) (hm : (m : ℤ) < -D.h i μ) (hn : (n : ℤ) < -D.h i μ) :
    psiLin (sy := sy) (hc := hc) t cs μ μ rfl rfl
      (relation D Sc (.invM₅ i μ m n hm hn)) = 0 := by
  classical
  simp only [relation, map_sub, psiLin_dg]
  rw [psiRaw_append t cs μ μ (etaL i m) (dcapL i n) rfl (inv_du μ i) rfl (sChain_etaL i m) (sChain_dcapL i n)]
  simp only [invRaw_eta, invRaw_dcap]
  rw [psi_invM₅ cs t ht μ i m n hm hn]
  split_ifs
  · erw [psiLin_idg t cs μ μ [] rfl]
    exact sub_self _
  · rw [map_zero, sub_self]

/-- The inversion constructors (1.12)–(1.14), including the presentation's
zero conventions for matrix entries outside their allowed ranges. -/
def Rel.IsInversion : Rel D → Prop
  | .invNe₁ .. | .invNe₂ .. | .invP₁ .. | .invP₂ .. | .invP₃ .. | .invP₄ ..
  | .invP₅ .. | .invM₁ .. | .invM₂ .. | .invM₃ .. | .invM₄ .. | .invM₅ ..
  | .dcupZero .. | .dcapZero .. => True
  | _ => False

private theorem invLin_weight (t : k) (cs : CScalars Sc) (ν ν' μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (hs' : wt D μ s = ν') (hr' : wt D μ r = ν') (e : ν = ν')
    (f : LinDiagram k (ob D μ s) (ob D μ r))
    (hf : psiLin (sy := sy) (hc := hc) t cs ν' μ hs' hr' f = 0) :
    psiLin (sy := sy) (hc := hc) t cs ν μ hs hr f = 0 := by
  cases e
  exact hf

/-- Inversion-family kernel inclusion for the seven-shape evaluator on the
free linear presentation, at any valid choice of left weight. -/
theorem psiLin_inversion (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (R : Rel D) (hR : R.IsInversion) (ν : X)
    (hs : wt D R.ν R.dom = ν) (hr : wt D R.ν R.cod = ν) :
    psiLin (sy := sy) (hc := hc) t cs ν R.ν hs hr (relation D Sc R) = 0 := by
  cases R with
  | invNe₁ i j μ hij =>
    exact invLin_weight t cs ν (wt D μ [up j, dn i]) μ hs hr rfl rfl hs.symm _
      (psiLin_invNe₁ t ht cs μ i j hij)
  | invNe₂ i j μ hij =>
    have e : ν = wt D μ [up j, dn i] := hs.symm.trans ((sChain_sigmaL i j).wt_eq D μ)
    exact invLin_weight t cs ν (wt D μ [up j, dn i]) μ hs hr _ _ e _
      (psiLin_invNe₂ t ht cs μ i j hij)
  | invP₁ i μ hh =>
    have e : ν = μ := hs.symm.trans (inv_ud μ i)
    exact invLin_weight t cs ν μ μ hs hr _ _ e _ (psiLin_invP₁ t ht cs μ i hh)
  | invP₂ i μ hh =>
    have e : ν = μ := hs.symm.trans (inv_du μ i)
    exact invLin_weight t cs ν μ μ hs hr _ _ e _ (psiLin_invP₂ t ht cs μ i hh)
  | invP₃ i μ m hm =>
    have e : ν = μ := hs.symm.trans (inv_du μ i)
    exact invLin_weight t cs ν μ μ hs hr _ _ e _ (psiLin_invP₃ t ht cs μ i m hm)
  | invP₄ i μ n hn =>
    have e : ν = μ := hs.symm
    exact invLin_weight t cs ν μ μ hs hr _ _ e _ (psiLin_invP₄ t cs μ i n hn)
  | invP₅ i μ m n hm hn =>
    have e : ν = μ := hs.symm
    exact invLin_weight t cs ν μ μ hs hr _ _ e _ (psiLin_invP₅ t ht cs μ i m n hm hn)
  | invM₁ i μ hh =>
    have e : ν = μ := hs.symm.trans (inv_du μ i)
    exact invLin_weight t cs ν μ μ hs hr _ _ e _ (psiLin_invM₁ t ht cs μ i hh)
  | invM₂ i μ hh =>
    have e : ν = μ := hs.symm.trans (inv_ud μ i)
    exact invLin_weight t cs ν μ μ hs hr _ _ e _ (psiLin_invM₂ t ht cs μ i hh)
  | invM₃ i μ m hm =>
    have e : ν = μ := hs.symm
    exact invLin_weight t cs ν μ μ hs hr _ _ e _ (psiLin_invM₃ t ht cs μ i m hm)
  | invM₄ i μ n hn =>
    have e : ν = μ := hs.symm.trans (inv_ud μ i)
    exact invLin_weight t cs ν μ μ hs hr _ _ e _ (psiLin_invM₄ t cs μ i n hn)
  | invM₅ i μ m n hm hn =>
    have e : ν = μ := hs.symm
    exact invLin_weight t cs ν μ μ hs hr _ _ e _ (psiLin_invM₅ t ht cs μ i m n hm hn)
  | dcupZero i μ n hn =>
    have e : ν = μ := hs.symm
    exact invLin_weight t cs ν μ μ hs hr _ _ e _ (psiLin_dcupZero t cs μ i n hn)
  | dcapZero i μ n hn =>
    have e : ν = μ := hs.symm.trans (inv_du μ i)
    exact invLin_weight t cs ν μ μ hs hr _ _ e _ (psiLin_dcapZero t cs μ i n hn)
  | _ => exact False.elim hR

/-- Inversion relations still evaluate to zero between arbitrary linear
pre- and post-compositions. This is the vertical-context slice used by descent. -/
theorem psiLin_inversion_context (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (R : Rel D) (hR : R.IsInversion) (ν : X)
    (hs : wt D R.ν R.dom = ν) (hr : wt D R.ν R.cod = ν)
    {a b : List (Letter I)} (ha : wt D R.ν a = ν) (hb : wt D R.ν b = ν)
    (f : LinDiagram k (ob D R.ν a) (ob D R.ν R.dom))
    (g : LinDiagram k (ob D R.ν R.cod) (ob D R.ν b)) :
    psiLin (sy := sy) (hc := hc) t cs ν R.ν ha hb (f ≫ relation D Sc R ≫ g) = 0 := by
  rw [psiLin_comp t cs ν R.ν ha hs hb,
    psiLin_comp t cs ν R.ν hs hr hb, psiLin_inversion t ht cs R hR ν hs hr]
  simp

end OddMath.SKM
