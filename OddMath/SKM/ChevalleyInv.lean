/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyRel

/-!
# The Chevalley involution is an involution (Brundan–Ellis, Proposition 3.5)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 3.5:
`ω² = id`. Applying `ω` twice to a generator gives back the generator (the double image of the
upward dot is straightened by (2.3) and (1.10), that of the upward crossing by (2.5), (2.4) and
(1.10)), so `ω ∘ ω` is the identity on every normal-form diagram.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation Supercategory

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

/-! ## `omegaL` and whiskering -/

theorem omegaL_map_whL (u v : List (Letter I)) (A : List (LayerData I)) :
    omegaL (A.map (whL u v)) = (omegaL A).map (whL (flipW u) (flipW v)) := by
  induction A with
  | nil => rfl
  | cons x A ih =>
    obtain ⟨a, g, b⟩ := x
    simp [ih, whL, List.map_map, Function.comp_def]

theorem omegaC_map_whL (u v : List (Letter I)) (A : List (LayerData I)) :
    omegaC D k (A.map (whL u v)) = omegaC D k A := by
  induction A with
  | nil => rfl
  | cons x A ih =>
    obtain ⟨a, g, b⟩ := x
    simp [ih, whL]

theorem parsum_omegaL (L : List (LayerData I)) : parsum D (omegaL L) = parsum D L := by
  induction L with
  | nil => rfl
  | cons x L ih => simp [parsum_append, ih, parsum_chevL, add_comm]

/-! ## Double images of the generators -/

theorem omegaL_ddotL (i : I) :
    omegaL (ddotL i) = [([up i], Shape.cup i, [])] ++ (ddotsL i 1).map (whL [up i] [up i]) ++
      [([], Shape.cap i, [up i])] := by
  simp only [ddotL, mateL, omegaL_append, omegaL_map_whL, omegaL_dotsL, omegaL_cons, omegaL_nil,
    chevL, List.nil_append, flipW_cons, flipW_nil, flipL_dn, map_whL_map_whL, List.map_cons,
    List.map_nil]
  rfl

variable (Sc) in
/-- The double image of the upward dot is the upward dot, by (2.3) and (1.10). -/
theorem cl_omegaL_ddotL (μ : X) (i : I) :
    cl D Sc μ [up i] [up i] (omegaL (ddotL i)) = cl D Sc μ [up i] [up i] (dotsL [] i [] 1) := by
  rw [omegaL_ddotL]
  have E := eq_2_3_a' (Sc := Sc) i (wt D μ []) 1
  simp only [show (1 / 2 : ℕ) = 0 from rfl, Nat.cast_zero, mul_zero, zsign_zero, one_smul] at E
  have h1 := cl_step (D := D) (Sc := Sc) μ (s₀ := [up i]) (t₀ := [up i]) []
    [([], Shape.cap i, [up i])] [up i] [] E (by simp) ⟨by simp [Shape.dom], rfl⟩
    (L := [([up i], Shape.cup i, [])] ++ (ddotsL i 1).map (whL [up i] [up i]) ++
      [([], Shape.cap i, [up i])])
    (L' := [] ++ ([([], Shape.cup i, [])] ++ (dotsL [] i [] 1).map (whL [dn i] [])).map
      (whL [up i] []) ++ [([], Shape.cap i, [up i])])
    (by simp [whL]) rfl
  rw [h1]
  have h2 := (cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := [up i]) (T := [up i])
    [([up i], Shape.cup i, [])] [] [] [] [] (A := [([], Shape.cap i, [])])
    (s := [up i, dn i]) (s' := []) ⟨rfl, rfl⟩ (sChain_dotsL [] i [] 1)
    (Or.inl (by simp [parsum, Shape.parity]))).symm
  simp [whL] at h2 ⊢
  rw [h2]
  exact cl_step (D := D) (Sc := Sc) μ [] (dotsL [] i [] 1) [] [] (cl_zigE Sc i (wt D μ []))
    (by simp) (by simpa using sChain_dotsL [] i [] 1) (by simp [whL, dotsL]) (by simp)

theorem omegaL_dcrossL (j i : I) :
    omegaL (dcrossL j i) = [([up i, up j], Shape.cup i, [])] ++
      (omegaSigma j i).map (whL [up i] [up i]) ++ [([], Shape.cap i, [up j, up i])] := by
  simp only [dcrossL, omegaL_append, omegaL_map_whL, omegaL_sigmaL, omegaL_cons, omegaL_nil,
    chevL, List.nil_append, flipW_cons, flipW_nil, flipL_dn, List.map_cons, List.map_nil]
  rfl

variable (Sc) in
/-- The double image of the upward crossing is the upward crossing, by (2.5), (2.4) and
(1.10). -/
theorem cl_omegaL_dcrossL (μ : X) (i j : I) :
    cl D Sc μ [up i, up j] [up j, up i] (omegaL (dcrossL j i)) =
      cl D Sc μ [up i, up j] [up j, up i] (crossL [] i j []) := by
  rw [omegaL_dcrossL]
  have h1 := cl_step (D := D) (Sc := Sc) μ (s₀ := [up i, up j]) (t₀ := [up j, up i])
    [([up i, up j], Shape.cup i, [])] [([], Shape.cap i, [up j, up i])] [up i] [up i]
    (cl_omegaSigma Sc (wt D μ [up i]) j i) ⟨rfl, by simp [Shape.cod]⟩ ⟨by simp [Shape.dom], rfl⟩
    (L := [([up i, up j], Shape.cup i, [])] ++ (omegaSigma j i).map (whL [up i] [up i]) ++
      [([], Shape.cap i, [up j, up i])]) rfl rfl
  rw [h1]
  have h2 := cl_step (D := D) (Sc := Sc) μ (s₀ := [up i, up j]) (t₀ := [up j, up i])
    [] [([], Shape.cap i, [up j, up i])] [up i] [] (eq_2_4_b Sc i j (wt D μ [])) (by simp)
    ⟨by simp [Shape.dom], rfl⟩
    (L := [([up i, up j], Shape.cup i, [])] ++ (sigmaL i j).map (whL [up i] [up i]) ++
      [([], Shape.cap i, [up j, up i])])
    (L' := [] ++ [([], Shape.cup i, [up j]), ([dn i], Shape.cross i j, [])].map (whL [up i] []) ++
      [([], Shape.cap i, [up j, up i])])
    (by simp [whL]) rfl
  rw [h2]
  have h3 := (cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := [up i, up j]) (T := [up j, up i])
    [([up i], Shape.cup i, [up j])] [] [] [] [] (A := [([], Shape.cap i, [])])
    (B := [([], Shape.cross i j, [])]) (s := [up i, dn i]) (s' := []) (t := [up i, up j])
    (t' := [up j, up i]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (Or.inl (by simp [parsum, Shape.parity]))).symm
  simp [whL] at h3 ⊢
  rw [h3]
  exact cl_step (D := D) (Sc := Sc) μ [] [([], Shape.cross i j, [])] [] [up j]
    (cl_zigE Sc i (wt D μ [up j])) (by simp) ⟨by simp [Shape.dom], rfl⟩ (by simp [whL])
    (by simp [crossL])

variable (Sc) in
/-- The double image of a generator is the generator (layers). -/
theorem cl_omegaL_chevL (ν : X) (g : Shape I) :
    cl D Sc ν g.dom g.cod (omegaL (chevL g)) = cl D Sc ν g.dom g.cod [([], g, [])] := by
  cases g with
  | dot i => exact cl_omegaL_ddotL Sc ν i
  | cross i j => exact cl_omegaL_dcrossL Sc ν i j
  | cup i => simp [chevL]
  | cap i => simp [chevL]
  | lcross i j => simp [chevL, lcrossL]
  | dcup i n => simp [chevL, dcapL, dcupL]
  | dcap i n => simp [chevL, dcapL, dcupL]

/-- The double image of a generator is the generator (scalars). -/
theorem chevC_mul_omegaC (g : Shape I) : chevC D k g * omegaC D k (chevL g) = 1 := by
  cases g with
  | dot i =>
    simp [chevC, chevL, ddotL, mateL, omegaC_append, omegaC_map_whL, omegaC_dotsL, parsum_append,
      parsum_dotsL, Shape.parity, zsign_zero]
  | cross i j =>
    simp only [chevC, chevL, dcrossL, omegaC_append, omegaC_map_whL, omegaC_sigmaL, parsum_append,
      parsum_map_whL, parsum_sigmaL, omegaC_cons, omegaC_nil, parsum_cons, parsum_nil,
      Shape.parity]
    generalize D.parity i = a; generalize D.parity j = b
    fin_cases a <;> fin_cases b <;> simp (config := {decide := true}) [zsign]
  | cup i => simp [chevC, chevL, zsign_zero]
  | cap i => simp [chevC, chevL, zsign_zero]
  | lcross i j => simp [chevC, chevL, lcrossL, zsign_zero]
  | dcup i n =>
    simp only [chevC, chevL, dcapL, omegaC_cons, omegaC_nil, parsum_nil, mul_zero, zsign_zero,
      one_mul, mul_one]
    exact zsign_mul_self _
  | dcap i n =>
    simp only [chevC, chevL, dcupL, omegaC_cons, omegaC_nil, parsum_nil, mul_zero, zsign_zero,
      one_mul, mul_one]
    exact zsign_mul_self _

theorem omegaC_omegaL (L : List (LayerData I)) : omegaC D k L * omegaC D k (omegaL L) = 1 := by
  induction L with
  | nil => simp
  | cons x L ih =>
    obtain ⟨u, g, v⟩ := x
    simp only [omegaC_cons, omegaL_cons, omegaC_append, parsum_omegaL, parsum_map_whL,
      parsum_chevL, omegaC_map_whL]
    have hz := zsign_mul_self (k := k) (g.parity D * parsum D L)
    have hc := chevC_mul_omegaC (D := D) (k := k) g
    rw [mul_comm (parsum D L)]
    linear_combination (chevC D k g * omegaC D k (chevL g) * omegaC D k L *
      omegaC D k (omegaL L)) * hz + (omegaC D k L * omegaC D k (omegaL L)) * hc + ih

/-- `ω ∘ ω` on the layers of a normal-form diagram. -/
theorem cl_omegaL_omegaL (μ : X) {s t : List (Letter I)} {L : List (LayerData I)}
    (h : SChain s L t) : cl D Sc μ s t (omegaL (omegaL L)) = cl D Sc μ s t L := by
  induction L generalizing s with
  | nil =>
    obtain rfl : s = t := h
    rfl
  | cons x L ih =>
    obtain ⟨u, g, v⟩ := x
    obtain ⟨rfl, h2⟩ := h
    have e : omegaL (omegaL ((u, g, v) :: L)) =
        (omegaL (chevL g)).map (whL u v) ++ omegaL (omegaL L) := by
      simp [omegaL_map_whL]
    rw [e]
    have hA : SChain (u ++ g.dom ++ v) ((omegaL (chevL g)).map (whL u v)) (u ++ g.cod ++ v) := by
      simpa using (sChain_omegaL (sChain_chevL g)).whisk u v
    have hB : SChain (u ++ g.cod ++ v) (omegaL (omegaL L)) t := by
      simpa using sChain_omegaL (sChain_omegaL h2)
    rw [← cl_comp hA hB, ih h2]
    have hg := cl_step (D := D) (Sc := Sc) μ (s₀ := u ++ g.dom ++ v) (t₀ := u ++ g.cod ++ v) [] []
      u v (cl_omegaL_chevL Sc (wt D μ v) g) (by simp) (by simp)
      (L := (omegaL (chevL g)).map (whL u v)) (L' := [(u, g, v)]) (by simp) (by simp [whL])
    rw [hg, cl_comp (show SChain (u ++ g.dom ++ v) [(u, g, v)] (u ++ g.cod ++ v) from ⟨rfl, rfl⟩) h2]
    rfl

/-! ## `ω² = id` -/

theorem chevMap_chevMap_ob (μ : X) (t : List (Letter I)) :
    (chevMap D).obj ((chevMap D).obj (ob D μ t)) = ob D μ t := by
  rw [chevMap_obj, chevMap_obj, neg_neg, flipW_flipW]

theorem cl_congr_all {μ μ' : X} {s t s' t' : List (Letter I)} (L : List (LayerData I))
    (hμ : μ = μ') (hs : s = s') (ht : t = t') :
    cl D Sc μ s t L = eqToHom (by rw [hμ, hs]) ≫ cl D Sc μ' s' t' L ≫ eqToHom (by rw [hμ, ht]) := by
  subst hμ hs ht; simp

set_option backward.isDefEq.respectTransparency false in
/-- **Brundan–Ellis, Proposition 3.5: `ω² = id`** on every normal-form diagram (`ω` applied twice,
read through the two super-opposites). -/
theorem omega_omega_cl (μ : X) {s t : List (Letter I)} {L : List (LayerData I)} (h : SChain s L t) :
    SOp.unsop ((omega Sc).map (SOp.unsop ((omega Sc).map (cl D Sc μ s t L)))) =
      eqToHom (congrArg (pres D Sc).obj (chevMap_chevMap_ob μ s)) ≫ cl D Sc μ s t L ≫
        eqToHom (congrArg (pres D Sc).obj (chevMap_chevMap_ob μ t)).symm := by
  rw [omega_cl μ h, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map,
    Functor.map_smul, SOpMap.unsop_eqToHom_comp, SOpMap.unsop_comp_eqToHom, SOp.unsop_smul,
    omega_cl (-μ) (sChain_omegaL h), cl_congr_all _ (neg_neg μ) (flipW_flipW s) (flipW_flipW t),
    cl_omegaL_omegaL μ h]
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc, omegaC_omegaL, one_smul]

/-! ## Every diagram between the objects `E_s 1_μ` is in normal form -/

theorem wd_map_l (μ : X) (t : List (Letter I)) : (wd D μ t).map Col.l = t := by
  induction t with
  | nil => rfl
  | cons l t ih => simp [ih]

theorem ob_injective {μ : X} {s t : List (Letter I)} (h : ob D μ s = ob D μ t) : s = t := by
  have := congrArg (fun a : Obj (sig D) => a.word.map Col.l) h
  simpa [ob, wd_map_l] using this

/-- A well-formed word of colours is the word of its letters. -/
theorem word_eq_wd : ∀ (r : X) (w : List (Col I X)), (sig D).ok r w →
    w = wd D ((sig D).endR r w) (w.map Col.l) ∧ r = wt D ((sig D).endR r w) (w.map Col.l)
  | r, [], _ => ⟨rfl, rfl⟩
  | r, c :: w, h => by
    obtain ⟨hc, hw⟩ := h
    obtain ⟨h1, h2⟩ := word_eq_wd c.r w hw
    refine ⟨?_, ?_⟩
    · show c :: w = ⟨c.l, wt D ((sig D).endR c.r w) (w.map Col.l)⟩ ::
        wd D ((sig D).endR c.r w) (w.map Col.l)
      rw [← h2, ← h1]
    · show r = sh D c.l + wt D ((sig D).endR c.r w) (w.map Col.l)
      rw [← h2]; exact hc.symm

/-- A valid layer with bottom boundary `E_s 1_μ` is a normal-form layer. -/
theorem layer_eq_lay {μ : X} {s : List (Letter I)} {L : Layer (sig D)} (hv : L.Valid)
    (hd : L.dom = ob D μ s) :
    ∃ u g v, L = lay D μ u g v ∧ s = u ++ g.dom ++ v := by
  obtain ⟨start, left, ⟨g, ν⟩, right⟩ := L
  have hend : (sig D).endR ν right = μ := by
    have h := hv.endR_dom
    rw [hd] at h
    exact (h.symm.trans (endR_wd D μ s) :)
  obtain ⟨hr, hν⟩ := word_eq_wd (D := D) ν right hv.right_ok
  rw [hend] at hr hν
  set v := right.map Col.l
  have hlend : (sig D).endR start left = wt D μ (g.dom ++ v) := by
    rw [hv.left_end]; show wt D ν g.dom = _; rw [wt_append, ← hν]
  obtain ⟨hl, hs⟩ := word_eq_wd (D := D) start left hv.left_ok
  rw [hlend] at hl hs
  set u := left.map Col.l
  have hL : (⟨start, left, (g, ν), right⟩ : Layer (sig D)) = lay D μ u g v := by
    refine Layer.ext ?_ hl ?_ hr
    · show start = wt D μ (u ++ g.dom ++ v)
      rw [hs, List.append_assoc, wt_append D μ u]
    · show (g, ν) = (g, wt D μ v); rw [hν]
  refine ⟨u, g, v, hL, ?_⟩
  rw [hL, lay_dom] at hd
  exact (ob_injective hd).symm

/-- A chain of layers between `E_s 1_μ` and `E_t 1_μ` is in normal form. -/
theorem chain_eq_layList (μ : X) : ∀ (ls : List (Layer (sig D))) (s t : List (Letter I)),
    Chain (ob D μ s) ls (ob D μ t) → ∃ L, SChain s L t ∧ ls = layList D μ L
  | [], s, t, h => ⟨[], ob_injective h, rfl⟩
  | L :: ls, s, t, h => by
    obtain ⟨hv, hd, hc⟩ := h
    obtain ⟨u, g, v, rfl, rfl⟩ := layer_eq_lay hv hd
    rw [lay_cod] at hc
    obtain ⟨M, hM, rfl⟩ := chain_eq_layList μ ls _ t hc
    exact ⟨(u, g, v) :: M, ⟨rfl, hM⟩, rfl⟩

/-- Every diagram from `E_s 1_μ` to `E_t 1_μ` is a normal-form diagram. -/
theorem diag_eq_mkD {μ : X} {s t : List (Letter I)} (d : ob D μ s ⟶ ob D μ t) :
    ∃ L, ∃ h : SChain s L t, d = mkD D μ L h := by
  obtain ⟨ls, hc⟩ := d
  obtain ⟨L, hL, rfl⟩ := chain_eq_layList μ ls s t hc
  exact ⟨L, hL, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Brundan–Ellis, Proposition 3.5: `ω² = id`**: `ω` applied twice (read through the two
super-opposites) is the identity on every 2-morphism of `𝔘(𝔤)`. -/
theorem omega_omega {μ : X} {s t : List (Letter I)}
    (f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :
    SOp.unsop ((omega Sc).map (SOp.unsop ((omega Sc).map f))) =
      eqToHom (congrArg (pres D Sc).obj (chevMap_chevMap_ob μ s)) ≫ f ≫
        eqToHom (congrArg (pres D Sc).obj (chevMap_chevMap_ob μ t)).symm := by
  obtain ⟨g, rfl⟩ := (pres D Sc).lin_surjective f
  induction g using Finsupp.induction_linear with
  | zero =>
    simp only [Presentation.lin_zero, Functor.map_zero, SOp.unsop_zero, Limits.zero_comp,
      Limits.comp_zero]
  | add f₁ f₂ h₁ h₂ =>
    erw [Presentation.lin_add]
    simp only [Functor.map_add, SOp.unsop_add, h₁, h₂, Preadditive.add_comp, Preadditive.comp_add]
  | single d r =>
    obtain ⟨L, hL, rfl⟩ := diag_eq_mkD d
    rw [show (Finsupp.single (mkD D μ L hL) r : LinDiagram k _ _) = r • dg D μ L hL from
      (Finsupp.smul_single_one _ r).symm, Presentation.lin_smul, lin_dg hL, Functor.map_smul,
      SOp.unsop_smul, Functor.map_smul, SOp.unsop_smul, omega_omega_cl μ hL]
    simp only [Linear.smul_comp, Linear.comp_smul]

end OddMath.SKM
