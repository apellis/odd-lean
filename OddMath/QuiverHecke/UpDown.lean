/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.SplitFactorization
import OddMath.QuiverHecke.CornerImages
import OddMath.QuiverHecke.AlphaPrime
import OddMath.SKM.GradedExpansion

/-!
# Upward and downward placements on `E_𝐢 F_𝐢′ 1_λ`

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity, top step of the width
induction. An endomorphism `x` of `E_s` in `H` acts on `E_s F_t 1_λ` through the upward map
`α` of (11.7), on the left block of strands (`upE`); an endomorphism `y` of `E_t` acts through
`ω ∘ α`, the downward map of (11.8), on the right block (`dnE`). The upward placement is
multiplicative, the downward one reverses products up to the Koszul sign, and the products of
split diagrams of `SplitFactorization` are the products `dnE y * upE x`.

The downward placement is written at the weight `-ν` with `α` at `ν`, so that the weight of the
Chevalley involution needs no cast; this is `α′_{-ν}` of (11.8).

* `upE`, `upE_mul`, `upE_one`, `upE_hD`.
* `dnE`, `dnE_mul`, `dnE_one`, `dnE_hD`.
* `cl_udLayers`: a split product is `c • (dnE y * upE x)`.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams GradedWalk
open QuiverHecke (upWord upLayers alpha)

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  (Sc : Scalars D k)

/-- The object `E_s` of `H`. -/
abbrev hO (s : List I) : QuiverHecke.H D Sc := (QuiverHecke.pres D Sc).obj (QuiverHecke.ob D s)

/-- The diagram of a chain of layers of `H`. -/
abbrev hD {s t : List I} (M : List (QuiverHecke.LayerData I)) (h : QuiverHecke.SChain s M t) :
    hO Sc s ⟶ hO Sc t :=
  (QuiverHecke.pres D Sc).diag (QuiverHecke.mkD D M h)

theorem alpha_hD (μ : X) {s t : List I} (M : List (QuiverHecke.LayerData I))
    (h : QuiverHecke.SChain s M t) :
    (alpha D Sc μ).map (hD Sc M h) = cl D Sc μ (upWord s) (upWord t) (upLayers M) := by
  rw [QuiverHecke.alpha_diag, QuiverHecke.label_mkD, cl_of]

/-! ## The upward placement -/

/-- **The upward placement**: `x ∈ End(E_s)` acts by `α(x)` on the left block of `E_s V 1_μ`. -/
def upE (μ : X) (s : List I) (V : List (Letter I)) :
    End (hO Sc s) →ₗ[k] End ((pres D Sc).obj (ob D μ (upWord s ++ V))) where
  toFun x := plcL D Sc μ [] V (upWord s) (upWord s) ((alpha D Sc (wt D μ V)).map x)
  map_add' x y := by rw [Functor.map_add, map_add]
  map_smul' r x := by rw [Functor.map_smul, map_smul]; rfl

theorem upE_apply (μ : X) (s : List I) (V : List (Letter I)) (x : End (hO Sc s)) :
    upE Sc μ s V x = plcL D Sc μ [] V (upWord s) (upWord s) ((alpha D Sc (wt D μ V)).map x) :=
  rfl

theorem upE_mul (μ : X) (s : List I) (V : List (Letter I)) (x y : End (hO Sc s)) :
    upE Sc μ s V (x * y) = upE Sc μ s V x * upE Sc μ s V y := by
  change plcL D Sc μ [] V _ _ ((alpha D Sc (wt D μ V)).map (y ≫ x)) =
    plcL D Sc μ [] V _ _ ((alpha D Sc (wt D μ V)).map y) ≫
      plcL D Sc μ [] V _ _ ((alpha D Sc (wt D μ V)).map x)
  rw [CategoryTheory.Functor.map_comp, plcL_comp]

theorem upE_one (μ : X) (s : List I) (V : List (Letter I)) : upE Sc μ s V 1 = 1 := by
  change plcL D Sc μ [] V (upWord s) (upWord s) ((alpha D Sc (wt D μ V)).map (𝟙 (hO Sc s))) =
    𝟙 _
  erw [CategoryTheory.Functor.map_id, plcL_id]

theorem upE_hD (μ : X) (s : List I) (V : List (Letter I)) (M : List (QuiverHecke.LayerData I))
    (h : QuiverHecke.SChain s M s) :
    upE Sc μ s V (hD Sc M h) =
      cl D Sc μ (upWord s ++ V) (upWord s ++ V) ((upLayers M).map (whL [] V)) := by
  rw [upE_apply, alpha_hD, plcL_cl]; rfl

/-! ## The downward placement -/

/-- The object `ω(α_ν(E_t))` is `F_t 1_{-ν}`. -/
theorem omega_alpha_obj (ν : X) (t : List I) :
    ((omega Sc).obj ((pres D Sc).obj (ob D ν (upWord t)))).unop =
      (pres D Sc).obj (ob D (-ν) (dnWord t)) :=
  congrArg SOp.unop (omega_obj (Sc := Sc) ν (upWord t))

/-- `y ∈ End(E_t)` acts on `F_t 1_{-ν}` by `ω(α_ν(y))`. -/
def dnE₀ (ν : X) (t : List I) :
    End (hO Sc t) →ₗ[k] End ((pres D Sc).obj (ob D (-ν) (dnWord t))) where
  toFun y := eqToHom (omega_alpha_obj Sc ν t).symm ≫
    SOp.unsop ((omega Sc).map ((alpha D Sc ν).map y)) ≫ eqToHom (omega_alpha_obj Sc ν t)
  map_add' x y := by
    rw [Functor.map_add, Functor.map_add, SOp.unsop_add, Preadditive.add_comp,
      Preadditive.comp_add]
  map_smul' r x := by
    rw [Functor.map_smul, Functor.map_smul, SOp.unsop_smul, Linear.smul_comp,
      Linear.comp_smul]; rfl

theorem dnE₀_apply (ν : X) (t : List I) (y : End (hO Sc t)) :
    dnE₀ Sc ν t y = eqToHom (omega_alpha_obj Sc ν t).symm ≫
      SOp.unsop ((omega Sc).map ((alpha D Sc ν).map y)) ≫ eqToHom (omega_alpha_obj Sc ν t) :=
  rfl

theorem sign_mul_smul {M : Type*} [AddCommGroup M] [Module k M] (p q : ZMod 2) (m : M) :
    Supercategory.sign k (p * q) • m = ksign p q • m := by
  rw [← Int.cast_smul_eq_zsmul k]
  congr 1
  fin_cases p <;> fin_cases q <;> simp [ksign]

theorem unsop_omega_alpha_mem (ν : X) {t : List I} {p : ZMod 2} {x : End (hO Sc t)}
    (hx : x ∈ Supercategory.parity (R := k) (hO Sc t) (hO Sc t) p) :
    SOp.unsop ((omega Sc).map ((alpha D Sc ν).map x)) ∈
      Supercategory.parity (R := k) ((omega Sc).obj ((pres D Sc).obj (ob D ν (upWord t)))).unop
        ((omega Sc).obj ((pres D Sc).obj (ob D ν (upWord t)))).unop p :=
  omega_mem (QuiverHecke.alpha_mem_parity D Sc ν hx)

theorem dnE₀_mul (ν : X) (t : List I) {p q : ZMod 2} {x y : End (hO Sc t)}
    (hx : x ∈ Supercategory.parity (R := k) (hO Sc t) (hO Sc t) p)
    (hy : y ∈ Supercategory.parity (R := k) (hO Sc t) (hO Sc t) q) :
    dnE₀ Sc ν t x * dnE₀ Sc ν t y = ksign p q • dnE₀ Sc ν t (y * x) := by
  have h := SOp.comp_of_mem (R := k) (unsop_omega_alpha_mem Sc ν hx)
    (unsop_omega_alpha_mem Sc ν hy)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp] at h
  change dnE₀ Sc ν t y ≫ dnE₀ Sc ν t x = ksign p q • dnE₀ Sc ν t (x ≫ y)
  rw [dnE₀_apply, dnE₀_apply, dnE₀_apply, h, sign_mul_smul]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Linear.smul_comp, Linear.comp_smul, smul_smul]
  rw [show ksign p q * ksign p q = 1 by
    fin_cases p <;> fin_cases q <;> decide, one_smul]

theorem dnE₀_one (ν : X) (t : List I) : dnE₀ Sc ν t 1 = 1 := by
  change eqToHom (omega_alpha_obj Sc ν t).symm ≫
    SOp.unsop ((omega Sc).map ((alpha D Sc ν).map (𝟙 (hO Sc t)))) ≫
      eqToHom (omega_alpha_obj Sc ν t) = 𝟙 _
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, SOp.unsop_id,
    Category.id_comp, eqToHom_trans, eqToHom_refl]

/-- **The downward placement**: `y ∈ End(E_t)` acts by `ω(α_ν(y))` on the right block of
`U F_t 1_{-ν}`. -/
def dnE (ν : X) (U : List (Letter I)) (t : List I) :
    End (hO Sc t) →ₗ[k] End ((pres D Sc).obj (ob D (-ν) (U ++ dnWord t))) :=
  ((wordCast (-ν) (List.append_nil _) (List.append_nil _)).comp
    (plcL D Sc (-ν) U [] (dnWord t) (dnWord t))).comp (dnE₀ Sc ν t)

theorem dnE_apply (ν : X) (U : List (Letter I)) (t : List I) (y : End (hO Sc t)) :
    dnE Sc ν U t y = wordCast (-ν) (List.append_nil _) (List.append_nil _)
      (plcL D Sc (-ν) U [] (dnWord t) (dnWord t) (dnE₀ Sc ν t y)) :=
  rfl

theorem dnE_mul' (ν : X) (U : List (Letter I)) (t : List I) (x y : End (hO Sc t)) :
    dnE Sc ν U t x * dnE Sc ν U t y = wordCast (-ν) (List.append_nil _) (List.append_nil _)
      (plcL D Sc (-ν) U [] (dnWord t) (dnWord t) (dnE₀ Sc ν t x * dnE₀ Sc ν t y)) := by
  change dnE Sc ν U t y ≫ dnE Sc ν U t x = wordCast (-ν) _ _
    (plcL D Sc (-ν) U [] (dnWord t) (dnWord t) (dnE₀ Sc ν t y ≫ dnE₀ Sc ν t x))
  rw [dnE_apply, dnE_apply, plcL_comp, wordCast_comp]

theorem dnE_mul (ν : X) (U : List (Letter I)) (t : List I) {p q : ZMod 2} {x y : End (hO Sc t)}
    (hx : x ∈ Supercategory.parity (R := k) (hO Sc t) (hO Sc t) p)
    (hy : y ∈ Supercategory.parity (R := k) (hO Sc t) (hO Sc t) q) :
    dnE Sc ν U t x * dnE Sc ν U t y = ksign p q • dnE Sc ν U t (y * x) := by
  rw [dnE_mul', dnE₀_mul Sc ν t hx hy, map_zsmul, map_zsmul, dnE_apply]

theorem dnE_one (ν : X) (U : List (Letter I)) (t : List I) : dnE Sc ν U t 1 = 1 := by
  rw [dnE_apply, dnE₀_one]
  change wordCast (-ν) _ _ (plcL D Sc (-ν) U [] (dnWord t) (dnWord t) (𝟙 _)) = 𝟙 _
  rw [plcL_id, ← cl_nil, wordCast_cl, cl_nil]

/-! ## Split products -/

theorem chevC_mul_self (g : Shape I) : chevC D k g * chevC D k g = 1 := by
  cases g <;> simp [chevC, zsign_mul_self]

theorem omegaC_mul_self (L : List (LayerData I)) : omegaC D k L * omegaC D k L = 1 := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [omegaC_cons]
    calc zsign k (x.2.1.parity D * parsum D L) * chevC D k x.2.1 * omegaC D k L *
          (zsign k (x.2.1.parity D * parsum D L) * chevC D k x.2.1 * omegaC D k L) =
        (zsign k (x.2.1.parity D * parsum D L) * zsign k (x.2.1.parity D * parsum D L)) *
          (chevC D k x.2.1 * chevC D k x.2.1) * (omegaC D k L * omegaC D k L) := by ring
      _ = 1 := by rw [zsign_mul_self, chevC_mul_self, ih, one_mul, one_mul]

theorem dnE₀_hD (ν : X) (t : List I) (N : List (QuiverHecke.LayerData I))
    (h : QuiverHecke.SChain t N t) :
    dnE₀ Sc ν t (hD Sc N h) =
      omegaC D k (upLayers N) • cl D Sc (-ν) (dnWord t) (dnWord t) (omegaL (upLayers N)) := by
  rw [dnE₀_apply]
  erw [alpha_hD Sc ν N h, omega_cl ν h.up]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Category.comp_id]

theorem dnE_hD (ν : X) (U : List (Letter I)) (t : List I) (N : List (QuiverHecke.LayerData I))
    (h : QuiverHecke.SChain t N t) :
    dnE Sc ν U t (hD Sc N h) = omegaC D k (upLayers N) •
      cl D Sc (-ν) (U ++ dnWord t) (U ++ dnWord t) ((omegaL (upLayers N)).map (whL U [])) := by
  rw [dnE_apply, dnE₀_hD, map_smul, map_smul]
  erw [plcL_cl D Sc (-ν) U [] (dnWord t) (dnWord t) (omegaL (upLayers N)), wordCast_cl]

/-- **A split product is a product of an upward and a downward placement.** -/
theorem cl_udLayers (ν : X) (s t : List I) {M N : List (QuiverHecke.LayerData I)}
    (hM : QuiverHecke.SChain s M s) (hN : QuiverHecke.SChain t N t) :
    cl D Sc (-ν) (upWord s ++ dnWord t) (upWord s ++ dnWord t)
        (udLayers (dnWord t) (upWord s) M N) =
      omegaC D k (upLayers N) •
        (dnE Sc ν (upWord s) t (hD Sc N hN) * upE Sc (-ν) s (dnWord t) (hD Sc M hM)) := by
  have h₁ := hM.up.whisk [] (dnWord t)
  have h₂ := (sChain_omegaL hN.up).whisk (upWord s) []
  simp only [List.nil_append, List.append_nil] at h₁ h₂
  rw [dnE_hD, upE_hD, smul_mul_assoc, smul_smul, omegaC_mul_self, one_smul]
  change _ = cl D Sc (-ν) _ _ _ ≫ cl D Sc (-ν) _ _ _
  rw [cl_comp h₁ h₂]
  rfl

/-! ## Parities and supercommutation -/

section Parity

theorem zsign_mul_smul {M : Type*} [AddCommGroup M] [Module k M] (p q : ZMod 2) (m : M) :
    zsign k (p * q) • m = ksign p q • m := by
  rw [← Int.cast_smul_eq_zsmul k]
  congr 1
  fin_cases p <;> fin_cases q <;> simp [ksign, zsign]

theorem wordCast_mem_homPar {μ : X} {s t s' t' : List (Letter I)} (hs : s = s') (ht : t = t')
    {p : ZMod 2} {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    (hf : f ∈ homPar D Sc μ s t p) : wordCast μ hs ht f ∈ homPar D Sc μ s' t' p := by
  subst hs ht; exact hf

theorem eqToHom_conj_mem {A B : (pres D Sc).Presented} (e : A = B) {p : ZMod 2} {f : A ⟶ A}
    (hf : f ∈ Supercategory.parity (R := k) A A p) :
    eqToHom e.symm ≫ f ≫ eqToHom e ∈ Supercategory.parity (R := k) B B p := by
  subst e; simpa using hf

variable (sy : Symmetrizer D) (cs : CScalars Sc)
include sy cs

theorem alpha_mem_homPar (μ : X) {s : List I} {p : ZMod 2} {x : End (hO Sc s)}
    (hx : x ∈ Supercategory.parity (R := k) (hO Sc s) (hO Sc s) p) :
    (alpha D Sc μ).map x ∈ homPar D Sc μ (upWord s) (upWord s) p := by
  rw [homPar_eq_homDeg sy cs]; exact QuiverHecke.alpha_mem_parity D Sc μ hx

theorem upE_mem_homPar (μ : X) (s : List I) (V : List (Letter I)) {p : ZMod 2}
    {x : End (hO Sc s)} (hx : x ∈ Supercategory.parity (R := k) (hO Sc s) (hO Sc s) p) :
    upE Sc μ s V x ∈ homPar D Sc μ (upWord s ++ V) (upWord s ++ V) p :=
  plcL_mem μ [] V (alpha_mem_homPar Sc sy cs _ hx)

theorem dnE₀_mem_homPar (ν : X) (t : List I) {p : ZMod 2} {y : End (hO Sc t)}
    (hy : y ∈ Supercategory.parity (R := k) (hO Sc t) (hO Sc t) p) :
    dnE₀ Sc ν t y ∈ homPar D Sc (-ν) (dnWord t) (dnWord t) p := by
  rw [homPar_eq_homDeg sy cs]; exact eqToHom_conj_mem Sc _ (unsop_omega_alpha_mem Sc ν hy)

theorem dnE_mem_homPar (ν : X) (U : List (Letter I)) (t : List I) {p : ZMod 2}
    {y : End (hO Sc t)} (hy : y ∈ Supercategory.parity (R := k) (hO Sc t) (hO Sc t) p) :
    dnE Sc ν U t y ∈ homPar D Sc (-ν) (U ++ dnWord t) (U ++ dnWord t) p :=
  wordCast_mem_homPar Sc _ _ (plcL_mem (-ν) U [] (dnE₀_mem_homPar Sc sy cs ν t hy))

/-- **The upward and downward placements supercommute.** -/
theorem upE_comp_dnE (ν : X) (s t : List I) {p q : ZMod 2} {x : End (hO Sc s)}
    {y : End (hO Sc t)} (hx : x ∈ Supercategory.parity (R := k) (hO Sc s) (hO Sc s) p)
    (hy : y ∈ Supercategory.parity (R := k) (hO Sc t) (hO Sc t) q) :
    upE Sc (-ν) s (dnWord t) x ≫ dnE Sc ν (upWord s) t y =
      ksign p q • (dnE Sc ν (upWord s) t y ≫ upE Sc (-ν) s (dnWord t) x) := by
  rw [← zsign_mul_smul (k := k)]
  exact plcL_interchange_hom (-ν) rfl (alpha_mem_homPar Sc sy cs _ hx)
    (dnE₀_mem_homPar Sc sy cs ν t hy)

end Parity

end OddMath.SKM
