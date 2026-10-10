/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyBase
import OddMath.SKM.Lemma33Rot
import OddMath.SKM.LeftDot
import StringDiagrams.Super.SOpPresented

/-!
# The Chevalley involution (Brundan–Ellis, Proposition 3.5): images of generators

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 3.5
(TeX label `opiso`). The images under `ω` of the generating 2-morphisms, as normal-form diagrams
at the negated weight, read in the opposite direction:

| generator | image (a 2-morphism of `𝔘(𝔤)` from the image of the top to the image of the bottom) |
|---|---|
| `x` on `Eᵢ` | the downward dot on `Fᵢ` |
| `τ : EᵢEⱼ → EⱼEᵢ` | `-(-1)^{\|i\|\|j\|}` times the downward crossing `FⱼFᵢ → FᵢFⱼ` |
| `η : 1 → FᵢEᵢ` | the rightward cap `ε : EᵢFᵢ → 1` |
| `ε : EᵢFᵢ → 1` | the rightward cup `η : 1 → FᵢEᵢ` |
| leftward crossing `FᵢEⱼ → EⱼFᵢ` | minus the leftward crossing `FⱼEᵢ → EᵢFⱼ` |
| `♦`-cup with label `n` | `(-1)^{\|i\|n}` times the `♦`-cap with label `n` |
| `♦`-cap with label `n` | `(-1)^{\|i\|n}` times the `♦`-cup with label `n` |

The first four are the values in Proposition 3.5; the last three are the values the paper lists
for the other named 2-morphisms (the inverse matrix entries are generators of our presentation).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation Supercategory

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X) {k : Type w} [CommRing k]
  (Sc : Scalars D k)

/-- The supercategory structure on the presented category of `𝔘(𝔤)` (the parity of a diagram is
the number of its odd generators). -/
instance presSupercategory : Supercategory k (pres D Sc).Presented :=
  Presentation.supercategory (isParityHomogeneous D Sc)

variable {D Sc}

theorem cl_mem (μ : X) (s t : List (Letter I)) (L : List (LayerData I)) :
    cl D Sc μ s t L ∈ parity (R := k) ((pres D Sc).obj (ob D μ s)) ((pres D Sc).obj (ob D μ t))
      (parsum D L) := by
  unfold cl
  split_ifs with h
  · exact Presentation.diag_mem_homDeg' (by rw [degree_parity_mkD]; rfl)
  · exact Submodule.zero_mem _

/-! ## Images of generators -/

/-- The layers of the image under `ω` of a generator of the given shape. -/
def chevL : Shape I → List (LayerData I)
  | .dot i => ddotL i
  | .cross i j => dcrossL j i
  | .cup i => [([], Shape.cap i, [])]
  | .cap i => [([], Shape.cup i, [])]
  | .lcross i j => lcrossL j i
  | .dcup i n => dcapL i n
  | .dcap i n => dcupL i n

variable (D) in
/-- The scalar of the image under `ω` of a generator of the given shape. -/
def chevC (k : Type w) [CommRing k] : Shape I → k
  | .dot _ => 1
  | .cross i j => -zsign k (D.parity i * D.parity j)
  | .cup _ => 1
  | .cap _ => 1
  | .lcross _ _ => -1
  | .dcup i n => zsign k (D.parity i * n)
  | .dcap i n => zsign k (D.parity i * n)

theorem sChain_chevL (g : Shape I) : SChain (flipW g.cod) (chevL g) (flipW g.dom) := by
  cases g with
  | dot i => exact sChain_ddotL i
  | cross i j => exact sChain_dcrossL j i
  | cup i => exact ⟨rfl, rfl⟩
  | cap i => exact ⟨rfl, rfl⟩
  | lcross i j => exact sChain_lcrossL j i
  | dcup i n => exact sChain_dcapL i n
  | dcap i n => exact sChain_dcupL i n

theorem parsum_chevL (g : Shape I) : parsum D (chevL g) = g.parity D := by
  cases g with
  | dot i => show parsum D (ddotL i) = _; rw [← ddotsL_one, parsum_ddotsL, Nat.cast_one, one_mul]; rfl
  | cross i j =>
    simp [chevL, dcrossL, parsum_append, parsum_sigmaL, Shape.parity, mul_comm]
  | cup i => simp [chevL, Shape.parity]
  | cap i => simp [chevL, Shape.parity]
  | lcross i j => simp [chevL, lcrossL, Shape.parity, mul_comm]
  | dcup i n => simp [chevL, dcapL, Shape.parity]
  | dcap i n => simp [chevL, dcupL, Shape.parity]

theorem genCod_chev (g : (sig D).Gen) :
    LocalMap.genCod (chevMap D) g = ob D (-g.2) (flipW g.1.cod) := by
  rw [LocalMap.genCod, ← chevMap_obj]
  congr 1
  exact Obj.ext (Shape.wt_dom_eq_wt_cod D g.2 g.1) rfl

theorem genDom_chev (g : (sig D).Gen) :
    LocalMap.genDom (chevMap D) g = ob D (-g.2) (flipW g.1.dom) := by
  rw [LocalMap.genDom, ← chevMap_obj]
  rfl

variable (D Sc) in
/-- The image under `ω` of a generator, a morphism of `𝔘(𝔤)` from the image of its top boundary
to the image of its bottom boundary. -/
def chevImg (g : (sig D).Gen) :
    (pres D Sc).obj (LocalMap.genCod (chevMap D) g) ⟶ (pres D Sc).obj (LocalMap.genDom (chevMap D) g) :=
  eqToHom (congrArg (pres D Sc).obj (genCod_chev g)) ≫
    (chevC D k g.1 • cl D Sc (-g.2) (flipW g.1.cod) (flipW g.1.dom) (chevL g.1)) ≫
      eqToHom (congrArg (pres D Sc).obj (genDom_chev g)).symm

theorem chevImg_mem (g : (sig D).Gen) :
    chevImg D Sc g ∈ (pres D Sc).homDeg (parityDeg (sig D)) (LocalMap.genCod (chevMap D) g)
      (LocalMap.genDom (chevMap D) g) (parityDeg (sig D) g) := by
  rw [parityDeg_sig]
  have h := cl_mem (D := D) (Sc := Sc) (-g.2) (flipW g.1.cod) (flipW g.1.dom) (chevL g.1)
  rw [parsum_chevL] at h
  have := comp_mem_homDeg (eqToHom_mem_homDeg (P := pres D Sc) (parityDeg (sig D))
    (congrArg (pres D Sc).obj (genCod_chev g))) (comp_mem_homDeg (Submodule.smul_mem _
      (chevC D k g.1) h) (eqToHom_mem_homDeg (P := pres D Sc) (parityDeg (sig D))
        (congrArg (pres D Sc).obj (genDom_chev g)).symm))
  rwa [zero_add, add_zero] at this

/-! ## Images of layers -/

theorem cl_congr_idx {μ : X} {s t s' t' : List (Letter I)} (L : List (LayerData I)) (hs : s = s')
    (ht : t = t') :
    cl D Sc μ s t L = eqToHom (congrArg (fun x => (pres D Sc).obj (ob D μ x)) hs) ≫
      cl D Sc μ s' t' L ≫ eqToHom (congrArg (fun x => (pres D Sc).obj (ob D μ x)) ht).symm := by
  subst hs ht; simp

theorem whisk_congr_obj {a b : Obj (sig D)} (f : (pres D Sc).obj a ⟶ (pres D Sc).obj b)
    {u u' : Obj (sig D)} {v v' : List (sig D).Colour} (hu : u = u') (hv : v = v') :
    (pres D Sc).whisk f u v = eqToHom (by rw [hu, hv]) ≫ (pres D Sc).whisk f u' v' ≫
      eqToHom (by rw [hu, hv]) := by
  subst hu hv; simp

/-- Whiskering a morphism conjugated by `eqToHom`s. -/
theorem whisk_conj {a a' b b' : Obj (sig D)} (ha : a = a') (hb : b = b')
    (f : (pres D Sc).obj a' ⟶ (pres D Sc).obj b') (u : Obj (sig D)) (v : List (sig D).Colour) :
    (pres D Sc).whisk (eqToHom (congrArg (pres D Sc).obj ha) ≫ f ≫
        eqToHom (congrArg (pres D Sc).obj hb).symm) u v =
      eqToHom (congrArg (pres D Sc).obj (congrArg (Obj.whisker · u v) ha)) ≫
        (pres D Sc).whisk f u v ≫
          eqToHom (congrArg (pres D Sc).obj (congrArg (Obj.whisker · u v) hb)).symm := by
  subst ha hb
  simp

/-- Whiskering a normal-form diagram. -/
theorem whisk_cl (μ : X) (u v s t : List (Letter I)) (A : List (LayerData I))
    (hst : wt D (wt D μ v) t = wt D (wt D μ v) s) :
    (pres D Sc).whisk (cl D Sc (wt D μ v) s t A) (ob D (wt D (wt D μ v) s) u) (wd D μ v) =
      eqToHom (congrArg (pres D Sc).obj (ob_whisker D μ u v s s rfl)) ≫
        cl D Sc μ (u ++ s ++ v) (u ++ t ++ v) (A.map (whL u v)) ≫
          eqToHom (congrArg (pres D Sc).obj (ob_whisker D μ u v s t hst)).symm := by
  have h := plcL_cl (D := D) (Sc := Sc) μ u v s t A
  rw [plcL, dite_eq_left hst, plc] at h
  simp only [LinearMap.coe_mk, AddHom.coe_mk] at h
  rw [← h]
  simp

theorem whisk_cl' (μ ν : X) (u v s t : List (Letter I)) (hν : ν = wt D μ v) (A : List (LayerData I))
    (hst : wt D (wt D μ v) t = wt D (wt D μ v) s) {U : Obj (sig D)}
    (hU : U = ob D (wt D (wt D μ v) s) u) :
    (pres D Sc).whisk (cl D Sc ν s t A) U (wd D μ v) =
      eqToHom (by subst hν hU; exact congrArg (pres D Sc).obj (ob_whisker D μ u v s s rfl)) ≫
        cl D Sc μ (u ++ s ++ v) (u ++ t ++ v) (A.map (whL u v)) ≫
          eqToHom (by subst hν hU; exact (congrArg (pres D Sc).obj (ob_whisker D μ u v s t hst)).symm) := by
  subst hν hU
  exact whisk_cl μ u v s t A hst

theorem chev_lay_cod (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) :
    (chevMap D).obj (lay D μ u g v).cod = ob D (-μ) (flipW u ++ flipW g.cod ++ flipW v) := by
  rw [lay_cod, chevMap_obj, flipW_append, flipW_append]

theorem chev_lay_dom (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) :
    (chevMap D).obj (lay D μ u g v).dom = ob D (-μ) (flipW u ++ flipW g.dom ++ flipW v) := by
  rw [lay_dom, chevMap_obj, flipW_append, flipW_append]

set_option backward.isDefEq.respectTransparency false in
/-- **The image under `ω` of a layer** `u ⊗ g ⊗ v` with rightmost region `μ`: the image of `g`
placed between the reversed strands, at the region `-μ`. -/
theorem layerImg_chev (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) :
    SOpMap.layerImg (chevMap D) (chevImg D Sc) (lay D μ u g v) =
      eqToHom (congrArg (pres D Sc).obj (chev_lay_cod μ u g v)) ≫
        (chevC D k g • cl D Sc (-μ) (flipW u ++ flipW g.cod ++ flipW v)
          (flipW u ++ flipW g.dom ++ flipW v) ((chevL g).map (whL (flipW u) (flipW v)))) ≫
        eqToHom (congrArg (pres D Sc).obj (chev_lay_dom μ u g v)).symm := by
  have hv := lay_valid D μ u g v
  have hwC := SOpMap.genCod_whiskerOK (κ := chevMap D) hv
  have hwD : (LocalMap.genDom (chevMap D) (lay D μ u g v).gen).WhiskerOK
      ((chevMap D).obj ⟨(lay D μ u g v).start, (lay D μ u g v).left⟩)
      ((chevMap D).word (lay D μ u g v).right) := LocalMap.genDom_whiskerOK (chevMap D) hv
  have hU : (chevMap D).obj ⟨(lay D μ u g v).start, (lay D μ u g v).left⟩ =
      ob D (wt D (wt D (-μ) (flipW v)) (flipW g.cod)) (flipW u) := by
    refine Obj.ext ?_ ?_
    · show -(wt D μ (u ++ g.dom ++ v)) = wt D (wt D (wt D (-μ) (flipW v)) (flipW g.cod)) (flipW u)
      rw [← wt_append, ← wt_append, ← flipW_append, ← flipW_append, wt_flipW, wt_lay_dom,
        List.append_assoc]
    · show (chevMap D).word (wd D (wt D μ (g.dom ++ v)) u) =
        wd D (wt D (wt D (-μ) (flipW v)) (flipW g.cod)) (flipW u)
      rw [(chevMap D).word_eq]
      refine (wd_flipW D _ u).trans (congrArg (wd D · (flipW u)) ?_)
      rw [← wt_append, ← flipW_append, wt_flipW, wt_append, wt_append, Shape.wt_dom_eq_wt_cod]
  have hV : (chevMap D).word (lay D μ u g v).right = wd D (-μ) (flipW v) := by
    rw [(chevMap D).word_eq]; exact wd_flipW D μ v
  unfold SOpMap.layerImg chevImg
  rw [whisk_conj (genCod_chev _) (genDom_chev _), Presentation.whisk_smul, whisk_congr_obj _ hU hV,
    whisk_cl' (U := ob D (wt D (wt D (-μ) (flipW v)) (flipW g.cod)) (flipW u)) (-μ)
      (-(lay D μ u g v).gen.2) (flipW u) (flipW v)
      (flipW (lay D μ u g v).gen.1.cod) (flipW (lay D μ u g v).gen.1.dom)
      (by show -(wt D μ v) = _; rw [wt_flipW]) _
      (by show wt D (wt D (-μ) (flipW v)) (flipW g.dom) = wt D (wt D (-μ) (flipW v)) (flipW g.cod)
          rw [← wt_append, ← wt_append, ← flipW_append, ← flipW_append, wt_flipW, wt_flipW,
            wt_append, wt_append, Shape.wt_dom_eq_wt_cod])
      rfl]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

/-! ## Images of normal-form diagrams -/

/-- The layers of the image under `ω` of a normal-form diagram: the images of its layers, in
reverse order. -/
def omegaL : List (LayerData I) → List (LayerData I)
  | [] => []
  | x :: ls => omegaL ls ++ (chevL x.2.1).map (whL (flipW x.1) (flipW x.2.2))

variable (D k) in
/-- The scalar of the image under `ω` of a normal-form diagram. -/
def omegaC : List (LayerData I) → k
  | [] => 1
  | x :: ls => zsign k (x.2.1.parity D * parsum D ls) * chevC D k x.2.1 * omegaC ls

theorem sChain_omegaL {t t' : List (Letter I)} {ls : List (LayerData I)} (h : SChain t ls t') :
    SChain (flipW t') (omegaL ls) (flipW t) := by
  induction ls generalizing t with
  | nil => exact congrArg flipW (show t = t' from h).symm
  | cons x ls ih =>
    obtain ⟨rfl, h2⟩ := h
    refine (ih h2).append ?_
    have := (sChain_chevL x.2.1).whisk (flipW x.1) (flipW x.2.2)
    simpa only [flipW_append] using this

theorem sign_eq_zsign (p : ZMod 2) : sign k p = zsign k p := by
  fin_cases p <;> rfl

theorem chevPar (a b : Obj (sig D)) (p : ZMod 2) :
    parity (R := k) ((pres D Sc).obj a) ((pres D Sc).obj b) p =
      (pres D Sc).homDeg (parityDeg (sig D)) a b p := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The image under `ω` of a one-layer normal-form diagram. -/
theorem unsop_functor_one (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) :
    SOp.unsop ((SOpMap.functor (chevMap D) (chevImg D Sc)).map
      (mkD D μ [(u, g, v)] (t := u ++ g.dom ++ v) (t' := u ++ g.cod ++ v) ⟨rfl, rfl⟩)) =
      eqToHom (congrArg (pres D Sc).obj (chevMap_obj D μ (u ++ g.cod ++ v))) ≫
        (chevC D k g • cl D Sc (-μ) (flipW (u ++ g.cod ++ v)) (flipW (u ++ g.dom ++ v))
          ((chevL g).map (whL (flipW u) (flipW v)))) ≫
        eqToHom (congrArg (pres D Sc).obj (chevMap_obj D μ (u ++ g.dom ++ v))).symm := by
  show SOp.unsop ((SOpMap.interp (chevMap D) (chevImg D Sc)).functor.map
    (Diagram.mk [lay D μ u g v] _)) = _
  rw [Interpretation.functor_map_mk_cons, Interpretation.functor_map_mk_nil,
    SOpMap.unsop_eqToHom_comp, SOpMap.unsop_comp_eqToHom]
  erw [SOp.unsop_mk']
  rw [layerImg_chev, cl_congr_idx _ (by simp : flipW (u ++ g.cod ++ v) = flipW u ++ flipW g.cod ++ flipW v)
    (by simp : flipW (u ++ g.dom ++ v) = flipW u ++ flipW g.dom ++ flipW v)]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- **The image under `ω` of a normal-form diagram**: the images of its layers composed in reverse
order, with the super-opposite signs. -/
theorem unsop_functor_mkD (μ : X) {t t' : List (Letter I)} (ls : List (LayerData I))
    (h : SChain t ls t') :
    SOp.unsop ((SOpMap.functor (chevMap D) (chevImg D Sc)).map (mkD D μ ls h)) =
      eqToHom (congrArg (pres D Sc).obj (chevMap_obj D μ t')) ≫
        (omegaC D k ls • cl D Sc (-μ) (flipW t') (flipW t) (omegaL ls)) ≫
          eqToHom (congrArg (pres D Sc).obj (chevMap_obj D μ t)).symm := by
  induction ls generalizing t with
  | nil =>
    obtain rfl : t = t' := h
    show SOp.unsop ((SOpMap.interp (chevMap D) (chevImg D Sc)).functor.map (Diagram.mk [] _)) = _
    rw [Interpretation.functor_map_mk_nil]
    simp [omegaL, omegaC, cl_nil]
    rfl
  | cons x ls ih =>
    obtain ⟨u, g, v⟩ := x
    obtain ⟨rfl, h2⟩ := h
    rw [show mkD D μ ((u, g, v) :: ls) ⟨rfl, h2⟩ = mkD D μ [(u, g, v)] (t := u ++ g.dom ++ v)
        (t' := u ++ g.cod ++ v) ⟨rfl, rfl⟩ ≫ mkD D μ ls h2 from
        (mkD_comp D μ [(u, g, v)] ls ⟨rfl, rfl⟩ h2).symm,
      Functor.map_comp,
      SOp.comp_of_mem (SOp.mem_parity_iff.mp (SOpMap.functor_map_mem chevPar chevImg_mem _))
        (SOp.mem_parity_iff.mp (SOpMap.functor_map_mem chevPar chevImg_mem _)),
      unsop_functor_one, ih h2, degree_parity_mkD, degree_parity_mkD, sign_eq_zsign]
    have hA : SChain (flipW t') (omegaL ls) (flipW (u ++ g.cod ++ v)) := sChain_omegaL h2
    have hB : SChain (flipW (u ++ g.cod ++ v)) ((chevL g).map (whL (flipW u) (flipW v)))
        (flipW (u ++ g.dom ++ v)) := by
      simpa only [flipW_append] using (sChain_chevL g).whisk (flipW u) (flipW v)
    simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp, smul_smul]
    rw [← Category.assoc (cl D Sc (-μ) _ _ (omegaL ls)), cl_comp hA hB]
    congr 1
    simp only [omegaC, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, parsum]
    ring

/-! ## Computing `omegaL` and `omegaC` -/

@[simp] theorem omegaL_nil : omegaL ([] : List (LayerData I)) = [] := rfl

@[simp] theorem omegaL_cons (x : LayerData I) (ls : List (LayerData I)) :
    omegaL (x :: ls) = omegaL ls ++ (chevL x.2.1).map (whL (flipW x.1) (flipW x.2.2)) := rfl

@[simp] theorem omegaL_append (A B : List (LayerData I)) :
    omegaL (A ++ B) = omegaL B ++ omegaL A := by
  induction A with
  | nil => simp
  | cons x A ih => simp [ih]

@[simp] theorem omegaC_nil : omegaC D k [] = 1 := rfl

@[simp] theorem omegaC_cons (x : LayerData I) (ls : List (LayerData I)) :
    omegaC D k (x :: ls) = zsign k (x.2.1.parity D * parsum D ls) * chevC D k x.2.1 *
      omegaC D k ls := rfl

theorem omegaC_append (A B : List (LayerData I)) :
    omegaC D k (A ++ B) = zsign k (parsum D A * parsum D B) * omegaC D k A * omegaC D k B := by
  induction A with
  | nil => simp [zsign_zero]
  | cons x A ih =>
    simp only [List.cons_append, omegaC_cons, ih, parsum_cons, parsum_append, mul_add, add_mul,
      zsign_add]
    ring

theorem omegaL_dotsL (u : List (Letter I)) (i : I) (v : List (Letter I)) (n : ℕ) :
    omegaL (dotsL u i v n) = (ddotsL i n).map (whL (flipW u) (flipW v)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show ddotsL i (n + 1) = ddotsL i n ++ ddotL i by
        simp only [ddotsL, List.replicate_succ', List.flatten_append, List.flatten_singleton],
      dotsL, List.replicate_succ, omegaL_cons, ← dotsL, ih, List.map_append]
    rfl

theorem omegaC_dotsL (u : List (Letter I)) (i : I) (v : List (Letter I)) (n : ℕ) :
    omegaC D k (dotsL u i v n) = zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) := by
  induction n with
  | zero => simp [dotsL, zsign_zero]
  | succ n ih =>
    rw [dotsL, List.replicate_succ, omegaC_cons, ← dotsL, ih, parsum_dotsL]
    simp only [chevC, mul_one, ← zsign_add, Shape.parity]
    congr 1
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rw [show 2 * m / 2 = m by omega, show (2 * m + 1) / 2 = m by omega]
      push_cast
      rw [show (2 : ZMod 2) = 0 from rfl]; ring
    · rw [show (2 * m + 1) / 2 = m by omega, show (2 * m + 1 + 1) / 2 = m + 1 by omega]
      push_cast
      rw [show (2 : ZMod 2) = 0 from rfl]
      have := zmod2_mul_self (D.parity i)
      linear_combination this

/-! ## The linear map induced on relations -/

variable (Sc) in
/-- The image under `ω` of a linear combination of diagrams from `E_s 1_ν` to `E_t 1_ν`, as a
morphism from `F_t 1_{-ν}` to `F_s 1_{-ν}`. -/
def omegaLin (ν : X) (s t : List (Letter I)) :
    LinDiagram k (ob D ν s) (ob D ν t) →ₗ[k]
      ((pres D Sc).obj (ob D (-ν) (flipW t)) ⟶ (pres D Sc).obj (ob D (-ν) (flipW s))) where
  toFun f := eqToHom (congrArg (pres D Sc).obj (chevMap_obj D ν t)).symm ≫
    SOp.unsop ((freeLift k (SOpMap.functor (chevMap D) (chevImg D Sc))).map f) ≫
      eqToHom (congrArg (pres D Sc).obj (chevMap_obj D ν s))
  map_add' f g := by
    simp only [Functor.map_add, SOp.unsop_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by
    simp only [Functor.map_smul, SOp.unsop_smul, Linear.smul_comp, Linear.comp_smul,
      RingHom.id_apply]

theorem omegaLin_dg (ν : X) {s t : List (Letter I)} (ls : List (LayerData I)) (h : SChain s ls t) :
    omegaLin Sc ν s t (dg D ν ls h) =
      omegaC D k ls • cl D Sc (-ν) (flipW t) (flipW s) (omegaL ls) := by
  simp only [omegaLin, LinearMap.coe_mk, AddHom.coe_mk, dg, freeLift_map_of]
  rw [unsop_functor_mkD]
  simp

theorem omegaLin_idg (ν : X) (t : List (Letter I)) :
    omegaLin Sc ν t t (idg D ν t) = cl D Sc (-ν) (flipW t) (flipW t) [] := by
  simp only [omegaLin, LinearMap.coe_mk, AddHom.coe_mk, idg, freeLift_map_of]
  erw [SOp.unsop_id, Category.id_comp, eqToHom_trans, eqToHom_refl, cl_nil]

theorem eq_zero_of_omegaLin {ν : X} {s t : List (Letter I)} {f : LinDiagram k (ob D ν s) (ob D ν t)}
    (hf : omegaLin Sc ν s t f = 0) :
    (freeLift k (SOpMap.functor (chevMap D) (chevImg D Sc))).map f = 0 := by
  apply SOp.hom_ext
  rw [SOp.unsop_zero]
  simp only [omegaLin, LinearMap.coe_mk, AddHom.coe_mk] at hf
  have := congrArg (fun x => eqToHom (congrArg (pres D Sc).obj (chevMap_obj D ν t)) ≫ x ≫
    eqToHom (congrArg (pres D Sc).obj (chevMap_obj D ν s)).symm) hf
  simpa using this

end OddMath.SKM
