/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.EvenBridge.Functor
import OddMath.SKM.EvenBridge.KLUpCups
import Categorification.Diagrams.KL3.Pitchfork

/-!
# Fullness of the 2-functor `𝔘(𝔤) → U` for even data

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5, and
A. D. Lauda, M. Khovanov, *A categorification of quantum sl(n)* III, arXiv:0807.3250,
Definition 3.1.

Every 2-morphism of KL III's `U` between `E_s 1_μ` and `E_t 1_μ` is the image of a 2-morphism of
`𝔘(𝔤)` under `evenFunctor` (`evenFunctor_surjective`). Every normal-form diagram of `U` is a
composite of layers. The dots and crossings on upward strands and the cups and caps of downward
strands are images of the generators of Definition 1.5. The downward dot and crossing are rotations
of upward ones (KL III (3.3) and the cyclicity of the crossing). The upward cups and caps are
written through the downward ones, sideways crossings and the images of the `♦`-cups and `♦`-caps
(`Categorification.KL3.Diagram.cupUp_eq_dcupEF` and its companions).
-/

noncomputable section

namespace OddMath.SKM.EvenBridge

open CategoryTheory Categorification.KL3

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
  (C : Categorification.QuantumGroup.CartanDatum I) (hc : Compatible D C)
  (k : Type w) [CommRing k] (Sc : Scalars D k) (hD : IsEven D) (hS : IsKLScalars D k Sc)

/-- Shorthand for the KL III weight datum of `D`. -/
local notation "RD" => weightDatum D C hc

instance evenFunctor_additive : (evenFunctor D C hc k Sc hD hS).Additive := by
  unfold evenFunctor; infer_instance

instance evenFunctor_linear : (evenFunctor D C hc k Sc hD hS).Linear k := by
  unfold evenFunctor; infer_instance

theorem evenFunctor_map_diag {a b : StringDiagrams.Obj (sig D)} (d : a ⟶ b) :
    (evenFunctor D C hc k Sc hD hS).map ((pres D Sc).diag d) = (locMap D C hc k).functor.map d := by
  unfold evenFunctor
  exact StringDiagrams.LocalMap.liftGen_diag _ _ _ _ d

/-- The functor on 2-morphisms `E_s 1_μ ⟶ E_t 1_μ`, read between KL III's objects. -/
def mapOb (μ : X) (s t : List (Letter I)) :
    ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) →ₗ[k]
      ((Diagram.pres RD k).obj (Diagram.ob RD μ s) ⟶ (Diagram.pres RD k).obj (Diagram.ob RD μ t)) where
  toFun g := eqToHom (congrArg (Diagram.pres RD k).obj (κ_obj_ob D C hc μ s)).symm ≫
      (evenFunctor D C hc k Sc hD hS).map g ≫
        eqToHom (congrArg (Diagram.pres RD k).obj (κ_obj_ob D C hc μ t))
  map_add' f g := by simp [Functor.map_add]
  map_smul' r f := by simp [Functor.map_smul]

theorem mapOb_comp (μ : X) (s t r : List (Letter I)) (f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t))
    (g : (pres D Sc).obj (ob D μ t) ⟶ (pres D Sc).obj (ob D μ r)) :
    mapOb D C hc k Sc hD hS μ s r (f ≫ g) =
      mapOb D C hc k Sc hD hS μ s t f ≫ mapOb D C hc k Sc hD hS μ t r g := by
  simp [mapOb]

/-- The image of `evenFunctor` on 2-morphisms `E_s 1_μ ⟶ E_t 1_μ`. -/
abbrev range (μ : X) (s t : List (Letter I)) :=
  LinearMap.range (mapOb D C hc k Sc hD hS μ s t)

variable {D C hc k Sc hD hS}

theorem comp_mem_range {μ : X} {s t r : List (Letter I)} {f g}
    (hf : f ∈ range D C hc k Sc hD hS μ s t) (hg : g ∈ range D C hc k Sc hD hS μ t r) :
    f ≫ g ∈ range D C hc k Sc hD hS μ s r := by
  obtain ⟨f, rfl⟩ := hf
  obtain ⟨g, rfl⟩ := hg
  exact ⟨f ≫ g, mapOb_comp D C hc k Sc hD hS μ s t r f g⟩

theorem id_mem_range (μ : X) (s : List (Letter I)) :
    𝟙 _ ∈ range D C hc k Sc hD hS μ s s :=
  ⟨𝟙 _, by
    simp only [mapOb, LinearMap.coe_mk, AddHom.coe_mk]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]⟩

variable (D C hc k Sc hD hS)

/-- **The image of a generator placed between strands** lies in the image of the functor. -/
theorem plcL_imgS_mem (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) :
    Diagram.plcL RD k μ u v g.dom g.cod (imgS D C hc k (Diagram.wt RD μ v) g) ∈
      range D C hc k Sc hD hS μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) := by
  refine ⟨(pres D Sc).diag (mkD D μ [(u, g, v)] ⟨rfl, rfl⟩), ?_⟩
  simp [mapOb, evenFunctor_map_diag, map_mkD_single]

/-- A layer is its shape placed between the strands. -/
theorem dg_layer (μ : X) (u : List (Letter I)) (g : Diagram.Shape I) (v : List (Letter I)) :
    Diagram.dg RD k μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)] =
      Diagram.plcL RD k μ u v g.dom g.cod
        (Diagram.dg RD k (Diagram.wt RD μ v) g.dom g.cod [([], g, [])]) := by
  rw [Diagram.plcL_dg]
  simp

/-- The shapes of KL III that are images of generators of Definition 1.5. -/
def GoodShape : Diagram.Shape I → Prop
  | .dot l => l.1 = true
  | .cross ε _ _ => ε = true
  | .cup l => l.1 = false
  | .cap l => l.1 = false

theorem layer_mem_of_good (μ : X) (u : List (Letter I)) (g : Diagram.Shape I) (v : List (Letter I))
    (hg : GoodShape g) :
    Diagram.dg RD k μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)] ∈
      range D C hc k Sc hD hS μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) := by
  rw [dg_layer]
  cases g with
  | dot l =>
    obtain ⟨b, i⟩ := l
    obtain rfl : b = true := hg
    exact plcL_imgS_mem D C hc k Sc hD hS μ u (.dot i) v
  | cross ε i j =>
    obtain rfl : ε = true := hg
    exact plcL_imgS_mem D C hc k Sc hD hS μ u (.cross i j) v
  | cup l =>
    obtain ⟨b, i⟩ := l
    obtain rfl : b = false := hg
    exact plcL_imgS_mem D C hc k Sc hD hS μ u (.cup i) v
  | cap l =>
    obtain ⟨b, i⟩ := l
    obtain rfl : b = false := hg
    exact plcL_imgS_mem D C hc k Sc hD hS μ u (.cap i) v

theorem dg_mem_of_good (μ : X) {s t : List (Letter I)} (ls : List (Diagram.LayerData I))
    (h : Diagram.SChain s ls t) (hg : ∀ x ∈ ls, GoodShape x.2.1) :
    Diagram.dg RD k μ s t ls ∈ range D C hc k Sc hD hS μ s t := by
  induction ls generalizing s with
  | nil =>
    obtain rfl : s = t := h
    rw [Diagram.dg_nil]
    exact id_mem_range μ s
  | cons x ls ih =>
    obtain ⟨u, g, v⟩ := x
    obtain ⟨rfl, h'⟩ := h
    rw [show ((u, g, v) :: ls) = [(u, g, v)] ++ ls from rfl,
      ← Diagram.dg_comp
        (show Diagram.SChain (u ++ g.dom ++ v) [(u, g, v)] (u ++ g.cod ++ v) from ⟨rfl, rfl⟩) h']
    exact comp_mem_range (layer_mem_of_good D C hc k Sc hD hS μ u g v (hg (u, g, v) (by simp)))
      (ih h' fun y hy => hg y (List.mem_cons_of_mem _ hy))

/-- A placed diagram all of whose shapes are good lies in the image. -/
theorem plcL_dg_mem_of_good (μ : X) (u v : List (Letter I)) {s t : List (Letter I)}
    (ls : List (Diagram.LayerData I)) (h : Diagram.SChain s ls t) (hg : ∀ x ∈ ls, GoodShape x.2.1) :
    Diagram.plcL RD k μ u v s t (Diagram.dg RD k (Diagram.wt RD μ v) s t ls) ∈
      range D C hc k Sc hD hS μ (u ++ s ++ v) (u ++ t ++ v) := by
  rw [Diagram.plcL_dg]
  exact dg_mem_of_good D C hc k Sc hD hS μ _ (h.whisk u v) fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact hg y hy

theorem wt_dn_up (ν : X) (i : I) :
    Diagram.wt RD ν [Diagram.dn i, Diagram.up i] = Diagram.wt RD ν [] := by
  simp [Diagram.sh, Categorification.QuantumGroup.UDot.sgn]

theorem wt_up_dn (ν : X) (i : I) :
    Diagram.wt RD ν [Diagram.up i, Diagram.dn i] = Diagram.wt RD ν [] := by
  simp [Diagram.sh, Categorification.QuantumGroup.UDot.sgn]

/-- **Every layer of KL III's `U` lies in the image of the functor.** -/
theorem layer_mem (μ : X) (u : List (Letter I)) (g : Diagram.Shape I) (v : List (Letter I)) :
    Diagram.dg RD k μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)] ∈
      range D C hc k Sc hD hS μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) := by
  rcases g with ⟨b, i⟩ | ⟨ε, i, j⟩ | ⟨b, i⟩ | ⟨b, i⟩
  · cases b
    · rw [dg_layer]
      erw [Diagram.dg_cycDotL]
      exact plcL_dg_mem_of_good D C hc k Sc hD hS μ u v _ (by schain) (by simp [GoodShape])
    · exact layer_mem_of_good D C hc k Sc hD hS μ u _ v rfl
  · cases ε
    · rw [dg_layer]
      erw [Diagram.dg_cycCrossL]
      exact plcL_dg_mem_of_good D C hc k Sc hD hS μ u v _ (by schain) (by simp [GoodShape])
    · exact layer_mem_of_good D C hc k Sc hD hS μ u _ v rfl
  · cases b
    · exact layer_mem_of_good D C hc k Sc hD hS μ u _ v rfl
    · rw [dg_layer]
      by_cases h : 1 ≤ Diagram.ip RD i (Diagram.wt RD μ v)
      · erw [Diagram.cupUp_eq_dcupEF (k := k) i _ h]
        have := plcL_imgS_mem D C hc k Sc hD hS μ u
          (.dcup i ((Diagram.ip RD i (Diagram.wt RD μ v)).toNat - 1)) v
        have hn : (Diagram.ip RD i (Diagram.wt RD μ v)).toNat - 1 <
            (Diagram.ip RD i (Diagram.wt RD μ v)).toNat := by omega
        simp only [imgS, hn, ↓reduceIte] at this
        exact this
      · erw [Diagram.cupUp_eq_cupDotFE_crossr (k := k) i _ (by omega)]
        change Diagram.plcL RD k μ u v [] [Diagram.up i, Diagram.dn i] _ ∈
          range D C hc k Sc hD hS μ (u ++ [] ++ v) (u ++ [Diagram.up i, Diagram.dn i] ++ v)
        rw [← Diagram.plcL_comp RD k μ u v (wt_dn_up D C hc _ i)
          ((wt_up_dn D C hc _ i).trans (wt_dn_up D C hc _ i).symm)]
        exact comp_mem_range
          (plcL_dg_mem_of_good D C hc k Sc hD hS μ u v _ (by schain)
            (by simp [GoodShape, Diagram.cupDotFELs, List.mem_replicate]))
          (plcL_imgS_mem D C hc k Sc hD hS μ u (.lcross i i) v)
  · cases b
    · exact layer_mem_of_good D C hc k Sc hD hS μ u _ v rfl
    · rw [dg_layer]
      by_cases h : 0 ≤ Diagram.ip RD i (Diagram.wt RD μ v)
      · erw [Diagram.capUp_eq_crossr_dotCapEF (k := k) i _ h]
        change Diagram.plcL RD k μ u v [Diagram.dn i, Diagram.up i] [] _ ∈
          range D C hc k Sc hD hS μ (u ++ [Diagram.dn i, Diagram.up i] ++ v) (u ++ [] ++ v)
        rw [map_neg, ← Diagram.plcL_comp RD k μ u v
          ((wt_up_dn D C hc _ i).trans (wt_dn_up D C hc _ i).symm) (wt_up_dn D C hc _ i).symm]
        exact neg_mem (comp_mem_range (plcL_imgS_mem D C hc k Sc hD hS μ u (.lcross i i) v)
          (plcL_dg_mem_of_good D C hc k Sc hD hS μ u v _ (by schain)
            (by simp [GoodShape, Diagram.dotCapEFLs, List.mem_replicate]; aesop)))
      · erw [Diagram.capUp_eq_alphaFE (k := k) i]
        have := plcL_imgS_mem D C hc k Sc hD hS μ u
          (.dcap i ((-Diagram.ip RD i (Diagram.wt RD μ v)).toNat - 1)) v
        have hn : (-Diagram.ip RD i (Diagram.wt RD μ v)).toNat - 1 <
            (-Diagram.ip RD i (Diagram.wt RD μ v)).toNat := by omega
        simp only [imgS, hn, ↓reduceIte, Nat.sub_self] at this
        exact this

/-- Every normal-form diagram of KL III's `U` lies in the image of the functor. -/
theorem dg_mem (μ : X) {s t : List (Letter I)} (ls : List (Diagram.LayerData I))
    (h : Diagram.SChain s ls t) :
    Diagram.dg RD k μ s t ls ∈ range D C hc k Sc hD hS μ s t := by
  induction ls generalizing s with
  | nil =>
    obtain rfl : s = t := h
    rw [Diagram.dg_nil]
    exact id_mem_range μ s
  | cons x ls ih =>
    obtain ⟨u, g, v⟩ := x
    obtain ⟨rfl, h'⟩ := h
    rw [show ((u, g, v) :: ls) = [(u, g, v)] ++ ls from rfl, ← Diagram.dg_comp
        (show Diagram.SChain (u ++ g.dom ++ v) [(u, g, v)] (u ++ g.cod ++ v) from ⟨rfl, rfl⟩) h']
    exact comp_mem_range (layer_mem D C hc k Sc hD hS μ u g v) (ih h')

/-- **Fullness of `evenFunctor`** (BE2 Definition 1.5 → KL III Definition 3.1, even data): every
2-morphism `E_s 1_μ ⟶ E_t 1_μ` of KL III's `U` is the image of a 2-morphism of `𝔘(𝔤)`. -/
theorem range_eq_top (μ : X) (s t : List (Letter I)) : range D C hc k Sc hD hS μ s t = ⊤ := by
  refine eq_top_iff.2 fun f _ => ?_
  refine Submodule.span_le.2 ?_ (Diagram.mem_span_dg RD k μ f)
  rintro _ ⟨ls, hls, rfl⟩
  exact dg_mem D C hc k Sc hD hS μ ls hls

theorem evenFunctor_surjective (μ : X) (s t : List (Letter I))
    (f : (Diagram.pres RD k).obj (Diagram.ob RD μ s) ⟶ (Diagram.pres RD k).obj (Diagram.ob RD μ t)) :
    ∃ g : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t),
      eqToHom (congrArg (Diagram.pres RD k).obj (κ_obj_ob D C hc μ s)).symm ≫
        (evenFunctor D C hc k Sc hD hS).map g ≫
          eqToHom (congrArg (Diagram.pres RD k).obj (κ_obj_ob D C hc μ t)) = f := by
  have hf : f ∈ range D C hc k Sc hD hS μ s t := by rw [range_eq_top]; trivial
  exact hf

end OddMath.SKM.EvenBridge
