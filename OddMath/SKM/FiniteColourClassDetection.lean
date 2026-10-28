/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.FiniteColourIdealDescent
import OddMath.SKM.Calculus

/-!
# Finite-colour detection of relations among normal-form classes

Brundan–Ellis, *Super Kac–Moody 2-categories*, Definition 1.5, used as in
`SwappedActionAssembly`, §8. A finite relation `∑ cₘ [Nₘ] = 0` among classes of
normal-form layer lists in the full-colour presentation already holds in every
finite-colour restriction containing one finite witness set, as soon as all layer
lists come from that restriction. The witness set depends only on the original
relation, not on the restriction.

The inclusion of free diagrams is injective, and well-formedness of a layer list
is reflected by inclusion; together with the finite descent of the presentation
ideal these give the detection statement `sum_cl_eq_zero_restrict`. No functor
between presented categories and no faithfulness statement is used.
-/

noncomputable section
namespace OddMath.SKM.FiniteColour
open CategoryTheory StringDiagrams
open scoped Classical
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X) (J : Finset I)
variable {k : Type w} [CommRing k] (Sc : Scalars D k)

theorem letter_injective : Function.Injective (letter J) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ h
  simp only [letter, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  exact Prod.ext rfl (Subtype.ext h)

theorem shape_injective : Function.Injective (shape J) := by
  intro g g' h
  cases g <;> cases g' <;>
    simp only [shape, reduceCtorEq, Shape.dot.injEq, Shape.cross.injEq, Shape.cup.injEq,
      Shape.cap.injEq, Shape.lcross.injEq, Shape.dcup.injEq, Shape.dcap.injEq,
      Subtype.val_inj] at h ⊢ <;> exact h

omit [AddCommGroup X] in
theorem colour_injective : Function.Injective (colour J (X := X)) := by
  rintro ⟨l, r⟩ ⟨l', r'⟩ h
  simp only [colour, Col.mk.injEq] at h
  rw [letter_injective J h.1, h.2]

/-- Inclusion of layers is injective, including on generators and region labels. -/
theorem inclusion_layer_injective : Function.Injective (inclusion D J).layer := by
  rintro ⟨s, l, g, r⟩ ⟨s', l', g', r'⟩ h
  simp only [SigMap.layer, Layer.mk.injEq] at h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  have hw : Function.Injective (List.map (colour J (X := X))) :=
    List.map_injective_iff.mpr (colour_injective J)
  have hg : g = g' := by
    obtain ⟨g, μ⟩ := g
    obtain ⟨g', μ'⟩ := g'
    change (shape J g, μ) = (shape J g', μ') at h₃
    rw [Prod.mk.injEq] at h₃
    rw [shape_injective J h₃.1, h₃.2]
  rw [show s = s' from h₁, hw h₂, hg, hw h₄]

/-- Inclusion of free diagrams at normal-form boundaries is injective. -/
theorem diagram_injective (μ : X) (t t' : List (Letter J)) :
    Function.Injective (diagram D J (μ := μ) (t := t) (t' := t')) := by
  intro d d' h
  apply Diagram.ext
  have := congrArg Diagram.layers h
  simp only [diagram, Diagram.layers_cast, LayerMap.layers_map] at this
  exact (List.map_injective_iff.mpr (inclusion_layer_injective D J)) this

/-- Inclusion of free linear combinations is injective. -/
theorem linear_injective (μ : X) (t t' : List (Letter J)) :
    Function.Injective (linear (k := k) D J μ t t') :=
  Finsupp.mapDomain_injective (diagram_injective D J μ t t')

/-- `linear` is the cast of the layer-map image, at the normal-form boundaries. -/
theorem cast_lin_eq_linear (μ : X) (t t' : List (Letter J))
    (f : LinDiagram k (ob (D.restrictColours J) μ t) (ob (D.restrictColours J) μ t')) :
    LinDiagram.cast ((inclusion D J).toLayerMap.lin f) (inclusion_ob D J μ t)
      (inclusion_ob D J μ t') = linear D J μ t t' f := by
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ f) = Finsupp.mapDomain _ f
  rw [← Finsupp.mapDomain_comp]
  rfl

/-- Well-formedness of a normal-form layer list is reflected by inclusion. -/
theorem chain_of_map {t t' : List (Letter J)} {ls : List (LayerData J)}
    (h : SChain (t.map (letter J)) (ls.map (layerData J)) (t'.map (letter J))) :
    SChain t ls t' := by
  have hw : Function.Injective (List.map (letter J)) :=
    List.map_injective_iff.mpr (letter_injective J)
  induction ls generalizing t with
  | nil => exact hw h
  | cons x ls ih =>
    obtain ⟨h₁, h₂⟩ := h
    refine ⟨hw ?_, ih ?_⟩
    · simpa [layerData] using h₁
    · simpa [layerData] using h₂

theorem chain_map_iff {t t' : List (Letter J)} {ls : List (LayerData J)} :
    SChain (t.map (letter J)) (ls.map (layerData J)) (t'.map (letter J)) ↔ SChain t ls t' :=
  ⟨chain_of_map J, chain_map J⟩

/-- The free linear representative of a class: the diagram if the layers chain, else zero. -/
def clLin (μ : X) (s t : List (Letter I)) (ls : List (LayerData I)) :
    LinDiagram k (ob D μ s) (ob D μ t) :=
  if h : SChain s ls t then LinDiagram.of (mkD D μ ls h) else 0

theorem lin_clLin (μ : X) (s t : List (Letter I)) (ls : List (LayerData I)) :
    (pres D Sc).lin (clLin (k := k) D μ s t ls) = cl D Sc μ s t ls := by
  unfold clLin cl
  split_ifs <;> simp

theorem linear_clLin (μ : X) (s t : List (Letter J)) (ls : List (LayerData J)) :
    linear D J μ s t (clLin (k := k) (D.restrictColours J) μ s t ls) =
      clLin D μ (s.map (letter J)) (t.map (letter J)) (ls.map (layerData J)) := by
  unfold clLin
  by_cases h : SChain s ls t
  · rw [dite_eq_left h, dite_eq_left (chain_map J h), linear_of, diagram_mkD]
  · rw [dite_eq_right h, dite_eq_right (mt (chain_of_map J) h), linear_zero]

theorem lin_sum_clLin {ι : Type*} (μ : X) (s t : List (Letter I)) (F : Finset ι)
    (c : ι → k) (ls : ι → List (LayerData I)) :
    (pres D Sc).lin (∑ m ∈ F, c m • clLin D μ s t (ls m)) =
      ∑ m ∈ F, c m • cl D Sc μ s t (ls m) := by
  induction F using Finset.induction_on with
  | empty => simp
  | insert m F hm ih =>
    rw [Finset.sum_insert hm, Finset.sum_insert hm, Presentation.lin_add,
      Presentation.lin_smul, lin_clLin, ih]

/-- The finite-colour ideal grows with its colour set. -/
theorem finiteColourIdeal_mono {a b : Obj (sig D)} {J₁ J₂ : Finset I} (h : J₁ ⊆ J₂) :
    finiteColourIdeal D Sc a b J₁ ≤ finiteColourIdeal D Sc a b J₂ :=
  Submodule.span_mono (by
    rintro f ⟨c, hc, rfl⟩
    exact ⟨c, hc.trans h, rfl⟩)

/-- **Finite-colour detection of class relations.** A finite linear relation among
classes of layer lists in the full-colour presentation has one finite colour set `J₁`
such that, in every restriction to `J ⊇ J₁`, the same relation holds among classes
of any restricted layer lists including onto the original ones. -/
theorem sum_cl_eq_zero_restrict {ι : Type*} (μ : X) (s t : List (Letter I)) (F : Finset ι)
    (c : ι → k) (ls : ι → List (LayerData I))
    (h : ∑ m ∈ F, c m • cl D Sc μ s t (ls m) = 0) :
    ∃ J₁ : Finset I, ∀ J : Finset I, J₁ ⊆ J →
      ∀ (s' t' : List (Letter J)) (ls' : ι → List (LayerData J)),
        s'.map (letter J) = s → t'.map (letter J) = t →
        (∀ m ∈ F, (ls' m).map (layerData J) = ls m) →
        ∑ m ∈ F, c m • cl (D.restrictColours J) (Sc.restrictColours D J) μ s' t' (ls' m) = 0 := by
  let R : LinDiagram k (ob D μ s) (ob D μ t) := ∑ m ∈ F, c m • clLin D μ s t (ls m)
  have hR : R ∈ (pres D Sc).ideal _ _ := by
    have : (pres D Sc).lin R = (pres D Sc).lin 0 := by
      rw [lin_sum_clLin, h, Presentation.lin_zero]
    simpa using ((pres D Sc).lin_eq_iff R 0).mp this
  obtain ⟨J₁, hJ₁⟩ := mem_finiteColourIdeal D Sc hR
  refine ⟨J₁, fun J hJ s' t' ls' hs ht hls => ?_⟩
  subst hs ht
  obtain ⟨f, hf, hfR⟩ := supported_ideal_lift_at D J Sc
    (ob (D.restrictColours J) μ s') (ob (D.restrictColours J) μ t')
    (inclusion_ob D J μ s') (inclusion_ob D J μ t') (finiteColourIdeal_mono D Sc hJ hJ₁)
  rw [cast_lin_eq_linear] at hfR
  let R' : LinDiagram k (ob (D.restrictColours J) μ s') (ob (D.restrictColours J) μ t') :=
    ∑ m ∈ F, c m • clLin (D.restrictColours J) μ s' t' (ls' m)
  have hR' : linear D J μ s' t' R' = R := by
    simp only [R', R, linear_sum, linear_smul, linear_clLin]
    exact Finset.sum_congr rfl fun m hm => by rw [hls m hm]
  have hf' : f = R' := linear_injective D J μ s' t' (hfR.trans hR'.symm)
  have hlin : (pres (D.restrictColours J) (Sc.restrictColours D J)).lin R' = 0 := by
    rw [← hf', ← (pres (D.restrictColours J) (Sc.restrictColours D J)).lin_zero,
      (pres (D.restrictColours J) (Sc.restrictColours D J)).lin_eq_iff, sub_zero]
    exact hf
  rwa [lin_sum_clLin] at hlin

end OddMath.SKM.FiniteColour
