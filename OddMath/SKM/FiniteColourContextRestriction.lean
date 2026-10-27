/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.FiniteColourRestriction

/-!
# Supported free diagrams and superinterchange

The finite-derivation step of `SwappedActionAssembly`, §8, for
Brundan–Ellis Definition 1.5. Restriction keeps the original weight group
and every region label, including those on internal cup/cap strands.
-/

noncomputable section
namespace OddMath.SKM.FiniteColour
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X) (J : Finset I)
local instance contextRestrictionDecEq : DecidableEq I := Classical.decEq I

/-- Restrict each strand, retaining its orientation and region label. -/
def restrictWord (t : List (Col I X)) (ht : wordColours t ⊆ J) : List (Col J X) :=
  t.attach.map fun c => ⟨(c.val.l.1, ⟨c.val.l.2, ht (by
    classical
    simp only [wordColours, List.mem_toFinset, List.mem_map]
    exact ⟨c.val, c.property, rfl⟩)⟩), c.val.r⟩

omit [AddCommGroup X] in
@[simp] theorem word_restrictWord (t : List (Col I X)) (ht : wordColours t ⊆ J) :
    (restrictWord J t ht).map (colour J) = t := by
  simp [restrictWord, colour, letter, List.map_map]

/-- Restriction of a supported generating shape. -/
def restrictShape (g : Shape I) (hg : ∀ i ∈ g.colours, i ∈ J) : Shape J := by
  cases g with
  | dot i => exact .dot ⟨i, hg i (by simp [Shape.colours])⟩
  | cross i j => exact .cross ⟨i, hg i (by simp [Shape.colours])⟩ ⟨j, hg j (by simp [Shape.colours])⟩
  | cup i => exact .cup ⟨i, hg i (by simp [Shape.colours])⟩
  | cap i => exact .cap ⟨i, hg i (by simp [Shape.colours])⟩
  | lcross i j => exact .lcross ⟨i, hg i (by simp [Shape.colours])⟩ ⟨j, hg j (by simp [Shape.colours])⟩
  | dcup i n => exact .dcup ⟨i, hg i (by simp [Shape.colours])⟩ n
  | dcap i n => exact .dcap ⟨i, hg i (by simp [Shape.colours])⟩ n

@[simp] theorem shape_restrictShape (g : Shape I) (hg : ∀ i ∈ g.colours, i ∈ J) :
    shape J (restrictShape J g hg) = g := by
  cases g <;> rfl

/-- Restriction also applies to arbitrary, not necessarily normal-form, objects. -/
def restrictObj (a : Obj (sig D)) (ha : wordColours a.word ⊆ J) :
    Obj (sig (D.restrictColours J)) := ⟨a.start, restrictWord J a.word ha⟩

@[simp] theorem obj_restrictObj (a : Obj (sig D)) (ha : wordColours a.word ⊆ J) :
    (inclusion D J).obj (restrictObj D J a ha) = a := by
  apply Obj.ext
  · rfl
  · exact word_restrictWord J a.word ha

/-- Restriction retains the layer start and the generator's own region. -/
def restrictLayer (L : Layer (sig D)) (hL : layerColours D L ⊆ J) :
    Layer (sig (D.restrictColours J)) where
  start := L.start
  left := restrictWord J L.left (fun _ hi => hL (Finset.mem_union_left _ (Finset.mem_union_left _ hi)))
  gen := (restrictShape J L.gen.1 (fun _ hi => hL (Finset.mem_union_left _
    (Finset.mem_union_right _ (List.mem_toFinset.mpr hi)))), L.gen.2)
  right := restrictWord J L.right (fun _ hi => hL (Finset.mem_union_right _ hi))

@[simp] theorem layer_restrictLayer (L : Layer (sig D)) (hL : layerColours D L ⊆ J) :
    (inclusion D J).layer (restrictLayer D J L hL) = L := by
  cases L
  simp only [SigMap.layer, restrictLayer, inclusion, shape_restrictShape]
  congr 1 <;> exact word_restrictWord (X := X) J _ _

omit [AddCommGroup X] in
private theorem colour_injective : Function.Injective (colour (X := X) J) := by
  rintro ⟨⟨e, i, hi⟩, r⟩ ⟨⟨f, j, hj⟩, s⟩ h
  cases h
  rfl

/-- Inclusion is injective on raw objects, without a well-formedness assumption. -/
theorem inclusion_obj_injective : Function.Injective (inclusion D J).obj := by
  intro a b h
  apply Obj.ext
  · exact congrArg (fun c : Obj (sig D) => c.start) h
  · exact List.map_injective_iff.mpr (colour_injective J) (congrArg Obj.word h)

/-- Well-formedness is reflected because regions are unchanged. -/
theorem inclusion_ok_iff (r : X) (t : List (Col J X)) :
    (sig D).ok r ((inclusion D J).word t) ↔ (sig (D.restrictColours J)).ok r t := by
  induction t generalizing r with
  | nil => rfl
  | cons c t ih =>
    change (_ = r ∧ (sig D).ok c.r ((inclusion D J).word t)) ↔ _
    rw [ih]
    rfl

/-- Validity of arbitrary layers is reflected, including all intermediate regions. -/
theorem inclusion_layer_valid_iff (L : Layer (sig (D.restrictColours J))) :
    ((inclusion D J).layer L).Valid ↔ L.Valid := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (inclusion_ok_iff D J _ _).mp h.left_ok
    · have hh := h.left_end
      change (sig D).endR ((inclusion D J).region L.start) ((inclusion D J).word L.left) =
        (sig D).left ((inclusion D J).gen L.gen) at hh
      rw [(inclusion D J).endR_map, (inclusion D J).left] at hh
      exact hh
    · have hh := h.dom_ok
      change (sig D).ok ((sig D).left ((inclusion D J).gen L.gen))
        ((sig D).dom ((inclusion D J).gen L.gen)) at hh
      rw [(inclusion D J).left, (inclusion D J).dom] at hh
      exact (inclusion_ok_iff D J _ _).mp hh
    · have hh := h.dom_end
      change (sig D).endR ((sig D).left ((inclusion D J).gen L.gen))
        ((sig D).dom ((inclusion D J).gen L.gen)) = (sig D).right ((inclusion D J).gen L.gen) at hh
      rw [(inclusion D J).left, (inclusion D J).dom, (inclusion D J).right,
        (inclusion D J).endR_map] at hh
      exact hh
    · have hh := h.cod_ok
      change (sig D).ok ((sig D).left ((inclusion D J).gen L.gen))
        ((sig D).cod ((inclusion D J).gen L.gen)) at hh
      rw [(inclusion D J).left, (inclusion D J).cod] at hh
      exact (inclusion_ok_iff D J _ _).mp hh
    · have hh := h.cod_end
      change (sig D).endR ((sig D).left ((inclusion D J).gen L.gen))
        ((sig D).cod ((inclusion D J).gen L.gen)) = (sig D).right ((inclusion D J).gen L.gen) at hh
      rw [(inclusion D J).left, (inclusion D J).cod, (inclusion D J).right,
        (inclusion D J).endR_map] at hh
      exact hh
    · have hh := h.right_ok
      change (sig D).ok ((sig D).right ((inclusion D J).gen L.gen))
        ((inclusion D J).word L.right) at hh
      rw [(inclusion D J).right] at hh
      exact (inclusion_ok_iff D J _ _).mp hh
  · exact (inclusion D J).layer_valid

/-- Inclusion reflects a complete chain, not just its boundary words. -/
theorem inclusion_chain_iff (a b : Obj (sig (D.restrictColours J)))
    (ls : List (Layer (sig (D.restrictColours J)))) :
    Chain ((inclusion D J).obj a) (ls.map (inclusion D J).layer)
      ((inclusion D J).obj b) ↔ Chain a ls b := by
  constructor
  · intro h
    induction ls generalizing a with
    | nil => exact inclusion_obj_injective D J h
    | cons L ls ih =>
      have hv := (inclusion_layer_valid_iff D J L).mp h.1
      refine ⟨hv, inclusion_obj_injective D J ?_, ih L.cod ?_⟩
      · exact ((inclusion D J).toLayerMap.dom_eq hv).symm.trans h.2.1
      · have he : ((inclusion D J).layer L).cod = (inclusion D J).obj L.cod :=
          (inclusion D J).toLayerMap.cod_eq hv
        rw [← he]
        exact h.2.2
  · exact (inclusion D J).toLayerMap.chain

private theorem mem_fold_support (ls : List (Layer (sig D))) (L : Layer (sig D))
    (hL : L ∈ ls) (i : I) (hi : i ∈ layerColours D L) (A : Finset I) :
    i ∈ ls.foldl (fun K M => K ∪ layerColours D M) A := by
  induction ls generalizing A with
  | nil => simp at hL
  | cons M ls ih =>
    rcases List.mem_cons.mp hL with rfl | hL
    · have grow (ts : List (Layer (sig D))) (B : Finset I) :
          B ⊆ ts.foldl (fun K N => K ∪ layerColours D N) B := by
        induction ts generalizing B with
        | nil => exact Finset.Subset.rfl
        | cons N ts iht => exact Finset.subset_union_left.trans (iht _)
      exact grow ls _ (Finset.mem_union_right _ hi)
    · exact ih hL _

theorem diagram_source_supported {a b : Obj (sig D)} (f : a ⟶ b)
    (hf : diagramColours D f ⊆ J) : wordColours a.word ⊆ J :=
  Finset.Subset.trans (Finset.subset_union_left.trans Finset.subset_union_left) hf

theorem diagram_target_supported {a b : Obj (sig D)} (f : a ⟶ b)
    (hf : diagramColours D f ⊆ J) : wordColours b.word ⊆ J :=
  Finset.Subset.trans (Finset.subset_union_right.trans Finset.subset_union_left) hf

theorem diagram_layer_supported {a b : Obj (sig D)} (f : a ⟶ b)
    (hf : diagramColours D f ⊆ J) (L : Layer (sig D)) (hL : L ∈ Diagram.layers f) :
    layerColours D L ⊆ J := by
  intro i hi
  exact hf (Finset.mem_union_right _ (mem_fold_support D _ L hL i hi ∅))

/-- Restrict a supported list of layers, with no change to its order. -/
def restrictLayers (ls : List (Layer (sig D))) (hl : ∀ L ∈ ls, layerColours D L ⊆ J) :
    List (Layer (sig (D.restrictColours J))) :=
  ls.attach.map fun (L : {L : Layer (sig D) // L ∈ ls}) =>
    restrictLayer D J L.val (hl L.val L.property)

@[simp] theorem layers_restrictLayers (ls : List (Layer (sig D)))
    (hl : ∀ L ∈ ls, layerColours D L ⊆ J) :
    (restrictLayers D J ls hl).map (inclusion D J).layer = ls := by
  simp [restrictLayers, List.map_map]

/-- Chain validity survives restriction of all of its syntax. -/
theorem restrict_chain {a b : Obj (sig D)} (ls : List (Layer (sig D)))
    (hc : Chain a ls b) (ha : wordColours a.word ⊆ J) (hb : wordColours b.word ⊆ J)
    (hl : ∀ L ∈ ls, layerColours D L ⊆ J) :
    Chain (restrictObj D J a ha) (restrictLayers D J ls hl) (restrictObj D J b hb) := by
  apply (inclusion_chain_iff D J _ _ _).mp
  rw [obj_restrictObj, obj_restrictObj, layers_restrictLayers]
  exact hc

/-- The restriction of an arbitrary supported free diagram. -/
def restrictDiagram {a b : Obj (sig D)} (f : a ⟶ b) (hf : diagramColours D f ⊆ J) :
    restrictObj D J a (diagram_source_supported D J f hf) ⟶
      restrictObj D J b (diagram_target_supported D J f hf) :=
  Diagram.mk (restrictLayers D J (Diagram.layers f) (diagram_layer_supported D J f hf))
    (restrict_chain D J _ (Diagram.chain f) _ _ (diagram_layer_supported D J f hf))

/-- Inclusion recovers the complete free expression; the transports use only
proved source and target object equalities. -/
theorem diagram_restrictDiagram {a b : Obj (sig D)} (f : a ⟶ b)
    (hf : diagramColours D f ⊆ J) :
    Diagram.cast ((inclusion D J).toLayerMap.map (restrictDiagram D J f hf))
      (obj_restrictObj D J a _) (obj_restrictObj D J b _) = f := by
  apply Diagram.ext
  exact layers_restrictLayers D J (Diagram.layers f) (diagram_layer_supported D J f hf)

/-- Every supported free diagram has a restricted lift with the full original
layer list recovered by the actual signature inclusion. -/
theorem supported_diagram_lift {a b : Obj (sig D)} (f : a ⟶ b)
    (hf : diagramColours D f ⊆ J) :
    ∃ (a' b' : Obj (sig (D.restrictColours J))) (f' : a' ⟶ b')
      (ha : (inclusion D J).obj a' = a) (hb : (inclusion D J).obj b' = b),
      Diagram.cast ((inclusion D J).toLayerMap.map f') ha hb = f :=
  ⟨_, _, restrictDiagram D J f hf, obj_restrictObj D J a _, obj_restrictObj D J b _,
    diagram_restrictDiagram D J f hf⟩

/-- Inclusion of the raw parameters of superinterchange. -/
def includeInterchange (x : InterchangeData (sig (D.restrictColours J))) :
    InterchangeData (sig D) :=
  ⟨x.start, (inclusion D J).gen x.g, (inclusion D J).word x.mid, (inclusion D J).gen x.h⟩

@[simp] theorem includeInterchange_gh₁ (x : InterchangeData (sig (D.restrictColours J))) :
    (inclusion D J).layer x.gh₁ = (includeInterchange D J x).gh₁ := by
  simp [includeInterchange, InterchangeData.gh₁, SigMap.layer, (inclusion D J).dom]
  rfl

@[simp] theorem includeInterchange_gh₂ (x : InterchangeData (sig (D.restrictColours J))) :
    (inclusion D J).layer x.gh₂ = (includeInterchange D J x).gh₂ := by
  simp [includeInterchange, InterchangeData.gh₂, SigMap.layer, (inclusion D J).cod]
  rfl

@[simp] theorem includeInterchange_hg₁ (x : InterchangeData (sig (D.restrictColours J))) :
    (inclusion D J).layer x.hg₁ = (includeInterchange D J x).hg₁ := by
  simp [includeInterchange, InterchangeData.hg₁, SigMap.layer, (inclusion D J).dom]
  rfl

@[simp] theorem includeInterchange_hg₂ (x : InterchangeData (sig (D.restrictColours J))) :
    (inclusion D J).layer x.hg₂ = (includeInterchange D J x).hg₂ := by
  simp [includeInterchange, InterchangeData.hg₂, SigMap.layer, (inclusion D J).cod]
  rfl

@[simp] theorem includeInterchange_dom (x : InterchangeData (sig (D.restrictColours J))) :
    (inclusion D J).obj x.dom = (includeInterchange D J x).dom := by
  apply Obj.ext
  · rfl
  · simp [includeInterchange, InterchangeData.dom, ColourMap.obj, (inclusion D J).dom]

@[simp] theorem includeInterchange_cod (x : InterchangeData (sig (D.restrictColours J))) :
    (inclusion D J).obj x.cod = (includeInterchange D J x).cod := by
  apply Obj.ext
  · rfl
  · simp [includeInterchange, InterchangeData.cod, ColourMap.obj, (inclusion D J).cod]

/-- The sign is preserved before any specialization of the coefficient ring. -/
@[simp] theorem includeInterchange_sign (x : InterchangeData (sig (D.restrictColours J))) :
    (includeInterchange D J x).sign = x.sign := by
  simp only [InterchangeData.sign, includeInterchange, inclusion_odd]

/-- All four interchange layers have exactly the same validity conditions. -/
theorem includeInterchange_valid_iff (x : InterchangeData (sig (D.restrictColours J))) :
    (includeInterchange D J x).Valid ↔ x.Valid := by
  constructor
  · intro h
    exact ⟨(inclusion_layer_valid_iff D J _).mp (by simpa only [includeInterchange_gh₁] using h.gh₁),
      (inclusion_layer_valid_iff D J _).mp (by simpa only [includeInterchange_gh₂] using h.gh₂),
      (inclusion_layer_valid_iff D J _).mp (by simpa only [includeInterchange_hg₁] using h.hg₁),
      (inclusion_layer_valid_iff D J _).mp (by simpa only [includeInterchange_hg₂] using h.hg₂)⟩
  · intro h
    exact ⟨by simpa only [← includeInterchange_gh₁] using (inclusion D J).layer_valid h.gh₁,
      by simpa only [← includeInterchange_gh₂] using (inclusion D J).layer_valid h.gh₂,
      by simpa only [← includeInterchange_hg₁] using (inclusion D J).layer_valid h.hg₁,
      by simpa only [← includeInterchange_hg₂] using (inclusion D J).layer_valid h.hg₂⟩

/-- Raw support, equal to `allRelColours` for an interchange label. It cannot
be erased by cancellation of the corresponding linear relation. -/
def interchangeColours (x : InterchangeData (sig D)) : Finset I :=
  x.g.1.colours.toFinset ∪ wordColours x.mid ∪ x.h.1.colours.toFinset

theorem allRelColours_interchange {k : Type w} [CommRing k] (Sc : Scalars D k)
    (x : InterchangeData (sig D)) (hv : x.Valid) :
    allRelColours D Sc (.interchange x hv) = interchangeColours D x := rfl

/-- Restrict both vertices and every intervening strand. -/
def restrictInterchange (x : InterchangeData (sig D)) (hx : interchangeColours D x ⊆ J) :
    InterchangeData (sig (D.restrictColours J)) where
  start := x.start
  g := (restrictShape J x.g.1 (fun _ hi => hx
    (Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr hi)))), x.g.2)
  mid := restrictWord J x.mid (fun _ hi => hx
    (Finset.mem_union_left _ (Finset.mem_union_right _ hi)))
  h := (restrictShape J x.h.1 (fun _ hi => hx
    (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))), x.h.2)

@[simp] theorem interchange_restrictInterchange (x : InterchangeData (sig D))
    (hx : interchangeColours D x ⊆ J) :
    includeInterchange D J (restrictInterchange D J x hx) = x := by
  cases x
  simp only [includeInterchange, restrictInterchange, inclusion, shape_restrictShape]
  congr 1
  exact word_restrictWord (X := X) J _ _

/-- Restriction preserves the actual validity witness, not an assumed lift. -/
theorem restrictInterchange_valid (x : InterchangeData (sig D))
    (hx : interchangeColours D x ⊆ J) (hv : x.Valid) :
    (restrictInterchange D J x hx).Valid := by
  apply (includeInterchange_valid_iff D J _).mp
  rw [interchange_restrictInterchange]
  exact hv

/-- Both generating parities are retained, not merely their product. -/
theorem restrictInterchange_odd (x : InterchangeData (sig D))
    (hx : interchangeColours D x ⊆ J) :
    (sig (D.restrictColours J)).odd (restrictInterchange D J x hx).g = (sig D).odd x.g ∧
    (sig (D.restrictColours J)).odd (restrictInterchange D J x hx).h = (sig D).odd x.h := by
  have he := interchange_restrictInterchange D J x hx
  constructor
  · have h := congrArg (fun z : InterchangeData (sig D) => (sig D).odd z.g) he
    exact (inclusion_odd D J _).symm.trans h
  · have h := congrArg (fun z : InterchangeData (sig D) => (sig D).odd z.h) he
    exact (inclusion_odd D J _).symm.trans h

@[simp] theorem restrictInterchange_sign (x : InterchangeData (sig D))
    (hx : interchangeColours D x ⊆ J) :
    (restrictInterchange D J x hx).sign = x.sign := by
  rw [← includeInterchange_sign D J, interchange_restrictInterchange]

/-- Both complete layer lists of superinterchange commute with inclusion. -/
theorem includeInterchange_layers (x : InterchangeData (sig (D.restrictColours J))) :
    [x.gh₁, x.gh₂].map (inclusion D J).layer =
      [(includeInterchange D J x).gh₁, (includeInterchange D J x).gh₂] ∧
    [x.hg₁, x.hg₂].map (inclusion D J).layer =
      [(includeInterchange D J x).hg₁, (includeInterchange D J x).hg₂] := by
  simp only [List.map_cons, List.map_nil, includeInterchange_gh₁, includeInterchange_gh₂,
    includeInterchange_hg₁, includeInterchange_hg₂, and_self]

/-- The entire signed linear relation commutes with inclusion. -/
theorem includeInterchange_rel {k : Type w} [CommRing k]
    (x : InterchangeData (sig (D.restrictColours J))) (hv : x.Valid) :
    LinDiagram.cast ((inclusion D J).toLayerMap.lin (InterchangeData.rel k hv))
      (includeInterchange_dom D J x) (includeInterchange_cod D J x) =
      InterchangeData.rel k ((includeInterchange_valid_iff D J x).mpr hv) := by
  have hgh : Diagram.cast ((inclusion D J).toLayerMap.map (InterchangeData.ghDiagram hv))
      (includeInterchange_dom D J x) (includeInterchange_cod D J x) =
      InterchangeData.ghDiagram ((includeInterchange_valid_iff D J x).mpr hv) :=
    Diagram.ext (includeInterchange_layers D J x).1
  have hhg : Diagram.cast ((inclusion D J).toLayerMap.map (InterchangeData.hgDiagram hv))
      (includeInterchange_dom D J x) (includeInterchange_cod D J x) =
      InterchangeData.hgDiagram ((includeInterchange_valid_iff D J x).mpr hv) :=
    Diagram.ext (includeInterchange_layers D J x).2
  simp only [InterchangeData.rel, LayerMap.lin_sub, LayerMap.lin_smul, LayerMap.lin_of,
    LinDiagram.cast_sub, LinDiagram.cast_smul, LinDiagram.cast_of, hgh, hhg,
    includeInterchange_sign]

private theorem includeInterchange_rel_of_eq {k : Type w} [CommRing k]
    (y : InterchangeData (sig (D.restrictColours J))) (hy : y.Valid)
    (x : InterchangeData (sig D)) (hv : x.Valid) (he : includeInterchange D J y = x) :
    LinDiagram.cast ((inclusion D J).toLayerMap.lin (InterchangeData.rel k hy))
      ((includeInterchange_dom D J y).trans (congrArg InterchangeData.dom he))
      ((includeInterchange_cod D J y).trans (congrArg InterchangeData.cod he)) =
      InterchangeData.rel k hv := by
  cases he
  exact includeInterchange_rel D J y hy

/-- A supported valid interchange has a finite-subtype presentation relation
whose inclusion recovers the complete signed linear expression. -/
theorem supported_interchange_lift {k : Type w} [CommRing k]
    (x : InterchangeData (sig D)) (hx : interchangeColours D x ⊆ J) (hv : x.Valid) :
    ∃ (y : InterchangeData (sig (D.restrictColours J))) (hy : y.Valid)
      (ha : (inclusion D J).obj y.dom = x.dom) (hb : (inclusion D J).obj y.cod = x.cod),
      includeInterchange D J y = x ∧ y.sign = x.sign ∧
      [y.gh₁, y.gh₂].map (inclusion D J).layer = [x.gh₁, x.gh₂] ∧
      [y.hg₁, y.hg₂].map (inclusion D J).layer = [x.hg₁, x.hg₂] ∧
      LinDiagram.cast ((inclusion D J).toLayerMap.lin (InterchangeData.rel k hy)) ha hb =
        InterchangeData.rel k hv := by
  let y := restrictInterchange D J x hx
  have hy := restrictInterchange_valid D J x hx hv
  have he : includeInterchange D J y = x := interchange_restrictInterchange D J x hx
  have ha := (includeInterchange_dom D J y).trans (congrArg InterchangeData.dom he)
  have hb := (includeInterchange_cod D J y).trans (congrArg InterchangeData.cod he)
  refine ⟨y, hy, ha, hb, he, restrictInterchange_sign D J x hx, ?_, ?_, ?_⟩
  · exact (includeInterchange_layers D J y).1.trans (congrArg (fun z => [z.gh₁, z.gh₂]) he)
  · exact (includeInterchange_layers D J y).2.trans (congrArg (fun z => [z.hg₁, z.hg₂]) he)
  · exact includeInterchange_rel_of_eq D J y hy x hv he

end OddMath.SKM.FiniteColour
