/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.UpwardModuleAction
import StringDiagrams.LocalInterpretation

/-! # Layer representations and the relation obligations of the presentation

A *layer representation* of a signature assigns a module to every object and a linear map
`M L.dom → M L.cod` to every layer. Ext/restriction along the product of all the modules
makes it a `LocalInterpretation` (`LayerRep.toLocal`), so it gives a functor out of the free
2-category.

For the signature of `𝔘(𝔤)` (Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Definition 1.5) this file splits the soundness hypotheses of
`StringDiagrams.LocalInterpretation.respects_of` into named obligations, one for each group
of relations of `SKM.Rel` together with the interchange law:

* `QuadRelations`: `quadEq`, `quadZero`, `quadNe` ((1.7));
* `SlideRelations`: `slideL`, `slideLEq`, `slideR`, `slideREq` ((1.8));
* `BraidRelations`: `braid`, `braidEq` ((1.9));
* `ZigzagRelations`: `zigE`, `zigF` (the right adjunction (1.10));
* `InversionRelations`: `invNe₁`, `invNe₂`, `invP₁`–`invP₅`, `invM₁`–`invM₅`
  ((1.11)–(1.14), stated with the leftward crossing and the `♦`-cups and caps of (2.6));
* `WindowZeroRelations`: `dcupZero`, `dcapZero` (the vanishing `♦`-cups and caps of (2.6));
* `InterchangeLaw`: the super interchange law of the free 2-supercategory.

The leftward crossing `σ` of the source is the generator `Shape.lcross`; there is no separate
relation for it, since it is defined in the presentation through the inversion relations.

`SwappedObligations.upwardModuleAction` turns the seven obligations into an
`UpwardModuleAction` through `Presentation.lift`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams

universe u w w₀ w₁ w₂ w₃

/-- A representation of the layers of a signature: a module for every object and a linear map
for every layer. Only the maps of well-formed layers enter the functor. -/
structure LayerRep (S : Signature.{w₀, w₁, w₂}) (R : Type w) [CommRing R] where
  /-- The module of an object. -/
  M : Obj S → Type w₃
  [addM : ∀ a, AddCommGroup (M a)]
  [moduleM : ∀ a, Module R (M a)]
  /-- The map of a layer. -/
  act : ∀ L : Layer S, M L.dom →ₗ[R] M L.cod

attribute [instance] LayerRep.addM LayerRep.moduleM

namespace LayerRep

variable {S : Signature.{w₀, w₁, w₂}} {R : Type w} [CommRing R] (Q : LayerRep.{w, w₀, w₁, w₂, w₃} S R)

open Classical in
/-- A layer representation as a local interpretation on the product of all its modules. -/
def toLocal : LocalInterpretation S R (∀ a, Q.M a) Q.M where
  κ a := a
  ext a := LinearMap.single R Q.M a
  res a := LinearMap.proj a
  op L := LinearMap.single R Q.M L.cod ∘ₗ Q.act L ∘ₗ LinearMap.proj L.dom
  res_comp_ext a := by ext; simp
  res_op_ext_res L _ := by ext; simp

@[simp] theorem toLocal_κ (a : Obj S) : Q.toLocal.κ a = a := rfl

/-- The image of a layer under the local interpretation is the map of the layer. -/
theorem toLocal_layer (L : Layer S) (x : Q.M L.dom) :
    Q.toLocal.res L.cod (Q.toLocal.op L (Q.toLocal.ext L.dom x)) = Q.act L x := by
  classical
  simp [toLocal]

end LayerRep

section SKM

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : SKM.Datum I X} {Sc : SKM.Scalars D k}

/-- The groups of relations of `SKM.Rel`, one for each named obligation. -/
inductive RelGroup
  | quad
  | slide
  | braid
  | zigzag
  | inversion
  | windowZero
  deriving DecidableEq

/-- The group of a relation. -/
def relGroup : SKM.Rel D → RelGroup
  | .quadEq .. | .quadZero .. | .quadNe .. => .quad
  | .slideL .. | .slideLEq .. | .slideR .. | .slideREq .. => .slide
  | .braid .. | .braidEq .. => .braid
  | .zigE .. | .zigF .. => .zigzag
  | .invNe₁ .. | .invNe₂ .. | .invP₁ .. | .invP₂ .. | .invP₃ .. | .invP₄ .. | .invP₅ ..
  | .invM₁ .. | .invM₂ .. | .invM₃ .. | .invM₄ .. | .invM₅ .. => .inversion
  | .dcupZero .. | .dcapZero .. => .windowZero

variable (Sc) (Q : LayerRep.{u, u, u, u, w₃} (SKM.sig D) k)

/-- A relation holds in a layer representation: its whiskered evaluation vanishes. -/
def RelHolds (r : SKM.Rel D) : Prop :=
  ∀ (u : Obj (SKM.sig D)) (v : List (SKM.sig D).Colour),
    ((SKM.pres D Sc).dom r).WhiskerOK u v →
    Q.toLocal.evalW (((SKM.pres D Sc).dom r).whisker u v)
      (((SKM.pres D Sc).cod r).whisker u v) u v ((SKM.pres D Sc).rel r) = 0

/-- All relations of one group hold. -/
def GroupHolds (g : RelGroup) : Prop := ∀ r : SKM.Rel D, relGroup r = g → RelHolds Sc Q r

/-- (1.7): `quadEq`, `quadZero`, `quadNe`. -/
abbrev QuadRelations : Prop := GroupHolds Sc Q .quad
/-- (1.8): `slideL`, `slideLEq`, `slideR`, `slideREq`. -/
abbrev SlideRelations : Prop := GroupHolds Sc Q .slide
/-- (1.9): `braid`, `braidEq`. -/
abbrev BraidRelations : Prop := GroupHolds Sc Q .braid
/-- The right adjunction (1.10): `zigE`, `zigF`. -/
abbrev ZigzagRelations : Prop := GroupHolds Sc Q .zigzag
/-- (1.11)–(1.14): `invNe₁`, `invNe₂`, `invP₁`–`invP₅`, `invM₁`–`invM₅`. -/
abbrev InversionRelations : Prop := GroupHolds Sc Q .inversion
/-- (2.6): `dcupZero`, `dcapZero`. -/
abbrev WindowZeroRelations : Prop := GroupHolds Sc Q .windowZero

/-- The super interchange law, whiskered. -/
def InterchangeLaw : Prop :=
  ∀ (x : InterchangeData (SKM.sig D)) (hx : x.Valid) (u : Obj (SKM.sig D))
    (v : List (SKM.sig D).Colour), x.dom.WhiskerOK u v →
    Q.toLocal.evalW (x.dom.whisker u v) (x.cod.whisker u v) u v
      (InterchangeData.rel k hx) = 0

/-- The obligations of the assembly: every relation group and the interchange law. -/
structure SwappedObligations : Prop where
  quad : QuadRelations Sc Q
  slide : SlideRelations Sc Q
  braid : BraidRelations Sc Q
  zigzag : ZigzagRelations Sc Q
  inversion : InversionRelations Sc Q
  windowZero : WindowZeroRelations Sc Q
  interchange : InterchangeLaw Q

namespace SwappedObligations

variable {Sc Q} (h : SwappedObligations Sc Q)
include h

theorem relHolds (r : SKM.Rel D) : RelHolds Sc Q r := by
  cases hg : relGroup r
  · exact h.quad r hg
  · exact h.slide r hg
  · exact h.braid r hg
  · exact h.zigzag r hg
  · exact h.inversion r hg
  · exact h.windowZero r hg

/-- The obligations give soundness for the presentation. -/
theorem respects : (SKM.pres D Sc).Respects Q.toLocal.functor :=
  Q.toLocal.respects_of (SKM.pres D Sc) (fun r u v hw => h.relHolds r u v hw)
    (fun x hx u v hw => h.interchange x hx u v hw)

/-- The functor out of the presented 2-category. -/
def functor : (SKM.pres D Sc).Presented ⥤ ModuleCat.{w₃} k := (SKM.pres D Sc).lift h.respects

@[simp] theorem functor_obj (a : Obj (SKM.sig D)) :
    h.functor.obj ((SKM.pres D Sc).obj a) = ModuleCat.of k (Q.M a) := rfl

instance : h.functor.Additive := Presentation.lift_additive h.respects

instance : h.functor.Linear k := Presentation.lift_linear h.respects

/-- **The upward module action at rightmost weight `μ`** obtained from the obligations. -/
def upwardModuleAction (μ : X) : UpwardModuleAction D Sc μ where
  V t := Q.M (SKM.ob D μ (upWord t))
  act t t' :=
    { toFun f := (h.functor.map f).hom
      map_add' f g := by rw [Functor.map_add, ModuleCat.hom_add]
      map_smul' r f := by rw [Functor.map_smul, ModuleCat.hom_smul]; rfl }
  act_id t := by
    ext x
    simp
  act_comp t t' t'' f g := by
    ext x
    simp

theorem upwardModuleAction_act (μ : X) (t t' : List I) (f : UpwardHom D Sc μ t t') :
    (h.upwardModuleAction μ).act t t' f = (h.functor.map f).hom := rfl

end SwappedObligations

end SKM

end OddMath.QuiverHecke.SwappedAssembly
