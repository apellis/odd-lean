/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.ChevalleyGrading
import OddMath.SKM.SOpGrading
import OddMath.SKM.Envelope
import OddMath.SKM.ChevalleyInv

/-!
# The faithful graded Chevalley hom functor

`chevHom` restricts the original `omega` to each actual `UGr` hom category,
with weight-negated Koszul super-opposite target. Its square proves faithfulness;
its original parity and integer-degree preservation supply the forward functor
of `chevHomGradedEquivalence`.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Supercategory GradedSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

/-- Original negation of weight objects. -/
def negWeight (a : UGr D Sc sy hc) : UGr D Sc sy hc := ⟨-(show X from a.region)⟩

/-- Original Chevalley word with its actual endpoints. -/
def chevHomObj {a b : UGr D Sc sy hc} (f : a ⟶ b) : negWeight a ⟶ negWeight b where
  obj := (chevMap D).obj f.obj
  start_eq := congrArg (fun x : X => -x) f.start_eq
  wf := (chevMap D).ok_map f.wf
  endR_eq := ((chevMap D).obj_endR f.obj).trans (congrArg (fun x : X => -x) f.endR_eq)

/-- Restriction of the original omega to a genuine hom category. -/
def chevHom (a b : UGr D Sc sy hc) : (a ⟶ b) ⥤ SOp k (negWeight a ⟶ negWeight b) where
  obj f := ⟨chevHomObj f⟩
  map f := SOp.mk' (SOp.unsop (C := (pres D Sc).Presented) ((omega Sc).map f))
  map_id f := by
    apply SOp.hom_ext
    change SOp.unsop ((omega Sc).map (𝟙 ((pres D Sc).obj f.obj))) = 𝟙 _
    exact congrArg (SOp.unsop (C := (pres D Sc).Presented)) ((omega Sc).map_id _)
  map_comp {f g h} x y := by
    apply SOp.hom_ext
    change SOp.unsop (C := (pres D Sc).Presented) ((omega Sc).map (x ≫ y)) = _
    erw [Functor.map_comp]
    rfl

instance chevHom_additive (a b : UGr D Sc sy hc) : (chevHom a b).Additive where
  map_add {f g} x y := by
    apply SOp.hom_ext
    change SOp.unsop ((omega Sc).map (x + y)) =
      SOp.unsop ((omega Sc).map x) + SOp.unsop ((omega Sc).map y)
    exact congrArg (SOp.unsop (C := (pres D Sc).Presented))
      ((omega Sc).map_add (f := x) (g := y))

instance chevHom_linear (a b : UGr D Sc sy hc) : (chevHom a b).Linear k where
  map_smul {f g} x r := by
    apply SOp.hom_ext
    change SOp.unsop ((omega Sc).map (r • x)) = r • SOp.unsop ((omega Sc).map x)
    exact congrArg (SOp.unsop (C := (pres D Sc).Presented)) ((omega Sc).map_smul r x)

/-- The restriction is the original action, not a replacement equivalence. -/
theorem chevHom_map {a b : UGr D Sc sy hc} {f g : a ⟶ b} (x : f ⟶ g) :
    SOp.unsop ((chevHom a b).map x) =
      (show (chevHomObj g ⟶ chevHomObj f) from
        SOp.unsop (C := (pres D Sc).Presented) ((omega Sc).map x)) := rfl

instance chevHom_super (a b : UGr D Sc sy hc) : IsSuperfunctor k (chevHom a b) where
  map_mem {f g p x} hx := by
    change SOp.unsop ((omega Sc).map x) ∈
      parity (R := k) ((pres D Sc).obj ((chevMap D).obj g.obj))
        ((pres D Sc).obj ((chevMap D).obj f.obj)) p
    exact SOp.mem_parity_iff.mp (omega_mem hx)

instance chevHom_graded (a b : UGr D Sc sy hc) : IsGradedSuperfunctor k (chevHom a b) where
  map_mem_degree {f g n x} hx := by
    change SOp.unsop ((omega Sc).map x) ∈
      (pres D Sc).homDeg (gdeg D sy) ((chevMap D).obj g.obj) ((chevMap D).obj f.obj) n
    exact omega_mem_gdeg sy hx

/-- Any genuine word is its original signed-word normal form, at its end weight. -/
theorem homObj_normal {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    f.obj = ob D b.region (f.obj.word.map Col.l) := by
  obtain ⟨hw, hs⟩ := word_eq_wd (D := D) f.obj.start f.obj.word f.wf
  change f.obj.word = wd D f.obj.endR _ at hw
  change f.obj.start = wt D f.obj.endR _ at hs
  rw [f.endR_eq] at hw hs
  exact Obj.ext hs hw

/-- The original relabelling is involutive on all colour words. -/
theorem chevObj_square (f : Obj (sig D)) : (chevMap D).obj ((chevMap D).obj f) = f := by
  obtain ⟨r, s⟩ := f
  apply Obj.ext
  · exact neg_neg (show X from r)
  · change List (Col I X) at s
    change (s.map chevColour).map chevColour = s
    simp only [List.map_map]
    have h : (chevColour (I := I) (X := X)) ∘ chevColour = id := by
      funext c
      obtain ⟨l, r⟩ := c
      simp [chevColour, flipL_flipL]
    rw [h, List.map_id]

private theorem omega_square_of_normal {F G : Obj (sig D)} {μ : X}
    {s t : List (Letter I)} (hf : F = ob D μ s) (hg : G = ob D μ t)
    (x : (pres D Sc).obj F ⟶ (pres D Sc).obj G) :
    SOp.unsop ((omega Sc).map (SOp.unsop ((omega Sc).map x))) =
      eqToHom (congrArg (pres D Sc).obj (chevObj_square F)) ≫ x ≫
        eqToHom (congrArg (pres D Sc).obj (chevObj_square G)).symm := by
  subst F G
  exact omega_omega x

/-- Reuse the established original square identity on actual arbitrary homs. -/
theorem chevHom_square {a b : UGr D Sc sy hc} {f g : a ⟶ b} (x : f ⟶ g) :
    SOp.unsop ((omega Sc).map (SOp.unsop ((omega Sc).map x))) =
      eqToHom (congrArg (pres D Sc).obj (chevObj_square f.obj)) ≫ x ≫
        eqToHom (congrArg (pres D Sc).obj (chevObj_square g.obj)).symm := by
  exact omega_square_of_normal (homObj_normal f) (homObj_normal g) x

instance chevHom_faithful (a b : UGr D Sc sy hc) : (chevHom a b).Faithful where
  map_injective {f g} x y h := by
    change (pres D Sc).Bicat at a b
    change (pres D Sc).obj f.obj ⟶ (pres D Sc).obj g.obj at x y
    have h' := congrArg (SOp.unsop (C := (negWeight a ⟶ negWeight b))) h
    change SOp.unsop ((omega Sc).map x) = SOp.unsop ((omega Sc).map y) at h'
    have h'' := congrArg (fun z => SOp.unsop ((omega Sc).map z)) h'
    rw [chevHom_square x, chevHom_square y] at h''
    have h''' := congrArg (fun z =>
      eqToHom (congrArg (pres D Sc).obj (chevObj_square f.obj)).symm ≫ z ≫
        eqToHom (congrArg (pres D Sc).obj (chevObj_square g.obj))) h''
    change @Eq ((pres D Sc).obj f.obj ⟶ (pres D Sc).obj g.obj) x y
    simpa [Category.assoc] using h'''

end OddMath.SKM
