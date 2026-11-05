/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.FunctorCategory

/-! # Homogeneous isomorphisms of superfunctors

The pointwise inverse construction for homogeneous supernatural transformations,
needed by Brundan–Ellis (1.12) both for old-module morphisms and for naturality
in the input module. Pointwise inverse maps have the same parity; their
naturality follows by cancellation from the twisted naturality of the forward
maps. No evenness hypothesis is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.HomogeneousSuperfunctorIso
universe w u₁ v₁ u₂ v₂
variable {k : Type w} [CommRing k]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C] [Supercategory k C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear k D] [Supercategory k D]
  {F G : Superfunctor k C D}

/-- Total components detect maps between superfunctors into any supercategory. -/
theorem total_ext {f g : F ⟶ G} (h : ∀ X, f.total X = g.total X) : f = g := by
  apply Superfunctor.hom_ext
  intro p X
  have hp (s : F ⟶ G) : proj k p (s.total X) = s.app p X := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · exact proj_eq_of_add rfl (s.app_mem 0 X) (s.app_mem 1 X)
    · exact proj_eq_of_add (add_comm _ _) (s.app_mem 1 X)
        (by simpa only [SuperNatTrans.zmod2_one_add_one] using s.app_mem 0 X)
  rw [← hp f, ← hp g, h X]

/-- The total of a homogeneous map is its specified homogeneous component. -/
theorem total_eq_app {p : ZMod 2} (f : F ⟶ G)
    (hf : f ∈ parity (R := k) F G p) (X : C) : f.total X = f.app p X := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · change f.app 0 X + f.app 1 X = f.app 0 X
    rw [Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) X, add_zero]
  · change f.app 0 X + f.app 1 X = f.app 1 X
    rw [Superfunctor.app_eq_zero_of_mem hf (by decide : (0 : ZMod 2) ≠ 1) X, zero_add]

/-- An inverse family has the same supernatural parity as its forward family. -/
theorem inverseSupernatural {p : ZMod 2} (e : ∀ X, F.obj X ≅ G.obj X)
    (h : IsSupernatural k p (F := F.toFunctor) (G := G.toFunctor) (fun X => (e X).hom)) :
    IsSupernatural k p (F := G.toFunctor) (G := F.toFunctor) (fun X => (e X).inv) :=
  IsSupernatural.of_twist (fun X => inv_mem (e X) (h.mem X)) fun {X Y} f => by
    apply (cancel_mono (e Y).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h.naturality_twist (twist k p f), twist_twist]
    simp

/-- Turning a homogeneous family into a supernatural map preserves its total. -/
@[simp] theorem homogeneous_total {p : ZMod 2}
    {x : ∀ X, F.obj X ⟶ G.obj X}
    (h : IsSupernatural k p (F := F.toFunctor) (G := G.toFunctor) x) (X : C) :
    h.toSuperNatTrans.total X = x X := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans]

/-- Pointwise homogeneous isomorphisms form an isomorphism of superfunctors. -/
def ofComponents {p : ZMod 2} (e : ∀ X, F.obj X ≅ G.obj X)
    (h : IsSupernatural k p (F := F.toFunctor) (G := G.toFunctor) (fun X => (e X).hom)) :
    F ≅ G where
  hom := h.toSuperNatTrans
  inv := (inverseSupernatural e h).toSuperNatTrans
  hom_inv_id := by
    apply total_ext
    intro X
    change (h.toSuperNatTrans.vcomp (inverseSupernatural e h).toSuperNatTrans).total X =
      (SuperNatTrans.id F.toFunctor).total X
    rw [SuperNatTrans.vcomp_total, homogeneous_total, homogeneous_total, SuperNatTrans.id_total]
    exact (e X).hom_inv_id
  inv_hom_id := by
    apply total_ext
    intro X
    change ((inverseSupernatural e h).toSuperNatTrans.vcomp h.toSuperNatTrans).total X =
      (SuperNatTrans.id G.toFunctor).total X
    rw [SuperNatTrans.vcomp_total, homogeneous_total, homogeneous_total, SuperNatTrans.id_total]
    exact (e X).inv_hom_id

@[simp] theorem ofComponents_hom_total {p : ZMod 2} (e : ∀ X, F.obj X ≅ G.obj X)
    (h : IsSupernatural k p (F := F.toFunctor) (G := G.toFunctor) (fun X => (e X).hom)) (X : C) :
    (ofComponents e h).hom.total X = (e X).hom := homogeneous_total h X

@[simp] theorem ofComponents_inv_total {p : ZMod 2} (e : ∀ X, F.obj X ≅ G.obj X)
    (h : IsSupernatural k p (F := F.toFunctor) (G := G.toFunctor) (fun X => (e X).hom)) (X : C) :
    (ofComponents e h).inv.total X = (e X).inv := homogeneous_total (inverseSupernatural e h) X

/-- The forward map retains its specified parity. -/
theorem ofComponents_hom_mem {p : ZMod 2} (e : ∀ X, F.obj X ≅ G.obj X)
    (h : IsSupernatural k p (F := F.toFunctor) (G := G.toFunctor) (fun X => (e X).hom)) :
    (ofComponents e h).hom ∈ parity (R := k) F G p :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr h.toSuperNatTrans_isHomogeneous

/-- Reassemble a given homogeneous map from isomorphisms of its total components. -/
def ofHom {p : ZMod 2} (f : F ⟶ G) (hf : f ∈ parity (R := k) F G p)
    (e : ∀ X, F.obj X ≅ G.obj X) (he : ∀ X, (e X).hom = f.total X) : F ≅ G :=
  ofComponents e (by
    have h := f.isSupernatural p
    have hx : (fun X => (e X).hom) = f.app p := by
      funext X
      exact (he X).trans (total_eq_app f hf X)
    exact hx.symm ▸ h)

/-- The constructed isomorphism has exactly the prescribed homogeneous forward map. -/
@[simp] theorem ofHom_hom {p : ZMod 2} (f : F ⟶ G) (hf : f ∈ parity (R := k) F G p)
    (e : ∀ X, F.obj X ≅ G.obj X) (he : ∀ X, (e X).hom = f.total X) :
    (ofHom f hf e he).hom = f := by
  apply total_ext
  intro X
  exact (ofComponents_hom_total e _ X).trans (he X)

@[simp] theorem ofHom_inv_total {p : ZMod 2} (f : F ⟶ G) (hf : f ∈ parity (R := k) F G p)
    (e : ∀ X, F.obj X ≅ G.obj X) (he : ∀ X, (e X).hom = f.total X) (X : C) :
    (ofHom f hf e he).inv.total X = (e X).inv := ofComponents_inv_total e _ X

@[simp] theorem ofHom_hom_inv_id {p : ZMod 2} (f : F ⟶ G) (hf : f ∈ parity (R := k) F G p)
    (e : ∀ X, F.obj X ≅ G.obj X) (he : ∀ X, (e X).hom = f.total X) :
    f ≫ (ofHom f hf e he).inv = 𝟙 F := by
  simpa only [ofHom_hom] using (ofHom f hf e he).hom_inv_id

@[simp] theorem ofHom_inv_hom_id {p : ZMod 2} (f : F ⟶ G) (hf : f ∈ parity (R := k) F G p)
    (e : ∀ X, F.obj X ≅ G.obj X) (he : ∀ X, (e X).hom = f.total X) :
    (ofHom f hf e he).inv ≫ f = 𝟙 G := by
  simpa only [ofHom_hom] using (ofHom f hf e he).inv_hom_id

end OddMath.HomogeneousSuperfunctorIso
