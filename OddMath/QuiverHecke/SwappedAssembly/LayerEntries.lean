/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Matrices

/-! # Entries of composites of layers in the swapped layer representation

Tools for computing the swapped layer representation of
`OddMath/QuiverHecke/SwappedAssembly/Matrices.lean` on composites of layers, as needed for the
relation obligations of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Definition 1.5:

* the path functors are linear superfunctors (`pathFunctor_map_smul`, `pathFunctor_map_mem`);
* the entry of a layer at an output path given as an explicit concatenation `pu · p' · pv` is
  the sum over the paths `p` of the bottom boundary of the generator (`layerMap_apply_append`);
* transport of matrix entries along an equality of objects (`Mod.cast_apply`), and the
  interpretation of `LayerRep.toLocal` on two composable layers between objects that are only
  propositionally equal to their boundaries (`LayerRep.res_op_op_ext`).

The junction objects of a composite of layers coincide with the boundaries of the layers only
up to reassociation of words; these lemmas move the resulting transports onto summand paths,
where `SPath.append_assoc_heq` removes them.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams Supercategory OddMath.SKM

universe u

namespace SPath

variable {I X : Type u} [AddCommGroup X]

omit [AddCommGroup X] in
/-- Concatenation of summand paths is associative up to the reassociation of words. -/
theorem append_assoc_heq : {l m r : List (Col I X)} → {s t t' t'' : Sector I} →
    (p : SPath l s t) → (q : SPath m t t') → (q' : SPath r t' t'') →
    HEq ((p.append q).append q') (p.append (q.append q'))
  | _, _, _, _, _, _, _, .nil _, _, _ => HEq.rfl
  | _ :: l, m, r, _, _, _, _, .cons c side s hv p, q, q' => by
    have h := append_assoc_heq p q q'
    change HEq (SPath.cons c side s hv ((p.append q).append q'))
      (SPath.cons c side s hv (p.append (q.append q')))
    have hw : l ++ m ++ r = l ++ (m ++ r) := List.append_assoc l m r
    revert h
    generalize (p.append q).append q' = a
    generalize p.append (q.append q') = b
    revert a
    rw [hw]
    intro a h
    rw [eq_of_heq h]

omit [AddCommGroup X] in
/-- Concatenation respects heterogeneous equality of the right factor. -/
theorem append_heq_right {l m m' : List (Col I X)} {s t r : Sector I} (p : SPath l s t)
    {q : SPath m t r} {q' : SPath m' t r} (hm : m = m') (hq : HEq q q') :
    HEq (p.append q) (p.append q') := by
  subst hm
  rw [eq_of_heq hq]

omit [AddCommGroup X] in
/-- Concatenation respects heterogeneous equality of the left factor. -/
theorem append_heq_left {l l' m : List (Col I X)} {s t r : Sector I} {p : SPath l s t}
    {p' : SPath l' s t} (q : SPath m t r) (hl : l = l') (hp : HEq p p') :
    HEq (p.append q) (p'.append q) := by
  subst hl
  rw [eq_of_heq hp]

omit [AddCommGroup X] in
/-- Every path of a concatenated word is the concatenation of its two parts. -/
theorem exists_eq_append (l : List (Col I X)) {m : List (Col I X)} {s r : Sector I}
    (q : SPath (l ++ m) s r) : ∃ (t : Sector I) (p : SPath l s t) (p' : SPath m t r),
      q = p.append p' :=
  ⟨(split l q).1, (split l q).2.1, (split l q).2.2, (append_split l q).symm⟩

end SPath

namespace LayerRep

/-- Restriction to an index of the inclusion of an equal index is the transport along the
equality. -/
theorem proj_single_of_eq {S : Signature.{u, u, u}} {R : Type u} [CommRing R]
    (Q : LayerRep.{u, u, u, u, u} S R) {_ : DecidableEq (Obj S)} {a b : Obj S} (h : a = b)
    (y : Q.M a) : LinearMap.proj (R := R) (φ := Q.M) b (LinearMap.single R Q.M a y) =
      cast (congrArg Q.M h) y := by
  subst h
  simp

/-- The composite of two layers in the local interpretation of a layer representation, between
indices that are only propositionally equal to the boundaries of the layers. -/
theorem res_op_op_ext {S : Signature.{u, u, u}} {R : Type u} [CommRing R]
    (Q : LayerRep.{u, u, u, u, u} S R) {a c : Obj S} (L₁ L₂ : Layer S) (h₁ : a = L₁.dom)
    (h₂ : L₁.cod = L₂.dom) (h₃ : L₂.cod = c) (x : Q.M a) :
    Q.toLocal.res c (Q.toLocal.op L₂ (Q.toLocal.op L₁ (Q.toLocal.ext a x))) =
      cast (congrArg Q.M h₃) (Q.act L₂ (cast (congrArg Q.M h₂)
        (Q.act L₁ (cast (congrArg Q.M h₁) x)))) := by
  simp only [toLocal, LinearMap.comp_apply]
  rw [proj_single_of_eq Q h₁, proj_single_of_eq Q h₂, proj_single_of_eq Q h₃]

/-- Transport of zero is zero. -/
theorem cast_zero {S : Signature.{u, u, u}} {R : Type u} [CommRing R]
    (Q : LayerRep.{u, u, u, u, u} S R) {a a' : Obj S} (h : a = a') :
    cast (congrArg Q.M h) 0 = 0 := by
  subst h; rfl

end LayerRep

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-- The Hom-sector functor of one strand is additive. -/
private instance step_additive (l : Letter I) (side : Bool) (s : Sector I)
    (hv : StepValid l side s) : (P.step l side s hv).Additive := by
  obtain ⟨_ | _, i⟩ := l <;> cases side <;>
    (dsimp only [step, homContentPreE, homContentPreF]; infer_instance)

/-- The Hom-sector functor of a path is additive. -/
private instance pathFunctor_additive :
    {w : List (Col I X)} → {s t : Sector I} → (p : SPath w s t) → (P.pathFunctor p).Additive
  | _, _, _, .nil _ => by rw [pathFunctor_nil]; infer_instance
  | _, _, _, .cons c side s hv p => by
    have := pathFunctor_additive p
    rw [pathFunctor_cons]; infer_instance

/-- The Hom-sector functor of one strand is linear. -/
private instance step_linear (l : Letter I) (side : Bool) (s : Sector I) (hv : StepValid l side s) :
    (P.step l side s hv).Linear k := by
  obtain ⟨_ | _, i⟩ := l <;> cases side <;>
    (dsimp only [step, homContentPreE, homContentPreF]; infer_instance)

/-- The Hom-sector functor of one strand is a superfunctor. -/
private instance step_isSuperfunctor (l : Letter I) (side : Bool) (s : Sector I)
    (hv : StepValid l side s) : IsSuperfunctor k (P.step l side s hv) := by
  obtain ⟨_ | _, i⟩ := l <;> cases side <;>
    (dsimp only [step, homContentPreE, homContentPreF, homContentPostE, homContentPostF];
      infer_instance)

/-- The Hom-sector functor of a path is linear. -/
private instance pathFunctor_linear :
    {w : List (Col I X)} → {s t : Sector I} → (p : SPath w s t) → (P.pathFunctor p).Linear k
  | _, _, _, .nil _ => by rw [pathFunctor_nil]; infer_instance
  | _, _, _, .cons c side s hv p => by
    have := pathFunctor_linear p
    rw [pathFunctor_cons]; infer_instance

/-- The Hom-sector functor of a path is a superfunctor. -/
private instance pathFunctor_isSuperfunctor :
    {w : List (Col I X)} → {s t : Sector I} → (p : SPath w s t) →
      IsSuperfunctor k (P.pathFunctor p)
  | _, _, _, .nil _ => ⟨fun hf => hf⟩
  | _, _, _, .cons c side s hv p => by
    have := pathFunctor_isSuperfunctor p
    exact ⟨fun hf => IsSuperfunctor.map_mem (F := P.step c.l side s hv)
      (IsSuperfunctor.map_mem (F := P.pathFunctor p) hf)⟩

/-- The Hom-sector functor of a path commutes with scalars. -/
theorem pathFunctor_map_smul {w : List (Col I X)} {s t : Sector I} (p : SPath w s t)
    {Y Z : P.H t} (c : k) (f : Y ⟶ Z) :
    (P.pathFunctor p).map (c • f) = c • (P.pathFunctor p).map f :=
  Functor.map_smul _ _ _

/-- The Hom-sector functor of a path preserves parities. -/
theorem pathFunctor_map_mem {w : List (Col I X)} {s t : Sector I} (p : SPath w s t)
    {Y Z : P.H t} {q : ZMod 2} {f : Y ⟶ Z} (hf : f ∈ parity (R := k) Y Z q) :
    (P.pathFunctor p).map f ∈ parity (R := k) _ _ q :=
  IsSuperfunctor.map_mem hf

section Entries

variable {P} {Gs Ys : ∀ s, P.H s}

omit [∀ a b : B, Linear k (a ⟶ b)] [∀ a b : B, Supercategory k (a ⟶ b)]
  [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- A family of morphisms followed by `eqToHom` does not depend on the index up to equality. -/
theorem comp_eqToHom_congr {C : Type*} [Category C] {α : Sort*} {W Y : C} {T : α → C}
    (E : ∀ a, W ⟶ T a) {a b : α} (h : a = b) (h₁ : T a = Y) (h₂ : T b = Y) :
    E a ≫ eqToHom h₁ = E b ≫ eqToHom h₂ := by
  subst h
  rfl

open Classical in
/-- **The entry of a layer at an explicit concatenation** `pu · p' · pv` of a path of the
left whisker, a path of the top boundary of the generator and a path of the right whisker: the
sum over the paths `p` of the bottom boundary of the generator. -/
theorem layerMap_apply_append (gens : P.Generators) (L : Layer (SKM.sig D)) (hL : L.Valid)
    (x : P.Mod Gs Ys L.dom) {sl t s sr : Sector I} (pu : SPath L.left sl t)
    (pg' : SPath ((SKM.sig D).cod L.gen) t s) (pv : SPath L.right s sr)
    (hq : P.wt sr = L.cod.endR) :
    letI := Fintype.ofFinite (SPath ((SKM.sig D).dom L.gen) t s)
    layerMap gens L x sl ⟨sr, hq⟩ ((pu.append pg').append pv) =
      ∑ pg : SPath ((SKM.sig D).dom L.gen) t s, layerEntry gens L hL x pu pg pg' pv hq := by
  show layerFun gens L x sl ⟨sr, hq⟩ _ = _
  unfold layerFun
  split_ifs
  rw [← Preadditive.sum_comp]
  refine (comp_eqToHom_congr (T := fun a : Σ t, SPath (L.left ++ (SKM.sig D).cod L.gen) sl t ×
      SPath L.right t sr => (P.pathFunctor (((SPath.split L.left a.2.1).2.1.append
        (SPath.split L.left a.2.1).2.2).append a.2.2)).obj (Ys sr))
    (fun a => letI := Fintype.ofFinite (SPath ((SKM.sig D).dom L.gen)
        (SPath.split L.left a.2.1).1 a.1)
      ∑ pg : SPath ((SKM.sig D).dom L.gen) (SPath.split L.left a.2.1).1 a.1,
        layerEntry gens L hL x (SPath.split L.left a.2.1).2.1 pg (SPath.split L.left a.2.1).2.2
          a.2.2 hq)
    (SPath.split_append (pu.append pg') pv) _ (by simp only [SPath.append_split])).trans ?_
  dsimp only
  refine (comp_eqToHom_congr (T := fun a : Σ t', SPath L.left sl t' ×
      SPath ((SKM.sig D).cod L.gen) t' s => (P.pathFunctor ((a.2.1.append a.2.2).append pv)).obj
        (Ys sr))
    (fun a => letI := Fintype.ofFinite (SPath ((SKM.sig D).dom L.gen) a.1 s)
      ∑ pg : SPath ((SKM.sig D).dom L.gen) a.1 s, layerEntry gens L hL x a.2.1 pg a.2.2 pv hq)
    (SPath.split_append pu pg') _ rfl).trans ?_
  simp only [eqToHom_refl, Category.comp_id]

/-- **Transport of a matrix entry** along an equality of objects: the entry at a path `p` of
the new word is the entry at the corresponding path `p'` of the old word. -/
theorem Mod.cast_apply {a a' : Obj (SKM.sig D)} (h : a = a') (y : P.Mod Gs Ys a)
    (s : Sector I) (t : {t : Sector I // P.wt t = a'.endR}) (p : SPath a'.word s t.1)
    (p' : SPath a.word s t.1) (hp : HEq p' p) :
    cast (congrArg (P.Mod Gs Ys) h) y s t p =
      y s ⟨t.1, t.2.trans (congrArg Obj.endR h).symm⟩ p' ≫
        eqToHom (by subst h; rw [eq_of_heq hp]) := by
  subst h
  cases eq_of_heq hp
  simp

end Entries

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
