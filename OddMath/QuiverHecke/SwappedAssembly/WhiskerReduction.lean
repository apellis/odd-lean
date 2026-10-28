/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Matrices
import OddMath.SKM.RouquierHomPreSuperInverse

/-! # Reduction of the whiskered relations to their matrix entries

The relation obligations of `SwappedAssembly/Interpretation.lean` for the swapped layer
representation `ProbeReservoir.layerRep` (`docs/Nondegeneracy/SwappedActionAssembly.md`, (A1))
quantify over all whiskerings `u ⊗ r ⊗ v` of a relation `r` of the presentation of
Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5. This file
reduces them to the unwhiskered relation, entry by entry.

* `compLayer gens L p q Z : F_p Z ⟶ F_q Z` is the matrix entry of a layer between summand
  paths `p` of its bottom and `q` of its top boundary: the image of the generator in the
  middle, the identity on the whiskers (`compLayer_eq`), zero when the outer parts of `p` and
  `q` differ.
* `compList`, `compDiag`, `compEval`: the entries of a chain of layers, of a diagram and of a
  linear combination of diagrams (sums over the intermediate paths).
* `res_opList_ext_apply`: the evaluation of a chain of layers in `layerRep` is the matrix
  product of its entries with the input family.
* `compList_whisker`, `compList_whisker_eq_zero`: the entries of `u ⊗ d ⊗ v` are block
  diagonal in the outer parts, with block `F_{pu}` applied to the entry of `d` at `F_{pv} Z`.
* `relHolds_of_compEval`: a relation holds in `layerRep` once its unwhiskered entries vanish.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u

variable {I X : Type u}

namespace SPath

/-- Transport of a path along an equality of words. -/
def cast {w w' : List (Col I X)} {s t : Sector I} (h : w = w') (p : SPath w s t) :
    SPath w' s t :=
  h ▸ p

@[simp] theorem cast_rfl {w : List (Col I X)} {s t : Sector I} (p : SPath w s t) :
    p.cast rfl = p := rfl

@[simp] theorem cast_cast {w w' w'' : List (Col I X)} {s t : Sector I} (h : w = w')
    (h' : w' = w'') (p : SPath w s t) : (p.cast h).cast h' = p.cast (h.trans h') := by
  subst h; subst h'; rfl

theorem cast_injective {w w' : List (Col I X)} {s t : Sector I} (h : w = w') :
    Function.Injective (cast (s := s) (t := t) h) := by
  subst h; exact fun _ _ h => h

/-- Transport of paths along an equality of words, as an equivalence. -/
def castEquiv {w w' : List (Col I X)} {s t : Sector I} (h : w = w') :
    SPath w s t ≃ SPath w' s t where
  toFun := cast h
  invFun := cast h.symm
  left_inv p := by simp
  right_inv p := by simp

theorem cast_cons {c : Col I X} {w w' : List (Col I X)} {s t : Sector I} (side : Bool)
    (hv : StepValid c.l side s) (p : SPath w (nextSector c.l side s) t)
    (h : c :: w = c :: w') :
    (SPath.cons c side s hv p).cast h = .cons c side s hv (p.cast (List.cons.inj h).2) := by
  obtain rfl := (List.cons.inj h).2
  rfl

theorem append_assoc {l m r : List (Col I X)} {s t t' t'' : Sector I} (p : SPath l s t)
    (q : SPath m t t') (q' : SPath r t' t'') :
    (p.append q).append q' = (p.append (q.append q')).cast (List.append_assoc l m r).symm := by
  induction p with
  | nil s => rfl
  | cons c side s hv p ih =>
    simp only [append]
    rw [cast_cons, ih]

/-- A decomposition of a path of `l ++ m ++ r` into its three parts. -/
abbrev Dec (l m r : List (Col I X)) (s t : Sector I) : Type u :=
  Σ x : Sector I × Sector I, SPath l s x.1 × SPath m x.1 x.2 × SPath r x.2 t

/-- The path of a decomposition. -/
def Dec.path {l m r : List (Col I X)} {s t : Sector I} (d : Dec l m r s t) :
    SPath (l ++ m ++ r) s t :=
  (d.2.1.append d.2.2.1).append d.2.2.2

/-- The outer parts of a decomposition. -/
def Dec.outer {l m r : List (Col I X)} {s t : Sector I} (d : Dec l m r s t) :
    (Σ x, SPath l s x) × (Σ y, SPath r y t) :=
  (⟨d.1.1, d.2.1⟩, ⟨d.1.2, d.2.2.2⟩)

/-- The decomposition of a path of `l ++ m ++ r`. -/
def decOf (l m : List (Col I X)) {r : List (Col I X)} {s t : Sector I}
    (p : SPath (l ++ m ++ r) s t) : Dec l m r s t :=
  ⟨((split l (split (l ++ m) p).2.1).1, (split (l ++ m) p).1),
    (split l (split (l ++ m) p).2.1).2.1, (split l (split (l ++ m) p).2.1).2.2,
    (split (l ++ m) p).2.2⟩

@[simp] theorem path_decOf (l m : List (Col I X)) {r : List (Col I X)} {s t : Sector I}
    (p : SPath (l ++ m ++ r) s t) : (decOf l m p).path = p := by
  simp only [decOf, Dec.path]
  rw [append_split, append_split]

@[simp] theorem decOf_path {l m r : List (Col I X)} {s t : Sector I} (d : Dec l m r s t) :
    decOf l m d.path = d := by
  obtain ⟨⟨x, y⟩, pu, pg, pv⟩ := d
  simp only [decOf, Dec.path]
  rw [split_append, split_append]

theorem Dec.path_injective {l m r : List (Col I X)} {s t : Sector I} :
    Function.Injective (Dec.path : Dec l m r s t → _) := fun d d' h => by
  rw [← decOf_path d, ← decOf_path d', h]

/-- Paths of `l ++ m ++ r` are their decompositions. -/
def decEquiv (l m r : List (Col I X)) (s t : Sector I) :
    SPath (l ++ m ++ r) s t ≃ Dec l m r s t where
  toFun := decOf l m
  invFun := Dec.path
  left_inv := path_decOf l m
  right_inv := decOf_path

instance (l m r : List (Col I X)) (s t : Sector I) : Finite (Dec l m r s t) :=
  Finite.of_equiv _ (decEquiv l m r s t)

theorem sigma_eq_of_append_left {l l' : List (Col I X)} {s x x' y y' : Sector I}
    {p : SPath l s x} {q : SPath l' x y} {p' : SPath l s x'} {q' : SPath l' x' y'}
    (h : (⟨y, p.append q⟩ : Σ z, SPath (l ++ l') s z) = ⟨y', p'.append q'⟩) :
    (⟨x, p⟩ : Σ z, SPath l s z) = ⟨x', p'⟩ := by
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  have h := congrArg (split l) (eq_of_heq h)
  rw [split_append, split_append] at h
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  simp only [heq_eq_eq, Prod.mk.injEq] at h
  rw [h.1]

theorem sigma_eq_of_append_right {l l' : List (Col I X)} {x x' y y' t : Sector I}
    {p : SPath l y x} {q : SPath l' x t} {p' : SPath l y' x'} {q' : SPath l' x' t}
    (h : (⟨y, p.append q⟩ : Σ z, SPath (l ++ l') z t) = ⟨y', p'.append q'⟩) :
    (⟨x, q⟩ : Σ z, SPath l' z t) = ⟨x', q'⟩ := by
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  have h := congrArg (split l) (eq_of_heq h)
  rw [split_append, split_append] at h
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  simp only [heq_eq_eq, Prod.mk.injEq] at h
  rw [h.2]

@[simp] theorem cast_self {w : List (Col I X)} {s t : Sector I} (h : w = w) (p : SPath w s t) :
    p.cast h = p := rfl

theorem append_cast_left {l l' m : List (Col I X)} {s t r : Sector I} (h : l = l')
    (p : SPath l s t) (q : SPath m t r) :
    (p.cast h).append q = (p.append q).cast (congrArg (· ++ m) h) := by
  subst h; rfl

theorem append_cast_right {l m m' : List (Col I X)} {s t r : Sector I} (h : m = m')
    (p : SPath l s t) (q : SPath m t r) :
    p.append (q.cast h) = (p.append q).cast (congrArg (l ++ ·) h) := by
  subst h; rfl

/-- Reassociation of a whiskered decomposed path. -/
theorem append_append_reassoc {lu l m r lv : List (Col I X)} {s x x' y' y t : Sector I}
    (pu : SPath lu s x) (pl : SPath l x x') (pg : SPath m x' y') (pr : SPath r y' y)
    (pv : SPath lv y t) :
    (pu.append ((pl.append pg).append pr)).append pv =
      (((pu.append pl).append pg).append (pr.append pv)).cast
        (by simp only [List.append_assoc]) := by
  simp only [append_assoc, append_cast_left, append_cast_right, cast_cast]

theorem append_left_cancel {l m : List (Col I X)} {s x t : Sector I} (pu : SPath l s x)
    {p q : SPath m x t} (h : pu.append p = pu.append q) : p = q := by
  have h := congrArg (split l) h
  rw [split_append, split_append] at h
  simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h
  exact h

theorem append_right_cancel {l m : List (Col I X)} {s x t : Sector I} {p q : SPath l s x}
    (pv : SPath m x t) (h : p.append pv = q.append pv) : p = q := by
  have h := congrArg (split l) h
  rw [split_append, split_append] at h
  simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h
  exact h.1

end SPath

variable [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

instance step_additive : ∀ (l : Letter I) (side : Bool) (s : Sector I)
    (hv : StepValid l side s), (P.step l side s hv).Additive
  | (true, _), true, _, _ => by dsimp only [step]; infer_instance
  | (true, _), false, _, _ => by dsimp only [step]; infer_instance
  | (false, _), true, _, _ => by dsimp only [step]; infer_instance
  | (false, _), false, _, _ => by dsimp only [step]; infer_instance

instance step_linear : ∀ (l : Letter I) (side : Bool) (s : Sector I)
    (hv : StepValid l side s), (P.step l side s hv).Linear k
  | (true, _), true, _, _ => by dsimp only [step]; infer_instance
  | (true, _), false, _, _ => by dsimp only [step]; infer_instance
  | (false, _), true, _, _ => by dsimp only [step]; infer_instance
  | (false, _), false, _, _ => by dsimp only [step]; infer_instance

instance pathFunctor_additive : ∀ {w : List (Col I X)} {s t : Sector I} (p : SPath w s t),
    (P.pathFunctor p).Additive
  | _, _, _, .nil _ => by rw [pathFunctor_nil]; infer_instance
  | _, _, _, .cons c side s hv p => by
    have := pathFunctor_additive p
    rw [pathFunctor_cons]; infer_instance

instance pathFunctor_linear : ∀ {w : List (Col I X)} {s t : Sector I} (p : SPath w s t),
    (P.pathFunctor p).Linear k
  | _, _, _, .nil _ => by rw [pathFunctor_nil]; infer_instance
  | _, _, _, .cons c side s hv p => by
    have := pathFunctor_linear p
    rw [pathFunctor_cons]; infer_instance

theorem pathFunctor_cast {w w' : List (Col I X)} {s t : Sector I} (h : w = w')
    (p : SPath w s t) : P.pathFunctor (p.cast h) = P.pathFunctor p := by
  subst h; rfl

theorem pathFunctor_obj_congr {w : List (Col I X)} {s t : Sector I} {p p' : SPath w s t}
    (h : p = p') (Z : P.H t) : (P.pathFunctor p).obj Z = (P.pathFunctor p').obj Z := by
  rw [h]

variable {P}

theorem Generators.image_congr (gens : P.Generators) (g : (SKM.sig D).Gen) {t s : Sector I}
    (p : SPath (wd D g.2 g.1.dom) t s) (p' : SPath (wd D g.2 g.1.cod) t s) {Z Z' : P.H s}
    (h : Z = Z') :
    gens.image g p p' Z = eqToHom (by rw [h]) ≫ gens.image g p p' Z' ≫ eqToHom (by rw [h]) := by
  subst h; simp

/-! ## The entries of a layer -/

open Classical in
/-- The entry of a layer from the bottom path `p` to the top path with decomposition `e`. -/
def compLayerAt (gens : P.Generators) (L : Layer (SKM.sig D)) {s t : Sector I}
    (p : SPath L.dom.word s t)
    (e : SPath.Dec L.left ((SKM.sig D).cod L.gen) L.right s t) (Z : P.H t) :
    (P.pathFunctor p).obj Z ⟶ (P.pathFunctor e.path).obj Z :=
  letI := Fintype.ofFinite (SPath ((SKM.sig D).dom L.gen) e.1.1 e.1.2)
  ∑ pg, if h : p = SPath.Dec.path (m := (SKM.sig D).dom L.gen) ⟨e.1, e.2.1, pg, e.2.2.2⟩ then
      eqToHom (P.pathFunctor_obj_congr h Z) ≫
        eqToHom (P.pathFunctor_append_append_obj e.2.1 pg e.2.2.2 Z) ≫
        (P.pathFunctor e.2.1).map (gens.image L.gen pg e.2.2.1 ((P.pathFunctor e.2.2.2).obj Z)) ≫
        eqToHom (P.pathFunctor_append_append_obj e.2.1 e.2.2.1 e.2.2.2 Z).symm
    else 0

/-- **The entry of a layer** between a path `p` of its bottom and a path `q` of its top
boundary. -/
def compLayer (gens : P.Generators) (L : Layer (SKM.sig D)) {s t : Sector I}
    (p : SPath L.dom.word s t) (q : SPath L.cod.word s t) (Z : P.H t) :
    (P.pathFunctor p).obj Z ⟶ (P.pathFunctor q).obj Z :=
  compLayerAt gens L p (SPath.decOf L.left _ q) Z ≫
    eqToHom (P.pathFunctor_obj_congr (SPath.path_decOf _ _ q) Z)

theorem compLayer_eq_compLayerAt (gens : P.Generators) (L : Layer (SKM.sig D))
    {s t : Sector I} (p : SPath L.dom.word s t) (q : SPath L.cod.word s t) (Z : P.H t)
    (e : SPath.Dec L.left ((SKM.sig D).cod L.gen) L.right s t)
    (he : SPath.decOf L.left _ q = e) :
    compLayer gens L p q Z = compLayerAt gens L p e Z ≫
      eqToHom (P.pathFunctor_obj_congr (by rw [← he, SPath.path_decOf]) Z) := by
  subst he; rfl

theorem compLayerAt_eq (gens : P.Generators) (L : Layer (SKM.sig D)) {s t : Sector I}
    (p : SPath L.dom.word s t) (e : SPath.Dec L.left ((SKM.sig D).cod L.gen) L.right s t)
    (Z : P.H t) (pg : SPath ((SKM.sig D).dom L.gen) e.1.1 e.1.2)
    (h : p = SPath.Dec.path (m := (SKM.sig D).dom L.gen) ⟨e.1, e.2.1, pg, e.2.2.2⟩) :
    compLayerAt gens L p e Z =
      eqToHom (P.pathFunctor_obj_congr h Z) ≫
        eqToHom (P.pathFunctor_append_append_obj e.2.1 pg e.2.2.2 Z) ≫
        (P.pathFunctor e.2.1).map (gens.image L.gen pg e.2.2.1 ((P.pathFunctor e.2.2.2).obj Z)) ≫
        eqToHom (P.pathFunctor_append_append_obj e.2.1 e.2.2.1 e.2.2.2 Z).symm := by
  classical
  unfold compLayerAt
  rw [Finset.sum_eq_single pg]
  · rw [dite_eq_left h]
  · intro pg' _ hne
    rw [dite_eq_right fun h' => ?_]
    have := SPath.Dec.path_injective (h.symm.trans h')
    simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at this
    exact hne this.1.symm
  · simp

theorem compLayerAt_eq_zero (gens : P.Generators) (L : Layer (SKM.sig D)) {s t : Sector I}
    (p : SPath L.dom.word s t) (e : SPath.Dec L.left ((SKM.sig D).cod L.gen) L.right s t)
    (Z : P.H t) (d : SPath.Dec L.left ((SKM.sig D).dom L.gen) L.right s t)
    (hp : p = d.path) (hne : d.outer ≠ e.outer) : compLayerAt gens L p e Z = 0 := by
  classical
  unfold compLayerAt
  refine Finset.sum_eq_zero fun pg _ => ?_
  rw [dite_eq_right fun h => ?_]
  have := SPath.Dec.path_injective (hp.symm.trans h)
  subst this
  exact hne rfl

/-- **The entry of a layer at decomposed paths**: the image of the generator in the middle. -/
theorem compLayer_eq (gens : P.Generators) (L : Layer (SKM.sig D)) {s x y t : Sector I}
    (pu : SPath L.left s x) (pg : SPath ((SKM.sig D).dom L.gen) x y)
    (qg : SPath ((SKM.sig D).cod L.gen) x y) (pv : SPath L.right y t) (Z : P.H t) :
    compLayer gens L ((pu.append pg).append pv) ((pu.append qg).append pv) Z =
      eqToHom (P.pathFunctor_append_append_obj pu pg pv Z) ≫
        (P.pathFunctor pu).map (gens.image L.gen pg qg ((P.pathFunctor pv).obj Z)) ≫
        eqToHom (P.pathFunctor_append_append_obj pu qg pv Z).symm := by
  refine (compLayer_eq_compLayerAt gens L _ _ Z ⟨(x, y), pu, qg, pv⟩
    (SPath.decOf_path ⟨(x, y), pu, qg, pv⟩)).trans ?_
  refine (congrArg (· ≫ _) (compLayerAt_eq gens L _ ⟨(x, y), pu, qg, pv⟩ Z pg rfl)).trans ?_
  simp

/-- The entry of a layer vanishes when the outer parts of the two paths differ. -/
theorem compLayer_eq_zero (gens : P.Generators) (L : Layer (SKM.sig D)) {s t : Sector I}
    (d : SPath.Dec L.left ((SKM.sig D).dom L.gen) L.right s t)
    (e : SPath.Dec L.left ((SKM.sig D).cod L.gen) L.right s t) (hne : d.outer ≠ e.outer)
    (Z : P.H t) : compLayer gens L d.path e.path Z = 0 := by
  rw [compLayer_eq_compLayerAt gens L _ _ Z e (SPath.decOf_path e),
    compLayerAt_eq_zero gens L _ e Z d rfl hne, Limits.zero_comp]

variable {Gs Ys : ∀ s, P.H s}

open Classical in
/-- **The action of a layer is the matrix product with its entries.** -/
theorem layerMap_apply (gens : P.Generators) (L : Layer (SKM.sig D)) (hL : L.Valid)
    (x : P.Mod Gs Ys L.dom) (sl : Sector I) (sr : {t : Sector I // P.wt t = L.cod.endR})
    (q : SPath L.cod.word sl sr.1) [Fintype (SPath L.dom.word sl sr.1)] :
    layerMap gens L x sl sr q =
      ∑ p, x sl ⟨sr.1, sr.2.trans hL.endR_eq⟩ p ≫ compLayer gens L p q (Ys sr.1) := by
  simp only [layerMap, LinearMap.coe_mk, AddHom.coe_mk, layerFun]
  rw [dite_eq_left hL]
  simp only [compLayer, compLayerAt, Preadditive.sum_comp, Preadditive.comp_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun pg _ => ?_
  simp only [dite_comp, comp_dite, Limits.zero_comp, Limits.comp_zero]
  rw [Finset.sum_dite_eq', ite_eq_left (Finset.mem_univ _)]
  simp [layerEntry, SPath.decOf, SPath.Dec.path]

/-! ## Whiskered layers -/

theorem pathFunctor_map_append {l m : List (Col I X)} {s x t : Sector I} (pu : SPath l s x)
    (pl : SPath m x t) {Z Z' : P.H t} (f : Z ⟶ Z') :
    (P.pathFunctor (pu.append pl)).map f =
      eqToHom (by rw [pathFunctor_append]; rfl) ≫ (P.pathFunctor pu).map ((P.pathFunctor pl).map f) ≫
        eqToHom (by rw [pathFunctor_append]; rfl) := by
  rw [Functor.congr_hom (P.pathFunctor_append pu pl) f]
  rfl

/-- **The entry of a whiskered layer** at whiskered paths: the entry of the layer, under the
left whisker, at the object of the right whisker. -/
theorem compLayer_whisker (gens : P.Generators) (L : Layer (SKM.sig D)) (u : Obj (SKM.sig D))
    (v : List (SKM.sig D).Colour) {s x y t : Sector I} (pu : SPath u.word s x)
    (p : SPath L.dom.word x y) (q : SPath L.cod.word x y) (pv : SPath v y t) (Z : P.H t) :
    compLayer gens (L.whisker u v)
        (((pu.append p).append pv).cast (congrArg Obj.word (L.whisker_dom u v).symm))
        (((pu.append q).append pv).cast (congrArg Obj.word (L.whisker_cod u v).symm)) Z =
      eqToHom (by rw [pathFunctor_cast]; exact P.pathFunctor_append_append_obj pu p pv Z) ≫
        (P.pathFunctor pu).map (compLayer gens L p q ((P.pathFunctor pv).obj Z)) ≫
        eqToHom (by rw [pathFunctor_cast]; exact (P.pathFunctor_append_append_obj pu q pv Z).symm) := by
  obtain ⟨⟨⟨x1, y1⟩, pl, pg, pr⟩, rfl⟩ :
      ∃ d : SPath.Dec L.left ((SKM.sig D).dom L.gen) L.right x y, d.path = p :=
    ⟨_, SPath.path_decOf _ _ p⟩
  obtain ⟨⟨⟨x2, y2⟩, ql, qg, qr⟩, rfl⟩ :
      ∃ e : SPath.Dec L.left ((SKM.sig D).cod L.gen) L.right x y, e.path = q :=
    ⟨_, SPath.path_decOf _ _ q⟩
  have he : SPath.decOf (L.whisker u v).left _
      (((pu.append (SPath.Dec.path ⟨(x2, y2), ql, qg, qr⟩)).append pv).cast
        (congrArg Obj.word (L.whisker_cod u v).symm)) =
      ⟨(x2, y2), pu.append ql, qg, qr.append pv⟩ := by
    apply SPath.Dec.path_injective
    rw [SPath.path_decOf]
    simp only [SPath.Dec.path]
    rw [SPath.append_append_reassoc, SPath.cast_cast]
    rfl
  refine (compLayer_eq_compLayerAt gens (L.whisker u v) _ _ Z _ he).trans ?_
  have hp : ((pu.append (SPath.Dec.path ⟨(x1, y1), pl, pg, pr⟩)).append pv).cast
        (congrArg Obj.word (L.whisker_dom u v).symm) =
      SPath.Dec.path (m := (SKM.sig D).dom (L.whisker u v).gen)
        ⟨(x1, y1), pu.append pl, pg, pr.append pv⟩ := by
    simp only [SPath.Dec.path]
    rw [SPath.append_append_reassoc, SPath.cast_cast]
    rfl
  by_cases hout : ((⟨x1, pl⟩, ⟨y1, pr⟩) : (Σ z, SPath L.left x z) × (Σ z, SPath L.right z y)) =
      (⟨x2, ql⟩, ⟨y2, qr⟩)
  · simp only [Prod.mk.injEq, Sigma.mk.injEq] at hout
    obtain ⟨⟨rfl, h1⟩, ⟨rfl, h2⟩⟩ := hout
    cases h1; cases h2
    refine (congrArg (· ≫ _) (compLayerAt_eq gens (L.whisker u v) _
      ⟨(x1, y1), pu.append pl, qg, pr.append pv⟩ Z pg hp)).trans ?_
    dsimp only [SPath.Dec.path]
    rw [compLayer_eq, pathFunctor_map_append, Generators.image_congr gens (L.whisker u v).gen
      pg qg (Functor.congr_obj (P.pathFunctor_append pr pv) Z)]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    rfl
  · refine (congrArg (· ≫ _) (compLayerAt_eq_zero gens (L.whisker u v) _ _ Z _ hp ?_)).trans ?_
    · intro h
      apply hout
      simp only [SPath.Dec.outer, Prod.mk.injEq, Sigma.mk.injEq] at h ⊢
      obtain ⟨⟨rfl, h1⟩, ⟨rfl, h2⟩⟩ := h
      exact ⟨⟨rfl, heq_of_eq (SPath.append_left_cancel pu (eq_of_heq h1))⟩,
        ⟨rfl, heq_of_eq (SPath.append_right_cancel pv (eq_of_heq h2))⟩⟩
    · rw [compLayer_eq_zero gens L ⟨(x1, y1), pl, pg, pr⟩ ⟨(x2, y2), ql, qg, qr⟩ hout]
      simp

/-- The entry of a whiskered layer vanishes between paths with different whisker parts. -/
theorem compLayer_whisker_eq_zero (gens : P.Generators) (L : Layer (SKM.sig D))
    (u : Obj (SKM.sig D)) (v : List (SKM.sig D).Colour) {s x y x' y' t : Sector I}
    (pu : SPath u.word s x) (p : SPath L.dom.word x y) (pv : SPath v y t)
    (pu' : SPath u.word s x') (q : SPath L.cod.word x' y') (pv' : SPath v y' t)
    (hne : ((⟨x, pu⟩ : Σ z, SPath u.word s z), (⟨y, pv⟩ : Σ z, SPath v z t)) ≠
      (⟨x', pu'⟩, ⟨y', pv'⟩)) (Z : P.H t) :
    compLayer gens (L.whisker u v)
        (((pu.append p).append pv).cast (congrArg Obj.word (L.whisker_dom u v).symm))
        (((pu'.append q).append pv').cast (congrArg Obj.word (L.whisker_cod u v).symm)) Z = 0 := by
  obtain ⟨⟨⟨x1, y1⟩, pl, pg, pr⟩, rfl⟩ :
      ∃ d : SPath.Dec L.left ((SKM.sig D).dom L.gen) L.right x y, d.path = p :=
    ⟨_, SPath.path_decOf _ _ p⟩
  obtain ⟨⟨⟨x2, y2⟩, ql, qg, qr⟩, rfl⟩ :
      ∃ e : SPath.Dec L.left ((SKM.sig D).cod L.gen) L.right x' y', e.path = q :=
    ⟨_, SPath.path_decOf _ _ q⟩
  have he : SPath.decOf (L.whisker u v).left _
      (((pu'.append (SPath.Dec.path ⟨(x2, y2), ql, qg, qr⟩)).append pv').cast
        (congrArg Obj.word (L.whisker_cod u v).symm)) =
      ⟨(x2, y2), pu'.append ql, qg, qr.append pv'⟩ := by
    apply SPath.Dec.path_injective
    rw [SPath.path_decOf]
    simp only [SPath.Dec.path]
    rw [SPath.append_append_reassoc, SPath.cast_cast]
    rfl
  have hp : ((pu.append (SPath.Dec.path ⟨(x1, y1), pl, pg, pr⟩)).append pv).cast
        (congrArg Obj.word (L.whisker_dom u v).symm) =
      SPath.Dec.path (m := (SKM.sig D).dom (L.whisker u v).gen)
        ⟨(x1, y1), pu.append pl, pg, pr.append pv⟩ := by
    simp only [SPath.Dec.path]
    rw [SPath.append_append_reassoc, SPath.cast_cast]
    rfl
  refine (compLayer_eq_compLayerAt gens (L.whisker u v) _ _ Z _ he).trans ?_
  rw [compLayerAt_eq_zero gens (L.whisker u v) _ _ Z _ hp fun h => hne ?_, Limits.zero_comp]
  simp only [SPath.Dec.outer, Prod.mk.injEq] at h
  exact Prod.ext (SPath.sigma_eq_of_append_left h.1) (SPath.sigma_eq_of_append_right h.2)

/-! ## The entries of a chain of layers -/

open Classical in
/-- **The entry of a chain of layers** between a path `p` of its bottom and a path `q` of its
top boundary: the sum over the intermediate paths of the products of the layer entries. -/
def compList (gens : P.Generators) : (ls : List (Layer (SKM.sig D))) →
    {a b : Obj (SKM.sig D)} → Chain a ls b → {s t : Sector I} → (p : SPath a.word s t) →
    (q : SPath b.word s t) → (Z : P.H t) → ((P.pathFunctor p).obj Z ⟶ (P.pathFunctor q).obj Z)
  | [], _, _, h, _, _, p, q, Z =>
    if hq : p.cast (congrArg Obj.word h) = q then
      eqToHom (by rw [← hq, pathFunctor_cast])
    else 0
  | L :: ls, _, _, h, s, t, p, q, Z =>
    letI := Fintype.ofFinite (SPath L.cod.word s t)
    ∑ pm, eqToHom (by rw [pathFunctor_cast]) ≫
      compLayer gens L (p.cast (congrArg Obj.word h.2.1.symm)) pm Z ≫
        compList gens ls h.2.2 pm q Z

theorem compList_nil (gens : P.Generators) {a : Obj (SKM.sig D)} {s t : Sector I}
    (p q : SPath a.word s t) (Z : P.H t) [Decidable (p = q)] :
    compList gens [] (rfl : Chain a [] a) p q Z =
      if hq : p = q then eqToHom (by rw [hq]) else 0 := by
  simp only [compList, SPath.cast_self]
  congr

open Classical in
theorem compList_cons (gens : P.Generators) (L : Layer (SKM.sig D)) (ls : List (Layer (SKM.sig D)))
    {b : Obj (SKM.sig D)} (hv : L.Valid) (hc : Chain L.cod ls b) {s t : Sector I}
    (p : SPath L.dom.word s t) (q : SPath b.word s t) (Z : P.H t) :
    letI := Fintype.ofFinite (SPath L.cod.word s t)
    compList gens (L :: ls) ⟨hv, rfl, hc⟩ p q Z =
      ∑ pm, compLayer gens L p pm Z ≫ compList gens ls hc pm q Z := by
  simp [compList]

/-- Changing the bottom object of a chain along an equality. -/
theorem compList_cast (gens : P.Generators) (ls : List (Layer (SKM.sig D)))
    {a a' b : Obj (SKM.sig D)} (ha : a = a') (h : Chain a ls b) (h' : Chain a' ls b)
    {s t : Sector I} (p : SPath a.word s t) (q : SPath b.word s t) (Z : P.H t) :
    compList gens ls h' (p.cast (congrArg Obj.word ha)) q Z =
      eqToHom (by rw [pathFunctor_cast]) ≫ compList gens ls h p q Z := by
  subst ha; simp

theorem layerRep_toLocal_op_ext (gens : P.Generators) (L : Layer (SKM.sig D))
    (x : P.Mod Gs Ys L.dom) :
    (P.layerRep Gs Ys gens).toLocal.op L ((P.layerRep Gs Ys gens).toLocal.ext L.dom x) =
      (P.layerRep Gs Ys gens).toLocal.ext L.cod (layerMap gens L x) := by
  classical
  simp [LayerRep.toLocal, layerRep]

/-- **The evaluation of a chain of layers** in `layerRep` is the matrix product of its entries
with the input family. -/
theorem res_opList_ext_apply (gens : P.Generators) (ls : List (Layer (SKM.sig D)))
    {a b : Obj (SKM.sig D)} (h : Chain a ls b) (x : P.Mod Gs Ys a) (s : Sector I)
    (t : {t : Sector I // P.wt t = b.endR}) (q : SPath b.word s t.1)
    [Fintype (SPath a.word s t.1)] :
    ((P.layerRep Gs Ys gens).toLocal.res b
        ((P.layerRep Gs Ys gens).toLocal.opList ls
          ((P.layerRep Gs Ys gens).toLocal.ext a x)) : P.Mod Gs Ys b) s t q =
      ∑ p, x s ⟨t.1, t.2.trans h.endR_eq⟩ p ≫ compList gens ls h p q (Ys t.1) := by
  classical
  induction ls generalizing a with
  | nil =>
    subst h
    simp only [LocalInterpretation.opList_nil_apply, LocalInterpretation.res_ext_apply,
      compList_nil, comp_dite, Limits.comp_zero]
    rw [Finset.sum_dite_eq', ite_eq_left (Finset.mem_univ _)]
    simp
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    let := Fintype.ofFinite (SPath L.cod.word s t.1)
    rw [LocalInterpretation.opList_cons_apply, layerRep_toLocal_op_ext, ih hc]
    simp only [layerMap_apply gens L hv, Preadditive.sum_comp, Category.assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [compList_cons gens L ls hv hc, Preadditive.comp_sum]

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
