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
* `relHolds_of_compEval`: a relation holds in `layerRep` once its unwhiskered entries vanish;
  `relHolds_of_compEval_wt`: it suffices that they vanish at weight-matched rightmost sectors.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u uB v w

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

/-- Sums over the paths of a word `l ++ m ++ r` (up to an equality of words) are sums over
decompositions. -/
theorem sum_cast_dec {M : Type*} [AddCommMonoid M] {l m r w : List (Col I X)}
    (hw : l ++ m ++ r = w) {s t : Sector I} [Fintype (SPath w s t)] [Fintype (Dec l m r s t)]
    (g : SPath w s t → M) : ∑ pm, g pm = ∑ d : Dec l m r s t, g (d.path.cast hw) :=
  (Fintype.sum_equiv ((decEquiv l m r s t).symm.trans (castEquiv hw))
    (fun d => g (d.path.cast hw)) g fun _ => rfl).symm

/-- A sum over decompositions supported on fixed outer parts is a sum over middle parts. -/
theorem sum_dec_eq {M : Type*} [AddCommMonoid M] {l m r : List (Col I X)}
    {s x y t : Sector I} (pu : SPath l s x) (pv : SPath r y t) [Fintype (Dec l m r s t)]
    [Fintype (SPath m x y)] (g : Dec l m r s t → M)
    (hg : ∀ d : Dec l m r s t, d.outer ≠ (⟨x, pu⟩, ⟨y, pv⟩) → g d = 0) :
    ∑ d, g d = ∑ mm : SPath m x y, g ⟨(x, y), pu, mm, pv⟩ := by
  classical
  let ι : SPath m x y → Dec l m r s t := fun mm => ⟨(x, y), pu, mm, pv⟩
  have hinj : Set.InjOn ι (Finset.univ : Finset (SPath m x y)) := fun a _ b _ h => by
    simpa [ι] using h
  rw [← Finset.sum_image (f := g) hinj]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun d _ hd => hg d fun h => hd ?_
  obtain ⟨⟨x', y'⟩, pu', mm, pv'⟩ := d
  simp only [Dec.outer, Prod.mk.injEq, Sigma.mk.injEq] at h
  obtain ⟨⟨rfl, h1⟩, ⟨rfl, h2⟩⟩ := h
  cases h1; cases h2
  exact Finset.mem_image_of_mem _ (Finset.mem_univ mm)

end SPath

variable [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
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

/-- The entry of a whiskered chain vanishes between paths with different whisker parts. -/
theorem compList_whisker_eq_zero (gens : P.Generators) (u : Obj (SKM.sig D))
    (v : List (SKM.sig D).Colour) (ls : List (Layer (SKM.sig D))) {a b : Obj (SKM.sig D)}
    (h : Chain a ls b) (hw : a.WhiskerOK u v) {s x y x' y' t : Sector I}
    (pu : SPath u.word s x) (p : SPath a.word x y) (pv : SPath v y t)
    (pu' : SPath u.word s x') (q : SPath b.word x' y') (pv' : SPath v y' t)
    (hne : ((⟨x, pu⟩ : Σ z, SPath u.word s z), (⟨y, pv⟩ : Σ z, SPath v z t)) ≠
      (⟨x', pu'⟩, ⟨y', pv'⟩)) (Z : P.H t) :
    compList gens (ls.map (·.whisker u v)) (h.whisker hw) ((pu.append p).append pv)
      ((pu'.append q).append pv') Z = 0 := by
  induction ls generalizing a x y pu p pv with
  | nil =>
    subst h
    simp only [List.map_nil, compList]
    refine dite_eq_right fun hq => hne ?_
    exact congrArg SPath.Dec.outer (SPath.Dec.path_injective (l := u.word) (m := a.word) (r := v)
      (a₁ := ⟨(x, y), pu, p, pv⟩) (a₂ := ⟨(x', y'), pu', q, pv'⟩) hq)
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    have hw' : L.cod.WhiskerOK u v := Chain.whiskerOK (ls := [L]) ⟨hv, rfl, rfl⟩ hw
    erw [compList.eq_2]
    let _ : Fintype (SPath.Dec u.word L.cod.word v s t) := Fintype.ofFinite _
    let _ : Fintype (SPath (L.whisker u v).cod.word s t) := Fintype.ofFinite _
    rw [SPath.sum_cast_dec (congrArg Obj.word (L.whisker_cod u v).symm)]
    refine Finset.sum_eq_zero fun d _ => ?_
    obtain ⟨⟨x'', y''⟩, pu'', m, pv''⟩ := d
    by_cases hd : ((⟨x'', pu''⟩ : Σ z, SPath u.word s z), (⟨y'', pv''⟩ : Σ z, SPath v z t)) =
        (⟨x, pu⟩, ⟨y, pv⟩)
    · simp only [Prod.mk.injEq, Sigma.mk.injEq] at hd
      obtain ⟨⟨rfl, h1⟩, ⟨rfl, h2⟩⟩ := hd
      cases h1; cases h2
      erw [compList_cast gens _ (L.whisker_cod u v).symm (hc.whisker hw'), ih hc hw' _ m _ hne]
      simp
    · erw [compLayer_whisker_eq_zero gens L u v pu p pv pu'' m pv'' (Ne.symm hd)]
      simp

/-- **The entry of a whiskered chain** at whiskered paths: the entry of the chain, under the
left whisker, at the object of the right whisker. -/
theorem compList_whisker (gens : P.Generators) (u : Obj (SKM.sig D))
    (v : List (SKM.sig D).Colour) (ls : List (Layer (SKM.sig D))) {a b : Obj (SKM.sig D)}
    (h : Chain a ls b) (hw : a.WhiskerOK u v) {s x y t : Sector I} (pu : SPath u.word s x)
    (p : SPath a.word x y) (q : SPath b.word x y) (pv : SPath v y t) (Z : P.H t) :
    compList gens (ls.map (·.whisker u v)) (h.whisker hw) ((pu.append p).append pv)
        ((pu.append q).append pv) Z =
      eqToHom (P.pathFunctor_append_append_obj pu p pv Z) ≫
        (P.pathFunctor pu).map (compList gens ls h p q ((P.pathFunctor pv).obj Z)) ≫
        eqToHom (P.pathFunctor_append_append_obj pu q pv Z).symm := by
  induction ls generalizing a pu p pv with
  | nil =>
    subst h
    simp only [List.map_nil, compList, SPath.cast_self]
    by_cases hpq : p = q
    · subst hpq
      rw [dite_eq_left rfl, dite_eq_left rfl]
      simp
    · rw [dite_eq_right fun hq => hpq ?_, dite_eq_right hpq]
      · simp
      have := SPath.Dec.path_injective (l := u.word) (m := a.word) (r := v)
        (a₁ := ⟨(x, y), pu, p, pv⟩) (a₂ := ⟨(x, y), pu, q, pv⟩) hq
      simpa using this
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    have hw' : L.cod.WhiskerOK u v := Chain.whiskerOK (ls := [L]) ⟨hv, rfl, rfl⟩ hw
    let _ : Fintype (SPath L.cod.word x y) := Fintype.ofFinite _
    rw [compList_cons gens L ls hv hc, Functor.map_sum, Preadditive.sum_comp,
      Preadditive.comp_sum]
    erw [compList.eq_2]
    let _ : Fintype (SPath.Dec u.word L.cod.word v s t) := Fintype.ofFinite _
    let _ : Fintype (SPath (L.whisker u v).cod.word s t) := Fintype.ofFinite _
    rw [SPath.sum_cast_dec (congrArg Obj.word (L.whisker_cod u v).symm), SPath.sum_dec_eq pu pv]
    · refine Finset.sum_congr rfl fun m _ => ?_
      erw [compLayer_whisker gens L u v pu p m pv,
        compList_cast gens _ (L.whisker_cod u v).symm (hc.whisker hw'), ih hc hw' pu m pv]
      simp
    · rintro ⟨⟨x'', y''⟩, pu'', m, pv''⟩ hd
      erw [compLayer_whisker_eq_zero gens L u v pu p pv pu'' m pv'' (Ne.symm hd)]
      simp

/-! ## Entries of diagrams and of linear combinations -/

/-- The entry of a diagram between summand paths of its boundaries. -/
def compDiag (gens : P.Generators) {a b : Obj (SKM.sig D)} (d : a ⟶ b) {s t : Sector I}
    (p : SPath a.word s t) (q : SPath b.word s t) (Z : P.H t) :
    (P.pathFunctor p).obj Z ⟶ (P.pathFunctor q).obj Z :=
  compList gens (Diagram.layers d) (Diagram.chain d) p q Z

/-- **The entry of a linear combination of diagrams** between summand paths of its
boundaries. -/
def compEval (gens : P.Generators) {a b : Obj (SKM.sig D)} (X : (a ⟶ b) →₀ k)
    {s t : Sector I} (p : SPath a.word s t) (q : SPath b.word s t) (Z : P.H t) :
    (P.pathFunctor p).obj Z ⟶ (P.pathFunctor q).obj Z :=
  X.sum fun d r => r • compDiag gens d p q Z

@[simp] theorem Mod.zero_apply {a : Obj (SKM.sig D)} (s : Sector I)
    (t : {t : Sector I // P.wt t = a.endR}) (p : SPath a.word s t.1) :
    (0 : P.Mod Gs Ys a) s t p = 0 :=
  rfl

theorem Mod.sum_apply {a : Obj (SKM.sig D)} {ι : Type*} (S : Finset ι) (f : ι → P.Mod Gs Ys a)
    (s : Sector I) (t : {t : Sector I // P.wt t = a.endR}) (p : SPath a.word s t.1) :
    (∑ i ∈ S, f i) s t p = ∑ i ∈ S, f i s t p := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert i S hi ih => rw [Finset.sum_insert hi, Mod.add_apply, ih, Finset.sum_insert hi]

/-- The entry of a whiskered linear combination at whiskered paths. -/
theorem compEval_whisker (gens : P.Generators) (u : Obj (SKM.sig D))
    (v : List (SKM.sig D).Colour) {a b : Obj (SKM.sig D)} (X : (a ⟶ b) →₀ k)
    (hw : a.WhiskerOK u v) {s x y t : Sector I} (pu : SPath u.word s x) (p : SPath a.word x y)
    (q : SPath b.word x y) (pv : SPath v y t) (Z : P.H t) :
    (X.sum fun d r => r • compList gens ((Diagram.layers d).map (·.whisker u v))
        ((Diagram.chain d).whisker hw) ((pu.append p).append pv) ((pu.append q).append pv) Z) =
      eqToHom (P.pathFunctor_append_append_obj pu p pv Z) ≫
        (P.pathFunctor pu).map (compEval gens X p q ((P.pathFunctor pv).obj Z)) ≫
        eqToHom (P.pathFunctor_append_append_obj pu q pv Z).symm := by
  simp only [compEval, compDiag, Finsupp.sum, Functor.map_sum, Functor.map_smul,
    Preadditive.sum_comp, Preadditive.comp_sum, Linear.smul_comp, Linear.comp_smul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [compList_whisker (hw := hw)]

omit [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- Along a summand path of a word that is well formed from the region `ρ`, the sector weights
follow the regions of the word: if the rightmost sector has the weight of the rightmost region,
the leftmost sector has weight `ρ`. -/
theorem wt_eq_of_ok : {v : List (Col I X)} → {y t : Sector I} → (pv : SPath v y t) →
    (ρ : X) → (SKM.sig D).ok ρ v → P.wt t = (SKM.sig D).endR ρ v → P.wt y = ρ
  | _, _, _, .nil _, _, _, h => h
  | _, _, _, .cons c side s hv p, ρ, hok, h => by
    obtain ⟨h1, h2⟩ := hok
    rw [P.wt_nextSector c.l side s hv, wt_eq_of_ok p c.r h2 h]
    exact h1

/-- **Reduction of a whiskered evaluation to weight-matched entries**: a linear combination of
diagrams whose entries vanish whenever the rightmost sector has the weight of the rightmost
region evaluates to zero after every whiskering. -/
theorem evalW_eq_zero_of_compEval_wt (gens : P.Generators) {a b : Obj (SKM.sig D)}
    (X : (a ⟶ b) →₀ k)
    (hX : ∀ {s t : Sector I} (p : SPath a.word s t) (q : SPath b.word s t) (Z : P.H t),
      P.wt t = a.endR → compEval gens X p q Z = 0)
    (u : Obj (SKM.sig D)) (v : List (SKM.sig D).Colour) (hw : a.WhiskerOK u v) :
    (P.layerRep Gs Ys gens).toLocal.evalW (a.whisker u v) (b.whisker u v) u v X = 0 := by
  classical
  ext x : 1
  funext s t Q
  rw [LocalInterpretation.evalW, Finsupp.linearCombination_apply]
  simp only [LinearMap.zero_apply]
  rw [Finsupp.sum, LinearMap.sum_apply, Mod.sum_apply, Mod.zero_apply]
  let _ : Fintype (SPath (a.whisker u v).word s t.1) := Fintype.ofFinite _
  rcases X.support.eq_empty_or_nonempty with hX0 | ⟨d0, -⟩
  · rw [hX0, Finset.sum_empty]
  have hend : P.wt t.1 = (a.whisker u v).endR := t.2.trans ((Diagram.chain d0).whisker hw).endR_eq
  have hterm : ∀ d : a ⟶ b,
      ((X d • ((P.layerRep Gs Ys gens).toLocal.res (b.whisker u v) ∘ₗ
        (P.layerRep Gs Ys gens).toLocal.opList ((Diagram.layers d).map (·.whisker u v)) ∘ₗ
        (P.layerRep Gs Ys gens).toLocal.ext (a.whisker u v))) x :
          P.Mod Gs Ys (b.whisker u v)) s t Q =
      ∑ pp, x s ⟨t.1, hend⟩ pp ≫
        (X d • compList gens _ ((Diagram.chain d).whisker hw) pp Q (Ys t.1)) := by
    intro d
    rw [LinearMap.smul_apply, Mod.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      res_opList_ext_apply gens _ ((Diagram.chain d).whisker hw), Finset.smul_sum]
    simp only [Linear.comp_smul]
  erw [Finset.sum_congr rfl fun d _ => hterm d]
  refine (Finset.sum_comm).trans (Finset.sum_eq_zero fun pp _ => ?_)
  rw [← Preadditive.comp_sum]
  obtain ⟨⟨⟨x1, y1⟩, pu, p, pv⟩, rfl⟩ :
      ∃ d : SPath.Dec u.word a.word v s t.1, d.path = pp := ⟨_, SPath.path_decOf _ _ pp⟩
  obtain ⟨⟨⟨x2, y2⟩, pu', q, pv'⟩, rfl⟩ :
      ∃ e : SPath.Dec u.word b.word v s t.1, e.path = Q := ⟨_, SPath.path_decOf _ _ Q⟩
  by_cases hout : ((⟨x1, pu⟩ : Σ z, SPath u.word s z), (⟨y1, pv⟩ : Σ z, SPath v z t.1)) =
      (⟨x2, pu'⟩, ⟨y2, pv'⟩)
  · simp only [Prod.mk.injEq, Sigma.mk.injEq] at hout
    obtain ⟨⟨rfl, h1⟩, ⟨rfl, h2⟩⟩ := hout
    cases h1; cases h2
    have hy : P.wt y1 = a.endR := by
      refine P.wt_eq_of_ok pv a.endR hw.2.2 (hend.trans ?_)
      rw [Obj.endR, Obj.whisker_start, Obj.whisker_word, Signature.endR_append,
        Signature.endR_append]
      exact congrArg (fun r => (SKM.sig D).endR ((SKM.sig D).endR r a.word) v) hw.2.1
    have := compEval_whisker gens u v X hw pu p q pv (Ys t.1)
    simp only [Finsupp.sum] at this
    erw [this, hX p q _ hy]
    simp
  · refine (congrArg _ (Finset.sum_eq_zero fun d _ => ?_)).trans (Limits.comp_zero)
    erw [compList_whisker_eq_zero gens u v _ (Diagram.chain d) hw pu p pv pu' q pv' hout]
    simp

/-- **Reduction of a whiskered evaluation to entries**: a linear combination of diagrams
whose entries all vanish evaluates to zero after every whiskering. -/
theorem evalW_eq_zero_of_compEval (gens : P.Generators) {a b : Obj (SKM.sig D)}
    (X : (a ⟶ b) →₀ k)
    (hX : ∀ {s t : Sector I} (p : SPath a.word s t) (q : SPath b.word s t) (Z : P.H t),
      compEval gens X p q Z = 0)
    (u : Obj (SKM.sig D)) (v : List (SKM.sig D).Colour) (hw : a.WhiskerOK u v) :
    (P.layerRep Gs Ys gens).toLocal.evalW (a.whisker u v) (b.whisker u v) u v X = 0 :=
  evalW_eq_zero_of_compEval_wt gens X (fun p q Z _ => hX p q Z) u v hw

/-- **Reduction of a relation to its weight-matched entries**: a relation of the presentation
holds in the swapped layer representation (under every whiskering) once the entries of the
unwhiskered relation vanish at every rightmost sector of the weight of its rightmost region. -/
theorem relHolds_of_compEval_wt (gens : P.Generators) (r : SKM.Rel D)
    (h : ∀ {s t : Sector I} (p : SPath ((SKM.pres D Sc).dom r).word s t)
      (q : SPath ((SKM.pres D Sc).cod r).word s t) (Z : P.H t),
      P.wt t = ((SKM.pres D Sc).dom r).endR → compEval gens ((SKM.pres D Sc).rel r) p q Z = 0) :
    RelHolds Sc (P.layerRep Gs Ys gens) r := fun u v hw =>
  evalW_eq_zero_of_compEval_wt gens _ h u v hw

/-- **Reduction of a relation to its entries**: a relation of the presentation holds in the
swapped layer representation (under every whiskering) once all entries of the unwhiskered
relation vanish. -/
theorem relHolds_of_compEval (gens : P.Generators) (r : SKM.Rel D)
    (h : ∀ {s t : Sector I} (p : SPath ((SKM.pres D Sc).dom r).word s t)
      (q : SPath ((SKM.pres D Sc).cod r).word s t) (Z : P.H t),
      compEval gens ((SKM.pres D Sc).rel r) p q Z = 0) :
    RelHolds Sc (P.layerRep Gs Ys gens) r := fun u v hw =>
  evalW_eq_zero_of_compEval gens _ h u v hw

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
