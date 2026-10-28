/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Interpretation
import OddMath.QuiverHecke.SwappedAssembly.Sectors

/-! # The swapped objects as finite-support matrices, and the generator images

The objects `C_λ` of `docs/Nondegeneracy/SwappedActionAssembly.md`, (A1), are families over
the sectors of weight `λ`; the 1-morphism of a word of strands is the matrix of Hom-sector
functors indexed by summand paths (`SPath`), with finitely many nonzero entries in each row.
Evaluating at two fixed families `Gs`, `Ys` of sector objects gives, for an object `a` of the
free 2-category on the signature of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Definition 1.5, the module

  `Mod Gs Ys a = Π (s : Sector) (t : {t // wt t = a.endR}) (p : SPath a.word s t), Gs s ⟶ F_p (Ys t)`.

*Generator images.* `Generators` records, for every generator shape and every rightmost weight,
a component `F_p Z ⟶ F_{p'} Z` for each pair of summand paths `p` of the bottom boundary and `p'`
of the top boundary between the same sectors: the matrix entries of the image of the generator.
Only components are recorded; supernaturality (with the Koszul sign for odd generators) is part
of the interchange obligation. The prescribed entries are those of
`docs/Nondegeneracy/SwappedActionAssembly.md`, §§1–5; they are supplied by separate modules.

A layer `u ⊗ g ⊗ v` acts by the image of `g` in the middle and identities on the whiskers: the
entry at an output path `pu · p' · pv` is the sum over the paths `p` of the bottom boundary of
the input entry at `pu · p · pv`, followed by `F_{pu}` applied to the component of `g` at
`F_{pv} (Ys t)` (`layerMap`). This is the layer representation `layerRep`, to which the relation
obligations of `SwappedAssembly/Interpretation.lean` apply.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

theorem pathFunctor_append_append_obj {l m r : List (Col I X)} {s t s' t' : Sector I}
    (pu : SPath l s t) (pg : SPath m t s') (pv : SPath r s' t') (Z : P.H t') :
    (P.pathFunctor ((pu.append pg).append pv)).obj Z =
      (P.pathFunctor pu).obj ((P.pathFunctor pg).obj ((P.pathFunctor pv).obj Z)) := by
  rw [pathFunctor_append, pathFunctor_append]
  rfl

/-- The matrix entries of the image of the generator of shape `g` with rightmost weight `ν`:
a component for each pair of summand paths of its bottom and top boundaries. -/
def GenImage (g : SKM.Shape I) (ν : X) : Type u :=
  ∀ {t s : Sector I} (_p : SPath (wd D ν g.dom) t s) (_p' : SPath (wd D ν g.cod) t s)
    (Z : P.H s), (P.pathFunctor _p).obj Z ⟶ (P.pathFunctor _p').obj Z

/-- The images of the generators of Definition 1.5 and (2.6), one field per shape. -/
structure Generators where
  /-- The upward dot. -/
  dot : ∀ (i : I) (ν : X), P.GenImage (.dot i) ν
  /-- The upward crossing. -/
  cross : ∀ (i j : I) (ν : X), P.GenImage (.cross i j) ν
  /-- The rightward cup. -/
  cup : ∀ (i : I) (ν : X), P.GenImage (.cup i) ν
  /-- The rightward cap. -/
  cap : ∀ (i : I) (ν : X), P.GenImage (.cap i) ν
  /-- The leftward crossing. -/
  lcross : ∀ (i j : I) (ν : X), P.GenImage (.lcross i j) ν
  /-- The `♦`-cup with its label. -/
  dcup : ∀ (i : I) (n : ℕ) (ν : X), P.GenImage (.dcup i n) ν
  /-- The `♦`-cap with its label. -/
  dcap : ∀ (i : I) (n : ℕ) (ν : X), P.GenImage (.dcap i n) ν

variable {P}

/-- The image of a generator of the signature. -/
def Generators.image (gens : P.Generators) : (g : (SKM.sig D).Gen) → P.GenImage g.1 g.2
  | (.dot i, ν) => gens.dot i ν
  | (.cross i j, ν) => gens.cross i j ν
  | (.cup i, ν) => gens.cup i ν
  | (.cap i, ν) => gens.cap i ν
  | (.lcross i j, ν) => gens.lcross i j ν
  | (.dcup i n, ν) => gens.dcup i n ν
  | (.dcap i n, ν) => gens.dcap i n ν

variable (P) (Gs Ys : ∀ s, P.H s)

/-- The module of an object: the matrix entries `Gs s ⟶ F_p (Ys t)` over all summand paths
`p` of its word whose rightmost sector has the rightmost weight of the object. Each row `s`
has finitely many entries (`SPath.finite`). -/
def Mod (a : Obj (SKM.sig D)) : Type u :=
  ∀ (s : Sector I) (t : {t : Sector I // P.wt t = a.endR}) (p : SPath a.word s t.1),
    Gs s ⟶ (P.pathFunctor p).obj (Ys t.1)

instance (a : Obj (SKM.sig D)) : AddCommGroup (P.Mod Gs Ys a) := by
  unfold Mod; infer_instance

instance (a : Obj (SKM.sig D)) : Module k (P.Mod Gs Ys a) := by
  unfold Mod; infer_instance

variable {P Gs Ys}

@[simp] theorem Mod.add_apply {a : Obj (SKM.sig D)} (x y : P.Mod Gs Ys a) (s : Sector I)
    (t : {t : Sector I // P.wt t = a.endR}) (p : SPath a.word s t.1) :
    (x + y) s t p = x s t p + y s t p :=
  rfl

@[simp] theorem Mod.smul_apply {a : Obj (SKM.sig D)} (r : k) (x : P.Mod Gs Ys a) (s : Sector I)
    (t : {t : Sector I // P.wt t = a.endR}) (p : SPath a.word s t.1) :
    (r • x) s t p = r • x s t p :=
  rfl

/-- The entry of a layer at an output path `pu · p' · pv`, from the input path `pu · p · pv`.
-/
def layerEntry (gens : P.Generators) (L : Layer (SKM.sig D)) (hL : L.Valid) (x : P.Mod Gs Ys L.dom)
    {sl t s sr : Sector I} (pu : SPath L.left sl t) (pg : SPath ((SKM.sig D).dom L.gen) t s)
    (pg' : SPath ((SKM.sig D).cod L.gen) t s) (pv : SPath L.right s sr)
    (hq : P.wt sr = L.cod.endR) :
    Gs sl ⟶ (P.pathFunctor ((pu.append pg').append pv)).obj (Ys sr) :=
  x sl ⟨sr, hq.trans hL.endR_eq⟩ ((pu.append pg).append pv) ≫
    eqToHom (P.pathFunctor_append_append_obj pu pg pv (Ys sr)) ≫
    (P.pathFunctor pu).map (gens.image L.gen pg pg' ((P.pathFunctor pv).obj (Ys sr))) ≫
    eqToHom (P.pathFunctor_append_append_obj pu pg' pv (Ys sr)).symm

omit [AddCommGroup X] in
theorem append_split_split {l m r : List (Col I X)} {s t : Sector I}
    (q : SPath (l ++ m ++ r) s t) :
    ((SPath.split l (SPath.split (l ++ m) q).2.1).2.1.append
      (SPath.split l (SPath.split (l ++ m) q).2.1).2.2).append
        (SPath.split (l ++ m) q).2.2 = q := by
  rw [SPath.append_split, SPath.append_split]

open Classical in
/-- The action of a layer on the matrix entries (zero on an ill-formed layer). -/
def layerFun (gens : P.Generators) (L : Layer (SKM.sig D)) (x : P.Mod Gs Ys L.dom) :
    P.Mod Gs Ys L.cod := fun sl sr q =>
  if hL : L.Valid then
    letI := Fintype.ofFinite
    ∑ pg : SPath ((SKM.sig D).dom L.gen)
        (SPath.split L.left (SPath.split (L.left ++ (SKM.sig D).cod L.gen) q).2.1).1
        (SPath.split (L.left ++ (SKM.sig D).cod L.gen) q).1,
      layerEntry gens L hL x
          (SPath.split L.left (SPath.split (L.left ++ (SKM.sig D).cod L.gen) q).2.1).2.1 pg
          (SPath.split L.left (SPath.split (L.left ++ (SKM.sig D).cod L.gen) q).2.1).2.2
          (SPath.split (L.left ++ (SKM.sig D).cod L.gen) q).2.2 sr.2 ≫
        eqToHom (by rw [append_split_split])
  else 0

/-- The linear map of a layer. -/
def layerMap (gens : P.Generators) (L : Layer (SKM.sig D)) :
    P.Mod Gs Ys L.dom →ₗ[k] P.Mod Gs Ys L.cod where
  toFun := layerFun gens L
  map_add' x y := by
    funext sl sr q
    simp only [layerFun, Mod.add_apply]
    split_ifs with hL
    · simp only [layerEntry, Mod.add_apply, Preadditive.add_comp, Finset.sum_add_distrib]
    · simp
  map_smul' r x := by
    funext sl sr q
    simp only [layerFun, Mod.smul_apply, RingHom.id_apply]
    split_ifs with hL
    · simp only [layerEntry, Mod.smul_apply, Linear.smul_comp, Finset.smul_sum]
    · simp

variable (P Gs Ys) in
/-- **The swapped layer representation** with generator images `gens`, evaluated at the
families `Gs`, `Ys`. -/
def layerRep (gens : P.Generators) : LayerRep.{u, u, u, u, u} (SKM.sig D) k where
  M := P.Mod Gs Ys
  act := layerMap gens

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
