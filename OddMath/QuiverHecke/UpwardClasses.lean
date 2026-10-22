/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.GrothendieckIntegral
import OddMath.QuiverHecke.DividedPowerSpan
import OddMath.QuiverHecke.CentreFinite
import OddMath.QuiverHecke.SerreDividedPowers
import OddMath.QuiverHecke.SerreClassUp

/-!
# The class map of the upward functor `α`

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity, class step. The paper
compares classes in `K₀(Ḣ_{q,π})` with classes in `K₀(𝔘̇(𝔤))` through the map induced by the
upward functor `α` of (11.7). For a fixed right weight `ν`, `α_ν` sends a word `t` to the
1-morphism `E_t 1_ν` from `μ = wt_ν(t)` to `ν`, so only the words of one weight land in a fixed
hom category `Hom(μ, ν)`.

* `Mat_.restrictMap hP F`: keep the entries of a matrix that lie in an object property `P`, then
  apply `F : P.FullSubcategory ⥤ D`; a functor when morphisms from objects in `P` to objects
  outside `P` vanish. Its value on a one-entry matrix is the one-entry matrix of the image
  (`Mat_.mapFun_restrictMap_single`) or zero (`Mat_.isZero_mapFun_restrictMap_single`).
* `Karoubi.mapFun G`: the functor on Karoubi envelopes induced by `G`.
* `upFun μ ν`: `α_ν` on the shifted words of weight `wt_ν = μ`, into the even degree-zero
  envelope of `Hom(μ, ν)`; morphisms between words of different weights vanish
  (`wtProp_hom_eq_zero`, since nonzero morphisms permute the letters).
* `upK0 μ ν : K₀(Ḣ_{q,π}) →+ K₀(𝔘̇(𝔤))`, with `[Q^n Π^p (t, e)] ↦ [Q^n Π^p (E_t 1_ν, α(e))]`
  when `wt_ν(t) = μ` (`upK0_raw`) and `↦ 0` otherwise (`upK0_raw_of_ne`).
-/

noncomputable section

namespace CategoryTheory.Mat_

variable {C : Type*} [Category C] [Preadditive C] {D : Type*} [Category D] [Preadditive D]
  {P : ObjectProperty C} (hP : ∀ {X Y : C}, P X → ¬ P Y → ∀ f : X ⟶ Y, f = 0)
  (F : P.FullSubcategory ⥤ D) [F.Additive]

/-- `homMk` as an additive map. -/
def homMkAdd {X Y : P.FullSubcategory} : (X.obj ⟶ Y.obj) →+ (X ⟶ Y) where
  toFun := ObjectProperty.homMk
  map_zero' := rfl
  map_add' _ _ := rfl

open Classical in
/-- Matrices restricted to the entries in `P`, followed by `F`. Well defined as a functor when
morphisms from objects in `P` to objects outside `P` vanish. -/
def restrictMap : Mat_ C ⥤ Mat_ D where
  obj M := ⟨{i // P (M.X i)}, fun i => F.obj ⟨M.X i.1, i.2⟩⟩
  map f i j := F.map (ObjectProperty.homMk (f i.1 j.1))
  map_id M := by
    ext i j
    rw [id_apply, id_apply]
    by_cases h : i = j
    · subst h
      simp only [dite_true, eqToHom_refl]
      exact F.map_id _
    · have h' : i.1 ≠ j.1 := fun e => h (Subtype.ext e)
      simp [h, h']
  map_comp {M N K} f g := by
    ext i k
    change F.map (ObjectProperty.homMk (P := P) (X := ⟨M.X i.1, i.2⟩) (Y := ⟨K.X k.1, k.2⟩)
        (∑ j, f i.1 j ≫ g j k.1)) =
      ∑ j : {j // P (N.X j)}, F.map (ObjectProperty.homMk (P := P) (X := ⟨M.X i.1, i.2⟩)
        (Y := ⟨N.X j.1, j.2⟩) (f i.1 j.1)) ≫
        F.map (ObjectProperty.homMk (P := P) (X := ⟨N.X j.1, j.2⟩) (Y := ⟨K.X k.1, k.2⟩)
          (g j.1 k.1))
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j => P (N.X j))]
    rw [Finset.sum_eq_zero (s := Finset.univ)
        (f := fun j : {j // ¬ P (N.X j)} => f i.1 j.1 ≫ g j.1 k.1)
        (fun j _ => by rw [hP i.2 j.2 (f i.1 j.1), Limits.zero_comp]), add_zero]
    change F.map (homMkAdd (∑ j : {j // P (N.X j)}, _)) = _
    rw [map_sum, F.map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← F.map_comp]
    rfl

instance : (restrictMap hP F).Additive where
  map_add {M N f g} := by
    ext i j
    change F.map (homMkAdd (P := P) (X := ⟨M.X i.1, i.2⟩) (Y := ⟨N.X j.1, j.2⟩)
      (f i.1 j.1 + g i.1 j.1)) = F.map (homMkAdd (f i.1 j.1)) + F.map (homMkAdd (g i.1 j.1))
    rw [map_add, F.map_add]

/-- The index set of a restricted one-entry matrix with entry in `P`. -/
abbrev uniqueRestrictEmbedding (X : C) (hX : P X) :
    Unique ((restrictMap hP F).obj ((embedding C).obj X)).ι :=
  ⟨⟨⟨PUnit.unit, hX⟩⟩, fun _ => Subtype.ext rfl⟩

/-- On a one-entry matrix whose entry is in `P`, `restrictMap` is the one-entry matrix of the
image. -/
def restrictMapEmbeddingIso (X : C) (hX : P X) :
    (restrictMap hP F).obj ((embedding C).obj X) ≅ (embedding D).obj (F.obj ⟨X, hX⟩) where
  hom := (fun _ _ => 𝟙 _ : Hom ((restrictMap hP F).obj ((embedding C).obj X))
    ((embedding D).obj (F.obj ⟨X, hX⟩)))
  inv := (fun _ _ => 𝟙 _ : Hom ((embedding D).obj (F.obj ⟨X, hX⟩))
    ((restrictMap hP F).obj ((embedding C).obj X)))
  hom_inv_id := by
    let := uniqueRestrictEmbedding hP F X hX
    let : Unique ((embedding D).obj (F.obj ⟨X, hX⟩)).ι := inferInstanceAs (Unique PUnit)
    refine hom_ext _ _ fun i j => ?_
    have : i = j := Subtype.ext (Subsingleton.elim (α := PUnit) _ _)
    subst this
    erw [comp_apply, id_apply_self, Fintype.sum_unique]
    exact Category.comp_id _
  inv_hom_id := by
    let := uniqueRestrictEmbedding hP F X hX
    let : Unique ((embedding D).obj (F.obj ⟨X, hX⟩)).ι := inferInstanceAs (Unique PUnit)
    refine hom_ext _ _ fun i j => ?_
    have : i = j := Subsingleton.elim (α := PUnit) _ _
    subst this
    erw [comp_apply, id_apply_self, Fintype.sum_unique]
    exact Category.comp_id _

theorem restrictMapEmbeddingIso_naturality (X : C) (hX : P X) (e : X ⟶ X) :
    (restrictMap hP F).map ((embedding C).map e) ≫ (restrictMapEmbeddingIso hP F X hX).hom =
      (restrictMapEmbeddingIso hP F X hX).hom ≫
        (embedding D).map (F.map (ObjectProperty.homMk e)) := by
  let := uniqueRestrictEmbedding hP F X hX
  let : Unique ((embedding D).obj (F.obj ⟨X, hX⟩)).ι := inferInstanceAs (Unique PUnit)
  refine hom_ext _ _ fun i j => ?_
  erw [comp_apply, comp_apply]
  erw [Fintype.sum_unique, Fintype.sum_unique]
  simp [restrictMapEmbeddingIso, restrictMap, embedding]

end CategoryTheory.Mat_

namespace CategoryTheory.Idempotents.Karoubi

variable {C : Type*} [Category C] [Preadditive C] {D : Type*} [Category D] [Preadditive D]

/-- The functor `Karoubi C ⥤ Karoubi D` induced by a functor `C ⥤ D`. -/
@[simps]
def mapFun (G : C ⥤ D) : Karoubi C ⥤ Karoubi D where
  obj P := ⟨G.obj P.X, G.map P.p, by rw [← G.map_comp, P.idem]⟩
  map {P Q} f := ⟨G.map f.f, by
    change G.map P.p ≫ G.map f.f ≫ G.map Q.p = _
    rw [← G.map_comp, ← G.map_comp, f.comm]⟩

instance (G : C ⥤ D) [G.Additive] : (mapFun G).Additive where
  map_add := Karoubi.hom_ext_iff.2 (G.map_add)

end CategoryTheory.Idempotents.Karoubi

namespace CategoryTheory.Mat_

open Idempotents StringDiagrams Limits

variable {C : Type*} [Category C] [Preadditive C] {D : Type*} [Category D] [Preadditive D]
  {P : ObjectProperty C} (hP : ∀ {X Y : C}, P X → ¬ P Y → ∀ f : X ⟶ Y, f = 0)
  (F : P.FullSubcategory ⥤ D) [F.Additive]

/-- The summand `(X, e)` of the one-entry matrix `X`. -/
abbrev oneEntry (X : C) (e : X ⟶ X) (he : e ≫ e = e) : Karoubi (Mat_ C) :=
  ⟨(embedding C).obj X, (embedding C).map e, by rw [← Functor.map_comp, he]⟩

theorem mapFun_restrictMap_single (X : C) (hX : P X) (e : X ⟶ X) (he : e ≫ e = e) :
    Nonempty ((Karoubi.mapFun (restrictMap hP F)).obj (oneEntry X e he) ≅
      oneEntry (F.obj ⟨X, hX⟩) (F.map (ObjectProperty.homMk e)) (by
        rw [← F.map_comp]; exact congrArg F.map (InducedCategory.hom_ext he))) :=
  ⟨Karoubi.mkIso (restrictMapEmbeddingIso hP F X hX)
    (restrictMapEmbeddingIso_naturality hP F X hX e)⟩

theorem isZero_mapFun_restrictMap_single (X : C) (hX : ¬ P X) (e : X ⟶ X) (he : e ≫ e = e) :
    IsZero ((Karoubi.mapFun (restrictMap hP F)).obj (oneEntry X e he)) := by
  have : IsEmpty ((Karoubi.mapFun (restrictMap hP F)).obj (oneEntry X e he)).X.ι :=
    ⟨fun i => hX i.2⟩
  rw [IsZero.iff_id_eq_zero]
  exact Karoubi.hom_ext_iff.2 (hom_ext _ _ fun i => isEmptyElim i)

end CategoryTheory.Mat_

namespace OddMath.QuiverHecke

open CategoryTheory StringDiagrams GradedSupercategory OddMath.SKM.Summands

variable {I : Type*} {X : Type*} [AddCommGroup X] {D : SKM.Datum I X} {k : Type*} [CommRing k]
  {Sc : SKM.Scalars D k} {sy : SKM.Symmetrizer D} {hc : Sc.Homogeneous}

theorem wt_eq_sum (μ : X) (t : List (SKM.Letter I)) :
    SKM.wt D μ t = (t.map (SKM.sh D)).sum + μ := by
  induction t with
  | nil => simp
  | cons l t ih => rw [SKM.wt_cons, ih, List.map_cons, List.sum_cons, add_assoc]

theorem wt_upWord_perm (μ : X) {t t' : List I} (h : t'.Perm t) :
    SKM.wt D μ (upWord t') = SKM.wt D μ (upWord t) := by
  rw [wt_eq_sum, wt_eq_sum, upWord, upWord, ((h.map SKM.up).map (SKM.sh D)).sum_eq]

variable (Sc sy hc) in
/-- The words `t` with `wt_ν(t) = μ`, i.e. those `α_ν` sends into `Hom(μ, ν)`. -/
def wtProp (μ ν : X) : ObjectProperty (Base k (HGr D Sc sy hc)) :=
  fun Y => SKM.wt D ν (upWord Y.obj.obj.obj.obj.as.word) = μ

theorem wtProp_hom_eq_zero {μ ν : X} {Y Y' : Base k (HGr D Sc sy hc)} (hY : wtProp Sc sy hc μ ν Y)
    (hY' : ¬ wtProp Sc sy hc μ ν Y') (f : Y ⟶ Y') : f = 0 := by
  have h : f.1.1 = 0 := hom_eq_zero_of_not_perm D Sc (t := Y.obj.obj.obj.obj.as.word)
    (t' := Y'.obj.obj.obj.obj.as.word) (fun hp => hY' ((wt_upWord_perm ν hp).trans hY)) f.1.1
  exact Subtype.ext (Subtype.ext h)

variable (Sc sy hc) in
/-- **The upward map `α_ν` on the words of weight `μ`**, on the even degree-zero envelopes:
`Q^n Π^p t ↦ Q^n Π^p E_t 1_ν`. -/
def upFun (μ ν : X) :
    (wtProp Sc sy hc μ ν).FullSubcategory ⥤ Base k (SerreComplex.UHom D Sc sy hc μ ν) where
  obj Y := shifted (k := k)
    (SKM.K0Relations.word Sc sy hc μ ν (upWord Y.obj.obj.obj.obj.obj.as.word)
    Y.property) Y.obj.obj.obj.obj.shift Y.obj.obj.obj.par
  map {Y Y'} f := ⟨⟨(alpha D Sc ν).map f.hom.1.1, by
      have h := f.hom.1.2
      change f.hom.1.1 ∈ GradedSupercategory.degree (R := k) (C := HGr D Sc sy hc) _ _
        (0 + (Y.obj.obj.obj.obj.shift - Y'.obj.obj.obj.obj.shift)) at h
      exact alpha_mem_degree D Sc sy ν h⟩, by
      have h := f.hom.2
      change f.hom.1.1 ∈ Supercategory.parity (R := k) (C := HGr D Sc sy hc) _ _
        (0 + (Y.obj.obj.obj.par + Y'.obj.obj.obj.par)) at h
      exact alpha_mem_parity D Sc ν h⟩
  map_id Y := Subtype.ext (Subtype.ext ((alpha D Sc ν).map_id _))
  map_comp f g := Subtype.ext (Subtype.ext ((alpha D Sc ν).map_comp _ _))

instance (μ ν : X) : (upFun Sc sy hc μ ν).Additive where
  map_add {_ _ f g} := Subtype.ext (Subtype.ext ((alpha D Sc ν).map_add (f := f.hom.1.1)
    (g := g.hom.1.1)))

/-- `α_ν(e)` on the 1-morphism `E_t 1_ν` from `μ` to `ν`. -/
def upProj {μ ν : X} {t : List I} (h : SKM.wt D ν (upWord t) = μ) (e : HEnd D Sc sy hc t) :
    SKM.K0Relations.word Sc sy hc μ ν _ h ⟶ SKM.K0Relations.word Sc sy hc μ ν _ h :=
  (alpha D Sc ν).map e

theorem upProj_idem {μ ν : X} {t : List I} (h : SKM.wt D ν (upWord t) = μ)
    {e : HEnd D Sc sy hc t} (he : e ≫ e = e) : upProj h e ≫ upProj h e = upProj h e := by
  change (alpha D Sc ν).map _ ≫ (alpha D Sc ν).map _ = _
  rw [← Functor.map_comp]
  exact congrArg _ he

variable (Sc sy hc) in
/-- **The class map `[α_ν] : K₀(Ḣ_{q,π}) → K₀(𝔘̇(𝔤))`, component `Hom(μ, ν)`**: the additive
functor induced by `α_ν` on the summands of the words of weight `wt_ν = μ`, the other words
being sent to zero. -/
def upK0 (μ ν : X) : K₀ (HKar D Sc sy hc) →+ SKM.K0Relations.Grothendieck Sc sy hc :=
  (SerreComplex.toGr sy hc μ ν).comp
    (K₀.map (Idempotents.Karoubi.mapFun (Mat_.restrictMap (P := wtProp Sc sy hc μ ν)
      (fun hY hY' f => wtProp_hom_eq_zero hY hY' f) (upFun Sc sy hc μ ν))))

theorem upK0_raw {μ ν : X} {t : List I} {e : HEnd D Sc sy hc t} (he : e ≫ e = e)
    (hd : e ∈ GradedSupercategory.degree (R := k) _ _ 0)
    (hp : e ∈ Supercategory.parity (R := k) _ _ 0) (n : ℤ) (p : ZMod 2)
    (h : SKM.wt D ν (upWord t) = μ) :
    upK0 Sc sy hc μ ν (K₀.mk (raw he hd hp n p)) =
      SerreComplex.rcls sy hc (upProj_idem h he) (alpha_mem_degree D Sc sy ν hd)
        (alpha_mem_parity D Sc ν hp) n p := by
  rw [upK0, AddMonoidHom.comp_apply, K₀.map_mk]
  obtain ⟨i⟩ := Mat_.mapFun_restrictMap_single (P := wtProp Sc sy hc μ ν)
    (fun hY hY' f => wtProp_hom_eq_zero hY hY' f) (upFun Sc sy hc μ ν)
    (shifted (k := k) (hObj D Sc sy hc t) n p) h _
    (projector_idem he hd hp n p)
  exact (congrArg (SerreComplex.toGr sy hc μ ν) (K₀.mk_eq_mk_of_iso i)).trans rfl

theorem upK0_raw_of_ne {μ ν : X} {t : List I} {e : HEnd D Sc sy hc t} (he : e ≫ e = e)
    (hd : e ∈ GradedSupercategory.degree (R := k) _ _ 0)
    (hp : e ∈ Supercategory.parity (R := k) _ _ 0) (n : ℤ) (p : ZMod 2)
    (h : SKM.wt D ν (upWord t) ≠ μ) :
    upK0 Sc sy hc μ ν (K₀.mk (raw he hd hp n p)) = 0 := by
  rw [upK0, AddMonoidHom.comp_apply, K₀.map_mk]
  have hz := Mat_.isZero_mapFun_restrictMap_single (P := wtProp Sc sy hc μ ν)
    (fun hY hY' f => wtProp_hom_eq_zero hY hY' f) (upFun Sc sy hc μ ν)
    (shifted (k := k) (hObj D Sc sy hc t) n p) h _ (projector_idem he hd hp n p)
  exact (congrArg (SerreComplex.toGr sy hc μ ν) (K₀.mk_eq_mk_of_iso hz.isoZero)).trans
    (by rw [K₀.mk_zero, map_zero])

end OddMath.QuiverHecke
