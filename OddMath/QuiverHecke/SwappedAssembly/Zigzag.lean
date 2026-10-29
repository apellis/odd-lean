/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.WhiskerReduction

/-! # The zigzag relations in the swapped layer representation

The relations `zigE` and `zigF` of `OddMath.SKM.Presentation` are the right adjunction (1.10)
of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5:
`(ε ⊗ 1)(1 ⊗ η) = 1` on `Eᵢ` and `(1 ⊗ ε)(η ⊗ 1) = 1` on `Fᵢ`.

By `relHolds_of_compEval` it suffices to check the unwhiskered relations entry by entry. The
boundary of either relation is a single strand, whose summand path is unique
(`SPath.eq_of_single`), so each relation is one matrix identity: the sum, over the summand
paths of the middle strand, of the composite of the entries of the cup and the cap is the
identity. `CupCapZigzag` states these two identities for the generator images, and
`zigzagRelations` deduces `ZigzagRelations` for the swapped layer representation.

Main declarations: `ProbeReservoir.CupCapZigzag`, `ProbeReservoir.zigzagRelations`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u

variable {I X : Type u}

namespace SPath

/-- The summand of a strand is determined by its sectors. -/
theorem side_eq_of_nextSector_eq {l : Letter I} {a b : Bool} {s : Sector I}
    (ha : StepValid l a s) (hb : StepValid l b s) (h : nextSector l a s = nextSector l b s) :
    a = b := by
  obtain ⟨_ | _, i⟩ := l <;> cases a <;> cases b <;> try rfl
  all_goals
    simp only [nextSector, Prod.mk.injEq] at h
    have h1 := congrArg (fun f => f i) h.1
    have h2 := congrArg (fun f => f i) h.2
    simp only [StepValid] at ha hb
    simp only [Finsupp.add_apply, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same] at h1 h2
    omega

theorem eq_of_nil {s t : Sector I} (p : SPath ([] : List (Col I X)) s t) : s = t := by
  cases p; rfl

/-- A single strand has at most one summand path between two sectors. -/
theorem eq_of_single {c : Col I X} {s t : Sector I} (p q : SPath [c] s t) : p = q := by
  cases p with
  | cons _ a _ ha p =>
    cases p
    cases q with
    | cons _ b _ hb q =>
      obtain rfl := side_eq_of_nextSector_eq hb ha (eq_of_nil q)
      rw [Subsingleton.elim q (.nil _)]

/-- Transport of a path along a change of the weight of its first strand. -/
theorem cast_cons_col {a : Letter I} {x y : X} {w w' : List (Col I X)} {s t : Sector I}
    (side : Bool) (hv : StepValid a side s) (p : SPath w (nextSector a side s) t)
    (h : (⟨a, x⟩ : Col I X) :: w = ⟨a, y⟩ :: w') :
    (SPath.cons ⟨a, x⟩ side s hv p).cast h =
      .cons ⟨a, y⟩ side s hv (p.cast (List.cons.inj h).2) := by
  obtain ⟨h₁, rfl⟩ := List.cons.inj h
  obtain rfl : x = y := (Col.mk.inj h₁).2
  rfl

/-- Two transports of the same path agree with transported targets. -/
theorem cast_eq_eq {w₀ w w' : List (Col I X)} {s t : Sector I} (h₁ : w₀ = w) (h₂ : w₀ = w')
    (x : SPath w₀ s t) (y : SPath w s t) (y' : SPath w' s t)
    (hy : y = y'.cast (h₂.symm.trans h₁)) : (x.cast h₁ = y) = (x.cast h₂ = y') := by
  subst h₁ h₂ hy
  rfl

end SPath

variable [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-- Equal paths of a word cut into three parts give equal objects. -/
theorem obj_eq_of_cast_eq {l m r l' m' r' : List (Col I X)} (hw : l ++ m ++ r = l' ++ m' ++ r')
    {s x y t x' y' : Sector I} (p₁ : SPath l s x) (p₂ : SPath m x y) (p₃ : SPath r y t)
    (p₄ : SPath l' s x') (p₅ : SPath m' x' y') (p₆ : SPath r' y' t)
    (h : ((p₁.append p₂).append p₃).cast hw = (p₄.append p₅).append p₆) (Z : P.H t) :
    (P.pathFunctor p₁).obj ((P.pathFunctor p₂).obj ((P.pathFunctor p₃).obj Z)) =
      (P.pathFunctor p₄).obj ((P.pathFunctor p₅).obj ((P.pathFunctor p₆).obj Z)) := by
  rw [← pathFunctor_append_append_obj, ← pathFunctor_append_append_obj, ← h, pathFunctor_cast]

theorem zigE_word (D : Datum I X) (i : I) (ν : X) :
    wd D ν [up i] ++ wd D ν (Shape.cup i).cod ++ [] =
      [] ++ wd D (SKM.wt D ν [up i]) (Shape.cap i).dom ++ wd D ν [up i] := by
  show [(⟨up i, ν⟩ : Col I X), ⟨dn i, SKM.wt D ν [up i]⟩, ⟨up i, ν⟩] =
    [⟨up i, SKM.wt D (SKM.wt D ν [up i]) [dn i]⟩, ⟨dn i, SKM.wt D ν [up i]⟩, ⟨up i, ν⟩]
  simp [sh]

theorem zigF_word (D : Datum I X) (i : I) (ν : X) :
    [] ++ wd D (SKM.wt D ν [dn i]) (Shape.cup i).cod ++ wd D ν [dn i] =
      wd D ν [dn i] ++ wd D ν (Shape.cap i).dom ++ [] := by
  show [(⟨dn i, SKM.wt D (SKM.wt D ν [dn i]) [up i]⟩ : Col I X), ⟨up i, SKM.wt D ν [dn i]⟩,
    ⟨dn i, ν⟩] = [⟨dn i, ν⟩, ⟨up i, SKM.wt D ν [dn i]⟩, ⟨dn i, ν⟩]
  simp [sh]

variable {P}

open Classical in
/-- **The zigzag identities for the cup and cap images** (Brundan–Ellis, arXiv:1701.04133v2,
(1.10)), entry by entry. For a strand `Eᵢ` (resp. `Fᵢ`) with summand path `q`, the sum over the
summand paths `m` of the cup and `r` of the cap that agree with `q` and with each other on the
three strands of the middle object, of the composite of the cup entry and the cap entry, is the
identity of the summand `F_q Z`. -/
structure CupCapZigzag (gens : P.Generators) : Prop where
  /-- `(ε ⊗ 1)(1 ⊗ η) = 1` on `Eᵢ 1_ν`. -/
  zigE : ∀ (i : I) (ν : X) {s t : Sector I} (q : SPath (wd D ν [up i]) s t) (Z : P.H t),
    letI := Fintype.ofFinite (SPath (wd D ν (Shape.cup i).cod) t t)
    letI := Fintype.ofFinite (SPath (wd D (SKM.wt D ν [up i]) (Shape.cap i).dom) s s)
    ∑ m : SPath (wd D ν (Shape.cup i).cod) t t,
      ∑ r : SPath (wd D (SKM.wt D ν [up i]) (Shape.cap i).dom) s s,
        (if h : ((q.append m).append (.nil t)).cast (zigE_word D i ν) =
            ((SPath.nil s).append r).append q then
          (P.pathFunctor q).map (gens.cup i ν (.nil t) m Z) ≫
            eqToHom (P.obj_eq_of_cast_eq _ q m (.nil t) (.nil s) r q h Z) ≫
            gens.cap i (SKM.wt D ν [up i]) r (.nil s) ((P.pathFunctor q).obj Z)
        else 0) = 𝟙 _
  /-- `(1 ⊗ ε)(η ⊗ 1) = 1` on `Fᵢ 1_ν`. -/
  zigF : ∀ (i : I) (ν : X) {s t : Sector I} (q : SPath (wd D ν [dn i]) s t) (Z : P.H t),
    letI := Fintype.ofFinite (SPath (wd D (SKM.wt D ν [dn i]) (Shape.cup i).cod) s s)
    letI := Fintype.ofFinite (SPath (wd D ν (Shape.cap i).dom) t t)
    ∑ m : SPath (wd D (SKM.wt D ν [dn i]) (Shape.cup i).cod) s s,
      ∑ r : SPath (wd D ν (Shape.cap i).dom) t t,
        (if h : (((SPath.nil s).append m).append q).cast (zigF_word D i ν) =
            (q.append r).append (.nil t) then
          gens.cup i (SKM.wt D ν [dn i]) (.nil s) m ((P.pathFunctor q).obj Z) ≫
            eqToHom (P.obj_eq_of_cast_eq _ (.nil s) m q q r (.nil t) h Z) ≫
            (P.pathFunctor q).map (gens.cap i ν r (.nil t) Z)
        else 0) = 𝟙 _

/-- The entry of the difference of two diagrams. -/
theorem compEval_single_sub_single (gens : P.Generators) {a b : Obj (SKM.sig D)} (d e : a ⟶ b)
    {s t : Sector I} (p : SPath a.word s t) (q : SPath b.word s t) (Z : P.H t) :
    compEval gens (Finsupp.single d (1 : k) - Finsupp.single e 1) p q Z =
      compDiag gens d p q Z - compDiag gens e p q Z := by
  unfold compEval
  rw [Finsupp.sum_sub_index (fun _ _ _ => sub_smul _ _ _), Finsupp.sum_single_index (by simp),
    Finsupp.sum_single_index (by simp), one_smul, one_smul]

open Classical in
/-- The entry of an identity diagram. -/
theorem compDiag_id (gens : P.Generators) {a : Obj (SKM.sig D)} {s t : Sector I}
    (p q : SPath a.word s t) (Z : P.H t) :
    compDiag gens (𝟙 a) p q Z = if h : p = q then eqToHom (by rw [h]) else 0 :=
  compList_nil gens p q Z

/-- The entry of a chain of one layer. -/
theorem compList_one (gens : P.Generators) (L : Layer (SKM.sig D)) {a b : Obj (SKM.sig D)}
    (h : Chain a [L] b) {s t : Sector I} (p : SPath a.word s t) (q : SPath b.word s t)
    (Z : P.H t) :
    compList gens [L] h p q Z =
      eqToHom (by rw [pathFunctor_cast]) ≫
        compLayer gens L (p.cast (congrArg Obj.word h.2.1.symm))
          (q.cast (congrArg Obj.word h.2.2.symm)) Z ≫
        eqToHom (by rw [pathFunctor_cast]) := by
  classical
  obtain ⟨hv, rfl, rfl⟩ := h
  let _ : Fintype (SPath L.cod.word s t) := Fintype.ofFinite _
  rw [compList_cons gens L [] hv rfl]
  simp only [compList_nil, SPath.cast_rfl, eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [Finset.sum_eq_single q (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem zigE_entry (gens : P.Generators) (hz : CupCapZigzag gens) (i : I) (ν : X)
    (hc : Chain (SKM.ob D ν [up i])
      (SKM.layList D ν [([up i], Shape.cup i, []), ([], Shape.cap i, [up i])])
      (SKM.ob D ν [up i])) {s t : Sector I} (q : SPath [(⟨up i, ν⟩ : Col I X)] s t)
    (Z : P.H t) :
    compList gens _ hc q q Z = 𝟙 _ := by
  classical
  have hq := hz.zigE i ν q Z
  cases q with
  | cons _ σ _ hv q =>
  cases q
  obtain ⟨hv₁, h₁, hc'⟩ := hc
  erw [compList.eq_2]
  simp only [List.map_cons, List.map_nil, compList_one]
  let _ : Fintype (SPath.Dec (wd D ν [up i]) (wd D ν (Shape.cup i).cod) []
    s (nextSector (up i) σ s)) := Fintype.ofFinite _
  let _ : Fintype (SPath (wd D ν (Shape.cup i).cod) (nextSector (up i) σ s)
    (nextSector (up i) σ s)) := Fintype.ofFinite _
  let _ : Fintype (SPath (wd D ν [up i] ++ wd D ν (Shape.cup i).cod ++ []) s
    (nextSector (up i) σ s)) := Fintype.ofFinite _
  refine (SPath.sum_cast_dec (l := wd D ν [up i]) (m := wd D ν (Shape.cup i).cod) (r := [])
    rfl _).trans ?_
  rw [SPath.sum_dec_eq (l := wd D ν [up i]) (r := []) (.cons _ σ s hv (.nil _)) (.nil _)]
  · refine Eq.trans ?_ hq
    refine Finset.sum_congr rfl fun m _ => ?_
    erw [compLayer_eq gens (SKM.lay D ν [up i] (Shape.cup i) []) (.cons _ σ s hv (.nil _))
      (.nil _) m (.nil _) Z]
    erw [compLayer_eq_compLayerAt gens (SKM.lay D ν [] (Shape.cap i) [up i]) _ _ Z
      ⟨(s, s), .nil s, .nil s, .cons _ σ s hv (.nil _)⟩ (SPath.decOf_path _)]
    unfold compLayerAt
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, comp_dite, dite_comp,
      Limits.comp_zero, Limits.zero_comp]
    refine Finset.sum_congr rfl fun r _ => ?_
    refine dite_congr ?_ (fun h => ?_) (fun _ => rfl)
    · simp only [SPath.cast_cast, SPath.Dec.path]
      rfl
    · simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, Category.comp_id]
      rfl
  · rintro ⟨⟨x, y⟩, pu, mm, pv⟩ hd
    erw [compLayer_eq_zero gens (SKM.lay D ν [up i] (Shape.cup i) [])
      ⟨(_, _), .cons _ σ s hv (.nil _), .nil _, .nil _⟩ ⟨(x, y), pu, mm, pv⟩ (Ne.symm hd) Z]
    simp

theorem zigF_entry (gens : P.Generators) (hz : CupCapZigzag gens) (i : I) (ν : X)
    (hc : Chain (SKM.ob D ν [dn i])
      (SKM.layList D ν [([], Shape.cup i, [dn i]), ([dn i], Shape.cap i, [])])
      (SKM.ob D ν [dn i])) {s t : Sector I} (q : SPath [(⟨dn i, ν⟩ : Col I X)] s t)
    (Z : P.H t) :
    compList gens _ hc q q Z = 𝟙 _ := by
  classical
  have hq := hz.zigF i ν q Z
  cases q with
  | cons _ σ _ hv q =>
  cases q
  obtain ⟨hv₁, h₁, hc'⟩ := hc
  erw [compList.eq_2]
  simp only [List.map_cons, List.map_nil, compList_one]
  let _ : Fintype (SPath.Dec [] (wd D (SKM.wt D ν [dn i]) (Shape.cup i).cod) (wd D ν [dn i])
    s (nextSector (dn i) σ s)) := Fintype.ofFinite _
  let _ : Fintype (SPath (wd D (SKM.wt D ν [dn i]) (Shape.cup i).cod) s s) := Fintype.ofFinite _
  let _ : Fintype (SPath ([] ++ wd D (SKM.wt D ν [dn i]) (Shape.cup i).cod ++ wd D ν [dn i]) s
    (nextSector (dn i) σ s)) := Fintype.ofFinite _
  refine (SPath.sum_cast_dec (l := []) (m := wd D (SKM.wt D ν [dn i]) (Shape.cup i).cod)
    (r := wd D ν [dn i]) rfl _).trans ?_
  rw [SPath.sum_dec_eq (l := []) (r := wd D ν [dn i]) (.nil _) (.cons _ σ s hv (.nil _))]
  · refine Eq.trans ?_ hq
    refine Finset.sum_congr rfl fun m _ => ?_
    erw [compLayer_eq gens (SKM.lay D ν [] (Shape.cup i) [dn i]) (.nil _) (.nil _) m
      (.cons _ σ s hv (.nil _)) Z]
    erw [compLayer_eq_compLayerAt gens (SKM.lay D ν [dn i] (Shape.cap i) []) _ _ Z
      ⟨(_, _), .cons _ σ s hv (.nil _), .nil _, .nil _⟩
      (by
        erw [SPath.cast_cons_col, SPath.cast_self]
        exact SPath.decOf_path (l := (SKM.lay D ν [dn i] (Shape.cap i) []).left)
          (m := (SKM.sig D).cod (SKM.lay D ν [dn i] (Shape.cap i) []).gen)
          (r := (SKM.lay D ν [dn i] (Shape.cap i) []).right)
          ⟨(_, _), .cons _ σ s hv (.nil _), .nil _, .nil _⟩)]
    unfold compLayerAt
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, comp_dite, dite_comp,
      Limits.comp_zero, Limits.zero_comp]
    refine Finset.sum_congr rfl fun r _ => ?_
    refine dite_congr ?_ (fun h => ?_) (fun _ => rfl)
    · simp only [SPath.cast_cast, SPath.Dec.path]
      refine SPath.cast_eq_eq _ _ _ _ _ ?_
      refine Eq.trans ?_ (SPath.cast_cons_col σ hv (((SPath.nil _).append r).append
        (SPath.nil _)) _).symm
      rfl
    · simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
        Category.id_comp, Category.comp_id]
      rfl
  · rintro ⟨⟨x, y⟩, pu, mm, pv⟩ hd
    erw [compLayer_eq_zero gens (SKM.lay D ν [] (Shape.cup i) [dn i])
      ⟨(_, _), .nil _, .nil _, .cons _ σ s hv (.nil _)⟩ ⟨(x, y), pu, mm, pv⟩ (Ne.symm hd) Z]
    simp

variable {Gs Ys : ∀ s, P.H s}

/-- **`ZigzagRelations` for the swapped layer representation**: the zigzag relations
`zigE` and `zigF` of (1.10) hold, whiskered arbitrarily, as soon as the cup and cap images
satisfy the entrywise zigzag identities `CupCapZigzag`. -/
theorem zigzagRelations {gens : P.Generators} (hz : CupCapZigzag gens) :
    ZigzagRelations Sc (P.layerRep Gs Ys gens) := by
  intro r hr
  cases r with
  | zigE i ν =>
    refine relHolds_of_compEval gens _ fun p q Z => ?_
    obtain rfl : p = q := SPath.eq_of_single (c := ⟨up i, ν⟩) p q
    change compEval gens (Finsupp.single _ (1 : k) - Finsupp.single (𝟙 _) 1) p p Z = 0
    rw [compEval_single_sub_single, sub_eq_zero]
    refine (zigE_entry gens hz i ν _ p Z).trans ?_
    erw [compDiag_id]
    simp
  | zigF i ν =>
    refine relHolds_of_compEval gens _ fun p q Z => ?_
    obtain rfl : p = q := SPath.eq_of_single (c := ⟨dn i, ν⟩) p q
    change compEval gens (Finsupp.single _ (1 : k) - Finsupp.single (𝟙 _) 1) p p Z = 0
    rw [compEval_single_sub_single, sub_eq_zero]
    refine (zigF_entry gens hz i ν _ p Z).trans ?_
    erw [compDiag_id]
    simp
  | _ => simp [relGroup] at hr

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
