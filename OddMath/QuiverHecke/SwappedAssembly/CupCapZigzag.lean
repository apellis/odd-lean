/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Zigzag
import OddMath.QuiverHecke.SwappedAssembly.Generators

/-! # The zigzag identities for the swapped cup and cap

The images `cupImage` and `capImage` of the rightward cup and cap satisfy the right adjunction
(1.10) of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5,
entry by entry: `CupCapZigzag (swappedGens c L)`.

For a strand with summand `σ`, the only summand paths of the cup and of the cap that agree with
it on the middle object are the ones running through `σ` twice (a closed two-letter path of
`Fᵢ Eᵢ` or `Eᵢ Fᵢ` stays in one summand). On that term the cup and the cap are the unit and the
counit of the same content-shifted adjunction (`homContentPreAdjunction` for a probe strand,
`homContentPostAdjunction` for a reservoir strand), up to the transport of the inner strand
along an equality of sectors, so the composite is the identity by the triangle identities.

Main declaration: `ProbeReservoir.cupCapZigzag_swappedGens`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u v₁ v₂ u₁ u₂ w

section Triangle

/-- A triangle identity of a family of adjunctions, with the counit taken at an index equal
to that of the unit and with the objects matched along equalities. -/
theorem triangle_left_of_eq {A : Type u₁} [Category.{v₁} A] {Xb : Type w}
    {C : Xb → Type u₂} [∀ b, Category.{v₂} (C b)] {Pr : Xb → Prop}
    (E : ∀ b, Pr b → A ⥤ C b) (F : ∀ b, Pr b → C b ⥤ A) (adj : ∀ b h, E b h ⊣ F b h)
    {b b' : Xb} (eb : b = b') (h : Pr b) (h' : Pr b')
    {Y₀ Y V W : A} {U : C b} {V₁ Y₂ : C b'} (x₁ : Y₀ = Y) (x₂ : (E b h).obj Y = U)
    (x₃ : (F b h).obj U = V) (x₄ : (E b' h').obj V = V₁) (x₅ : V₁ = (E b' h').obj W)
    (x₆ : W = (F b' h').obj Y₂) (x₇ : Y₂ = (E b' h').obj Y₀) :
    (E b' h').map (eqToHom x₁ ≫ ((adj b h).unit.app Y ≫ (F b h).map (eqToHom x₂)) ≫
        eqToHom x₃) ≫ eqToHom x₄ ≫ eqToHom x₅ ≫
      (((E b' h').map (eqToHom x₆) ≫ (adj b' h').counit.app Y₂) ≫ eqToHom x₇) = 𝟙 _ := by
  subst eb x₁ x₂ x₃ x₄ x₆ x₇
  simp

/-- The other triangle identity of a family of adjunctions, with the counit taken at an index
equal to that of the unit. -/
theorem triangle_right_of_eq {Xa : Type w} {A : Xa → Type u₁} [∀ a, Category.{v₁} (A a)]
    {C : Type u₂} [Category.{v₂} C] {Pr : Xa → Prop}
    (E : ∀ a, Pr a → A a ⥤ C) (F : ∀ a, Pr a → C ⥤ A a) (adj : ∀ a h, E a h ⊣ F a h)
    {a a' : Xa} (ea : a' = a) (h : Pr a) (h' : Pr a')
    {Y V : A a} {Y₁ : A a'} {U W W₂ Y₂ : C} (x₁ : (F a h).obj W₂ = Y) (x₂ : (E a h).obj Y = U)
    (x₃ : (F a h).obj U = V) (x₄ : V = (F a h).obj W) (x₅ : W = (E a' h').obj Y₁)
    (x₆ : Y₁ = (F a' h').obj Y₂) (x₇ : Y₂ = W₂) :
    (eqToHom x₁ ≫ ((adj a h).unit.app Y ≫ (F a h).map (eqToHom x₂)) ≫ eqToHom x₃) ≫
      eqToHom x₄ ≫ (F a h).map (eqToHom x₅ ≫ ((E a' h').map (eqToHom x₆) ≫
        (adj a' h').counit.app Y₂) ≫ eqToHom x₇) = 𝟙 _ := by
  subst ea x₁ x₂ x₇ x₆ x₅ x₄
  simp

end Triangle

variable {I X : Type u}

namespace SPath

/-- The summands through which a path runs, letter by letter. -/
def sides : {w : List (Col I X)} → {s t : Sector I} → SPath w s t → List Bool
  | _, _, _, .nil _ => []
  | _, _, _, .cons _ side _ _ p => side :: sides p

theorem sides_append {l m : List (Col I X)} {s t r : Sector I} (p : SPath l s t)
    (q : SPath m t r) : (p.append q).sides = p.sides ++ q.sides := by
  induction p with
  | nil s => rfl
  | cons c side s hv p ih => simp [append, sides, ih]

theorem sides_cast {w w' : List (Col I X)} {s t : Sector I} (h : w = w') (p : SPath w s t) :
    (p.cast h).sides = p.sides := by
  subst h; rfl

/-- A path is determined by its summands. -/
theorem eq_of_sides : {w : List (Col I X)} → {s t : Sector I} → (p q : SPath w s t) →
    p.sides = q.sides → p = q
  | _, _, _, .nil _, .nil _, _ => rfl
  | _, _, _, .cons _ a _ ha p, .cons _ b _ hb q, h => by
    simp only [sides, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rw [eq_of_sides p q h]

/-- The path of a two-letter word through given summands. -/
def two {c₁ c₂ : Col I X} {t t' : Sector I} (τ₁ τ₂ : Bool) (hw₁ : StepValid c₁.l τ₁ t)
    (hw₂ : StepValid c₂.l τ₂ (nextSector c₁.l τ₁ t))
    (e : nextSector c₂.l τ₂ (nextSector c₁.l τ₁ t) = t') : SPath [c₁, c₂] t t' :=
  .cons c₁ τ₁ t hw₁ (.cons c₂ τ₂ _ hw₂ (e ▸ .nil _))

theorem sides_two {c₁ c₂ : Col I X} {t t' : Sector I} (τ₁ τ₂ : Bool)
    (hw₁ : StepValid c₁.l τ₁ t) (hw₂ : StepValid c₂.l τ₂ (nextSector c₁.l τ₁ t))
    (e : nextSector c₂.l τ₂ (nextSector c₁.l τ₁ t) = t') :
    (two τ₁ τ₂ hw₁ hw₂ e).sides = [τ₁, τ₂] := by
  subst e; rfl

/-- Every path of a two-letter word runs through two summands. -/
theorem exists_eq_two {c₁ c₂ : Col I X} {t t' : Sector I} (p : SPath [c₁, c₂] t t') :
    ∃ τ₁ τ₂ hw₁ hw₂ e, p = two (c₁ := c₁) (c₂ := c₂) τ₁ τ₂ hw₁ hw₂ e := by
  cases p with
  | cons _ τ₁ _ hw₁ p =>
    cases p with
    | cons _ τ₂ _ hw₂ p =>
      cases p
      exact ⟨τ₁, τ₂, hw₁, hw₂, rfl, rfl⟩

/-- A closed path of a lowering and a raising strand of the same colour stays in one
summand. -/
theorem side_eq_of_closed {a b : Bool} {i : I} {x y : X} {t : Sector I}
    (p : SPath [(⟨(a, i), x⟩ : Col I X), ⟨(b, i), y⟩] t t) (hab : a ≠ b) :
    ∃ σ, p.sides = [σ, σ] := by
  obtain ⟨τ₁, τ₂, hw₁, hw₂, e, rfl⟩ := exists_eq_two p
  refine ⟨τ₁, ?_⟩
  rw [sides_two]
  congr 1
  cases a <;> cases b <;> simp at hab <;> cases τ₁ <;> cases τ₂ <;> try rfl
  all_goals
    exfalso
    simp only [nextSector] at e
    have h1 := congrArg (fun p => p.1 i) e
    have h2 := congrArg (fun p => p.2 i) e
    simp only [StepValid] at hw₁ hw₂
    simp only [Finsupp.add_apply, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
      at h1 h2 hw₁ hw₂
    omega

end SPath

variable [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-- The entry of a two-letter matrix from the empty word at the path through given
summands. -/
theorem zeroTwo_two (d₁ d₂ : Col I X)
    (f : ∀ (t : Sector I) (τ₁ τ₂ : Bool) (hw₁ : StepValid d₁.l τ₁ t)
      (hw₂ : StepValid d₂.l τ₂ (nextSector d₁.l τ₁ t))
      (hs : t = nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t))
      (Z : P.H (nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t))),
      (hs ▸ Z : P.H t) ⟶ (P.step d₁.l τ₁ t hw₁).obj ((P.step d₂.l τ₂ _ hw₂).obj Z))
    {t t' : Sector I} (τ₁ τ₂ : Bool) (hw₁ : StepValid d₁.l τ₁ t)
    (hw₂ : StepValid d₂.l τ₂ (nextSector d₁.l τ₁ t))
    (e : nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t) = t') (hs : t = t') (Z : P.H t')
    (Z' : P.H (nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t))) (hZ : HEq Z' Z) :
    P.zeroTwo d₁ d₂ f (.nil t) (SPath.two τ₁ τ₂ hw₁ hw₂ e) hs Z =
      eqToHom (by subst e; obtain rfl := eq_of_heq hZ; rfl) ≫
        f t τ₁ τ₂ hw₁ hw₂ (hs.trans e.symm) Z' ≫
        eqToHom (by subst e; obtain rfl := eq_of_heq hZ; rfl) := by
  subst e; obtain rfl := eq_of_heq hZ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- The entry of a two-letter matrix to the empty word at the path through given
summands. -/
theorem twoZero_two (c₁ c₂ : Col I X)
    (f : ∀ (t : Sector I) (σ₁ σ₂ : Bool) (hv₁ : StepValid c₁.l σ₁ t)
      (hv₂ : StepValid c₂.l σ₂ (nextSector c₁.l σ₁ t))
      (hs : t = nextSector c₂.l σ₂ (nextSector c₁.l σ₁ t))
      (Z : P.H (nextSector c₂.l σ₂ (nextSector c₁.l σ₁ t))),
      (P.step c₁.l σ₁ t hv₁).obj ((P.step c₂.l σ₂ _ hv₂).obj Z) ⟶ (hs ▸ Z : P.H t))
    {t t' : Sector I} (σ₁ σ₂ : Bool) (hv₁ : StepValid c₁.l σ₁ t)
    (hv₂ : StepValid c₂.l σ₂ (nextSector c₁.l σ₁ t))
    (e : nextSector c₂.l σ₂ (nextSector c₁.l σ₁ t) = t') (hs : t = t') (Z : P.H t')
    (Z' : P.H (nextSector c₂.l σ₂ (nextSector c₁.l σ₁ t))) (hZ : HEq Z' Z) :
    P.twoZero c₁ c₂ f (SPath.two σ₁ σ₂ hv₁ hv₂ e) (.nil t) hs Z =
      eqToHom (by subst e; obtain rfl := eq_of_heq hZ; rfl) ≫
        f t σ₁ σ₂ hv₁ hv₂ (hs.trans e.symm) Z' ≫
        eqToHom (by subst e; obtain rfl := eq_of_heq hZ; rfl) := by
  subst e; obtain rfl := eq_of_heq hZ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

open Classical in
/-- The first zigzag identity for generators whose cup and cap are `cupImage` and
`capImage`. -/
theorem zigE_of (gens : P.Generators) (hcup : gens.cup = P.cupImage)
    (hcap : gens.cap = P.capImage) (i : I) (ν : X) {s t : Sector I}
    (q : SPath (wd D ν [up i]) s t) (Z : P.H t) :
    letI := Fintype.ofFinite (SPath (wd D ν (Shape.cup i).cod) t t)
    letI := Fintype.ofFinite (SPath (wd D (SKM.wt D ν [up i]) (Shape.cap i).dom) s s)
    ∑ m : SPath (wd D ν (Shape.cup i).cod) t t,
      ∑ r : SPath (wd D (SKM.wt D ν [up i]) (Shape.cap i).dom) s s,
        (if h : ((q.append m).append (.nil t)).cast (zigE_word D i ν) =
            ((SPath.nil s).append r).append q then
          (P.pathFunctor q).map (gens.cup i ν (.nil t) m Z) ≫
            eqToHom (P.obj_eq_of_cast_eq _ q m (.nil t) (.nil s) r q h Z) ≫
            gens.cap i (SKM.wt D ν [up i]) r (.nil s) ((P.pathFunctor q).obj Z)
        else 0) = 𝟙 _ := by
  classical
  cases q with
  | cons _ σ _ hv q =>
  cases q
  have hw₁ : StepValid (dn i) σ (nextSector (up i) σ s) := by
    cases σ <;> simp [StepValid, nextSector]
  have hw₂ : StepValid (up i) σ (nextSector (dn i) σ (nextSector (up i) σ s)) := by
    cases σ <;> simp [StepValid, nextSector]
  have e : nextSector (up i) σ (nextSector (dn i) σ (nextSector (up i) σ s)) =
      nextSector (up i) σ s := by
    cases σ <;> simp only [nextSector] <;> ext j <;> simp
  have e' : nextSector (dn i) σ (nextSector (up i) σ s) = s := by
    cases σ <;> simp only [nextSector] <;> ext j <;> simp
    simp only [Finsupp.single_apply]
    split_ifs with hj
    · subst hj; exact Nat.sub_add_cancel hv
    · simp
  let m₀ : SPath (wd D ν (Shape.cup i).cod) _ _ := SPath.two σ σ hw₁ hw₂ e
  let r₀ : SPath (wd D (SKM.wt D ν [up i]) (Shape.cap i).dom) s s :=
    SPath.two σ σ hv hw₁ e'
  have hm₀ : m₀.sides = [σ, σ] := SPath.sides_two _ _ _ _ _
  have hr₀ : r₀.sides = [σ, σ] := SPath.sides_two _ _ _ _ _
  have key : ∀ m r, ((SPath.append (.cons _ σ s hv (.nil _)) m).append (.nil _)).cast
      (zigE_word D i ν) = ((SPath.nil s).append r).append (.cons _ σ s hv (.nil _)) →
      m = m₀ ∧ r = r₀ := by
    intro m r h
    have h := congrArg SPath.sides h
    simp only [SPath.sides_cast, SPath.sides_append] at h
    obtain ⟨a, ha⟩ := SPath.side_eq_of_closed m (by simp)
    obtain ⟨b, hb⟩ := SPath.side_eq_of_closed r (by simp)
    rw [ha, hb] at h
    simp only [SPath.sides, List.cons_append, List.nil_append, List.append_nil,
      List.cons.injEq] at h
    obtain ⟨rfl, rfl, -, -⟩ := h
    exact ⟨SPath.eq_of_sides _ _ (ha.trans hm₀.symm), SPath.eq_of_sides _ _ (hb.trans hr₀.symm)⟩
  have hc : ((SPath.append (.cons _ σ s hv (.nil _)) m₀).append (.nil _)).cast
      (zigE_word D i ν) = ((SPath.nil s).append r₀).append (.cons _ σ s hv (.nil _)) := by
    apply SPath.eq_of_sides
    simp only [SPath.sides_cast, SPath.sides_append, hm₀, hr₀]
    rfl
  rw [Finset.sum_eq_single m₀ (fun m _ hm => Finset.sum_eq_zero fun r _ =>
      dite_eq_right fun h => hm (key m r h).1) (by simp),
    Finset.sum_eq_single r₀ (fun r _ hr => dite_eq_right fun h => hr (key m₀ r h).2) (by simp),
    dite_eq_left hc]
  simp only [hcup, hcap, cupImage, capImage]
  simp only [m₀, r₀]
  rw [zeroTwo_two (Z' := e.symm ▸ Z) (hZ := eqRec_heq _ _)]
  rw [twoZero_two (Z' := e'.symm ▸ (P.pathFunctor (.cons _ σ s hv (.nil _))).obj Z)
    (hZ := eqRec_heq _ _)]
  cases σ
  · simp only [cupEntry, capEntry, postCup, postCap]
    exact triangle_left_of_eq
      (C := fun b => homWeightSector P.T.obj P.W.obj (P.muP s) b)
      (Pr := fun b => P.muM (nextSector (up i) false s) + D.α i = b)
      (fun b h => homContentPostE P.T.obj P.W i s.1 (P.muP s) h)
      (fun b h => homContentPostF P.T.obj P.W i s.1 (P.muP s) h)
      (fun b h => homContentPostAdjunction P.T.obj P.W i s.1 (P.muP s) h)
      (congrArg P.muM e') _ _ _ _ _ _ _ _ _
  · simp only [cupEntry, capEntry, preCup, preCap]
    exact triangle_left_of_eq (C := fun b => homWeightSector P.T.obj P.W.obj b (P.muM s))
      (Pr := fun b => -b + D.α i = -P.muP (nextSector (up i) true s))
      (fun b h => homContentPreE P.T P.W.obj i (P.muM s) h)
      (fun b h => homContentPreF P.T P.W.obj i (P.muM s) h)
      (fun b h => homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i (P.muM s) h)
      (congrArg P.muP e') _ _ _ _ _ _ _ _ _

open Classical in
/-- The second zigzag identity for generators whose cup and cap are `cupImage` and
`capImage`. -/
theorem zigF_of (gens : P.Generators) (hcup : gens.cup = P.cupImage)
    (hcap : gens.cap = P.capImage) (i : I) (ν : X) {s t : Sector I}
    (q : SPath (wd D ν [dn i]) s t) (Z : P.H t) :
    letI := Fintype.ofFinite (SPath (wd D (SKM.wt D ν [dn i]) (Shape.cup i).cod) s s)
    letI := Fintype.ofFinite (SPath (wd D ν (Shape.cap i).dom) t t)
    ∑ m : SPath (wd D (SKM.wt D ν [dn i]) (Shape.cup i).cod) s s,
      ∑ r : SPath (wd D ν (Shape.cap i).dom) t t,
        (if h : (((SPath.nil s).append m).append q).cast (zigF_word D i ν) =
            (q.append r).append (.nil t) then
          gens.cup i (SKM.wt D ν [dn i]) (.nil s) m ((P.pathFunctor q).obj Z) ≫
            eqToHom (P.obj_eq_of_cast_eq _ (.nil s) m q q r (.nil t) h Z) ≫
            (P.pathFunctor q).map (gens.cap i ν r (.nil t) Z)
        else 0) = 𝟙 _ := by
  classical
  cases q with
  | cons _ σ _ hv q =>
  cases q
  have hw₂ : StepValid (up i) σ (nextSector (dn i) σ s) := by
    cases σ <;> simp [StepValid, nextSector]
  have hv' : StepValid (dn i) σ (nextSector (up i) σ (nextSector (dn i) σ s)) := by
    cases σ <;> simp [StepValid, nextSector]
  have e₁ : nextSector (up i) σ (nextSector (dn i) σ s) = s := by
    cases σ <;> simp only [nextSector] <;> ext j <;> simp
    simp only [Finsupp.single_apply]
    split_ifs with hj
    · subst hj; exact Nat.sub_add_cancel hv
    · simp
  have e₂ : nextSector (dn i) σ (nextSector (up i) σ (nextSector (dn i) σ s)) =
      nextSector (dn i) σ s := by
    cases σ <;> simp only [nextSector] <;> ext j <;> simp
  let m₀ : SPath (wd D (SKM.wt D ν [dn i]) (Shape.cup i).cod) s s := SPath.two σ σ hv hw₂ e₁
  let r₀ : SPath (wd D ν (Shape.cap i).dom) _ _ := SPath.two σ σ hw₂ hv' e₂
  have hm₀ : m₀.sides = [σ, σ] := SPath.sides_two _ _ _ _ _
  have hr₀ : r₀.sides = [σ, σ] := SPath.sides_two _ _ _ _ _
  have key : ∀ m r, (((SPath.nil s).append m).append (.cons _ σ s hv (.nil _))).cast
      (zigF_word D i ν) = (SPath.append (.cons _ σ s hv (.nil _)) r).append (.nil _) →
      m = m₀ ∧ r = r₀ := by
    intro m r h
    have h := congrArg SPath.sides h
    simp only [SPath.sides_cast, SPath.sides_append] at h
    obtain ⟨a, ha⟩ := SPath.side_eq_of_closed m (by simp)
    obtain ⟨b, hb⟩ := SPath.side_eq_of_closed r (by simp)
    rw [ha, hb] at h
    simp only [SPath.sides, List.cons_append, List.nil_append, List.append_nil,
      List.cons.injEq] at h
    obtain ⟨rfl, rfl, -, -⟩ := h
    exact ⟨SPath.eq_of_sides _ _ (ha.trans hm₀.symm), SPath.eq_of_sides _ _ (hb.trans hr₀.symm)⟩
  have hc : (((SPath.nil s).append m₀).append (.cons _ σ s hv (.nil _))).cast
      (zigF_word D i ν) = (SPath.append (.cons _ σ s hv (.nil _)) r₀).append (.nil _) := by
    apply SPath.eq_of_sides
    simp only [SPath.sides_cast, SPath.sides_append, hm₀, hr₀]
    rfl
  rw [Finset.sum_eq_single m₀ (fun m _ hm => Finset.sum_eq_zero fun r _ =>
      dite_eq_right fun h => hm (key m r h).1) (by simp),
    Finset.sum_eq_single r₀ (fun r _ hr => dite_eq_right fun h => hr (key m₀ r h).2) (by simp),
    dite_eq_left hc]
  simp only [hcup, hcap, cupImage, capImage]
  simp only [m₀, r₀]
  rw [zeroTwo_two (Z' := e₁.symm ▸ (P.pathFunctor (.cons _ σ s hv (.nil _))).obj Z)
    (hZ := eqRec_heq _ _)]
  rw [twoZero_two (Z' := e₂.symm ▸ Z) (hZ := eqRec_heq _ _)]
  cases σ
  · simp only [cupEntry, capEntry, postCup, postCap, pathFunctor_cons, pathFunctor_nil,
      Functor.id_comp]
    exact triangle_right_of_eq (A := fun a => homWeightSector P.T.obj P.W.obj (P.muP s) a)
      (C := homWeightSector P.T.obj P.W.obj (P.muP s) (P.muM (nextSector (dn i) false s)))
      (Pr := fun a => a + D.α i = P.muM (nextSector (dn i) false s))
      (fun a h => homContentPostE P.T.obj P.W i s.1 (P.muP s) h)
      (fun a h => homContentPostF P.T.obj P.W i s.1 (P.muP s) h)
      (fun a h => homContentPostAdjunction P.T.obj P.W i s.1 (P.muP s) h)
      (a := P.muM s)
      (a' := P.muM ((nextSector (dn i) false s).1, (nextSector (dn i) false s).2 - Finsupp.single i 1))
      (congrArg P.muM e₁ :) _ _ _ _ _ _ _ _ _
  · simp only [cupEntry, capEntry, preCup, preCap, pathFunctor_cons, pathFunctor_nil,
      Functor.id_comp]
    exact triangle_right_of_eq (A := fun a => homWeightSector P.T.obj P.W.obj a (P.muM s))
      (Pr := fun a => -P.muP (nextSector (dn i) true s) + D.α i = -a)
      (fun a h => homContentPreE P.T P.W.obj i (P.muM s) h)
      (fun a h => homContentPreF P.T P.W.obj i (P.muM s) h)
      (fun a h => homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i (P.muM s) h)
      (congrArg P.muP e₁) _ _ _ _ _ _ _ _ _

/-- Generators whose cup and cap are `cupImage` and `capImage` satisfy the zigzag identities. -/
theorem cupCapZigzag_of (gens : P.Generators) (hcup : gens.cup = P.cupImage)
    (hcap : gens.cap = P.capImage) : CupCapZigzag gens where
  zigE i ν _ _ q Z := P.zigE_of gens hcup hcap i ν q Z
  zigF i ν _ _ q Z := P.zigF_of gens hcup hcap i ν q Z

/-- The swapped generators satisfy the zigzag identities (1.10). -/
theorem cupCapZigzag_swappedGens (c : P.CrossCoeff) (L : P.LeftwardData) :
    CupCapZigzag (P.swappedGens c L) :=
  P.cupCapZigzag_of _ rfl rfl

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
