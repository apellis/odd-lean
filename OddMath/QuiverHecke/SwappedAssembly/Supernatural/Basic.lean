/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.CupCapZigzag
import OddMath.QuiverHecke.SwappedAssembly.Interchange
import OddMath.QuiverHecke.SwappedAssembly.WhiskerReduction

/-! # Supernaturality of the swapped dot, cup and cap

The super interchange law of the swapped layer representation (`interchangeLaw` in
`OddMath/QuiverHecke/SwappedAssembly/Interchange.lean`) follows from `GeneratorsSupernatural`:
every matrix entry of a generator image is a homogeneous supernatural transformation, of the
parity of the generator, between the functors of its two summand paths
(`docs/Nondegeneracy/SwappedActionAssembly.md`, end of §3).

This file reduces that statement, for the matrices built by `oneLetterDiag`, `zeroTwo` and
`twoZero`, to the supernaturality of their components at sectors in general position
(`oneLetterDiag_supernatural`, `zeroTwo_supernatural`, `twoZero_supernatural`). The paths of a
generator end at a common sector, while the components are written at the sectors reached
letter by letter; the two are compared by transport of Hom-sector objects along an equality
of sectors (`castH`). It then proves the supernaturality of the images of the upward dot
(parity `pᵢ`), the rightward cup and the rightward cap (parity `0`): the dot is the inherited
dot on the probe summand and the content-shifted postcomposition dot on the reservoir summand,
and the cup and the cap are the units and counits of the content-shifted adjunctions.

Main declarations: `ProbeReservoir.castH`, `ProbeReservoir.dotImage_supernatural`,
`ProbeReservoir.cupImage_supernatural`, `ProbeReservoir.capImage_supernatural`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams Supercategory OddMath.SKM

universe u uB v w

section Generic

variable {R : Type*} [CommRing R]
  {C : Type*} [Category C] [Preadditive C] [Linear R C] [Supercategory R C]
  {D : Type*} [Category D] [Preadditive D] [Linear R D] [Supercategory R D]

/-- The zero family is supernatural of every parity. -/
theorem isSupernatural_zero (p : ZMod 2) {F G : C ⥤ D} :
    IsSupernatural R p (F := F) (G := G) fun _ => 0 where
  mem _ := Submodule.zero_mem _
  naturality _ := by simp

/-- The comparison maps of an equality of functors form an even supernatural
transformation. -/
theorem isSupernatural_eqToHom {F G : C ⥤ D} [G.Linear R] (h : F = G)
    (e : ∀ X, F.obj X = G.obj X) : IsSupernatural R 0 fun X => eqToHom (e X) := by
  subst h
  simpa using isSupernatural_id (R := R) (F := F)

/-- Supernaturality is transported along equalities of the source and target functors. -/
theorem IsSupernatural.of_eq_conj {p : ZMod 2} {F F' G G' : C ⥤ D} (hF : F = F')
    (hG : G = G') {x : ∀ X, F'.obj X ⟶ G'.obj X} (hx : IsSupernatural R p x)
    (y : ∀ X, F.obj X ⟶ G.obj X) (e₁ : ∀ X, F.obj X = F'.obj X)
    (e₂ : ∀ X, G'.obj X = G.obj X) (hy : ∀ X, y X = eqToHom (e₁ X) ≫ x X ≫ eqToHom (e₂ X)) :
    IsSupernatural R p y := by
  subst hF hG
  have : y = x := funext fun X => by simpa using hy X
  subst this
  exact hx

end Generic

variable {I X : Type u}

namespace SPath

/-- The path of a one-letter word through a given summand. -/
def one {c : Col I X} {t t' : Sector I} (σ : Bool) (hv : StepValid c.l σ t)
    (e : nextSector c.l σ t = t') : SPath [c] t t' :=
  .cons c σ t hv (e ▸ .nil _)

/-- Every path of a one-letter word runs through one summand. -/
theorem exists_eq_one {c : Col I X} {t t' : Sector I} (p : SPath [c] t t') :
    ∃ σ hv e, p = one (c := c) σ hv e := by
  cases p with
  | cons _ σ _ hv p =>
    cases p
    exact ⟨σ, hv, rfl, rfl⟩

/-- Every path of the empty word is the transport of the trivial path. -/
theorem exists_eq_nil {t t' : Sector I} (p : SPath ([] : List (Col I X)) t t') :
    ∃ e : t = t', p = e ▸ .nil t := by
  cases p
  exact ⟨rfl, rfl⟩

end SPath

variable [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-! ## Transport along an equality of sectors -/

/-- Transport of Hom-sector objects along an equality of sectors. -/
def castH {a b : Sector I} (h : a = b) : P.H b ⥤ P.H a where
  obj Z := (h ▸ Z : P.H a)
  map {Z Z'} f := by subst h; exact f
  map_id := by subst h; intro; rfl
  map_comp := by subst h; intros; rfl

omit [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
theorem castH_rfl (a : Sector I) : P.castH (rfl : a = a) = 𝟭 _ := rfl

instance castH_additive {a b : Sector I} (h : a = b) : (P.castH h).Additive := by
  subst h; rw [castH_rfl]; infer_instance

instance castH_linear {a b : Sector I} (h : a = b) : (P.castH h).Linear k := by
  subst h; rw [castH_rfl]; infer_instance

instance castH_isSuperfunctor {a b : Sector I} (h : a = b) :
    IsSuperfunctor k (P.castH h) := by
  subst h; exact ⟨fun hf => hf⟩

omit [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
theorem castH_obj_heq {a b : Sector I} (h : a = b) (Z : P.H b) : HEq ((P.castH h).obj Z) Z := by
  subst h; rfl

omit [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
theorem castH_comp_castH {a b : Sector I} (h : a = b) (h' : b = a) :
    P.castH h' ⋙ P.castH h = 𝟭 _ := by
  subst h; rfl

theorem pathFunctor_one {c : Col I X} {t t' : Sector I} (σ : Bool) (hv : StepValid c.l σ t)
    (e : nextSector c.l σ t = t') :
    P.pathFunctor (SPath.one σ hv e) = P.castH e ⋙ P.step c.l σ t hv := by
  subst e; rfl

theorem pathFunctor_two {c₁ c₂ : Col I X} {t t' : Sector I} (τ₁ τ₂ : Bool)
    (hw₁ : StepValid c₁.l τ₁ t) (hw₂ : StepValid c₂.l τ₂ (nextSector c₁.l τ₁ t))
    (e : nextSector c₂.l τ₂ (nextSector c₁.l τ₁ t) = t') :
    P.pathFunctor (SPath.two τ₁ τ₂ hw₁ hw₂ e) =
      (P.castH e ⋙ P.step c₂.l τ₂ _ hw₂) ⋙ P.step c₁.l τ₁ t hw₁ := by
  subst e; rfl

/-- The Hom-sector functor of one strand is a superfunctor. -/
instance step_isSuperfunctor (l : Letter I) (side : Bool) (s : Sector I)
    (hv : StepValid l side s) : IsSuperfunctor k (P.step l side s hv) := by
  obtain ⟨_ | _, i⟩ := l <;> cases side <;>
    (dsimp only [step, homContentPreE, homContentPreF, homContentPostE, homContentPostF];
      infer_instance)

/-! ## One-letter diagonal matrices -/

theorem oneLetterDiag_one_of_ne (l : Letter I) (r : X)
    (f : ∀ (side : Bool) (t : Sector I) (hv : StepValid l side t)
      (Z : P.H (nextSector l side t)), End ((P.step l side t hv).obj Z))
    {t s s' : Sector I} (σ τ : Bool) (hv : StepValid l σ t) (hw : StepValid l τ t)
    (e : nextSector l σ t = s) (e' : nextSector l τ t = s') (hs : s = s') (Z : P.H s')
    (hne : σ ≠ τ) :
    P.oneLetterDiag l r f (SPath.one (c := ⟨l, r⟩) σ hv e) (SPath.one (c := ⟨l, r⟩) τ hw e')
      hs Z = 0 := by
  subst e e'
  exact dite_eq_right_of_eq_false (eq_false hne)

/-- **Supernaturality of a one-letter diagonal matrix** from that of its components. -/
theorem oneLetterDiag_supernatural (l : Letter I) (r : X) (p : ZMod 2)
    (f : ∀ (side : Bool) (t : Sector I) (hv : StepValid l side t)
      (Z : P.H (nextSector l side t)), End ((P.step l side t hv).obj Z))
    (hf : ∀ side t hv, IsSupernatural k p (F := P.step l side t hv)
      (G := P.step l side t hv) (f side t hv))
    {t s : Sector I} (q q' : SPath [⟨l, r⟩] t s) :
    IsSupernatural k p (fun Z => P.oneLetterDiag l r f q q' rfl Z) := by
  obtain ⟨σ, hv, e, rfl⟩ := q.exists_eq_one
  subst e
  obtain ⟨τ, hw, e', rfl⟩ := q'.exists_eq_one
  by_cases h : σ = τ
  · subst h
    refine IsSupernatural.of_eq_conj (P.pathFunctor_one σ hv rfl)
      (P.pathFunctor_one σ hw e') (hf σ t hv) _ (fun _ => rfl) (fun _ => rfl) fun Z => ?_
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact P.oneLetterDiag_self l r f σ t hv hw Z
  · simp only [P.oneLetterDiag_one_of_ne l r f σ τ hv hw rfl e' rfl _ h]
    exact isSupernatural_zero p

/-! ## Two-letter matrices from and to the empty word -/

/-- **Supernaturality of a matrix from the empty word to a two-letter word** from that of its
components. -/
theorem zeroTwo_supernatural (d₁ d₂ : Col I X) (p : ZMod 2)
    (f : ∀ (t : Sector I) (τ₁ τ₂ : Bool) (hw₁ : StepValid d₁.l τ₁ t)
      (hw₂ : StepValid d₂.l τ₂ (nextSector d₁.l τ₁ t))
      (hs : t = nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t))
      (Z : P.H (nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t))),
      (hs ▸ Z : P.H t) ⟶ (P.step d₁.l τ₁ t hw₁).obj ((P.step d₂.l τ₂ _ hw₂).obj Z))
    (hf : ∀ t τ₁ τ₂ hw₁ hw₂ hs, IsSupernatural k p (F := P.castH hs)
      (G := P.step d₂.l τ₂ _ hw₂ ⋙ P.step d₁.l τ₁ t hw₁) (f t τ₁ τ₂ hw₁ hw₂ hs))
    {t s : Sector I} (q : SPath [] t s) (q' : SPath [d₁, d₂] t s) :
    IsSupernatural k p (fun Z => P.zeroTwo d₁ d₂ f q q' rfl Z) := by
  cases q
  obtain ⟨τ₁, τ₂, hw₁, hw₂, e, rfl⟩ := SPath.exists_eq_two q'
  have hx := (hf t τ₁ τ₂ hw₁ hw₂ e.symm).whiskerLeft (P.castH e)
  refine IsSupernatural.of_eq_conj (P.castH_comp_castH e.symm e).symm
    (P.pathFunctor_two τ₁ τ₂ hw₁ hw₂ e) hx _ (fun Z => ?_)
    (fun _ => by rw [P.pathFunctor_two]) fun Z => ?_
  · exact (eq_of_heq ((P.castH_obj_heq e.symm _).trans (P.castH_obj_heq e _))).symm
  · rw [P.zeroTwo_two d₁ d₂ f τ₁ τ₂ hw₁ hw₂ e rfl Z ((P.castH e).obj Z) (P.castH_obj_heq e Z)]

/-- **Supernaturality of a matrix from a two-letter word to the empty word** from that of its
components. -/
theorem twoZero_supernatural (c₁ c₂ : Col I X) (p : ZMod 2)
    (f : ∀ (t : Sector I) (σ₁ σ₂ : Bool) (hv₁ : StepValid c₁.l σ₁ t)
      (hv₂ : StepValid c₂.l σ₂ (nextSector c₁.l σ₁ t))
      (hs : t = nextSector c₂.l σ₂ (nextSector c₁.l σ₁ t))
      (Z : P.H (nextSector c₂.l σ₂ (nextSector c₁.l σ₁ t))),
      (P.step c₁.l σ₁ t hv₁).obj ((P.step c₂.l σ₂ _ hv₂).obj Z) ⟶ (hs ▸ Z : P.H t))
    (hf : ∀ t σ₁ σ₂ hv₁ hv₂ hs, IsSupernatural k p
      (F := P.step c₂.l σ₂ _ hv₂ ⋙ P.step c₁.l σ₁ t hv₁) (G := P.castH hs)
      (f t σ₁ σ₂ hv₁ hv₂ hs))
    {t s : Sector I} (q : SPath [c₁, c₂] t s) (q' : SPath [] t s) :
    IsSupernatural k p (fun Z => P.twoZero c₁ c₂ f q q' rfl Z) := by
  cases q'
  obtain ⟨σ₁, σ₂, hv₁, hv₂, e, rfl⟩ := SPath.exists_eq_two q
  have hx := (hf t σ₁ σ₂ hv₁ hv₂ e.symm).whiskerLeft (P.castH e)
  refine IsSupernatural.of_eq_conj (P.pathFunctor_two σ₁ σ₂ hv₁ hv₂ e)
    (P.castH_comp_castH e.symm e).symm hx _ (fun _ => by rw [P.pathFunctor_two])
    (fun Z => ?_) fun Z => ?_
  · exact eq_of_heq ((P.castH_obj_heq e.symm _).trans (P.castH_obj_heq e _))
  · rw [P.twoZero_two c₁ c₂ f σ₁ σ₂ hv₁ hv₂ e rfl Z ((P.castH e).obj Z) (P.castH_obj_heq e Z)]

/-! ## The dot -/

/-- The diagonal components of the dot are supernatural of the parity of its colour. -/
theorem dotDiag_supernatural (i : I) (side : Bool) (t : Sector I)
    (hv : StepValid (true, i) side t) :
    IsSupernatural k (D.parity i) (F := P.step (true, i) side t hv)
      (G := P.step (true, i) side t hv) (P.dotDiag i side t hv) := by
  cases side
  · have hx := homContentPostDot_power_supernatural (k := k) P.T.obj P.W i t.1 (P.muP t)
      (P.muM_postE i hv) 1
    simp only [Nat.cast_one, one_mul, pow_one] at hx
    exact hx
  · have h : -P.muP t + D.α i = -P.muP (t.1 + Finsupp.single i 1, t.2) := by
      simp only [muP, contentWeight_add_single]; abel
    have hx := (homPreTransform (k := k) (c := P.W.obj (P.muM t)) (P.T.dot i h)
      (P.T.dot_mem i h)).isSupernatural (D.parity i)
    refine IsSupernatural.of_eq_conj (F := P.step (true, i) true t hv)
      (G := P.step (true, i) true t hv) rfl rfl hx _ (fun _ => rfl) (fun _ => rfl) fun Z => ?_
    simp [homPreTransform, dotDiag]

/-- **The image of the upward dot is supernatural.** -/
theorem dotImage_supernatural (i : I) (ν : X) {t s : Sector I}
    (q q' : SPath [⟨(true, i), ν⟩] t s) :
    IsSupernatural k (D.parity i) (fun Z => P.dotImage i ν q q' Z) :=
  P.oneLetterDiag_supernatural _ _ _ _ (P.dotDiag_supernatural i) q q'

/-! ## Functors of a strand transported along an equality of sectors -/

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
theorem preE_functor_heq (i : I) {s s' : Sector I} (hs : s = s') {x : X}
    (h : -x + D.α i = -P.muP s) (h' : -x + D.α i = -P.muP s') :
    HEq (P.castH hs ⋙ homContentPreE P.T P.W.obj i (P.muM s) h)
      (homContentPreE P.T P.W.obj i (P.muM s') h') := by
  subst hs; rfl

theorem preF_functor_heq (i : I) {s s' : Sector I} (hs : s = s') {x : X}
    (h : -P.muP s + D.α i = -x) (h' : -P.muP s' + D.α i = -x) :
    HEq (P.castH hs ⋙ homContentPreF P.T P.W.obj i (P.muM s) h)
      (homContentPreF P.T P.W.obj i (P.muM s') h') := by
  subst hs; rfl

theorem postE_functor_heq (i : I) (β : I →₀ ℕ) {s s' : Sector I} (hs : s = s') {x : X}
    (h : P.muM s + D.α i = x) (h' : P.muM s' + D.α i = x) :
    HEq (P.castH hs ⋙ homContentPostE P.T.obj P.W i β (P.muP s) h)
      (homContentPostE P.T.obj P.W i β (P.muP s') h') := by
  subst hs; rfl

theorem postF_functor_heq (i : I) (β : I →₀ ℕ) {s s' : Sector I} (hs : s = s') {x : X}
    (h : x + D.α i = P.muM s) (h' : x + D.α i = P.muM s') :
    HEq (P.castH hs ⋙ homContentPostF P.T.obj P.W i β (P.muP s) h)
      (homContentPostF P.T.obj P.W i β (P.muP s') h') := by
  subst hs; rfl

/-! ## The cup and the cap -/

theorem preCup_supernatural (i : I) (t : Sector I) (hv : StepValid (false, i) true t)
    (hw : StepValid (true, i) true (nextSector (false, i) true t))
    (hs : t = nextSector (true, i) true (nextSector (false, i) true t)) :
    IsSupernatural k 0 (F := P.castH hs)
      (G := P.step (true, i) true _ hw ⋙ P.step (false, i) true t hv)
      (P.preCup i t hv hw hs) := by
  have := P.step_additive (false, i) true t hv
  have := P.step_linear (false, i) true t hv
  have := P.step_isSuperfunctor (false, i) true t hv
  have hu := (isSupernatural_of_natTrans (R := k) (P.preAdjAt i hv).unit
    (fun Z => homContentPreAdjunction_unit_mem ..)).whiskerLeft (P.castH hs)
  have hE := (isSupernatural_eqToHom (R := k)
    (eq_of_heq (P.preE_functor_heq i hs (P.muP_preF i hv) (P.muP_preE i _)))
    (fun Z => eq_of_heq (P.preE_obj_heq i hs _ _ Z))).whiskerRight
      (P.step (false, i) true t hv)
  have := hu.comp hE
  rw [add_zero] at this
  exact this

theorem postCup_supernatural (i : I) (t : Sector I) (hv : StepValid (false, i) false t)
    (hw : StepValid (true, i) false (nextSector (false, i) false t))
    (hs : t = nextSector (true, i) false (nextSector (false, i) false t)) :
    IsSupernatural k 0 (F := P.castH hs)
      (G := P.step (true, i) false _ hw ⋙ P.step (false, i) false t hv)
      (P.postCup i t hv hw hs) := by
  have := P.step_additive (false, i) false t hv
  have := P.step_linear (false, i) false t hv
  have := P.step_isSuperfunctor (false, i) false t hv
  have hu := (isSupernatural_of_natTrans (R := k)
    (homContentPostAdjunction P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).unit
    (fun Z => homContentPostAdjunction_unit_mem ..)).whiskerLeft (P.castH hs)
  have hE := (isSupernatural_eqToHom (R := k)
    (eq_of_heq (P.postE_functor_heq i t.1 hs (P.muM_postF i t) (P.muM_postE i hw)))
    (fun Z => eq_of_heq (P.postE_obj_heq i t.1 hs _ _ Z))).whiskerRight
      (P.step (false, i) false t hv)
  have := hu.comp hE
  rw [add_zero] at this
  exact this

theorem preCap_supernatural (i : I) (t : Sector I) (hv : StepValid (true, i) true t)
    (hw : StepValid (false, i) true (nextSector (true, i) true t))
    (hs : t = nextSector (false, i) true (nextSector (true, i) true t)) :
    IsSupernatural k 0 (F := P.step (false, i) true _ hw ⋙ P.step (true, i) true t hv)
      (G := P.castH hs) (P.preCap i t hv hw hs) := by
  have := P.step_additive (true, i) true t hv
  have := P.step_linear (true, i) true t hv
  have := P.step_isSuperfunctor (true, i) true t hv
  have hc := (isSupernatural_of_natTrans (R := k)
    (homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i (P.muM t) (P.muP_preE i t)).counit
    (fun Z => homContentPreAdjunction_counit_mem ..)).whiskerLeft (P.castH hs)
  have hE := (isSupernatural_eqToHom (R := k)
    (eq_of_heq (P.preF_functor_heq i hs (P.muP_preE i t) (P.muP_preF i hw))).symm
    (fun Z => eq_of_heq (P.preF_obj_heq i hs _ _ Z).symm)).whiskerRight
      (P.step (true, i) true t hv)
  have := hE.comp hc
  rw [add_zero] at this
  exact this

theorem postCap_supernatural (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (hw : StepValid (false, i) false (nextSector (true, i) false t))
    (hs : t = nextSector (false, i) false (nextSector (true, i) false t)) :
    IsSupernatural k 0 (F := P.step (false, i) false _ hw ⋙ P.step (true, i) false t hv)
      (G := P.castH hs) (P.postCap i t hv hw hs) := by
  have := P.step_additive (true, i) false t hv
  have := P.step_linear (true, i) false t hv
  have := P.step_isSuperfunctor (true, i) false t hv
  have hc := (isSupernatural_of_natTrans (R := k)
    (homContentPostAdjunction P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv)).counit
    (fun Z => homContentPostAdjunction_counit_mem ..)).whiskerLeft (P.castH hs)
  have hE := (isSupernatural_eqToHom (R := k)
    (eq_of_heq (P.postF_functor_heq i t.1 hs (P.muM_postE i hv) (P.muM_postF i _))).symm
    (fun Z => eq_of_heq (P.postF_obj_heq i t.1 hs _ _ Z).symm)).whiskerRight
      (P.step (true, i) false t hv)
  have := hE.comp hc
  rw [add_zero] at this
  exact this

/-- **The image of the rightward cup is supernatural** (of parity `0`). -/
theorem cupImage_supernatural (i : I) (ν : X) {t s : Sector I} (q : SPath [] t s)
    (q' : SPath (wd D ν (Shape.cup i).cod) t s) :
    IsSupernatural k 0 (fun Z => P.cupImage i ν q q' Z) := by
  refine P.zeroTwo_supernatural _ _ 0 _ (fun t τ₁ τ₂ hw₁ hw₂ hs => ?_) q q'
  cases τ₁ <;> cases τ₂
  · exact P.postCup_supernatural i t hw₁ hw₂ hs
  · exact isSupernatural_zero 0
  · exact isSupernatural_zero 0
  · exact P.preCup_supernatural i t hw₁ hw₂ hs

/-- **The image of the rightward cap is supernatural** (of parity `0`). -/
theorem capImage_supernatural (i : I) (ν : X) {t s : Sector I}
    (q : SPath (wd D ν (Shape.cap i).dom) t s) (q' : SPath [] t s) :
    IsSupernatural k 0 (fun Z => P.capImage i ν q q' Z) := by
  refine P.twoZero_supernatural _ _ 0 _ (fun t σ₁ σ₂ hv₁ hv₂ hs => ?_) q q'
  cases σ₁ <;> cases σ₂
  · exact P.postCap_supernatural i t hv₁ hv₂ hs
  · exact isSupernatural_zero 0
  · exact isSupernatural_zero 0
  · exact P.preCap_supernatural i t hv₁ hv₂ hs

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
