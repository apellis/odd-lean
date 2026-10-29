/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.CrossEntries
import OddMath.QuiverHecke.SwappedAssembly.Generators

/-! # The same-colour quadratic relation for the swapped crossing

The relation `τ² = 0` on `Eᵢ Eᵢ` of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, (1.7), for the image `crossImage` of the upward crossing in the swapped
action (`docs/Nondegeneracy/SwappedActionAssembly.md`, §3, row `quadEq`).

A path of `Eᵢ Eᵢ` is a choice of probe (`P`) or reservoir (`R`) summand for each letter; the
number of probe summands is determined by the endpoints, so the paths between two sectors are
`PP`, `RR`, or the mixed pair `PR`, `RP` (`sum_paths_PP`, `sum_paths_RR`,
`sum_paths_mixed`). On `PP` and `RR` the square is the factor relation `T.square`, resp.
`W.square` transported through the word comparison. On the mixed pair the four entries of the
square cancel for every coefficient `a` (the four cancellations of the matrix (A6)).

## Main results

* `ProbeReservoir.swappedGens_quadEq`: the entry `crossCross` of two swapped crossings on
  `Eᵢ Eᵢ` is zero.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct

universe u

variable {I X : Type u}

section Paths

variable (i : I) (r₁ r₂ : X) (s : Sector I) {M : Type*} [AddCommMonoid M]

/-- The only path `PP` of `Eᵢ Eᵢ` to its endpoint. -/
theorem sum_paths_PP
    {_ : Fintype (SPath [(⟨(true, i), r₁⟩ : Col I X), ⟨(true, i), r₂⟩] s
      (nextSector (true, i) true (nextSector (true, i) true s)))}
    (f : SPath [(⟨(true, i), r₁⟩ : Col I X), ⟨(true, i), r₂⟩] s
      (nextSector (true, i) true (nextSector (true, i) true s)) → M) :
    ∑ m, f m = f (.cons _ true s trivial (.cons _ true _ trivial (.nil _))) := by
  refine Fintype.sum_eq_single _ fun m hm => ?_
  obtain ⟨ρ₁, ρ₂, hv₁, hv₂, e, rfl⟩ := SPath.exists_eq_mk₂ m
  exfalso
  have he := congrArg (fun x : Sector I => x.1 i) e
  simp only [nextSector_fst_same] at he
  cases ρ₁ <;> cases ρ₂ <;> simp at he <;> first | exact hm rfl | omega

/-- The only path `RR` of `Eᵢ Eᵢ` to its endpoint. -/
theorem sum_paths_RR (hv₁ : StepValid (true, i) false s)
    (hv₂ : StepValid (true, i) false (nextSector (true, i) false s))
    {_ : Fintype (SPath [(⟨(true, i), r₁⟩ : Col I X), ⟨(true, i), r₂⟩] s
      (nextSector (true, i) false (nextSector (true, i) false s)))}
    (f : SPath [(⟨(true, i), r₁⟩ : Col I X), ⟨(true, i), r₂⟩] s
      (nextSector (true, i) false (nextSector (true, i) false s)) → M) :
    ∑ m, f m = f (.cons _ false s hv₁ (.cons _ false _ hv₂ (.nil _))) := by
  refine Fintype.sum_eq_single _ fun m hm => ?_
  obtain ⟨ρ₁, ρ₂, hw₁, hw₂, e, rfl⟩ := SPath.exists_eq_mk₂ m
  exfalso
  have he := congrArg (fun x : Sector I => x.1 i) e
  simp only [nextSector_fst_same] at he
  cases ρ₁ <;> cases ρ₂ <;> simp at he <;> first | exact hm rfl | omega

/-- The two mixed paths `PR` and `RP` of `Eᵢ Eᵢ` to their common endpoint. -/
theorem sum_paths_mixed (h : 1 ≤ s.2 i)
    {_ : Fintype (SPath [(⟨(true, i), r₁⟩ : Col I X), ⟨(true, i), r₂⟩] s
      (nextSector (true, i) false (nextSector (true, i) true s)))}
    (f : SPath [(⟨(true, i), r₁⟩ : Col I X), ⟨(true, i), r₂⟩] s
      (nextSector (true, i) false (nextSector (true, i) true s)) → M) :
    ∑ m, f m = f (.cons _ true s trivial (.cons _ false _ h (.nil _))) +
      f (.cons _ false s h (.cons _ true _ trivial (.nil _))) := by
  refine Fintype.sum_eq_add _ _ (fun e => by cases e) fun m hm => ?_
  obtain ⟨ρ₁, ρ₂, hw₁, hw₂, e, rfl⟩ := SPath.exists_eq_mk₂ m
  exfalso
  have he := congrArg (fun x : Sector I => x.1 i) e
  simp only [nextSector_fst_same] at he
  cases ρ₁ <;> cases ρ₂ <;> simp at he <;> first | exact hm.1 rfl | exact hm.2 rfl

end Paths
variable [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}


namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

theorem crossImage_self (c : P.CrossCoeff Sc) (i : I) (ν : X) {t s : Sector I}
    (p q : SPath (wd D ν [up i, up i]) t s) (Z : P.H s) :
    P.crossImage c i i ν p q Z = P.twoTwo _ _ _ _ (P.crossSameEntry c i _ _ _ _) p q rfl Z := by
  rw [crossImage]
  split_ifs with h
  · rfl
  · exact absurd rfl h

theorem swappedGens_cross_self (c : P.CrossCoeff Sc) (L : P.LeftwardData) (i : I) (ν : X)
    {t s : Sector I} (p q : SPath (wd D ν [up i, up i]) t s) (Z : P.H s) :
    (P.swappedGens c L).cross i i ν p q Z =
      P.twoTwo _ _ _ _ (P.crossSameEntry c i _ _ _ _) p q rfl Z :=
  P.crossImage_self c i ν p q Z

/-- The square of the probe/probe entry vanishes. -/
theorem preCrossSame_sq (i : I) (t : Sector I)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) true t))) :
    P.preCrossSame i t Z ≫ P.preCrossSame i t Z = 0 := by
  simp only [preCrossSame, Linear.smul_comp, Linear.comp_smul, smul_smul, Category.assoc,
    Iso.hom_inv_id_assoc]
  have h : P.T.cross i i (P.muP_preE i t) (P.muP_preE i _) (P.muP_preE i t) (P.muP_preE i _) ▷ Z ≫
      P.T.cross i i (P.muP_preE i t) (P.muP_preE i _) (P.muP_preE i t) (P.muP_preE i _) ▷ Z
        = 0 := by
    rw [← TwoSupercategory.comp_whiskerRight (R := k), P.T.square]
    exact (homPost (k := k) Z).map_zero _ _
  rw [reassoc_of% h]
  simp

/-- The square of the reservoir/reservoir entry vanishes. -/
theorem postCrossSame_sq (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (hw : StepValid (true, i) false (nextSector (true, i) false t))
    (Z : P.H (nextSector (true, i) false (nextSector (true, i) false t))) :
    P.postCrossSame i t hv hw Z ≫ P.postCrossSame i t hv hw Z = 0 := by
  simp only [postCrossSame, homContentPostCrossingApp, Category.assoc, Iso.inv_hom_id_app_assoc]
  have hz : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), f ◁ (0 : g ⟶ g) = 0 := fun f g =>
    (homPre (k := k) f).map_zero g g
  slice_lhs 2 3 => rw [← TwoSupercategory.whiskerLeft_comp (R := k), P.W.square, hz]
  simp

/-- **`τ² = 0` on `Eᵢ Eᵢ`** for the swapped crossing. -/
theorem swappedGens_quadEq (c : P.CrossCoeff Sc) (L : P.LeftwardData) (i : I) (ν : X)
    {s t : Sector I} (p q : SPath (wd D ν [up i, up i]) s t) (Z : P.H t) :
    crossCross (P.swappedGens c L) i i ν p q Z = 0 := by
  obtain ⟨σ₁, σ₂, hv₁, hv₂, e₁, rfl⟩ := SPath.exists_eq_mk₂ p
  subst e₁
  obtain ⟨τ₁, τ₂, hw₁, hw₂, e₂, rfl⟩ := SPath.exists_eq_mk₂ q
  have he := congrArg (fun x : Sector I => x.1 i) e₂
  simp only [nextSector_fst_same] at he
  cases σ₁ <;> cases σ₂ <;> cases τ₁ <;> cases τ₂ <;> try (simp at he <;> omega)
  all_goals rw [crossCross]
  case false.false.false.false =>
    refine Eq.trans (sum_paths_RR i _ _ s hv₁ hv₂ _) ?_
    rw [swappedGens_cross_self, swappedGens_cross_self]
    exact P.postCrossSame_sq i s hv₁ hv₂ Z
  case false.true.false.true =>
    refine Eq.trans (sum_paths_mixed i _ _ s hv₁ _) ?_
    rw [swappedGens_cross_self, swappedGens_cross_self, swappedGens_cross_self,
      swappedGens_cross_self]
    show (-(c.a i s hv₁ Z ≫ c.a i s hv₁ Z ≫ (P.mixedJ i i s hv₁ Z).inv)) ≫
        (P.mixedJ i i s hv₁ Z).hom + c.a i s hv₁ Z ≫ c.a i s hv₁ Z = 0
    simp
  case false.true.true.false =>
    refine Eq.trans (sum_paths_mixed i _ _ s hv₁ _) ?_
    rw [swappedGens_cross_self, swappedGens_cross_self, swappedGens_cross_self,
      swappedGens_cross_self]
    show (-(c.a i s hv₁ Z ≫ c.a i s hv₁ Z ≫ (P.mixedJ i i s hv₁ Z).inv)) ≫
        (-((P.mixedJ i i s hv₁ Z).hom ≫ c.a i s hv₁ Z ≫ (P.mixedJ i i s hv₁ Z).inv)) +
        c.a i s hv₁ Z ≫ (-(c.a i s hv₁ Z ≫ c.a i s hv₁ Z ≫ (P.mixedJ i i s hv₁ Z).inv)) = 0
    simp
  case true.false.false.true =>
    refine Eq.trans (sum_paths_mixed i _ _ s hv₂ _) ?_
    rw [swappedGens_cross_self, swappedGens_cross_self, swappedGens_cross_self,
      swappedGens_cross_self]
    show (-((P.mixedJ i i s hv₂ Z).hom ≫ c.a i s hv₂ Z ≫ (P.mixedJ i i s hv₂ Z).inv)) ≫
        (P.mixedJ i i s hv₂ Z).hom + (P.mixedJ i i s hv₂ Z).hom ≫ c.a i s hv₂ Z = 0
    simp
  case true.false.true.false =>
    refine Eq.trans (sum_paths_mixed i _ _ s hv₂ _) ?_
    rw [swappedGens_cross_self, swappedGens_cross_self, swappedGens_cross_self,
      swappedGens_cross_self]
    show (-((P.mixedJ i i s hv₂ Z).hom ≫ c.a i s hv₂ Z ≫ (P.mixedJ i i s hv₂ Z).inv)) ≫
        (-((P.mixedJ i i s hv₂ Z).hom ≫ c.a i s hv₂ Z ≫ (P.mixedJ i i s hv₂ Z).inv)) +
        (P.mixedJ i i s hv₂ Z).hom ≫
          (-(c.a i s hv₂ Z ≫ c.a i s hv₂ Z ≫ (P.mixedJ i i s hv₂ Z).inv)) = 0
    simp
  case true.true.true.true =>
    refine Eq.trans (sum_paths_PP i _ _ s _) ?_
    rw [swappedGens_cross_self, swappedGens_cross_self]
    exact P.preCrossSame_sq i s Z

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
