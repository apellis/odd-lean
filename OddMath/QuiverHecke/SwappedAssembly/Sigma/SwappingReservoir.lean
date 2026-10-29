/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SwappingMate
import OddMath.QuiverHecke.SwappedAssembly.Generators.CrossCoeffExistence
import OddMath.SKM.RouquierHomDistinctMixedPostDotsComp

/-! # The swapping block `W_B` of the same-colour sideways crossing is invertible

The entry `W_B` of `docs/Nondegeneracy/AugmentedSectorBlocks.md` §2 of the sideways crossing
`σ = sigmaL i i : Eᵢ Fᵢ → Fᵢ Eᵢ` of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Definition 1.5, (1.11), between the summand paths `[P, R]` and `[R, P]`,
is the mate under the reservoir adjunction of the crossing entry `-(a ; a ; J⁻¹)`: reservoir
unit, crossing, reservoir counit. Up to the transport of objects along equalities of weights,
this is the dotted post-side mate `homDistinctMixedMateDot` of `J (-(a²)) J⁻¹`. Its
invertibility uses only the defining inverse identities of the coefficient `a`
(`CrossCoeff.IsInverse`), invertibility of the probe dots and nilpotence of the reservoir dots;
no relation for bubbles is used.

## Main results

* `OddMath.SKM.isIso_homContentDistinctMixedPostMate_of_eq`: the dotted post-side mate for the
  content-shifted postcomposition adjunctions is invertible when it is pointwise, with the
  objects matched along equalities of weights.
* `ProbeReservoir.isIso_sigmaEntry_reservoir`: the entry `W_B` of `sigmaL i i`, from `(P,R)` to
  `(R,P)`, is an isomorphism.
* `ProbeReservoir.swappingReservoirInvertible`, `ProbeReservoir.swappingInvertible_of_factor`:
  all swapping entries are invertible.
* `ProbeReservoir.augmentedInvertible_of_central`: the augmented blocks are invertible once the
  central entries are.
-/

noncomputable section

namespace OddMath.SKM
open CategoryTheory StringDiagrams
universe r' u' v' w'
section PostMate
variable {k : Type r'} [CommRing k] {B : Type u'} [BicategoryStruct.{w',v'} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T W : RouquierFamily (k := k) (B := B) D) (i : I)

/-- The dotted post-side mate of a family of crossings `C` is invertible when it is invertible
for each object `H`, with the unit taken at a weight `b` equal to the weight `b'` of the
counit and the objects matched along this equality. -/
theorem isIso_homContentDistinctMixedPostMate_of_eq {nuP muP b b' nuM : X} (eb : b = b')
    (hE : -nuP + D.α i = -muP) (h : b + D.α i = nuM) (h' : b' + D.α i = nuM)
    (βc βu : I →₀ ℕ)
    (C : ∀ W₀ : homWeightSector T.obj W.obj muP b,
      (homContentPostE T.obj W i βu nuP h).obj ((homContentPreE T W.obj i b hE).obj W₀) ⟶
        (homContentPreE T W.obj i nuM hE).obj ((homContentPostE T.obj W i βc muP h).obj W₀))
    (hC : ∀ H : homWeightSector T.obj W.obj muP nuM,
      IsIso (homDistinctMixedMateDot (T.E i hE) (W.adj i h) (homContentShift D i βc)
        (homContentShift D i βu) H
        ((homMixedInterchange (k := k) (T.E i hE) (W.E i h) (homContentShift D i βc)
          (homContentShift D i βu) ((homContentPostF T.obj W i βc muP h).obj H)).hom ≫
            C ((homContentPostF T.obj W i βc muP h).obj H))))
    {A0 A1 Y A5 A16 : homWeightSector T.obj W.obj nuP b'}
    {U : homWeightSector T.obj W.obj nuP nuM}
    {W₀ V₁ : homWeightSector T.obj W.obj muP b} {V Y₂ V' : homWeightSector T.obj W.obj muP nuM}
    (x₁ : A0 = A1) (x₂ : A1 = Y)
    (x₃ : (homContentPostE T.obj W i βu nuP h').obj Y = U)
    (x₄ : (homContentPostF T.obj W i βu nuP h').obj U = A5)
    (x₅ : A5 = (homContentPostF T.obj W i βu nuP h').obj
      ((homContentPostE T.obj W i βu nuP h).obj ((homContentPreE T W.obj i b hE).obj W₀)))
    (x₆ : (homContentPostF T.obj W i βu nuP h').obj
      ((homContentPreE T W.obj i nuM hE).obj ((homContentPostE T.obj W i βc muP h).obj W₀)) =
      (homContentPostF T.obj W i βu nuP h').obj ((homContentPreE T W.obj i nuM hE).obj V))
    (x₇ : V = (homContentPostE T.obj W i βc muP h).obj V₁)
    (x₈ : V₁ = (homContentPostF T.obj W i βc muP h).obj Y₂) (x₉ : Y₂ = V')
    (x₁₀ : (homContentPostF T.obj W i βu nuP h').obj
      ((homContentPreE T W.obj i nuM hE).obj V') = A16)
    (xY : HEq Y ((homContentPreE T W.obj i b hE).obj W₀)) (xZ : W₀ = V₁) :
    IsIso (eqToHom x₁ ≫ eqToHom x₂ ≫
      (homContentPostAdjunction T.obj W i βu nuP h').unit.app Y ≫
      (homContentPostF T.obj W i βu nuP h').map (eqToHom x₃) ≫ eqToHom x₄ ≫ eqToHom x₅ ≫
      (homContentPostF T.obj W i βu nuP h').map (C W₀) ≫ eqToHom x₆ ≫
      (homContentPostF T.obj W i βu nuP h').map ((homContentPreE T W.obj i nuM hE).map
        (eqToHom x₇ ≫ (homContentPostE T.obj W i βc muP h).map (eqToHom x₈) ≫
          (homContentPostAdjunction T.obj W i βc muP h).counit.app Y₂ ≫ eqToHom x₉)) ≫
      eqToHom x₁₀) := by
  subst eb
  obtain rfl : h' = h := rfl
  obtain rfl := eq_of_heq xY
  subst x₁ x₂ x₃ x₄ x₁₀ x₉ x₈ xZ x₇
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.map_id]
  have hI := hC Y₂
  unfold homDistinctMixedMateDot at hI
  simp only [Category.assoc] at hI
  erw [Iso.inv_hom_id_assoc] at hI
  erw [Category.id_comp]
  rw [← Functor.map_comp]
  exact hI

end PostMate
end OddMath.SKM

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
variable {P : ProbeReservoir k B D Sc}


attribute [local irreducible] Finsupp.zipWith contentWeight

/-- A reservoir `Fᵢ` followed by a reservoir `Eᵢ` returns to the sector. -/
theorem nextSector_upR_dnR {i : I} (t : Sector I) :
    nextSector (true, i) false (nextSector (false, i) false t) = t := by
  obtain ⟨a, b⟩ := t
  simp only [nextSector, Prod.mk.injEq, true_and]
  exact add_tsub_cancel_right b _

/-- A reservoir `Eᵢ` followed by a reservoir `Fᵢ` returns to the sector. -/
theorem nextSector_dnR_upR {i : I} {t : Sector I} (h : StepValid (true, i) false t) :
    nextSector (false, i) false (nextSector (true, i) false t) = t := by
  obtain ⟨a, b⟩ := t
  simp only [StepValid] at h
  simp only [nextSector, Prod.mk.injEq, true_and]
  exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 h)

/-- The swapping entry `W_B` of the same-colour sideways crossing, from the path `(P,R)` of
`Eᵢ Fᵢ` to the path `(R,P)` of `Fᵢ Eᵢ`, is invertible: it is the reservoir mate of the
crossing entry `-(a ; a ; J⁻¹)`, whose dotted mate is invertible by the inverse identities of
`a`, invertibility of the probe dot and nilpotence of the reservoir dot. -/
theorem isIso_sigmaEntry_reservoir (c : P.CrossCoeff) (hc : c.IsInverse)
    (hT : ∀ (i : I) {x y : X} (h : x + D.α i = y), IsUnit (show End (P.T.E i h) from P.T.dot i h))
    (hW : ∀ (i : I) {x y : X} (h : x + D.α i = y),
      IsNilpotent (show End (P.W.E i h) from P.W.dot i h)) (i : I) (ν : X) {t s : Sector I}
    (p : SPath (wd D ν [up i, dn i]) t s) (q : SPath (wd D ν [dn i, up i]) t s)
    (hp : p.sides = [true, false]) (hq : q.sides = [false, true]) (Z : P.H s) :
    IsIso (P.sigmaEntry c i i ν p q Z) := by
  obtain ⟨τ₁, τ₂, hv₁, hv₂, ep, rfl⟩ := SPath.exists_eq_two p
  obtain ⟨σ₁, σ₂, hw₁, hw₂, eq, rfl⟩ := SPath.exists_eq_two q
  rw [SPath.sides_two] at hp hq
  simp only [List.cons.injEq, and_true] at hp hq
  obtain ⟨rfl, rfl⟩ := hp
  obtain ⟨rfl, rfl⟩ := hq
  subst eq
  let t' := nextSector (false, i) false t
  have hR : StepValid (true, i) false t' := by simp [t', StepValid, nextSector]
  -- the cup (reservoir)
  let qg₁ : SPath ((SKM.sig D).cod (sigL₁ (D := D) i i ν).gen) t t :=
    SPath.two false false hw₁ hR (nextSector_upR_dnR t)
  let m₁ : SPath (sigL₁ (D := D) i i ν).cod.word t _ :=
    ((SPath.nil t).append qg₁).append (SPath.two true false hv₁ hv₂ ep)
  -- the crossing
  let x := nextSector (true, i) true (nextSector (true, i) false t')
  have hx : StepValid (false, i) false x := trivial
  have hR' : StepValid (true, i) false (nextSector (true, i) true t') := hR
  let pu₂ : SPath (sigL₂ (D := D) i i ν).left t t' := .cons _ false t hw₁ (.nil _)
  let pg₂ : SPath ((SKM.sig D).dom (sigL₂ (D := D) i i ν).gen) t' x :=
    .cons _ false t' hR (.cons _ true _ trivial (.nil _))
  let qg₂ : SPath ((SKM.sig D).cod (sigL₂ (D := D) i i ν).gen) t' x :=
    .cons _ true t' trivial (.cons _ false _ hR' (.nil _))
  let pv₂ : SPath (sigL₂ (D := D) i i ν).right x (nextSector (true, i) true t') :=
    .cons _ false x hx ((SPath.nil _).castTgt (nextSector_dnR_upR (i := i) hR'))
  let m₂ : SPath (sigL₂ (D := D) i i ν).cod.word t _ := (pu₂.append qg₂).append pv₂
  rw [sigmaEntry_eq_sigmaTerm (m₁ := m₁) (m₂ := m₂) (p₁ := true) (p₂ := false) (q₁ := false)
    (q₂ := true) (hp := rfl) (hq := rfl)
    (hm₁ := by simp [m₁, qg₁, SPath.sides_append, SPath.sides_two, SPath.sides])
    (hm₂ := by simp [m₂, pu₂, qg₂, pv₂, SPath.sides_append, SPath.sides])]
  have sd := @SPath.sides_cast.{u}
  -- the cap (reservoir)
  let s₀ := nextSector (true, i) true t'
  have hd : StepValid (false, i) false (nextSector (true, i) false s₀) := trivial
  let pu₃ : SPath (sigL₃ (D := D) i i ν).left t s₀ :=
    .cons _ false t hw₁ (.cons _ true _ hw₂ (.nil _))
  let pg₃ : SPath ((SKM.sig D).dom (sigL₃ (D := D) i i ν).gen) s₀ s₀ :=
    SPath.two false false hR' hd (nextSector_dnR_upR hR')
  rw [sigmaTerm_eq_of_paths _ i i ν _ _ m₁ m₂ (SPath.nil t) (SPath.nil t) qg₁
      (SPath.two true false hv₁ hv₂ ep)
      (SPath.eq_of_sides _ _ (by simp [SPath.sides_append, SPath.sides_two, SPath.sides]))
      (SPath.eq_of_sides _ _ (by simp [m₁, qg₁, SPath.sides_append, SPath.sides_two, SPath.sides]))
      pu₂ pg₂ qg₂ pv₂
      (SPath.eq_of_sides _ _ (by
        simp [m₁, qg₁, pu₂, pg₂, pv₂, SPath.sides_append, SPath.sides_two, SPath.sides]))
      (SPath.eq_of_sides _ _ (by simp [m₂, pu₂, qg₂, pv₂, SPath.sides_append, SPath.sides]))
      pu₃ pg₃ (SPath.nil s₀) (SPath.nil s₀)
      (SPath.eq_of_sides _ _ (by
        simp [m₂, pu₂, qg₂, pv₂, pu₃, pg₃, SPath.sides_append, SPath.sides_two, SPath.sides]))
      (SPath.eq_of_sides _ _ (by simp [pu₃, sd, SPath.sides_append, SPath.sides_two, SPath.sides]))]
  simp only [upwardGens, Generators.image, sigL₁, sigL₂, sigL₃, SKM.lay, crossImage, dite_eq_left,
    cupImage, capImage]
  have hcross : ∀ W, P.twoTwo _ _ _ _ (P.crossSameEntry c i _ _ _ _) pg₂ qg₂ rfl W =
      -(c.a i t' hR W ≫ c.a i t' hR W ≫ (P.mixedJ i i t' hR' W).inv) := fun W => rfl
  erw [hcross]
  simp only [qg₁, pg₃]
  rw [zeroTwo_two (Z' := (nextSector_upR_dnR t).symm ▸ _) (hZ := eqRec_heq _ _)]
  rw [twoZero_two (Z' := (nextSector_dnR_upR hR').symm ▸ _) (hZ := eqRec_heq _ _)]
  simp only [cupEntry, capEntry, postCup, postCap]
  simp only [pu₂, pu₃, pathFunctor_cons, pathFunctor_nil, Functor.comp_map, Functor.id_map]
  simp only [Category.assoc]
  refine isIso_homContentDistinctMixedPostMate_of_eq P.T P.W i
    (b := P.muM (nextSector (true, i) false s₀)) (b' := P.muM t) (nuM := P.muM t')
    (nuP := P.muP t) (muP := P.muP s₀) ?eb _ _ _ s₀.1 t.1
    (fun W₀ => -(c.a i t' hR W₀ ≫ c.a i t' hR W₀ ≫ (P.mixedJ i i t' hR' W₀).inv)) ?hC
    _ _ _ _ _ _ _ _ _ _ ?xY ?xZ
  case eb =>
    simp only [ProbeReservoir.muM, s₀, t', nextSector]
    rw [add_tsub_cancel_right]
  case xY =>
    refine (eqRec_heq _ _).trans ?_
    refine (eqRec_heq _ _).trans ?_
    exact pathFunctor_two_obj_heq (nextSector_upR_dnR t).symm true false hv₁ hv₂ ep hv₁ pv₂
      (congrArg (List.cons false) (SPath.sides_castTgt _ _)) Z
  case xZ =>
    exact eq_of_heq (pathFunctor_one_obj_heq (nextSector_upR_upP t').symm false pv₂
      (congrArg (List.cons false) (SPath.sides_castTgt _ _)) hd Z
      ((eqRec_heq _ _).trans (pathFunctor_obj_heq_of_nil _ Z)))
  case hC =>
    intro H
    have hin := CrossCoeffInputs.of_factor P hT hW
    rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
    · apply homDistinctMixedMateDot_isIso_of_inverse
      · exact hi ▸ P.T.dot_mem i _
      · exact hi ▸ P.W.dot_mem i _
      · exact (isUnit_iff_isIso _).1 (hT i _)
      · exact hW i _
      · exact (hc.even i hi t' hR _).1
      · exact (hc.even i hi t' hR _).2
    · apply homDistinctMixedMateDot_isIso_of_inverse_odd
      · exact hi ▸ P.T.dot_mem i _
      · exact hi ▸ P.W.dot_mem i _
      · exact (isUnit_iff_isIso _).1 (hT i _)
      · exact hW i _
      · exact hin.preDot_isUnit i t' hR _
      · exact hin.postDot_isNilpotent i t' hR _
      · have h := (hc.odd i hi t' hR ((homContentPostF P.T.obj P.W i s₀.1 (P.muP s₀)
          (P.muM_postE i hR)).obj H)).2
        refine Eq.trans (congrArg (· ≫ _) ?_) (h.trans ?_)
        · rfl
        · rfl

/-- The swapping entries `W_B` are invertible for a coefficient with the characterizing inverse
identities, when every probe dot is invertible and every reservoir dot is nilpotent. -/
theorem swappingReservoirInvertible (c : P.CrossCoeff) (hc : c.IsInverse)
    (hT : ∀ (i : I) {x y : X} (h : x + D.α i = y), IsUnit (show End (P.T.E i h) from P.T.dot i h))
    (hW : ∀ (i : I) {x y : X} (h : x + D.α i = y),
      IsNilpotent (show End (P.W.E i h) from P.W.dot i h)) :
    P.SwappingReservoirInvertible c :=
  fun i ν _ _ p q hp hq Z => isIso_sigmaEntry_reservoir c hc hT hW i ν p q hp hq Z

/-- All swapping entries of the same-colour sideways crossing are invertible, under the same
hypotheses. -/
theorem swappingInvertible_of_factor (c : P.CrossCoeff) (hc : c.IsInverse)
    (hT : ∀ (i : I) {x y : X} (h : x + D.α i = y), IsUnit (show End (P.T.E i h) from P.T.dot i h))
    (hW : ∀ (i : I) {x y : X} (h : x + D.α i = y),
      IsNilpotent (show End (P.W.E i h) from P.W.dot i h)) :
    P.SwappingInvertible c :=
  swappingInvertible_of_reservoir c (swappingReservoirInvertible c hc hT hW)

/-- The augmented blocks of the same-colour sideways crossing are invertible once the central
entries are: the swapping entries need no further hypothesis. -/
theorem augmentedInvertible_of_central (c : P.CrossCoeff) (hc : c.IsInverse)
    (hT : ∀ (i : I) {x y : X} (h : x + D.α i = y), IsUnit (show End (P.T.E i h) from P.T.dot i h))
    (hW : ∀ (i : I) {x y : X} (h : x + D.α i = y),
      IsNilpotent (show End (P.W.E i h) from P.W.dot i h))
    (hcentral : P.CentralInvertible c) : P.AugmentedInvertible c :=
  augmentedInvertible_of_central_of_swapping c hcentral (swappingInvertible_of_factor c hc hT hW)

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
