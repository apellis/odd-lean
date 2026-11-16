import OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirProbeEntry
import OddMath.SKM.RouquierHomDistinctPreMate
import OddMath.SKM.RouquierHomDistinctPostShift

/-! # The pure distinct-colour sideways entries

Brundan–Ellis Definition 1.5, (1.11): the pure probe entry is the
left mate of the probe crossing, and the pure reservoir entry is the
right mate of the reservoir crossing. The left-mate hypothesis remains
explicit in this intermediate result.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
section Transport
variable (T : RouquierFamily (k := k) (B := B) D) (W : X → B) (i j : I)
  (hL : LeftMateInvertible T T.leftAdjoints) (hij : i ≠ j) (μ : X)
local notation "H" a:max => homWeightSector T.obj W a μ
local notation "Ei" h:max => homContentPreE T W i μ h
local notation "Fi" h:max => homContentPreF T W i μ h
local notation "Ej" h:max => homContentPreE T W j μ h
local notation "A" h:max => homContentPreAdjunction T W T.leftAdjoints i μ h

include hL hij in
private theorem preDistinct_of_eq {a b b' c d d' : X} (eb : b = b') (ed : d = d')
    (h₁ : -a + D.α i = -b) (h₂ : -b + D.α j = -d)
    (h₃ : -a + D.α j = -c) (h₄ : -c + D.α i = -d)
    (h₁' : -a + D.α i = -b') (h₄' : -c + D.α i = -d')
    {S Y Tg : H b'} {W₀ : H d} (Z : H c)
    (xs : S = Y)
    (xpre : (Fi h₁').obj ((Ei h₁').obj Y) =
      (Fi h₁').obj ((Ei h₁).obj ((Ej h₂).obj W₀)))
    (xpost : (Fi h₁').obj ((Ej h₃).obj ((Ei h₄).obj W₀)) =
      (Fi h₁').obj ((Ej h₃).obj ((Ei h₄').obj ((Fi h₄').obj Z))))
    (xt : (Fi h₁').obj ((Ej h₃).obj Z) = Tg)
    (hY : HEq Y ((Ej h₂).obj W₀)) (hW : HEq W₀ ((Fi h₄').obj Z)) :
    IsIso (eqToHom xs ≫ (A h₁').unit.app Y ≫ eqToHom xpre ≫
      (Fi h₁').map (associator (T.E i h₁) (T.E j h₂) W₀).inv ≫
      (Fi h₁').map (T.cross j i h₁ h₂ h₃ h₄ ▷ W₀) ≫
      (Fi h₁').map (associator (T.E j h₃) (T.E i h₄) W₀).hom ≫
      eqToHom xpost ≫ (Fi h₁').map ((Ej h₃).map ((A h₄').counit.app Z)) ≫ eqToHom xt) := by
  subst eb ed
  obtain rfl : h₁' = h₁ := rfl
  obtain rfl : h₄' = h₄ := rfl
  obtain rfl := eq_of_heq hY
  obtain rfl := eq_of_heq hW
  subst xs xt
  have hiso := homContentDistinctPreMate_isIso T W T.leftAdjoints hL hij μ h₁' h₂ h₃ h₄' Z
  simp only [homDistinctPreMate, Functor.map_comp] at hiso
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  with_unfolding_all exact hiso

include hL hij in
/-- Transport charts around the pre/pre mate, retained separately so comparisons of
sector weights are supplied as equalities rather than unfolded during matching. -/
private theorem preDistinct_charts_of_eq {a b b' c d d' : X} (eb : b = b') (ed : d = d')
    (h₁ : -a + D.α i = -b) (h₂ : -b + D.α j = -d)
    (h₃ : -a + D.α j = -c) (h₄ : -c + D.α i = -d)
    (h₁' : -a + D.α i = -b') (h₄' : -c + D.α i = -d')
    {S A1 Y U1 U2 U3 V1 V2 V3 V4 E1 Tg : H b'} {W₀ : H d} (Z : H c)
    (xs₀ : S = A1) (xs₁ : A1 = Y)
    (xp₀ : (Fi h₁').obj ((Ei h₁').obj Y) = U1) (xp₁ : U1 = U2) (xp₂ : U2 = U3)
    (xp₃ : U3 = (Fi h₁').obj ((Ei h₁).obj ((Ej h₂).obj W₀)))
    (xq₀ : (Fi h₁').obj ((Ej h₃).obj ((Ei h₄).obj W₀)) = V1)
    (xq₁ : V1 = V2) (xq₂ : V2 = V3) (xq₃ : V3 = V4)
    (xq₄ : V4 = (Fi h₁').obj ((Ej h₃).obj ((Ei h₄').obj ((Fi h₄').obj Z))))
    (xt₀ : (Fi h₁').obj ((Ej h₃).obj Z) = E1) (xt₁ : E1 = Tg)
    (hY : HEq Y ((Ej h₂).obj W₀)) (hW : HEq W₀ ((Fi h₄').obj Z)) :
    IsIso (eqToHom xs₀ ≫ eqToHom xs₁ ≫ (A h₁').unit.app Y ≫
      eqToHom xp₀ ≫ eqToHom xp₁ ≫ eqToHom xp₂ ≫ eqToHom xp₃ ≫
      (Fi h₁').map (associator (T.E i h₁) (T.E j h₂) W₀).inv ≫
      (Fi h₁').map (T.cross j i h₁ h₂ h₃ h₄ ▷ W₀) ≫
      (Fi h₁').map (associator (T.E j h₃) (T.E i h₄) W₀).hom ≫
      eqToHom xq₀ ≫ eqToHom xq₁ ≫ eqToHom xq₂ ≫ eqToHom xq₃ ≫ eqToHom xq₄ ≫
      (Fi h₁').map ((Ej h₃).map ((A h₄').counit.app Z)) ≫
      eqToHom xt₀ ≫ eqToHom xt₁) := by
  simp only [eqToHom_trans_assoc, eqToHom_trans]
  exact preDistinct_of_eq T W i j hL hij μ eb ed h₁ h₂ h₃ h₄ h₁' h₄' Z
    _ _ _ _ hY hW

end Transport

namespace ProbeReservoir
variable {P : ProbeReservoir k B D Sc}
attribute [local irreducible] Finsupp.zipWith contentWeight
  homContentPreAdjunction RouquierFamily.leftAdjoints

private theorem nextSector_probeUp_probeUp {i j : I} (t : Sector I) :
    nextSector (up j) true (nextSector (up i) true t) =
      nextSector (up i) true (nextSector (up j) true t) := by
  simp only [nextSector, add_right_comm]

private theorem pathFunctor_two_obj_heq_tail {c₁ c₂ : Col I X} {a a' x s : Sector I}
    (ea : a = a') (ex : nextSector c₁.l true a' = x)
    (hw₁ : StepValid c₁.l true a) (hw₂ : StepValid c₂.l true (nextSector c₁.l true a))
    (ep : nextSector c₂.l true (nextSector c₁.l true a) = s)
    (hv' : StepValid c₁.l true a') (pv : SPath [c₂] x s) (hpv : pv.sides = [true])
    (Z : P.H s) (W : P.H (nextSector c₁.l true a'))
    (hW : HEq W ((P.pathFunctor pv).obj Z)) :
    HEq ((P.pathFunctor (SPath.two true true hw₁ hw₂ ep)).obj Z)
      ((P.step c₁.l true a' hv').obj W) := by
  subst ea ex
  obtain rfl := eq_of_heq hW
  exact pathFunctor_two_obj_heq rfl true true hw₁ hw₂ ep hv' pv hpv Z

/-- The pure probe entry is invertible under the factor left-mate input. -/
theorem isIso_sigmaEntry_pure_probe (hL : LeftMateInvertible P.T P.T.leftAdjoints) (c : P.CrossCoeff) {i j : I} (hij : i ≠ j) (ν : X)
    {t s : Sector I} (p : SPath (wd D ν [up j, dn i]) t s) (q : SPath (wd D ν [dn i, up j]) t s)
    (hp : p.sides = [true, true]) (hq : q.sides = [true, true]) (Z : P.H s) :
    IsIso (P.sigmaEntry c i j ν p q Z) := by
  obtain ⟨τ₁, τ₂, hv₁, hv₂, ep, rfl⟩ := SPath.exists_eq_two p
  obtain ⟨σ₁, σ₂, hw₁, hw₂, eq, rfl⟩ := SPath.exists_eq_two q
  rw [SPath.sides_two] at hp hq
  simp only [List.cons.injEq, and_true] at hp hq
  obtain ⟨rfl, rfl⟩ := hp
  obtain ⟨rfl, rfl⟩ := hq
  subst eq
  -- the cup
  let qg₁ : SPath ((SKM.sig D).cod (sigL₁ (D := D) i j ν).gen) t t :=
    SPath.two true true hw₁ trivial (nextSector_up_dn hw₁)
  let m₁ : SPath (sigL₁ (D := D) i j ν).cod.word t _ :=
    ((SPath.nil t).append qg₁).append (SPath.two true true hv₁ hv₂ ep)
  -- the crossing
  let t' := nextSector (false, i) true t
  let x := nextSector (true, i) true (nextSector (true, j) true t')
  have hx : StepValid (false, i) true x := by
    simp [x, t', StepValid, nextSector]
  let pu₂ : SPath (sigL₂ (D := D) i j ν).left t t' := .cons _ true t hw₁ (.nil _)
  let pg₂ : SPath ((SKM.sig D).dom (sigL₂ (D := D) i j ν).gen) t' x :=
    SPath.two true true trivial trivial (nextSector_probeUp_probeUp (i := i) (j := j) t')
  let qg₂ : SPath ((SKM.sig D).cod (sigL₂ (D := D) i j ν).gen) t' x :=
    SPath.two true true trivial trivial rfl
  let pv₂ : SPath (sigL₂ (D := D) i j ν).right x (nextSector (true, j) true t') :=
    .cons _ true x hx ((SPath.nil _).castTgt (nextSector_dn_up (nextSector (up j) true t')))
  let m₂ : SPath (sigL₂ (D := D) i j ν).cod.word t _ := (pu₂.append qg₂).append pv₂
  rw [sigmaEntry_eq_sigmaTerm (m₁ := m₁) (m₂ := m₂) (p₁ := true) (p₂ := true) (q₁ := true)
    (q₂ := true) (hp := SPath.sides_two ..) (hq := SPath.sides_two ..)
    (hm₁ := by simp [m₁, qg₁, SPath.sides_append, SPath.sides_two, SPath.sides])
    (hm₂ := by simp [m₂, pu₂, qg₂, pv₂, SPath.sides_append, SPath.sides_two, SPath.sides])]
  have sd := @SPath.sides_cast.{u}
  -- the cap
  let s₀ := nextSector (true, j) true t'
  have hd : StepValid (false, i) true (nextSector (true, i) true s₀) := by
    simp [s₀, StepValid, nextSector]
  let pu₃ : SPath (sigL₃ (D := D) i j ν).left t s₀ :=
    .cons _ true t hw₁ (.cons _ true _ hw₂ (.nil _))
  let pg₃ : SPath ((SKM.sig D).dom (sigL₃ (D := D) i j ν).gen) s₀ s₀ :=
    SPath.two true true trivial hd (nextSector_dn_up s₀)
  rw [sigmaTerm_eq_of_paths _ i j ν _ _ m₁ m₂ (SPath.nil t) (SPath.nil t) qg₁
      (SPath.two true true hv₁ hv₂ ep)
      (SPath.eq_of_sides _ _ (by simp [SPath.sides_append, SPath.sides_two, SPath.sides]))
      (SPath.eq_of_sides _ _ (by simp [m₁, qg₁, SPath.sides_append, SPath.sides_two, SPath.sides]))
      pu₂ pg₂ qg₂ pv₂
      (SPath.eq_of_sides _ _ (by
        simp [m₁, qg₁, pu₂, pg₂, pv₂, SPath.sides_append, SPath.sides_two, SPath.sides]))
      (SPath.eq_of_sides _ _ (by
        simp [m₂, pu₂, qg₂, pv₂, SPath.sides_append, SPath.sides_two, SPath.sides, SPath.sides_castTgt]))
      pu₃ pg₃ (SPath.nil s₀) (SPath.nil s₀)
      (SPath.eq_of_sides _ _ (by
        simp [m₂, pu₂, qg₂, pv₂, pu₃, pg₃, sd, SPath.sides_append, SPath.sides_two, SPath.sides,
          SPath.sides_castTgt]))
      (SPath.eq_of_sides _ _ (by simp [pu₃, sd, SPath.sides_append, SPath.sides_two, SPath.sides]))]
  simp only [upwardGens, Generators.image, sigL₁, sigL₂, sigL₃, SKM.lay, crossImage,
    dite_eq_right hij, cupImage, capImage]
  have hcross (W : P.H x) := P.twoTwo_two
    ⟨up i, SKM.wt D (sigL₂ (D := D) i j ν).gen.2 [up j]⟩
    ⟨up j, (sigL₂ (D := D) i j ν).gen.2⟩
    ⟨up j, SKM.wt D (sigL₂ (D := D) i j ν).gen.2 [up i]⟩
    ⟨up i, (sigL₂ (D := D) i j ν).gen.2⟩ (P.crossNeEntry i j _ _ _ _)
    true true true true trivial trivial trivial trivial
    (nextSector_probeUp_probeUp (i := i) (j := j) t') rfl rfl W W HEq.rfl
  dsimp only [crossNeEntry] at hcross
  dsimp only [sigL₁, sigL₂, sigL₃, SKM.lay, wd] at hcross
  erw [hcross]
  simp only [qg₁, pg₃]
  rw [zeroTwo_two (Z' := (nextSector_up_dn hw₁).symm ▸ _) (hZ := eqRec_heq _ _)]
  rw [twoZero_two (Z' := (nextSector_dn_up s₀).symm ▸ _) (hZ := eqRec_heq _ _)]
  simp only [cupEntry, capEntry, preCup, preCap, preAdjAt]
  simp only [pu₂, pu₃, pathFunctor_cons, pathFunctor_nil, Functor.comp_map, Functor.id_map]
  simp only [preCrossNe, Functor.map_comp, eqToHom_map, Category.assoc]
  apply preDistinct_charts_of_eq P.T P.W.obj i j hL hij (P.muM t)
    (a := P.muP t') (b := P.muP (nextSector (up i) true t')) (b' := P.muP t)
    (c := P.muP s₀) (d := P.muP (nextSector (up j) true (nextSector (up i) true t')))
    (d' := P.muP x)
  · simp [muP, t', nextSector, tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hw₁)]
  · simp only [muP, x, nextSector, add_right_comm]
  · refine (eqRec_heq _ _).trans ((eqRec_heq _ _).trans ?_)
    exact pathFunctor_two_obj_heq_tail (nextSector_up_dn hw₁).symm
      (nextSector_probeUp_probeUp (i := i) (j := j) t') hv₁ hv₂ ep trivial pv₂
      (congrArg (List.cons true) (SPath.sides_castTgt _ _)) Z _ (eqRec_heq _ _)
  · refine (eqRec_heq _ _).trans ?_
    refine (pathFunctor_one_obj_heq rfl true pv₂
      (congrArg (List.cons true) (SPath.sides_castTgt _ _)) hd Z ?_).trans
        (P.preF_obj_heq i (nextSector_dn_up s₀) _ _ _)
    exact (eqRec_heq _ _).trans ((eqRec_heq _ _).trans
      ((eqRec_heq _ _).trans HEq.rfl))

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
