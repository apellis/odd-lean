import OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirProbeEntry
import OddMath.QuiverHecke.SwappedAssembly.Sigma.DistinctReservoirShift

/-! # The pure distinct-colour reservoir sideways entry

Brundan–Ellis Definition 1.5, (1.11): the pure reservoir entry is the
right mate of its prescribed reservoir crossing, with the given content
parity shifts. Its factor mate is invertible by the reservoir's
multicolour inversion relation.
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
variable (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
  (M : RouquierMulticolour W Sc) (i j : I) (hij : i ≠ j) (β : I →₀ ℕ) (μ : X)
local notation "H" a:max => homWeightSector T W.obj μ a
local notation "Ei" h:max => homContentPostE T W i β μ h
local notation "Fi" h:max => homContentPostF T W i β μ h
local notation "Ej" h:max => homContentPostE T W j β μ h
local notation "A" h:max => homContentPostAdjunction T W i β μ h

include M hij in
private theorem postDistinct_of_eq {a b b' c d : X} (eb : b = b')
    (h₁ : a + D.α j = b) (h₂ : b + D.α i = c)
    (h₃ : a + D.α i = d) (h₄ : d + D.α j = c) (h₂' : b' + D.α i = c)
    (cross : ∀ U : H a, (Ei h₂).obj ((Ej h₁).obj U) ⟶ (Ej h₄).obj ((Ei h₃).obj U))
    (hc : ∀ U, cross U = homShiftedPostCrossing (homContentShift D i β)
      (homContentShift D j β) (W.cross i j h₁ h₂ h₃ h₄) U)
    {S Y Tg : H b'} {U : H a} (Z : H d)
    (xs : S = Y)
    (xpre : (Fi h₂').obj ((Ei h₂').obj Y) = (Fi h₂').obj ((Ei h₂).obj ((Ej h₁).obj U)))
    (xpost : (Fi h₂').obj ((Ej h₄).obj ((Ei h₃).obj U)) =
      (Fi h₂').obj ((Ej h₄).obj ((Ei h₃).obj ((Fi h₃).obj Z))))
    (xt : (Fi h₂').obj ((Ej h₄).obj Z) = Tg)
    (hY : HEq Y ((Ej h₁).obj U)) (hU : U = (Fi h₃).obj Z) :
    IsIso (eqToHom xs ≫ (A h₂').unit.app Y ≫ eqToHom xpre ≫
      (Fi h₂').map (cross U) ≫ eqToHom xpost ≫
      (Fi h₂').map ((Ej h₄).map ((A h₃).counit.app Z)) ≫ eqToHom xt) := by
  subst eb
  obtain rfl : h₂' = h₂ := rfl
  obtain rfl := eq_of_heq hY
  subst hU xs xt
  rw [hc]
  have hiso := homShiftedPostCrossMate_isIso W M i j hij h₁ h₂ h₃ h₄
    (homContentShift D i β) (homContentShift D j β) Z
  simpa only [homShiftedPostCrossMate, Functor.map_comp,
    eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc] using hiso
end Transport
namespace ProbeReservoir
variable {P : ProbeReservoir k B D Sc}
attribute [local irreducible] Finsupp.zipWith contentWeight

private theorem nextSector_resUp_dn {i : I} (t : Sector I) :
    nextSector (up i) false (nextSector (dn i) false t) = t := by
  obtain ⟨a, b⟩ := t
  simp only [nextSector, Prod.mk.injEq, true_and]
  exact add_tsub_cancel_right b _

private theorem nextSector_resDn_up {i : I} {t : Sector I}
    (h : StepValid (up i) false t) :
    nextSector (dn i) false (nextSector (up i) false t) = t := by
  obtain ⟨a, b⟩ := t
  simp only [StepValid] at h
  simp only [nextSector, Prod.mk.injEq, true_and]
  exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 h)

private theorem nextSector_resUp_resUp {i j : I} (t : Sector I) :
    nextSector (up j) false (nextSector (up i) false t) =
      nextSector (up i) false (nextSector (up j) false t) := by
  simp only [nextSector, tsub_right_comm]

private theorem contentShift_pair_parity (i j : I) (β : I →₀ ℕ) :
    (homContentShift D j β + homContentShift D i β) * (D.parity i * D.parity j) = 0 := by
  unfold homContentShift
  generalize D.parity i = pi
  generalize D.parity j = pj
  generalize contentParity D β = b
  fin_cases pi <;> fin_cases pj <;> fin_cases b <;> decide

/-- The pure reservoir entry is invertible by the reservoir factor inversion relation. -/
theorem isIso_sigmaEntry_pure_reservoir (c : P.CrossCoeff) {i j : I} (hij : i ≠ j) (ν : X)
    {t s : Sector I} (p : SPath (wd D ν [up j, dn i]) t s) (q : SPath (wd D ν [dn i, up j]) t s)
    (hp : p.sides = [false, false]) (hq : q.sides = [false, false]) (Z : P.H s) :
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
    SPath.two false false hw₁ (by simp [StepValid, nextSector]) (nextSector_resUp_dn t)
  let m₁ : SPath (sigL₁ (D := D) i j ν).cod.word t _ :=
    ((SPath.nil t).append qg₁).append (SPath.two false false hv₁ hv₂ ep)
  -- the crossing
  let t' := nextSector (false, i) false t
  let x := nextSector (true, i) false (nextSector (true, j) false t')
  have hpi : StepValid (true, i) false t' := by simp [t', StepValid, nextSector]
  have hpj : StepValid (true, j) false (nextSector (true, i) false t') := by
    simpa only [t', nextSector_resUp_dn] using hv₁
  have hqi : StepValid (true, i) false (nextSector (true, j) false t') := by
    classical
    simp [t', StepValid, nextSector, Finsupp.coe_tsub, Finsupp.single_apply, hij, Ne.symm hij]
  have hx : StepValid (false, i) false x := trivial
  let pu₂ : SPath (sigL₂ (D := D) i j ν).left t t' := .cons _ false t hw₁ (.nil _)
  let pg₂ : SPath ((SKM.sig D).dom (sigL₂ (D := D) i j ν).gen) t' x :=
    SPath.two false false hpi hpj (nextSector_resUp_resUp (i := i) (j := j) t')
  let qg₂ : SPath ((SKM.sig D).cod (sigL₂ (D := D) i j ν).gen) t' x :=
    SPath.two false false hw₂ hqi rfl
  let pv₂ : SPath (sigL₂ (D := D) i j ν).right x (nextSector (true, j) false t') :=
    .cons _ false x hx ((SPath.nil _).castTgt (nextSector_resDn_up hqi))
  let m₂ : SPath (sigL₂ (D := D) i j ν).cod.word t _ := (pu₂.append qg₂).append pv₂
  rw [sigmaEntry_eq_sigmaTerm (m₁ := m₁) (m₂ := m₂) (p₁ := false) (p₂ := false) (q₁ := false)
    (q₂ := false) (hp := SPath.sides_two ..) (hq := SPath.sides_two ..)
    (hm₁ := by simp [m₁, qg₁, SPath.sides_append, SPath.sides_two, SPath.sides])
    (hm₂ := by simp [m₂, pu₂, qg₂, pv₂, SPath.sides_append, SPath.sides_two, SPath.sides])]
  have sd := @SPath.sides_cast.{u}
  -- the cap
  let s₀ := nextSector (true, j) false t'
  have hd : StepValid (false, i) false (nextSector (true, i) false s₀) := trivial
  let pu₃ : SPath (sigL₃ (D := D) i j ν).left t s₀ :=
    .cons _ false t hw₁ (.cons _ false _ hw₂ (.nil _))
  let pg₃ : SPath ((SKM.sig D).dom (sigL₃ (D := D) i j ν).gen) s₀ s₀ :=
    SPath.two false false hqi hd (nextSector_resDn_up hqi)
  rw [sigmaTerm_eq_of_paths _ i j ν _ _ m₁ m₂ (SPath.nil t) (SPath.nil t) qg₁
      (SPath.two false false hv₁ hv₂ ep)
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
  dsimp only [wd, SKM.sig, SKM.Shape.dom, SKM.Shape.cod] at *
  have hcross (W : P.H x) := P.twoTwo_two
    ⟨up i, SKM.wt D (sigL₂ (D := D) i j ν).gen.2 [up j]⟩
    ⟨up j, (sigL₂ (D := D) i j ν).gen.2⟩
    ⟨up j, SKM.wt D (sigL₂ (D := D) i j ν).gen.2 [up i]⟩
    ⟨up i, (sigL₂ (D := D) i j ν).gen.2⟩ (P.crossNeEntry i j _ _ _ _)
    false false false false hpi hpj hw₂ hqi
    (nextSector_resUp_resUp (i := i) (j := j) t') rfl rfl W W HEq.rfl
  dsimp only [crossNeEntry] at hcross
  dsimp only [sigL₁, sigL₂, sigL₃, SKM.lay, wd] at hcross
  with_unfolding_all rw [show ∀ W, P.twoTwo _ _ _ _ (P.crossNeEntry i j _ _ _ _) pg₂ qg₂ rfl W = _ from hcross]
  simp only [qg₁, pg₃]
  rw [zeroTwo_two (Z' := (nextSector_resUp_dn t).symm ▸ _) (hZ := eqRec_heq _ _)]
  rw [twoZero_two (Z' := (nextSector_resDn_up hqi).symm ▸ _) (hZ := eqRec_heq _ _)]
  simp only [cupEntry, capEntry, postCup, postCap]
  simp only [pu₂, pu₃, pathFunctor_cons, pathFunctor_nil, Functor.comp_map, Functor.id_map]
  simp only [postCrossNe, Functor.map_comp, eqToHom_map, Category.assoc]
  simp only [← eqToHom_trans]
  apply postDistinct_of_eq P.T.obj P.W P.reservoirRel i j hij t.1 (P.muP t)
  · simp [muM, t', nextSector]
  · intro U
    simpa only [contentShift_pair_parity, sign_zero, one_smul] using
      postPairCrossing_eq (homContentShift D i t.1) (homContentShift D j t.1)
        _ (P.W.cross_mem i j _ _ _ _) U
  · refine (eqRec_heq _ _).trans ((eqRec_heq _ _).trans ?_)
    exact pathFunctor_two_obj_heq (nextSector_resUp_dn t).symm false false hv₁ hv₂ ep hv₁ pv₂
      (congrArg (List.cons false) (SPath.sides_castTgt _ _)) Z
  · exact eq_of_heq (pathFunctor_one_obj_heq (nextSector_resUp_resUp (i := i) (j := j) t') false pv₂
      (congrArg (List.cons false) (SPath.sides_castTgt _ _)) hd Z
      ((eqRec_heq _ _).trans (pathFunctor_obj_heq_of_nil _ Z)))

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
