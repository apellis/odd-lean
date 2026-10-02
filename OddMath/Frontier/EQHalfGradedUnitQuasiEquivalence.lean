import OddMath.Frontier.EQHalfGradedUnit

/-!
# The integral low-rank half-graded unit quasi-equivalence

The actual unit functor induces bijections on Hom cohomology for every weight
and degree when N ≤ 1. Homogeneous ordinary representatives and primitives are
placed at their actual half-graded indices. Identity cocycles give essential
surjectivity. No half-graded derived or compact K₀ calculation is claimed here.
-/

noncomputable section
open CategoryTheory DG DG.HalfGradedDGRing DirectSum
open scoped DG.DegreeZero
namespace OddMath.Frontier.EQHalfGradedUnit.QuasiIso
open EQSkewDifferential

set_option backward.isDefEq.respectTransparency false

section General
variable {A : Type*} [Ring A] (H : HalfGradedDGRing A 2)

def evaluation : H.Regraded →+ A :=
  DirectSum.toAddMonoid fun p => (H.hgrading (halfDegree 2 p)).subtype

@[simp] theorem evaluation_place (p : ℤ × ℤ) (a : A)
    (ha : a ∈ H.hgrading (halfDegree 2 p)) : evaluation H (H.place p a ha) = a :=
  DirectSum.toAddMonoid_of _ _ _

theorem evaluation_d (x : H.Regraded) : evaluation H (d x) = H.hd (evaluation H x) := by
  induction x using HalfGradedDGRing.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | mk p a ha => rw [d_place, evaluation_place, evaluation_place]

theorem hom_eq_place {X Y : WeightCategory H.Regraded} {n : ℤ}
    {f : X ⟶ Y} (hf : f ∈ DG.grading n) :
    ∃ (a : A) (ha : a ∈ H.hgrading (halfDegree 2 (n, Y.as - X.as))),
      f.1 = H.place (n, Y.as - X.as) a ha := by
  let x : ⨁ p : ℤ × ℤ, ↥(halfGrading H.hgrading 2 p) := f.1
  refine ⟨(x (n, Y.as - X.as) : A), (x (n, Y.as - X.as)).2, ?_⟩
  have hsupp : ∀ p, p ≠ (n, Y.as - X.as) → x p = 0 := fun p hp => by
    by_cases h1 : p.1 = n
    · exact f.2 p (fun h2 => hp (Prod.ext h1 h2))
    · exact hf p h1
  change x = DirectSum.of _ (n, Y.as - X.as) (x (n, Y.as - X.as))
  ext p : 1
  by_cases hp : p = (n, Y.as - X.as)
  · subst hp; rw [DirectSum.of_eq_same]
  · rw [hsupp p hp, DirectSum.of_eq_of_ne _ _ _ hp]

def placedHom (X Y : WeightCategory H.Regraded) (n : ℤ) (a : A)
    (ha : a ∈ H.hgrading (halfDegree 2 (n, Y.as - X.as))) : X ⟶ Y :=
  ⟨H.place (n, Y.as - X.as) a ha, place_mem_wgrading (H := H) (n, Y.as - X.as) ha⟩

theorem placedHom_mem (X Y : WeightCategory H.Regraded) (n : ℤ) (a : A)
    (ha : a ∈ H.hgrading (halfDegree 2 (n, Y.as - X.as))) :
    placedHom H X Y n a ha ∈ DG.grading n := place_mem_grading (H := H) (n, Y.as - X.as) ha
end General

abbrev homCohomologyMap (N : ℕ) (X Y : WeightCategory source.Regraded) (n : ℤ) :=
  cohomology.mapAddMonoidHom ((weightFunctor N).mapAddHom (X := X) (Y := Y))
    (fun h => (weightFunctor N).map_mem_grading h) (fun f => (weightFunctor N).map_d f) n

theorem homCohomologyMap_injective {N : ℕ} (hN : N ≤ 1)
    (X Y : WeightCategory source.Regraded) (n : ℤ) :
    Function.Injective (homCohomologyMap N X Y n) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  induction x using DG.cohomology.induction_on with
  | h f =>
    simp only [homCohomologyMap] at hx
    obtain ⟨g, _, hg⟩ := (cohomology.mk_eq_zero_iff _).mp hx
    obtain ⟨z, hz, ef⟩ := hom_eq_place source f.2.1
    have he : evaluation (target N) (((weightFunctor N).map f.1).1) = (z : OPol N) := by
      rw [weightFunctor_map_val, ef, regradedMap_place, evaluation_place]
    have hd : d (evaluation (target N) g.1) = (z : OPol N) := by
      calc
        d (evaluation (target N) g.1) = evaluation (target N) (d g.1) :=
          (evaluation_d (target N) g.1).symm
        _ = evaluation (target N) (((weightFunctor N).map f.1).1) :=
          congrArg (fun t => evaluation (target N) t.1) hg
        _ = (z : OPol N) := he
    have hz0 : z = 0 := EQSmallRankDG.dg_int_eq_zero_of_boundary hN hd.symm
    have hf0 : f.1 = 0 := WeightCategory.hom_ext (ef.trans (by simp [hz0]))
    have hf : f = 0 := Subtype.ext hf0
    rw [hf, map_zero]


section GeneralComparison
variable {A : Type*} [Ring A] (H : HalfGradedDGRing A 2)

theorem hom_ext_of_evaluation {X Y : WeightCategory H.Regraded} {n : ℤ}
    {f g : X ⟶ Y} (hf : f ∈ DG.grading n) (hg : g ∈ DG.grading n)
    (he : evaluation H f.1 = evaluation H g.1) : f = g := by
  obtain ⟨a, ha, ea⟩ := hom_eq_place H hf
  obtain ⟨b, hb, eb⟩ := hom_eq_place H hg
  rw [ea, eb, evaluation_place, evaluation_place] at he
  exact WeightCategory.hom_ext (ea.trans ((place_congr rfl he ha hb).trans eb.symm))

theorem boundary_of_evaluation {X Y : WeightCategory H.Regraded} {n : ℤ}
    {f : X ⟶ Y} (hf : f ∈ DG.grading n) (b : A)
    (hb : b ∈ H.hgrading (halfDegree 2 (n - 1, Y.as - X.as)))
    (hd : H.hd b = evaluation H f.1) : f ∈ coboundaries (X ⟶ Y) n := by
  refine ⟨placedHom H X Y (n - 1) b hb, placedHom_mem H X Y (n - 1) b hb, ?_⟩
  apply hom_ext_of_evaluation H (n := n)
    (by simpa using DG.d_mem (placedHom_mem H X Y (n - 1) b hb)) hf
  change evaluation H (d (H.place _ b hb)) = _
  rw [evaluation_d, evaluation_place]
  exact hd
end GeneralComparison

/-- An integer in the correct original degree and an actual homogeneous primitive. -/
theorem homogeneous_representative {N : ℕ} (hN : N ≤ 1) {j : ℤ}
    (a : OPol N) (ha : a ∈ DG.grading j) (hda : d a = 0) :
    ∃ z : ℤ, z ∈ DG.grading j ∧ ∃ b : OPol N,
      b ∈ DG.grading (j - 1) ∧ d b = (z : OPol N) - a := by
  obtain ⟨x, hx⟩ := (EQSmallRankDG.intInclusion_isQuasiIso hN j).2
    (cohomology.mk (OPol N) j ⟨a, ha, hda⟩)
  induction x using cohomology.induction_on with
  | h z =>
    rw [DGRingHom.cohomologyMap_mk] at hx
    obtain ⟨b, hb, hd⟩ := (cohomology.mk_eq_mk_iff _ _).mp hx
    exact ⟨z.1, z.2.1, b, hb, hd⟩

/-- The supported diagonal shifts down by one for the primitive. -/
theorem diagonal_predecessor {n w j : ℤ}
    (h : diagonalDegree j = halfDegree 2 (n, w)) :
    diagonalDegree (j - 1) = halfDegree 2 (n - 1, w) := by
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  apply Prod.ext
  · simp only [diagonalDegree_apply, halfDegree_apply] at hfst ⊢
    omega
  · simpa only [diagonalDegree_apply, halfDegree_apply, Int.cast_sub, Int.cast_one]
      using congrArg (fun x : ZMod 2 => x - 1) hsnd

/-- Surjectivity of the actual integer inclusion in every weight and degree. -/
theorem homCohomologyMap_surjective {N : ℕ} (hN : N ≤ 1)
    (X Y : WeightCategory source.Regraded) (n : ℤ) :
    Function.Surjective (homCohomologyMap N X Y n) := by
  intro x
  induction x using cohomology.induction_on with
  | h f =>
    obtain ⟨a, ha, ea⟩ := hom_eq_place (target N) f.2.1
    have heval : evaluation (target N) f.1.1 = a := by rw [ea, evaluation_place]
    have hda : d a = 0 := by
      rw [← heval]
      change (target N).hd (evaluation (target N) f.1.1) = 0
      rw [← evaluation_d]
      change evaluation (target N) (d f.1).1 = 0
      rw [f.2.2]
      exact map_zero _
    by_cases hp : halfDegree 2 (n, Y.as - X.as) ∈ Set.range diagonalDegree
    · obtain ⟨j, hj⟩ := hp
      have ha' : a ∈ DG.grading j := by
        change a ∈ Diagonal.grading (OPol N) (halfDegree 2 (n, Y.as - X.as)) at ha
        rwa [← hj, Diagonal.grading_diagonal] at ha
      obtain ⟨z, hz, b, hb, hd⟩ := homogeneous_representative hN a ha' hda
      have hz' : z ∈ source.hgrading (halfDegree 2 (n, Y.as - X.as)) := by
        change z ∈ Diagonal.grading ℤ _
        rw [← hj, Diagonal.grading_diagonal]
        exact hz
      let s : X ⟶ Y := placedHom source X Y n z hz'
      have hs : s ∈ cocycles (X ⟶ Y) n := by
        refine ⟨placedHom_mem source X Y n z hz', ?_⟩
        apply WeightCategory.hom_ext
        change d (source.place _ z hz') = 0
        rw [d_place]
        exact (place_congr rfl (show source.hd z = 0 from rfl) _ _).trans (place_zero _)
      refine ⟨cohomology.mk (X ⟶ Y) n ⟨s, hs⟩, ?_⟩
      change cohomology.mk _ n _ = cohomology.mk _ n f
      apply (cohomology.mk_eq_mk_iff _ _).mpr
      apply boundary_of_evaluation (target N)
        (sub_mem ((weightFunctor N).map_mem_grading hs.1) f.2.1) b
      · change b ∈ Diagonal.grading (OPol N) (halfDegree 2 (n - 1, Y.as - X.as))
        rw [← diagonal_predecessor hj, Diagonal.grading_diagonal]
        exact hb
      · change d b = evaluation (target N) (((weightFunctor N).map s).1 - f.1.1)
        rw [map_sub, heval, weightFunctor_map_val]
        change d b = evaluation (target N) (regradedMap N (source.place _ z hz')) - a
        rw [regradedMap_place, evaluation_place]
        exact hd
    · have ha0 : a = 0 := by
        change a ∈ (ofDGRing (OPol N)).hgrading (halfDegree 2 (n, Y.as - X.as)) at ha
        rw [ofDGRing_hgrading_eq_bot (OPol N) hp] at ha
        exact ha
      have hf0 : f = 0 := Subtype.ext (WeightCategory.hom_ext (ea.trans (by simp [ha0])))
      refine ⟨0, ?_⟩
      rw [hf0, map_zero, map_zero]

theorem homCohomologyMap_bijective {N : ℕ} (hN : N ≤ 1)
    (X Y : WeightCategory source.Regraded) (n : ℤ) :
    Function.Bijective (homCohomologyMap N X Y n) :=
  ⟨homCohomologyMap_injective hN X Y n, homCohomologyMap_surjective hN X Y n⟩

/-- The original unit functor is a dg quasi-equivalence in integral rank zero or one. -/
theorem weightFunctor_isQuasiEquivalence {N : ℕ} (hN : N ≤ 1) :
    DG.IsQuasiEquivalence (weightFunctor N) where
  bijective_cohomology := homCohomologyMap_bijective hN
  exists_iso := by
    rintro ⟨k⟩
    let Z : WeightCategory (target N).Regraded := ⟨k⟩
    refine ⟨⟨k⟩, 𝟙 Z, 𝟙 Z, id_mem_cocycles Z, id_mem_cocycles Z, ?_, ?_⟩ <;>
      change (𝟙 Z) ≫ (𝟙 Z) - (𝟙 Z) ∈ coboundaries (Z ⟶ Z) 0
    all_goals rw [Category.id_comp, sub_self]; exact zero_mem _

end OddMath.Frontier.EQHalfGradedUnit.QuasiIso
