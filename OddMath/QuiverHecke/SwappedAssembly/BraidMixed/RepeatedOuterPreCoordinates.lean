/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPreRoutes
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Basic

/-! Literal dot coordinates and coefficient on Ri Rj Pi, for Brundan–Ellis (1.9). -/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace RepeatedOuterPre
open ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hi : StepValid (true, i) false s)
  (hj : StepValid (true, j) false (nextSector (true, i) false s))
  (Z : P.H (nextSector (true, j) false
    (nextSector (true, i) false (nextSector (true, i) true s))))

abbrev obj := (P.step (true, i) false s hi).obj
  (P.rpObj j i (nextSector (true, i) false s) hj Z)

def outerDot : End (obj P i j s hi hj Z) :=
  P.dotDiag i false s hi (P.rpObj j i (nextSector (true, i) false s) hj Z)
def middleDot : End (obj P i j s hi hj Z) :=
  (P.step (true, i) false s hi).map
    (P.dotDiag j false (nextSector (true, i) false s) hj
      ((P.step (true, i) true _ trivial).obj Z))
def innerDot : End (obj P i j s hi hj Z) :=
  (P.step (true, i) false s hi).map
    ((P.step (true, j) false (nextSector (true, i) false s) hj).map
      (P.dotDiag i true (nextSector (true, j) false (nextSector (true, i) false s)) trivial Z))

def coefficientAlg : End (middleObj P i j s hi hj Z) →ₐ[k] End (obj P i j s hi hj Z) :=
  conjAlg (k := k) (rightIso P i j s hi hj Z)

private lemma forward_conj {C : Type u} [Category C] [Preadditive C] [Linear k C]
    {V W : C} (K : V ≅ W) (x : End V) (y : End W) (ε : k)
    (h : x ≫ K.hom = ε • (K.hom ≫ y)) :
    K.inv ≫ x ≫ K.hom = ε • y := by
  rw [← Category.assoc, Category.assoc K.inv, h, Linear.comp_smul,
    Iso.inv_hom_id_assoc]

lemma coefficientAlg_pre :
    coefficientAlg P i j s hi hj Z (P.rpPreDot i s hi (rest P i j s hj Z)) =
      zsign k (D.parity i * D.parity j) • innerDot P i j s hi hj Z := by
  apply forward_conj
  have h := congrArg (P.step (true, i) false s hi).map
    (P.prPreDot_comp_mixedJ_ne i j (nextSector (true, i) false s) hj Z)
  simp only [Functor.map_comp, Functor.map_smul] at h
  exact h

lemma coefficientAlg_post :
    coefficientAlg P i j s hi hj Z (P.rpPostDot i s hi (rest P i j s hj Z)) =
      zsign k (D.parity i * D.parity j) • outerDot P i j s hi hj Z := by
  apply forward_conj
  have h := (P.dotDiag_supernatural i false s hi).naturality
    ((P.mixedJ_supernatural i j (nextSector (true, i) false s) hj).mem Z)
  have hz (p : ZMod 2) : sign k p = zsign k p := by
    fin_cases p <;> simp [sign, zsign]
  have hp : D.parity i * (D.parity i * D.parity j) = D.parity i * D.parity j := by
    rw [← mul_assoc, SKM.zmod2_mul_self]
  simp only [hp, hz] at h
  have h' := congrArg (fun f => zsign k (D.parity i * D.parity j) • f) h
  simp only [smul_smul, ProbeReservoir.zsign_mul_self', one_smul] at h'
  exact h'.symm

def normalizedCoeff (c : P.CrossCoeff Sc) : End (obj P i j s hi hj Z) :=
  zsign k (D.parity i * D.parity j) •
    coefficientAlg P i j s hi hj Z (c.a i s hi (rest P i j s hj Z))

lemma coeff_even (c : P.CrossCoeff Sc) (hc : c.IsInverse) (hp : D.parity i = 0) :
    normalizedCoeff P i j s hi hj Z c *
      (outerDot P i j s hi hj Z - innerDot P i j s hi hj Z) = 1 := by
  have h := congrArg (coefficientAlg P i j s hi hj Z)
    (hc.even i hp s hi (rest P i j s hj Z)).2
  simp only [← End.mul_def, map_mul, map_sub, ← End.one_def, map_one,
    coefficientAlg_pre, coefficientAlg_post, hp, zero_mul, zsign_zero, one_smul] at h
  simpa only [normalizedCoeff, hp, zero_mul, zsign_zero, one_smul] using h

lemma coeff_odd (c : P.CrossCoeff Sc) (hc : c.IsInverse) (hp : D.parity i = 1) :
    normalizedCoeff P i j s hi hj Z c *
      (outerDot P i j s hi hj Z * outerDot P i j s hi hj Z -
        innerDot P i j s hi hj Z * innerDot P i j s hi hj Z) =
      outerDot P i j s hi hj Z - innerDot P i j s hi hj Z := by
  have h := congrArg (coefficientAlg P i j s hi hj Z)
    (hc.odd i hp s hi (rest P i j s hj Z)).2
  simp only [← End.mul_def, map_mul, map_sub, coefficientAlg_pre, coefficientAlg_post,
    smul_mul_assoc, mul_smul_comm, smul_smul, ProbeReservoir.zsign_mul_self', one_smul] at h
  have h' := congrArg (fun f => -(zsign k (D.parity i * D.parity j) • f)) h
  simpa only [normalizedCoeff, smul_sub, smul_smul, ProbeReservoir.zsign_mul_self', one_smul,
    ← smul_mul_assoc, ← mul_neg, neg_sub, ← smul_neg] using h'

lemma dotX (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    dotEntry (P.swappedGens c L) ν [] i [up j, up i]
      (SPath.three false false true hi hj trivial rfl) Z = outerDot P i j s hi hj Z := by
  unfold dotEntry
  refine eq_of_heq ((heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [] (SKM.Shape.dot i) [up j, up i]) (.nil s)
    (.cons _ false _ hi (.nil _)) (.cons _ false _ hi (.nil _))
    (SPath.two false true hj trivial rfl) _ _ rfl rfl Z)).trans ?_)
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (P.dotImage_reservoir i (SKM.wt D ν [up j, up i]) s hi hi _)

lemma dotY (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    dotEntry (P.swappedGens c L) ν [up i] j [up i]
      (SPath.three false false true hi hj trivial rfl) Z = middleDot P i j s hi hj Z := by
  unfold dotEntry
  refine eq_of_heq ((heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [up i] (SKM.Shape.dot j) [up i]) (.cons _ false s hi (.nil _))
    (.cons _ false _ hj (.nil _)) (.cons _ false _ hj (.nil _))
    (.cons _ true _ trivial (.nil _)) _ _ rfl rfl Z)).trans ?_)
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (congrArg (P.step (true, i) false s hi).map
    (P.dotImage_reservoir j (SKM.wt D ν [up i]) (nextSector (true, i) false s) hj hj _))

lemma dotZ (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    dotEntry (P.swappedGens c L) ν [up i, up j] i []
      (SPath.three false false true hi hj trivial rfl) Z = innerDot P i j s hi hj Z := by
  unfold dotEntry
  refine eq_of_heq ((heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [up i, up j] (SKM.Shape.dot i) []) (SPath.two false false hi hj rfl)
    (.cons _ true _ trivial (.nil _)) (.cons _ true _ trivial (.nil _))
    (.nil _) _ _ rfl rfl Z)).trans ?_)
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (congrArg (fun f => (P.step (true, i) false s hi).map
    ((P.step (true, j) false (nextSector (true, i) false s) hj).map f))
    (P.dotImage_probe i ν (nextSector (true, j) false (nextSector (true, i) false s))
      trivial trivial Z))
lemma dots_xz :
    outerDot P i j s hi hj Z * innerDot P i j s hi hj Z =
      zsign k (D.parity i) •
        (innerDot P i j s hi hj Z * outerDot P i j s hi hj Z) := by
  have h := congrArg (coefficientAlg P i j s hi hj Z)
    (P.rpPreDot_comp_rpPostDot i s hi (rest P i j s hj Z))
  simp only [koszulSign_smul_eq_zsign (k := k), SKM.zmod2_mul_self,
    ← End.mul_def, map_mul, map_smul, coefficientAlg_pre, coefficientAlg_post,
    smul_mul_assoc, mul_smul_comm, smul_smul, ProbeReservoir.zsign_mul_self', one_smul] at h
  exact h

lemma dots_zy :
    innerDot P i j s hi hj Z * middleDot P i j s hi hj Z =
      zsign k (D.parity i * D.parity j) •
        (middleDot P i j s hi hj Z * innerDot P i j s hi hj Z) := by
  have h := (P.dotDiag_supernatural j false (nextSector (true, i) false s) hj).naturality
    ((P.dotDiag_supernatural i true
      (nextSector (true, j) false (nextSector (true, i) false s)) trivial).mem Z)
  have hz (p : ZMod 2) : sign k p = zsign k p := by
    fin_cases p <;> simp [sign, zsign]
  simp only [hz, mul_comm (D.parity j)] at h
  have h' := congrArg (fun f => zsign k (D.parity i * D.parity j) • f) h
  simp only [smul_smul, ProbeReservoir.zsign_mul_self', one_smul] at h'
  have hm := congrArg (P.step (true, i) false s hi).map h'.symm
  simp only [Functor.map_comp, Functor.map_smul] at hm
  exact hm

lemma q_correction (c : P.CrossCoeff Sc) (hc : c.IsInverse) :
    let x := outerDot P i j s hi hj Z
    let y := middleDot P i j s hi hj Z
    let z := innerDot P i j s hi hj Z
    zsign k (D.parity i * D.parity j) •
      (normalizedCoeff P i j s hi hj Z c * (qExpr Sc x y i j - qExpr Sc z y i j)) =
      (∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (x ^ (D.dn i j - 1 - a) * z ^ a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (x ^ (b - 1 - a) * y ^ d * z ^ a) := by
  exact RepeatedOuterQCorrection.qExpr_correction Sc _ _ _ _ i j
    (dots_xz P i j s hi hj Z) (dots_zy P i j s hi hj Z)
    (coeff_even P i j s hi hj Z c hc) (coeff_odd P i j s hi hj Z c hc)

end RepeatedOuterPre
end OddMath.QuiverHecke.SwappedAssembly
