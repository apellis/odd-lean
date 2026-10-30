/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctReservoirQPair
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterQCorrection
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.SectorDots

/-! Coordinates and normalized correction on the literal path Pᵢ Rⱼ Rᵢ. -/
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

namespace RepeatedOuterPost
open ProbeReservoir
private lemma reverse_conj {C : Type u} [Category C] [Preadditive C] [Linear k C]
    {V W : C} (K : V ≅ W) (x : End V) (y : End W) (ε : k)
    (hε : ε * ε = 1) (h : x ≫ K.hom = ε • (K.hom ≫ y)) :
    K.hom ≫ y ≫ K.inv = ε • x := by
  have he := congrArg (fun f => ε • (f ≫ K.inv)) h
  simp only [Linear.smul_comp, smul_smul, hε, one_smul, Category.assoc,
    Iso.hom_inv_id, Category.comp_id] at he
  exact he.symm

private lemma trans_map_conj {C C' : Type u} [Category C] [Category C']
    (F : C ⥤ C') {V W : C} {U : C'} (K : U ≅ F.obj V)
    (L : V ≅ W) (a : End W) :
    (K ≪≫ F.mapIso L).hom ≫ F.map a ≫ (K ≪≫ F.mapIso L).inv =
      K.hom ≫ F.map (L.hom ≫ a ≫ L.inv) ≫ K.inv := by
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc]

variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hj0 : StepValid (true, j) false s)
  (hi0 : StepValid (true, i) false (nextSector (true, j) false s))
  (Z : P.H (nextSector (true, i) false
    (nextSector (true, j) false (nextSector (true, i) true s))))

abbrev rest := P.distinctReservoirRest i j i s hi0 Z

abbrev obj := P.prObj i j s hj0 (rest P i j s hi0 Z)

def firstIso := P.mixedJ i j s hj0 (rest P i j s hi0 Z)

def comparison : obj P i j s hj0 hi0 Z ≅
    (P.step (true, j) false s hj0).obj
      (P.rpObj i i (nextSector (true, j) false s) hi0 Z) :=
  firstIso P i j s hj0 hi0 Z ≪≫
    (P.step (true, j) false s hj0).mapIso
      (P.mixedJ i i (nextSector (true, j) false s) hi0 Z)

/-- Literal outer probe-dot entry, not a conjugate used as a definition. -/
def outerDot : End (obj P i j s hj0 hi0 Z) :=
  P.T.dot i (P.muP_preE i s) ▷
    (P.step (true, j) false (nextSector (true, i) true s) hj0).obj
      ((P.step (true, i) false
        (nextSector (true, j) false (nextSector (true, i) true s)) hi0).obj Z)

/-- Literal innermost reservoir-dot entry, with both spectator maps. -/
def innerDot : End (obj P i j s hj0 hi0 Z) :=
  (P.step (true, i) true s trivial).map
    ((P.step (true, j) false (nextSector (true, i) true s) hj0).map
      (P.dotDiag i false
        (nextSector (true, j) false (nextSector (true, i) true s)) hi0 Z))

/-- The actual two-stage coefficient map, in its composite-isomorphism form. -/
def coefficientAlg :
    End (P.rpObj i i (nextSector (true, j) false s) hi0 Z) →ₐ[k]
      End (obj P i j s hj0 hi0 Z) :=
  (conjAlg (k := k) (comparison P i j s hj0 hi0 Z).symm).comp
    (functorAlg (k := k) (P.step (true, j) false s hj0) _)

lemma coefficientAlg_apply (a : End
    (P.rpObj i i (nextSector (true, j) false s) hi0 Z)) :
    coefficientAlg P i j s hj0 hi0 Z a =
      (firstIso P i j s hj0 hi0 Z).hom ≫
        (P.step (true, j) false s hj0).map
          ((P.mixedJ i i (nextSector (true, j) false s) hi0 Z).hom ≫ a ≫
            (P.mixedJ i i (nextSector (true, j) false s) hi0 Z).inv) ≫
        (firstIso P i j s hj0 hi0 Z).inv := by
  exact trans_map_conj _ _ _ _

lemma firstIso_conj_pre :
    (firstIso P i j s hj0 hi0 Z).hom ≫
      (P.step (true, j) false s hj0).map
        (P.prPreDot i i (nextSector (true, j) false s) hi0 Z) ≫
      (firstIso P i j s hj0 hi0 Z).inv =
    zsign k (D.parity i * D.parity j) • outerDot P i j s hj0 hi0 Z := by
  have h := P.prPreDot_comp_mixedJ_ne i j s hj0 (rest P i j s hi0 Z)
  exact reverse_conj (firstIso P i j s hj0 hi0 Z) _ _ _
    (ProbeReservoir.zsign_mul_self' _) h

lemma firstIso_conj_post :
    (firstIso P i j s hj0 hi0 Z).hom ≫
      (P.step (true, j) false s hj0).map
        (P.prPostDot i i (nextSector (true, j) false s) hi0 Z) ≫
      (firstIso P i j s hj0 hi0 Z).inv =
    zsign k (D.parity i * D.parity j) • innerDot P i j s hj0 hi0 Z := by
  have h := P.distinctReservoirLastDot_comp_firstIso i j i s hj0 hi0 Z
  have hp : D.parity i * D.parity j * D.parity i = D.parity i * D.parity j := by
    rw [mul_right_comm, SKM.zmod2_mul_self]
  rw [koszulSign_smul_eq_zsign (k := k), hp] at h
  exact reverse_conj (firstIso P i j s hj0 hi0 Z) _ _ _
    (ProbeReservoir.zsign_mul_self' _) h

/-- The image of the coefficient's probe variable is q ε times the outer dot. -/
lemma coefficientAlg_pre :
    coefficientAlg P i j s hj0 hi0 Z
      (P.rpPreDot i (nextSector (true, j) false s) hi0 Z) =
    (zsign k (D.parity i) * zsign k (D.parity i * D.parity j)) •
      outerDot P i j s hj0 hi0 Z := by
  have h := P.mixedJ_conj_rpPreDot i (nextSector (true, j) false s) hi0 Z
  rw [koszulSign_smul_eq_zsign (k := k), SKM.zmod2_mul_self] at h
  rw [coefficientAlg_apply, h, Functor.map_smul,
    Linear.smul_comp, Linear.comp_smul, firstIso_conj_pre, smul_smul]

/-- The image of the coefficient's reservoir variable is q ε times the inner dot. -/
lemma coefficientAlg_post :
    coefficientAlg P i j s hj0 hi0 Z
      (P.rpPostDot i (nextSector (true, j) false s) hi0 Z) =
    (zsign k (D.parity i) * zsign k (D.parity i * D.parity j)) •
      innerDot P i j s hj0 hi0 Z := by
  have h := P.mixedJ_conj_rpPostDot i (nextSector (true, j) false s) hi0 Z
  rw [koszulSign_smul_eq_zsign (k := k), SKM.zmod2_mul_self] at h
  rw [coefficientAlg_apply, h, Functor.map_smul,
    Linear.smul_comp, Linear.comp_smul, firstIso_conj_post, smul_smul]

/-- The map is applied to the supplied coefficient, not a replacement coefficient. -/
lemma coefficientAlg_coeff (c : P.CrossCoeff Sc) :
    coefficientAlg P i j s hj0 hi0 Z
      (c.a i (nextSector (true, j) false s) hi0 Z) =
    (comparison P i j s hj0 hi0 Z).hom ≫
      (P.step (true, j) false s hj0).map
        (c.a i (nextSector (true, j) false s) hi0 Z) ≫
      (comparison P i j s hj0 hi0 Z).inv := rfl

private lemma alg_even {R T : Type u} [Ring R] [Ring T] [Algebra k R] [Algebra k T]
    (φ : R →ₐ[k] T) (a x₀ z₀ : R) (x z : T)
    (hx : φ x₀ = x) (hz : φ z₀ = z) (ha : a * (z₀ - x₀) = 1) :
    (-1 : k) • φ a * (x - z) = 1 := by
  have he := congrArg φ ha
  simp only [map_mul, map_sub, map_one, hx, hz] at he
  rw [neg_one_smul, neg_mul, ← mul_neg, neg_sub]
  exact he

private lemma alg_odd {R T : Type u} [Ring R] [Ring T] [Algebra k R] [Algebra k T]
    (φ : R →ₐ[k] T) (a x₀ z₀ : R) (x z : T) (ε : k) (hε : ε * ε = 1)
    (hx : φ x₀ = ε • x) (hz : φ z₀ = ε • z)
    (ha : a * (x₀ * x₀ - z₀ * z₀) = x₀ - z₀) :
    (ε • φ a) * (x * x - z * z) = x - z := by
  have he := congrArg φ ha
  simp only [map_mul, map_sub, hx, hz, smul_mul_assoc, mul_smul_comm,
    smul_smul, hε, one_smul] at he
  have he' := congrArg (fun a => ε • a) he
  simpa only [smul_sub, smul_smul, hε, one_smul, smul_mul_assoc] using he'

def normalizedCoeff (c : P.CrossCoeff Sc) : End (obj P i j s hj0 hi0 Z) :=
  (-zsign k (D.parity i * D.parity j)) •
    coefficientAlg P i j s hj0 hi0 Z (c.a i (nextSector (true, j) false s) hi0 Z)

def middleDot : End (obj P i j s hj0 hi0 Z) :=
  P.prPostDot i j s hj0 (rest P i j s hi0 Z)

lemma coeff_even (c : P.CrossCoeff Sc) (hc : c.IsInverse) (hi : D.parity i = 0) :
    normalizedCoeff P i j s hj0 hi0 Z c *
      (outerDot P i j s hj0 hi0 Z - innerDot P i j s hj0 hi0 Z) = 1 := by
  have hx := coefficientAlg_pre P i j s hj0 hi0 Z
  have hz := coefficientAlg_post P i j s hj0 hi0 Z
  rw [hi, zero_mul, zsign_zero, one_mul, one_smul] at hx hz
  have he := alg_even (coefficientAlg P i j s hj0 hi0 Z)
    (c.a i (nextSector (true, j) false s) hi0 Z) _ _ _ _ hx hz
    (hc.even i hi (nextSector (true, j) false s) hi0 Z).2
  change ((-zsign k (D.parity i * D.parity j)) • _) * _ = 1
  rw [hi, zero_mul, zsign_zero]
  exact he

lemma coeff_odd (c : P.CrossCoeff Sc) (hc : c.IsInverse) (hi : D.parity i = 1) :
    normalizedCoeff P i j s hj0 hi0 Z c *
      (outerDot P i j s hj0 hi0 Z * outerDot P i j s hj0 hi0 Z -
        innerDot P i j s hj0 hi0 Z * innerDot P i j s hj0 hi0 Z) =
      outerDot P i j s hj0 hi0 Z - innerDot P i j s hj0 hi0 Z := by
  have hx := coefficientAlg_pre P i j s hj0 hi0 Z
  have hz := coefficientAlg_post P i j s hj0 hi0 Z
  have hsign : zsign k (1 : ZMod 2) = -1 := rfl
  rw [hi, hsign, neg_one_mul] at hx hz
  have hε : (-zsign k (D.parity i * D.parity j)) *
      (-zsign k (D.parity i * D.parity j)) = 1 := by
    rw [neg_mul_neg, ProbeReservoir.zsign_mul_self']
  apply alg_odd (coefficientAlg P i j s hj0 hi0 Z)
    (c.a i (nextSector (true, j) false s) hi0 Z)
    (P.rpPreDot i (nextSector (true, j) false s) hi0 Z)
    (P.rpPostDot i (nextSector (true, j) false s) hi0 Z) _ _ _ hε
  · simpa only [hi] using hx
  · simpa only [hi] using hz
  · exact (hc.odd i hi (nextSector (true, j) false s) hi0 Z).2

lemma dots_xz :
    outerDot P i j s hj0 hi0 Z * innerDot P i j s hj0 hi0 Z =
      zsign k (D.parity i) •
        (innerDot P i j s hj0 hi0 Z * outerDot P i j s hj0 hi0 Z) := by
  have h := (P.distinctReservoir_dots_probe i j i s hj0 hi0 Z).2
  rw [SKM.zmod2_mul_self] at h
  exact h

lemma dots_zy :
    innerDot P i j s hj0 hi0 Z * middleDot P i j s hj0 hi0 Z =
      zsign k (D.parity i * D.parity j) •
        (middleDot P i j s hj0 hi0 Z * innerDot P i j s hj0 hi0 Z) := by
  have h := P.distinctReservoir_dots_reservoir i j i s hj0 hi0 Z
  have h' := congrArg (fun f => zsign k (D.parity i * D.parity j) • f) h
  simp only [smul_smul, ProbeReservoir.zsign_mul_self', one_smul] at h'
  exact h'.symm

lemma q_correction (c : P.CrossCoeff Sc) (hc : c.IsInverse) :
    let x := outerDot P i j s hj0 hi0 Z
    let y := middleDot P i j s hj0 hi0 Z
    let z := innerDot P i j s hj0 hi0 Z
    zsign k (D.parity i * D.parity j) •
      (normalizedCoeff P i j s hj0 hi0 Z c * (qExpr Sc x y i j - qExpr Sc z y i j)) =
      (∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (x ^ (D.dn i j - 1 - a) * z ^ a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (x ^ (b - 1 - a) * y ^ d * z ^ a) := by
  exact RepeatedOuterQCorrection.qExpr_correction Sc _ _ _ _ i j
    (dots_xz P i j s hj0 hi0 Z) (dots_zy P i j s hj0 hi0 Z)
    (coeff_even P i j s hj0 hi0 Z c hc) (coeff_odd P i j s hj0 hi0 Z c hc)


end RepeatedOuterPost
end OddMath.QuiverHecke.SwappedAssembly
