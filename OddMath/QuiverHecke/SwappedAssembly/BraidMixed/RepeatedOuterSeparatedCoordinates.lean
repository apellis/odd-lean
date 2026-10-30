/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterWeightedSquare
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.SectorDots

/-! # Separated repeated-outer correction coordinates

The native dots on `Pᵢ Pⱼ Rᵢ` satisfy the two signed correction sums with the
coefficient normalized by `-(-1)^(pᵢpⱼ)`. Both parity-dependent denominator
identities follow from the supplied coefficient inverse identities, transported
through actual mixed isomorphisms. This supplies the coordinate calculation for
the remaining diagonal component of `CrossBraid`, not its matrix identification.
-/
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
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hR : StepValid (true, i) false s)
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

def separatedOuterAlg :=
  (conjAlg (k := k) (P.distinctProbeFirstIso i j i s hR Z).symm).comp
    (conjAlg (k := k)
      (P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj Z)).symm)

private lemma reverse_conj {C : Type u} [Category C] [Preadditive C] [Linear k C]
    {V W : C} (K : V ≅ W) (x : End V) (y : End W) (ε : k)
    (hε : ε * ε = 1) (h : x ≫ K.hom = ε • (K.hom ≫ y)) :
    K.hom ≫ y ≫ K.inv = ε • x := by
  have he := congrArg (fun f => ε • (f ≫ K.inv)) h
  simp only [Linear.smul_comp, smul_smul, hε, one_smul, Category.assoc,
    Iso.hom_inv_id, Category.comp_id] at he
  exact he.symm

lemma separatedOuterAlg_pre :
    P.separatedOuterAlg i j s hR Z
      (P.rpPreDot i s hR ((P.step (true, j) true _ trivial).obj Z)) =
    (zsign k (D.parity i) * zsign k (D.parity i * D.parity j)) •
      P.distinctProbeOuterDot i j i s hR Z := by
  let K := P.distinctProbeFirstIso i j i s hR Z
  let φ := conjAlg (k := k) K.symm
  have hh := P.mixedJ_conj_rpPreDot i s hR ((P.step (true, j) true _ trivial).obj Z)
  rw [koszulSign_smul_eq_zsign (k := k), SKM.zmod2_mul_self] at hh
  have hk := P.distinctProbeOuterDot_comp_firstIso i j i s hR Z
  have hp : D.parity i * D.parity j * D.parity i = D.parity i * D.parity j := by
    rw [mul_right_comm, SKM.zmod2_mul_self]
  rw [hp] at hk
  have hr := reverse_conj K _ _ (zsign k (D.parity i * D.parity j))
    (zsign_mul_self' _) hk
  have he := congrArg φ hh
  change φ _ = _ at he
  rw [map_smul] at he
  change φ (P.prPreDot i i s hR ((P.step (true, j) true _ trivial).obj Z)) = _ at hr
  exact he.trans ((congrArg (fun a => zsign k (D.parity i) • a) hr).trans
    (smul_smul _ _ _))

lemma separatedOuterAlg_post :
    P.separatedOuterAlg i j s hR Z
      (P.rpPostDot i s hR ((P.step (true, j) true _ trivial).obj Z)) =
    (zsign k (D.parity i) * zsign k (D.parity i * D.parity j)) •
      P.distinctProbeSpectatorDot i j i s hR Z := by
  let K := P.distinctProbeFirstIso i j i s hR Z
  let φ := conjAlg (k := k) K.symm
  have hh := P.mixedJ_conj_rpPostDot i s hR ((P.step (true, j) true _ trivial).obj Z)
  rw [koszulSign_smul_eq_zsign (k := k), SKM.zmod2_mul_self] at hh
  have hr := P.distinctProbeFirstIso_conj_prPostDot i j i s hR Z
  rw [mul_comm (D.parity j)] at hr
  have he := congrArg φ hh
  change φ _ = _ at he
  rw [map_smul] at he
  change φ (P.prPostDot i i s hR ((P.step (true, j) true _ trivial).obj Z)) = _ at hr
  exact he.trans ((congrArg (fun a => zsign k (D.parity i) • a) hr).trans
    (smul_smul _ _ _))

private lemma conj_chain {C : Type u} [Category C] {A B D : C}
    (K : A ≅ B) (H : B ≅ D) (a : End D) :
    K.hom ≫ (H.hom ≫ a ≫ H.inv) ≫ K.inv =
      K.hom ≫ H.hom ≫ a ≫ H.inv ≫ K.inv := by
  simp only [Category.assoc]

lemma separatedOuterAlg_coeff (c : P.CrossCoeff Sc) :
    P.separatedOuterAlg i j s hR Z
      (c.a i s hR ((P.step (true, j) true _ trivial).obj Z)) =
    P.repeatedOuterMixedSeparatedCoeff i j s hR Z c := by
  exact conj_chain _ _ _
def separatedOuterCoeff (c : P.CrossCoeff Sc) :=
  (-zsign k (D.parity i * D.parity j)) •
    P.separatedOuterAlg i j s hR Z
      (c.a i s hR ((P.step (true, j) true _ trivial).obj Z))

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

lemma separatedOuterCoeff_even (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (hi : D.parity i = 0) :
    P.separatedOuterCoeff i j s hR Z c *
      (P.distinctProbeOuterDot i j i s hR Z -
        P.distinctProbeSpectatorDot i j i s hR Z) = 1 := by
  have hx := P.separatedOuterAlg_pre i j s hR Z
  have hz := P.separatedOuterAlg_post i j s hR Z
  rw [hi, zero_mul, zsign_zero, one_mul, one_smul] at hx hz
  have he := alg_even (P.separatedOuterAlg i j s hR Z)
    (c.a i s hR ((P.step (true, j) true _ trivial).obj Z)) _ _ _ _ hx hz
    (hc.even i hi s hR ((P.step (true, j) true _ trivial).obj Z)).2
  change ((-zsign k (D.parity i * D.parity j)) • _) * _ = 1
  rw [hi, zero_mul, zsign_zero]
  exact he

lemma separatedOuterCoeff_odd (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (hi : D.parity i = 1) :
    P.separatedOuterCoeff i j s hR Z c *
      (P.distinctProbeOuterDot i j i s hR Z * P.distinctProbeOuterDot i j i s hR Z -
        P.distinctProbeSpectatorDot i j i s hR Z * P.distinctProbeSpectatorDot i j i s hR Z) =
      P.distinctProbeOuterDot i j i s hR Z - P.distinctProbeSpectatorDot i j i s hR Z := by
  have hx := P.separatedOuterAlg_pre i j s hR Z
  have hz := P.separatedOuterAlg_post i j s hR Z
  have hsign : zsign k (1 : ZMod 2) = -1 := rfl
  rw [hi, hsign, neg_one_mul] at hx hz
  have hε : (-zsign k (D.parity i * D.parity j)) *
      (-zsign k (D.parity i * D.parity j)) = 1 := by
    rw [neg_mul_neg, zsign_mul_self']
  apply alg_odd (P.separatedOuterAlg i j s hR Z)
    (c.a i s hR ((P.step (true, j) true _ trivial).obj Z))
    (P.rpPreDot i s hR ((P.step (true, j) true _ trivial).obj Z))
    (P.rpPostDot i s hR ((P.step (true, j) true _ trivial).obj Z))
    _ _ _ hε
  · simpa only [hi] using hx
  · simpa only [hi] using hz
  · exact (hc.odd i hi s hR ((P.step (true, j) true _ trivial).obj Z)).2

lemma separatedOuterDots_xz :
    P.distinctProbeOuterDot i j i s hR Z * P.distinctProbeSpectatorDot i j i s hR Z =
      zsign k (D.parity i) •
        (P.distinctProbeSpectatorDot i j i s hR Z * P.distinctProbeOuterDot i j i s hR Z) := by
  have he := TwoSupercategory.super_interchange (R := k)
    (P.T.dot_mem i (P.muP_preE i s))
    ((P.prPostDot_supernatural j i (nextSector (true, i) true s) hR).mem Z)
  rw [koszulSign_smul_eq_zsign (k := k), SKM.zmod2_mul_self] at he
  have he' := congrArg (fun a => zsign k (D.parity i) • a) he
  rw [smul_smul, zsign_mul_self', one_smul] at he'
  exact he'.symm

private lemma map_signed_comm {C C' : Type u} [Category C] [Preadditive C]
    [Linear k C] [Category C'] [Preadditive C'] [Linear k C']
    (F : C ⥤ C') [F.Linear k] {V : C} (x y : End V) (ε : k)
    (h : x ≫ y = ε • (y ≫ x)) :
    F.map x ≫ F.map y = ε • (F.map y ≫ F.map x) := by
  simpa only [Functor.map_comp, Functor.map_smul] using congrArg F.map h

lemma separatedOuterDots_zy :
    P.distinctProbeSpectatorDot i j i s hR Z * P.distinctProbeInnerDot i j i s hR Z =
      zsign k (D.parity i * D.parity j) •
        (P.distinctProbeInnerDot i j i s hR Z * P.distinctProbeSpectatorDot i j i s hR Z) := by
  let t := nextSector (true, j) true (nextSector (true, i) true s)
  have hd := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W i t.1
    (P.muP t) (P.muM_postE i hR) 1).mem Z
  simp only [Nat.cast_one, one_mul, pow_one] at hd
  have he := TwoSupercategory.super_interchange (R := k)
    (P.T.dot_mem j (P.muP_preE j (nextSector (true, i) true s))) hd
  rw [koszulSign_smul_eq_zsign (k := k), mul_comm (D.parity j)] at he
  have : (P.step (true, i) true s trivial).Linear k := P.step_linear _ _ _ _
  exact map_signed_comm (P.step (true, i) true s trivial)
    (P.prPreDot j i (nextSector (true, i) true s) hR Z)
    (P.prPostDot j i (nextSector (true, i) true s) hR Z) _ he

lemma separatedOuter_qExpr_correction (c : P.CrossCoeff Sc) (hc : c.IsInverse) :
    let x := P.distinctProbeOuterDot i j i s hR Z
    let y := P.distinctProbeInnerDot i j i s hR Z
    let z := P.distinctProbeSpectatorDot i j i s hR Z
    let a := P.separatedOuterCoeff i j s hR Z c
    zsign k (D.parity i * D.parity j) •
        (a * (qExpr Sc x y i j - qExpr Sc z y i j)) =
      (∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (x ^ (D.dn i j - 1 - a) * z ^ a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ c ∈ Finset.Ioo 0 (D.dn j i),
        ∑ a ∈ Finset.range b,
          (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b c) •
            (x ^ (b - 1 - a) * y ^ c * z ^ a) := by
  exact RepeatedOuterQCorrection.qExpr_correction Sc _ _ _ _ i j
    (P.separatedOuterDots_xz i j s hR Z) (P.separatedOuterDots_zy i j s hR Z)
    (P.separatedOuterCoeff_even i j s hR Z c hc)
    (P.separatedOuterCoeff_odd i j s hR Z c hc)
end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
