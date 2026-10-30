/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidEq.Algebra
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPureProbeMatrix
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ReverseReservoirSector

/-! Reverse Q commutator, obtained by reversing the nil-Hecke slide and
reflecting the supported correction sums. The literal RPR diagonal is derived below. -/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory

universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {D : Datum I X}

namespace ProbeReservoir

variable {C : Type*} [Category C] [Preadditive C] [Linear k C]

/-- The reverse Q commutator has the same ordered correction as
`comp_qExpr_sub`. The extra dot relations permit reflection of that correction.
No reverse slide, crossing braid, or nilpotence is assumed. -/
theorem qExpr_comp_sub_reverse (Sc : Scalars D k) (i j : I)
    {A : C} (ψ x₁ x₂ y : End A)
    (h₁ : x₁ ≫ ψ - zsign k (D.parity i * D.parity i) • (ψ ≫ x₂) = 𝟙 A)
    (h₂ : ψ ≫ y = zsign k (D.parity i * D.parity j) • (y ≫ ψ))
    (hy₁ : y ≫ x₁ = zsign k (D.parity i * D.parity j) • (x₁ ≫ y))
    (hy₂ : y ≫ x₂ = zsign k (D.parity i * D.parity j) • (x₂ ≫ y))
    (hx : x₂ ≫ x₁ = zsign k (D.parity i * D.parity i) • (x₁ ≫ x₂)) :
    qExpr Sc x₁ y i j ≫ ψ - ψ ≫ qExpr Sc x₂ y i j =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (zsign k (D.parity i * D.parity j) • x₂) a ≫
            compPow (zsign k (D.parity i * D.parity j) • x₁) (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ c ∈ Finset.Ioo 0 (D.dn j i),
        ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b c) •
          (compPow (zsign k (D.parity i * D.parity j) • x₂) a ≫
            compPow (zsign k (D.parity i * D.parity j) • y) c ≫
            compPow (zsign k (D.parity i * D.parity j) • x₁) (b - 1 - a)) := by
  classical
  let q : k := zsign k (D.parity i * D.parity i)
  let ε : k := zsign k (D.parity i * D.parity j)
  have hqq : q * q = 1 := zsign_mul_self' (k := k) (D.parity i * D.parity i)
  have hself : D.parity i * D.parity i = D.parity i := by
    generalize D.parity i = p
    fin_cases p <;> rfl
  have hq : q = zsign k (D.parity i) := by simp only [q, hself]
  have hslide : ((-q) • ψ) ≫ x₂ - q • (x₁ ≫ ((-q) • ψ)) = 𝟙 A := by
    calc
      ((-q) • ψ) ≫ x₂ - q • (x₁ ≫ ((-q) • ψ)) =
          x₁ ≫ ψ - q • (ψ ≫ x₂) := by
        rw [Linear.smul_comp, Linear.comp_smul]
        rw [smul_smul, mul_neg, hqq]
        simp only [neg_smul, one_smul]
        abel
      _ = 𝟙 A := h₁
  have hmiddle : ((-q) • ψ) ≫ y = ε • (y ≫ ((-q) • ψ)) := by
    rw [Linear.smul_comp, h₂, Linear.comp_smul]
    simp only [smul_smul]
    congr 1
    exact mul_comm _ _
  have hf := comp_qExpr_sub Sc i j ((-q) • ψ) x₂ x₁ y hslide hmiddle hy₁
  have hf' := congrArg (fun f : End A => q • f) hf
  have hl : q • (((-q) • ψ) ≫ qExpr Sc x₂ y i j -
      qExpr Sc x₁ y i j ≫ ((-q) • ψ)) =
      qExpr Sc x₁ y i j ≫ ψ - ψ ≫ qExpr Sc x₂ y i j := by
    rw [Linear.smul_comp, Linear.comp_smul]
    simp only [smul_sub, smul_smul]
    rw [mul_neg, hqq]
    simp only [neg_smul, one_smul]
    abel
  rw [hl] at hf'
  rw [hf', smul_add]
  -- Scale both dots before applying the public ring-valued reflection lemma.
  have hscaled (a b : End A) (r : k) (h : a * b = r • (b * a)) :
      (ε • a) * (ε • b) = r • ((ε • b) * (ε • a)) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [h]
    simp only [smul_smul]
    congr 1
    ring
  have hxz : (ε • x₁) * (ε • x₂) =
      zsign k (D.parity i) • ((ε • x₂) * (ε • x₁)) := by
    apply hscaled
    simpa only [End.mul_def, hself] using hx
  have hxy : (ε • x₁) * (ε • y) =
      zsign k (D.parity i * D.parity j) • ((ε • y) * (ε • x₁)) := by
    apply hscaled
    exact hy₁
  have hzy : (ε • x₂) * (ε • y) =
      zsign k (D.parity i * D.parity j) • ((ε • y) * (ε • x₂)) := by
    apply hscaled
    exact hy₂
  simp only [compPow_eq_pow, ← End.mul_def]
  apply congrArg₂ (· + ·)
  · simpa only [hq, ε, pow_zero, mul_one] using
      pureCorrection_reflect_sum (k := k) (ε • x₁) (ε • y) (ε • x₂)
        (D.parity i) (D.parity j) hxz hxy hzy (D.dn i j) 0
        (RepeatedOuterQCorrection.outer_degree_even i j)
        (fun _ => ⟨0, rfl⟩) (Sc.t i j : k)
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hs : Sc.s i j b c = 0
    · simp only [hs, mul_zero, zero_smul, Finset.sum_const_zero, smul_zero]
    · simpa only [hq, ε] using
        pureCorrection_reflect_sum (k := k) (ε • x₁) (ε • y) (ε • x₂)
          (D.parity i) (D.parity j) hxz hxy hzy b c
          (RepeatedOuterQCorrection.supported_outer_even Sc i j b c hs)
          (RepeatedOuterQCorrection.supported_inner_even Sc i j b c hs) (Sc.s i j b c)


variable {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] {Sc : Scalars D k}
variable (P : ProbeReservoir k B D Sc) (ν : X) (i j : I) (s : Sector I)
  (hv : StepValid (true, i) false s)
  (hw : StepValid (true, i) false (nextSector (true, i) false s))
  (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (Z : P.H (nextSector (true, i) false (nextSector (true, i) false (nextSector (true, j) true s))))

/-- The two original RPR diagonal sums have unique supported routes. -/
theorem middleProbe_routes (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i j i ν
      (reservoirPairMiddle ν j i s hv hw) (reservoirPairMiddle ν j i s hv hw) Z =
      (((P.reservoirPairFirstIso j i s hv hw Z).inv ≫
        P.mixedQ j i s hv (P.reservoirPairRest j i s hw Z)) ≫
        P.reservoirPairCross j i s hv hw Z) ≫ (P.reservoirPairFirstIso j i s hv hw Z).hom ∧
    braidRight (P.swappedGens c L) i j i ν
      (reservoirPairMiddle ν j i s hv hw) (reservoirPairMiddle ν j i s hv hw) Z =
      ((P.step (true, i) false s hv).map (P.mixedJ j i (nextSector (true, i) false s) hw Z).hom ≫
        P.postCrossSame i s hv hw ((P.step (true, j) true _ trivial).obj Z)) ≫
      (P.step (true, i) false s hv).map
        ((P.mixedJ j i (nextSector (true, i) false s) hw Z).inv ≫
          P.mixedQ j i (nextSector (true, i) false s) hw Z) := by
  classical
  let : Subsingleton (SPath (wd D ν [up j, up i, up i]) s
      (nextSector (true, i) false (nextSector (true, i) false (nextSector (true, j) true s)))) :=
    ⟨fun p q => (reservoirPairSource_unique ν j i s hv hw hij.symm p).trans
      (reservoirPairSource_unique ν j i s hv hw hij.symm q).symm⟩
  let : Subsingleton (SPath (wd D ν [up i, up j, up i]) s
      (nextSector (true, i) false (nextSector (true, i) false (nextSector (true, j) true s)))) :=
    ⟨fun p q => (reservoirPairMiddle_unique ν j i s hv hw hij.symm p).trans
      (reservoirPairMiddle_unique ν j i s hv hw hij.symm q).symm⟩
  let : Subsingleton (SPath (wd D ν [up i, up i, up j]) s
      (nextSector (true, i) false (nextSector (true, i) false (nextSector (true, j) true s)))) :=
    ⟨fun p q => (reservoirPairTarget_unique ν j i s hv hw hij.symm p).trans
      (reservoirPairTarget_unique ν j i s hv hw hij.symm q).symm⟩
  let := Fintype.ofFinite (SPath (wd D ν [up j, up i, up i]) s
    (nextSector (true, i) false (nextSector (true, i) false (nextSector (true, j) true s))))
  let := Fintype.ofFinite (SPath (wd D ν [up i, up j, up i]) s
    (nextSector (true, i) false (nextSector (true, i) false (nextSector (true, j) true s))))
  let := Fintype.ofFinite (SPath (wd D ν [up i, up i, up j]) s
    (nextSector (true, i) false (nextSector (true, i) false (nextSector (true, j) true s))))
  constructor
  · unfold braidLeft
    rw [Fintype.sum_subsingleton _ (reservoirPairSource (D := D) ν j i s hv hw),
      Fintype.sum_subsingleton _ (reservoirPairSource (D := D) ν j i s hv hw)]
    rw [P.reverseReservoirPair_left_mixed ν j i s hv hw c L Z hij.symm,
      P.reservoirPair_right_same, P.reservoirPair_left_mixed ν j i s hv hw c L Z hij.symm]
    rfl
  · unfold braidRight
    rw [Fintype.sum_subsingleton _ (reservoirPairTarget (D := D) ν j i s hv hw),
      Fintype.sum_subsingleton _ (reservoirPairTarget (D := D) ν j i s hv hw)]
    rw [P.reservoirPair_right_mixed ν j i s hv hw c L Z hij.symm,
      P.reservoirPair_left_same, P.reverseReservoirPair_right_mixed ν j i s hv hw c L Z hij.symm]

private lemma middleProbe_conjugate {C : Type u} [Category C] [Preadditive C]
    {A B W : C} (J : A ≅ B) (K : B ≅ W) (S R : End A) (T : End W) (Q : End B)
    (h : S ≫ J.hom ≫ K.hom = J.hom ≫ K.hom ≫ T) :
    J.hom ≫ ((((J.inv ≫ R) ≫ S) ≫ J.hom) -
      ((K.hom ≫ T) ≫ (K.inv ≫ Q))) ≫ J.inv =
      R ≫ S - S ≫ (J.hom ≫ Q ≫ J.inv) := by
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have hh := congrArg (fun f => f ≫ K.inv ≫ Q ≫ J.inv) h
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [hh]

/-- The literal RPR diagonal difference is the reverse Q commutator. -/
theorem middleProbe_commutator (hij : i ≠ j) :
    (P.reservoirPairFirstIso j i s hv hw Z).hom ≫
      (braidLeft (P.swappedGens c L) i j i ν
        (reservoirPairMiddle ν j i s hv hw) (reservoirPairMiddle ν j i s hv hw) Z -
       braidRight (P.swappedGens c L) i j i ν
        (reservoirPairMiddle ν j i s hv hw) (reservoirPairMiddle ν j i s hv hw) Z) ≫
      (P.reservoirPairFirstIso j i s hv hw Z).inv =
      qExpr Sc (P.prPostDot j i s hv (P.reservoirPairRest j i s hw Z))
        (P.prPreDot j i s hv (P.reservoirPairRest j i s hw Z)) i j ≫ P.reservoirPairCross j i s hv hw Z -
      P.reservoirPairCross j i s hv hw Z ≫ qExpr Sc (P.reservoirPairLastDot j i s hv hw Z)
        (P.prPreDot j i s hv (P.reservoirPairRest j i s hw Z)) i j := by
  rw [(P.middleProbe_routes ν i j s hv hw c L Z hij).1,
    (P.middleProbe_routes ν i j s hv hw c L Z hij).2]
  simp only [Functor.map_comp]
  erw [middleProbe_conjugate (P.reservoirPairFirstIso j i s hv hw Z) ((P.step (true, i) false s hv).mapIso
    (P.mixedJ j i (nextSector (true, i) false s) hw Z)) _ _ _ _
    (P.postCrossSame_mixedJ_pair_ne j i s hv hw Z), P.reservoirPairFirstIso_conj_mixedQ]
  have swap (a : End (P.reservoirPairObj j i s hv hw Z))
      (h : a ≫ P.prPreDot j i s hv (P.reservoirPairRest j i s hw Z) =
        koszulSign (D.parity j) (D.parity i) •
          (P.prPreDot j i s hv (P.reservoirPairRest j i s hw Z) ≫ a)) :
      qExpr Sc (P.prPreDot j i s hv (P.reservoirPairRest j i s hw Z)) a j i =
        qExpr Sc a (P.prPreDot j i s hv (P.reservoirPairRest j i s hw Z)) i j := by
    apply qExpr_swap Sc _ _ j i (zsign k (D.parity j * D.parity i))
    · simpa only [koszulSign_smul_eq_zsign (k := k), End.mul_def] using h
    · exact fun n hn => zsign_pow_of_mul_eq_zero _ _ n hn
  change qExpr Sc _ _ j i ≫ _ - _ ≫ qExpr Sc _ _ j i = _
  rw [swap _ (P.reservoirPairFirstDot_comp_probeDot j i s hv hw Z),
    swap _ (P.reservoirPairLastDot_comp_prPreDot j i s hv hw Z)]
  rfl

/-- Literal outer reservoir dot on the RPR path. -/
theorem middleProbe_dotX :
    dotEntry (P.swappedGens c L) ν [] i [up j, up i] (reservoirPairMiddle ν j i s hv hw) Z =
      homContentPostDot P.T.obj P.W i s.1 (P.muP s) (P.muM_postE i hv)
        ((P.step (true, j) true (nextSector (true, i) false s) trivial).obj
          (P.reservoirPairRest j i s hw Z)) := by
  apply eq_of_heq
  unfold dotEntry
  refine (heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [] (SKM.Shape.dot i) [up j, up i]) (.nil s)
    (.cons _ false _ hv (.nil _)) (.cons _ false _ hv (.nil _))
    (SPath.two true false trivial hw rfl) _ _ rfl rfl Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (P.dotImage_reservoir i (SKM.wt D ν [up j, up i]) s hv hv _)

/-- Literal middle probe dot on the RPR path. -/
theorem middleProbe_dotY :
    dotEntry (P.swappedGens c L) ν [up i] j [up i] (reservoirPairMiddle ν j i s hv hw) Z =
      (P.step (true, i) false s hv).map
        (P.T.dot j (P.muP_preE j s) ▷ P.reservoirPairRest j i s hw Z) := by
  apply eq_of_heq
  unfold dotEntry
  refine (heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [up i] (SKM.Shape.dot j) [up i]) (.cons _ false s hv (.nil _))
    (.cons _ true _ trivial (.nil _)) (.cons _ true _ trivial (.nil _))
    (.cons _ false _ hw (.nil _)) _ _ rfl rfl Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (congrArg (P.step (true, i) false s hv).map
    (P.dotImage_probe j (SKM.wt D ν [up i]) (nextSector (true, i) false s) trivial trivial
      (P.reservoirPairRest j i s hw Z)))

/-- Literal inner reservoir dot on the RPR path. -/
theorem middleProbe_dotZ :
    dotEntry (P.swappedGens c L) ν [up i, up j] i [] (reservoirPairMiddle ν j i s hv hw) Z =
      (P.step (true, i) false s hv).map (P.prPostDot j i (nextSector (true, i) false s) hw Z) := by
  apply eq_of_heq
  unfold dotEntry
  refine (heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [up i, up j] (SKM.Shape.dot i) []) (SPath.two false true hv trivial rfl)
    (.cons _ false _ hw (.nil _)) (.cons _ false _ hw (.nil _))
    (.nil _) _ _ rfl rfl Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (congrArg (fun f => (P.step (true, i) false s hv).map
    ((P.step (true, j) true (nextSector (true, i) false s) trivial).map f))
    (P.dotImage_reservoir i ν (nextSector (true, j) true (nextSector (true, i) false s)) hw hw Z))

/-- The three literal dot coordinates, with their actual colour signs. -/
theorem middleProbe_dot_coordinates :
    let φ := conjAlg (k := k) (P.reservoirPairFirstIso j i s hv hw Z).symm
    let ε := zsign k (D.parity i * D.parity j)
    φ (dotEntry (P.swappedGens c L) ν [] i [up j, up i] (reservoirPairMiddle ν j i s hv hw) Z) =
      ε • P.prPostDot j i s hv (P.reservoirPairRest j i s hw Z) ∧
    φ (dotEntry (P.swappedGens c L) ν [up i] j [up i] (reservoirPairMiddle ν j i s hv hw) Z) =
      ε • P.prPreDot j i s hv (P.reservoirPairRest j i s hw Z) ∧
    φ (dotEntry (P.swappedGens c L) ν [up i, up j] i [] (reservoirPairMiddle ν j i s hv hw) Z) =
      ε • P.reservoirPairLastDot j i s hv hw Z := by
  dsimp only
  rw [P.middleProbe_dotX, P.middleProbe_dotY, P.middleProbe_dotZ]
  simp only [conjAlg_apply, Iso.symm_inv, Iso.symm_hom]
  constructor
  · have h := congrArg (fun f => zsign k (D.parity j * D.parity i) • f)
      (P.prPostDot_comp_mixedJ_ne j i s hv (P.reservoirPairRest j i s hw Z))
    simp only [smul_smul, zsign_mul_self', one_smul] at h
    have hh := congrArg (fun f => f ≫ (P.reservoirPairFirstIso j i s hv hw Z).inv) h
    simp only [reservoirPairFirstIso, Linear.smul_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id] at hh
    simpa only [reservoirPairFirstIso, mul_comm (D.parity j) (D.parity i)] using hh.symm
  constructor
  · have h := congrArg (fun f => zsign k (D.parity j * D.parity i) • f)
      (P.prPreDot_comp_mixedJ_ne j i s hv (P.reservoirPairRest j i s hw Z))
    simp only [smul_smul, zsign_mul_self', one_smul] at h
    have hh := congrArg (fun f => f ≫ (P.reservoirPairFirstIso j i s hv hw Z).inv) h
    simp only [reservoirPairFirstIso, Linear.smul_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id] at hh
    simpa only [reservoirPairFirstIso, mul_comm (D.parity j) (D.parity i)] using hh.symm
  · have h := P.reservoirPairFirstIso_conj_map_prPostDot j i s hv hw Z
    rw [koszulSign_smul_eq_zsign (k := k), mul_assoc, SKM.zmod2_mul_self] at h
    simpa only [mul_comm (D.parity j) (D.parity i)] using h

/-- The complete signed correction for the literal RPR diagonal. -/
theorem middleProbe_braidEq_diag (hij : i ≠ j) :
    let p := reservoirPairMiddle (D := D) ν j i s hv hw
    braidLeft (P.swappedGens c L) i j i ν p p Z -
      braidRight (P.swappedGens c L) i j i ν p p Z =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p Z) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p Z) (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p Z) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [up i] j [up i] p Z) d ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p Z) (b - 1 - a)) := by
  classical
  dsimp only
  let J := P.reservoirPairFirstIso j i s hv hw Z
  let φ := conjAlg (k := k) J.symm
  let x := P.prPostDot j i s hv (P.reservoirPairRest j i s hw Z)
  let y := P.prPreDot j i s hv (P.reservoirPairRest j i s hw Z)
  let z := P.reservoirPairLastDot j i s hv hw Z
  let ψ := P.reservoirPairCross j i s hv hw Z
  let ε := zsign k (D.parity i * D.parity j)
  have hinj : Function.Injective φ := by
    intro a b hab
    apply (cancel_epi J.hom).1
    apply (cancel_mono J.inv).1
    change J.hom ≫ a ≫ J.inv = J.hom ≫ b ≫ J.inv at hab
    simpa only [Category.assoc] using hab
  apply hinj
  have hc := P.middleProbe_dot_coordinates ν i j s hv hw c L Z
  have hb := P.middleProbe_commutator ν i j s hv hw c L Z hij
  change φ _ = _ at hb
  rw [hb]
  have h₁ : x ≫ ψ - zsign k (D.parity i * D.parity i) • (ψ ≫ z) = 𝟙 _ := by
    simpa only [koszulSign_smul_eq_zsign (k := k)] using
      (P.reservoirPairCross_slides j i s hv hw Z).1
  have h₂ : ψ ≫ y = ε • (y ≫ ψ) := by
    simpa only [koszulSign_smul_eq_zsign (k := k), mul_comm (D.parity j) (D.parity i)] using
      P.reservoirPairCross_comp_prPreDot j i s hv hw Z
  have hy₁ : y ≫ x = ε • (x ≫ y) := by
    have h := congrArg (fun f => ε • f) (P.reservoirPairFirstDot_comp_probeDot j i s hv hw Z)
    simp only [koszulSign_smul_eq_zsign (k := k), mul_comm (D.parity j) (D.parity i),
      ε, smul_smul, zsign_mul_self', one_smul] at h
    exact h.symm
  have hy₂ : y ≫ z = ε • (z ≫ y) := by
    have h := congrArg (fun f => ε • f) (P.reservoirPairLastDot_comp_prPreDot j i s hv hw Z)
    simp only [koszulSign_smul_eq_zsign (k := k), mul_comm (D.parity j) (D.parity i),
      ε, smul_smul, zsign_mul_self', one_smul] at h
    exact h.symm
  have hx : z ≫ x = zsign k (D.parity i * D.parity i) • (x ≫ z) := by
    simpa only [koszulSign_smul_eq_zsign (k := k)] using
      P.reservoirPairLastDot_comp_prPostDot j i s hv hw Z
  rw [qExpr_comp_sub_reverse Sc i j ψ x z y h₁ h₂ hy₁ hy₂ hx]
  simp only [← End.mul_def, compPow_eq_pow, map_add, map_sum, map_smul, map_mul, map_pow,
    show φ = conjAlg (k := k) (P.reservoirPairFirstIso j i s hv hw Z).symm from rfl,
    hc.1, hc.2.1, hc.2.2]
  rfl

include hv hw in
/-- The complete RPR diagonal correction at arbitrary terminal sectors and paths. -/
theorem middleProbe_braidEq_diag_transport {t : Sector I}
    (e : nextSector (true, i) false (nextSector (true, i) false (nextSector (true, j) true s)) = t)
    (W : P.H t) (p : SPath (wd D ν [up i, up j, up i]) s t) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i j i ν p p W -
      braidRight (P.swappedGens c L) i j i ν p p W =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p W) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p W) (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p W) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [up i] j [up i] p W) d ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p W) (b - 1 - a)) := by
  subst e
  rw [reservoirPairMiddle_unique ν j i s hv hw hij.symm p]
  exact P.middleProbe_braidEq_diag ν i j s hv hw c L W hij

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
