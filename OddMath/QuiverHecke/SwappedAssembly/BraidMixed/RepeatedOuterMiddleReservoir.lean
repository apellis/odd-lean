/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.QWeightedReverseSector
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPureProbeMatrix
import OddMath.QuiverHecke.SwappedAssembly.BraidEq.Algebra

/-! # The repeated-outer probe/reservoir/probe diagonal correction -/

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
variable (P : ProbeReservoir k B D Sc)
variable (ν : X) (i j : I) (s : Sector I) (hR : StepValid (true, j) false s)
  (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (Z : P.H (nextSector (true, j) false (nextSector (true, i) true (nextSector (true, i) true s))))

/-- Both literal diagonal path sums reduce to their unique supported routes. -/
theorem middleReservoir_routes (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i j i ν
      (probePairMiddle ν i j s hR) (probePairMiddle ν i j s hR) Z =
      ((P.mixedJ i j s hR ((P.step (true, i) true _ trivial).obj Z)).hom ≫
        (P.step (true, j) false s hR).map (P.preCrossSame i (nextSector (true, j) false s) Z)) ≫
      ((P.mixedJ i j s hR ((P.step (true, i) true _ trivial).obj Z)).inv ≫
        P.mixedQ i j s hR ((P.step (true, i) true _ trivial).obj Z)) ∧
    braidRight (P.swappedGens c L) i j i ν
      (probePairMiddle ν i j s hR) (probePairMiddle ν i j s hR) Z =
      (((P.probePairFirstIso i j s hR Z).inv ≫
        (P.step (true, i) true s trivial).map (P.mixedQ i j (nextSector (true, i) true s) hR Z)) ≫
        P.preCrossSame i s ((P.step (true, j) false (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z)) ≫
      (P.probePairFirstIso i j s hR Z).hom := by
  classical
  let : Subsingleton (SPath (wd D ν [up i, up i, up j]) s
      (nextSector (true, j) false (nextSector (true, i) true (nextSector (true, i) true s)))) :=
    ⟨fun p q => (probePairSource_unique ν i j s hR hij p).trans
      (probePairSource_unique ν i j s hR hij q).symm⟩
  let : Subsingleton (SPath (wd D ν [up i, up j, up i]) s
      (nextSector (true, j) false (nextSector (true, i) true (nextSector (true, i) true s)))) :=
    ⟨fun p q => (probePairMiddle_unique ν i j s hR hij p).trans
      (probePairMiddle_unique ν i j s hR hij q).symm⟩
  let : Subsingleton (SPath (wd D ν [up j, up i, up i]) s
      (nextSector (true, j) false (nextSector (true, i) true (nextSector (true, i) true s)))) :=
    ⟨fun p q => (probePairTarget_unique ν i j s hR hij p).trans
      (probePairTarget_unique ν i j s hR hij q).symm⟩
  let := Fintype.ofFinite (SPath (wd D ν [up i, up i, up j]) s
    (nextSector (true, j) false (nextSector (true, i) true (nextSector (true, i) true s))))
  let := Fintype.ofFinite (SPath (wd D ν [up i, up j, up i]) s
    (nextSector (true, j) false (nextSector (true, i) true (nextSector (true, i) true s))))
  let := Fintype.ofFinite (SPath (wd D ν [up j, up i, up i]) s
    (nextSector (true, j) false (nextSector (true, i) true (nextSector (true, i) true s))))
  constructor
  · unfold braidLeft
    rw [Fintype.sum_subsingleton _ (probePairTarget (D := D) ν i j s hR),
      Fintype.sum_subsingleton _ (probePairTarget (D := D) ν i j s hR)]
    rw [P.probePair_left_mixed ν i j s hR c L Z hij,
      P.probePair_right_same, P.reverseProbePair_left_mixed ν i j s hR c L Z hij]
  · unfold braidRight
    rw [Fintype.sum_subsingleton _ (probePairSource (D := D) ν i j s hR),
      Fintype.sum_subsingleton _ (probePairSource (D := D) ν i j s hR)]
    rw [P.reverseProbePair_right_mixed ν i j s hR c L Z hij,
      P.probePair_left_same, P.probePair_right_mixed ν i j s hR c L Z hij]
    simp only [probePairFirstIso, Functor.mapIso_inv, Functor.mapIso_hom, Functor.map_comp]


private lemma middle_conjugate {C : Type u} [Category C] [Preadditive C]
    {A B W : C} (J : A ≅ B) (K : B ≅ W) (S R : End A) (T : End W) (Q : End B)
    (h : S ≫ J.hom ≫ K.hom = J.hom ≫ K.hom ≫ T) :
    J.hom ≫ (((K.hom ≫ T) ≫ (K.inv ≫ Q)) -
      (((J.inv ≫ R) ≫ S) ≫ J.hom)) ≫ J.inv =
      S ≫ (J.hom ≫ Q ≫ J.inv) - R ≫ S := by
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have hh := congrArg (fun f => f ≫ K.inv ≫ Q ≫ J.inv) h
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [hh]

/-- The full literal braid difference conjugates to the same-colour Q commutator. -/
theorem middleReservoir_commutator (hij : i ≠ j) :
    let W := (P.step (true, j) false (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z
    (P.probePairFirstIso i j s hR Z).hom ≫
      (braidLeft (P.swappedGens c L) i j i ν
        (probePairMiddle ν i j s hR) (probePairMiddle ν i j s hR) Z -
       braidRight (P.swappedGens c L) i j i ν
        (probePairMiddle ν i j s hR) (probePairMiddle ν i j s hR) Z) ≫
      (P.probePairFirstIso i j s hR Z).inv =
      P.preCrossSame i s W ≫ qExpr Sc (P.ppLeftDot i s W) (P.probePairSpectatorDot i j s hR Z) i j -
      qExpr Sc (P.ppRightDot i s W) (P.probePairSpectatorDot i j s hR Z) i j ≫ P.preCrossSame i s W := by
  dsimp only
  rw [(P.middleReservoir_routes ν i j s hR c L Z hij).1,
    (P.middleReservoir_routes ν i j s hR c L Z hij).2]
  rw [middle_conjugate _ _ _ _ _ _ (P.preCrossSame_mixedJ_pair_ne i j s hR Z),
    P.probePairFirstIso_conj_mixedQ, P.probePair_map_mixedQ]

/-- Literal outer dot on the PRP path. -/
theorem middleReservoir_dotX :
    dotEntry (P.swappedGens c L) ν [] i [up j, up i] (probePairMiddle ν i j s hR) Z =
      P.prPreDot i j s hR ((P.step (true, i) true _ trivial).obj Z) := by
  apply eq_of_heq
  unfold dotEntry
  refine (heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [] (SKM.Shape.dot i) [up j, up i]) (.nil s)
    (.cons _ true _ trivial (.nil _)) (.cons _ true _ trivial (.nil _))
    (SPath.two false true hR trivial rfl) _ _ rfl rfl Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (P.dotImage_probe i (SKM.wt D ν [up j, up i]) s trivial trivial _)

/-- Literal middle reservoir dot on the PRP path. -/
theorem middleReservoir_dotY :
    dotEntry (P.swappedGens c L) ν [up i] j [up i] (probePairMiddle ν i j s hR) Z =
      P.prPostDot i j s hR ((P.step (true, i) true _ trivial).obj Z) := by
  apply eq_of_heq
  unfold dotEntry
  refine (heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [up i] (SKM.Shape.dot j) [up i]) (.cons _ true s trivial (.nil _))
    (.cons _ false _ hR (.nil _)) (.cons _ false _ hR (.nil _))
    (.cons _ true _ trivial (.nil _)) _ _ rfl rfl Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (congrArg (P.step (true, i) true s trivial).map
    (P.dotImage_reservoir j (SKM.wt D ν [up i]) (nextSector (true, i) true s) hR hR
      ((P.step (true, i) true _ trivial).obj Z)))

/-- Literal inner probe dot on the PRP path. -/
theorem middleReservoir_dotZ :
    dotEntry (P.swappedGens c L) ν [up i, up j] i [] (probePairMiddle ν i j s hR) Z =
      (P.step (true, i) true s trivial).map
        ((P.step (true, j) false (nextSector (true, i) true s) hR).map
          (P.T.dot i (P.muP_preE i (nextSector (true, i) true s)) ▷ Z)) := by
  apply eq_of_heq
  unfold dotEntry
  refine (heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [up i, up j] (SKM.Shape.dot i) []) (SPath.two true false trivial hR rfl)
    (.cons _ true _ trivial (.nil _)) (.cons _ true _ trivial (.nil _))
    (.nil _) _ _ rfl rfl Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (congrArg (fun f => (P.step (true, i) true s trivial).map
    ((P.step (true, j) false (nextSector (true, i) true s) hR).map f))
    (P.dotImage_probe i ν (nextSector (true, j) false (nextSector (true, i) true s)) trivial trivial Z))


/-- All three literal dot coordinates under the mixed comparison. -/
theorem middleReservoir_dot_coordinates :
    let φ := conjAlg (k := k) (P.probePairFirstIso i j s hR Z).symm
    let W := (P.step (true, j) false (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z
    let ε := zsign k (D.parity i * D.parity j)
    φ (dotEntry (P.swappedGens c L) ν [] i [up j, up i] (probePairMiddle ν i j s hR) Z) =
      ε • P.ppLeftDot i s W ∧
    φ (dotEntry (P.swappedGens c L) ν [up i] j [up i] (probePairMiddle ν i j s hR) Z) =
      ε • P.probePairSpectatorDot i j s hR Z ∧
    φ (dotEntry (P.swappedGens c L) ν [up i, up j] i [] (probePairMiddle ν i j s hR) Z) =
      ε • P.ppRightDot i s W := by
  dsimp only
  rw [P.middleReservoir_dotX, P.middleReservoir_dotY, P.middleReservoir_dotZ]
  constructor
  · have hx := congrArg (fun f => zsign k (D.parity i * D.parity j) • f)
      (P.ppLeftDot_comp_probePairFirstIso i j s hR Z)
    simp only [smul_smul, zsign_mul_self', one_smul] at hx
    have hh := congrArg (fun f => f ≫ (P.probePairFirstIso i j s hR Z).inv) hx
    simp only [Linear.smul_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id] at hh
    exact hh.symm
  constructor
  · exact P.probePairFirstIso_conj_prPostDot i j s hR Z
  · have hz := congrArg (fun f => zsign k (D.parity i * D.parity j) • f)
      (P.prPreDot_comp_mixedJ_ne i j (nextSector (true, i) true s) hR Z)
    simp only [smul_smul, zsign_mul_self', one_smul] at hz
    have hh := congrArg (fun f => f ≫ (P.mixedJ i j (nextSector (true, i) true s) hR Z).inv) hz
    simp only [Linear.smul_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id] at hh
    have hm := congrArg (P.step (true, i) true s trivial).map hh.symm
    simp only [Functor.map_comp, Functor.map_smul] at hm
    exact hm

/-- The exact signed correction for the literal PRP diagonal matrix entry. -/
theorem middleReservoir_braidEq_diag (hij : i ≠ j) :
    let p := probePairMiddle (D := D) ν i j s hR
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
  let J := P.probePairFirstIso i j s hR Z
  let φ := conjAlg (k := k) J.symm
  let W := (P.step (true, j) false (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z
  have hinj : Function.Injective φ := by
    intro a b hab
    apply (cancel_epi J.hom).1
    apply (cancel_mono J.inv).1
    change J.hom ≫ a ≫ J.inv = J.hom ≫ b ≫ J.inv at hab
    simpa only [Category.assoc] using hab
  apply hinj
  have hc := P.middleReservoir_dot_coordinates ν i j s hR c L Z
  have hb := P.middleReservoir_commutator ν i j s hR c L Z hij
  change φ _ = _ at hb
  rw [hb]
  have h₁ : P.preCrossSame i s W ≫ P.ppLeftDot i s W -
      zsign k (D.parity i * D.parity i) • (P.ppRightDot i s W ≫ P.preCrossSame i s W) = 𝟙 _ := by
    simpa only [koszulSign_smul_eq_zsign (k := k)] using (P.preCrossSame_slides i s W).2
  have h₂ : P.preCrossSame i s W ≫ P.probePairSpectatorDot i j s hR Z =
      zsign k (D.parity i * D.parity j) •
        (P.probePairSpectatorDot i j s hR Z ≫ P.preCrossSame i s W) := by
    simpa only [koszulSign_smul_eq_zsign (k := k)] using
      P.preCrossSame_comp_probePairSpectatorDot i j s hR Z
  have h₃ : P.probePairSpectatorDot i j s hR Z ≫ P.ppRightDot i s W =
      zsign k (D.parity i * D.parity j) •
        (P.ppRightDot i s W ≫ P.probePairSpectatorDot i j s hR Z) := by
    have h := congrArg (fun f => zsign k (D.parity i * D.parity j) • f)
      (P.ppRightDot_comp_probePairSpectatorDot i j s hR Z)
    simp only [koszulSign_smul_eq_zsign (k := k), smul_smul, zsign_mul_self', one_smul] at h
    exact h.symm
  rw [comp_qExpr_sub Sc i j _ _ _ _ h₁ h₂ h₃]
  simp only [← End.mul_def, compPow_eq_pow, map_add, map_sum, map_smul, map_mul, map_pow,
    show φ = conjAlg (k := k) (P.probePairFirstIso i j s hR Z).symm from rfl,
    hc.1, hc.2.1, hc.2.2]
  rfl

include hR in
/-- The complete PRP diagonal correction at arbitrary terminal sectors and paths. -/
theorem middleReservoir_braidEq_diag_transport {t : Sector I}
    (e : nextSector (true, j) false (nextSector (true, i) true (nextSector (true, i) true s)) = t)
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
  rw [probePairMiddle_unique ν i j s hR hij p]
  exact P.middleReservoir_braidEq_diag ν i j s hR c L W hij

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
