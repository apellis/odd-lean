/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ReverseDistinctProbeSector

/-! # Middle two-probe braid sector for three distinct colours

`middleDistinctProbe_braid` proves the literal sector entry
`PᵢRᵣPⱼ → PⱼRᵣPᵢ` for arbitrary supplied data and pairwise distinct
colours. The individual Q factor is transported using the prescribed unequal
probe slide and supernaturalness. The proof reuses the forward sector braid
and cancels only mixed comparison isomorphisms, never Q or a probe crossing.
This supplies a missing family for `CrossBraid.braid`; unequal reservoir
colours and the arbitrary-sector assembly are separate obligations.
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
variable (P : ProbeReservoir k B D Sc)

/-- Transport the inner Q factor alone across the unequal probe crossing. -/
theorem preCrossNe_qExpr_inner (i j r : I) (hij : i ≠ j) (s : Sector I)
    (hs : nextSector (true, j) true (nextSector (true, i) true s) =
      nextSector (true, i) true (nextSector (true, j) true s))
    (Z : P.H (nextSector (true, i) true (nextSector (true, j) true s)))
    (θ : End Z) (hθ : θ ∈ parity (R := k) _ _ (D.parity r)) :
    let Z₀ : P.H (nextSector (true, j) true (nextSector (true, i) true s)) := hs ▸ Z
    let y : End ((P.step (true, i) true s trivial).obj ((P.step (true, j) true _ trivial).obj Z₀)) := (P.step (true, i) true s trivial).map (P.T.dot j (P.muP_preE j (nextSector (true, i) true s)) ▷ Z₀)
    let z := (P.step (true, i) true s trivial).map
      ((P.step (true, j) true _ trivial).map ((P.castH hs).map θ))
    let x' := P.T.dot j (P.muP_preE j s) ▷ (P.step (true, i) true _ trivial).obj Z
    let z' := (P.step (true, j) true s trivial).map
      ((P.step (true, i) true _ trivial).map θ)
    qExpr Sc y z j r ≫ P.preCrossNe i j s hs Z =
      P.preCrossNe i j s hs Z ≫ qExpr Sc x' z' j r := by
  dsimp only
  symm
  apply comp_qExpr (Sc := Sc) _ _ _ _ _ j r
    (zsign k (D.parity j * D.parity i))
    (zsign k (D.parity r * (D.parity i * D.parity j)))
  · simpa only [mul_comm] using P.preCrossNe_slideR i j hij s hs Z
  · have h := (P.preCrossNe_supernatural i j s hs).naturality hθ
    have he : sign k (D.parity i * D.parity j * D.parity r) =
        zsign k (D.parity i * D.parity j * D.parity r) := by
      generalize D.parity i * D.parity j * D.parity r = p
      fin_cases p <;> simp [sign, zsign]
    simp only [Functor.comp_map, he] at h
    rw [h, smul_smul]
    simp only [mul_comm (D.parity r), zsign_mul_self', one_smul]
  · exact zsign_pow_of_mul_eq_zero (k := k) (D.parity j) (D.parity i)
  · exact zsign_pow_of_mul_eq_zero (k := k) (D.parity r) (D.parity i * D.parity j)

/-- A single inner factor with a homogeneous spectator. -/
def probeInnerQ (i j r : I) (s : Sector I)
    (Y : P.H (nextSector (true, j) true (nextSector (true, i) true s))) (θ : End Y) :=
  qExpr Sc ((P.step (true, i) true s trivial).map
    (P.T.dot j (P.muP_preE j (nextSector (true, i) true s)) ▷ Y))
    ((P.step (true, i) true s trivial).map ((P.step (true, j) true _ trivial).map θ)) j r

/-- Heterogeneous transport of the single inner factor. -/
theorem probeInnerQ_heq (i j r : I) (s : Sector I)
    {Y Y' : P.H (nextSector (true, j) true (nextSector (true, i) true s))}
    (hY : Y = Y') {θ : End Y} {θ' : End Y'} (hθ : HEq θ θ') :
    HEq (P.probeInnerQ i j r s Y θ) (P.probeInnerQ i j r s Y' θ') := by
  subst hY
  cases hθ
  rfl

section Paths
variable (ν : X) (i j r : I) (s : Sector I) (hR : StepValid (true, r) false s)
  {t : Sector I}
  (e : nextSector (true, r) false (nextSector (true, j) true (nextSector (true, i) true s)) = t)
  (Z : P.H t)

/-- The first mixed comparison as an isomorphism of sector-path objects. -/
def distinctProbeFirstSectorIso :
    (P.pathFunctor (distinctProbeSource (D := D) ν i j r s hR e)).obj Z ≅
      (P.pathFunctor (distinctProbeMiddle (D := D) ν i j r s hR e)).obj Z := by
  subst e
  exact P.distinctProbeFirstIso i j r s hR Z

/-- The second mixed comparison as an isomorphism of sector-path objects. -/
def distinctProbeSecondSectorIso :
    (P.pathFunctor (distinctProbeMiddle (D := D) ν i j r s hR e)).obj Z ≅
      (P.pathFunctor (distinctProbeTarget (D := D) ν i j r s hR e)).obj Z := by
  subst e
  exact P.mixedJ i r s hR ((P.step (true, j) true _ trivial).obj Z)

/-- The Q weight of the reverse first mixed edge. -/
def distinctProbeInnerSectorQ :
    End ((P.pathFunctor (distinctProbeSource (D := D) ν i j r s hR e)).obj Z) := by
  subst e
  exact (P.step (true, i) true s trivial).map (P.mixedQ j r (nextSector (true, i) true s) hR Z)

/-- The Q weight of the reverse second mixed edge. -/
def distinctProbeMiddleSectorQ :
    End ((P.pathFunctor (distinctProbeMiddle (D := D) ν i j r s hR e)).obj Z) := by
  subst e
  exact P.mixedQ i r s hR ((P.step (true, j) true _ trivial).obj Z)

/-- The first sector weight is the inner dot polynomial. -/
theorem distinctProbeInnerSectorQ_heq :
    HEq (P.distinctProbeInnerSectorQ ν i j r s hR e Z)
      (qExpr Sc (P.distinctProbeInnerDot i j r s hR (e ▸ Z))
        (P.distinctProbeSpectatorDot i j r s hR (e ▸ Z)) j r) := by
  subst e
  exact heq_of_eq (P.distinctProbe_map_mixedQ i j r s hR Z)

/-- Conjugating the middle weight gives the outer dot polynomial. -/
theorem distinctProbeMiddleSectorQ_conj_heq :
    HEq ((P.distinctProbeFirstSectorIso ν i j r s hR e Z).hom ≫
      P.distinctProbeMiddleSectorQ ν i j r s hR e Z ≫
      (P.distinctProbeFirstSectorIso ν i j r s hR e Z).inv)
      (qExpr Sc (P.distinctProbeOuterDot i j r s hR (e ▸ Z))
        (P.distinctProbeSpectatorDot i j r s hR (e ▸ Z)) i r) := by
  subst e
  exact heq_of_eq (P.distinctProbeFirstIso_conj_mixedQ i j r s hR Z)

variable (c : P.CrossCoeff Sc) (L : P.LeftwardData)

/-- Evaluation of the first forward mixed edge. -/
theorem distinctProbeFirstSectorIso_hom_eq (hjr : j ≠ r) :
    (P.distinctProbeFirstSectorIso ν i j r s hR e Z).hom =
      crossEntry (P.swappedGens c L) ν [up i] j r []
        (distinctProbeSource ν i j r s hR e) (distinctProbeMiddle ν i j r s hR e) Z := by
  subst e
  symm
  refine (crossEntry_right (P.swappedGens c L) ν i j r true trivial
    (.cons _ true _ trivial (.cons _ false _ hR (.nil _)))
    (.cons _ false _ hR (.cons _ true _ trivial (.nil _))) Z).trans ?_
  dsimp only [swappedGens]
  rw [P.crossImage_ne c hjr]
  rfl

/-- Evaluation of the second forward mixed edge. -/
theorem distinctProbeSecondSectorIso_hom_eq (hir : i ≠ r) :
    (P.distinctProbeSecondSectorIso ν i j r s hR e Z).hom =
      crossEntry (P.swappedGens c L) ν [] i r [up j]
        (distinctProbeMiddle ν i j r s hR e) (distinctProbeTarget ν i j r s hR e) Z := by
  subst e
  symm
  refine (crossEntry_left (P.swappedGens c L) ν i r j
    (.cons _ true s trivial (.cons _ false _ hR (.nil _)))
    (.cons _ false s hR (.cons _ true _ trivial (.nil _)))
    (.cons _ true _ trivial (.nil _)) Z).trans ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  dsimp only [swappedGens]
  rw [P.crossImage_ne c hir]
  rfl

/-- Evaluation of the reverse first edge, retaining its Q factor. -/
theorem reverseDistinctProbe_first_eq (hjr : j ≠ r) :
    crossEntry (P.swappedGens c L) ν [up i] r j []
      (distinctProbeMiddle ν i j r s hR e) (distinctProbeSource ν i j r s hR e) Z =
    (P.distinctProbeFirstSectorIso ν i j r s hR e Z).inv ≫
      P.distinctProbeInnerSectorQ ν i j r s hR e Z := by
  subst e
  rw [eq_of_heq (P.reverseDistinctProbe_right_mixed_heq ν i j r s hR rfl c L Z hjr)]
  exact (P.step (true, i) true s trivial).map_comp _ _

/-- Evaluation of the reverse second edge, retaining its Q factor. -/
theorem reverseDistinctProbe_second_eq (hir : i ≠ r) :
    crossEntry (P.swappedGens c L) ν [] r i [up j]
      (distinctProbeTarget ν i j r s hR e) (distinctProbeMiddle ν i j r s hR e) Z =
    (P.distinctProbeSecondSectorIso ν i j r s hR e Z).inv ≫
      P.distinctProbeMiddleSectorQ ν i j r s hR e Z := by
  subst e
  exact eq_of_heq (P.reverseDistinctProbe_left_mixed_heq ν i j r s hR rfl c L Z hir)
end Paths

/-- Transport of the single Q factor needed for the middle sector. -/
theorem distinctProbeInnerSectorQ_cross (ν : X) (i j r : I) (s : Sector I)
    (hR : StepValid (true, r) false s) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    (hs : nextSector (true, j) true (nextSector (true, i) true s) =
      nextSector (true, i) true (nextSector (true, j) true s))
    (hsR : nextSector (true, r) false (nextSector (true, j) true (nextSector (true, i) true s)) =
      nextSector (true, r) false (nextSector (true, i) true (nextSector (true, j) true s)))
    (Z : P.H (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, j) true s)))) :
    P.distinctProbeInnerSectorQ ν i j r s hR hsR Z ≫
        crossEntry (P.swappedGens c L) ν [] i j [up r]
          (distinctProbeSource ν i j r s hR hsR) (distinctProbeSource ν j i r s hR rfl) Z =
      crossEntry (P.swappedGens c L) ν [] i j [up r]
          (distinctProbeSource ν i j r s hR hsR) (distinctProbeSource ν j i r s hR rfl) Z ≫
        ((P.distinctProbeFirstSectorIso ν j i r s hR rfl Z).hom ≫
          P.distinctProbeMiddleSectorQ ν j i r s hR rfl Z ≫
          (P.distinctProbeFirstSectorIso ν j i r s hR rfl Z).inv) := by
  let Y := (P.step (true, r) false (nextSector (true, i) true (nextSector (true, j) true s)) hR).obj Z
  let θ := P.dotDiag r false (nextSector (true, i) true (nextSector (true, j) true s)) hR Z
  have hθ : θ ∈ parity (R := k) _ _ (D.parity r) := by
    have h := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W r
      (nextSector (true, i) true (nextSector (true, j) true s)).1
      (P.muP (nextSector (true, i) true (nextSector (true, j) true s)))
      (P.muM_postE r hR) 1).mem Z
    simpa only [θ, dotDiag, step, Nat.cast_one, one_mul, pow_one] using h
  have hQ := P.preCrossNe_qExpr_inner i j r hij s hs Y θ hθ
  obtain ⟨hA, hf⟩ := P.distinctProbe_left ν i j r s hR hs hsR c L Z hij hir hjr
  obtain ⟨hY, hd⟩ := P.reservoirDot_cast r hs hR hR Z
  have hw := P.probeInnerQ_heq i j r s hY hd
  have hw' : HEq (P.distinctProbeInnerSectorQ ν i j r s hR hsR Z)
      (P.probeInnerQ i j r s ((P.castH hs).obj Y) ((P.castH hs).map θ)) :=
    (P.distinctProbeInnerSectorQ_heq ν i j r s hR hsR Z).trans hw.symm
  apply rectangle_of_heq hA hA hA rfl rfl hw' hf hf
    (P.distinctProbeMiddleSectorQ_conj_heq ν j i r s hR rfl Z)
  apply heq_of_eq
  simpa only [probeInnerQ, Category.assoc, Y, θ, dotDiag, distinctProbeOuterDot,
    distinctProbeInnerDot, distinctProbeSpectatorDot, prPreDot, prPostDot, castH] using hQ

/-- The middle two-probe sector for three pairwise distinct colours.
Only mixed comparison isomorphisms are cancelled; the Q factor is retained. -/
theorem middleDistinctProbe_braid (ν : X) (i j r : I) (s : Sector I)
    (hR : StepValid (true, r) false s) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    (hsR : nextSector (true, r) false (nextSector (true, j) true (nextSector (true, i) true s)) =
      nextSector (true, r) false (nextSector (true, i) true (nextSector (true, j) true s)))
    (Z : P.H (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, j) true s)))) :
    braidLeft (P.swappedGens c L) i r j ν
      (distinctProbeMiddle ν i j r s hR hsR) (distinctProbeMiddle ν j i r s hR rfl) Z =
    braidRight (P.swappedGens c L) i r j ν
      (distinctProbeMiddle ν i j r s hR hsR) (distinctProbeMiddle ν j i r s hR rfl) Z := by
  classical
  have hs : nextSector (true, j) true (nextSector (true, i) true s) =
      nextSector (true, i) true (nextSector (true, j) true s) := by
    simp only [nextSector, add_right_comm]
  let t := nextSector (true, r) false (nextSector (true, i) true (nextSector (true, j) true s))
  let : Subsingleton (SPath (wd D ν [up i, up j, up r]) s t) :=
    ⟨path_eq_three_distinct hij hir hjr⟩
  let := Fintype.ofFinite (SPath (wd D ν [up i, up j, up r]) s t)
  let : Subsingleton (SPath (wd D ν [up j, up i, up r]) s t) :=
    ⟨path_eq_three_distinct hij.symm hjr hir⟩
  let := Fintype.ofFinite (SPath (wd D ν [up j, up i, up r]) s t)
  let : Subsingleton (SPath (wd D ν [up j, up r, up i]) s t) :=
    ⟨path_eq_three_distinct hjr hij.symm hir.symm⟩
  let := Fintype.ofFinite (SPath (wd D ν [up j, up r, up i]) s t)
  let : Subsingleton (SPath (wd D ν [up i, up r, up j]) s t) :=
    ⟨path_eq_three_distinct hir hij hjr.symm⟩
  let := Fintype.ofFinite (SPath (wd D ν [up i, up r, up j]) s t)
  let : Subsingleton (SPath (wd D ν [up r, up i, up j]) s t) :=
    ⟨path_eq_three_distinct hir.symm hjr.symm hij⟩
  let := Fintype.ofFinite (SPath (wd D ν [up r, up i, up j]) s t)
  let : Subsingleton (SPath (wd D ν [up r, up j, up i]) s t) :=
    ⟨path_eq_three_distinct hjr.symm hir.symm hij.symm⟩
  let := Fintype.ofFinite (SPath (wd D ν [up r, up j, up i]) s t)
  have hf := P.distinctProbe_braid ν i j r s hR c L hij hir hjr hsR Z
  unfold braidLeft braidRight at hf
  rw [Fintype.sum_subsingleton _ (distinctProbeMiddle (D := D) ν j i r s hR rfl),
    Fintype.sum_subsingleton _ (distinctProbeSource (D := D) ν j i r s hR rfl),
    Fintype.sum_subsingleton _ (distinctProbeTarget (D := D) ν i j r s hR hsR),
    Fintype.sum_subsingleton _ (distinctProbeMiddle (D := D) ν i j r s hR hsR)] at hf
  rw [← P.distinctProbeFirstSectorIso_hom_eq ν j i r s hR rfl Z c L hir,
    ← P.distinctProbeSecondSectorIso_hom_eq ν j i r s hR rfl Z c L hjr,
    ← P.distinctProbeFirstSectorIso_hom_eq ν i j r s hR hsR Z c L hjr,
    ← P.distinctProbeSecondSectorIso_hom_eq ν i j r s hR hsR Z c L hir] at hf
  unfold braidLeft braidRight
  rw [Fintype.sum_subsingleton _ (distinctProbeTarget (D := D) ν j i r s hR rfl),
    Fintype.sum_subsingleton _ (distinctProbeTarget (D := D) ν i j r s hR hsR),
    Fintype.sum_subsingleton _ (distinctProbeSource (D := D) ν j i r s hR rfl),
    Fintype.sum_subsingleton _ (distinctProbeSource (D := D) ν i j r s hR hsR)]
  rw [← P.distinctProbeSecondSectorIso_hom_eq ν i j r s hR hsR Z c L hir,
    ← P.distinctProbeFirstSectorIso_hom_eq ν j i r s hR rfl Z c L hir,
    P.reverseDistinctProbe_first_eq ν i j r s hR hsR Z c L hjr,
    P.reverseDistinctProbe_second_eq ν j i r s hR rfl Z c L hjr]
  apply (cancel_epi (P.distinctProbeFirstSectorIso ν i j r s hR hsR Z).hom).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (P.distinctProbeFirstSectorIso ν i j r s hR hsR Z).hom,
    ← Category.assoc ((P.distinctProbeFirstSectorIso ν i j r s hR hsR Z).hom ≫
      (P.distinctProbeSecondSectorIso ν i j r s hR hsR Z).hom),
    ← hf]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (P.distinctProbeInnerSectorQ ν i j r s hR hsR Z),
    P.distinctProbeInnerSectorQ_cross ν i j r s hR c L hij hir hjr hs hsR Z]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
