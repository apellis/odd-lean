/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPureProbe
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterQCorrection

/-! # Literal pure-probe correction coordinates

The three dot entries, their arbitrary powers and their finite correction sums
are compared on the canonical pure-probe path. These comparisons serve the
pure-probe diagonal braid equation. -/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
include k

/-- Vertical powers commute with either whiskering, without parity restrictions. -/
theorem pureCorrection_power_right {a b d : B} {E : a ⟶ b}
    (x : End E) (Z : b ⟶ d) (n : ℕ) :
    compPow (x ▷ Z) n = rouquierPower x n ▷ Z := by
  rw [rouquierPower_eq_pow, ← compPow_eq_pow]
  induction n with
  | zero => simp only [compPow, TwoSupercategory.id_whiskerRight (R := k)]
  | succ n ih =>
    simp only [compPow, TwoSupercategory.comp_whiskerRight (R := k), ih]

/-- Left whiskering preserves every vertical power. -/
theorem pureCorrection_power_left {a b d : B} (E : a ⟶ b)
    {F : b ⟶ d} (y : End F) (n : ℕ) :
    compPow (E ◁ y) n = E ◁ compPow y n := by
  induction n with
  | zero => simp only [compPow, TwoSupercategory.whiskerLeft_id (R := k)]
  | succ n ih =>
    simp only [compPow, TwoSupercategory.whiskerLeft_comp (R := k), ih]

/-- The first factor dot through the triple normalization. -/
theorem pureCorrection_triple_first {a b d e f : B}
    (E : a ⟶ b) (F : b ⟶ d) (G : d ⟶ e) (Z : e ⟶ f) (x : End E) :
    (tripleRightIso (k := k) E F G Z).inv ≫ (x ▷ (F ≫ G)) ▷ Z ≫
      (tripleRightIso (k := k) E F G Z).hom = x ▷ (F ≫ G ≫ Z) := by
  simp only [tripleRightIso, Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [TwoSupercategory.associator_naturality_left_assoc (R := k)]
  simp only [Iso.inv_hom_id_assoc]
  rw [TwoSupercategory.whisker_exchange_of_even_right (R := k) x
    (TwoSupercategory.associator_hom_mem (R := k) F G Z)]
  simp only [← Category.assoc, ← TwoSupercategory.whiskerLeft_comp (R := k), Iso.inv_hom_id,
    TwoSupercategory.whiskerLeft_id (R := k), Category.id_comp]

/-- The last two factors through the triple normalization. -/
theorem pureCorrection_triple_tail {a b d e f : B}
    (E : a ⟶ b) (F : b ⟶ d) (G : d ⟶ e) (Z : e ⟶ f) (y : End (F ≫ G)) :
    (tripleRightIso (k := k) E F G Z).inv ≫ (E ◁ y) ▷ Z ≫
      (tripleRightIso (k := k) E F G Z).hom =
    E ◁ ((associator F G Z).inv ≫ y ▷ Z ≫ (associator F G Z).hom) :=
  (tripleRightIso_right (k := k) E F G F G Z y).symm

/-- The middle factor dot through triple reassociation. -/
theorem pureCorrection_triple_middle {a b d e f : B}
    (E : a ⟶ b) (F : b ⟶ d) (G : d ⟶ e) (Z : e ⟶ f) (y : End F) :
    (tripleRightIso (k := k) E F G Z).inv ≫ (E ◁ (y ▷ G)) ▷ Z ≫
      (tripleRightIso (k := k) E F G Z).hom = E ◁ (y ▷ (G ≫ Z)) := by
  rw [pureCorrection_triple_tail (k := k)]
  rw [TwoSupercategory.associator_naturality_left (R := k)]
  simp only [Iso.inv_hom_id_assoc]

/-- The final factor dot through triple reassociation. -/
theorem pureCorrection_triple_last {a b d e f : B}
    (E : a ⟶ b) (F : b ⟶ d) (G : d ⟶ e) (Z : e ⟶ f) (z : End G) :
    (tripleRightIso (k := k) E F G Z).inv ≫ (E ◁ F ◁ z) ▷ Z ≫
      (tripleRightIso (k := k) E F G Z).hom = E ◁ F ◁ (z ▷ Z) := by
  rw [pureCorrection_triple_tail (k := k)]
  rw [TwoSupercategory.associator_naturality_middle (R := k)]
  simp only [Iso.inv_hom_id_assoc]

/-- Conjugation of a product by the triple reassociation. -/
theorem pureCorrection_triple_comp {a b d e f : B}
    (E : a ⟶ b) (F : b ⟶ d) (G : d ⟶ e) (Z : e ⟶ f)
    (x y : End (E ≫ F ≫ G)) :
    (tripleRightIso (k := k) E F G Z).inv ≫ (x ≫ y) ▷ Z ≫
      (tripleRightIso (k := k) E F G Z).hom =
    ((tripleRightIso (k := k) E F G Z).inv ≫ x ▷ Z ≫
      (tripleRightIso (k := k) E F G Z).hom) ≫
    ((tripleRightIso (k := k) E F G Z).inv ≫ y ▷ Z ≫
      (tripleRightIso (k := k) E F G Z).hom) := by
  simp only [TwoSupercategory.comp_whiskerRight (R := k), Category.assoc,
    Iso.hom_inv_id_assoc]

/-- Finite sums commute with right whiskering. -/
theorem pureCorrection_sum_right {a b d : B} {E F : a ⟶ b}
    {ι : Type*} (s : Finset ι) (x : ι → (E ⟶ F)) (Z : b ⟶ d) :
    (∑ n ∈ s, x n) ▷ Z = ∑ n ∈ s, x n ▷ Z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, TwoSupercategory.zero_whiskerRight (R := k)]
  | @insert n s hn ih =>
    simp only [Finset.sum_insert hn, TwoSupercategory.add_whiskerRight (R := k), ih]

/-- Expand the transported factor polynomial into the three nested probe dots.
The order of the powers here is the factor order, before reflection of the finite sum. -/
theorem repeatedOuterPureProbe_factor_polynomial
    (P : ProbeReservoir k B D Sc) (i j : I) {a b d e : X}
    (hi : a + D.α i = b) (hj : b + D.α j = d) (hk : d + D.α i = e)
    {f : B} (Z : P.T.obj e ⟶ f) :
    let E := P.T.E i hi
    let F := P.T.E j hj
    let G := P.T.E i hk
    let Θ := tripleRightIso (k := k) E F G Z
    Θ.inv ≫ P.repeatedOuterProbeCorrection i j hi hj hk ▷ Z ≫ Θ.hom =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (P.T.dot i hi ▷ (F ≫ G ≫ Z)) a ≫
            compPow (E ◁ F ◁ (P.T.dot i hk ▷ Z)) (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i),
        ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (compPow (P.T.dot i hi ▷ (F ≫ G ≫ Z)) a ≫
            compPow (E ◁ (P.T.dot j hj ▷ (G ≫ Z))) d ≫
            compPow (E ◁ F ◁ (P.T.dot i hk ▷ Z)) (b - 1 - a)) := by
  classical
  dsimp only
  simp only [repeatedOuterProbeCorrection, TwoSupercategory.add_whiskerRight (R := k),
    pureCorrection_sum_right (k := k), TwoSupercategory.smul_whiskerRight (R := k),
    Preadditive.comp_add, Preadditive.add_comp, Preadditive.comp_sum, Preadditive.sum_comp,
    Linear.comp_smul, Linear.smul_comp]
  simp only [pureCorrection_triple_comp (k := k), pureCorrection_triple_first (k := k),
    pureCorrection_triple_middle (k := k), pureCorrection_triple_last (k := k),
    pureCorrection_power_left (k := k), pureCorrection_power_right (k := k)]

section Algebra
variable {R : Type*} [Ring R] [Algebra k R]

/-- Complementary powers in an even-degree odd correction commute. -/
theorem pureCorrection_outer_commute (x z : R) (pi : ZMod 2)
    (hxz : x * z = zsign k pi • (z * x)) (n a : ℕ) (ha : a < n)
    (hn : pi = 1 → Even n) : Commute (x ^ (n - 1 - a)) (z ^ a) := by
  rcases (show pi = 0 ∨ pi = 1 by fin_cases pi <;> (first | exact Or.inl rfl | exact Or.inr rfl)) with rfl | rfl
  · exact (show Commute x z by simpa [Commute, SemiconjBy, zsign] using hxz).pow_pow _ _
  · have hx : x * z = -(z * x) := by simpa [zsign] using hxz
    obtain ⟨m, hm⟩ := hn rfl
    have he : Even (n - 1 - a) ∨ Even a := by
      simp only [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
      omega
    rcases he with ⟨r, hr⟩ | ⟨r, hr⟩
    · rw [show n - 1 - a = 2 * r by omega, pow_mul]
      exact ((RepeatedOuterPolynomial.square_commute x z hx).pow_left r).pow_right a
    · have hz : z * x = -(x * z) := by rw [hx, neg_neg]
      rw [show a = 2 * r by omega, pow_mul]
      exact (((RepeatedOuterPolynomial.square_commute z x hz).pow_left r).symm).pow_left _

/-- Reflection of the signed scalar at complementary exponents. -/
theorem pureCorrection_reflect_sign (pi pj : ZMod 2) (n a : ℕ) (ha : a < n)
    (hn : pi = 1 → Even n) :
    zsign k pi * zsign k (pi * (pj + ((n - 1 - a : ℕ) : ZMod 2))) =
      zsign k (pi * (pj + a)) := by
  rcases (show pi = 0 ∨ pi = 1 by fin_cases pi <;> (first | exact Or.inl rfl | exact Or.inr rfl)) with rfl | rfl
  · simp only [zero_mul, zsign_zero, mul_one]
  · rw [← zsign_add]
    congr 1
    obtain ⟨m, hm⟩ := hn rfl
    have he : n - 1 - a + a + 1 = m + m := by omega
    have he' := congrArg (fun n : ℕ => (n : ZMod 2)) he
    simp only [Nat.cast_add, Nat.cast_one, CharTwo.add_self_eq_zero] at he'
    simp only [one_mul]
    linear_combination (norm := ring_nf) he'
    simp only [mul_two, CharTwo.add_self_eq_zero, neg_zero]

/-- Reflection of the complete ordered monomial sum, including a supported middle power. -/
theorem pureCorrection_reflect_sum (x y z : R) (pi pj : ZMod 2)
    (hxz : x * z = zsign k pi • (z * x))
    (hxy : x * y = zsign k (pi * pj) • (y * x))
    (hzy : z * y = zsign k (pi * pj) • (y * z))
    (n d : ℕ) (hn : pi = 1 → Even n) (hd : pj = 1 → Even d) (w : k) :
    zsign k pi • (∑ a ∈ Finset.range n,
      (zsign k (pi * (pj + a)) * w) • (z ^ (n - 1 - a) * y ^ d * x ^ a)) =
    ∑ a ∈ Finset.range n,
      (zsign k (pi * (pj + a)) * w) • (x ^ (n - 1 - a) * y ^ d * z ^ a) := by
  rw [Finset.smul_sum, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' := Finset.mem_range.mp ha
  rw [show n - 1 - (n - 1 - a) = a by omega]
  have h1 := (RepeatedOuterQCorrection.supported_middle_commute x y pi pj hxy d hd).pow_left (n - 1 - a)
  have h2 := (RepeatedOuterQCorrection.supported_middle_commute z y pi pj hzy d hd).pow_left a
  have h3 := pureCorrection_outer_commute (k := k) x z pi hxz n a ha' hn
  rw [mul_assoc, ← h1.eq, ← mul_assoc, ← h3.eq, mul_assoc, h2.eq, ← mul_assoc]
  rw [smul_smul, ← mul_assoc, pureCorrection_reflect_sign (k := k) pi pj n a ha' hn]

end Algebra

omit k in
private theorem pureCorrection_parity_self (p : ZMod 2) : p * p = p := by
  fin_cases p <;> rfl

/-- The signed interchange in functional endomorphism multiplication. -/
theorem pureCorrection_separated_commute {a b d : B} {E : a ⟶ b} {F : b ⟶ d}
    {x : End E} {y : End F} {p q : ZMod 2}
    (hx : x ∈ parity (R := k) E E p) (hy : y ∈ parity (R := k) F F q) :
    E ◁ y ≫ x ▷ F = zsign k (p * q) • (x ▷ F ≫ E ◁ y) := by
  have h := TwoSupercategory.super_interchange (R := k) hx hy
  rw [koszulSign_smul_eq_zsign (k := k)] at h
  have h' := congrArg (zsign k (p * q) • ·) h
  simp only [smul_smul, zsign_mul_self', one_smul] at h'
  exact h'.symm

/-- The factor correction, with its equal-crossing scalar, has the ordered
three-dot polynomial prescribed by the swapped braid relation. -/
theorem repeatedOuterPureProbe_normalized_polynomial
    (P : ProbeReservoir k B D Sc) (i j : I) {a b d e : X}
    (hi : a + D.α i = b) (hj : b + D.α j = d) (hk : d + D.α i = e)
    {f : B} (Z : P.T.obj e ⟶ f) :
    let E := P.T.E i hi
    let F := P.T.E j hj
    let G := P.T.E i hk
    let x : End (E ≫ F ≫ G ≫ Z) := P.T.dot i hi ▷ (F ≫ G ≫ Z)
    let y : End (E ≫ F ≫ G ≫ Z) := E ◁ (P.T.dot j hj ▷ (G ≫ Z))
    let z : End (E ≫ F ≫ G ≫ Z) := E ◁ F ◁ (P.T.dot i hk ▷ Z)
    let Θ := tripleRightIso (k := k) E F G Z
    koszulSign (D.parity i) (D.parity i) •
      (Θ.inv ≫ P.repeatedOuterProbeCorrection i j hi hj hk ▷ Z ≫ Θ.hom) =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow z a ≫ compPow x (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i),
        ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (compPow z a ≫ compPow y d ≫ compPow x (b - 1 - a)) := by
  classical
  dsimp only
  let E := P.T.E i hi
  let F := P.T.E j hj
  let G := P.T.E i hk
  let x : End (E ≫ F ≫ G ≫ Z) := P.T.dot i hi ▷ (F ≫ G ≫ Z)
  let y : End (E ≫ F ≫ G ≫ Z) := E ◁ (P.T.dot j hj ▷ (G ≫ Z))
  let z : End (E ≫ F ≫ G ≫ Z) := E ◁ F ◁ (P.T.dot i hk ▷ Z)
  have hxz : x * z = zsign k (D.parity i) • (z * x) := by
    have h := pureCorrection_separated_commute (P.T.dot_mem i hi)
      (TwoSupercategory.whiskerLeft_mem (R := k) F
        (TwoSupercategory.whiskerRight_mem (R := k) Z (P.T.dot_mem i hk)))
    simpa only [pureCorrection_parity_self, x, z, E, F, G, End.mul_def] using h
  have hxy : x * y = zsign k (D.parity i * D.parity j) • (y * x) :=
    pureCorrection_separated_commute (P.T.dot_mem i hi)
      (TwoSupercategory.whiskerRight_mem (R := k) (G ≫ Z) (P.T.dot_mem j hj))
  have hzy : z * y = zsign k (D.parity i * D.parity j) • (y * z) := by
    have h := TwoSupercategory.super_interchange (R := k) (P.T.dot_mem j hj)
      (TwoSupercategory.whiskerRight_mem (R := k) Z (P.T.dot_mem i hk))
    have h' := congrArg (fun f => E ◁ f) h
    simpa only [TwoSupercategory.whiskerLeft_comp (R := k),
      TwoSupercategory.whiskerLeft_zsmul (R := k), koszulSign_smul_eq_zsign (k := k),
      TwoSupercategory.whiskerLeft_smul (R := k),
      End.mul_def, mul_comm (D.parity j) (D.parity i)] using h'
  rw [koszulSign_smul_eq_zsign (k := k), pureCorrection_parity_self,
    P.repeatedOuterPureProbe_factor_polynomial i j hi hj hk Z, smul_add]
  simp only [compPow_eq_pow, ← End.mul_def]
  apply congrArg₂ (· + ·)
  · simpa only [pow_zero, mul_one] using
      pureCorrection_reflect_sum (k := k) x y z (D.parity i) (D.parity j)
        hxz hxy hzy (D.dn i j) 0 (RepeatedOuterQCorrection.outer_degree_even i j)
        (fun _ => ⟨0, rfl⟩) (Sc.t i j : k)
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hs : Sc.s i j b d = 0
    · simp only [hs, mul_zero, zero_smul, Finset.sum_const_zero, smul_zero]
    · exact pureCorrection_reflect_sum (k := k) x y z (D.parity i) (D.parity j)
        hxz hxy hzy b d (RepeatedOuterQCorrection.supported_outer_even Sc i j b d hs)
        (RepeatedOuterQCorrection.supported_inner_even Sc i j b d hs) (Sc.s i j b d)

variable [∀ a b : B, PiSupercategory k (a ⟶ b)]
variable (P : ProbeReservoir k B D Sc) (ν : X) (i j : I) (s : Sector I)
  (c : P.CrossCoeff Sc) (L : P.LeftwardData)

/-- The literal X dot at an arbitrary transported endpoint. -/
theorem repeatedOuterPureProbe_dotX_heq {t : Sector I}
    (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) true s)) = t)
    (Z : P.H t) :
    HEq (dotEntry (P.swappedGens c L) ν [] i [up j, up i]
      (SPath.three true true true trivial trivial trivial hs) Z)
      (P.dotDiag i true s trivial ((P.step (true, j) true _ trivial).obj ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z)))) := by
  subst hs
  unfold dotEntry
  refine (heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [] (SKM.Shape.dot i) [up j, up i]) (.nil s)
    (.cons _ true _ trivial (.nil _)) (.cons _ true _ trivial (.nil _)) (SPath.two true true trivial trivial rfl) _ _ rfl rfl Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (P.dotImage_probe i (SKM.wt D ν [up j, up i]) s trivial trivial _)

/-- The literal Y dot at an arbitrary transported endpoint. -/
theorem repeatedOuterPureProbe_dotY_heq {t : Sector I}
    (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) true s)) = t)
    (Z : P.H t) :
    HEq (dotEntry (P.swappedGens c L) ν [up i] j [up i]
      (SPath.three true true true trivial trivial trivial hs) Z)
      ((P.step (true, i) true s trivial).map (P.dotDiag j true _ trivial ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z)))) := by
  subst hs
  unfold dotEntry
  refine (heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [up i] (SKM.Shape.dot j) [up i]) (.cons _ true s trivial (.nil _))
    (.cons _ true _ trivial (.nil _)) (.cons _ true _ trivial (.nil _)) (.cons _ true _ trivial (.nil _)) _ _ rfl rfl Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (congrArg (P.step (true, i) true s trivial).map
    (P.dotImage_probe j (SKM.wt D ν [up i]) (nextSector (true, i) true s) trivial trivial
      ((P.step (true, i) true _ trivial).obj Z)))

/-- The literal Z dot at an arbitrary transported endpoint. -/
theorem repeatedOuterPureProbe_dotZ_heq {t : Sector I}
    (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) true s)) = t)
    (Z : P.H t) :
    HEq (dotEntry (P.swappedGens c L) ν [up i, up j] i []
      (SPath.three true true true trivial trivial trivial hs) Z)
      ((P.step (true, i) true s trivial).map ((P.step (true, j) true _ trivial).map (P.dotDiag i true _ trivial ((P.castH hs).obj Z)))) := by
  subst hs
  unfold dotEntry
  refine (heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [up i, up j] (SKM.Shape.dot i) []) (SPath.two true true trivial trivial rfl)
    (.cons _ true _ trivial (.nil _)) (.cons _ true _ trivial (.nil _)) (.nil _) _ _ rfl rfl Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (congrArg (fun f => (P.step (true, i) true s trivial).map
    ((P.step (true, j) true _ trivial).map f))
    (P.dotImage_probe i ν (nextSector (true, j) true (nextSector (true, i) true s))
      trivial trivial Z))

private theorem pureCorrection_polynomial_heq
    {C : Type u} [Category C] [Preadditive C] [Linear k C]
    (i j : I) {A A' : C} (e : A = A')
    {x y z : End A} {x' y' z' : End A'}
    (hx : HEq x x') (hy : HEq y y') (hz : HEq z z') :
    HEq ((∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
        (compPow z a ≫ compPow x (D.dn i j - 1 - a))) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
        (compPow z a ≫ compPow y d ≫ compPow x (b - 1 - a)))
      ((∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
        (compPow z' a ≫ compPow x' (D.dn i j - 1 - a))) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
        (compPow z' a ≫ compPow y' d ≫ compPow x' (b - 1 - a))) := by
  subst e
  cases hx; cases hy; cases hz
  rfl

/-- The factor polynomial is exactly the literal finite correction in path dots,
with every power and both coefficient sums retained. -/
theorem repeatedOuterPureProbe_correction_heq
    (Z : P.H (nextSector (true, i) true (nextSector (true, j) true
      (nextSector (true, i) true s)))) :
    let p := distinctPureProbePath (D := D) ν i j i s rfl
    let Θ := tripleRightIso (k := k) (P.T.E i (P.muP_preE i s))
      (P.T.E j (P.muP_preE j _)) (P.T.E i (P.muP_preE i _)) Z
    HEq (koszulSign (D.parity i) (D.parity i) •
        (Θ.inv ≫ P.repeatedOuterProbeCorrection i j
          (P.muP_preE i s) (P.muP_preE j _) (P.muP_preE i _) ▷ Z ≫ Θ.hom))
      (∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p Z) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p Z)
              (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p Z) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [up i] j [up i] p Z) d ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p Z) (b - 1 - a))) := by
  classical
  dsimp only
  refine (heq_of_eq (P.repeatedOuterPureProbe_normalized_polynomial i j
    (P.muP_preE i s) (P.muP_preE j _) (P.muP_preE i _) Z)).trans ?_
  symm
  exact pureCorrection_polynomial_heq i j
    (eq_of_heq (P.distinctPureProbe_obj ν i j i s rfl Z rfl rfl rfl rfl
      (P.muP_preE i s) (P.muP_preE j _) (P.muP_preE i _) Z HEq.rfl))
    (P.repeatedOuterPureProbe_dotX_heq ν i j s c L rfl Z)
    (P.repeatedOuterPureProbe_dotY_heq ν i j s c L rfl Z)
    (P.repeatedOuterPureProbe_dotZ_heq ν i j s c L rfl Z)

/-- The literal diagonal field of `CrossBraid` at any pure-probe endpoint. -/
theorem repeatedOuterPureProbe_braidEq_diag {t : Sector I}
    (ht : nextSector (true, i) true (nextSector (true, j) true
      (nextSector (true, i) true s)) = t)
    (p : SPath (wd D ν [up i, up j, up i]) s t) (Z : P.H t) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i j i ν p p Z -
      braidRight (P.swappedGens c L) i j i ν p p Z =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p Z) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p Z)
              (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p Z) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [up i] j [up i] p Z) d ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p Z) (b - 1 - a)) := by
  classical
  subst ht
  rw [pureProbePath_unique rfl p]
  exact eq_of_heq ((P.repeatedOuterPureProbe_canonical_heq ν i j s c L hij Z).trans
    (P.repeatedOuterPureProbe_correction_heq ν i j s c L Z))

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
