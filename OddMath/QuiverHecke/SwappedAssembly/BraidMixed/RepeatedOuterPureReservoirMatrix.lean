/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPureReservoir
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterQCorrection

/-! # Literal reservoir correction coordinates

Transport of the repeated-outer factor polynomial to the three literal reservoir dots.
-/

noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u,u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir

/-- The first reservoir dot through removal of all three parity shifts. -/
theorem pureReservoir_shift_first {a b d e f : B}
    (Z : a ⟶ b) (E : b ⟶ d) (F : d ⟶ e) (G : e ⟶ f)
    (p q r t : ZMod 2) (x : End E) (hx : x ∈ parity (R := k) E E t) :
    (homParityShift (k := k) r).map
      ((homParityShift (k := k) q).map
        ((homParityShift (k := k) p).map (Z ◁ x) ▷ F) ▷ G) ≫
      (reservoirShiftTripleIso Z E F G p q r).hom =
    sign k ((p + q + r) * t) • ((reservoirShiftTripleIso Z E F G p q r).hom ≫
      ((Z ◁ x) ▷ F) ▷ G) := by
  have hx0 := TwoSupercategory.whiskerLeft_mem (R := k) Z hx
  have hx1 := IsSuperfunctor.map_mem (F := homParityShift (k := k) p) hx0
  have hx2 := TwoSupercategory.whiskerRight_mem (R := k) F hx1
  have hx3 := IsSuperfunctor.map_mem (F := homParityShift (k := k) q) hx2
  have hx4 := TwoSupercategory.whiskerRight_mem (R := k) G hx3
  simp only [reservoirShiftTripleIso, Iso.trans_hom, whiskerRightIso, Category.assoc]
  rw [reassoc_of% ((homParityShiftDatum (k := k) r).hom_naturality hx4)]
  simp only [Linear.smul_comp, Category.assoc]
  have hq := congrArg (fun f => f ▷ G)
    ((homParityShiftDatum (k := k) q).hom_naturality hx2)
  have hp := congrArg (fun f => (f ▷ F) ▷ G)
    ((homParityShiftDatum (k := k) p).hom_naturality hx0)
  simp only [TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.smul_whiskerRight (R := k)] at hq hp
  rw [reassoc_of% hq]
  simp only [Linear.comp_smul, Linear.smul_comp, smul_smul, Category.assoc]
  rw [hp]
  simp only [Linear.comp_smul, smul_smul, add_mul, Supercategory.sign_add]
  congr 1
  ring

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- Move a homogeneous comparison past a right dot, retaining its scalar. -/
theorem pureReservoir_exchange_dot {a b d : B} {A A' : a ⟶ b}
    {F : b ⟶ d} {η : A ⟶ A'} {y : End F} {p t : ZMod 2}
    (hη : η ∈ parity (R := k) A A' p) (hy : y ∈ parity (R := k) F F t) :
    A ◁ y ≫ η ▷ F = sign k (p * t) • (η ▷ F ≫ A' ◁ y) := by
  have h := TwoSupercategory.super_interchange (R := k) hη hy
  rw [koszulSign_smul (R := k)] at h
  have h' := congrArg (sign k (p * t) • ·) h
  simpa only [smul_smul, Supercategory.sign_mul_self, one_smul] using h'.symm

/-- The middle reservoir dot through all three shift removals. -/
theorem pureReservoir_shift_middle {a b d e f : B}
    (Z : a ⟶ b) (E : b ⟶ d) (F : d ⟶ e) (G : e ⟶ f)
    (p q r t : ZMod 2) (y : End F) (hy : y ∈ parity (R := k) F F t) :
    (homParityShift (k := k) r).map
      ((homParityShift (k := k) q).map
        ((homParityShift (k := k) p).obj (Z ≫ E) ◁ y) ▷ G) ≫
      (reservoirShiftTripleIso Z E F G p q r).hom =
    sign k ((p + q + r) * t) • ((reservoirShiftTripleIso Z E F G p q r).hom ≫
      ((Z ≫ E) ◁ y) ▷ G) := by
  have hy0 := TwoSupercategory.whiskerLeft_mem (R := k)
    ((homParityShift (k := k) p).obj (Z ≫ E)) hy
  have hy1 := IsSuperfunctor.map_mem (F := homParityShift (k := k) q) hy0
  have hy2 := TwoSupercategory.whiskerRight_mem (R := k) G hy1
  have hq := congrArg (fun f => f ▷ G)
    ((homParityShiftDatum (k := k) q).hom_naturality hy0)
  have hp := congrArg (fun f => f ▷ G) (pureReservoir_exchange_dot
    ((homParityShiftDatum (k := k) p).hom_mem (Z ≫ E)) hy)
  simp only [TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.smul_whiskerRight (R := k)] at hq hp
  simp only [reservoirShiftTripleIso, Iso.trans_hom, whiskerRightIso, Category.assoc]
  rw [reassoc_of% ((homParityShiftDatum (k := k) r).hom_naturality hy2)]
  simp only [Linear.smul_comp, Category.assoc]
  rw [reassoc_of% hq]
  simp only [Linear.comp_smul, Linear.smul_comp, smul_smul, Category.assoc]
  rw [hp]
  simp only [Linear.comp_smul, smul_smul, add_mul, Supercategory.sign_add]
  congr 1
  ring

/-- The final reservoir dot through all three shift removals. -/
theorem pureReservoir_shift_last {a b d e f : B}
    (Z : a ⟶ b) (E : b ⟶ d) (F : d ⟶ e) (G : e ⟶ f)
    (p q r t : ZMod 2) (z : End G) (hz : z ∈ parity (R := k) G G t) :
    (homParityShift (k := k) r).map
      ((homParityShift (k := k) q).obj
        ((homParityShift (k := k) p).obj (Z ≫ E) ≫ F) ◁ z) ≫
      (reservoirShiftTripleIso Z E F G p q r).hom =
    sign k ((p + q + r) * t) • ((reservoirShiftTripleIso Z E F G p q r).hom ≫
      ((Z ≫ E) ≫ F) ◁ z) := by
  have hz0 := TwoSupercategory.whiskerLeft_mem (R := k)
    ((homParityShift (k := k) q).obj ((homParityShift (k := k) p).obj (Z ≫ E) ≫ F)) hz
  have hq := pureReservoir_exchange_dot
    ((homParityShiftDatum (k := k) q).hom_mem
      ((homParityShift (k := k) p).obj (Z ≫ E) ≫ F)) hz
  have hp := pureReservoir_exchange_dot
    (TwoSupercategory.whiskerRight_mem (R := k) F
      ((homParityShiftDatum (k := k) p).hom_mem (Z ≫ E))) hz
  simp only [reservoirShiftTripleIso, Iso.trans_hom, whiskerRightIso, Category.assoc]
  rw [reassoc_of% ((homParityShiftDatum (k := k) r).hom_naturality hz0)]
  simp only [Linear.smul_comp, Category.assoc]
  rw [reassoc_of% hq]
  simp only [Linear.comp_smul, Linear.smul_comp, smul_smul, Category.assoc]
  rw [hp]
  simp only [Linear.comp_smul, smul_smul, add_mul, Supercategory.sign_add]
  congr 1
  ring

/-- Fully normalized first reservoir dot. -/
theorem pureReservoir_total_first {a b d e f : B}
    (Z : a ⟶ b) (E : b ⟶ d) (F : d ⟶ e) (G : e ⟶ f)
    (p q r t : ZMod 2) (x : End E) (hx : x ∈ parity (R := k) E E t) :
    (homParityShift (k := k) r).map
      ((homParityShift (k := k) q).map
        ((homParityShift (k := k) p).map (Z ◁ x) ▷ F) ▷ G) =
    sign k ((p + q + r) * t) • ((reservoirTotalIso Z E F G p q r).hom ≫
      Z ◁ (x ▷ (F ≫ G)) ≫ (reservoirTotalIso Z E F G p q r).inv) := by
  apply (cancel_mono (reservoirTotalIso (k := k) Z E F G p q r).hom).mp
  simp only [Linear.smul_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [reservoirTotalIso, Iso.trans_hom]
  rw [← Category.assoc, pureReservoir_shift_first Z E F G p q r t x hx]
  simp only [Linear.smul_comp, Category.assoc]
  congr 2
  simp only [reservoirTripleIso, Iso.trans_hom, Category.assoc]
  rw [TwoSupercategory.associator_naturality_left_assoc (R := k),
    TwoSupercategory.associator_naturality_middle (R := k)]

/-- Fully normalized middle reservoir dot. -/
theorem pureReservoir_total_middle {a b d e f : B}
    (Z : a ⟶ b) (E : b ⟶ d) (F : d ⟶ e) (G : e ⟶ f)
    (p q r t : ZMod 2) (y : End F) (hy : y ∈ parity (R := k) F F t) :
    (homParityShift (k := k) r).map
      ((homParityShift (k := k) q).map
        ((homParityShift (k := k) p).obj (Z ≫ E) ◁ y) ▷ G) =
    sign k ((p + q + r) * t) • ((reservoirTotalIso Z E F G p q r).hom ≫
      Z ◁ (E ◁ (y ▷ G)) ≫ (reservoirTotalIso Z E F G p q r).inv) := by
  apply (cancel_mono (reservoirTotalIso (k := k) Z E F G p q r).hom).mp
  simp only [Linear.smul_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [reservoirTotalIso, Iso.trans_hom]
  rw [← Category.assoc, pureReservoir_shift_middle Z E F G p q r t y hy]
  simp only [Linear.smul_comp, Category.assoc]
  congr 2
  simp only [reservoirTripleIso, Iso.trans_hom, Category.assoc]
  rw [TwoSupercategory.associator_naturality_middle_assoc (R := k),
    TwoSupercategory.associator_naturality_right (R := k)]

/-- Fully normalized final reservoir dot. -/
theorem pureReservoir_total_last {a b d e f : B}
    (Z : a ⟶ b) (E : b ⟶ d) (F : d ⟶ e) (G : e ⟶ f)
    (p q r t : ZMod 2) (z : End G) (hz : z ∈ parity (R := k) G G t) :
    (homParityShift (k := k) r).map
      ((homParityShift (k := k) q).obj
        ((homParityShift (k := k) p).obj (Z ≫ E) ≫ F) ◁ z) =
    sign k ((p + q + r) * t) • ((reservoirTotalIso Z E F G p q r).hom ≫
      Z ◁ (E ◁ F ◁ z) ≫ (reservoirTotalIso Z E F G p q r).inv) := by
  apply (cancel_mono (reservoirTotalIso (k := k) Z E F G p q r).hom).mp
  simp only [Linear.smul_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [reservoirTotalIso, Iso.trans_hom]
  rw [← Category.assoc, pureReservoir_shift_last Z E F G p q r t z hz]
  simp only [Linear.smul_comp, Category.assoc]
  congr 2
  simp only [reservoirTripleIso, Iso.trans_hom, Category.assoc]
  rw [TwoSupercategory.associator_naturality_right_assoc (R := k),
    TwoSupercategory.associator_naturality_right (R := k)]

section ScalarSupport
include k

/-- Powers of the parity scalar, with the natural exponent explicitly cast. -/
theorem pureReservoir_sign_pow (p : ZMod 2) (n : ℕ) :
    sign k p ^ n = sign k (p * (n : ZMod 2)) := by
  induction n with
  | zero => simp only [pow_zero, Nat.cast_zero, mul_zero, Supercategory.sign_zero]
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_add, Nat.cast_one, mul_add, mul_one,
      Supercategory.sign_add]

omit k in
private theorem supported_parity_zero (pi : ZMod 2) (n : ℕ)
    (hn : pi = 1 → Even n) : pi * (n : ZMod 2) = 0 := by
  rcases parity_eq_zero_or_one pi with rfl | rfl
  · exact zero_mul _
  · obtain ⟨m, hm⟩ := hn rfl
    rw [hm, Nat.cast_add, CharTwo.add_self_eq_zero, mul_zero]

/-- Every supported correction monomial has the repeated-colour parity. -/
theorem pureReservoir_supported_sign (q pi pj : ZMod 2) (n d a : ℕ) (ha : a < n)
    (hn : pi = 1 → Even n) (hd : pj = 1 → Even d) :
    sign k (q * pi) ^ (n - 1 - a) * sign k (q * pj) ^ d * sign k (q * pi) ^ a =
      sign k (q * pi) := by
  have hn' := supported_parity_zero pi n hn
  have hd' := supported_parity_zero pj d hd
  have he : n - 1 - a + a + 1 = n := by omega
  have he' := congrArg (fun n : ℕ => (n : ZMod 2)) he
  simp only [Nat.cast_add, Nat.cast_one] at he'
  have hsum : pi * (((n - 1 - a : ℕ) : ZMod 2) + (a : ZMod 2)) = pi := by
    have h := hn'
    rw [← he'] at h
    linear_combination (norm := ring_nf) h
    simp only [mul_two, CharTwo.add_self_eq_zero, neg_zero]
  simp only [pureReservoir_sign_pow (k := k), ← Supercategory.sign_add]
  congr 1
  calc
    q * pi * ((n - 1 - a : ℕ) : ZMod 2) + q * pj * (d : ZMod 2) + q * pi * (a : ZMod 2) =
      q * (pi * (((n - 1 - a : ℕ) : ZMod 2) + (a : ZMod 2)) + pj * (d : ZMod 2)) := by ring
    _ = q * pi := by rw [hsum, hd', add_zero]

variable {R : Type*} [Ring R] [Algebra k R]

/-- Supported ordered monomials acquire exactly one uniform scalar. -/
theorem pureReservoir_monomial_scalars (x y z : R) (q pi pj : ZMod 2)
    (n d a : ℕ) (ha : a < n) (hn : pi = 1 → Even n) (hd : pj = 1 → Even d) :
    (sign k (q * pi) • x) ^ (n - 1 - a) * (sign k (q * pj) • y) ^ d *
      (sign k (q * pi) • z) ^ a = sign k (q * pi) • (x ^ (n - 1 - a) * y ^ d * z ^ a) := by
  simp only [smul_pow, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  calc
    _ = sign k (q * pi) ^ (n - 1 - a) * sign k (q * pj) ^ d * sign k (q * pi) ^ a := by ring
    _ = _ := pureReservoir_supported_sign (k := k) q pi pj n d a ha hn hd

/-- The full scalar comparison keeps both finite coefficient sums. -/
theorem pureReservoir_polynomial_scalars (i j : I) (x y z : R) (q : ZMod 2) :
    (∑ a ∈ Finset.range (D.dn i j),
      (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
        ((sign k (q * D.parity i) • x) ^ (D.dn i j - 1 - a) *
          (sign k (q * D.parity i) • z) ^ a)) +
    (∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
      (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
        ((sign k (q * D.parity i) • x) ^ (b - 1 - a) *
          (sign k (q * D.parity j) • y) ^ d * (sign k (q * D.parity i) • z) ^ a)) =
    sign k (q * D.parity i) • ((∑ a ∈ Finset.range (D.dn i j),
      (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
        (x ^ (D.dn i j - 1 - a) * z ^ a)) +
    ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
      (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
        (x ^ (b - 1 - a) * y ^ d * z ^ a)) := by
  classical
  rw [smul_add]
  simp only [Finset.smul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro a ha
    have h := pureReservoir_monomial_scalars (k := k) x y z q (D.parity i) (D.parity j)
      (D.dn i j) 0 a (Finset.mem_range.mp ha)
      (RepeatedOuterQCorrection.outer_degree_even i j) (fun _ => ⟨0, rfl⟩)
    simp only [pow_zero, mul_one] at h
    rw [h, smul_comm]
  · apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hs : Sc.s i j b d = 0
    · simp only [hs, mul_zero, zero_smul, smul_zero]
    · rw [pureReservoir_monomial_scalars (k := k) x y z q (D.parity i) (D.parity j)
        b d a (Finset.mem_range.mp ha) (RepeatedOuterQCorrection.supported_outer_even Sc i j b d hs)
        (RepeatedOuterQCorrection.supported_inner_even Sc i j b d hs), smul_comm]

end ScalarSupport

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- Algebra maps carry the full reservoir factor correction to its ordered dot polynomial. -/
theorem pureReservoir_factor_polynomial (P : ProbeReservoir k B D Sc) (i j : I)
    {a b d e : X} (hi : a + D.α i = b) (hj : b + D.α j = d) (hk : d + D.α i = e)
    {R : Type*} [Ring R] [Algebra k R]
    (φ : End (P.W.E i hi ≫ P.W.E j hj ≫ P.W.E i hk) →ₐ[k] R) :
    let x := φ (End.of (P.W.dot i hi ▷ (P.W.E j hj ≫ P.W.E i hk)))
    let y := φ (End.of (P.W.E i hi ◁ (P.W.dot j hj ▷ P.W.E i hk)))
    let z := φ (End.of (P.W.E i hi ◁ P.W.E j hj ◁ P.W.dot i hk))
    φ (P.repeatedOuterReservoirCorrection i j hi hj hk) =
      (∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (z ^ (D.dn i j - 1 - a) * x ^ a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (z ^ (b - 1 - a) * y ^ d * x ^ a) := by
  classical
  dsimp only
  have hl {a b d : B} (E : a ⟶ b) {F : b ⟶ d} (x : End F) (n : ℕ) :
      E ◁ (x ^ n) = (End.of (E ◁ x)) ^ n := by
    rw [whiskerLeft_rouquierPower (k := k), rouquierPower_eq_pow]
  have hr {a b d : B} {E : a ⟶ b} (x : End E) (F : b ⟶ d) (n : ℕ) :
      (x ^ n) ▷ F = (End.of (x ▷ F)) ^ n := by
    rw [whiskerRight_rouquierPower (k := k), rouquierPower_eq_pow]
  simp only [repeatedOuterReservoirCorrection, rouquierPower_eq_pow, hl, hr,
    ← End.mul_def, map_add, map_sum, map_smul, map_mul, map_pow]

variable (P : ProbeReservoir k B D Sc) (ν : X) (i j : I) (s : Sector I)
  (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (h0 : StepValid (true, i) false s)
  (h1 : StepValid (true, j) false (nextSector (true, i) false s))
  (h2 : StepValid (true, i) false (nextSector (true, j) false (nextSector (true, i) false s)))

/-- The literal X dot at an arbitrary transported endpoint. -/
theorem repeatedOuterPureReservoir_dotX_heq {t : Sector I}
    (hs : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) false s)) = t)
    (Z : P.H t) :
    HEq (dotEntry (P.swappedGens c L) ν [] i [up j, up i]
      (SPath.three false false false h0 h1 h2 hs) Z)
      (P.dotDiag i false s h0 ((P.step (true, j) false _ h1).obj ((P.step (true, i) false _ h2).obj ((P.castH hs).obj Z)))) := by
  subst hs
  unfold dotEntry
  refine (heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [] (SKM.Shape.dot i) [up j, up i]) (.nil s)
    (.cons _ false _ h0 (.nil _)) (.cons _ false _ h0 (.nil _)) (SPath.two false false h1 h2 rfl) _ _ rfl rfl Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (P.dotImage_reservoir i (SKM.wt D ν [up j, up i]) s h0 h0 _)

/-- The literal Y dot at an arbitrary transported endpoint. -/
theorem repeatedOuterPureReservoir_dotY_heq {t : Sector I}
    (hs : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) false s)) = t)
    (Z : P.H t) :
    HEq (dotEntry (P.swappedGens c L) ν [up i] j [up i]
      (SPath.three false false false h0 h1 h2 hs) Z)
      ((P.step (true, i) false s h0).map (P.dotDiag j false _ h1 ((P.step (true, i) false _ h2).obj ((P.castH hs).obj Z)))) := by
  subst hs
  unfold dotEntry
  refine (heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [up i] (SKM.Shape.dot j) [up i]) (.cons _ false s h0 (.nil _))
    (.cons _ false _ h1 (.nil _)) (.cons _ false _ h1 (.nil _)) (.cons _ false _ h2 (.nil _)) _ _ rfl rfl Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (congrArg (P.step (true, i) false s h0).map
    (P.dotImage_reservoir j (SKM.wt D ν [up i]) (nextSector (true, i) false s) h1 h1
      ((P.step (true, i) false _ h2).obj Z)))

/-- The literal Z dot at an arbitrary transported endpoint. -/
theorem repeatedOuterPureReservoir_dotZ_heq {t : Sector I}
    (hs : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) false s)) = t)
    (Z : P.H t) :
    HEq (dotEntry (P.swappedGens c L) ν [up i, up j] i []
      (SPath.three false false false h0 h1 h2 hs) Z)
      ((P.step (true, i) false s h0).map ((P.step (true, j) false _ h1).map (P.dotDiag i false _ h2 ((P.castH hs).obj Z)))) := by
  subst hs
  unfold dotEntry
  refine (heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [up i, up j] (SKM.Shape.dot i) []) (SPath.two false false h0 h1 rfl)
    (.cons _ false _ h2 (.nil _)) (.cons _ false _ h2 (.nil _)) (.nil _) _ _ rfl rfl Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (congrArg (fun f => (P.step (true, i) false s h0).map
    ((P.step (true, j) false _ h1).map f))
    (P.dotImage_reservoir i ν (nextSector (true, j) false (nextSector (true, i) false s))
      h2 h2 Z))

private theorem reservoir_polynomial_heq
    {C : Type u} [Category C] [Preadditive C] [Linear k C]
    (i j : I) {A A' : C} (e : A = A')
    {x y z : End A} {x' y' z' : End A'}
    (hx : HEq x x') (hy : HEq y y') (hz : HEq z z') :
    HEq ((∑ a ∈ Finset.range (D.dn i j), (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
        (compPow z a ≫ compPow x (D.dn i j - 1 - a))) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) • (compPow z a ≫ compPow y d ≫ compPow x (b - 1 - a))) ((∑ a ∈ Finset.range (D.dn i j), (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
        (x' ^ (D.dn i j - 1 - a) * z' ^ a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) • (x' ^ (b - 1 - a) * y' ^ d * z' ^ a)) := by
  subst e
  cases hx; cases hy; cases hz
  apply heq_of_eq
  simp only [compPow_eq_pow, End.mul_def]

/-- The reservoir factor polynomial is the literal path-dot correction,
including its content-parity scalar and every finite coefficient sum. -/
theorem repeatedOuterPureReservoir_correction_heq
    (Z : P.H (nextSector (true, i) false (nextSector (true, j) false
      (nextSector (true, i) false s)))) :
    let p := distinctPureReservoirPath (D := D) ν i j i s h0 h1 h2 rfl
    let Θ := reservoirTotalIso (k := k) Z
      (P.W.E i (P.muM_postE i h2)) (P.W.E j (P.muM_postE j h1))
      (P.W.E i (P.muM_postE i h0))
      (homContentShift D i s.1) (homContentShift D j s.1) (homContentShift D i s.1)
    HEq (sign k (homContentShift D i s.1 * (D.parity j * D.parity i)) •
      (Θ.hom ≫ Z ◁ P.repeatedOuterReservoirCorrection i j
        (P.muM_postE i h2) (P.muM_postE j h1) (P.muM_postE i h0) ≫ Θ.inv))
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
  apply heq_of_eq
  let E := P.W.E i (P.muM_postE i h2)
  let F := P.W.E j (P.muM_postE j h1)
  let G := P.W.E i (P.muM_postE i h0)
  let p := homContentShift D i s.1
  let q := homContentShift D j s.1
  let Θ := reservoirTotalIso (k := k) Z E F G p q p
  let φ := (conjAlg (k := k) Θ.symm).comp
    (functorAlg (k := k) (homPre (k := k) Z) (E ≫ F ≫ G))
  have hp : p + q + p = q := by
    rw [add_right_comm, Supercategory.zmod2_add_self, zero_add]
  have hx := eq_of_heq (P.repeatedOuterPureReservoir_dotX_heq ν i j s c L h0 h1 h2 rfl Z)
  have hy := eq_of_heq (P.repeatedOuterPureReservoir_dotY_heq ν i j s c L h0 h1 h2 rfl Z)
  have hz := eq_of_heq (P.repeatedOuterPureReservoir_dotZ_heq ν i j s c L h0 h1 h2 rfl Z)
  have hX : dotEntry (P.swappedGens c L) ν [] i [up j, up i]
      (distinctPureReservoirPath (D := D) ν i j i s h0 h1 h2 rfl) Z =
      sign k (q * D.parity i) • φ (End.of (E ◁ F ◁ P.W.dot i (P.muM_postE i h0))) := by
    refine hx.trans ?_
    have h := pureReservoir_total_last Z E F G p q p (D.parity i)
      (P.W.dot i (P.muM_postE i h0)) (P.W.dot_mem i _)
    rw [hp] at h
    exact h
  have hY : dotEntry (P.swappedGens c L) ν [up i] j [up i]
      (distinctPureReservoirPath (D := D) ν i j i s h0 h1 h2 rfl) Z =
      sign k (q * D.parity j) • φ (End.of (E ◁ (P.W.dot j (P.muM_postE j h1) ▷ G))) := by
    refine hy.trans ?_
    have h := pureReservoir_total_middle Z E F G p q p (D.parity j)
      (P.W.dot j (P.muM_postE j h1)) (P.W.dot_mem j _)
    rw [hp] at h
    exact h
  have hZ : dotEntry (P.swappedGens c L) ν [up i, up j] i []
      (distinctPureReservoirPath (D := D) ν i j i s h0 h1 h2 rfl) Z =
      sign k (q * D.parity i) • φ (End.of (P.W.dot i (P.muM_postE i h2) ▷ (F ≫ G))) := by
    refine hz.trans ?_
    have h := pureReservoir_total_first Z E F G p q p (D.parity i)
      (P.W.dot i (P.muM_postE i h2)) (P.W.dot_mem i _)
    rw [hp] at h
    exact h
  have hscalar : p * (D.parity j * D.parity i) = q * D.parity i := by
    dsimp only [p, q, homContentShift]
    rw [show D.parity i * contentParity D s.1 * (D.parity j * D.parity i) =
      (D.parity i * D.parity i) * (contentParity D s.1 * D.parity j) by ring,
      SKM.zmod2_mul_self]
    ring
  have hpowers := reservoir_polynomial_heq (Sc := Sc) i j rfl
    (heq_of_eq hX) (heq_of_eq hY) (heq_of_eq hZ)
  refine eq_of_heq (HEq.trans ?_ hpowers.symm)
  apply heq_of_eq
  refine Eq.trans ?_ (pureReservoir_polynomial_scalars (Sc := Sc) i j
    (φ (End.of (E ◁ F ◁ P.W.dot i (P.muM_postE i h0))))
    (φ (End.of (E ◁ (P.W.dot j (P.muM_postE j h1) ▷ G))))
    (φ (End.of (P.W.dot i (P.muM_postE i h2) ▷ (F ≫ G)))) q).symm
  change sign k (p * (D.parity j * D.parity i)) • φ _ = _
  rw [hscalar]
  exact congrArg (sign k (q * D.parity i) • ·)
    (P.pureReservoir_factor_polynomial i j (P.muM_postE i h2)
      (P.muM_postE j h1) (P.muM_postE i h0) φ)

include h0 h1 h2 in
/-- The literal diagonal field of `CrossBraid` at any pure-reservoir endpoint. -/
theorem repeatedOuterPureReservoir_braidEq_diag {t : Sector I}
    (ht : nextSector (true, i) false (nextSector (true, j) false
      (nextSector (true, i) false s)) = t)
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
  rw [pureReservoirPath_unique h0 h1 h2 rfl p]
  exact eq_of_heq ((P.repeatedOuterPureReservoir_canonical_heq ν i j s c L hij h0 h1 h2 Z).trans
    (P.repeatedOuterPureReservoir_correction_heq ν i j s c L h0 h1 h2 Z))

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
