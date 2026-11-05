/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Generators.CrossCoeffExistence
import OddMath.SKM.RouquierHomPostInverseUnits

/-! # Source denominator norms for the reservoir mixed mate

These are the three literal source-unit inputs of the post-side mixed mate.
They require no common nilpotence exponent on a reservoir weight fibre.
The previous whole-dot unit/nilpotence hypotheses remain sufficient.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe r u v w

section Source
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B} (E : a ⟶ b) {E' : c ⟶ d} {F' : d ⟶ c}
  (A : SuperAdjunction (k := k) E' F') (κ : ZMod 2) (H : b ⟶ d)

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in

/-- Signed reversal preserves nilpotence of a homogeneous endomorphism. -/
theorem isNilpotent_rightTranspose_of_mem {p : ZMod 2} {y : End E'}
    (hy : y ∈ parity (R := k) _ _ p) (hn : IsNilpotent y) :
    IsNilpotent (show End F' from SuperAdjunction.rightTranspose A A y) := by
  obtain ⟨n, hn⟩ := hn
  have hs := SuperAdjunction.rightTranspose_power A hy n
  rw [rouquierPower_eq_pow, hn, rouquierPower_eq_pow] at hs
  have hz : SuperAdjunction.rightTranspose A A (0 : End E') = 0 :=
    (SuperAdjunction.rightTransposeLinear A A).map_zero
  rw [hz] at hs
  let t : End F' := SuperAdjunction.rightTranspose A A y
  let s : ℤ := koszulSign p p ^ (n.choose 2)
  have hss : s * s = 1 := by
    dsimp [s]
    rw [← mul_pow, koszulSign_mul_self, one_pow]
  refine ⟨n, ?_⟩
  change t ^ n = 0
  calc
    _ = s • (s • t ^ n) := by rw [smul_smul, hss, one_smul]
    _ = 0 := by rw [← hs]; simp

/-- The source pre dot is a functorial image of the probe dot. -/
theorem mixedPostSourcePreDot_isUnit {x : End E} (hu : IsUnit x) :
    IsUnit (mixedPostSourcePreDot (k := k) E κ H (F' := F') x) :=
  hu.map ((homPost (k := k) ((homParityShift (k := k) κ).obj H ≫ F')).mapEnd E)

/-- The source post dot is a functorial image of the actual right transpose. -/
theorem mixedPostSourcePostDot_isNilpotent {p : ZMod 2} {y : End E'}
    (hy : y ∈ parity (R := k) _ _ p) (hn : IsNilpotent y) :
    IsNilpotent (mixedPostSourcePostDot (k := k) E κ H A y) := by
  obtain ⟨n, hn⟩ := isNilpotent_rightTranspose_of_mem A hy hn
  refine ⟨n, ?_⟩
  rw [← rouquierPower_eq_pow] at hn
  unfold mixedPostSourcePostDot
  rw [whiskerLeft_rouquierPower (k := k), rouquierPower_eq_pow,
    whiskerLeft_rouquierPower (k := k), hn]
  rw [whiskerLeft_zero' (k := k), whiskerLeft_zero' (k := k)]

/-- Whole-dot nilpotence is sufficient for the even source denominator. -/
theorem mixedPostSource_difference_isUnit_of_nilpotent {x : End E} (hx : x ∈ parity (R := k) _ _ 0)
    {p : ZMod 2} {y : End E'} (hy : y ∈ parity (R := k) _ _ p)
    (hu : IsUnit x) (hn : IsNilpotent y) :
    IsUnit (mixedPostSourcePreDot (k := k) E κ H (F' := F') x -
      mixedPostSourcePostDot (k := k) E κ H A y) := by
  have hu' := mixedPostSourcePreDot_isUnit (k := k) (F' := F') E κ H hu
  have hn' := mixedPostSourcePostDot_isNilpotent E A κ H hy hn
  have hc := (commute_mixedPostSource E A κ H hx (y := y)).symm
  simpa only [sub_eq_add_neg, add_comm] using
    hn'.neg.isUnit_add_left_of_commute hu' hc.neg_left

/-- Whole-dot nilpotence is sufficient for both odd source square norms. -/
theorem mixedPostSource_square_norms_isUnit_of_nilpotent {x : End E} (hx : x ∈ parity (R := k) _ _ 1)
    {y : End E'} (hy : y ∈ parity (R := k) _ _ 1)
    (hu : IsUnit x) (hn : IsNilpotent y) :
    IsUnit (mixedPostSourcePreDot (k := k) E κ H (F' := F') x ^ 2 -
      mixedPostSourcePostDot (k := k) E κ H A y ^ 2) ∧
    IsUnit (mixedPostSourcePreDot (k := k) E κ H (F' := F') x ^ 2 +
      mixedPostSourcePostDot (k := k) E κ H A y ^ 2) := by
  let a := mixedPostSourcePreDot (k := k) E κ H (F' := F') x
  let b := mixedPostSourcePostDot (k := k) E κ H A y
  have ha : IsUnit a := mixedPostSourcePreDot_isUnit (k := k) E κ H hu
  have hb : IsNilpotent b := mixedPostSourcePostDot_isNilpotent E A κ H hy hn
  have hg := TwoSupercategory.whiskerLeft_mem (R := k)
    ((homParityShift (k := k) κ).obj H) (SuperAdjunction.rightTranspose_mem A A hy)
  have hab : b * a = -(a * b) := by
    have hh := TwoSupercategory.super_interchange (R := k) hx hg
    have hz : koszulSign (1 : ZMod 2) 1 = -1 := by simp [koszulSign]
    rw [hz, neg_one_zsmul] at hh
    exact hh
  have hc := OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.commute_sq_of_anticommute hab
  have hcc : Commute (b ^ 2) (a ^ 2) := by
    simpa only [pow_two] using hc.2.mul_left hc.2
  constructor
  · have hh := (hb.pow_of_pos two_ne_zero).neg.isUnit_add_left_of_commute
      (ha.pow 2) hcc.neg_left
    simpa only [sub_eq_add_neg, add_comm] using hh
  · have hh := (hb.pow_of_pos two_ne_zero).isUnit_add_left_of_commute
      (ha.pow 2) hcc
    simpa only [add_comm] using hh

end Source
end OddMath.SKM

namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)

/-- Literal transposed source norms, independently of any whole-fibre dot exponent. -/
structure CrossTransposeNormUnits : Prop where
  even : ∀ (i : I), D.parity i = 0 → ∀ {xP yP xW yW : X}
    (hP : xP + D.α i = yP) (hW : xW + D.α i = yW) (κ : ZMod 2)
    (H : P.T.obj yP ⟶ P.W.obj yW),
    IsUnit (mixedPostSourcePreDot (k := k) (P.T.E i hP) κ H (F' := P.W.F i hW) (P.T.dot i hP) -
      mixedPostSourcePostDot (k := k) (P.T.E i hP) κ H (P.W.adj i hW) (P.W.dot i hW))
  odd_sub : ∀ (i : I), D.parity i = 1 → ∀ {xP yP xW yW : X}
    (hP : xP + D.α i = yP) (hW : xW + D.α i = yW) (κ : ZMod 2)
    (H : P.T.obj yP ⟶ P.W.obj yW),
    IsUnit (mixedPostSourcePreDot (k := k) (P.T.E i hP) κ H (F' := P.W.F i hW) (P.T.dot i hP) ^ 2 -
      mixedPostSourcePostDot (k := k) (P.T.E i hP) κ H (P.W.adj i hW) (P.W.dot i hW) ^ 2)
  odd_add : ∀ (i : I), D.parity i = 1 → ∀ {xP yP xW yW : X}
    (hP : xP + D.α i = yP) (hW : xW + D.α i = yW) (κ : ZMod 2)
    (H : P.T.obj yP ⟶ P.W.obj yW),
    IsUnit (mixedPostSourcePreDot (k := k) (P.T.E i hP) κ H (F' := P.W.F i hW) (P.T.dot i hP) ^ 2 +
      mixedPostSourcePostDot (k := k) (P.T.E i hP) κ H (P.W.adj i hW) (P.W.dot i hW) ^ 2)

/-- The former whole-dot assumptions imply the precise source norm inputs. -/
theorem CrossTransposeNormUnits.of_factor
    (hT : ∀ (i : I) {x y : X} (h : x + D.α i = y),
      IsUnit (show End (P.T.E i h) from P.T.dot i h))
    (hW : ∀ (i : I) {x y : X} (h : x + D.α i = y),
      IsNilpotent (show End (P.W.E i h) from P.W.dot i h)) :
    P.CrossTransposeNormUnits := by
  constructor
  · intro i hi xP yP xW yW hP hR κ H
    exact mixedPostSource_difference_isUnit_of_nilpotent (P.T.E i hP) (P.W.adj i hR) κ H
      (hi ▸ P.T.dot_mem i hP) (P.W.dot_mem i hR) (hT i hP) (hW i hR)
  · intro i hi xP yP xW yW hP hR κ H
    exact (mixedPostSource_square_norms_isUnit_of_nilpotent (P.T.E i hP) (P.W.adj i hR) κ H
      (hi ▸ P.T.dot_mem i hP) (hi ▸ P.W.dot_mem i hR) (hT i hP) (hW i hR)).1
  · intro i hi xP yP xW yW hP hR κ H
    exact (mixedPostSource_square_norms_isUnit_of_nilpotent (P.T.E i hP) (P.W.adj i hR) κ H
      (hi ▸ P.T.dot_mem i hP) (hi ▸ P.W.dot_mem i hR) (hT i hP) (hW i hR)).2

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
