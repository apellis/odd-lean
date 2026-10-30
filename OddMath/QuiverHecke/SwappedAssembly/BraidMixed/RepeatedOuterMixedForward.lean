/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterMixedDiagonal

/-! # Coefficient-bearing repeated-outer finite routes -/
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

private lemma forward_route {C : Type u} [Category C] [Preadditive C]
    {A B V T : C} (f : A ⟶ B) (g : B ⟶ B) (r : B ⟶ T)
    (h : B ⟶ V) (r' : V ⟶ T) (hr : r = 0) :
    (f ≫ g) ≫ r + (f ≫ h) ≫ r' = (f ≫ h) ≫ r' := by
  rw [hr, Limits.comp_zero, zero_add]

private lemma reverse_signed {k : Type u} [CommRing k]
    {C : Type u} [Category C] [Preadditive C] [Linear k C]
    {A B : C} (f g : A ⟶ B) (ε : k) (hε : ε * ε = 1)
    (h : f = ε • g) : g = ε • f := by
  rw [h, smul_smul, hε, one_smul]

variable (P : ProbeReservoir k B D Sc)

/-- Transport the outer Q factor alone across the unequal probe crossing. -/
theorem preCrossNe_qExpr_outer (i j r : I) (hij : i ≠ j) (s : Sector I)
    (hs : nextSector (true, j) true (nextSector (true, i) true s) =
      nextSector (true, i) true (nextSector (true, j) true s))
    (Z : P.H (nextSector (true, i) true (nextSector (true, j) true s)))
    (θ : End Z) (hθ : θ ∈ parity (R := k) _ _ (D.parity r)) :
    let Z₀ : P.H (nextSector (true, j) true (nextSector (true, i) true s)) := hs ▸ Z
    let x : End ((P.step (true, i) true s trivial).obj ((P.step (true, j) true _ trivial).obj Z₀)) := P.T.dot i (P.muP_preE i s) ▷ (P.step (true, j) true _ trivial).obj Z₀
    let z := (P.step (true, i) true s trivial).map
      ((P.step (true, j) true _ trivial).map ((P.castH hs).map θ))
    let y' := (P.step (true, j) true s trivial).map
      (P.T.dot i (P.muP_preE i (nextSector (true, j) true s)) ▷ Z)
    let z' := (P.step (true, j) true s trivial).map
      ((P.step (true, i) true _ trivial).map θ)
    qExpr Sc x z i r ≫ P.preCrossNe i j s hs Z =
      P.preCrossNe i j s hs Z ≫ qExpr Sc y' z' i r := by
  dsimp only
  symm
  apply comp_qExpr (Sc := Sc) _ _ _ _ _ i r
    (zsign k (D.parity i * D.parity j))
    (zsign k (D.parity i * D.parity j * D.parity r))
  · exact reverse_signed (C := P.H s) _ _ _ (zsign_mul_self' _)
      (P.preCrossNe_slideL i j hij s hs Z)
  · have h := (P.preCrossNe_supernatural i j s hs).naturality hθ
    simp only [Functor.comp_map, sign_eq_zsign] at h
    exact reverse_signed (C := P.H s) _ _ _ (zsign_mul_self' _) h
  · exact zsign_pow_of_mul_eq_zero (k := k) (D.parity i) (D.parity j)
  · simpa only [mul_comm (D.parity r)] using
      zsign_pow_of_mul_eq_zero (k := k) (D.parity r) (D.parity i * D.parity j)

variable (G : P.Generators)
  (ν : X) (i j : I) (s : Sector I) (hR : StepValid (true, i) false s)
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

/-- The full forward off-diagonal left sum has one surviving route.
The middle equal crossing is the prescribed coefficient-square entry. -/
theorem repeatedOuter_forward_left_route (hij : i ≠ j) :
    let m : SPath (wd D ν [up i, up j, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three false true true hR trivial trivial hs
    let n : SPath (wd D ν [up i, up j, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three true true false trivial trivial hR rfl
    let a : SPath (wd D ν [up j, up i, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three true false true trivial hR trivial hs
    let b : SPath (wd D ν [up j, up i, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three true true false trivial trivial hR hs
    braidLeft G i j i ν m n Z =
      (crossEntry G ν [] i j [up i] m a Z ≫
        crossEntry G ν [up j] i i [] a b Z) ≫
          crossEntry G ν [] j i [up i] b n Z := by
  classical
  dsimp only
  have hr := P.repeatedOuter_braidLeft_row G ν i j s hR hs Z hij
    (SPath.three true true false trivial trivial hR rfl)
  have hz := P.crossEntry_left_three_zero G ν j i i true false true true true false
    (by decide) trivial hR trivial trivial trivial hR hs rfl Z
  exact hr.trans (forward_route _ _ _ _ _ hz)

/-- The full forward off-diagonal right sum has one surviving route. -/
theorem repeatedOuter_forward_right_route (hij : i ≠ j) :
    let m : SPath (wd D ν [up i, up j, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three false true true hR trivial trivial hs
    let n : SPath (wd D ν [up i, up j, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three true true false trivial trivial hR rfl
    let a : SPath (wd D ν [up i, up i, up j]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three false true true hR trivial trivial rfl
    let b : SPath (wd D ν [up i, up i, up j]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three true false true trivial hR trivial rfl
    braidRight G i j i ν m n Z =
      (crossEntry G ν [up i] j i [] m a Z ≫
        crossEntry G ν [] i i [up j] a b Z) ≫
          crossEntry G ν [up i] i j [] b n Z := by
  classical
  dsimp only
  have hr := P.repeatedOuter_braidRight_row G ν i j s hR hs Z hij
    (SPath.three true true false trivial trivial hR rfl)
  have hz := crossEntry_right_eq_zero G ν i i j false true Bool.false_ne_true
    hR trivial (SPath.two true true trivial trivial rfl)
    (SPath.two true false trivial hR rfl) Z
  exact hr.trans (forward_route _ _ _ _ _ hz)

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
