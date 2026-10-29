/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctQTransport
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Cross
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctProbeDots
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctProbeSector

/-! # Unequal probe crossing transport of two Q factors

The spectator morphism is homogeneous of the reservoir colour. Its transport
is derived from supernaturalness of the prescribed probe crossing.
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

/-- The unequal probe crossing transports both different Q factors with the same
spectator. Neither the crossing nor either polynomial is cancelled. -/
theorem preCrossNe_qExpr_pair (i j r : I) (hij : i ≠ j) (s : Sector I)
    (hs : nextSector (true, j) true (nextSector (true, i) true s) =
      nextSector (true, i) true (nextSector (true, j) true s))
    (Z : P.H (nextSector (true, i) true (nextSector (true, j) true s)))
    (θ : End Z) (hθ : θ ∈ parity (R := k) _ _ (D.parity r)) :
    let Z₀ : P.H (nextSector (true, j) true (nextSector (true, i) true s)) := hs ▸ Z
    let x : End ((P.step (true, i) true s trivial).obj ((P.step (true, j) true _ trivial).obj Z₀)) := P.T.dot i (P.muP_preE i s) ▷ (P.step (true, j) true _ trivial).obj Z₀
    let y : End ((P.step (true, i) true s trivial).obj ((P.step (true, j) true _ trivial).obj Z₀)) := (P.step (true, i) true s trivial).map (P.T.dot j (P.muP_preE j (nextSector (true, i) true s)) ▷ Z₀)
    let z := (P.step (true, i) true s trivial).map
      ((P.step (true, j) true _ trivial).map ((P.castH hs).map θ))
    let x' := P.T.dot j (P.muP_preE j s) ▷ (P.step (true, i) true _ trivial).obj Z
    let y' := (P.step (true, j) true s trivial).map (P.T.dot i (P.muP_preE i (nextSector (true, j) true s)) ▷ Z)
    let z' := (P.step (true, j) true s trivial).map
      ((P.step (true, i) true _ trivial).map θ)
    qExpr Sc x z i r ≫ qExpr Sc y z j r ≫ P.preCrossNe i j s hs Z =
      P.preCrossNe i j s hs Z ≫ qExpr Sc x' z' j r ≫ qExpr Sc y' z' i r := by
  dsimp only
  apply qExpr_pair_swap_transport Sc
  · exact P.preCrossNe_slideL i j hij s hs Z
  · have h := P.preCrossNe_slideR i j hij s hs Z
    rw [h, smul_smul, zsign_mul_self', one_smul]
  · have h := (P.preCrossNe_supernatural i j s hs).naturality hθ
    have he : sign k (D.parity i * D.parity j * D.parity r) =
        zsign k (D.parity i * D.parity j * D.parity r) := by
      generalize D.parity i * D.parity j * D.parity r = p
      fin_cases p <;> simp [sign, zsign]
    simpa only [Functor.comp_map, he] using h
  · have h := TwoSupercategory.super_interchange (R := k)
      (P.T.dot_mem j (P.muP_preE j s))
      (TwoSupercategory.whiskerRight_mem Z (P.T.dot_mem i (P.muP_preE i _)))
    simpa only [step, homContentPreE, homPre, koszulSign_smul_eq_zsign (k := k)] using h
  · have h := TwoSupercategory.super_interchange (R := k)
      (P.T.dot_mem j (P.muP_preE j s))
      (TwoSupercategory.whiskerLeft_mem (P.T.E i (P.muP_preE i _)) hθ)
    simpa only [step, homContentPreE, homPre, koszulSign_smul_eq_zsign (k := k)] using h
  · have h := TwoSupercategory.super_interchange (R := k)
      (P.T.dot_mem i (P.muP_preE i (nextSector (true, j) true s))) hθ
    have hm := congrArg (P.step (true, j) true s trivial).map h
    simpa only [Functor.map_comp, Functor.map_zsmul, step, homContentPreE, homPre,
      TwoSupercategory.whiskerLeft_zsmul (R := k), TwoSupercategory.whiskerLeft_smul (R := k),
      TwoSupercategory.whiskerLeft_comp (R := k),
      koszulSign_smul_eq_zsign (k := k)] using hm

/-- The two Q factors on a probe pair with a homogeneous spectator endomorphism. -/
def probeQPair (i j r : I) (s : Sector I)
    (Y : P.H (nextSector (true, j) true (nextSector (true, i) true s))) (θ : End Y) :=
  qExpr Sc (P.T.dot i (P.muP_preE i s) ▷ (P.step (true, j) true _ trivial).obj Y)
      ((P.step (true, i) true s trivial).map ((P.step (true, j) true _ trivial).map θ)) i r ≫
    qExpr Sc ((P.step (true, i) true s trivial).map
      (P.T.dot j (P.muP_preE j (nextSector (true, i) true s)) ▷ Y))
      ((P.step (true, i) true s trivial).map ((P.step (true, j) true _ trivial).map θ)) j r

/-- Transport the reservoir step and its dot along a sector equality. -/
theorem reservoirDot_cast (r : I) {a b : Sector I} (h : a = b)
    (ha : StepValid (true, r) false a) (hb : StepValid (true, r) false b)
    (Z : P.H (nextSector (true, r) false b)) :
    (P.castH h).obj ((P.step (true, r) false b hb).obj Z) =
      (P.step (true, r) false a ha).obj ((congrArg (nextSector (true, r) false) h) ▸ Z) ∧
    HEq ((P.castH h).map (P.dotDiag r false b hb Z))
      (P.dotDiag r false a ha ((congrArg (nextSector (true, r) false) h) ▸ Z)) := by
  subst h
  exact ⟨rfl, HEq.rfl⟩

/-- A probe-pair Q product preserves a heterogeneous spectator equality. -/
theorem probeQPair_heq (i j r : I) (s : Sector I)
    {Y Y' : P.H (nextSector (true, j) true (nextSector (true, i) true s))}
    (hY : Y = Y') {θ : End Y} {θ' : End Y'} (hθ : HEq θ θ') :
    HEq (P.probeQPair i j r s Y θ) (P.probeQPair i j r s Y' θ') := by
  subst hY
  cases hθ
  rfl

/-- The two-factor mixed weight on `PᵢPⱼRᵣ`. -/
def distinctProbeWeight (i j r : I) (s : Sector I)
    (hR : StepValid (true, r) false s)
    (Z : P.H (nextSector (true, r) false (nextSector (true, j) true (nextSector (true, i) true s)))) :=
  qExpr Sc (P.distinctProbeOuterDot i j r s hR Z) (P.distinctProbeSpectatorDot i j r s hR Z) i r ≫
    qExpr Sc (P.distinctProbeInnerDot i j r s hR Z) (P.distinctProbeSpectatorDot i j r s hR Z) j r

/-- The weight agrees with the homogeneous-spectator formulation. -/
theorem distinctProbeWeight_eq (i j r : I) (s : Sector I)
    (hR : StepValid (true, r) false s)
    (Z : P.H (nextSector (true, r) false (nextSector (true, j) true (nextSector (true, i) true s)))) :
    P.distinctProbeWeight i j r s hR Z =
      P.probeQPair i j r s
        ((P.step (true, r) false (nextSector (true, j) true (nextSector (true, i) true s)) hR).obj Z)
        (P.dotDiag r false (nextSector (true, j) true (nextSector (true, i) true s)) hR Z) := rfl

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
