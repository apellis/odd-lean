import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterLiteralDiagonal
import Lean.Util.CollectAxioms

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
  (i j : I) (s : Sector I) (hR : StepValid (true, i) false s)
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

/-- Apply the full finite right diagonal identification. -/
theorem separatedOuter_braidRight_obligation (ν : X) (c : P.CrossCoeff Sc)
    (L : P.LeftwardData) (hij : i ≠ j) :
    braidRight (P.swappedGens c L) i j i ν
      (SPath.three true true false trivial trivial hR rfl)
      (SPath.three true true false trivial trivial hR rfl) Z =
      -(P.repeatedOuterMixedSeparatedCoeff i j s hR Z c ≫
        (P.step (true, i) true s trivial).map
          (P.mixedQ j i (nextSector (true, i) true s) hR Z)) :=
  P.separatedOuter_braidRight ν i j s hR Z c L hij
theorem separatedOuter_braidLeft_obligation (ν : X) (c : P.CrossCoeff Sc)
    (L : P.LeftwardData) (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j)
    (hs₀ : nextSector (true, i) true (nextSector (true, j) true s) =
      nextSector (true, j) true (nextSector (true, i) true s))
    (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
      nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true true false trivial trivial hR rfl
    let b : SPath (wd D ν [up j, up i, up i]) s _ :=
      SPath.three true true false trivial trivial hR hs
    braidLeft (P.swappedGens c L) i j i ν n n Z =
      -((crossEntry (P.swappedGens c L) ν [] i j [up i] n b Z ≫
        crossEntry (P.swappedGens c L) ν [] j i [up i] b n Z) ≫
        P.repeatedOuterMixedSeparatedCoeff i j s hR Z c) :=
  P.separatedOuter_braidLeft ν i j s hR Z hs₀ hs c L hc h hij
theorem separatedOuter_native_routes_obligation (ν : X) (c : P.CrossCoeff Sc)
    (L : P.LeftwardData) (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j)
    (hs₀ : nextSector (true, i) true (nextSector (true, j) true s) =
      nextSector (true, j) true (nextSector (true, i) true s))
    (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
      nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :
    (braidLeft (P.swappedGens c L) i j i ν
      (SPath.three true true false trivial trivial hR rfl)
      (SPath.three true true false trivial trivial hR rfl) Z =
      -(qExpr Sc (P.distinctProbeOuterDot i j i s hR Z)
        (P.distinctProbeInnerDot i j i s hR Z) i j ≫
        P.repeatedOuterMixedSeparatedCoeff i j s hR Z c)) ∧
    (braidRight (P.swappedGens c L) i j i ν
      (SPath.three true true false trivial trivial hR rfl)
      (SPath.three true true false trivial trivial hR rfl) Z =
      -(P.repeatedOuterMixedSeparatedCoeff i j s hR Z c ≫
        qExpr Sc (P.distinctProbeSpectatorDot i j i s hR Z)
          (P.distinctProbeInnerDot i j i s hR Z) i j)) :=
  ⟨P.separatedOuter_braidLeft_qExpr ν i j s hR Z hs₀ hs c L hc h hij,
    P.separatedOuter_braidRight_qExpr ν i j s hR Z c L hij⟩
theorem separatedOuter_braidEq_diag_obligation (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j)
    (hs₀ : nextSector (true, i) true (nextSector (true, j) true s) =
      nextSector (true, j) true (nextSector (true, i) true s))
    (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
      nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true true false trivial trivial hR rfl
    braidLeft (P.swappedGens c L) i j i ν n n Z -
      braidRight (P.swappedGens c L) i j i ν n n Z =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] n Z) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] n Z)
              (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] n Z) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [up i] j [up i] n Z) d ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] n Z) (b - 1 - a)) :=
  P.separatedOuter_braidEq_diag ν i j s hR Z c L hc h hij hs₀ hs
include hR in
theorem repeatedOuter_oneReservoir_offDiag_obligation (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) {t : Sector I}
    (e₀ : nextSector (true, i) true (nextSector (true, j) true
      (nextSector (true, i) false s)) = t)
    (e₁ : nextSector (true, i) false (nextSector (true, j) true
      (nextSector (true, i) true s)) = t)
    (p q : SPath (wd D ν [up i, up j, up i]) s t) (W : P.H t) (hpq : p ≠ q) :
    braidLeft (P.swappedGens c L) i j i ν p q W =
      braidRight (P.swappedGens c L) i j i ν p q W :=
  P.repeatedOuter_oneReservoir_offDiag ν i j s hR c L hc h hij e₀ e₁ p q W hpq
theorem separatedOuter_braidEq_diag_transport_obligation (ν : X) {t : Sector I}
    (e : nextSector (true, i) false (nextSector (true, j) true (nextSector (true, i) true s)) = t)
    (W : P.H t) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true true false trivial trivial hR e
    braidLeft (P.swappedGens c L) i j i ν n n W -
      braidRight (P.swappedGens c L) i j i ν n n W =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] n W) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] n W)
              (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] n W) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [up i] j [up i] n W) d ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] n W) (b - 1 - a)) :=
  P.separatedOuter_braidEq_diag_transport ν i j s hR e W c L hc h hij
end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.separatedOuter_braidRight_obligation
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.separatedOuter_braidEq_diag_transport_obligation
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.repeatedOuter_oneReservoir_offDiag_obligation

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterLiteralDiagonal
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == owner then
      for name in env.header.moduleData[i]!.constNames do
        count := count + 1
        let axioms ← Lean.collectAxioms name
        for axiomName in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
  if count == 0 then
    throwError "Missing owned module {owner}"
  logInfo m!"{owner}: audited {count} declarations; standard axioms only"
