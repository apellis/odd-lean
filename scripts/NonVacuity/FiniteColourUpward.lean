import OddMath.QuiverHecke.FiniteColourUpward
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke OddMath.SKM
open scoped Classical
private def oddDatum : Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else 0
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else 0)
    split <;> simp

private def params : Scalars oddDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

private def bubbles : CScalars params where
  c := fun _ _ => 1
  shift := fun _ _ _ => by simp [params]

/-- Upward injectivity on every finite restriction of a two-colour word pair gives
upward injectivity for the datum itself; a conditional consumer of the detection theorem. -/
example (μ : Bool → ℤ)
    (h : ∀ (J : Finset Bool) (tJ t'J : List J), tJ.map Subtype.val = [false, true] →
      t'J.map Subtype.val = [true, false] →
      Function.Injective (upwardCoefficientMap (oddDatum.restrictColours J)
        (params.restrictColours oddDatum J) (bubbles.restrictColours oddDatum J params)
        μ tJ t'J)) :
    Function.Injective (upwardCoefficientMap oddDatum params bubbles μ
      [false, true] [true, false]) :=
  upwardCoefficientMap_injective_of_restrictColours oddDatum params bubbles μ _ _ h

/-- Every coefficient-extended morphism of the two-colour datum is a finite combination of
generator words and normal forms; no hypothesis. -/
example (x : coefficientObj oddDatum params [false, true] ⟶
    coefficientObj oddDatum params [true, false]) :
    ∃ L : List (ℚ × List (SYMGen oddDatum) × NFIdx [false, true] [true, false]),
      x = (L.map fun q => q.1 • sourceCoefficientHom oddDatum params
        ((q.2.1.map (SYM.ι oddDatum ℚ)).prod) q.2.2.nf).sum :=
  exists_list_eq oddDatum params _ _ x

/-- The inclusion of coefficient-extended Hom spaces of the one-colour restriction. -/
example : (coefficientObj (oddDatum.restrictColours {true}) (params.restrictColours oddDatum {true})
      [⟨true, Finset.mem_singleton_self _⟩] ⟶
        coefficientObj (oddDatum.restrictColours {true}) (params.restrictColours oddDatum {true})
          [⟨true, Finset.mem_singleton_self _⟩]) →ₗ[ℚ]
      (coefficientObj oddDatum params [true] ⟶ coefficientObj oddDatum params [true]) :=
  coefficientInclude oddDatum params {true} _ _

#print axioms upwardCoefficientMap_injective_of_restrictColours
#print axioms exists_list_eq
#print axioms coefficientInclude_source

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.FiniteColourUpward then
      for name in env.header.moduleData[i]!.constNames do
        for axiomName in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations found"
  logInfo m!"Audited {count} owned declarations: standard axioms only"
