import OddMath.QuiverHecke.CyclotomicAction.ELVTensorReservoirWords
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.ELVTensorReservoirWords
namespace TwoOdd
private abbrev D := AsymmetricParameters.datum
private abbrev originalSc := AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 20
private def m (i : Bool) : ℕ := if i then 2 else 1
private def Λ : Bool → ℤ := fun _ => 20
private abbrev N := PowerWordContent.powerBound D cutoff L
private def labels : List (Col Bool (Bool → ℤ)) := wd D 0 [up true,up false]
private theorem upward : ∀ a ∈ labels, a.l.1 = true := by simp [labels,wd]
private def path := SPath.reservoirPath labels upward 0
private abbrev ν : List Bool := [false,true]
private abbrev σ : List Bool := ν.reverse
private abbrev β := PowerWordWeight.wordBlock D Λ ν
private def w : ContentCategory D Sc cutoff N β.1 := ⟨⟨ν⟩,rfl⟩
private abbrev chosenEquiv := moduleIsoLinearEquiv
  (Pi.isoApp (TensorReservoirWords.valueChart D Sc m cutoff L Λ Λ path upward) β) w
private theorem powers_high (q : Bool × ℕ) : 16 ≤ L q * SKM.SYM.elementaryWeight D q := by
  have hw : 0 < SKM.SYM.elementaryWeight D q := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  change 16 ≤ 20 * SKM.SYM.elementaryWeight D q
  omega
private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D originalSc σ σ 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 16 ≤ 20)) powers_high (by decide)
private def identityNF : NFIdx σ σ := by
  have hc : Categorification.TypeA.canWord σ.length (1 : Equiv.Perm (Fin σ.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([],1),by simp,by simp,?_⟩
  simp only [List.map_nil,hc,cw,List.reverse_nil,List.nil_append,pl,QuiverHecke.SChain]
private def oddIndex : SKM.SYM.CoefficientIndex D := (0,{⟨false,rfl⟩,⟨true,rfl⟩})
private def occupied : ExtendedAtMost D originalSc σ σ 2 :=
  ⟨extensionBasis D originalSc σ σ (oddIndex,identityNF),
    Submodule.subset_span ⟨(oddIndex,identityNF),by decide,rfl⟩⟩
private def contentVector : (PowerWordWeight.wordAt D Sc cutoff L ν β.1).obj w :=
  powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val
private theorem contentVector_ne_zero : contentVector ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D originalSc σ σ 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc σ σ).ne_zero (oddIndex,identityNF) (congrArg Subtype.val hh)
private def chosenVector := chosenEquiv.symm contentVector
private theorem chosenVector_ne_zero : chosenVector ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have he := congrArg chosenEquiv hz
  simpa only [chosenVector,LinearEquiv.apply_symm_apply,map_zero] using he

/-- Whole actual selected tensor-Hom functors agree, including all source
morphisms, at the proved original-weight presentation. -/
example := TensorReservoirWords.pathHomAt_eq_wordHom D Sc m cutoff L Λ Λ path upward
example := TensorReservoirWords.path_weight D Λ path upward
example {c : Bool →₀ ℕ} (p : SPath labels (0,c) (0,0)) :=
  TensorReservoirWords.pathHom_heq D Sc m cutoff L Λ Λ p upward
example := TensorReservoirWords.pathHomAt_eq_wordHom D Sc m cutoff L Λ Λ
  (SPath.nil (0,0)) (by simp)
example (M N₀ : probeOldWeightSpace D Sc m Λ (-Λ)) (f : M ⟶ N₀) :
    HEq ((TensorReservoirWords.pathHomAt D Sc m cutoff L Λ Λ path upward).map f)
      ((TensorVacuumWords.wordHom D Sc m cutoff L Λ Λ ν).map f) := by
  rw [TensorReservoirWords.pathHomAt_eq_wordHom]
  rfl
example := TensorReservoirWords.valueChart_hom_mem D Sc m cutoff L Λ Λ path upward
example : chosenVector ≠ 0 := chosenVector_ne_zero
example : chosenEquiv chosenVector = contentVector := chosenEquiv.apply_symm_apply _
end TwoOdd
namespace Mixed
private def D : SKM.Datum Bool (Bool → ℤ) :=
  { AsymmetricParameters.datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => AsymmetricParameters.datum.even_of_odd i j rfl }
private def originalSc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 20
private def m (i : Bool) : ℕ := if i then 2 else 1
private def Λ : Bool → ℤ := fun _ => 20
private abbrev N := PowerWordContent.powerBound D cutoff L
private def labels : List (Col Bool (Bool → ℤ)) := wd D 0 [up true,up false]
private theorem upward : ∀ a ∈ labels, a.l.1 = true := by simp [labels,wd]
private def path := SPath.reservoirPath labels upward 0
private abbrev ν : List Bool := [false,true]
private abbrev σ : List Bool := ν.reverse
private abbrev β := PowerWordWeight.wordBlock D Λ ν
private def w : ContentCategory D Sc cutoff N β.1 := ⟨⟨ν⟩,rfl⟩
private abbrev chosenEquiv := moduleIsoLinearEquiv
  (Pi.isoApp (TensorReservoirWords.valueChart D Sc m cutoff L Λ Λ path upward) β) w
private theorem powers_high (q : Bool × ℕ) : 16 ≤ L q * SKM.SYM.elementaryWeight D q := by
  have hw : 0 < SKM.SYM.elementaryWeight D q := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  change 16 ≤ 20 * SKM.SYM.elementaryWeight D q
  omega
private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D originalSc σ σ 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 16 ≤ 20)) powers_high (by decide)
private def identityNF : NFIdx σ σ := by
  have hc : Categorification.TypeA.canWord σ.length (1 : Equiv.Perm (Fin σ.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([],1),by simp,by simp,?_⟩
  simp only [List.map_nil,hc,cw,List.reverse_nil,List.nil_append,pl,QuiverHecke.SChain]
private def oddIndex : SKM.SYM.CoefficientIndex D := (0,{⟨true,rfl⟩})
private def occupied : ExtendedAtMost D originalSc σ σ 2 :=
  ⟨extensionBasis D originalSc σ σ (oddIndex,identityNF),
    Submodule.subset_span ⟨(oddIndex,identityNF),by decide,rfl⟩⟩
private def contentVector : (PowerWordWeight.wordAt D Sc cutoff L ν β.1).obj w :=
  powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val
private theorem contentVector_ne_zero : contentVector ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D originalSc σ σ 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc σ σ).ne_zero (oddIndex,identityNF) (congrArg Subtype.val hh)
private def chosenVector := chosenEquiv.symm contentVector
private theorem chosenVector_ne_zero : chosenVector ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have he := congrArg chosenEquiv hz
  simpa only [chosenVector,LinearEquiv.apply_symm_apply,map_zero] using he

/-- Whole actual selected tensor-Hom functors agree, including all source
morphisms, at the proved original-weight presentation. -/
example := TensorReservoirWords.pathHomAt_eq_wordHom D Sc m cutoff L Λ Λ path upward
example := TensorReservoirWords.path_weight D Λ path upward
example {c : Bool →₀ ℕ} (p : SPath labels (0,c) (0,0)) :=
  TensorReservoirWords.pathHom_heq D Sc m cutoff L Λ Λ p upward
example := TensorReservoirWords.pathHomAt_eq_wordHom D Sc m cutoff L Λ Λ
  (SPath.nil (0,0)) (by simp)
example (M N₀ : probeOldWeightSpace D Sc m Λ (-Λ)) (f : M ⟶ N₀) :
    HEq ((TensorReservoirWords.pathHomAt D Sc m cutoff L Λ Λ path upward).map f)
      ((TensorVacuumWords.wordHom D Sc m cutoff L Λ Λ ν).map f) := by
  rw [TensorReservoirWords.pathHomAt_eq_wordHom]
  rfl
example := TensorReservoirWords.valueChart_hom_mem D Sc m cutoff L Λ Λ path upward
example : chosenVector ≠ 0 := chosenVector_ne_zero
example : chosenEquiv chosenVector = contentVector := chosenEquiv.apply_symm_apply _
end Mixed
end NonVacuity.ELVTensorReservoirWords
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVTensorReservoirWords
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
