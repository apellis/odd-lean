import OddMath.QuiverHecke.CyclotomicAction.ELVTensorHomContexts
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.ELVTensorHomContexts

namespace TwoOdd
private abbrev D := AsymmetricParameters.datum
private abbrev originalSc := AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 40
private def L (_ : Bool × ℕ) : ℕ := 40
private def m (i : Bool) : ℕ := if i then 2 else 1
private def Λ : Bool → ℤ := fun _ => 40
private abbrev N := PowerWordContent.powerBound D cutoff L
private abbrev ν : List Bool := [false, true]
private abbrev η : List Bool := [false]
private abbrev R := WeightTensorVacuum.regularProbe D Sc m Λ
private abbrev W := elvRouquierData D Sc cutoff N Λ
private abbrev ζ (i j : Bool) : List Bool := (ν ++ [j]) ++ [i]
private abbrev τ (i j : Bool) : List Bool := ζ i j ++ η
private abbrev σ (i j : Bool) : List Bool := (τ i j).reverse
private abbrev x₀ := PowerWordWeight.wordWeight D Λ ν
private abbrev h₁ (j : Bool) := PowerWordWeight.wordWeight_append D Λ ν j
private abbrev h₂ (i j : Bool) := PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i
private theorem h₄ (i j : Bool) :
    (x₀ + D.α i) + D.α j = PowerWordWeight.wordWeight D Λ (ζ i j) := by
  calc
    (x₀ + D.α i) + D.α j = (x₀ + D.α j) + D.α i := by abel
    _ = PowerWordWeight.wordWeight D Λ (ν ++ [j]) + D.α i := congrArg (fun x => x + D.α i) (h₁ j)
    _ = PowerWordWeight.wordWeight D Λ (ζ i j) := h₂ i j
private abbrev β := PowerWordWeight.wordBlock D Λ ν
private abbrev ε (i j : Bool) := blockSucc D Λ false rfl
  (blockSucc₂ D i j Λ (h₁ j) (h₂ i j) β)
private def w (i j : Bool) : ContentCategory D Sc cutoff N (ε i j).1 := ⟨⟨τ i j⟩, by
  change ((((ν ++ [j]) ++ [i]) ++ [false] : List Bool) : Multiset Bool) =
    {false} + ({i} + ({j} + (ν : Multiset Bool)))
  rw [← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.coe_add]
  ac_rfl⟩
private abbrev chosenEquiv (i j : Bool) := moduleIsoLinearEquiv
  (Pi.isoApp (TensorHomContexts.pairChart D Sc m cutoff L Λ Λ ν η i j (h₁ j) (h₂ i j)) (ε i j)) (w i j)
private theorem powers_high (q : Bool × ℕ) : 32 ≤ L q * SKM.SYM.elementaryWeight D q := by
  have hw : 0 < SKM.SYM.elementaryWeight D q := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  change 32 ≤ 40 * SKM.SYM.elementaryWeight D q
  omega
private theorem bounded_injective (i j : Bool) :
    Function.Injective (fun x : ExtendedAtMost D originalSc (σ i j) (σ i j) 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L (σ i j) (σ i j) x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 32 ≤ 40)) powers_high (by change 2 + 2 * (5 : ℕ).choose 2 < 32; decide)
private def identityNF (i j : Bool) : NFIdx (σ i j) (σ i j) := by
  have hc : Categorification.TypeA.canWord (σ i j).length (1 : Equiv.Perm (Fin (σ i j).length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]
private def oddIndex : SKM.SYM.CoefficientIndex D := (0, {⟨false, rfl⟩, ⟨true, rfl⟩})
private def occupied (i j : Bool) : ExtendedAtMost D originalSc (σ i j) (σ i j) 2 :=
  ⟨extensionBasis D originalSc (σ i j) (σ i j) (oddIndex, identityNF i j),
    Submodule.subset_span ⟨(oddIndex, identityNF i j), by cases i <;> cases j <;> decide, rfl⟩⟩
private def contentVector (i j : Bool) :
    (PowerWordWeight.wordAt D Sc cutoff L (τ i j) (ε i j).1).obj (w i j) :=
  powerWordHalfTurnCoordinate D originalSc cutoff L (σ i j) (σ i j) (occupied i j).val
private theorem contentVector_ne_zero (i j : Bool) : contentVector i j ≠ 0 := by
  intro hz
  have hh : occupied i j = (0 : ExtendedAtMost D originalSc (σ i j) (σ i j) 2) := by
    apply bounded_injective i j
    change powerWordHalfTurnCoordinate D originalSc cutoff L (σ i j) (σ i j) (occupied i j).val =
      powerWordHalfTurnCoordinate D originalSc cutoff L (σ i j) (σ i j) 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc (σ i j) (σ i j)).ne_zero (oddIndex, identityNF i j)
    (congrArg Subtype.val hh)
private def chosenVector (i j : Bool) := (chosenEquiv i j).symm (contentVector i j)
private theorem chosenVector_ne_zero (i j : Bool) : chosenVector i j ≠ 0 := by
  intro hz
  apply contentVector_ne_zero i j
  have he := congrArg (chosenEquiv i j) hz
  simpa only [chosenVector, LinearEquiv.apply_symm_apply, map_zero] using he

private abbrev G (i j : Bool) := TensorVacuumWords.wordHom D Sc m cutoff L Λ Λ ν ≫
  W.E j (h₁ j) ≫ W.E i (h₂ i j) ≫
    TensorHomContexts.context D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ (ζ i j)) η

/-- The literal equal odd crossing in the nonempty two-letter context. -/
example := TensorHomContexts.cross_apply D Sc m cutoff L Λ Λ ν η false false
  (h₁ false) (h₂ false false) rfl (h₄ false false)
  (G false false) (𝟙 _) (ε false false) (w false false) (chosenVector false false)
/-- The distinct crossing includes both colours in a nonzero four-E input. -/
example := TensorHomContexts.cross_apply D Sc m cutoff L Λ Λ ν η false true
  (h₁ true) (h₂ false true) rfl (h₄ false true)
  (G false true) (𝟙 _) (ε false true) (w false true) (chosenVector false true)
example : chosenVector false false ≠ 0 := chosenVector_ne_zero false false
example : chosenVector false true ≠ 0 := chosenVector_ne_zero false true
example (i j : Bool) := TensorHomContexts.cross D Sc m cutoff L Λ Λ ν η i j (h₁ j) (h₂ i j) rfl (h₄ i j)
example (i j : Bool) (f : End (G i j))
    (β' : WeightBlocks D Λ (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D Λ (ζ i j)) η))
    (c : ContentCategory D Sc cutoff N β'.1) (z : (((G i j).obj R) β').obj c) :=
  TensorHomContexts.cross_apply D Sc m cutoff L Λ Λ ν η i j (h₁ j) (h₂ i j) rfl (h₄ i j)
    (G i j) f β' c z
example := TensorVacuumWords.valueIso_even D Sc m cutoff L Λ Λ ν
example := TensorVacuumWords.chart_even D Sc m cutoff L Λ Λ ν
example := TensorVacuumWords.wordHom_append D Sc m cutoff L Λ Λ ν false
/-- Whole Hom coordinates on the actual tensor-Hom word, with a supplied
old identity and no endpoint comparison premise. -/
example := TensorVacuumWords.homEquiv_from_old D Sc m cutoff L Λ Λ ν ν
  (𝟙 (OldCategory.mk ν : OldCategory D Sc cutoff))
example (τ' : List Bool)
    (v : (PowerWordWeight.wordAt D Sc cutoff L τ' (ν : Multiset Bool)).obj
      (PowerWordContentCyclicity.wordObject D Sc cutoff L ν (ν : Multiset Bool) rfl)) :
    TensorVacuumWords.homEquiv D Sc m cutoff L Λ Λ ν τ'
      ((TensorVacuumWords.homEquiv D Sc m cutoff L Λ Λ ν τ').symm v) = v :=
  LinearEquiv.apply_symm_apply _ v

namespace Dot
private abbrev τ : List Bool := (ν ++ [false]) ++ η
private abbrev σ : List Bool := τ.reverse
private abbrev δ := blockSucc D Λ false rfl
  (blockSucc D Λ false (PowerWordWeight.wordWeight_append D Λ ν false) (PowerWordWeight.wordBlock D Λ ν))
private def w : ContentCategory D Sc cutoff N δ.1 := ⟨⟨τ⟩, by
  change (((ν ++ [false]) ++ [false] : List Bool) : Multiset Bool) = {false} + ({false} + (ν : Multiset Bool))
  rw [← Multiset.coe_add, ← Multiset.coe_add]
  ac_rfl⟩
private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D originalSc σ σ 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 32 ≤ 40)) powers_high (by decide)
private def identityNF : NFIdx σ σ := by
  have hc : Categorification.TypeA.canWord σ.length (1 : Equiv.Perm (Fin σ.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]
private def occupied : ExtendedAtMost D originalSc σ σ 2 :=
  ⟨extensionBasis D originalSc σ σ (oddIndex, identityNF),
    Submodule.subset_span ⟨(oddIndex, identityNF), by decide, rfl⟩⟩
private def contentVector : (PowerWordWeight.wordAt D Sc cutoff L τ δ.1).obj w :=
  powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val
private theorem contentVector_ne_zero : contentVector ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D originalSc σ σ 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc σ σ).ne_zero (oddIndex, identityNF) (congrArg Subtype.val hh)
private abbrev chosenEquiv := moduleIsoLinearEquiv
  (Pi.isoApp (TensorHomContexts.dotChart D Sc m cutoff L Λ Λ ν η false) δ) w
private def chosenVector := chosenEquiv.symm contentVector
example : chosenVector ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have he := congrArg chosenEquiv hz
  simpa only [chosenVector, LinearEquiv.apply_symm_apply, map_zero] using he
/-- The literal odd dot in the same nonempty context, on a surviving
full-coefficient vector in its three-E tensor-Hom input. -/
private abbrev G := TensorVacuumWords.wordHom D Sc m cutoff L Λ Λ ν ≫
  W.E false (PowerWordWeight.wordWeight_append D Λ ν false) ≫
    TensorHomContexts.context D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ (ν ++ [false])) η
example := TensorHomContexts.dot_apply D Sc m cutoff L Λ Λ ν η false G (𝟙 _) δ w chosenVector
example := TensorHomContexts.dot D Sc m cutoff L Λ Λ ν η false
example (f : End G)
    (β' : WeightBlocks D Λ (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D Λ (ν ++ [false])) η))
    (c : ContentCategory D Sc cutoff N β'.1) (z : ((G.obj R) β').obj c) :=
  TensorHomContexts.dot_apply D Sc m cutoff L Λ Λ ν η false G f β' c z
end Dot
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
private def cutoff (_ : Bool) : ℕ := 40
private def L (_ : Bool × ℕ) : ℕ := 40
private def m (i : Bool) : ℕ := if i then 2 else 1
private def Λ : Bool → ℤ := fun _ => 40
private abbrev N := PowerWordContent.powerBound D cutoff L
private abbrev ν : List Bool := [false, true]
private abbrev η : List Bool := [false]
private abbrev R := WeightTensorVacuum.regularProbe D Sc m Λ
private abbrev W := elvRouquierData D Sc cutoff N Λ
private abbrev ζ (i j : Bool) : List Bool := (ν ++ [j]) ++ [i]
private abbrev τ (i j : Bool) : List Bool := ζ i j ++ η
private abbrev σ (i j : Bool) : List Bool := (τ i j).reverse
private abbrev x₀ := PowerWordWeight.wordWeight D Λ ν
private abbrev h₁ (j : Bool) := PowerWordWeight.wordWeight_append D Λ ν j
private abbrev h₂ (i j : Bool) := PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i
private theorem h₄ (i j : Bool) :
    (x₀ + D.α i) + D.α j = PowerWordWeight.wordWeight D Λ (ζ i j) := by
  calc
    (x₀ + D.α i) + D.α j = (x₀ + D.α j) + D.α i := by abel
    _ = PowerWordWeight.wordWeight D Λ (ν ++ [j]) + D.α i := congrArg (fun x => x + D.α i) (h₁ j)
    _ = PowerWordWeight.wordWeight D Λ (ζ i j) := h₂ i j
private abbrev β := PowerWordWeight.wordBlock D Λ ν
private abbrev ε (i j : Bool) := blockSucc D Λ false rfl
  (blockSucc₂ D i j Λ (h₁ j) (h₂ i j) β)
private def w (i j : Bool) : ContentCategory D Sc cutoff N (ε i j).1 := ⟨⟨τ i j⟩, by
  change ((((ν ++ [j]) ++ [i]) ++ [false] : List Bool) : Multiset Bool) =
    {false} + ({i} + ({j} + (ν : Multiset Bool)))
  rw [← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.coe_add]
  ac_rfl⟩
private abbrev chosenEquiv (i j : Bool) := moduleIsoLinearEquiv
  (Pi.isoApp (TensorHomContexts.pairChart D Sc m cutoff L Λ Λ ν η i j (h₁ j) (h₂ i j)) (ε i j)) (w i j)
private theorem powers_high (q : Bool × ℕ) : 32 ≤ L q * SKM.SYM.elementaryWeight D q := by
  have hw : 0 < SKM.SYM.elementaryWeight D q := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  change 32 ≤ 40 * SKM.SYM.elementaryWeight D q
  omega
private theorem bounded_injective (i j : Bool) :
    Function.Injective (fun x : ExtendedAtMost D originalSc (σ i j) (σ i j) 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L (σ i j) (σ i j) x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 32 ≤ 40)) powers_high (by change 2 + 2 * (5 : ℕ).choose 2 < 32; decide)
private def identityNF (i j : Bool) : NFIdx (σ i j) (σ i j) := by
  have hc : Categorification.TypeA.canWord (σ i j).length (1 : Equiv.Perm (Fin (σ i j).length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]
private def oddIndex : SKM.SYM.CoefficientIndex D := (0, {⟨true, rfl⟩})
private def occupied (i j : Bool) : ExtendedAtMost D originalSc (σ i j) (σ i j) 2 :=
  ⟨extensionBasis D originalSc (σ i j) (σ i j) (oddIndex, identityNF i j),
    Submodule.subset_span ⟨(oddIndex, identityNF i j), by cases i <;> cases j <;> decide, rfl⟩⟩
private def contentVector (i j : Bool) :
    (PowerWordWeight.wordAt D Sc cutoff L (τ i j) (ε i j).1).obj (w i j) :=
  powerWordHalfTurnCoordinate D originalSc cutoff L (σ i j) (σ i j) (occupied i j).val
private theorem contentVector_ne_zero (i j : Bool) : contentVector i j ≠ 0 := by
  intro hz
  have hh : occupied i j = (0 : ExtendedAtMost D originalSc (σ i j) (σ i j) 2) := by
    apply bounded_injective i j
    change powerWordHalfTurnCoordinate D originalSc cutoff L (σ i j) (σ i j) (occupied i j).val =
      powerWordHalfTurnCoordinate D originalSc cutoff L (σ i j) (σ i j) 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc (σ i j) (σ i j)).ne_zero (oddIndex, identityNF i j)
    (congrArg Subtype.val hh)
private def chosenVector (i j : Bool) := (chosenEquiv i j).symm (contentVector i j)
private theorem chosenVector_ne_zero (i j : Bool) : chosenVector i j ≠ 0 := by
  intro hz
  apply contentVector_ne_zero i j
  have he := congrArg (chosenEquiv i j) hz
  simpa only [chosenVector, LinearEquiv.apply_symm_apply, map_zero] using he

private abbrev G (i j : Bool) := TensorVacuumWords.wordHom D Sc m cutoff L Λ Λ ν ≫
  W.E j (h₁ j) ≫ W.E i (h₂ i j) ≫
    TensorHomContexts.context D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ (ζ i j)) η

/-- The literal equal odd crossing in the nonempty two-letter context. -/
example := TensorHomContexts.cross_apply D Sc m cutoff L Λ Λ ν η true true
  (h₁ true) (h₂ true true) rfl (h₄ true true)
  (G true true) (𝟙 _) (ε true true) (w true true) (chosenVector true true)
/-- The distinct crossing includes both colours in a nonzero four-E input. -/
example := TensorHomContexts.cross_apply D Sc m cutoff L Λ Λ ν η false true
  (h₁ true) (h₂ false true) rfl (h₄ false true)
  (G false true) (𝟙 _) (ε false true) (w false true) (chosenVector false true)
example : chosenVector true true ≠ 0 := chosenVector_ne_zero true true
example : chosenVector false true ≠ 0 := chosenVector_ne_zero false true
example (i j : Bool) := TensorHomContexts.cross D Sc m cutoff L Λ Λ ν η i j (h₁ j) (h₂ i j) rfl (h₄ i j)
example (i j : Bool) (f : End (G i j))
    (β' : WeightBlocks D Λ (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D Λ (ζ i j)) η))
    (c : ContentCategory D Sc cutoff N β'.1) (z : (((G i j).obj R) β').obj c) :=
  TensorHomContexts.cross_apply D Sc m cutoff L Λ Λ ν η i j (h₁ j) (h₂ i j) rfl (h₄ i j)
    (G i j) f β' c z
example := TensorVacuumWords.valueIso_even D Sc m cutoff L Λ Λ ν
example := TensorVacuumWords.chart_even D Sc m cutoff L Λ Λ ν
example := TensorVacuumWords.wordHom_append D Sc m cutoff L Λ Λ ν true
/-- Whole Hom coordinates on the actual tensor-Hom word, with a supplied
old identity and no endpoint comparison premise. -/
example := TensorVacuumWords.homEquiv_from_old D Sc m cutoff L Λ Λ ν ν
  (𝟙 (OldCategory.mk ν : OldCategory D Sc cutoff))
example (τ' : List Bool)
    (v : (PowerWordWeight.wordAt D Sc cutoff L τ' (ν : Multiset Bool)).obj
      (PowerWordContentCyclicity.wordObject D Sc cutoff L ν (ν : Multiset Bool) rfl)) :
    TensorVacuumWords.homEquiv D Sc m cutoff L Λ Λ ν τ'
      ((TensorVacuumWords.homEquiv D Sc m cutoff L Λ Λ ν τ').symm v) = v :=
  LinearEquiv.apply_symm_apply _ v

namespace Dot
private abbrev τ : List Bool := (ν ++ [true]) ++ η
private abbrev σ : List Bool := τ.reverse
private abbrev δ := blockSucc D Λ false rfl
  (blockSucc D Λ true (PowerWordWeight.wordWeight_append D Λ ν true) (PowerWordWeight.wordBlock D Λ ν))
private def w : ContentCategory D Sc cutoff N δ.1 := ⟨⟨τ⟩, by
  change (((ν ++ [true]) ++ [false] : List Bool) : Multiset Bool) = {false} + ({true} + (ν : Multiset Bool))
  rw [← Multiset.coe_add, ← Multiset.coe_add]
  ac_rfl⟩
private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D originalSc σ σ 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 32 ≤ 40)) powers_high (by decide)
private def identityNF : NFIdx σ σ := by
  have hc : Categorification.TypeA.canWord σ.length (1 : Equiv.Perm (Fin σ.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]
private def occupied : ExtendedAtMost D originalSc σ σ 2 :=
  ⟨extensionBasis D originalSc σ σ (oddIndex, identityNF),
    Submodule.subset_span ⟨(oddIndex, identityNF), by decide, rfl⟩⟩
private def contentVector : (PowerWordWeight.wordAt D Sc cutoff L τ δ.1).obj w :=
  powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val
private theorem contentVector_ne_zero : contentVector ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D originalSc σ σ 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc σ σ).ne_zero (oddIndex, identityNF) (congrArg Subtype.val hh)
private abbrev chosenEquiv := moduleIsoLinearEquiv
  (Pi.isoApp (TensorHomContexts.dotChart D Sc m cutoff L Λ Λ ν η true) δ) w
private def chosenVector := chosenEquiv.symm contentVector
example : chosenVector ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have he := congrArg chosenEquiv hz
  simpa only [chosenVector, LinearEquiv.apply_symm_apply, map_zero] using he
/-- The literal odd dot in the same nonempty context, on a surviving
full-coefficient vector in its three-E tensor-Hom input. -/
private abbrev G := TensorVacuumWords.wordHom D Sc m cutoff L Λ Λ ν ≫
  W.E true (PowerWordWeight.wordWeight_append D Λ ν true) ≫
    TensorHomContexts.context D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ (ν ++ [true])) η
example := TensorHomContexts.dot_apply D Sc m cutoff L Λ Λ ν η true G (𝟙 _) δ w chosenVector
example := TensorHomContexts.dot D Sc m cutoff L Λ Λ ν η true
example (f : End G)
    (β' : WeightBlocks D Λ (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D Λ (ν ++ [true])) η))
    (c : ContentCategory D Sc cutoff N β'.1) (z : ((G.obj R) β').obj c) :=
  TensorHomContexts.dot_apply D Sc m cutoff L Λ Λ ν η true G f β' c z
end Dot
end Mixed

end NonVacuity.ELVTensorHomContexts
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVTensorHomContexts
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
