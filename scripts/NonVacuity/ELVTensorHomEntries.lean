import OddMath.QuiverHecke.CyclotomicAction.ELVTensorHomEntries
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.ELVTensorHomEntries

namespace TwoOdd
private abbrev D := AsymmetricParameters.datum
private abbrev originalSc := AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 20
private def m (i : Bool) : ℕ := if i then 2 else 1
private def Λ : Bool → ℤ := fun _ => 20
private abbrev N := PowerWordContent.powerBound D cutoff L
private abbrev R := WeightTensorVacuum.regularProbe D Sc m Λ
private abbrev W := elvRouquierData D Sc cutoff N Λ
private abbrev ν : List Bool := [false, true]
private abbrev τ (i j : Bool) : List Bool := (ν ++ [j]) ++ [i]
private abbrev σ (i j : Bool) : List Bool := (τ i j).reverse
private abbrev x₀ := PowerWordWeight.wordWeight D Λ ν
private abbrev h₁ (j : Bool) := PowerWordWeight.wordWeight_append D Λ ν j
private abbrev h₂ (i j : Bool) := PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i
private theorem h₄ (i j : Bool) :
    (x₀ + D.α i) + D.α j = PowerWordWeight.wordWeight D Λ (τ i j) := by
  calc
    (x₀ + D.α i) + D.α j = (x₀ + D.α j) + D.α i := by abel
    _ = PowerWordWeight.wordWeight D Λ (ν ++ [j]) + D.α i := congrArg (fun x => x + D.α i) (h₁ j)
    _ = PowerWordWeight.wordWeight D Λ (τ i j) := h₂ i j
private abbrev β := PowerWordWeight.wordBlock D Λ ν
private abbrev ε (i j : Bool) := blockSucc₂ D i j Λ (h₁ j) (h₂ i j) β
private def w (i j : Bool) : ContentCategory D Sc cutoff N (ε i j).1 := ⟨⟨τ i j⟩, by
  change (((ν ++ [j]) ++ [i] : List Bool) : Multiset Bool) = {i} + ({j} + (ν : Multiset Bool))
  rw [← Multiset.coe_add, ← Multiset.coe_add]
  ac_rfl⟩
private abbrev chosenEquiv (i j : Bool) := moduleIsoLinearEquiv
  (Pi.isoApp (TensorVacuumWords.pairChart D Sc m cutoff L Λ Λ ν i j (h₁ j) (h₂ i j)) (ε i j)) (w i j)
private theorem powers_high (q : Bool × ℕ) : 16 ≤ L q * SKM.SYM.elementaryWeight D q := by
  have hw : 0 < SKM.SYM.elementaryWeight D q := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  change 16 ≤ 20 * SKM.SYM.elementaryWeight D q
  omega
private theorem bounded_injective (i j : Bool) :
    Function.Injective (fun x : ExtendedAtMost D originalSc (σ i j) (σ i j) 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L (σ i j) (σ i j) x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 16 ≤ 20)) powers_high (by change 2 + 2 * (4 : ℕ).choose 2 < 16; decide)
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

private abbrev G (i j : Bool) :=
  TensorVacuumWords.wordHom D Sc m cutoff L Λ Λ ν ≫ W.E j (h₁ j) ≫ W.E i (h₂ i j)
private def inputEntry (i j : Bool) : End (G i j) := (2 : ℚ) • 𝟙 _
private theorem inputEntry_apply (i j : Bool) :
    (((inputEntry i j).total R) (ε i j)).total (w i j) (chosenVector i j) =
      (2 : ℚ) • chosenVector i j := by
  change ((((2 : ℚ) • 𝟙 ((G i j).obj R) + (2 : ℚ) • (0 : (G i j).obj R ⟶ (G i j).obj R))
    (ε i j)).total (w i j)) (chosenVector i j) = _
  rw [smul_zero, add_zero]
  change ((2 : ℚ) • 𝟙 (((G i j).obj R) (ε i j))).total
    (w i j) (chosenVector i j) = _
  change ((2 : ℚ) • 𝟙 ((((G i j).obj R) (ε i j)).obj (w i j))) (chosenVector i j) +
    ((2 : ℚ) • (0 : (((G i j).obj R) (ε i j)).obj (w i j) ⟶
      (((G i j).obj R) (ε i j)).obj (w i j))) (chosenVector i j) = _
  simp only [SVec.smul_apply, SVec.id_apply, SVec.zero_apply, smul_zero, add_zero]
private theorem inputEntry_vector_ne_zero (i j : Bool) :
    (((inputEntry i j).total R) (ε i j)).total (w i j) (chosenVector i j) ≠ 0 := by
  rw [inputEntry_apply]
  exact smul_ne_zero (by norm_num) (chosenVector_ne_zero i j)

/-- The literal equal odd crossing in the nonempty two-letter context. -/
example := TensorHomEntries.cross_apply D Sc m cutoff L Λ Λ ν false false
  (h₁ false) (h₂ false false) rfl (h₄ false false)
  (G false false) (inputEntry false false) (ε false false) (w false false) (chosenVector false false)
/-- The distinct crossing includes both colours in a nonzero four-E input. -/
example := TensorHomEntries.cross_apply D Sc m cutoff L Λ Λ ν false true
  (h₁ true) (h₂ false true) rfl (h₄ false true)
  (G false true) (inputEntry false true) (ε false true) (w false true) (chosenVector false true)
example : chosenVector false false ≠ 0 := chosenVector_ne_zero false false
example : chosenVector false true ≠ 0 := chosenVector_ne_zero false true
example (i j : Bool) :
    (((inputEntry i j).total R) (ε i j)).total (w i j) (chosenVector i j) ≠ 0 :=
  inputEntry_vector_ne_zero i j
example (i j : Bool) (f : End (G i j)) (β' : WeightBlocks D Λ (PowerWordWeight.wordWeight D Λ (τ i j)))
    (c : ContentCategory D Sc cutoff N β'.1) (z : (((G i j).obj R) β').obj c) :=
  TensorHomEntries.cross_apply D Sc m cutoff L Λ Λ ν i j (h₁ j) (h₂ i j) rfl (h₄ i j)
    (G i j) f β' c z
example (f : End (TensorVacuumWords.wordHom D Sc m cutoff L Λ Λ ν)) :=
  TensorHomEntries.coordinates_apply D Sc m cutoff L Λ Λ ν ν
    (TensorVacuumWords.wordHom D Sc m cutoff L Λ Λ ν) (TensorVacuumWords.chart D Sc m cutoff L Λ Λ ν) f
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
private abbrev τ : List Bool := ν ++ [false]
private abbrev σ : List Bool := τ.reverse
private abbrev δ := blockSucc D Λ false (PowerWordWeight.wordWeight_append D Λ ν false)
  (PowerWordWeight.wordBlock D Λ ν)
private def w : ContentCategory D Sc cutoff N δ.1 := ⟨⟨τ⟩, by
  change ((ν ++ [false] : List Bool) : Multiset Bool) = {false} + (ν : Multiset Bool)
  rw [← Multiset.coe_add]
  exact add_comm _ _⟩
private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D originalSc σ σ 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 16 ≤ 20)) powers_high (by decide)
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
  (Pi.isoApp (TensorVacuumWords.dotChart D Sc m cutoff L Λ Λ ν false) δ) w
private def chosenVector := chosenEquiv.symm contentVector
example : chosenVector ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have he := congrArg chosenEquiv hz
  simpa only [chosenVector, LinearEquiv.apply_symm_apply, map_zero] using he
/-- The literal odd dot in the same nonempty context, on a surviving
full-coefficient vector in its three-E tensor-Hom input. -/
private abbrev G := TensorVacuumWords.wordHom D Sc m cutoff L Λ Λ ν ≫
  W.E false (PowerWordWeight.wordWeight_append D Λ ν false)
private def inputEntry : End G := (2 : ℚ) • 𝟙 _
private theorem inputEntry_apply :
    ((inputEntry.total R) δ).total w chosenVector = (2 : ℚ) • chosenVector := by
  change ((((2 : ℚ) • 𝟙 (G.obj R) + (2 : ℚ) • (0 : G.obj R ⟶ G.obj R)) δ).total w) chosenVector = _
  rw [smul_zero, add_zero]
  change ((2 : ℚ) • 𝟙 ((G.obj R) δ)).total w chosenVector = _
  change ((2 : ℚ) • 𝟙 (((G.obj R) δ).obj w)) chosenVector +
    ((2 : ℚ) • (0 : ((G.obj R) δ).obj w ⟶ ((G.obj R) δ).obj w)) chosenVector = _
  simp only [SVec.smul_apply, SVec.id_apply, SVec.zero_apply, smul_zero, add_zero]
example := TensorHomEntries.dot_apply D Sc m cutoff L Λ Λ ν false G inputEntry δ w chosenVector
example : ((inputEntry.total R) δ).total w chosenVector ≠ 0 := by
  rw [inputEntry_apply]
  apply smul_ne_zero (by norm_num)
  intro hz
  apply contentVector_ne_zero
  have he := congrArg chosenEquiv hz
  simpa only [chosenVector, LinearEquiv.apply_symm_apply, map_zero] using he
example (f : End G) (β' : WeightBlocks D Λ (PowerWordWeight.wordWeight D Λ τ))
    (c : ContentCategory D Sc cutoff N β'.1) (z : ((G.obj R) β').obj c) :=
  TensorHomEntries.dot_apply D Sc m cutoff L Λ Λ ν false G f β' c z
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
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 20
private def m (i : Bool) : ℕ := if i then 2 else 1
private def Λ : Bool → ℤ := fun _ => 20
private abbrev N := PowerWordContent.powerBound D cutoff L
private abbrev R := WeightTensorVacuum.regularProbe D Sc m Λ
private abbrev W := elvRouquierData D Sc cutoff N Λ
private abbrev ν : List Bool := [false, true]
private abbrev τ (i j : Bool) : List Bool := (ν ++ [j]) ++ [i]
private abbrev σ (i j : Bool) : List Bool := (τ i j).reverse
private abbrev x₀ := PowerWordWeight.wordWeight D Λ ν
private abbrev h₁ (j : Bool) := PowerWordWeight.wordWeight_append D Λ ν j
private abbrev h₂ (i j : Bool) := PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i
private theorem h₄ (i j : Bool) :
    (x₀ + D.α i) + D.α j = PowerWordWeight.wordWeight D Λ (τ i j) := by
  calc
    (x₀ + D.α i) + D.α j = (x₀ + D.α j) + D.α i := by abel
    _ = PowerWordWeight.wordWeight D Λ (ν ++ [j]) + D.α i := congrArg (fun x => x + D.α i) (h₁ j)
    _ = PowerWordWeight.wordWeight D Λ (τ i j) := h₂ i j
private abbrev β := PowerWordWeight.wordBlock D Λ ν
private abbrev ε (i j : Bool) := blockSucc₂ D i j Λ (h₁ j) (h₂ i j) β
private def w (i j : Bool) : ContentCategory D Sc cutoff N (ε i j).1 := ⟨⟨τ i j⟩, by
  change (((ν ++ [j]) ++ [i] : List Bool) : Multiset Bool) = {i} + ({j} + (ν : Multiset Bool))
  rw [← Multiset.coe_add, ← Multiset.coe_add]
  ac_rfl⟩
private abbrev chosenEquiv (i j : Bool) := moduleIsoLinearEquiv
  (Pi.isoApp (TensorVacuumWords.pairChart D Sc m cutoff L Λ Λ ν i j (h₁ j) (h₂ i j)) (ε i j)) (w i j)
private theorem powers_high (q : Bool × ℕ) : 16 ≤ L q * SKM.SYM.elementaryWeight D q := by
  have hw : 0 < SKM.SYM.elementaryWeight D q := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  change 16 ≤ 20 * SKM.SYM.elementaryWeight D q
  omega
private theorem bounded_injective (i j : Bool) :
    Function.Injective (fun x : ExtendedAtMost D originalSc (σ i j) (σ i j) 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L (σ i j) (σ i j) x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 16 ≤ 20)) powers_high (by change 2 + 2 * (4 : ℕ).choose 2 < 16; decide)
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

private abbrev G (i j : Bool) :=
  TensorVacuumWords.wordHom D Sc m cutoff L Λ Λ ν ≫ W.E j (h₁ j) ≫ W.E i (h₂ i j)
private def inputEntry (i j : Bool) : End (G i j) := (2 : ℚ) • 𝟙 _
private theorem inputEntry_apply (i j : Bool) :
    (((inputEntry i j).total R) (ε i j)).total (w i j) (chosenVector i j) =
      (2 : ℚ) • chosenVector i j := by
  change ((((2 : ℚ) • 𝟙 ((G i j).obj R) + (2 : ℚ) • (0 : (G i j).obj R ⟶ (G i j).obj R))
    (ε i j)).total (w i j)) (chosenVector i j) = _
  rw [smul_zero, add_zero]
  change ((2 : ℚ) • 𝟙 (((G i j).obj R) (ε i j))).total
    (w i j) (chosenVector i j) = _
  change ((2 : ℚ) • 𝟙 ((((G i j).obj R) (ε i j)).obj (w i j))) (chosenVector i j) +
    ((2 : ℚ) • (0 : (((G i j).obj R) (ε i j)).obj (w i j) ⟶
      (((G i j).obj R) (ε i j)).obj (w i j))) (chosenVector i j) = _
  simp only [SVec.smul_apply, SVec.id_apply, SVec.zero_apply, smul_zero, add_zero]
private theorem inputEntry_vector_ne_zero (i j : Bool) :
    (((inputEntry i j).total R) (ε i j)).total (w i j) (chosenVector i j) ≠ 0 := by
  rw [inputEntry_apply]
  exact smul_ne_zero (by norm_num) (chosenVector_ne_zero i j)

/-- The literal equal odd crossing in the nonempty two-letter context. -/
example := TensorHomEntries.cross_apply D Sc m cutoff L Λ Λ ν true true
  (h₁ true) (h₂ true true) rfl (h₄ true true)
  (G true true) (inputEntry true true) (ε true true) (w true true) (chosenVector true true)
/-- The distinct crossing includes both colours in a nonzero four-E input. -/
example := TensorHomEntries.cross_apply D Sc m cutoff L Λ Λ ν false true
  (h₁ true) (h₂ false true) rfl (h₄ false true)
  (G false true) (inputEntry false true) (ε false true) (w false true) (chosenVector false true)
example : chosenVector true true ≠ 0 := chosenVector_ne_zero true true
example : chosenVector false true ≠ 0 := chosenVector_ne_zero false true
example (i j : Bool) :
    (((inputEntry i j).total R) (ε i j)).total (w i j) (chosenVector i j) ≠ 0 :=
  inputEntry_vector_ne_zero i j
example (i j : Bool) (f : End (G i j)) (β' : WeightBlocks D Λ (PowerWordWeight.wordWeight D Λ (τ i j)))
    (c : ContentCategory D Sc cutoff N β'.1) (z : (((G i j).obj R) β').obj c) :=
  TensorHomEntries.cross_apply D Sc m cutoff L Λ Λ ν i j (h₁ j) (h₂ i j) rfl (h₄ i j)
    (G i j) f β' c z
example (f : End (TensorVacuumWords.wordHom D Sc m cutoff L Λ Λ ν)) :=
  TensorHomEntries.coordinates_apply D Sc m cutoff L Λ Λ ν ν
    (TensorVacuumWords.wordHom D Sc m cutoff L Λ Λ ν) (TensorVacuumWords.chart D Sc m cutoff L Λ Λ ν) f
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
private abbrev τ : List Bool := ν ++ [true]
private abbrev σ : List Bool := τ.reverse
private abbrev δ := blockSucc D Λ true (PowerWordWeight.wordWeight_append D Λ ν true)
  (PowerWordWeight.wordBlock D Λ ν)
private def w : ContentCategory D Sc cutoff N δ.1 := ⟨⟨τ⟩, by
  change ((ν ++ [true] : List Bool) : Multiset Bool) = {true} + (ν : Multiset Bool)
  rw [← Multiset.coe_add]
  exact add_comm _ _⟩
private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D originalSc σ σ 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 16 ≤ 20)) powers_high (by decide)
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
  (Pi.isoApp (TensorVacuumWords.dotChart D Sc m cutoff L Λ Λ ν true) δ) w
private def chosenVector := chosenEquiv.symm contentVector
example : chosenVector ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have he := congrArg chosenEquiv hz
  simpa only [chosenVector, LinearEquiv.apply_symm_apply, map_zero] using he
/-- The literal odd dot in the same nonempty context, on a surviving
full-coefficient vector in its three-E tensor-Hom input. -/
private abbrev G := TensorVacuumWords.wordHom D Sc m cutoff L Λ Λ ν ≫
  W.E true (PowerWordWeight.wordWeight_append D Λ ν true)
private def inputEntry : End G := (2 : ℚ) • 𝟙 _
private theorem inputEntry_apply :
    ((inputEntry.total R) δ).total w chosenVector = (2 : ℚ) • chosenVector := by
  change ((((2 : ℚ) • 𝟙 (G.obj R) + (2 : ℚ) • (0 : G.obj R ⟶ G.obj R)) δ).total w) chosenVector = _
  rw [smul_zero, add_zero]
  change ((2 : ℚ) • 𝟙 ((G.obj R) δ)).total w chosenVector = _
  change ((2 : ℚ) • 𝟙 (((G.obj R) δ).obj w)) chosenVector +
    ((2 : ℚ) • (0 : ((G.obj R) δ).obj w ⟶ ((G.obj R) δ).obj w)) chosenVector = _
  simp only [SVec.smul_apply, SVec.id_apply, SVec.zero_apply, smul_zero, add_zero]
example := TensorHomEntries.dot_apply D Sc m cutoff L Λ Λ ν true G inputEntry δ w chosenVector
example : ((inputEntry.total R) δ).total w chosenVector ≠ 0 := by
  rw [inputEntry_apply]
  apply smul_ne_zero (by norm_num)
  intro hz
  apply contentVector_ne_zero
  have he := congrArg chosenEquiv hz
  simpa only [chosenVector, LinearEquiv.apply_symm_apply, map_zero] using he
example (f : End G) (β' : WeightBlocks D Λ (PowerWordWeight.wordWeight D Λ τ))
    (c : ContentCategory D Sc cutoff N β'.1) (z : ((G.obj R) β').obj c) :=
  TensorHomEntries.dot_apply D Sc m cutoff L Λ Λ ν true G f β' c z
end Dot
end Mixed

end NonVacuity.ELVTensorHomEntries
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVTensorHomEntries
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
