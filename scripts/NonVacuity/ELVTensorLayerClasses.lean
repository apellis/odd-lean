import OddMath.QuiverHecke.CyclotomicAction.ELVTensorLayerClasses
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.ELVTensorLayerClasses

private theorem coordinate_ne_zero (D : SKM.Datum Bool (Bool → ℤ)) (Sc : SKM.Scalars D ℚ)
    (cutoff : Bool → ℕ) (L : Bool × ℕ → ℕ) (s t : List Bool)
    (v : (powerWordModule D (parameterTwist D Sc) cutoff L t.reverse).obj (OldCategory.mk s.reverse))
    (hv : v ≠ 0) : PowerWordQuotientCoordinates.coordinate D Sc cutoff L s t v ≠ 0 := by
  intro h
  let e := PowerWordQuotientCoordinates.quotientEquiv D Sc cutoff L s t
  have hh := congrArg e h
  change e (e.symm v) = e 0 at hh
  rw [LinearEquiv.apply_symm_apply, map_zero] at hh
  exact hv hh

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

private theorem sourceContent (i j : Bool) : ((σ i j).reverse : Multiset Bool) = (ε i j).1 := by
  change ((τ i j : List Bool) : Multiset Bool) = (ε i j).1
  exact (w i j).content
private def identityEntry (i j : Bool) : End (G i j) := 𝟙 _
private def inputVector (i j : Bool) := TensorLayerClasses.crossVector D originalSc cutoff L m Λ Λ ν η i j
  (h₁ j) (h₂ i j) (G i j) (𝟙 _) (σ i j) (ε i j) (sourceContent i j) (chosenVector i j)
private theorem evaluated_id (i j : Bool) :
    (((((identityEntry i j).total R) (ε i j)).total (w i j)) (chosenVector i j)) = chosenVector i j := by
  change (((𝟙 ((G i j).obj R) + 0) (ε i j)).total (w i j)) (chosenVector i j) = _
  rw [add_zero]
  change (𝟙 ((((G i j).obj R) (ε i j)).obj (w i j)) + 0) (chosenVector i j) = _
  simp only [add_zero, SVec.id_apply]
private theorem inputVector_ne_zero (i j : Bool) : inputVector i j ≠ 0 := by
  intro hv
  have hz := (TensorLayerClasses.crossVector_eq_zero_iff D originalSc cutoff L m Λ Λ ν η i j
    (h₁ j) (h₂ i j) (G i j) (𝟙 _) (σ i j) (ε i j) (sourceContent i j) (chosenVector i j)).mp hv
  change ((((identityEntry i j).total R) (ε i j)).total (w i j) (chosenVector i j)) = 0 at hz
  rw [evaluated_id] at hz
  exact chosenVector_ne_zero i j hz
private abbrev K (i j : Bool) := PowerWordQuotientCoordinates.kernel D originalSc cutoff L (σ i j)
  (PowerWordLayerClasses.domWord ν η (.cross i j))
private def inputClass (i j : Bool) := PowerWordQuotientCoordinates.coordinate D originalSc cutoff L (σ i j)
  (PowerWordLayerClasses.domWord ν η (.cross i j)) (inputVector i j)
private def representative (i j : Bool) := Classical.choose ((Submodule.mkQ_surjective (K i j)) (inputClass i j))
private theorem representative_spec (i j : Bool) : inputClass i j = (K i j).mkQ (representative i j) :=
  (Classical.choose_spec ((Submodule.mkQ_surjective (K i j)) (inputClass i j))).symm

/-- The class premise is supplied by quotient surjectivity for the actual
nonzero full-coefficient tensor vector, rather than assumed. -/
example (i j : Bool) := TensorLayerClasses.cross_class_square D originalSc cutoff L m Λ Λ ν η i j
  (h₁ j) (h₂ i j) rfl (h₄ i j) (G i j) (𝟙 _) (σ i j) (ε i j) (sourceContent i j)
  (chosenVector i j) (representative i j) (representative_spec i j)
example (i j : Bool) : inputVector i j ≠ 0 := inputVector_ne_zero i j
example (i j : Bool) : inputClass i j ≠ 0 :=
  coordinate_ne_zero D originalSc cutoff L (σ i j) (PowerWordLayerClasses.domWord ν η (.cross i j))
    (inputVector i j) (inputVector_ne_zero i j)

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
/-- The literal odd dot in the same nonempty context, on a surviving
full-coefficient vector in its four-E tensor-Hom input. -/
private abbrev G := TensorVacuumWords.wordHom D Sc m cutoff L Λ Λ ν ≫
  W.E false (PowerWordWeight.wordWeight_append D Λ ν false) ≫
    TensorHomContexts.context D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ (ν ++ [false])) η
private theorem sourceContent : (σ.reverse : Multiset Bool) = δ.1 := by
  change ((τ : List Bool) : Multiset Bool) = δ.1
  exact w.content
private def identityEntry : End G := 𝟙 _
private def inputVector := TensorLayerClasses.dotVector D originalSc cutoff L m Λ Λ ν η false
  G (𝟙 _) σ δ sourceContent chosenVector
private theorem evaluated_id : ((((identityEntry.total R) δ).total w) chosenVector) = chosenVector := by
  change (((𝟙 (G.obj R) + 0) δ).total w) chosenVector = _
  rw [add_zero]
  change (𝟙 (((G.obj R) δ).obj w) + 0) chosenVector = _
  simp only [add_zero, SVec.id_apply]
private theorem chosenVector_ne_zero : chosenVector ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have he := congrArg chosenEquiv hz
  simpa only [chosenVector, LinearEquiv.apply_symm_apply, map_zero] using he
private theorem inputVector_ne_zero : inputVector ≠ 0 := by
  intro hv
  have hz := (TensorLayerClasses.dotVector_eq_zero_iff D originalSc cutoff L m Λ Λ ν η false
    G (𝟙 _) σ δ sourceContent chosenVector).mp hv
  change (((identityEntry.total R) δ).total w chosenVector) = 0 at hz
  rw [evaluated_id] at hz
  exact chosenVector_ne_zero hz
private abbrev K := PowerWordQuotientCoordinates.kernel D originalSc cutoff L σ
  (PowerWordLayerClasses.domWord ν η (.dot false))
private def inputClass := PowerWordQuotientCoordinates.coordinate D originalSc cutoff L σ
  (PowerWordLayerClasses.domWord ν η (.dot false)) inputVector
private def representative := Classical.choose ((Submodule.mkQ_surjective K) inputClass)
private theorem representative_spec : inputClass = K.mkQ representative :=
  (Classical.choose_spec ((Submodule.mkQ_surjective K) inputClass)).symm
example := TensorLayerClasses.dot_class_square D originalSc cutoff L m Λ Λ ν η false
  G (𝟙 _) σ δ sourceContent chosenVector representative representative_spec
example : inputVector ≠ 0 := inputVector_ne_zero
example : inputClass ≠ 0 :=
  coordinate_ne_zero D originalSc cutoff L σ (PowerWordLayerClasses.domWord ν η (.dot false))
    inputVector inputVector_ne_zero
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

private theorem sourceContent (i j : Bool) : ((σ i j).reverse : Multiset Bool) = (ε i j).1 := by
  change ((τ i j : List Bool) : Multiset Bool) = (ε i j).1
  exact (w i j).content
private def identityEntry (i j : Bool) : End (G i j) := 𝟙 _
private def inputVector (i j : Bool) := TensorLayerClasses.crossVector D originalSc cutoff L m Λ Λ ν η i j
  (h₁ j) (h₂ i j) (G i j) (𝟙 _) (σ i j) (ε i j) (sourceContent i j) (chosenVector i j)
private theorem evaluated_id (i j : Bool) :
    (((((identityEntry i j).total R) (ε i j)).total (w i j)) (chosenVector i j)) = chosenVector i j := by
  change (((𝟙 ((G i j).obj R) + 0) (ε i j)).total (w i j)) (chosenVector i j) = _
  rw [add_zero]
  change (𝟙 ((((G i j).obj R) (ε i j)).obj (w i j)) + 0) (chosenVector i j) = _
  simp only [add_zero, SVec.id_apply]
private theorem inputVector_ne_zero (i j : Bool) : inputVector i j ≠ 0 := by
  intro hv
  have hz := (TensorLayerClasses.crossVector_eq_zero_iff D originalSc cutoff L m Λ Λ ν η i j
    (h₁ j) (h₂ i j) (G i j) (𝟙 _) (σ i j) (ε i j) (sourceContent i j) (chosenVector i j)).mp hv
  change ((((identityEntry i j).total R) (ε i j)).total (w i j) (chosenVector i j)) = 0 at hz
  rw [evaluated_id] at hz
  exact chosenVector_ne_zero i j hz
private abbrev K (i j : Bool) := PowerWordQuotientCoordinates.kernel D originalSc cutoff L (σ i j)
  (PowerWordLayerClasses.domWord ν η (.cross i j))
private def inputClass (i j : Bool) := PowerWordQuotientCoordinates.coordinate D originalSc cutoff L (σ i j)
  (PowerWordLayerClasses.domWord ν η (.cross i j)) (inputVector i j)
private def representative (i j : Bool) := Classical.choose ((Submodule.mkQ_surjective (K i j)) (inputClass i j))
private theorem representative_spec (i j : Bool) : inputClass i j = (K i j).mkQ (representative i j) :=
  (Classical.choose_spec ((Submodule.mkQ_surjective (K i j)) (inputClass i j))).symm

/-- The class premise is supplied by quotient surjectivity for the actual
nonzero full-coefficient tensor vector, rather than assumed. -/
example (i j : Bool) := TensorLayerClasses.cross_class_square D originalSc cutoff L m Λ Λ ν η i j
  (h₁ j) (h₂ i j) rfl (h₄ i j) (G i j) (𝟙 _) (σ i j) (ε i j) (sourceContent i j)
  (chosenVector i j) (representative i j) (representative_spec i j)
example (i j : Bool) : inputVector i j ≠ 0 := inputVector_ne_zero i j
example (i j : Bool) : inputClass i j ≠ 0 :=
  coordinate_ne_zero D originalSc cutoff L (σ i j) (PowerWordLayerClasses.domWord ν η (.cross i j))
    (inputVector i j) (inputVector_ne_zero i j)

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
/-- The literal odd dot in the same nonempty context, on a surviving
full-coefficient vector in its four-E tensor-Hom input. -/
private abbrev G := TensorVacuumWords.wordHom D Sc m cutoff L Λ Λ ν ≫
  W.E true (PowerWordWeight.wordWeight_append D Λ ν true) ≫
    TensorHomContexts.context D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ (ν ++ [true])) η
private theorem sourceContent : (σ.reverse : Multiset Bool) = δ.1 := by
  change ((τ : List Bool) : Multiset Bool) = δ.1
  exact w.content
private def identityEntry : End G := 𝟙 _
private def inputVector := TensorLayerClasses.dotVector D originalSc cutoff L m Λ Λ ν η true
  G (𝟙 _) σ δ sourceContent chosenVector
private theorem evaluated_id : ((((identityEntry.total R) δ).total w) chosenVector) = chosenVector := by
  change (((𝟙 (G.obj R) + 0) δ).total w) chosenVector = _
  rw [add_zero]
  change (𝟙 (((G.obj R) δ).obj w) + 0) chosenVector = _
  simp only [add_zero, SVec.id_apply]
private theorem chosenVector_ne_zero : chosenVector ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have he := congrArg chosenEquiv hz
  simpa only [chosenVector, LinearEquiv.apply_symm_apply, map_zero] using he
private theorem inputVector_ne_zero : inputVector ≠ 0 := by
  intro hv
  have hz := (TensorLayerClasses.dotVector_eq_zero_iff D originalSc cutoff L m Λ Λ ν η true
    G (𝟙 _) σ δ sourceContent chosenVector).mp hv
  change (((identityEntry.total R) δ).total w chosenVector) = 0 at hz
  rw [evaluated_id] at hz
  exact chosenVector_ne_zero hz
private abbrev K := PowerWordQuotientCoordinates.kernel D originalSc cutoff L σ
  (PowerWordLayerClasses.domWord ν η (.dot true))
private def inputClass := PowerWordQuotientCoordinates.coordinate D originalSc cutoff L σ
  (PowerWordLayerClasses.domWord ν η (.dot true)) inputVector
private def representative := Classical.choose ((Submodule.mkQ_surjective K) inputClass)
private theorem representative_spec : inputClass = K.mkQ representative :=
  (Classical.choose_spec ((Submodule.mkQ_surjective K) inputClass)).symm
example := TensorLayerClasses.dot_class_square D originalSc cutoff L m Λ Λ ν η true
  G (𝟙 _) σ δ sourceContent chosenVector representative representative_spec
example : inputVector ≠ 0 := inputVector_ne_zero
example : inputClass ≠ 0 :=
  coordinate_ne_zero D originalSc cutoff L σ (PowerWordLayerClasses.domWord ν η (.dot true))
    inputVector inputVector_ne_zero
end Dot
end Mixed

end NonVacuity.ELVTensorLayerClasses
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVTensorLayerClasses
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
