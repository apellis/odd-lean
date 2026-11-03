import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTripleLastBlockComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierData

/-! # The second prescribed multicolour crossing on three inductions

Brundan--Ellis (1.9). The last-pair crossing is evaluated on the actual
first induced product, with its common first predecessor and both
last-pair weight paths retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {a b c c' d : X}
  (hal : a + D.α l = b) (hbj : b + D.α j = c) (hci : c + D.α i = d)
  (hbi : b + D.α i = c') (hcj : c' + D.α j = d)
local notation "E₁" => elvE D Sc cutoff bound l Λ hal
local notation "E₂" => elvE D Sc cutoff bound j Λ hbj
local notation "E₃" => elvE D Sc cutoff bound i Λ hci
local notation "E₂'" => elvE D Sc cutoff bound i Λ hbi
local notation "E₃'" => elvE D Sc cutoff bound j Λ hcj
local notation "p" => D.parity i * D.parity j

/-- The second given crossing, after the literal first weight induction. -/
abbrev elvWeightSuffixCross : E₁ ≫ E₂ ≫ E₃ ⟶ E₁ ≫ E₂' ≫ E₃' :=
  E₁ ◁ elvActionCross D Sc cutoff bound i j Λ hbj hci hbi hcj

/-- The literal suffix uses the prescribed component on the actual first-induced product. -/
theorem elvWeightSuffixCross_total
    (M : ELVWeightProduct D Sc cutoff bound Λ a) (ε : WeightBlocks D Λ d) :
    (elvWeightSuffixCross D Sc cutoff bound i j l Λ hal hbj hci hbi hcj).total M ε =
      elvWeightCrossComponent D Sc cutoff bound i j Λ hbj hci hbi hcj p
        ((elvEFunctor D Sc cutoff bound l Λ hal).obj M) ε :=
  congrFun (supernatural_total_of_mem
    (elvActionCross_mem D Sc cutoff bound i j Λ hbj hci hbi hcj) ((E₁).obj M)) ε

/-- The given suffix crossing at its common first predecessor and specified output. -/
theorem elvWeightSuffixCross_lastBlock
    (β : WeightBlocks D Λ a) (ε : WeightBlocks D Λ d)
    (hε : blockSucc₂ D i j Λ hbj hci (blockSucc D Λ l hal β) = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ a) :
    (elvWeightSuffixCross D Sc cutoff bound i j l Λ hal hbj hci hbi hcj).total M ε =
      (elvWeightCrossVia D Sc cutoff bound i j Λ hbj hci hbi hcj
        (blockSucc D Λ l hal β) ε hε).app p ((elvEFunctor D Sc cutoff bound l Λ hal).obj M) := by
  rw [elvWeightSuffixCross_total]
  exact elvWeightCrossComponent_of D Sc cutoff bound i j Λ hbj hci hbi hcj p _ _ ε hε

end OddMath.QuiverHecke.ELVOld
