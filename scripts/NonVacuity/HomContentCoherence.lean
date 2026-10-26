import OddMath.SKM.RouquierHomContentCoherence
import StringDiagrams.Super.Envelope
import StringDiagrams.Super.Superalgebra

/-! The double shift and the negative Π self-interchange on the integral
parity envelope. The latter is explicitly different from the identity. -/
noncomputable section
open CategoryTheory StringDiagrams OddMath.SKM
namespace NonVacuity.HomContentCoherence
private abbrev C := Envelope ℤ (UnitSupercat ℤ)
private def point : C := ⟨0, ()⟩

example : homParityShift (k := ℤ) (C := C) 1 ⋙ homParityShift (k := ℤ) 1 ≅
    homParityShift (k := ℤ) (C := C) 0 := homParityShiftAdd 1 1

example :
    (homParityShiftCommute (k := ℤ) (PiSupercategory.pi (R := ℤ) (C := C)) 1).hom.app point ≠
      𝟙 ((PiSupercategory.pi (R := ℤ)).obj ((PiSupercategory.pi (R := ℤ)).obj point)) := by
  intro h
  rw [homParityShiftCommute_pi] at h
  have hi := congrArg (fun f => SuperalgebraCat.toElem (Envelope.toHom f)) h
  change (-1 : ℤ) = 1 at hi
  norm_num at hi

#print axioms homParityShiftAdd
#print axioms homParityShiftCommute_pi
#print axioms homContentPostOutAdjunction
end NonVacuity.HomContentCoherence
