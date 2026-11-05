/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ScalarChangePresentation
import OddMath.SKM.GrassmannianOdd

/-!
# Coefficient change for the integral form

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, (1.24), (5.9), (5.10).
The relations of the integral form are imposed only when `2` is not invertible. Along a ring map
`R → S` in which `2` becomes invertible only in `S` they map to identities that hold in the target
presentation because of (1.24), (5.9) and (5.10) there (`cl_zSq`, `cl_zRight`, `cl_zLeft`), which
are proved from the other relations. This needs a normalization `cs : CScalars Sc` to state the
bubbles used in the proof.
-/

noncomputable section

namespace OddMath.SKM.ScalarChange

open CategoryTheory StringDiagrams Presentation

universe u v w w'

variable {R : Type w} {S : Type w'} [CommRing R] [CommRing S] (f : R →+* S)
  {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {Sc : IntegralScalars D R}

/-- Coefficient change carries the relations of the integral form into the target ideal whenever
the source admits a normalization `cs`. -/
theorem ZTransport.of_cScalars (cs : CScalars Sc) : ZTransport f D Sc := by
  by_cases h : IsUnit (2 : R) ∨ ¬IsUnit (2 : S)
  · exact .of_or f D Sc h
  have hR : ¬IsUnit (2 : R) := fun hR => h (.inl hR)
  refine ⟨fun b => ?_⟩
  by_cases hp : D.parity b.i = 1
  swap
  · cases b <;> simp [relation, ZBase.i] at hp ⊢ <;> rw [zGate_of_parity D _ _ hp, coeff_zero,
      lin_zero]
  cases b with
  | sq i ν =>
    simp only [relation, zGate_of_not_isUnit D i _ hp hR, dg, coeff_of, lin_of]
    rw [← cl_of]
    exact cl_zSq (cScalars D f cs) i ν hp
  | right i ν n hn =>
    simp only [relation, zGate_of_not_isUnit D i _ hp hR, dg, coeff_sub, coeff_smul, coeff_of,
      map_zsign, lin_sub, lin_smul, lin_of, sub_eq_zero]
    rw [← cl_of, ← cl_of]
    simpa only [List.append_assoc] using cl_zRight (cScalars D f cs) i ν hp n hn
  | left i ν n hn =>
    simp only [relation, zGate_of_not_isUnit D i _ hp hR, dg, coeff_sub, coeff_smul, coeff_of,
      map_zsign, lin_sub, lin_smul, lin_of, sub_eq_zero]
    rw [← cl_of, ← cl_of]
    simpa only [List.append_assoc] using cl_zLeft (cScalars D f cs) i ν hp n hn

end OddMath.SKM.ScalarChange
