/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.FiniteWeightAlgebra
import OddMath.CoveringQuantum.FiniteWeightDualityExamples

/-!
# Evaluation transport on the infinite-colour complex fixture

The finite lattice retains both the central weight and the infinite-support
seed. These checks use the modified-algebra equivalence, not only lattice
biduality. They assert no generator is nonzero and no bar-consistency.
-/

noncomputable section

namespace OddMath.CoveringQuantum.FiniteWeightAlgebraConsumer

open UDot UDot.FiniteWeightAlgebra FiniteWeightDuality
open SourceWeightLatticeConsumer

local instance : DecidableEq lattice := Classical.decEq _
local instance : DecidableEq (Module.Dual ℤ lattice →+ ℤ) := Classical.decEq _

variable {k : Type*} [CommRing k] (q : kˣ) (π : k)

/-- The existing nonunital modified algebra on the finite source lattice. -/
abbrev A := modified restrictedDatum q π

/-- The same algebra on the additive dual of the full integral dual. -/
abbrev B := modified (dualDatum restrictedDatum) q π

/-- The constructed algebra transport instantiated on the source fixture. -/
def transport : A q π ≃ₗ[k] B q π := modifiedEquiv restrictedDatum q π

theorem transport_mul (x y : A q π) :
    transport q π (x * y) = transport q π x * transport q π y :=
  modifiedEquiv_mul restrictedDatum q π x y

theorem roundtrip (x : A q π) : (transport q π).symm (transport q π x) = x :=
  (transport q π).symm_apply_apply x

theorem roundtrip_dual (x : B q π) : transport q π ((transport q π).symm x) = x :=
  (transport q π).apply_symm_apply x

theorem transport_one (μ : lattice) :
    (transport q π ⟨one restrictedDatum q π μ,
      one_mem_modified restrictedDatum q π μ⟩ :
        CoveringUDot k (dualDatum restrictedDatum) q π) =
      one (dualDatum restrictedDatum) q π (weightEquiv lattice μ) :=
  forward_one restrictedDatum q π μ

theorem transport_symm_one (μ : Module.Dual ℤ lattice →+ ℤ) :
    ((transport q π).symm ⟨one (dualDatum restrictedDatum) q π μ,
      one_mem_modified (dualDatum restrictedDatum) q π μ⟩ :
        CoveringUDot k restrictedDatum q π) =
      one restrictedDatum q π ((weightEquiv lattice).symm μ) :=
  backward_one restrictedDatum q π μ

theorem transport_E (i : colours) (μ : lattice) :
    (transport q π ⟨E restrictedDatum q π i μ,
      E_mem_modified restrictedDatum q π i μ⟩ :
        CoveringUDot k (dualDatum restrictedDatum) q π) =
      E (dualDatum restrictedDatum) q π i (weightEquiv lattice μ) :=
  forward_E restrictedDatum q π i μ

theorem transport_symm_E (i : colours) (μ : Module.Dual ℤ lattice →+ ℤ) :
    ((transport q π).symm ⟨E (dualDatum restrictedDatum) q π i μ,
      E_mem_modified (dualDatum restrictedDatum) q π i μ⟩ :
        CoveringUDot k restrictedDatum q π) =
      E restrictedDatum q π i ((weightEquiv lattice).symm μ) :=
  backward_E restrictedDatum q π i μ

theorem transport_F (i : colours) (μ : lattice) :
    (transport q π ⟨F restrictedDatum q π i μ,
      F_mem_modified restrictedDatum q π i μ⟩ :
        CoveringUDot k (dualDatum restrictedDatum) q π) =
      F (dualDatum restrictedDatum) q π i (weightEquiv lattice μ) :=
  forward_F restrictedDatum q π i μ

theorem transport_symm_F (i : colours) (μ : Module.Dual ℤ lattice →+ ℤ) :
    ((transport q π).symm ⟨F (dualDatum restrictedDatum) q π i μ,
      F_mem_modified (dualDatum restrictedDatum) q π i μ⟩ :
        CoveringUDot k restrictedDatum q π) =
      F restrictedDatum q π i ((weightEquiv lattice).symm μ) :=
  backward_F restrictedDatum q π i μ

theorem centralInWindow_one_roundtrip :
    (transport q π).symm
      (transport q π ⟨one restrictedDatum q π centralInWindow,
        one_mem_modified restrictedDatum q π centralInWindow⟩) =
      ⟨one restrictedDatum q π centralInWindow,
        one_mem_modified restrictedDatum q π centralInWindow⟩ :=
  roundtrip q π _

theorem centralInWindow_E_roundtrip (i : colours) :
    (transport q π).symm
      (transport q π ⟨E restrictedDatum q π i centralInWindow,
        E_mem_modified restrictedDatum q π i centralInWindow⟩) =
      ⟨E restrictedDatum q π i centralInWindow,
        E_mem_modified restrictedDatum q π i centralInWindow⟩ :=
  roundtrip q π _

theorem centralInWindow_F_roundtrip (i : colours) :
    (transport q π).symm
      (transport q π ⟨F restrictedDatum q π i centralInWindow,
        F_mem_modified restrictedDatum q π i centralInWindow⟩) =
      ⟨F restrictedDatum q π i centralInWindow,
        F_mem_modified restrictedDatum q π i centralInWindow⟩ :=
  roundtrip q π _

theorem seedInWindow_one_roundtrip :
    (transport q π).symm
      (transport q π ⟨one restrictedDatum q π seedInWindow,
        one_mem_modified restrictedDatum q π seedInWindow⟩) =
      ⟨one restrictedDatum q π seedInWindow,
        one_mem_modified restrictedDatum q π seedInWindow⟩ :=
  roundtrip q π _

theorem seedInWindow_E_roundtrip (i : colours) :
    (transport q π).symm
      (transport q π ⟨E restrictedDatum q π i seedInWindow,
        E_mem_modified restrictedDatum q π i seedInWindow⟩) =
      ⟨E restrictedDatum q π i seedInWindow,
        E_mem_modified restrictedDatum q π i seedInWindow⟩ :=
  roundtrip q π _

theorem seedInWindow_F_roundtrip (i : colours) :
    (transport q π).symm
      (transport q π ⟨F restrictedDatum q π i seedInWindow,
        F_mem_modified restrictedDatum q π i seedInWindow⟩) =
      ⟨F restrictedDatum q π i seedInWindow,
        F_mem_modified restrictedDatum q π i seedInWindow⟩ :=
  roundtrip q π _

theorem transport_block (μ η : lattice) (x : A q π)
    (hx : (x : CoveringUDot k restrictedDatum q π) ∈ block restrictedDatum q π μ η) :
    (transport q π x : CoveringUDot k (dualDatum restrictedDatum) q π) ∈
      block (dualDatum restrictedDatum) q π (weightEquiv lattice μ) (weightEquiv lattice η) :=
  forward_mem_block restrictedDatum q π hx

end OddMath.CoveringQuantum.FiniteWeightAlgebraConsumer

