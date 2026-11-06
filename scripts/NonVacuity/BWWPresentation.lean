import OddMath.QuiverHecke.BWWPresentation
import NonVacuity.BWWScalars

/-! # The quiver Hecke presentation with Brundan–Wang–Webster parameters

On the datum of `NonVacuity.BWWScalars`: the presentation with `Qᵢⱼ = u³ + v³ + 1` is
parity-homogeneous, and over the Brundan–Ellis parameters `u³ + uv² + v³` it is the quiver
Hecke presentation `pres`.
-/

noncomputable section
namespace NonVacuity.BWWPresentation
open OddMath OddMath.SKM OddMath.QuiverHecke NonVacuity.BWWScalars

example : (presBWW datum constantTerm).IsParityHomogeneous :=
  isParityHomogeneous_presBWW datum constantTerm

example : presBWW datum scalars.toBWW = QuiverHecke.pres datum scalars :=
  presBWW_toBWW datum scalars

end NonVacuity.BWWPresentation
