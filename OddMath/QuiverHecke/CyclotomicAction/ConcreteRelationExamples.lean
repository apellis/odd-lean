/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.MixedComparison
import OddMath.QuiverHecke.CyclotomicAction.BraidCorrection
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ParameterTransport

/-!
# Concrete asymmetric transported-parameter consumers

Consumers of the super port of
`Categorification/KLR/CyclotomicAction/Square.lean` and
`Categorification/KLR/CyclotomicAction/MixedComparison.lean`.
The all-odd datum with Cartan matrix `[[2,-2],[-4,2]]` uses the transported
quadratic `u²-v⁴`. The equations below hold in the concrete word endomorphism
rings and their actual cyclotomic matrix quotients, not a freely specified
representation. They do not prove nonvanishing or local inversion.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke.CyclotomicAction.ConcreteRelationExamples
open AsymmetricParameters

end OddMath.QuiverHecke.CyclotomicAction.ConcreteRelationExamples
