/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.RouquierMixedMate
import StringDiagrams.Super.SCat

/-! # Rectangular cup-crossing-cap components in SCat

The component expansion needed by the prescribed distinct-colour mate of
Brundan–Ellis (1.12). Both bending adjunctions are the same even adjunction;
the crossing changes the order of two different induction functors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.SKM
universe u
variable {k : Type u} [CommRing k] {C : SCat.{u,u,u + 1} k}

end OddMath.SKM
