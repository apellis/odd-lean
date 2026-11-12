/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.ReservoirWeightRestriction
import OddMath.QuiverHecke.CyclotomicAction.ParameterTransport
import OddMath.SKM.RouquierMulticolour
import OddMath.SKM.MoreGenerators

/-! # Parameters and multicolour restriction for the pairing extension

Extend the supplied parameters and weight-dependent units by the original
weight projection. The existing factor restriction along `x ↦ (x,0)` then
preserves the multicolour relations and the original supplied units. The
parameter twist commutes with this extension.
-/
noncomputable section
open CategoryTheory StringDiagrams
namespace OddMath.QuiverHecke.ReservoirWeights
universe uI uX uk uB vB wB
variable {I : Type uI} {X : Type uX} [AddCommGroup X]
  (D : SKM.Datum I X) {k : Type uk} [CommRing k]

@[simp] theorem pairingExtension_parity (i : I) :
    (pairingExtension D).parity i = D.parity i := rfl

@[simp] theorem pairingExtension_d (i j : I) :
    (pairingExtension D).d i j = D.d i j := by
  simp [SKM.Datum.d, pairingExtension, SKM.Datum.h, SKM.Datum.α]

@[simp] theorem pairingExtension_dn (i j : I) :
    (pairingExtension D).dn i j = D.dn i j := by
  simp only [SKM.Datum.dn, pairingExtension_d]

/-- The same parameter values on the pairing-complete datum. -/
def pairingExtensionScalars (Sc : SKM.Scalars D k) :
    SKM.Scalars (pairingExtension D) k where
  t := Sc.t
  t_self := Sc.t_self
  t_symm_of_d_eq_zero i j h :=
    Sc.t_symm_of_d_eq_zero i j (by simpa only [pairingExtension_d] using h)
  s := Sc.s
  s_symm := Sc.s_symm
  s_eq_zero := Sc.s_eq_zero
  two_isUnit := Sc.two_isUnit

@[simp] theorem pairingExtensionScalars_t (Sc : SKM.Scalars D k) (i j : I) :
    (pairingExtensionScalars D Sc).t i j = Sc.t i j := rfl

@[simp] theorem pairingExtensionScalars_s (Sc : SKM.Scalars D k)
    (i j : I) (p q : ℕ) :
    (pairingExtensionScalars D Sc).s i j p q = Sc.s i j p q := rfl

/-- Supplied units retain the original weight, including its coroot kernel. -/
def pairingExtensionCScalars {Sc : SKM.Scalars D k} (cs : SKM.CScalars Sc) :
    SKM.CScalars (pairingExtensionScalars D Sc) where
  c ν i := cs.c ν.1 i
  shift ν i j := cs.shift ν.1 i j

@[simp] theorem pairingExtensionCScalars_c {Sc : SKM.Scalars D k}
    (cs : SKM.CScalars Sc) (ν : X × (I → ℤ)) (i : I) :
    (pairingExtensionCScalars D cs).c ν i = cs.c ν.1 i := rfl

@[simp] theorem pairingExtension_ipar_original (i : I) (μ : X) :
    SKM.ipar (pairingExtension D) i (μ, 0) = SKM.ipar D i μ := by
  simp only [SKM.ipar, pairingExtension_parity, pairingExtension_h, Pi.zero_apply, add_zero]

/-- The same symmetrizer controls the extended Cartan datum. -/
def pairingExtensionSymmetrizer (sy : SKM.Symmetrizer D) :
    SKM.Symmetrizer (pairingExtension D) where
  d := sy.d
  pos := sy.pos
  symm i j := by simpa only [pairingExtension_d] using sy.symm i j

theorem pairingExtensionScalars_homogeneous (Sc : SKM.Scalars D k)
    (hc : Sc.Homogeneous) : (pairingExtensionScalars D Sc).Homogeneous := by
  simpa only [SKM.ScalarData.Homogeneous, pairingExtension_d, pairingExtensionScalars_s] using hc

private theorem scalars_ext {S T : SKM.Scalars D k}
    (ht : S.t = T.t) (hs : S.s = T.s) : S = T := by
  cases S
  cases T
  cases ht
  cases hs
  rfl

variable {B : Type uB} [BicategoryStruct.{wB, vB} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

end OddMath.QuiverHecke.ReservoirWeights
