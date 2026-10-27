/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.MoreGenerators
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The normalization parameter group

This constructs the unsaturated abelian presentation in
`docs/Nondegeneracy/GroundRingDescent.md` §3, a proposed deduction supporting
Brundan–Ellis, arXiv:1701.04133v2, Theorem 8.1 and the §8 conjecture.
The relations encode (1.5) and the supplied normalizations (1.17), retaining
all weights in the original `X`. No independence of roots is required.
This is the group part of the proposed parameter ring, not nondegeneracy
or a construction of its coefficient polynomial ring.
-/

noncomputable section

namespace OddMath.SKM.NormalizationParameterGroup

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X]

/-- Labels for endpoint units and all weight-labelled normalization units. -/
inductive Generator (I : Type u) (X : Type v)
  | t (i j : I)
  | c (μ : X) (i : I)

variable (D : Datum I X)

/-- The three families of additive relators, without saturation. -/
inductive Relation : FreeAbelianGroup (Generator I X) → Prop
  | diagonal (i : I) : Relation (FreeAbelianGroup.of (.t i i))
  | disconnected (i j : I) (h : D.d i j = 0) :
      Relation (FreeAbelianGroup.of (.t i j) - FreeAbelianGroup.of (.t j i))
  | shift (μ : X) (i j : I) :
      Relation (FreeAbelianGroup.of (.c (μ + D.α j) i) -
        FreeAbelianGroup.of (.c μ i) - FreeAbelianGroup.of (.t i j))

/-- Ordinary subgroup closure, not its saturation. -/
def relations : AddSubgroup (FreeAbelianGroup (Generator I X)) :=
  AddSubgroup.closure {r | Relation D r}

/-- The abelian group presenting all compatible endpoint and normalization units. -/
abbrev Group := FreeAbelianGroup (Generator I X) ⧸ relations D

/-- The class of a generator. -/
def of (g : Generator I X) : Group D :=
  QuotientAddGroup.mk' (relations D) (FreeAbelianGroup.of g)

/-- Universal endpoint parameter in additive notation. -/
def t (i j : I) : Group D := of D (.t i j)

/-- Universal normalization parameter in additive notation. -/
def c (μ : X) (i : I) : Group D := of D (.c μ i)

private theorem rel_zero {r : FreeAbelianGroup (Generator I X)} (hr : Relation D r) :
    QuotientAddGroup.mk' (relations D) r = 0 :=
  (QuotientAddGroup.eq_zero_iff r).2 (AddSubgroup.subset_closure hr)

@[simp] theorem t_self (i : I) : t D i i = 0 :=
  rel_zero D (.diagonal i)

theorem t_symm (i j : I) (h : D.d i j = 0) : t D i j = t D j i := by
  have hzero := rel_zero D (.disconnected i j h)
  change t D i j - t D j i = 0 at hzero
  exact sub_eq_zero.mp hzero

theorem c_shift (μ : X) (i j : I) : c D (μ + D.α j) i = t D i j + c D μ i := by
  have hzero := rel_zero D (.shift μ i j)
  change c D (μ + D.α j) i - c D μ i - t D i j = 0 at hzero
  have := sub_eq_zero.mp hzero
  exact (sub_eq_iff_eq_add.mp this)

variable {A : Type w} [AddCommGroup A]

/-- Compatible values in an arbitrary abelian group extend to the presented group. -/
def lift (tv : I → I → A) (cv : X → I → A)
    (ht : ∀ i, tv i i = 0)
    (hs : ∀ i j, D.d i j = 0 → tv i j = tv j i)
    (hc : ∀ μ i j, cv (μ + D.α j) i = tv i j + cv μ i) : Group D →+ A :=
  QuotientAddGroup.lift (relations D)
    (FreeAbelianGroup.lift (fun g => match g with | .t i j => tv i j | .c μ i => cv μ i))
    (by
      apply (AddSubgroup.closure_le _).2
      intro r hr
      change FreeAbelianGroup.lift _ r = 0
      cases hr with
      | diagonal i => simpa using ht i
      | disconnected i j h => simp [hs i j h]
      | shift μ i j => simp [hc μ i j])

@[simp] theorem lift_t (tv : I → I → A) (cv : X → I → A) ht hs hc (i j : I) :
    lift D tv cv ht hs hc (t D i j) = tv i j := by
  simp [lift, t, of]

@[simp] theorem lift_c (tv : I → I → A) (cv : X → I → A) ht hs hc (μ : X) (i : I) :
    lift D tv cv ht hs hc (c D μ i) = cv μ i := by
  simp [lift, c, of]

/-- Values on the two generator families determine the homomorphism uniquely. -/
@[ext] theorem hom_ext {f g : Group D →+ A}
    (ht : ∀ i j, f (t D i j) = g (t D i j))
    (hc : ∀ μ i, f (c D μ i) = g (c D μ i)) : f = g := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro x
  cases x with
  | t i j => exact ht i j
  | c μ i => exact hc μ i

variable {R : Type w} [CommRing R] {D}

/-- Specialization to the supplied units, with no additional ring hypotheses. -/
def specialize {Sc : Scalars D R} (cs : CScalars Sc) :
    Group D →+ Additive Rˣ :=
  lift D (fun i j => Additive.ofMul (Sc.t i j)) (fun μ i => Additive.ofMul (cs.c μ i))
    (fun i => congrArg Additive.ofMul (Sc.t_self i))
    (fun i j h => congrArg Additive.ofMul (Sc.t_symm_of_d_eq_zero i j h))
    (fun μ i j => congrArg Additive.ofMul (cs.shift μ i j))

@[simp] theorem specialize_t {Sc : Scalars D R} (cs : CScalars Sc) (i j : I) :
    (specialize cs (t D i j)).toMul = Sc.t i j := by
  simp [specialize]

@[simp] theorem specialize_c {Sc : Scalars D R} (cs : CScalars Sc) (μ : X) (i : I) :
    (specialize cs (c D μ i)).toMul = cs.c μ i := by
  simp [specialize]

/-- The universal units specialization is unique. -/
theorem specialize_unique {Sc : Scalars D R} (cs : CScalars Sc)
    (f : Group D →+ Additive Rˣ)
    (ht : ∀ i j, (f (t D i j)).toMul = Sc.t i j)
    (hc : ∀ μ i, (f (c D μ i)).toMul = cs.c μ i) : f = specialize cs := by
  apply hom_ext
  · intro i j
    exact congrArg Additive.ofMul ((ht i j).trans (specialize_t cs i j).symm)
  · intro μ i
    exact congrArg Additive.ofMul ((hc μ i).trans (specialize_c cs μ i).symm)

end OddMath.SKM.NormalizationParameterGroup
