/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendMackeyRho
import OddMath.QuiverHecke.CyclotomicAction.PrependTensorCoordinates

/-!
# Coordinates of the twisted prepend induction

The source module of the append-side Mackey boundary is `Ind_(φ_ε) N` with
`φ_ε = prependAlgebra i (n+1) ∘ tw_ε` (`prependTwist`); the parity shift `Π^ε` of
`docs/Nondegeneracy/DeformedMackeyBoundary.md` §1 is the twist `tw_ε`. Since
`tw_ε` is an involution fixing `1`, inducing along `φ_ε` is the same as inducing
along `prependAlgebra i (n+1)` from the twisted module `N^ε` (`TwistModule`), on
which `r` acts as `tw_ε(r)`.

## Main results

* `TwistModule`: `N` with the action precomposed by the parity twist.
* `prependTwistEquiv`: `Ind_(φ_ε) N ≃+ Ind_(prependAlgebra) N^ε`, `z ⊗ m ↦ z ⊗ m`.
* `prependTwistCoordinates`: the affine prepend PBW coordinates of `Ind_(φ_ε) N`,
  `((PrependShuffle (n+1) × ℕ) →₀ N) ≃+ Ind_(φ_ε) N`, sending `single (u, l) m` to
  `prependPBWCorner u l 1 ⊗ m`.
-/

noncomputable section
open CategoryTheory Categorification Categorification.InductionAlong MulOpposite
namespace OddMath.QuiverHecke
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

section Twist
variable (n : ℕ) (p : ZMod 2)

/-- The parity twist as a unital ring endomorphism. -/
def homMatrixTwistRingHom : Hn D Sc n →+* Hn D Sc n :=
  { (homMatrixTwistAlgebra D Sc n p : Hn D Sc n →ₙ+* Hn D Sc n) with
    map_one' := homMatrixTwist_one D Sc n p }

@[simp] theorem homMatrixTwistRingHom_apply (r : Hn D Sc n) :
    homMatrixTwistRingHom D Sc n p r = homMatrixTwist D Sc n p r := rfl

variable (N : Type w) [AddCommGroup N] [Module (Hn D Sc n) N]

/-- `N` with the action precomposed by the parity twist `tw_p`. -/
@[nolint unusedArguments]
def TwistModule (_ : SKM.Scalars D k) (_ : ℕ) (_ : ZMod 2) (N : Type w) : Type w := N

instance : AddCommGroup (TwistModule D Sc n p N) := inferInstanceAs (AddCommGroup N)

instance : Module (Hn D Sc n) (TwistModule D Sc n p N) :=
  Module.compHom N (homMatrixTwistRingHom D Sc n p)

/-- The identity of the underlying group. -/
def toTwistModule : N ≃+ TwistModule D Sc n p N := AddEquiv.refl N

theorem smul_toTwistModule (r : Hn D Sc n) (m : N) :
    r • toTwistModule D Sc n p N m = toTwistModule D Sc n p N (homMatrixTwist D Sc n p r • m) :=
  rfl

theorem toTwistModule_smul (r : Hn D Sc n) (m : N) :
    toTwistModule D Sc n p N (r • m) = homMatrixTwist D Sc n p r • toTwistModule D Sc n p N m := by
  rw [smul_toTwistModule, homMatrixTwist_twice]

end Twist

variable (i : I) (n : ℕ) (ε : ZMod 2) (N : Type w) [AddCommGroup N]
  [Module (Hn D Sc (n + 1)) N]

local notation "φ" => (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))

/-- The two corners agree: `φ_ε(1) = φ(1)`. -/
def prependTwistCorner : InductionAlong.Corner (prependTwist D Sc i n ε) ≃+ InductionAlong.Corner φ where
  toFun z := ⟨z.1, by
    change z.1 * prependAlgebra D Sc i (n + 1) 1 = z.1
    have h : z.1 * prependTwist D Sc i n ε 1 = z.1 := z.2
    exact (congrArg (z.1 * ·) (prependTwist_one D Sc i n ε)).symm.trans h⟩
  invFun z := ⟨z.1, by
    change z.1 * prependTwist D Sc i n ε 1 = z.1
    have h : z.1 * prependAlgebra D Sc i (n + 1) 1 = z.1 := z.2
    exact (congrArg (z.1 * ·) (prependTwist_one D Sc i n ε)).trans h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp] theorem prependTwistCorner_val (z : InductionAlong.Corner (prependTwist D Sc i n ε)) :
    (prependTwistCorner D Sc i n ε z).1 = z.1 := rfl

@[simp] theorem prependTwistCorner_symm_val (z : InductionAlong.Corner φ) :
    ((prependTwistCorner D Sc i n ε).symm z).1 = z.1 := rfl

theorem prependTwistCorner_op_smul (a : Hn D Sc (n + 1))
    (z : InductionAlong.Corner (prependTwist D Sc i n ε)) :
    prependTwistCorner D Sc i n ε (op a • z) =
      op (homMatrixTwist D Sc (n + 1) ε a) • prependTwistCorner D Sc i n ε z := rfl

/-- The forward map `z ⊗ m ↦ z ⊗ m` from `Ind_(φ_ε) N` to `Ind_φ N^ε`. -/
def prependTwistForward : Ind N (prependTwist D Sc i n ε) →+ Ind (TwistModule D Sc (n + 1) ε N) φ :=
  Ind.liftAdd
    (fun z m => Ind.tmul (prependTwistCorner D Sc i n ε z) (toTwistModule D Sc (n + 1) ε N m))
    (fun _ _ _ => by rw [map_add, Ind.add_tmul])
    (fun _ _ _ => by rw [map_add, Ind.tmul_add])
    (fun z a m => by
      rw [prependTwistCorner_op_smul, Ind.op_smul_tmul, toTwistModule_smul])

theorem prependTwistForward_tmul (z : InductionAlong.Corner (prependTwist D Sc i n ε)) (m : N) :
    prependTwistForward D Sc i n ε N (Ind.tmul z m) =
      Ind.tmul (prependTwistCorner D Sc i n ε z) (toTwistModule D Sc (n + 1) ε N m) := rfl

/-- The backward map `z ⊗ m ↦ z ⊗ m` from `Ind_φ N^ε` to `Ind_(φ_ε) N`. -/
def prependTwistBackward : Ind (TwistModule D Sc (n + 1) ε N) φ →+ Ind N (prependTwist D Sc i n ε) :=
  Ind.liftAdd
    (fun z m => Ind.tmul ((prependTwistCorner D Sc i n ε).symm z)
      ((toTwistModule D Sc (n + 1) ε N).symm m))
    (fun _ _ _ => by rw [map_add, Ind.add_tmul])
    (fun _ _ _ => by rw [map_add, Ind.tmul_add])
    (fun z a m => by
      have h : (prependTwistCorner D Sc i n ε).symm (op a • z) =
          op (homMatrixTwist D Sc (n + 1) ε a) • (prependTwistCorner D Sc i n ε).symm z :=
        Subtype.ext (by
          change z.1 * prependAlgebra D Sc i (n + 1) a =
            z.1 * prependAlgebra D Sc i (n + 1)
              (homMatrixTwist D Sc (n + 1) ε (homMatrixTwist D Sc (n + 1) ε a))
          rw [homMatrixTwist_twice])
      rw [h, Ind.op_smul_tmul]
      rfl)

theorem prependTwistBackward_tmul (z : InductionAlong.Corner φ)
    (m : TwistModule D Sc (n + 1) ε N) :
    prependTwistBackward D Sc i n ε N (Ind.tmul z m) =
      Ind.tmul ((prependTwistCorner D Sc i n ε).symm z) ((toTwistModule D Sc (n + 1) ε N).symm m) :=
  rfl

/-- `Ind_(φ_ε) N ≃+ Ind_φ N^ε`, `z ⊗ m ↦ z ⊗ m`. -/
def prependTwistEquiv :
    Ind N (prependTwist D Sc i n ε) ≃+ Ind (TwistModule D Sc (n + 1) ε N) φ where
  toFun := prependTwistForward D Sc i n ε N
  invFun := prependTwistBackward D Sc i n ε N
  left_inv t := by
    induction t using Ind.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul z m =>
      rw [prependTwistForward_tmul, prependTwistBackward_tmul, AddEquiv.symm_apply_apply,
        AddEquiv.symm_apply_apply]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  right_inv t := by
    induction t using Ind.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul z m =>
      rw [prependTwistBackward_tmul, prependTwistForward_tmul, AddEquiv.apply_symm_apply,
        AddEquiv.apply_symm_apply]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  map_add' := map_add _

@[simp] theorem prependTwistEquiv_tmul (z : InductionAlong.Corner (prependTwist D Sc i n ε))
    (m : N) :
    prependTwistEquiv D Sc i n ε N (Ind.tmul z m) =
      Ind.tmul (prependTwistCorner D Sc i n ε z) (toTwistModule D Sc (n + 1) ε N m) := rfl

@[simp] theorem prependTwistEquiv_symm_tmul (z : InductionAlong.Corner φ)
    (m : TwistModule D Sc (n + 1) ε N) :
    (prependTwistEquiv D Sc i n ε N).symm (Ind.tmul z m) =
      Ind.tmul ((prependTwistCorner D Sc i n ε).symm z) ((toTwistModule D Sc (n + 1) ε N).symm m) :=
  rfl

/-- The affine prepend PBW coordinates of the twisted induction. -/
def prependTwistCoordinates :
    ((PrependShuffle (n + 1) × ℕ) →₀ N) ≃+ Ind N (prependTwist D Sc i n ε) :=
  ((Finsupp.mapRange.addEquiv (toTwistModule D Sc (n + 1) ε N)).trans
    (prependTensorEquiv D Sc i (n + 1) (TwistModule D Sc (n + 1) ε N))).trans
    (prependTwistEquiv D Sc i n ε N).symm

@[simp] theorem prependTwistCoordinates_single (q : PrependShuffle (n + 1) × ℕ) (m : N) :
    prependTwistCoordinates D Sc i n ε N (Finsupp.single q m) =
      Ind.tmul ((prependTwistCorner D Sc i n ε).symm (prependPBWCorner D Sc i q.1 q.2 1)) m := by
  simp [prependTwistCoordinates, prependTensorEquiv]

end OddMath.QuiverHecke
