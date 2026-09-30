import OddMath.Frontier.EQOnhDGZn
import DG.Module.Opposite
import DG.Module.EndBimodule

/-!
# Corollary 3.9 in the language of endomorphism dg algebras

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§3.2, Corollary 3.9: `(ONH_n, d) ≅ END_{OΛ_n^op}(Z_n)`.

The `DG` library encodes right modules over `OΛ = OΛ_{n+2}` as left modules over the graded
opposite dg algebra `OΛᵒᵖ` (Koszul rule `op c • z = (-1)^{|c||z|} z c`,
`DG.DGRightModule.opModule`), and its endomorphism dg algebra `END_{OΛᵒᵖ}(Z)`
(`DG.DGModule.END`) acts on `Z` **on the right**, with product `f * g = (-1)^{|f||g|} g ∘ f`.
Accordingly the left action of `ONH = ONH_{n+2}` on `Z = Z_{n+2}` becomes a right action of the
graded opposite `ONHᵒᵖ` (`z • p = (-1)^{|p||z|} p z`), and Corollary 3.9 takes the form of a
morphism of dg rings

  `ONH.toENDZn n : ONHᵒᵖ →ᵈᵍ+* END_{OΛᵒᵖ}(Z_{n+2})`,

sending `p` to the endomorphism by which `p` acts (`ONH.toENDZn_smul`); it is injective
(`ONH.toENDZn_injective`, faithfulness of the polynomial representation). Equivalently, `p ↦ (z ↦ p z)`
is a morphism of dg rings from `ONH_{n+2}` to the opposite of `END_{OΛᵒᵖ}(Z_{n+2})`, i.e. to the
dg algebra of `OΛ`-linear endomorphisms under composition, as in Ellis–Qi.

That `ONH.toENDZn n` is also surjective, hence an isomorphism of dg algebras (Corollary 3.9), is
proved in `OddMath.Frontier.EQOnhDGEndIso`.
-/

noncomputable section

namespace OddMath.Frontier.EQOnhDG

open OddMath.Frontier.EQSkewDifferential (OPol OPolAlpha Zn osymDG)
open NilHeckeAction
open DG (GradedOpposite DGAlgebra)

variable {n : ℕ}

namespace ONH

/-- The graded opposite `OΛ_{n+2}ᵒᵖ` of the dg algebra `OΛ_{n+2}`. -/
abbrev OsymOp (n : ℕ) : Type := GradedOpposite (DGAlgebra.gradingSubmodule ℤ (osymDG (n + 2)))

/-- The graded opposite `ONH_{n+2}ᵒᵖ`. -/
abbrev ONHOp (n : ℕ) : Type := GradedOpposite (DGAlgebra.gradingSubmodule ℤ (ONH n))

/-- The double graded opposite `(ONH_{n+2}ᵒᵖ)ᵒᵖ`. -/
abbrev ONHOpOp (n : ℕ) : Type := GradedOpposite (DGAlgebra.gradingSubmodule ℤ (ONHOp n))

/-- `Z_{n+2}`, as a dg `(OΛ_{n+2}ᵒᵖ, ONH_{n+2}ᵒᵖ)`-bimodule. -/
def ZnE (n : ℕ) : Type := Zn (n + 2)

namespace ZnE

instance : AddCommGroup (ZnE n) := inferInstanceAs (AddCommGroup (Zn (n + 2)))
instance : DG.DGAddCommGroup (ZnE n) := inferInstanceAs (DG.DGAddCommGroup (Zn (n + 2)))
instance : Module (osymDG (n + 2))ᵐᵒᵖ (ZnE n) :=
  inferInstanceAs (Module (osymDG (n + 2))ᵐᵒᵖ (Zn (n + 2)))
instance : DG.DGRightModule (osymDG (n + 2)) (ZnE n) :=
  inferInstanceAs (DG.DGRightModule (osymDG (n + 2)) (Zn (n + 2)))
instance : Module (ONH n) (ZnE n) := inferInstanceAs (Module (ONH n) (Zn (n + 2)))
instance : DG.DGModule (ONH n) (ZnE n) := inferInstanceAs (DG.DGModule (ONH n) (Zn (n + 2)))
instance : SMulCommClass (ONH n) (osymDG (n + 2))ᵐᵒᵖ (ZnE n) :=
  inferInstanceAs (SMulCommClass (ONH n) (osymDG (n + 2))ᵐᵒᵖ (Zn (n + 2)))

/-- The identification with `Z_{n+2}`. -/
def equiv (n : ℕ) : Zn (n + 2) ≃+ ZnE n := AddEquiv.refl _

/-- The left action of `OΛᵒᵖ`: `op c • z = (-1)^{|c||z|} z c`. -/
instance instModuleOsymOp : Module (OsymOp n) (ZnE n) := DG.DGRightModule.opModule ℤ

instance instDGModuleOsymOp : DG.DGModule (OsymOp n) (ZnE n) :=
  DG.DGRightModule.dgModule_opModule ℤ

/-- The dg ring isomorphism `(ONHᵒᵖ)ᵒᵖ ≃ ONH`, as a morphism of dg rings. -/
def opOpHom (n : ℕ) : ONHOpOp n →ᵈᵍ+* ONH n :=
  (DG.GradedOpposite.opOpDGAlgEquiv (R := ℤ) (A := ONH n)).toDGAlgHom.toDGRingHom

instance instModuleONHOpOp : Module (ONHOpOp n) (ZnE n) := Module.compHom _ (opOpHom n).toRingHom

instance instDGModuleONHOpOp : DG.DGModule (ONHOpOp n) (ZnE n) :=
  DG.DGModule.compHom (opOpHom n) (ZnE n)

/-- The right action of `ONHᵒᵖ`: `z • op p = (-1)^{|p||z|} p z`. -/
instance instModuleONHOpMop : Module (ONHOp n)ᵐᵒᵖ (ZnE n) := DG.DGModule.mulOppositeModule ℤ

instance instDGRightModuleONHOp : DG.DGRightModule (ONHOp n) (ZnE n) :=
  DG.DGModule.dgRightModule_mulOppositeModule ℤ

theorem osymOp_smul_of_mem {i j : ℤ} {c : osymDG (n + 2)} {z : ZnE n}
    (hc : c ∈ DG.grading i) (hz : z ∈ DG.grading j) :
    DG.GradedOpposite.op (DGAlgebra.gradingSubmodule ℤ (osymDG (n + 2))) c • z =
      DG.koszulSign (i * j) • (MulOpposite.op c • z) :=
  DG.DGRightModule.opModule_op_smul_of_mem ℤ hc hz

theorem onhOp_smul_of_mem {i j : ℤ} {p : ONH n} {z : ZnE n}
    (hp : p ∈ DG.grading i) (hz : z ∈ DG.grading j) :
    MulOpposite.op (DG.GradedOpposite.op (DGAlgebra.gradingSubmodule ℤ (ONH n)) p) • z =
      DG.koszulSign (i * j) • (p • z) :=
  DG.DGModule.mulOppositeModule_op_smul_of_mem ℤ
    ((DG.GradedOpposite.op_mem_dgGrading_iff (R := ℤ)).mpr hp) hz

instance instSMulCommClass : SMulCommClass (OsymOp n) (ONHOp n)ᵐᵒᵖ (ZnE n) where
  smul_comm x y z := by
    induction x using DG.induction_on generalizing y z with
    | h_zero => rw [zero_smul, zero_smul, smul_zero]
    | h_add x x' hx hx' => rw [add_smul, add_smul, smul_add, hx, hx']
    | @h_homogeneous a x =>
      obtain ⟨x, hx⟩ := x
      obtain ⟨y, rfl⟩ : ∃ y' : ONHOp n, y = MulOpposite.op y' := ⟨y.unop, (MulOpposite.op_unop y).symm⟩
      induction y using DG.induction_on generalizing z with
      | h_zero => rw [MulOpposite.op_zero, zero_smul, zero_smul, smul_zero]
      | h_add y y' hy hy' => rw [MulOpposite.op_add, add_smul, add_smul, smul_add, hy, hy']
      | @h_homogeneous b y =>
        obtain ⟨y, hy⟩ := y
        induction z using DG.induction_on with
        | h_zero => rw [smul_zero, smul_zero, smul_zero]
        | h_add z z' hz hz' => simp only [smul_add, hz, hz']
        | @h_homogeneous k z =>
          obtain ⟨z, hz⟩ := z
          have hc := (DG.GradedOpposite.mem_dgGrading_iff (R := ℤ)).mp hx
          have hp := (DG.GradedOpposite.mem_dgGrading_iff (R := ℤ)).mp hy
          set c := DG.GradedOpposite.unop (DGAlgebra.gradingSubmodule ℤ (osymDG (n + 2))) x
          set p := DG.GradedOpposite.unop (DGAlgebra.gradingSubmodule ℤ (ONH n)) y
          have ex : x = DG.GradedOpposite.op (DGAlgebra.gradingSubmodule ℤ (osymDG (n + 2))) c :=
            rfl
          have ey : y = DG.GradedOpposite.op (DGAlgebra.gradingSubmodule ℤ (ONH n)) p := rfl
          simp only at hx hy hz ⊢
          have hpz : p • z ∈ DG.grading (b + k) := DG.smul_mem_grading hp hz
          have hcz : MulOpposite.op c • z ∈ DG.grading (k + a) := DG.op_smul_mem_grading hc hz
          have L : x • (MulOpposite.op y • z) =
              ((DG.koszulSign (b * k) : ℤ) * DG.koszulSign (a * (b + k))) •
                (MulOpposite.op c • (p • z)) := by
            rw [ey, onhOp_smul_of_mem hp hz, Units.smul_def,
              smul_comm x ((DG.koszulSign (b * k) : ℤˣ) : ℤ), ex, osymOp_smul_of_mem hc hpz,
              Units.smul_def, smul_smul]
          have R : MulOpposite.op y • (x • z) =
              ((DG.koszulSign (a * k) : ℤ) * DG.koszulSign (b * (k + a))) •
                (p • (MulOpposite.op c • z)) := by
            rw [ex, osymOp_smul_of_mem hc hz, Units.smul_def,
              smul_comm (MulOpposite.op y) ((DG.koszulSign (a * k) : ℤˣ) : ℤ), ey,
              onhOp_smul_of_mem hp hcz, Units.smul_def, smul_smul]
          rw [L, R, ← smul_comm p (MulOpposite.op c) z, ← Units.val_mul, ← Units.val_mul,
            ← DG.koszulSign_add, ← DG.koszulSign_add]
          congr 3
          ring

instance instDGBimodule : DG.DGBimodule (OsymOp n) (ONHOp n) (ZnE n) := DG.DGBimodule.mk'

end ZnE

/-- **Ellis–Qi, Corollary 3.9** (dg form): the action of `ONH_{n+2}` on `Z_{n+2}` as a morphism of
dg rings `ONH_{n+2}ᵒᵖ → END_{OΛ_{n+2}ᵒᵖ}(Z_{n+2})` (the `DG` library's endomorphism dg algebra acts
on the right; see the module docstring). -/
def toENDZn (n : ℕ) : ONHOp n →ᵈᵍ+* DG.DGModule.END (OsymOp n) (ZnE n) where
  toRingHom := DG.DGBimodule.toEND (OsymOp n) (ZnE n)
  map_mem' hb := DG.DGBimodule.toEND_mem_grading hb
  map_d' b := DG.DGBimodule.toEND_d b

/-- The endomorphism `toENDZn n (op p)` acts on `Z_{n+2}` as `p` does, with the Koszul sign of the
right action: `z · toENDZn (op p) = (-1)^{|p||z|} p z`. -/
theorem toENDZn_smul {i j : ℤ} {p : ONH n} (hp : p ∈ DG.grading i) {z : ZnE n}
    (hz : z ∈ DG.grading j) :
    MulOpposite.op (toENDZn n (DG.GradedOpposite.op (DGAlgebra.gradingSubmodule ℤ (ONH n)) p)) • z =
      DG.koszulSign (i * j) • (p • z) := by
  rw [show toENDZn n _ = DG.DGBimodule.toEND (OsymOp n) (ZnE n) _ from rfl,
    DG.DGBimodule.op_toEND_smul, ZnE.onhOp_smul_of_mem hp hz]

theorem eq_zero_of_toENDZn_eq_zero {i : ℤ} {w : ONHOp n} (hw : w ∈ DG.grading i)
    (h : toENDZn n w = 0) : w = 0 := by
  have hp := (DG.GradedOpposite.mem_dgGrading_iff (R := ℤ)).mp hw
  set p := DG.GradedOpposite.unop (DGAlgebra.gradingSubmodule ℤ (ONH n)) w
  have ew : w = DG.GradedOpposite.op (DGAlgebra.gradingSubmodule ℤ (ONH n)) p := rfl
  have hz : ∀ z : ZnE n, p • z = 0 := by
    intro z
    induction z using DG.induction_on with
    | h_zero => rw [smul_zero]
    | h_add z z' hz hz' => rw [smul_add, hz, hz', add_zero]
    | @h_homogeneous j z =>
      have := toENDZn_smul hp z.2
      rw [← ew, h, MulOpposite.op_zero, zero_smul] at this
      have h2 := congrArg (DG.koszulSign (i * j) • ·) this
      simp only [smul_zero, smul_smul, Int.units_mul_self, one_smul] at h2
      exact h2.symm
  rw [ew, eq_zero_of_forall_smul_eq_zero hz, map_zero]

/-- `toENDZn n` is injective: the action of `ONH_{n+2}` on `Z_{n+2}` is faithful. -/
theorem toENDZn_injective : Function.Injective (toENDZn n) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro w hw
  have hcomp : ∀ i, (DirectSum.decompose (DG.grading (M := ONHOp n)) w i : ONHOp n) = 0 := by
    intro i
    have := (toENDZn n).decompose_apply w i
    rw [hw, DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero] at this
    exact eq_zero_of_toENDZn_eq_zero (DirectSum.decompose (DG.grading (M := ONHOp n)) w i).2
      this.symm
  rw [← DirectSum.sum_support_decompose (DG.grading (M := ONHOp n)) w]
  exact Finset.sum_eq_zero fun i _ => hcomp i

end ONH

end OddMath.Frontier.EQOnhDG

end
