import OddMath.Frontier.EQOnhDGEnd

/-!
# Corollary 3.9: `ONH_{n+2}ᵒᵖ ≅ END_{OΛᵒᵖ}(Z_{n+2})` as dg algebras

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§3.2, Corollary 3.9: `(ONH_n, d) ≅ END_{OΛ_n^op}(Z_n)`.

With the conventions of `OddMath.Frontier.EQOnhDGEnd` (the `DG` library's endomorphism dg algebra
acts on the right, so the left action of `ONH` appears as a right action of the graded opposite
`ONHᵒᵖ`), the morphism of dg rings `ONH.toENDZn n : ONHᵒᵖ →ᵈᵍ+* END_{OΛᵒᵖ}(Z_{n+2})` is
bijective (`ONH.toENDZn_bijective`), hence an isomorphism of dg `ℤ`-algebras
(`ONH.toENDZnEquiv`).

* `ONH.mem_grading_of_smul_mem`: an element of `ONH_{n+2}` shifting the degree of `Z_{n+2}` by
  `i` is homogeneous of degree `i`;
* `ONH.cochain_op_smul`: an `OΛᵒᵖ`-linear cochain on `Z_{n+2}` (Koszul-signed linearity) is
  right `OΛ`-linear in the unsigned sense;
* surjectivity: such a cochain is right `OΛ`-linear, hence (EKL's
  `ONH_N ≅ End_{OΛ̃_N}(OPol_N)`, `EQZn.onhEndEquiv`) the operator of an element of `ONH_{n+2}`,
  which is homogeneous of the degree of the cochain.
-/

noncomputable section

namespace OddMath.Frontier.EQOnhDG

open OddMath.SkewPolynomial (SkewPolynomial)
open OddMath.Frontier.EQSkewDifferential (OPol OPolAlpha Zn osymDG twistRev)
open NilHeckeAction
open DG (GradedOpposite DGAlgebra)

variable {n : ℕ}

namespace ONH

/-- **Homogeneity from the action**: if `p ∈ ONH_{n+2}` maps `Z_{n+2}` of each degree `j` to
degree `i + j`, then `p` is homogeneous of degree `i`. -/
theorem mem_grading_of_smul_mem {p : ONH n} {i : ℤ}
    (h : ∀ {j : ℤ} {z : Zn (n + 2)}, z ∈ DG.grading j → p • z ∈ DG.grading (i + j)) :
    p ∈ DG.grading i := by
  classical
  have hcomp : ∀ m, m ≠ i → (DirectSum.decompose (DG.grading (M := ONH n)) p m : ONH n) = 0 := by
    intro m hm
    refine eq_zero_of_forall_smul_eq_zero fun z => ?_
    induction z using DG.induction_on with
    | h_zero => rw [smul_zero]
    | h_add z z' hz hz' => rw [smul_add, hz, hz', add_zero]
    | @h_homogeneous j z =>
      have key := DG.decompose_map (k := j) ((smulAddHom (ONH n) (Zn (n + 2))).flip z)
        (fun hq => DG.smul_mem_grading hq z.2) p m
      change (DirectSum.decompose (DG.grading (M := Zn (n + 2))) (p • (z : Zn (n + 2))) (m + j) :
          Zn (n + 2)) = (DirectSum.decompose (DG.grading (M := ONH n)) p m : ONH n) • (z : Zn (n + 2))
        at key
      rw [← key, DirectSum.decompose_of_mem_ne _ (h z.2) (by omega)]
  rw [← DirectSum.sum_support_decompose (DG.grading (M := ONH n)) p]
  refine AddSubgroup.sum_mem _ fun m _ => ?_
  by_cases hm : m = i
  · subst hm; exact (DirectSum.decompose (DG.grading (M := ONH n)) p m).2
  · rw [hcomp m hm]; exact zero_mem _

/-- An `OΛᵒᵖ`-linear cochain on `Z_{n+2}` (Koszul-signed linearity) commutes with the right action
of `OΛ` without signs. -/
theorem cochain_op_smul {i : ℤ} (f : DG.Cochain (OsymOp n) (ZnE n) (ZnE n) i)
    (c : osymDG (n + 2)) (z : ZnE n) : f (MulOpposite.op c • z) = MulOpposite.op c • f z := by
  induction c using DG.induction_on generalizing z with
  | h_zero => rw [MulOpposite.op_zero, zero_smul, zero_smul, map_zero]
  | h_add c c' hc hc' => rw [MulOpposite.op_add, add_smul, add_smul, map_add, hc, hc']
  | @h_homogeneous a c =>
    obtain ⟨c, hc⟩ := c
    induction z using DG.induction_on with
    | h_zero => rw [smul_zero, map_zero, smul_zero]
    | h_add z z' hz hz' => rw [smul_add, map_add, hz, hz', map_add, smul_add]
    | @h_homogeneous k z =>
      obtain ⟨z, hz⟩ := z
      have e : ∀ {l : ℤ} {y : ZnE n}, y ∈ DG.grading l →
          MulOpposite.op c • y = DG.koszulSign (a * l) •
            (DG.GradedOpposite.op (DGAlgebra.gradingSubmodule ℤ (osymDG (n + 2))) c • y) := by
        intro l y hy
        rw [ZnE.osymOp_smul_of_mem hc hy, smul_smul, Int.units_mul_self, one_smul]
      have hop := (DG.GradedOpposite.op_mem_dgGrading_iff (R := ℤ)).mpr hc
      simp only
      rw [e hz, DG.Cochain.map_units_smul, DG.Cochain.map_smul f hop, e (f.map_mem hz), smul_smul,
        ← DG.koszulSign_add]
      congr 2
      ring

/-- The additive endomorphism of `OPol_{n+2}` underlying a cochain on `Z_{n+2}`. -/
def cochainEnd {i : ℤ} (f : DG.Cochain (OsymOp n) (ZnE n) (ZnE n) i) :
    Module.End ℤ (SkewPolynomial (n + 2)) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun g => (OPolAlpha.equiv _ (EQSkewDifferential.oddStrands (n + 2))).symm
        (f (ZnE.equiv n (OPolAlpha.equiv _ _ g)))
      map_zero' := by rw [map_zero, map_zero, map_zero, map_zero]
      map_add' := fun g g' => by rw [map_add, map_add, map_add, map_add] }

theorem cochainEnd_mem {i : ℤ} (f : DG.Cochain (OsymOp n) (ZnE n) (ZnE n) i) :
    cochainEnd f ∈ EQZn.rightOsymEnd (n + 2) := by
  intro g c hc
  let c' : osymDG (n + 2) :=
    ⟨OPol.equiv (n + 2) c, EQSkewDifferential.mem_osymDG.mpr (by rwa [RingEquiv.symm_apply_apply])⟩
  have hsmul : ∀ y : ZnE n, (OPolAlpha.equiv _ (EQSkewDifferential.oddStrands (n + 2))).symm
      (MulOpposite.op c' • y) =
        (OPolAlpha.equiv _ (EQSkewDifferential.oddStrands (n + 2))).symm y * twistRev (n + 2) c :=
    fun y => EQSkewDifferential.Zn.symm_op_smul (OPol.equiv (n + 2) c) y
  have h1 : ZnE.equiv n (OPolAlpha.equiv _ _ (g * twistRev (n + 2) c)) =
      MulOpposite.op c' • ZnE.equiv n (OPolAlpha.equiv _ _ g) := by
    apply (OPolAlpha.equiv _ (EQSkewDifferential.oddStrands (n + 2))).symm.injective
    rw [hsmul]
    rfl
  change (OPolAlpha.equiv _ (EQSkewDifferential.oddStrands (n + 2))).symm
      (f (ZnE.equiv n (OPolAlpha.equiv _ _ (g * twistRev (n + 2) c)))) =
    (OPolAlpha.equiv _ (EQSkewDifferential.oddStrands (n + 2))).symm
      (f (ZnE.equiv n (OPolAlpha.equiv _ _ g))) * twistRev (n + 2) c
  rw [h1, cochain_op_smul, hsmul]

/-- The element of `ONH_{n+2}` acting on `Z_{n+2}` as a given cochain. -/
def ofCochain {i : ℤ} (f : DG.Cochain (OsymOp n) (ZnE n) (ZnE n) i) : ONH n :=
  equiv n ((EQZn.onhEndEquiv n).symm ⟨cochainEnd f, cochainEnd_mem f⟩)

theorem ofCochain_smul {i : ℤ} (f : DG.Cochain (OsymOp n) (ZnE n) (ZnE n) i) (z : ZnE n) :
    ofCochain f • z = f z := by
  have h := congrArg Subtype.val
    ((EQZn.onhEndEquiv n).apply_symm_apply ⟨cochainEnd f, cochainEnd_mem f⟩)
  apply (OPolAlpha.equiv _ (EQSkewDifferential.oddStrands (n + 2))).symm.injective
  have h2 := LinearMap.congr_fun h ((OPolAlpha.equiv _ (EQSkewDifferential.oddStrands (n + 2))).symm z)
  rw [EQZn.onhEndEquiv_apply] at h2
  change action n ((EQZn.onhEndEquiv n).symm ⟨cochainEnd f, cochainEnd_mem f⟩)
    ((OPolAlpha.equiv _ _).symm z) = _
  rw [h2]
  rfl

theorem ofCochain_mem_grading {i : ℤ} (f : DG.Cochain (OsymOp n) (ZnE n) (ZnE n) i) :
    ofCochain f ∈ DG.grading i :=
  mem_grading_of_smul_mem fun {j z} hz => by
    have := f.map_mem (x := (z : ZnE n)) hz
    rw [add_comm] at this
    exact (ofCochain_smul f z).symm ▸ this

theorem toENDZn_ofCochain {i : ℤ} (f : DG.Cochain (OsymOp n) (ZnE n) (ZnE n) i) :
    toENDZn n (DG.GradedOpposite.op (DGAlgebra.gradingSubmodule ℤ (ONH n)) (ofCochain f)) =
      DirectSum.of (fun k => DG.Cochain (OsymOp n) (ZnE n) (ZnE n) k) i f := by
  refine DG.DGModule.END.ext_op_smul fun x => ?_
  induction x using DG.induction_on with
  | h_zero => rw [smul_zero, smul_zero]
  | h_add x x' hx hx' => rw [smul_add, smul_add, hx, hx']
  | @h_homogeneous k x =>
    rw [toENDZn_smul (ofCochain_mem_grading f) x.2, DG.DGModule.END.op_of_smul f x.2,
      ofCochain_smul]

/-- `toENDZn n` is surjective: every endomorphism of `Z_{n+2}` over `OΛᵒᵖ` is the action of an
element of `ONH_{n+2}`. -/
theorem toENDZn_surjective : Function.Surjective (toENDZn n) := by
  intro F
  induction F using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of i f => exact ⟨_, toENDZn_ofCochain f⟩
  | add F G hF hG =>
    obtain ⟨w, rfl⟩ := hF
    obtain ⟨w', rfl⟩ := hG
    exact ⟨w + w', map_add _ _ _⟩

theorem toENDZn_bijective : Function.Bijective (toENDZn n) :=
  ⟨toENDZn_injective, toENDZn_surjective⟩

/-- **Ellis–Qi, Corollary 3.9**: `(ONH_{n+2}, d) ≅ END_{OΛ_{n+2}^op}(Z_{n+2})`, as an isomorphism
of dg `ℤ`-algebras `ONH_{n+2}ᵒᵖ ≃ END_{OΛᵒᵖ}(Z_{n+2})` in the conventions of the `DG` library
(endomorphisms act on the right; the graded opposite accounts for the left action of `ONH`). -/
def toENDZnEquiv (n : ℕ) : ONHOp n ≃ᵈᵍₐ[ℤ] DG.DGModule.END (OsymOp n) (ZnE n) :=
  DG.DGAlgEquiv.ofAlgEquiv
    (AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (toENDZn n).toRingHom toENDZn_bijective)
      fun r => by
        rw [eq_intCast (algebraMap ℤ (ONHOp n)) r,
          eq_intCast (algebraMap ℤ (DG.DGModule.END (OsymOp n) (ZnE n))) r]
        exact map_intCast _ r)
    (fun ha => (toENDZn n).map_mem ha) fun a => (toENDZn n).map_d a

theorem toENDZnEquiv_apply (w : ONHOp n) : toENDZnEquiv n w = toENDZn n w := by
  rw [toENDZnEquiv, DG.DGAlgEquiv.coe_ofAlgEquiv]
  rfl

end ONH

end OddMath.Frontier.EQOnhDG

end
