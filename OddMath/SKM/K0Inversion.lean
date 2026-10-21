import OddMath.SKM.K0Relations
import OddMath.SKM.K0Finite

/-!
# Same-colour inversion in the completed envelope

BE2 arXiv:1701.04133v2, Lemma 11.6, mixed relation. The negative-weight
summands have degree `dᵢ(h+1+2n)`, as forced by the degree of the cup in
(1.14). The opposite exponent in the proof display of Lemma 11.6 is a
proof misprint; the statement of the lemma is unchanged.
-/

noncomputable section
namespace OddMath.SKM.K0Relations
open CategoryTheory CategoryTheory.Limits StringDiagrams Presentation
open CategoryTheory.Preadditive

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] (Sc : Scalars D k) (sy : Symmetrizer D)
  (hc : Sc.Homogeneous)

abbrev ef (i : I) (ν : X) (a : ZMod 2) :=
  shifted Sc sy hc ν ν [up i, dn i] (by simp [wt, sh]) 0 a
abbrev fe (i : I) (ν : X) (a : ZMod 2) :=
  shifted Sc sy hc ν ν [dn i, up i] (by simp [wt, sh]) 0 a
abbrev idShift (ν : X) (n : ℤ) (a : ZMod 2) :=
  shifted Sc sy hc ν ν [] rfl n a

/-- The positive-weight summands of inversion (1.13). -/
def plusFamily (i : I) (ν : X) (a : ZMod 2) :
    Fin ((D.h i ν).toNat + 1) →
      ((show UUnderline D Sc sy hc from ⟨⟨⟨⟨⟨ν⟩⟩⟩⟩⟩) ⟶
        (show UUnderline D Sc sy hc from ⟨⟨⟨⟨⟨ν⟩⟩⟩⟩⟩)) :=
  Fin.cases (fe Sc sy hc i ν (D.parity i + a)) fun n =>
    idShift Sc sy hc ν (sy.d i * (D.h i ν - 1 - 2 * n.val)) (n.val * D.parity i + a)

private theorem crossParity (p a : ZMod 2) :
    p * p = a + (p + a) ∧ p * p = (p + a) + a := by revert p a; decide

private theorem shiftParity (p a : ZMod 2) :
    p = a + (p + a) ∧ p = (p + a) + a := by revert p a; decide

def plusProj (i : I) (ν : X) (a : ZMod 2) :
    ∀ n, ef Sc sy hc i ν a ⟶ plusFamily Sc sy hc i ν a n :=
  Fin.cases
    (lift Sc sy hc (sigmaL i i) (sChain_sigmaL i i) (by simp)
      (by rw [parity_sigmaL]; exact (crossParity _ _).1))
    (fun n => lift Sc sy hc (epsL i n.val) (sChain_epsL i n.val)
      (by simp; ring) (by rw [parity_epsL]; exact (shiftParity _ _).1))

def plusIncl (i : I) (ν : X) (a : ZMod 2) :
    ∀ n, plusFamily Sc sy hc i ν a n ⟶ ef Sc sy hc i ν a :=
  Fin.cases
    (-lift Sc sy hc (lcrossL i i) (sChain_lcrossL i i) (by simp)
      (by rw [parity_lcrossL]; exact (crossParity _ _).2))
    (fun n => lift Sc sy hc (dcupL i n.val) (sChain_dcupL i n.val)
      (by simp) (by rw [parity_dcupL, mul_comm]; exact (shiftParity _ _).2))

theorem plus_diag (i : I) (ν : X) (a : ZMod 2) (hh : 0 ≤ D.h i ν) (n) :
    plusIncl Sc sy hc i ν a n ≫ plusProj Sc sy hc i ν a n = 𝟙 _ := by
  refine Fin.cases ?_ (fun n => ?_) n
  · dsimp only [plusIncl, plusProj, Fin.cases_zero]
    rw [neg_comp]
    apply Subtype.ext; apply Subtype.ext
    change -(cl D Sc ν [dn i, up i] [up i, dn i] (lcrossL i i) ≫
      cl D Sc ν [up i, dn i] [dn i, up i] (sigmaL i i)) = 𝟙 _
    rw [cl_comp (sChain_lcrossL i i) (sChain_sigmaL i i),
      cl_invP₂ Sc i ν hh, neg_neg, cl_nil]
  · apply Subtype.ext; apply Subtype.ext
    change cl D Sc ν _ _ _ ≫ cl D Sc ν _ _ _ = 𝟙 _
    rw [cl_comp (sChain_dcupL i n.val) (sChain_epsL i n.val),
      cl_invP₅ Sc i ν n.val n.val (by omega) (by omega), ite_eq_left rfl, cl_nil]

theorem plus_off (i : I) (ν : X) (a : ZMod 2) (n m)
    (hnm : n ≠ m) :
    plusIncl Sc sy hc i ν a n ≫ plusProj Sc sy hc i ν a m = 0 := by
  revert hnm
  refine Fin.cases ?_ (fun n => ?_) n <;> refine Fin.cases ?_ (fun m => ?_) m
  · exact fun h => (h rfl).elim
  · intro _
    dsimp only [plusIncl, plusProj, Fin.cases_zero, Fin.cases_succ]
    rw [neg_comp]
    apply Subtype.ext; apply Subtype.ext
    change -(cl D Sc ν [dn i, up i] [up i, dn i] (lcrossL i i) ≫
      cl D Sc ν [up i, dn i] [] (epsL i m.val)) = 0
    rw [ cl_comp (sChain_lcrossL i i) (sChain_epsL i m.val),
      cl_invP₃ Sc i ν m.val (by omega), neg_zero]
  · intro _
    apply Subtype.ext; apply Subtype.ext
    change cl D Sc ν _ _ _ ≫ cl D Sc ν _ _ _ = 0
    rw [cl_comp (sChain_dcupL i n.val) (sChain_sigmaL i i),
      cl_invP₄ Sc i ν n.val (by omega)]
  · intro h
    apply Subtype.ext; apply Subtype.ext
    change cl D Sc ν _ _ _ ≫ cl D Sc ν _ _ _ = 0
    rw [cl_comp (sChain_dcupL i n.val) (sChain_epsL i m.val),
      cl_invP₅ Sc i ν m.val n.val (by omega) (by omega), ite_eq_right]
    intro e; exact h (congrArg Fin.succ (Fin.ext e.symm))

theorem plus_total (i : I) (ν : X) (a : ZMod 2) (hh : 0 ≤ D.h i ν) :
    ∑ n, plusProj Sc sy hc i ν a n ≫ plusIncl Sc sy hc i ν a n = 𝟙 _ := by
  let forget : (ef Sc sy hc i ν a ⟶ ef Sc sy hc i ν a) →+
      ((pres D Sc).obj (ob D ν [up i, dn i]) ⟶ (pres D Sc).obj (ob D ν [up i, dn i])) :=
    { toFun := fun f => f.1.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Injective forget := fun _ _ h => Subtype.ext (Subtype.ext h)
  apply hf
  rw [Fin.sum_univ_succ]
  simp only [plusProj, plusIncl, Fin.cases_zero, Fin.cases_succ, comp_neg]
  rw [map_add, map_neg, map_sum]
  change -(cl D Sc ν [up i, dn i] [dn i, up i] (sigmaL i i) ≫
      cl D Sc ν [dn i, up i] [up i, dn i] (lcrossL i i)) +
    ∑ n : Fin (D.h i ν).toNat,
      cl D Sc ν [up i, dn i] [] (epsL i n.val) ≫
      cl D Sc ν [] [up i, dn i] (dcupL i n.val) = 𝟙 _
  simp only [cl_comp (sChain_sigmaL i i) (sChain_lcrossL i i),
    cl_comp (sChain_epsL i _) (sChain_dcupL i _)]
  rw [Fin.sum_univ_eq_sum_range (fun n =>
    cl D Sc ν [up i, dn i] [up i, dn i] (epsL i n ++ dcupL i n)),
    cl_invP₁ Sc i ν hh, cl_nil]

/-- The positive-weight part of the mixed relation, before coefficient conversion. -/
theorem mixed_nonneg (i : I) (ν : X) (a : ZMod 2) (hh : 0 ≤ D.h i ν) :
    K₀.mk ((inclusion Sc sy hc ν ν).obj (ef Sc sy hc i ν a)) =
      K₀.mk ((inclusion Sc sy hc ν ν).obj (fe Sc sy hc i ν (D.parity i + a))) +
      ∑ n : Fin (D.h i ν).toNat,
        K₀.mk ((inclusion Sc sy hc ν ν).obj (idShift Sc sy hc ν
          (sy.d i * (D.h i ν - 1 - 2 * n.val)) (n.val * D.parity i + a))) := by
  simpa only [Fin.sum_univ_succ, plusFamily, Fin.cases_zero, Fin.cases_succ] using
    mk_of_mapped_matrix (inclusion Sc sy hc ν ν) (ef Sc sy hc i ν a)
      (plusFamily Sc sy hc i ν a) (plusProj Sc sy hc i ν a) (plusIncl Sc sy hc i ν a)
      (plus_diag Sc sy hc i ν a hh) (plus_off Sc sy hc i ν a) (plus_total Sc sy hc i ν a hh)

/-- The negative-weight summands of inversion (1.14). -/
def minusFamily (i : I) (ν : X) (a : ZMod 2) :
    Fin ((-D.h i ν).toNat + 1) →
      ((show UUnderline D Sc sy hc from ⟨⟨⟨⟨⟨ν⟩⟩⟩⟩⟩) ⟶
        (show UUnderline D Sc sy hc from ⟨⟨⟨⟨⟨ν⟩⟩⟩⟩⟩)) :=
  Fin.cases (ef Sc sy hc i ν (D.parity i + a)) fun n =>
    idShift Sc sy hc ν (sy.d i * (D.h i ν + 1 + 2 * n.val)) (n.val * D.parity i + a)

def minusProj (i : I) (ν : X) (a : ZMod 2) :
    ∀ n, fe Sc sy hc i ν a ⟶ minusFamily Sc sy hc i ν a n :=
  Fin.cases
    (lift Sc sy hc (lcrossL i i) (sChain_lcrossL i i) (by simp)
      (by rw [parity_lcrossL]; exact (crossParity _ _).1))
    (fun n => lift Sc sy hc (dcapL i n.val) (sChain_dcapL i n.val)
      (by simp) (by rw [parity_dcapL, mul_comm]; exact (shiftParity _ _).1))

def minusIncl (i : I) (ν : X) (a : ZMod 2) :
    ∀ n, minusFamily Sc sy hc i ν a n ⟶ fe Sc sy hc i ν a :=
  Fin.cases
    (-lift Sc sy hc (sigmaL i i) (sChain_sigmaL i i) (by simp)
      (by rw [parity_sigmaL]; exact (crossParity _ _).2))
    (fun n => lift Sc sy hc (etaL i n.val) (sChain_etaL i n.val)
      (by simp; ring) (by rw [parity_etaL]; exact (shiftParity _ _).2))

theorem minus_diag (i : I) (ν : X) (a : ZMod 2) (hh : D.h i ν ≤ 0) (n) :
    minusIncl Sc sy hc i ν a n ≫ minusProj Sc sy hc i ν a n = 𝟙 _ := by
  refine Fin.cases ?_ (fun n => ?_) n
  · dsimp only [minusIncl, minusProj, Fin.cases_zero]
    rw [neg_comp]
    apply Subtype.ext; apply Subtype.ext
    change -(cl D Sc ν [up i, dn i] [dn i, up i] (sigmaL i i) ≫
      cl D Sc ν [dn i, up i] [up i, dn i] (lcrossL i i)) = 𝟙 _
    rw [cl_comp (sChain_sigmaL i i) (sChain_lcrossL i i),
      cl_invM₂ Sc i ν hh, neg_neg, cl_nil]
  · apply Subtype.ext; apply Subtype.ext
    change cl D Sc ν _ _ _ ≫ cl D Sc ν _ _ _ = 𝟙 _
    rw [cl_comp (sChain_etaL i n.val) (sChain_dcapL i n.val),
      cl_invM₅ Sc i ν n.val n.val (by omega) (by omega), ite_eq_left rfl, cl_nil]

theorem minus_off (i : I) (ν : X) (a : ZMod 2) (n m)
    (hnm : n ≠ m) :
    minusIncl Sc sy hc i ν a n ≫ minusProj Sc sy hc i ν a m = 0 := by
  revert hnm
  refine Fin.cases ?_ (fun n => ?_) n <;> refine Fin.cases ?_ (fun m => ?_) m
  · exact fun h => (h rfl).elim
  · intro _
    dsimp only [minusIncl, minusProj, Fin.cases_zero, Fin.cases_succ]
    rw [neg_comp]
    apply Subtype.ext; apply Subtype.ext
    change -(cl D Sc ν [up i, dn i] [dn i, up i] (sigmaL i i) ≫
      cl D Sc ν [dn i, up i] [] (dcapL i m.val)) = 0
    rw [ cl_comp (sChain_sigmaL i i) (sChain_dcapL i m.val),
      cl_invM₄ Sc i ν m.val (by omega), neg_zero]
  · intro _
    apply Subtype.ext; apply Subtype.ext
    change cl D Sc ν _ _ _ ≫ cl D Sc ν _ _ _ = 0
    rw [cl_comp (sChain_etaL i n.val) (sChain_lcrossL i i),
      cl_invM₃ Sc i ν n.val (by omega)]
  · intro h
    apply Subtype.ext; apply Subtype.ext
    change cl D Sc ν _ _ _ ≫ cl D Sc ν _ _ _ = 0
    rw [cl_comp (sChain_etaL i n.val) (sChain_dcapL i m.val),
      cl_invM₅ Sc i ν n.val m.val (by omega) (by omega), ite_eq_right]
    intro e; exact h (congrArg Fin.succ (Fin.ext e))

theorem minus_total (i : I) (ν : X) (a : ZMod 2) (hh : D.h i ν ≤ 0) :
    ∑ n, minusProj Sc sy hc i ν a n ≫ minusIncl Sc sy hc i ν a n = 𝟙 _ := by
  let forget : (fe Sc sy hc i ν a ⟶ fe Sc sy hc i ν a) →+
      ((pres D Sc).obj (ob D ν [dn i, up i]) ⟶ (pres D Sc).obj (ob D ν [dn i, up i])) :=
    { toFun := fun f => f.1.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Injective forget := fun _ _ h => Subtype.ext (Subtype.ext h)
  apply hf
  rw [Fin.sum_univ_succ]
  simp only [minusProj, minusIncl, Fin.cases_zero, Fin.cases_succ, comp_neg]
  rw [map_add, map_neg, map_sum]
  change -(cl D Sc ν [dn i, up i] [up i, dn i] (lcrossL i i) ≫
      cl D Sc ν [up i, dn i] [dn i, up i] (sigmaL i i)) +
    ∑ n : Fin (-D.h i ν).toNat,
      cl D Sc ν [dn i, up i] [] (dcapL i n.val) ≫
      cl D Sc ν [] [dn i, up i] (etaL i n.val) = 𝟙 _
  simp only [cl_comp (sChain_lcrossL i i) (sChain_sigmaL i i),
    cl_comp (sChain_dcapL i _) (sChain_etaL i _)]
  rw [Fin.sum_univ_eq_sum_range (fun n =>
    cl D Sc ν [dn i, up i] [dn i, up i] (dcapL i n ++ etaL i n)),
    cl_invM₁ Sc i ν hh, cl_nil]

/-- The negative-weight part of the mixed relation, before coefficient conversion. -/
theorem mixed_nonpos (i : I) (ν : X) (a : ZMod 2) (hh : D.h i ν ≤ 0) :
    K₀.mk ((inclusion Sc sy hc ν ν).obj (fe Sc sy hc i ν a)) =
      K₀.mk ((inclusion Sc sy hc ν ν).obj (ef Sc sy hc i ν (D.parity i + a))) +
      ∑ n : Fin (-D.h i ν).toNat,
        K₀.mk ((inclusion Sc sy hc ν ν).obj (idShift Sc sy hc ν
          (sy.d i * (D.h i ν + 1 + 2 * n.val)) (n.val * D.parity i + a))) := by
  simpa only [Fin.sum_univ_succ, minusFamily, Fin.cases_zero, Fin.cases_succ] using
    mk_of_mapped_matrix (inclusion Sc sy hc ν ν) (fe Sc sy hc i ν a)
      (minusFamily Sc sy hc i ν a) (minusProj Sc sy hc i ν a) (minusIncl Sc sy hc i ν a)
      (minus_diag Sc sy hc i ν a hh) (minus_off Sc sy hc i ν a) (minus_total Sc sy hc i ν a hh)

end OddMath.SKM.K0Relations
