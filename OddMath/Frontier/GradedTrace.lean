import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # A rank criterion for decompositions of graded idempotents

Let `V` be an abelian group spanned by subgroups `V_d` (`d` in an abelian group `ι`, typically
`ℤ`), each free of finite rank.  An operator has degree `k` if it maps `V_d` into `V_{d+k}`.

Let `P`, `e` be idempotents of degree `0`, and let `σ_i` (degree `s_i`), `ρ_i` (degree `-s_i`),
`i ∈ I` finite, satisfy `ρ_j σ_i = δ_{ij} e`, `P σ_i = σ_i`, `ρ_i P = ρ_i`, and
`σ_i e ρ_i = σ_i ρ_i`.  If in every degree
`rank P(V_d) = ∑_i rank e(V_{d - s_i})`, then `P = ∑_i σ_i ρ_i`.

Proof: `Q = P - ∑ σ_i ρ_i` is an idempotent of degree `0`; on each `V_d` the trace of an
idempotent is the rank of its image, and cyclicity of the trace gives
`tr(σ_i ρ_i | V_d) = tr(e | V_{d - s_i})`, so `Q` has trace `0`, hence vanishes, on every `V_d`.

This is the counting step behind EKL arXiv:1111.1320v1, Thms 4.15–4.16, which the paper derives
from `ONH_a ≅ Mat(OΛ_a)` (Cor 2.14).
-/
namespace OddMath.Frontier.GradedTrace
open Module LinearMap

section Idempotent
variable {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

/-- The trace of an idempotent on a free ℤ-module of finite rank is the rank of its image. -/
theorem trace_eq_finrank_range {f : M →ₗ[ℤ] M} (hf : f ∘ₗ f = f) :
    trace ℤ M f = finrank ℤ (range f) :=
  IsProj.trace ⟨fun x => mem_range_self f x, fun x ⟨y, hy⟩ => by
    rw [← hy, ← comp_apply, hf]⟩

/-- An idempotent of trace `0` on a free ℤ-module of finite rank vanishes. -/
theorem eq_zero_of_trace_eq_zero {f : M →ₗ[ℤ] M} (hf : f ∘ₗ f = f) (h : trace ℤ M f = 0) :
    f = 0 := by
  rw [trace_eq_finrank_range hf, Nat.cast_eq_zero, finrank_zero_iff] at h
  ext x
  exact congrArg Subtype.val (Subsingleton.elim (⟨f x, mem_range_self f x⟩ : range f) 0)

end Idempotent

variable {ι V : Type*} [AddCommGroup ι] [AddCommGroup V]

/-- `T` has degree `k`: it maps `V_d` into `V_{d+k}`. -/
def HasDegree (Vd : ι → Submodule ℤ V) (k : ι) (T : V →ₗ[ℤ] V) : Prop :=
  ∀ d, ∀ v ∈ Vd d, T v ∈ Vd (d + k)

theorem HasDegree.mem {Vd : ι → Submodule ℤ V} {k : ι} {T : V →ₗ[ℤ] V} (h : HasDegree Vd k T)
    {d d' : ι} (hd : d + k = d') {v : V} (hv : v ∈ Vd d) : T v ∈ Vd d' :=
  hd ▸ h d v hv

/-- The restriction `V_d → V_{d'}` of an operator of degree `k`, where `d + k = d'`. -/
abbrev HasDegree.res {Vd : ι → Submodule ℤ V} {k : ι} {T : V →ₗ[ℤ] V} (h : HasDegree Vd k T)
    (d d' : ι) (hd : d + k = d') : Vd d →ₗ[ℤ] Vd d' :=
  T.restrict fun _ hv => h.mem hd hv

/-- For an idempotent of degree `0`, the trace on `V_d` is the rank of `T(V_d)`. -/
theorem HasDegree.trace_res {Vd : ι → Submodule ℤ V} {d : ι} [Module.Free ℤ (Vd d)]
    [Module.Finite ℤ (Vd d)] {T : V →ₗ[ℤ] V} (h : HasDegree Vd 0 T) (hT : T ∘ₗ T = T) :
    trace ℤ (Vd d) (h.res d d (add_zero d)) = finrank ℤ ((Vd d).map T) := by
  have hmap : (range (h.res d d (add_zero d))).map (Vd d).subtype = (Vd d).map T := by
    ext x
    simp only [Submodule.mem_map, mem_range, Submodule.subtype_apply]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
  rw [trace_eq_finrank_range (f := h.res d d (add_zero d))
    (LinearMap.ext fun w => Subtype.ext (LinearMap.congr_fun hT w.1)), ← hmap,
    Submodule.finrank_map_subtype_eq]

variable {Vd : ι → Submodule ℤ V} [∀ d, Module.Free ℤ (Vd d)] [∀ d, Module.Finite ℤ (Vd d)]
  {I : Type*} [Fintype I] {s : I → ι} {P e : V →ₗ[ℤ] V} {σ ρ : I → V →ₗ[ℤ] V}

/-- Trace form: if `tr(P | V_d) = ∑_i tr(e | V_{d - s_i})` for all `d`, then `P = ∑ σ_i ρ_i`. -/
theorem eq_sum_of_trace (hspan : ⨆ d, Vd d = ⊤)
    (hP : HasDegree Vd 0 P) (he : HasDegree Vd 0 e)
    (hσ : ∀ i, HasDegree Vd (s i) (σ i)) (hρ : ∀ i, HasDegree Vd (-s i) (ρ i))
    (hPP : P ∘ₗ P = P) (hdiag : ∀ i, ρ i ∘ₗ σ i = e) (horth : ∀ i j, i ≠ j → ρ j ∘ₗ σ i = 0)
    (hPσ : ∀ i, P ∘ₗ σ i = σ i) (hρP : ∀ i, ρ i ∘ₗ P = ρ i)
    (hσe : ∀ i, σ i ∘ₗ e ∘ₗ ρ i = σ i ∘ₗ ρ i)
    (htr : ∀ d, trace ℤ (Vd d) (hP.res d d (add_zero d)) =
      ∑ i, trace ℤ (Vd (d - s i)) (he.res _ _ (add_zero (d - s i)))) :
    P = ∑ i, σ i ∘ₗ ρ i := by
  set Q := P - ∑ i, σ i ∘ₗ ρ i
  -- `Q` is idempotent
  have hQQ : Q ∘ₗ Q = Q := by
    simp only [Q, ← Module.End.mul_eq_comp] at *
    have hPE : P * ∑ i, σ i * ρ i = ∑ i, σ i * ρ i := by
      simp [Finset.mul_sum, ← mul_assoc, hPσ]
    have hEP : (∑ i, σ i * ρ i) * P = ∑ i, σ i * ρ i := by
      simp [Finset.sum_mul, mul_assoc, hρP]
    have hEE : (∑ i, σ i * ρ i) * ∑ i, σ i * ρ i = ∑ i, σ i * ρ i := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.sum_eq_single i (fun j _ hj => by
        rw [mul_assoc, ← mul_assoc (ρ i), horth j i hj, zero_mul, mul_zero])
        (by simp), mul_assoc, ← mul_assoc (ρ i), hdiag, hσe]
    simp only [Q, sub_mul, mul_sub, hPP, hPE, hEP, hEE, sub_self, sub_zero]
  have hQ : HasDegree Vd 0 Q := fun d v hv => by
    simp only [Q, sub_apply, coeFn_sum, Finset.sum_apply, comp_apply]
    refine sub_mem (hP d v hv) (Submodule.sum_mem _ fun i _ => ?_)
    exact (hσ i).mem (by abel) ((hρ i).mem (d := d) (d' := d - s i) (by abel) hv)
  suffices h : ∀ d, ∀ v ∈ Vd d, Q v = 0 by
    have : ⊤ ≤ ker Q := hspan ▸ iSup_le fun d v hv => h d v hv
    exact sub_eq_zero.1 (LinearMap.ext fun v => this Submodule.mem_top)
  intro d v hv
  have hQd : hQ.res d d (add_zero d) = 0 := by
    refine eq_zero_of_trace_eq_zero
      (LinearMap.ext fun w => Subtype.ext (LinearMap.congr_fun hQQ w.1)) ?_
    have hsplit : hQ.res d d (add_zero d) = hP.res d d (add_zero d) -
        ∑ i, (hσ i).res (d - s i) d (sub_add_cancel d (s i)) ∘ₗ
          (hρ i).res d (d - s i) (sub_eq_add_neg d (s i)).symm := by
      ext w
      simp only [Q, restrict_coe_apply, sub_apply, coeFn_sum, Finset.sum_apply, comp_apply,
        Submodule.coe_sub, Submodule.coe_sum]
    rw [hsplit, map_sub, map_sum, htr, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [trace_comp_comm']
    congr 1
    exact LinearMap.ext fun w => Subtype.ext (LinearMap.congr_fun (hdiag i) w.1).symm
  simpa using congrArg Subtype.val (LinearMap.congr_fun hQd ⟨v, hv⟩)

/-- Rank form: if `rank P(V_d) = ∑_i rank e(V_{d - s_i})` for all `d`, then `P = ∑ σ_i ρ_i`. -/
theorem eq_sum_of_finrank (hspan : ⨆ d, Vd d = ⊤)
    (hP : HasDegree Vd 0 P) (he : HasDegree Vd 0 e)
    (hσ : ∀ i, HasDegree Vd (s i) (σ i)) (hρ : ∀ i, HasDegree Vd (-s i) (ρ i))
    (hPP : P ∘ₗ P = P) (hee : e ∘ₗ e = e)
    (hdiag : ∀ i, ρ i ∘ₗ σ i = e) (horth : ∀ i j, i ≠ j → ρ j ∘ₗ σ i = 0)
    (hPσ : ∀ i, P ∘ₗ σ i = σ i) (hρP : ∀ i, ρ i ∘ₗ P = ρ i)
    (hσe : ∀ i, σ i ∘ₗ e ∘ₗ ρ i = σ i ∘ₗ ρ i)
    (hrank : ∀ d, finrank ℤ ((Vd d).map P) = ∑ i, finrank ℤ ((Vd (d - s i)).map e)) :
    P = ∑ i, σ i ∘ₗ ρ i :=
  eq_sum_of_trace hspan hP he hσ hρ hPP hdiag horth hPσ hρP hσe fun d => by
    simp only [hP.trace_res hPP, he.trace_res hee, hrank, Nat.cast_sum]

end OddMath.Frontier.GradedTrace
