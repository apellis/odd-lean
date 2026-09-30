import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.Abel

/-!
# p-complexes and slash cohomology

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.4.1.

A *p-complex* is a module `V` over `H = 𝕜[d]/(d^p)`, i.e. a `𝕜`-module with an endomorphism `d`
satisfying `d^p = 0` (the paper also asks for a grading with `deg d = 2`; the grading plays no
role in the statements below and is not recorded). For `0 ≤ k ≤ p - 2` the *slash cohomology*
is (Khovanov–Qi, *An approach to categorification of some small quantum groups*, §2)

  `H_{/k}(V) = Ker(d^{k+1}) / (Im(d^{p-k-1}) + Ker(d^k))`   (`SlashCohomology`).

**Misprint.** Ellis–Qi print `H_{/k}(V) = Ker(d^k)/(Im(d^{p-k-1}) + Ker(d^{k+1}))`. Since
`Ker(d^k) ⊆ Ker(d^{k+1})`, that quotient is always zero (`printedSlash_subsingleton`); the
formula (A.4) for `H_{/k}(V_i)` and the remark `H = H_{/0}` for `p = 2` hold for the definition
above, which is the one of the cited source.

Main results:

* `slash_shiftV_pos`, `slash_shiftV_zero`: formula (A.4) for the indecomposables
  `V_i = H/(d^{i+1})` (`shiftV i`, basis `v_0, …, v_i`, `d v_j = v_{j+1}`):
  `H_{/k}(V_i) = 𝕜 · v_{i-k}` if `k ≤ i < p - 1`, and `H_{/k}(V_i) = 0` if `i < k` or
  `i = p - 1`;
* `mem_range_of_homotopy`: if `v = Σ_{a+b=p-1} d^a h d^b v` and `d^j v = 0`, then
  `v ∈ Im(d^{p-j})`;
* `slash_of_isCompl`: a criterion computing all slash cohomology groups of a p-complex which
  splits as `T ⊕ F` with `d = 0` on `T` and `F` exact;
* `slashMap`, `IsQuasiIso`: the maps induced on slash cohomology by a morphism of p-complexes,
  and quasi-isomorphisms (isomorphisms on all `H_{/j}`, `0 ≤ j ≤ p - 2`).
-/

namespace OddMath.Frontier.EQPdg

open LinearMap Submodule

section Slash

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]

/-- The submodule `Im(d^{p-k-1}) + Ker(d^k)` of `V`. -/
def slashDen (d : Module.End k V) (p j : ℕ) : Submodule k V :=
  range (d ^ (p - j - 1)) ⊔ ker (d ^ j)

/-- Slash cohomology `H_{/j}(V) = Ker(d^{j+1}) / (Im(d^{p-j-1}) + Ker(d^j))`
(Khovanov–Qi; Ellis–Qi, Appendix A.4.1, with the indices of the printed formula corrected). -/
abbrev SlashCohomology (d : Module.End k V) (p j : ℕ) : Type _ :=
  ker (d ^ (j + 1)) ⧸ (slashDen d p j).comap (ker (d ^ (j + 1))).subtype

/-- The quotient printed in Ellis–Qi, Appendix A.4.1: `Ker(d^k)/(Im(d^{p-k-1}) + Ker(d^{k+1}))`. -/
abbrev PrintedSlash (d : Module.End k V) (p j : ℕ) : Type _ :=
  ker (d ^ j) ⧸ (range (d ^ (p - j - 1)) ⊔ ker (d ^ (j + 1))).comap (ker (d ^ j)).subtype

theorem ker_pow_le_ker_pow_succ (d : Module.End k V) (j : ℕ) : ker (d ^ j) ≤ ker (d ^ (j + 1)) := by
  intro v hv
  simp only [mem_ker] at hv ⊢
  rw [pow_succ', Module.End.mul_apply, hv, map_zero]

/-- The printed quotient is always zero. -/
theorem printedSlash_subsingleton (d : Module.End k V) (p j : ℕ) :
    Subsingleton (PrintedSlash d p j) := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  rintro ⟨v, hv⟩ -
  simp only [mem_comap, Submodule.coe_subtype]
  exact Submodule.mem_sup_right (ker_pow_le_ker_pow_succ d j hv)

theorem slashCohomology_subsingleton_iff (d : Module.End k V) (p j : ℕ) :
    Subsingleton (SlashCohomology d p j) ↔ ker (d ^ (j + 1)) ≤ slashDen d p j := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  constructor
  · intro h v hv
    simpa using h (Submodule.mem_top (x := (⟨v, hv⟩ : ker (d ^ (j + 1)))))
  · rintro h ⟨v, hv⟩ -
    simpa using h hv

/-- The class of an element of `Ker(d^{j+1})` in `H_{/j}`. -/
def slashClass (d : Module.End k V) (p j : ℕ) (v : V) (hv : (d ^ (j + 1)) v = 0) :
    SlashCohomology d p j :=
  Submodule.Quotient.mk ⟨v, hv⟩

theorem pow_apply_eq_zero_of_le (d : Module.End k V) {a b : ℕ} (hab : a ≤ b) {v : V}
    (hv : (d ^ a) v = 0) : (d ^ b) v = 0 := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [add_comm, pow_add, Module.End.mul_apply, hv, map_zero]

theorem slashDen_zero (d : Module.End k V) (p : ℕ) : slashDen d p 0 = range (d ^ (p - 1)) := by
  simp only [slashDen, Nat.sub_zero, pow_zero]
  rw [Module.End.one_eq_id, LinearMap.ker_id, sup_bot_eq]

/-- If `v = Σ_{a+b=p-1} d^a h d^b v` and `d^j v = 0` then `v ∈ Im(d^{p-j})`. -/
theorem mem_range_of_homotopy (d h : Module.End k V) (p j : ℕ) (hjp : j ≤ p) (v : V)
    (hv : v = ∑ a ∈ Finset.range p, (d ^ a) (h ((d ^ (p - 1 - a)) v)))
    (hdv : (d ^ j) v = 0) : v ∈ range (d ^ (p - j)) := by
  rw [hv]
  refine Submodule.sum_mem _ fun a ha => ?_
  have ha : a < p := Finset.mem_range.mp ha
  by_cases hja : j ≤ p - 1 - a
  · rw [pow_apply_eq_zero_of_le d hja hdv, map_zero, map_zero]
    exact Submodule.zero_mem _
  · have : p - j ≤ a := by omega
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le this
    refine ⟨(d ^ c) (h ((d ^ (p - 1 - (p - j + c))) v)), ?_⟩
    rw [pow_add, Module.End.mul_apply]

theorem pow_mem_of_map_le (d : Module.End k V) (F : Submodule k V) (hF : F.map d ≤ F) (j : ℕ)
    {v : V} (hv : v ∈ F) : (d ^ j) v ∈ F := by
  induction j with
  | zero => simpa using hv
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hF ⟨_, ih, rfl⟩

/-- **Splitting criterion.** Let `V = T ⊕ F` with `d = 0` on `T`, `d F ⊆ F`, and `F` exact in the
sense that `Ker(d^j) ∩ F ⊆ Im(d^{p-j})` for `1 ≤ j ≤ p - 1`. Then `H_{/j}(V) = 0` for
`1 ≤ j ≤ p - 2`, and `T → H_{/0}(V)` is bijective. -/
theorem slash_of_isCompl (d : Module.End k V) (p : ℕ) (hp : 2 ≤ p) (T F : Submodule k V)
    (hTF : IsCompl T F) (hT : T ≤ ker d) (hF : F.map d ≤ F)
    (hex : ∀ j, 1 ≤ j → j ≤ p - 1 → ∀ v ∈ F, (d ^ j) v = 0 → v ∈ range (d ^ (p - j))) :
    (∀ j, 1 ≤ j → j ≤ p - 2 → Subsingleton (SlashCohomology d p j)) ∧
    Function.Bijective (fun t : T => slashClass d p 0 t.1 (by
      simpa using (hT t.2 : d t.1 = 0))) := by
  have hdecomp : ∀ v : V, ∃ t ∈ T, ∃ f ∈ F, v = t + f := fun v => by
    have hv : v ∈ T ⊔ F := by rw [hTF.sup_eq_top]; trivial
    obtain ⟨t, ht, f, hf, h⟩ := Submodule.mem_sup.mp hv
    exact ⟨t, ht, f, hf, h.symm⟩
  have hTd : ∀ t ∈ T, ∀ j, 1 ≤ j → (d ^ j) t = 0 := fun t ht j hj =>
    pow_apply_eq_zero_of_le d (a := 1) hj (by simpa using hT ht)
  refine ⟨fun j hj1 hj2 => ?_, ?_, ?_⟩
  · rw [slashCohomology_subsingleton_iff]
    intro v hv
    obtain ⟨t, ht, f, hf, rfl⟩ := hdecomp v
    have hfv : (d ^ (j + 1)) f = 0 := by
      have := hv
      simp only [mem_ker, map_add, hTd t ht (j + 1) (by omega), zero_add] at this
      exact this
    have hfr := hex (j + 1) (by omega) (by omega) f hf hfv
    rw [add_comm]
    refine Submodule.add_mem_sup ?_ ?_
    · convert hfr using 3
    · exact hTd t ht j hj1
  · rintro ⟨t, ht⟩ ⟨t', ht'⟩ h
    simp only [slashClass] at h
    rw [Submodule.Quotient.eq, Submodule.mem_comap, slashDen_zero] at h
    obtain ⟨w, hw⟩ := h
    simp only [Submodule.coe_subtype, AddSubgroupClass.coe_sub] at hw
    obtain ⟨s, hs, f, hf, rfl⟩ := hdecomp w
    rw [map_add, hTd s hs (p - 1) (by omega), zero_add] at hw
    have h1 : t - t' ∈ F := hw ▸ pow_mem_of_map_le d F hF _ hf
    have h2 : t - t' ∈ T := T.sub_mem ht ht'
    have : t - t' = 0 := by
      have := hTF.inf_eq_bot ▸ (Submodule.mem_inf.mpr ⟨h2, h1⟩)
      simpa using this
    exact Subtype.ext (sub_eq_zero.mp this)
  · intro c
    induction c using Submodule.Quotient.induction_on with
    | H v =>
    obtain ⟨v, hv⟩ := v
    obtain ⟨t, ht, f, hf, rfl⟩ := hdecomp v
    have hfv : (d ^ 1) f = 0 := by
      have := hv
      simp only [mem_ker, map_add, hTd t ht (0 + 1) (by omega), zero_add] at this
      exact this
    obtain ⟨w, hw⟩ := hex 1 le_rfl (by omega) f hf hfv
    refine ⟨⟨t, ht⟩, ?_⟩
    simp only [slashClass]
    rw [Submodule.Quotient.eq, Submodule.mem_comap, slashDen_zero]
    refine ⟨-w, ?_⟩
    simp only [Submodule.coe_subtype, AddSubgroupClass.coe_sub, map_neg, hw]
    abel

section Map

variable {W : Type*} [AddCommGroup W] [Module k W]

theorem comp_pow_of_comm (d : Module.End k V) (d' : Module.End k W) (f : V →ₗ[k] W)
    (hf : f ∘ₗ d = d' ∘ₗ f) (m : ℕ) (v : V) : f ((d ^ m) v) = (d' ^ m) (f v) := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    exact congrArg (d' ^ m) (LinearMap.congr_fun hf v)

/-- The map induced on slash cohomology by a morphism of p-complexes `f` (`f d = d' f`). -/
def slashMap (d : Module.End k V) (d' : Module.End k W) (f : V →ₗ[k] W) (hf : f ∘ₗ d = d' ∘ₗ f)
    (p j : ℕ) : SlashCohomology d p j →ₗ[k] SlashCohomology d' p j :=
  Submodule.mapQ _ _ (f.restrict (p := ker (d ^ (j + 1))) (q := ker (d' ^ (j + 1)))
    fun v hv => by
      rw [mem_ker] at hv ⊢
      rw [← comp_pow_of_comm d d' f hf, hv, map_zero])
    (by
      rintro ⟨v, hv⟩ hden
      simp only [mem_comap, Submodule.coe_subtype, slashDen] at hden ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hden
      simp only [LinearMap.restrict_apply, map_add]
      refine Submodule.add_mem_sup ?_ ?_
      · obtain ⟨w, rfl⟩ := hx
        exact ⟨f w, (comp_pow_of_comm d d' f hf _ w).symm⟩
      · rw [mem_ker] at hy ⊢
        rw [← comp_pow_of_comm d d' f hf, hy, map_zero])

theorem slashMap_mk (d : Module.End k V) (d' : Module.End k W) (f : V →ₗ[k] W)
    (hf : f ∘ₗ d = d' ∘ₗ f) (p j : ℕ) (v : ker (d ^ (j + 1))) :
    slashMap d d' f hf p j (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ⟨f v, by
        rw [mem_ker, ← comp_pow_of_comm d d' f hf, (mem_ker.mp v.2), map_zero]⟩ := rfl

/-- A morphism of p-complexes is a *quasi-isomorphism* if it induces isomorphisms on all slash
cohomology groups `H_{/j}`, `0 ≤ j ≤ p - 2`. -/
def IsQuasiIso (d : Module.End k V) (d' : Module.End k W) (f : V →ₗ[k] W)
    (hf : f ∘ₗ d = d' ∘ₗ f) (p : ℕ) : Prop :=
  ∀ j, j ≤ p - 2 → Function.Bijective (slashMap d d' f hf p j)

end Map

end Slash

/-! ## The indecomposable p-complexes `V_i = H/(d^{i+1})` -/

section Indec

variable {k : Type*} [Field k]

/-- `V_i = H/(d^{i+1})` with basis `v_0, …, v_i` (the coordinate vectors of `Fin (i+1) → 𝕜`)
and `d v_j = v_{j+1}`, `d v_i = 0`. -/
def shiftV (i : ℕ) : Module.End k (Fin (i + 1) → k) where
  toFun v j := if h : 1 ≤ (j : ℕ) then v ⟨j - 1, by omega⟩ else 0
  map_add' v w := by
    ext j
    by_cases h : 1 ≤ (j : ℕ) <;> simp [h]
  map_smul' c v := by
    ext j
    by_cases h : 1 ≤ (j : ℕ) <;> simp [h]

theorem shiftV_pow_apply (i m : ℕ) (v : Fin (i + 1) → k) (j : Fin (i + 1)) :
    ((shiftV i) ^ m) v j = if h : m ≤ (j : ℕ) then v ⟨j - m, by omega⟩ else 0 := by
  induction m generalizing j with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    change (if h : 1 ≤ (j : ℕ) then ((shiftV i) ^ m) v ⟨j - 1, by omega⟩ else 0) = _
    by_cases hj : 1 ≤ (j : ℕ)
    · simp only [hj, ↓reduceDIte, ih]
      by_cases hm : m + 1 ≤ (j : ℕ)
      · have hm' : m ≤ (j : ℕ) - 1 := by omega
        simp only [hm, hm', ↓reduceDIte]
        congr 1; ext; simp; omega
      · have hm' : ¬ m ≤ (j : ℕ) - 1 := by omega
        simp only [hm, hm', ↓reduceDIte]
    · have hm : ¬ m + 1 ≤ (j : ℕ) := by omega
      simp only [hj, hm, ↓reduceDIte]

/-- The basis vector `v_j` of `V_i` (zero if `j > i`). -/
def vElem (i j : ℕ) : Fin (i + 1) → k := fun l => if (l : ℕ) = j then 1 else 0

theorem shiftV_pow_eq_zero (i : ℕ) : (shiftV (k := k) i) ^ (i + 1) = 0 := by
  refine LinearMap.ext fun v => funext fun j => ?_
  rw [shiftV_pow_apply]
  have : ¬ i + 1 ≤ (j : ℕ) := by omega
  simp only [this, ↓reduceDIte]
  rfl

/-- `V_i` is a p-complex for `i ≤ p - 1`. -/
theorem shiftV_isPComplex {p i : ℕ} (hi : i + 1 ≤ p) : (shiftV (k := k) i) ^ p = 0 := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [pow_add, shiftV_pow_eq_zero, zero_mul]

theorem mem_ker_shiftV_pow (i m : ℕ) (v : Fin (i + 1) → k) :
    v ∈ ker ((shiftV i) ^ m) ↔ ∀ j : Fin (i + 1), (j : ℕ) + m ≤ i → v j = 0 := by
  simp only [mem_ker]
  constructor
  · intro h j hj
    have := congrFun h ⟨j + m, by omega⟩
    rw [shiftV_pow_apply] at this
    have hm : m ≤ (j : ℕ) + m := by omega
    simp only [hm, ↓reduceDIte] at this
    convert this using 2
    ext; simp
  · intro h
    funext l
    rw [shiftV_pow_apply]
    by_cases hl : m ≤ (l : ℕ)
    · simp only [hl, ↓reduceDIte]
      exact h _ (by simp; omega)
    · simp only [hl, ↓reduceDIte]
      rfl

theorem mem_range_shiftV_pow (i m : ℕ) (w : Fin (i + 1) → k) :
    w ∈ range ((shiftV i) ^ m) ↔ ∀ j : Fin (i + 1), (j : ℕ) < m → w j = 0 := by
  constructor
  · rintro ⟨v, rfl⟩ j hj
    rw [shiftV_pow_apply]
    have : ¬ m ≤ (j : ℕ) := by omega
    simp only [this, ↓reduceDIte]
  · intro h
    refine ⟨fun l => if hl : (l : ℕ) + m ≤ i then w ⟨l + m, by omega⟩ else 0, ?_⟩
    funext j
    rw [shiftV_pow_apply]
    by_cases hj : m ≤ (j : ℕ)
    · have hj' : (j : ℕ) - m + m ≤ i := by omega
      simp only [hj, hj', ↓reduceDIte]
      congr 1; ext; simp; omega
    · simp only [hj, ↓reduceDIte]
      exact (h j (by omega)).symm

theorem vElem_mem_ker (i j : ℕ) (hji : j ≤ i) :
    ((shiftV (k := k) i) ^ (j + 1)) (vElem i (i - j)) = 0 := by
  have := (mem_ker_shiftV_pow (k := k) i (j + 1) (vElem i (i - j))).mpr (by
    intro l hl
    have : (l : ℕ) ≠ i - j := by omega
    simp [vElem, this])
  exact this

/-- **Formula (A.4), nonzero case.** For `k ≤ i < p - 1`, `H_{/k}(V_i)` is one-dimensional,
spanned by the class of `v_{i-k}`: the coordinate `v ↦ v_{i-k}` induces an isomorphism
`H_{/k}(V_i) ≃ 𝕜` (which sends `[v_{i-k}]` to `1`, see `vElem_mem_ker`). -/
theorem slash_shiftV_pos (p i j : ℕ) (hji : j ≤ i) (hip : i < p - 1) :
    ∃ e : SlashCohomology (shiftV (k := k) i) p j ≃ₗ[k] k,
      ∀ v : ker ((shiftV (k := k) i) ^ (j + 1)),
        e (Submodule.Quotient.mk v) = (v : Fin (i + 1) → k) ⟨i - j, by omega⟩ := by
  set d := shiftV (k := k) i
  let c : Fin (i + 1) := ⟨i - j, by omega⟩
  let φ : ker (d ^ (j + 1)) →ₗ[k] k := (LinearMap.proj c).comp (ker (d ^ (j + 1))).subtype
  have hker : (slashDen d p j).comap (ker (d ^ (j + 1))).subtype = ker φ := by
    ext ⟨v, hv⟩
    rw [mem_ker_shiftV_pow] at hv
    simp only [mem_comap, Submodule.coe_subtype, slashDen, mem_ker, φ, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.coe_proj, Function.eval]
    constructor
    · intro h
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp h
      rw [mem_range_shiftV_pow] at ha
      have hb' := (mem_ker_shiftV_pow i j b).mp hb
      simp only [Pi.add_apply]
      rw [ha c (by simp [c]; omega), hb' c (by simp [c]; omega), add_zero]
    · intro h
      refine Submodule.mem_sup_right ?_
      rw [mem_ker_shiftV_pow]
      intro l hl
      by_cases hlc : (l : ℕ) = i - j
      · have : l = c := Fin.ext hlc
        rw [this]; exact h
      · exact hv l (by omega)
  have hsurj : Function.Surjective φ := by
    intro a
    refine ⟨⟨a • vElem i (i - j), ?_⟩, ?_⟩
    · rw [mem_ker_shiftV_pow]
      intro l hl
      have : (l : ℕ) ≠ i - j := by omega
      simp [vElem, this]
    · simp [φ, vElem, c]
  refine ⟨(Submodule.quotEquivOfEq _ _ hker).trans (φ.quotKerEquivOfSurjective hsurj), ?_⟩
  intro v
  rw [LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

/-- **Formula (A.4), zero case.** `H_{/k}(V_i) = 0` if `i < k` or `i = p - 1`. -/
theorem slash_shiftV_zero (p i j : ℕ) (h : i < j ∨ i = p - 1) :
    Subsingleton (SlashCohomology (shiftV (k := k) i) p j) := by
  rw [slashCohomology_subsingleton_iff]
  intro v hv
  rw [mem_ker_shiftV_pow] at hv
  rcases h with h | h
  · refine Submodule.mem_sup_right ?_
    rw [mem_ker_shiftV_pow]
    intro l hl; omega
  · refine Submodule.mem_sup_left ?_
    rw [mem_range_shiftV_pow]
    intro l hl
    exact hv l (by omega)

end Indec

end OddMath.Frontier.EQPdg
