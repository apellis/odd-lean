import OddMath.Frontier.EQZabCell

/-!
# The cell filtration of `Z_{a,b}` (Ellis–Qi, Corollary 4.8)

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2, Corollary 4.8 and its proof (printed numbering); Example 2.7 (finite-cell modules).

Model of `EQZabModule`: `Z_{a,b} = OΛ_a ⊠ OΛ_b`, differential `dZ a b`, right action
`G · h = G φ(h)`; the basis element `s̃_μ(y) z` of Ellis–Qi is `s_μ(y) = inclY (untwisted b μ)`.
`|μ| = Σ_j μ_j` (`weight`).

For a set `S ⊆ Par(b,a)` let `Z_S = span{s_μ(y) z · c : μ ∈ S, c ∈ OΛ_{a+b}}` (`upSpan`). `S` is
*up-closed* (`UpClosed`) if it contains every `ν ∈ Par(b,a)` with `|ν| > |μ|` for some `μ ∈ S`.

* `upSpan_dZ`, `upSpan_mul_phiAB`: for up-closed `S`, `Z_S` is a dg submodule (stable under `d`,
  by Lemma 4.7, and under the right action of `OΛ_{a+b}`);
* `upSpan_cell`: if `S` and `S ∪ {μ}` are up-closed, then modulo `Z_S`,
  `d(s̃_μ(y) z · c) ≡ (-1)^{|μ|} s̃_μ(y) z · d(c)`;
* `upSpan_free`: `s̃_μ(y) z · c ∈ Z_S` with `μ ∉ S` forces `c = 0`;
  hence `Z_{S ∪ {μ}} / Z_S ≅ OΛ_{a+b}` (shifted), with differential `(-1)^{|μ|} d`;
* `upSpan_empty`, `upSpan_box`: `Z_∅ = 0` and `Z_{Par(b,a)} = Z_{a,b}`;
* `exists_cell_chain`: an enumeration `μ_1, …, μ_N` of `Par(b,a)` (by decreasing `|μ|`), all of
  whose initial segments are up-closed.

**Corollary 4.8** (`cor_4_8`): `0 = Z_{S_0} ⊆ Z_{S_1} ⊆ ⋯ ⊆ Z_{S_N} = Z_{a,b}` with
`S_j = {μ_1, …, μ_j}` is a finite filtration by dg submodules whose subquotients are free right
dg modules of rank one over `OΛ_{a+b}`: `Z_{a,b}` is a finite-cell (hence cofibrant) right dg
module over `OΛ_{a+b}`, with `N = #Par(b,a) = binom(a+b, a)` cells.
-/

namespace OddMath.Frontier.EQZab

open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open EQSkewDifferential EQSchur
open BoxComplement BoxPartitionCount
open scoped BigOperators

noncomputable section

local instance (priority := high) zabFiltNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) zabFiltNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {a b : ℕ}

/-- `|μ| = Σ_j μ_j`. -/
def weight (μ : Fin b → ℕ) : ℕ := ∑ j, μ j

/-- `Z_S = span{s̃_μ(y) z · c : μ ∈ S, c ∈ OΛ_{a+b}}`. -/
def upSpan (a b : ℕ) (S : Finset (Fin b → ℕ)) : Submodule ℤ (SkewPolynomial (a+b)) :=
  Submodule.span ℤ {F | ∃ μ ∈ S, ∃ c ∈ osym (a+b), F = inclY a b (untwisted b μ) * phiAB a b c}

/-- `S ⊆ Par(b,a)` contains every `ν ∈ Par(b,a)` heavier than one of its elements. -/
def UpClosed (a : ℕ) (S : Finset (Fin b → ℕ)) : Prop :=
  S ⊆ box b a ∧ ∀ μ ∈ S, ∀ ν ∈ box b a, weight μ < weight ν → ν ∈ S

theorem mem_upSpan {S : Finset (Fin b → ℕ)} {μ : Fin b → ℕ} (hμ : μ ∈ S) {c : SkewPolynomial (a+b)}
    (hc : c ∈ osym (a+b)) : inclY a b (untwisted b μ) * phiAB a b c ∈ upSpan a b S :=
  Submodule.subset_span ⟨μ, hμ, c, hc, rfl⟩

theorem upSpan_mono {S T : Finset (Fin b → ℕ)} (h : S ⊆ T) : upSpan a b S ≤ upSpan a b T :=
  Submodule.span_mono fun _ ⟨μ, hμ, c, hc, e⟩ => ⟨μ, h hμ, c, hc, e⟩

theorem weight_add_expSingle (μ : Fin b → ℕ) (i : Fin b) :
    weight (μ + expSingle i) = weight μ + 1 := by
  simp [weight, Finset.sum_add_distrib, expSingle]

open Classical in
/-- **`Z_S` is `d`-stable** for up-closed `S` (by Lemma 4.7 and the right Leibniz rule). -/
theorem upSpan_dZ {S : Finset (Fin b → ℕ)} (hS : UpClosed a S) {F : SkewPolynomial (a+b)}
    (hF : F ∈ upSpan a b S) : dZ a b F ∈ upSpan a b S := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, hμ, c, hc, rfl⟩ := hx
    have hμb := mem_box.1 (hS.1 hμ)
    rw [dZ_mul_phiAB, lemma_4_7_box μ hμb.1 hμb.2, Finset.sum_mul, parityInv_inclY,
      parityInv_untwisted, map_zsmul, smul_mul_assoc]
    refine add_mem (Submodule.sum_mem _ fun i _ => ?_) (Submodule.smul_mem _ _
      (mem_upSpan hμ (d_mem_osym hc)))
    split_ifs with h
    · rw [smul_mul_assoc]
      refine Submodule.smul_mem _ _ (mem_upSpan ?_ hc)
      have hν : μ + expSingle i ∈ box b a := mem_box.2 ⟨h.1, add_box_mem hμb.2 h⟩
      exact hS.2 μ hμ _ hν (by rw [weight_add_expSingle]; omega)
    · rw [ThickDecomposition.skew_zero_mul]
      exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul z x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ z hx

/-- `Z_S` is stable under the right action of `OΛ_{a+b}`. -/
theorem upSpan_mul_phiAB {S : Finset (Fin b → ℕ)} {F : SkewPolynomial (a+b)}
    (hF : F ∈ upSpan a b S) {h : SkewPolynomial (a+b)} (hh : h ∈ osym (a+b)) :
    F * phiAB a b h ∈ upSpan a b S := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, hμ, c, hc, rfl⟩ := hx
    have e : inclY a b (untwisted b μ) * phiAB a b c * phiAB a b h =
        inclY a b (untwisted b μ) * phiAB a b (c * h) := by
      rw [map_mul]; exact OddMath.SkewPolynomial.mul_assoc _ _ _
    rw [e]
    exact mem_upSpan hμ (mul_mem hc hh)
  | zero => rw [ThickDecomposition.skew_zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [ThickDecomposition.skew_add_mul]; exact add_mem hx hy
  | smul z x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ z hx

open Classical in
/-- **The cell differential**: if `S` and `S ∪ {μ}` are up-closed, then
`d(s̃_μ(y) z · c) - (-1)^{|μ|} s̃_μ(y) z · d(c) ∈ Z_S`. -/
theorem upSpan_cell {S : Finset (Fin b → ℕ)} {μ : Fin b → ℕ} (hS : UpClosed a (insert μ S))
    {c : SkewPolynomial (a+b)} (hc : c ∈ osym (a+b)) :
    dZ a b (inclY a b (untwisted b μ) * phiAB a b c) -
        (-1 : ℤ) ^ weight μ • (inclY a b (untwisted b μ) * phiAB a b (d (a+b) c)) ∈
      upSpan a b S := by
  have hμb := mem_box.1 (hS.1 (Finset.mem_insert_self μ S))
  rw [dZ_mul_phiAB, lemma_4_7_box μ hμb.1 hμb.2, Finset.sum_mul, parityInv_inclY,
    parityInv_untwisted, map_zsmul, smul_mul_assoc, weight, add_sub_cancel_right]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs with h
  · rw [smul_mul_assoc]
    refine Submodule.smul_mem _ _ (mem_upSpan ?_ hc)
    have hν : μ + expSingle i ∈ box b a := mem_box.2 ⟨h.1, add_box_mem hμb.2 h⟩
    have h1 := hS.2 μ (Finset.mem_insert_self μ S) _ hν
      (by rw [weight_add_expSingle]; omega)
    rcases Finset.mem_insert.1 h1 with h2 | h2
    · exfalso
      have := congrArg weight h2
      rw [weight_add_expSingle] at this
      omega
    · exact h2
  · rw [ThickDecomposition.skew_zero_mul]
    exact zero_mem _

/-- Every element of `Z_S` (`S ⊆ Par(b,a)`) is `Σ_{ν ∈ Par(b,a)} s̃_ν(y) z · e_ν` with `e_ν = 0`
for `ν ∉ S`. -/
theorem upSpan_repr {S : Finset (Fin b → ℕ)} (hS : S ⊆ box b a) {F : SkewPolynomial (a+b)}
    (hF : F ∈ upSpan a b S) :
    ∃ e : (Fin b → ℕ) → SkewPolynomial (a+b), (∀ ν, e ν ∈ osym (a+b)) ∧ (∀ ν, ν ∉ S → e ν = 0) ∧
      F = ∑ ν ∈ box b a, inclY a b (untwisted b ν) * phiAB a b (e ν) := by
  classical
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, hμ, c, hc, rfl⟩ := hx
    refine ⟨fun ν => if ν = μ then c else 0, fun ν => ?_, fun ν hν => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact hc
      · exact zero_mem _
    · dsimp only
      rw [ite_eq_right_iff]
      rintro rfl
      exact absurd hμ hν
    · rw [Finset.sum_eq_single_of_mem μ (hS hμ)]
      · dsimp only
        rw [ite_eq_left rfl]
      · intro ν _ hne
        dsimp only
        rw [ite_eq_right hne, map_zero, ThickDecomposition.skew_mul_zero]
  | zero =>
    refine ⟨fun _ => 0, fun _ => zero_mem _, fun _ _ => rfl, ?_⟩
    simp only [map_zero, ThickDecomposition.skew_mul_zero, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    obtain ⟨e, he, heS, rfl⟩ := hx
    obtain ⟨e', he', heS', rfl⟩ := hy
    refine ⟨fun ν => e ν + e' ν, fun ν => add_mem (he ν) (he' ν),
      fun ν hν => by simp only [heS ν hν, heS' ν hν, add_zero], ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [map_add, ThickDecomposition.skew_mul_add]
  | smul z x _ hx =>
    obtain ⟨e, he, heS, rfl⟩ := hx
    refine ⟨fun ν => z • e ν, fun ν => Subring.zsmul_mem _ (he ν) _,
      fun ν hν => by simp only [heS ν hν, smul_zero], ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [map_zsmul, mul_smul_comm]

/-- **Freeness of the cells**: `s̃_μ(y) z · c ∈ Z_S` with `μ ∈ Par(b,a) \ S` forces `c = 0`. -/
theorem upSpan_free {S : Finset (Fin b → ℕ)} (hS : S ⊆ box b a) {μ : Fin b → ℕ}
    (hμ : μ ∈ box b a) (hμS : μ ∉ S) {c : SkewPolynomial (a+b)} (hc : c ∈ osym (a+b))
    (h : inclY a b (untwisted b μ) * phiAB a b c ∈ upSpan a b S) : c = 0 := by
  classical
  obtain ⟨e, he, heS, he0⟩ := upSpan_repr hS h
  have hsum : ∑ ν ∈ box b a,
      inclY a b (untwisted b ν) * phiAB a b (e ν - if ν = μ then c else 0) = 0 := by
    have h1 : ∀ ν ∈ box b a,
        inclY a b (untwisted b ν) * phiAB a b (e ν - if ν = μ then c else 0) =
          inclY a b (untwisted b ν) * phiAB a b (e ν) -
            (if ν = μ then inclY a b (untwisted b μ) * phiAB a b c else 0) := by
      intro ν _
      split_ifs with hν
      · subst hν; rw [map_sub, mul_sub]
      · rw [sub_zero, sub_zero]
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_ite_eq' (box b a) μ,
      ite_eq_left hμ, ← he0, sub_self]
  have key := zab_indep (fun ν => e ν - if ν = μ then c else 0)
    (fun ν => sub_mem (he ν) (by split_ifs; exacts [hc, zero_mem _])) hsum μ hμ
  simpa [heS μ hμS] using key

theorem upSpan_empty : upSpan a b ∅ = ⊥ := by
  rw [upSpan, Submodule.span_eq_bot]
  rintro _ ⟨μ, hμ, _⟩
  exact absurd hμ (Finset.notMem_empty μ)

/-- `Z_{Par(b,a)} = Z_{a,b}`: the basis spans. -/
theorem mem_upSpan_box {F : SkewPolynomial (a+b)} (hF : F ∈ osymAB a b) :
    F ∈ upSpan a b (box b a) := by
  obtain ⟨c, hc, rfl⟩ := zab_span hF
  exact Submodule.sum_mem _ fun μ hμ => mem_upSpan hμ (hc μ)

theorem untwisted_mem_osym {N : ℕ} (l : Fin N → ℕ) : untwisted N l ∈ osym N := by
  rcases N with _ | _ | m
  · exact osym_small (by omega) _
  · exact osym_small (by omega) _
  · have ht : twisted (m+2) l ∈ ElementaryBranching.E (m+2) := by
      rw [twisted_eq_ekl, StaircaseIndependence.E_eq_kernel]
      exact ThickDots.schur_mem_kernel l
    have hE : ElementaryBranching.E (m+2) ≤ (osym (m+2)).map (theta (m+2)) := by
      refine Subring.closure_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      exact ⟨elementary (m+2) k, elementary_mem _ k, theta_elementary _ k⟩
    obtain ⟨x, hx, hxe⟩ := hE ht
    rw [untwisted_eq_theta_twisted, ← hxe]
    change theta (m+2) (theta (m+2) x) ∈ _
    rw [theta_theta]
    exact hx

/-- Conversely `Z_{Par(b,a)} ⊆ Z_{a,b}`. -/
theorem upSpan_le_osymAB {S : Finset (Fin b → ℕ)} {F : SkewPolynomial (a+b)}
    (hF : F ∈ upSpan a b S) : F ∈ osymAB a b := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, _, c, hc, rfl⟩ := hx
    exact mul_mem (inclY_mem (untwisted_mem_osym μ)) (phiAB_mem hc)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul z x _ hx => exact Subring.zsmul_mem _ hx z

/-- An enumeration of `Par(b,a)` by decreasing `|μ|`: all initial segments are up-closed. -/
theorem exists_cell_chain (a b : ℕ) :
    ∃ L : List (Fin b → ℕ), L.Nodup ∧ (∀ μ, μ ∈ L ↔ μ ∈ box b a) ∧
      ∀ j, UpClosed a (L.take j).toFinset := by
  classical
  let le : (Fin b → ℕ) → (Fin b → ℕ) → Bool := fun μ ν => decide (weight ν ≤ weight μ)
  let L := (box b a).toList.mergeSort le
  have hp : L.Perm (box b a).toList := List.mergeSort_perm _ _
  have hsort : L.Pairwise (fun μ ν => le μ ν = true) :=
    List.pairwise_mergeSort (fun x y z hxy hyz => by simp only [le, decide_eq_true_eq] at *; omega)
      (fun x y => by simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) _
  have hmem : ∀ μ, μ ∈ L ↔ μ ∈ box b a := fun μ => by rw [hp.mem_iff, Finset.mem_toList]
  refine ⟨L, hp.nodup_iff.mpr (Finset.nodup_toList _), hmem, fun j => ⟨?_, ?_⟩⟩
  · intro μ hμ
    rw [List.mem_toFinset] at hμ
    exact (hmem μ).1 (List.mem_of_mem_take hμ)
  · intro μ hμ ν hν hw
    rw [List.mem_toFinset] at hμ ⊢
    by_contra hν'
    have hνL := (hmem ν).2 hν
    rw [← List.take_append_drop j L, List.mem_append] at hνL
    rcases hνL with h | h
    · exact hν' h
    · have hpa := hsort
      rw [← List.take_append_drop j L, List.pairwise_append] at hpa
      have := hpa.2.2 μ hμ ν h
      simp only [le, decide_eq_true_eq] at this
      omega

/-- **Ellis–Qi, Corollary 4.8** (finite-cell structure): for the enumeration `μ_1, …, μ_N` of
`Par(b,a)` of `exists_cell_chain`, the submodules `Z_j = Z_{\{μ_1, …, μ_j\}}` satisfy
`Z_0 = 0`, `Z_{a,b} ⊆ Z_N ⊆ Z_{a,b}`, each `Z_j` is a dg submodule (stable under `d` and the right
`OΛ_{a+b}`-action), and `Z_{j+1} = Z_j + s̃_{μ_{j+1}}(y) z · OΛ_{a+b}` with
`d(s̃_μ(y) z · c) ≡ (-1)^{|μ|} s̃_μ(y) z · d(c) (mod Z_j)` and
`s̃_μ(y) z · c ∈ Z_j ⇒ c = 0`: each subquotient is a free right dg `OΛ_{a+b}`-module of rank one.
The first part of Corollary 4.8, the `d`-stability of `span_ℤ {s̃_μ(y) z}`, is
`EQZabSchur.cor_4_8_stable`. -/
theorem cor_4_8 (a b : ℕ) :
    ∃ L : List (Fin b → ℕ), L.Nodup ∧ (∀ μ, μ ∈ L ↔ μ ∈ box b a) ∧
      upSpan a b (L.take 0).toFinset = ⊥ ∧
      (∀ F ∈ osymAB a b, F ∈ upSpan a b (L.take L.length).toFinset) ∧
      (∀ j F, F ∈ upSpan a b (L.take j).toFinset → F ∈ osymAB a b) ∧
      (∀ j F, F ∈ upSpan a b (L.take j).toFinset → dZ a b F ∈ upSpan a b (L.take j).toFinset) ∧
      (∀ j F h, F ∈ upSpan a b (L.take j).toFinset → h ∈ osym (a+b) →
        F * phiAB a b h ∈ upSpan a b (L.take j).toFinset) ∧
      (∀ j (hj : j < L.length) c, c ∈ osym (a+b) →
        dZ a b (inclY a b (untwisted b L[j]) * phiAB a b c) -
          (-1 : ℤ) ^ weight L[j] • (inclY a b (untwisted b L[j]) * phiAB a b (d (a+b) c)) ∈
            upSpan a b (L.take j).toFinset) ∧
      (∀ j (hj : j < L.length) c, c ∈ osym (a+b) →
        inclY a b (untwisted b L[j]) * phiAB a b c ∈ upSpan a b (L.take j).toFinset → c = 0) := by
  classical
  obtain ⟨L, hnd, hmem, hup⟩ := exists_cell_chain a b
  have htake : ∀ j (hj : j < L.length), (L.take (j+1)).toFinset = insert L[j] (L.take j).toFinset :=
    fun j hj => by
      rw [List.take_add_one, List.toFinset_append, List.getElem?_eq_getElem hj]
      ext x
      simp [or_comm]
  have hnot : ∀ j (hj : j < L.length), L[j] ∉ L.take j := fun j hj h => by
    rw [List.mem_iff_getElem] at h
    obtain ⟨i, hi, hx⟩ := h
    rw [List.length_take] at hi
    rw [List.getElem_take] at hx
    have := (List.Nodup.getElem_inj_iff hnd).1 hx
    omega
  refine ⟨L, hnd, hmem, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [upSpan_empty]
  · intro F hF
    rw [List.take_length]
    have hbox : L.toFinset = box b a := by ext μ; rw [List.mem_toFinset, hmem]
    rw [hbox]
    exact mem_upSpan_box hF
  · intro j F hF
    exact upSpan_le_osymAB hF
  · intro j F hF
    exact upSpan_dZ (hup j) hF
  · intro j F h hF hh
    exact upSpan_mul_phiAB hF hh
  · intro j hj c hc
    have h1 := hup (j+1)
    rw [htake j hj] at h1
    exact upSpan_cell h1 hc
  · intro j hj c hc h
    refine upSpan_free (hup j).1 ((hmem _).1 (List.getElem_mem hj)) ?_ hc h
    rw [List.mem_toFinset]
    exact hnot j hj


/-- The number of cells: `#Par(b,a) = binom(a+b, a)` (the graded rank of `Z_{a,b}` over
`OΛ_{a+b}` is `Σ_{μ ∈ Par(b,a)} q^{|μ|} = BoxPartitionCount.gauss b a`, a Gaussian binomial). -/
theorem card_cells (a b : ℕ) : (box b a).card = (a + b).choose a := by
  rw [card_box, add_comm, Nat.choose_symm_add]

end

end OddMath.Frontier.EQZab
