import OddMath.SKM.BubbleGrading
import OddMath.SKM.GradedSpanning
import OddMath.SKM.Nondegeneracy
import OddMath.SKM.MixedFibres
import OddMath.SKM.WeightedWords

/-!
# Laurentian Hom-spaces

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §§11–12:
Theorem 8.1 implies finite-dimensional integer degree pieces and a uniform lower
bound for each Hom-space, with the normalizing units `CScalars` of (1.17).
For arbitrary colour sets we explicitly require that
only finitely many colours have symmetrizer degree below any fixed bound.
No nondegeneracy assumption or equality of boundary weights is needed.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation StringDiagrams.Chord
open scoped BigOperators

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}

/-- Local finiteness of the positive colour degrees, allowing infinitely many colours. -/
def Symmetrizer.DegreeLocallyFinite (sy : Symmetrizer D) : Prop :=
  ∀ N : ℕ, Set.Finite {i | sy.d i ≤ N}

variable (sy : Symmetrizer D)

/-- Colour local finiteness implies local finiteness of all coefficient generators. -/
theorem symGenNatDegree_finite (hf : sy.DegreeLocallyFinite) (N : ℕ) :
    Set.Finite {g | symGenNatDegree D sy g ≤ N} := by
  classical
  have hp := ((hf N).prod (Set.finite_Iic N)).image
    (fun p : I × ℕ => (Sum.inl p : SYMGen D))
  have he : Set.Finite {i : {i : I // D.parity i = 1} | sy.d i ≤ N} :=
    Set.Finite.preimage (f := fun i : {i : I // D.parity i = 1} => i.val)
      Subtype.val_injective.injOn (hf N)
  apply (hp.union (he.image Sum.inr)).subset
  intro g hg
  have hg' : symGenDegree D sy g ≤ (N : ℤ) := by
    rw [← symGenNatDegree_cast sy g]
    exact_mod_cast hg
  rcases g with ⟨i, n⟩ | i
  · apply Or.inl
    refine ⟨(i, n), ⟨?_, ?_⟩, rfl⟩
    all_goals
      have hi := sy.pos i
      dsimp [symGenDegree] at hg'
      split_ifs at hg' <;> simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    · nlinarith [Nat.cast_nonneg (α := ℤ) n]
    · nlinarith [Nat.cast_nonneg (α := ℤ) n]
    · have : (n : ℤ) ≤ N := by nlinarith [Nat.cast_nonneg (α := ℤ) n]
      exact_mod_cast this
    · have : (n : ℤ) ≤ N := by nlinarith [Nat.cast_nonneg (α := ℤ) n]
      exact_mod_cast this
  · apply Or.inr
    refine ⟨i, ?_, rfl⟩
    change sy.d i ≤ (N : ℤ)
    have hi := sy.pos i
    dsimp [symGenDegree] at hg'
    omega

/-- Coefficient words have finite bounded degree sets. -/
theorem symGen_words_finite (hf : sy.DegreeLocallyFinite) (N : ℤ) :
    Set.Finite {l : List (SYMGen D) | (l.map (symGenDegree D sy)).sum ≤ N} := by
  apply (finite_weighted_words (symGenNatDegree D sy) (symGenNatDegree_pos sy)
    (symGenNatDegree_finite sy hf) N.toNat).subset
  intro l hl
  change (l.map (symGenNatDegree D sy)).sum ≤ N.toNat
  have hc : ((l.map (symGenNatDegree D sy)).sum : ℤ) =
      (l.map (symGenDegree D sy)).sum := by
    simp only [Nat.cast_list_sum, List.map_map, Function.comp_def, symGenNatDegree_cast]
  change (l.map (symGenDegree D sy)).sum ≤ N at hl
  omega

namespace SYM
variable {k : Type w} [CommRing k]

/-- Words in the abstract generators span the coefficient algebra. -/
theorem span_words :
    Submodule.span k (Set.range (fun l : List (SYMGen D) => (l.map (ι D k)).prod)) = ⊤ := by
  let S := Submodule.span k (Set.range (fun l : List (SYMGen D) => (l.map (ι D k)).prod))
  have hone : (1 : SYM D k) ∈ S := Submodule.subset_span ⟨[], rfl⟩
  have hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨m, rfl⟩ := hy
        exact Submodule.subset_span ⟨l ++ m, by simp⟩
      | zero => simp
      | add x y _ _ hx hy => simpa only [mul_add] using S.add_mem hx hy
      | smul r x _ hx => simpa only [mul_smul_comm] using S.smul_mem r hx
    | zero => simp
    | add x y _ _ hx hy => simpa only [add_mul] using S.add_mem hx hy
    | smul r x _ hx => simpa only [smul_mul_assoc] using S.smul_mem r hx
  let A : Subalgebra k (SYM D k) :=
    { S with
      one_mem' := hone
      mul_mem' := fun hx hy => hmul _ hx _ hy
      algebraMap_mem' := fun r => by
        change algebraMap k (SYM D k) r ∈ S
        simpa only [Algebra.smul_def, mul_one] using S.smul_mem r hone }
  have h := range_le D k (AlgHom.id k (SYM D k)) A (fun g =>
    (Submodule.subset_span ⟨[g], by simp⟩ : ι D k g ∈ S))
  apply top_unique
  intro x _
  exact h ⟨x, rfl⟩

end SYM

namespace MatchingBasisChoice
variable {a b : List (Letter I)} (F : MatchingBasisChoice a b)
variable {k : Type w} [CommRing k] {Sc : Scalars D k} (cs : CScalars Sc) (μ : X)

/-- A decorated representative with a word of coefficient generators. -/
def wordEval (t : F.Labels × List (SYMGen D)) :
    (pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b) :=
  F.coefficientMap cs μ t.1 ((t.2.map (SYM.ι D k)).prod)

/-- The sum of the diagram degree and the coefficient-word degree. -/
def wordDegree (t : F.Labels × List (SYMGen D)) : ℤ :=
  tableDegree D sy μ (F.layers t.1) + (t.2.map (symGenDegree D sy)).sum

/-- Theorem 8.1 with coefficient words instead of abstract algebra coefficients. -/
theorem span_wordEval : Submodule.span k (Set.range (F.wordEval cs μ)) = ⊤ := by
  let S := Submodule.span k (Set.range (F.wordEval cs μ))
  have hm (t : F.Labels) (p : SYM D k) : F.coefficientMap cs μ t p ∈ S := by
    have hp : p ∈ Submodule.span k
        (Set.range (fun l : List (SYMGen D) => (l.map (SYM.ι D k)).prod)) := by
      rw [SYM.span_words]
      trivial
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨l, rfl⟩ := hp
      exact Submodule.subset_span ⟨(t, l), rfl⟩
    | zero => simpa only [map_zero] using S.zero_mem
    | add p q _ _ hp hq => simpa only [map_add] using S.add_mem hp hq
    | smul r p _ hp => simpa only [map_smul] using S.smul_mem r hp
  apply top_unique
  intro f hf
  clear hf
  obtain ⟨x, rfl⟩ := F.expansion_surjective cs μ f
  classical
  induction x using Finsupp.induction with
  | zero => simpa only [map_zero] using S.zero_mem
  | @single_add t p x _ _ ih =>
    rw [map_add, F.expansion_single]
    exact S.add_mem (hm t p) ih

/-- The coefficient word has the sum of its generator degrees. -/
theorem beta_word_mem_gdeg (l : List (SYMGen D)) :
    betaSYM cs μ ((l.map (SYM.ι D k)).prod) ∈
      (pres D Sc).homDeg (gdeg D sy) (ob D μ []) (ob D μ [])
        ((l.map (symGenDegree D sy)).sum) := by
  induction l with
  | nil =>
    simpa only [List.map_nil, List.prod_nil, List.sum_nil, map_one, End.one_def] using
      (id_mem_homDeg (pres D Sc) (gdeg D sy) (ob D μ []))
  | cons g l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, map_mul, betaSYM_ι]
    simpa only [add_comm, End.mul_def] using
      comp_mem_homDeg ih (betaSYMGen_mem_gdeg sy cs μ g)

/-- Every member of the spanning family has its declared integer degree. -/
theorem wordEval_mem_gdeg (t : F.Labels × List (SYMGen D)) :
    F.wordEval cs μ t ∈ (pres D Sc).homDeg (gdeg D sy) (ob D μ a) (ob D μ b)
      (F.wordDegree sy μ t) := by
  unfold wordEval coefficientMap wordDegree
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [add_comm]
  exact comp_mem_homDeg
    (bubAt_mem_gdeg sy a (beta_word_mem_gdeg sy cs μ t.2))
    (xev_mem_gdeg sy cs μ a b (F.layers t.1))

/-- Decorated diagrams have a uniform lower degree bound. -/
theorem degree_bounded_below : ∃ N : ℤ, ∀ t : F.Labels,
    N ≤ tableDegree D sy μ (F.layers t) := by
  have hf := matching_representatives_finite a b F.members
    (fun R hR => (F.matching R hR).1) F.unique
  have hb := (hf.image (fun R => tableDegree D sy μ (tLay a R))).bddBelow
  obtain ⟨N, hN⟩ := hb
  refine ⟨N, fun t => ?_⟩
  have hbase := hN (Set.mem_image_of_mem _ t.1.property)
  have hd := (mixed_decorated_degree_parity D sy μ (F.matching t.1 t.1.property).1
    (F.points t.1) (F.onStrand t.1) t.2 (F.serialize t.1 t.2) (F.decorates t.1 t.2)).1
  have hn : 0 ≤ ∑ j, (t.2 j : ℤ) * (2 * sy.d (matchingStrandColour a t.1.val j)) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (by omega) (sy.pos _).le))
  change N ≤ tableDegree D sy μ (dLay a (F.serialize t.1 t.2))
  omega

/-- Each decorated-diagram degree fiber is finite. -/
theorem degree_finite (n : ℤ) :
    Set.Finite {t : F.Labels | tableDegree D sy μ (F.layers t) = n} :=
  mixed_labelled_degree_finite D sy μ a b F.members
    (fun R hR => (F.matching R hR).1) F.unique F.points F.onStrand
    F.serialize F.decorates n

/-- Adding positive coefficient words preserves local finiteness of degree fibers. -/
theorem wordDegree_finite (hf : sy.DegreeLocallyFinite) (n : ℤ) :
    Set.Finite {t : F.Labels × List (SYMGen D) | F.wordDegree sy μ t = n} := by
  obtain ⟨N, hN⟩ := F.degree_bounded_below sy μ
  have hd : Set.Finite {t : F.Labels | tableDegree D sy μ (F.layers t) ≤ n} := by
    apply ((Set.finite_Icc N n).biUnion (fun z _ => F.degree_finite sy μ z)).subset
    intro t ht
    exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨⟨hN t, ht⟩, rfl⟩⟩
  apply (hd.prod (symGen_words_finite sy hf (n - N))).subset
  intro t ht
  have hn : 0 ≤ (t.2.map (symGenDegree D sy)).sum :=
    List.sum_nonneg (fun x hx => by
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
      exact (symGenDegree_pos sy g).le)
  have hb := hN t.1
  change tableDegree D sy μ (F.layers t.1) + (t.2.map (symGenDegree D sy)).sum = n at ht
  exact ⟨by change tableDegree D sy μ (F.layers t.1) ≤ n; omega,
    by change (t.2.map (symGenDegree D sy)).sum ≤ n - N; omega⟩

/-- The complete spanning family has a uniform lower degree bound. -/
theorem wordDegree_bounded_below : ∃ N : ℤ, ∀ t : F.Labels × List (SYMGen D),
    N ≤ F.wordDegree sy μ t := by
  obtain ⟨N, hN⟩ := F.degree_bounded_below sy μ
  refine ⟨N, fun t => ?_⟩
  have hn : 0 ≤ (t.2.map (symGenDegree D sy)).sum :=
    List.sum_nonneg (fun x hx => by
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
      exact (symGenDegree_pos sy g).le)
  exact (hN t.1).trans (le_add_of_nonneg_right hn)

end MatchingBasisChoice

variable {k : Type w} [Field k] (Sc : Scalars D k) (cs : CScalars Sc)
include cs

/-- **BE2 §§11–12: Laurentian Hom-spaces, with a local-finiteness hypothesis.**
This intermediate statement assumes `sy.DegreeLocallyFinite`, which is not
explicit in the paper. Whether the unrestricted infinite-colour assertions
require a completion or a finiteness restriction is a source question in issue #42.
All integer degree pieces are finite dimensional and vanish uniformly below
some bound. The proof uses spanning, without the Nondegeneracy Conjecture. -/
theorem hom_laurentian (hc : Sc.Homogeneous) (hf : sy.DegreeLocallyFinite)
    (μ : X) (a b : List (Letter I)) :
    (∀ n, FiniteDimensional k ((pres D Sc).homDeg (gdeg D sy) (ob D μ a) (ob D μ b) n)) ∧
      ∃ N, ∀ n < N, (pres D Sc).homDeg (gdeg D sy) (ob D μ a) (ob D μ b) n = ⊥ := by
  obtain ⟨F⟩ := MatchingBasisChoice.nonempty a b
  exact homDeg_laurentian_of_spanning D sy Sc hc _ _
    (F.wordEval cs μ) (F.wordDegree sy μ) (F.wordEval_mem_gdeg sy cs μ)
    (F.span_wordEval cs μ) (F.wordDegree_finite sy μ hf) (F.wordDegree_bounded_below sy μ)

/-- The integer-degree pieces intersected with either parity have the same
Laurentian bounds, with one lower bound for both parities. -/
theorem hom_parity_laurentian (hc : Sc.Homogeneous) (hf : sy.DegreeLocallyFinite)
    (μ : X) (a b : List (Letter I)) :
    (∀ n p, FiniteDimensional k
      ↥((pres D Sc).homDeg (gdeg D sy) (ob D μ a) (ob D μ b) n ⊓ homPar D Sc μ a b p)) ∧
      ∃ N, ∀ n < N, ∀ p,
        (pres D Sc).homDeg (gdeg D sy) (ob D μ a) (ob D μ b) n ⊓
          homPar D Sc μ a b p = ⊥ := by
  obtain ⟨hfin, N, hN⟩ := hom_laurentian sy Sc cs hc hf μ a b
  constructor
  · intro n p
    let := hfin n
    exact FiniteDimensional.of_injective (Submodule.inclusion inf_le_left)
      (Submodule.inclusion_injective inf_le_left)
  · exact ⟨N, fun n hn p => by rw [hN n hn, bot_inf_eq]⟩

end OddMath.SKM
