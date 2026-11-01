import OddMath.QuiverHecke.CyclotomicAction.ProbeDotPropagation
import OddMath.QuiverHecke.CyclotomicAction.Quotient
import Mathlib.RingTheory.Idempotents

/-! # Probe dot propagation in actual cyclotomic word corners

The equal-colour step of `InvertibleDotProbe.md` §3 uses the existing
cyclotomic algebra and its literal word idempotent corner. The affine
word endomorphism map is unital into this corner, even when the corner
vanishes. No second quotient presentation is introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  [Fintype I] (a : I → Polynomial k)

def cyclotomicWordIdempotent {n : ℕ} (s : Word I (n + 1)) :
    CyclotomicAlgebra D Sc a n :=
  cyclotomicMk D Sc a n (Hn.wordIdempotent s)

theorem cyclotomicWordIdempotent_idem {n : ℕ} (s : Word I (n + 1)) :
    IsIdempotentElem (cyclotomicWordIdempotent D Sc a s) := by
  change cyclotomicMk D Sc a n _ * cyclotomicMk D Sc a n _ = _
  rw [← map_mul, Hn.wordIdempotent_sq]
  rfl

abbrev CyclotomicWordCorner {n : ℕ} (s : Word I (n + 1)) :=
  (cyclotomicWordIdempotent_idem D Sc a s).Corner

/-- Literal diagonal insertion followed by the actual cyclotomic quotient,
with its codomain restricted to the word corner whose identity is e_s. -/
def cyclotomicWordEnd {n : ℕ} (s : Word I (n + 1)) :
    End (wordObj D Sc s) →+* CyclotomicWordCorner D Sc a s where
  toFun f := ⟨cyclotomicMk D Sc a n (Hn.cornerInclusion s f), by
    apply (Subsemigroup.mem_corner_iff (cyclotomicWordIdempotent_idem D Sc a s)).mpr
    constructor
    · change cyclotomicMk D Sc a n (FiniteHomMatrix.single s s (𝟙 _)) *
        cyclotomicMk D Sc a n (FiniteHomMatrix.single s s f) = _
      rw [← map_mul, FiniteHomMatrix.single_mul_single, Category.comp_id]
      rfl
    · change cyclotomicMk D Sc a n (FiniteHomMatrix.single s s f) *
        cyclotomicMk D Sc a n (FiniteHomMatrix.single s s (𝟙 _)) = _
      rw [← map_mul, FiniteHomMatrix.single_mul_single, Category.id_comp]
      rfl⟩
  map_one' := Subtype.ext rfl
  map_zero' := Subtype.ext (by
    change cyclotomicMk D Sc a n (Hn.cornerInclusion s 0) = 0
    rw [map_zero, map_zero])
  map_add' f g := Subtype.ext (by
    change cyclotomicMk D Sc a n (Hn.cornerInclusion s (f + g)) =
      cyclotomicMk D Sc a n (Hn.cornerInclusion s f) +
        cyclotomicMk D Sc a n (Hn.cornerInclusion s g)
    rw [map_add, map_add])
  map_mul' f g := Subtype.ext (by
    change cyclotomicMk D Sc a n (Hn.cornerInclusion s (f * g)) =
      cyclotomicMk D Sc a n (Hn.cornerInclusion s f) *
        cyclotomicMk D Sc a n (Hn.cornerInclusion s g)
    rw [map_mul, map_mul])

def probeBlockWord (pre post : List I) (i : I) :
    Word I ((pre.length + post.length + 1) + 1) :=
  ⟨pre ++ [i,i] ++ post, by simp; omega⟩

/-- The actual defining first-dot relation, now in the unital word corner. -/
theorem cyclotomicWordEnd_generator {n : ℕ} (s : Word I (n + 1)) :
    cyclotomicWordEnd D Sc a s
      (Polynomial.aeval (dotE D Sc s.val 0)
        (a (s.val.get ⟨0, by rw [s.property]; omega⟩))) = 0 := by
  apply Subtype.ext
  change cyclotomicMk D Sc a n (cyclotomicGenerator D Sc a s) = 0
  exact cyclotomicMk_generator D Sc a s

abbrev cyclotomicBlockDot (pre post : List I) (i : I) (r : ℕ) :
    CyclotomicWordCorner D Sc a (probeBlockWord pre post i) :=
  cyclotomicWordEnd D Sc a (probeBlockWord pre post i)
    (dotE D Sc (pre ++ [i,i] ++ post) r)

abbrev cyclotomicBlockCross (pre post : List I) (i : I) :
    CyclotomicWordCorner D Sc a (probeBlockWord pre post i) :=
  cyclotomicWordEnd D Sc a (probeBlockWord pre post i)
    (crossE D Sc (pre ++ [i,i] ++ post) pre.length)

private theorem oddTwo_map {R S : Type*} [Ring R] [Ring S] (q : R →+* S)
    {u v T : R} (h : SignedNilHecke.OddTwo u v T) :
    SignedNilHecke.OddTwo (q u) (q v) (q T) where
  t_u := by simpa only [map_add, map_mul, map_one] using congrArg q h.t_u
  u_t := by simpa only [map_add, map_mul, map_one] using congrArg q h.u_t
  u_v := by simpa only [map_mul, map_neg] using congrArg q h.u_v
  t_t := by simpa only [map_mul, map_zero] using congrArg q h.t_t

private theorem evenTwo_map {R S : Type*} [Ring R] [Ring S] (q : R →+* S)
    {u v T : R} (h : SignedNilHecke.EvenTwo u v T) :
    SignedNilHecke.EvenTwo (q u) (q v) (q T) where
  t_u := by simpa only [map_sub, map_mul, map_one] using congrArg q h.t_u
  u_t := by simpa only [map_sub, map_mul, map_one] using congrArg q h.u_t
  u_v := by simpa only [map_mul] using congrArg q h.u_v
  t_t := by simpa only [map_mul, map_zero] using congrArg q h.t_t

theorem cyclotomicBlock_oddTwo (pre post : List I) (i : I) (hi : D.parity i = 1) :
    SignedNilHecke.OddTwo (cyclotomicBlockDot D Sc a pre post i pre.length)
      (cyclotomicBlockDot D Sc a pre post i (pre.length + 1))
      (cyclotomicBlockCross D Sc a pre post i) := by
  exact oddTwo_map (cyclotomicWordEnd D Sc a (probeBlockWord pre post i))
    (oddTwo_block D Sc pre post i hi)

theorem cyclotomicBlock_evenTwo (pre post : List I) (i : I) (hi : D.parity i = 0) :
    SignedNilHecke.EvenTwo (cyclotomicBlockDot D Sc a pre post i pre.length)
      (cyclotomicBlockDot D Sc a pre post i (pre.length + 1))
      (cyclotomicBlockCross D Sc a pre post i) := by
  exact evenTwo_map (cyclotomicWordEnd D Sc a (probeBlockWord pre post i))
    (evenTwo_block D Sc pre post i hi)

/-- Same-colour probe induction in the actual quotient corner: injectivity
of the preceding dot implies injectivity of the next dot in either parity. -/
theorem cyclotomicBlock_dot_injective (pre post : List I) (i : I)
    (hu : Function.Injective (fun z : CyclotomicWordCorner D Sc a (probeBlockWord pre post i) =>
      cyclotomicBlockDot D Sc a pre post i pre.length * z)) :
    Function.Injective (fun z : CyclotomicWordCorner D Sc a (probeBlockWord pre post i) =>
      cyclotomicBlockDot D Sc a pre post i (pre.length + 1) * z) := by
  rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
  · exact (cyclotomicBlock_evenTwo D Sc a pre post i hi).right_mul_injective hu
  · exact (cyclotomicBlock_oddTwo D Sc a pre post i hi).right_mul_injective hu

/-- The first dot of the quadratic probe is its own inverse, in its actual
word corner. No nonzero-word or finite-dimensionality premise is used. -/
theorem quadraticProbe_firstDot_isUnit {n : ℕ} (s : Word I (n + 1)) :
    IsUnit (cyclotomicWordEnd D Sc (fun _ => Polynomial.X ^ 2 - 1) s
      (dotE D Sc s.val 0)) := by
  let x := cyclotomicWordEnd D Sc (fun _ => Polynomial.X ^ 2 - 1) s
    (dotE D Sc s.val 0)
  have hx : x * x = 1 := by
    have h := cyclotomicWordEnd_generator D Sc (fun _ => Polynomial.X ^ 2 - 1) s
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one] at h
    exact (pow_two x).symm.trans (sub_eq_zero.mp h)
  exact ⟨⟨x, x, hx, hx⟩, rfl⟩

/-- The first same-colour propagation step of the quadratic probe has every
premise discharged by the actual cyclotomic relation, for either parity. -/
theorem quadraticProbe_secondDot_injective (post : List I) (i : I) :
    Function.Injective (fun z : CyclotomicWordCorner D Sc
      (fun _ => Polynomial.X ^ 2 - 1) (probeBlockWord [] post i) =>
      cyclotomicBlockDot D Sc (fun _ => Polynomial.X ^ 2 - 1) [] post i 1 * z) := by
  apply cyclotomicBlock_dot_injective D Sc (fun _ => Polynomial.X ^ 2 - 1) [] post i
  exact (IsUnit.isUnit_iff_mulLeft_bijective.mp
    (quadraticProbe_firstDot_isUnit D Sc (probeBlockWord [] post i))).1

end OddMath.QuiverHecke
