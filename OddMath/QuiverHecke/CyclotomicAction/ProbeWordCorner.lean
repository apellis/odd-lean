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

end OddMath.QuiverHecke
