import OddMath.Frontier.VariableEmbedding
import OddMath.Frontier.DotContexts

/-!
# Functorial variable embeddings and naturality of dot words

This extends the checked zero-extension map and chronological (bottom-first)
dot action on the actual integer skew-polynomial model. Source convention:
EKL arXiv:1111.1320v1, §2.1.1 (2.1), p.3; increasing-index normal order and
Koszul signs are locked in the sign convention and translations.yaml.

All ranks, words and source inputs are arbitrary. Equality reflection below
quantifies only over embedded source inputs, not arbitrary ambient spectator
inputs. Neither raw-word faithfulness nor crossing naturality is asserted.
-/

namespace OddMath.Frontier.DotLocality

open OddMath.SkewPolynomial
open OddMath.Frontier.VariableEmbedding
open OddMath.Frontier.DotContexts

variable {m n p : ℕ}

/-- The unit exponent at a selected variable is preserved by zero extension. -/
@[simp] theorem expEmbed_single (e : Fin m ↪o Fin n) (i : Fin m) :
    expEmbed e (expSingle i) = expSingle (e i) := by
  classical
  funext j
  by_cases h : j ∈ Set.range e
  · obtain ⟨k, rfl⟩ := h
    simp [expSingle]
  · have hne : e i ≠ j := fun hij => h ⟨i, hij⟩
    simp [expEmbed_not_mem_range e _ j h, expSingle, hne]

/-- The polynomial embedding sends each dot generator to its selected variable. -/
@[simp] theorem embed_generator (e : Fin m ↪o Fin n) (i : Fin m) :
    embed e (generator i) = generator (e i) := by
  simp [generator]

@[simp] theorem expEmbed_id (a : Fin m → ℕ) :
    expEmbed ((OrderIso.refl (Fin m)).toOrderEmbedding) a = a := by
  funext i
  exact expEmbed_apply ((OrderIso.refl (Fin m)).toOrderEmbedding) a i

/-- Composition is first `e`, then `d`, on both exponents and their zero supports. -/
theorem expEmbed_comp (e : Fin m ↪o Fin n) (d : Fin n ↪o Fin p)
    (a : Fin m → ℕ) :
    expEmbed (e.trans d) a = expEmbed d (expEmbed e a) := by
  funext k
  by_cases hd : k ∈ Set.range d
  · obtain ⟨j, rfl⟩ := hd
    rw [expEmbed_apply]
    by_cases he : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := he
      exact (expEmbed_apply (e.trans d) a i).trans (expEmbed_apply e a i).symm
    · have hcomp : d j ∉ Set.range (e.trans d) := by
        rintro ⟨i, hi⟩
        exact he ⟨i, d.injective hi⟩
      rw [expEmbed_not_mem_range _ _ _ hcomp, expEmbed_not_mem_range _ _ _ he]
  · have hcomp : k ∉ Set.range (e.trans d) := by
      rintro ⟨i, hi⟩
      exact hd ⟨e i, hi⟩
    rw [expEmbed_not_mem_range _ _ _ hcomp, expEmbed_not_mem_range _ _ _ hd]

@[simp] theorem embed_id (f : SkewPolynomial m) :
    embed ((OrderIso.refl (Fin m)).toOrderEmbedding) f = f := by
  induction f using Finsupp.induction_linear with
  | zero => exact embed_zero _
  | add f g hf hg => rw [embed_add, hf, hg]
  | single a c =>
      change embed _ (monomial a c) = monomial a c
      rw [embed_monomial, expEmbed_id]

/-- Functoriality on the actual finite-support integer polynomials. -/
theorem embed_comp (e : Fin m ↪o Fin n) (d : Fin n ↪o Fin p)
    (f : SkewPolynomial m) :
    embed (e.trans d) f = embed d (embed e f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [embed_zero]
  | add f g hf hg => simp only [embed_add, hf, hg]
  | single a c =>
      change embed _ (monomial a c) = embed _ (embed _ (monomial a c))
      simp only [embed_monomial, expEmbed_comp]

/-- Every chronological dot word commutes with an order-preserving embedding. -/
theorem denote_embed (e : Fin m ↪o Fin n) (w : List (Fin m))
    (f : SkewPolynomial m) :
    embed e (denote w f) = denote (w.map e) (embed e f) := by
  induction w generalizing f with
  | nil => rfl
  | cons i rest ih =>
      simp only [denote_cons, List.map_cons]
      rw [ih, embed_mul, embed_generator]

/-- Reflection at a single source input, using the parent's injectivity theorem. -/
theorem denote_embed_eq_iff (e : Fin m ↪o Fin n) (u v : List (Fin m))
    (f : SkewPolynomial m) :
    denote (u.map e) (embed e f) = denote (v.map e) (embed e f) ↔
      denote u f = denote v f := by
  rw [← denote_embed, ← denote_embed]
  exact (embed_injective e).eq_iff

/-- Operator equality is preserved and reflected on embedded source inputs only. -/
theorem denote_embed_operator_eq_iff (e : Fin m ↪o Fin n) (u v : List (Fin m)) :
    (∀ f : SkewPolynomial m,
      denote (u.map e) (embed e f) = denote (v.map e) (embed e f)) ↔
    (∀ f : SkewPolynomial m, denote u f = denote v f) := by
  constructor
  · intro h f
    exact (denote_embed_eq_iff e u v f).mp (h f)
  · intro h f
    exact (denote_embed_eq_iff e u v f).mpr (h f)

end OddMath.Frontier.DotLocality
