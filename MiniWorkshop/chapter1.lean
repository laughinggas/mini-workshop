import Mathlib.Analysis.BoxIntegral.Partition.Basic
import Mathlib.Data.Finset.Sups
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Data.Fin.SuccPred
import Mathlib.Probability.ProbabilityMassFunction.Basic

-- The above files are our imports from Mathlib. It is possible that there are things in mathlib which are not in these files.
-- So, if you wish to search mathlib, you may look at `https://leanprover-community.github.io/mathlib4_docs/`.
-- Simply type the name of the theorem (or the name you think the theorem has), and potential searches will come up!
-- For today, I will put the names of all lemmas you might require.

-- We will often be dealing with `Fin n` , which is the set {0, 1, ..., n - 1}, and `Finset X` (finite sets taking values of type `X`).
-- Any natural number `i` is of type `Fin n` looks like `⟨i, hi⟩`, where `hi` is the proof that `hi : i < n`. This is how all numbers of type `Fin n` are constructed.
-- Instead of writing it in this way, given `x : Fin n`, `↑x : Nat` or `x.val` denotes the natural number `x % n`, or x mod n.

-- First we set our number of slices to be `n`. We set `n` to be non-zero in the typeclass inference system.
variable {n : ℕ} [NeZero n]

lemma pred'_eq_iff_eq_succ' (x y : Fin n) : x - 1 = y ↔ x = y + 1 := by
-- we need to split it into 2 implications
refine' ⟨_, _⟩ -- get `⟨` by pressing \ and <
-- now we have 2 goals: press \ and . to get `·`. It focuses on the first goal.
· intro h -- now we have a hypothesis, `intro` introduces it as a hypothesis instead of an implication
  rw [← h, sub_add_cancel] -- How can we now solve it? We first begin by rewriting `y` in terms of `x` using `h` in reverse, then we rewrite the lemma `sub_add_cancel`
· sorry -- can you complete this using `add_sub_cancel_right`?

-- Hmm, the above lemma seems fairly obvious, shouldn't this already be in the library?
-- Can I check if it is in the library without looking at mathlib documentation? Yep! Just try `apply?` after `by`.

-- Can you now try this?
lemma succ'_eq_iff_eq_pred' (x y : Fin n) : x + 1 = y ↔ x = y - 1 := by sorry

-- `apply?` seems to be a great trick! Does it always help though?
lemma pred'_ne_self (x : Fin (n + 1)) : x - 1 ≠ x := by
-- Lets try another tactic called `simp`. This is used to simplify expressions. Just type `simp` in the proof below.
-- This simplifies the expression vastly, but it does not catch that `n` must be nonzero. This fact is given by the lemma `NeZero.ne`.
-- To give an additional helpful lemma `h` or fact to `simp`, you can try `simp [h]`.
-- It is also good practice to know exactly which lemmas `simp` found. We get this by looking at `simp?`.
sorry

-- One can also tag lemmas with simp using `@[simp]`, and then they can be used-- try it with the previous lemma `succ'_eq_iff_eq_pred'`
lemma succ'_eq_iff_eq_pred'' (x y : Fin n) : x + 1 = y ↔ x = y - 1 := by sorry

lemma succ'_ne_self (x : Fin (n + 1)) : x + 1 ≠ x := by
-- what does `apply?` give you here?
  sorry

-- Some other rewrite categories:
-- `rw [h] at t` rewrites `h` at the hypothesis `t`
-- `rw [← h]` rewrites `h` backwards (`←` can be got by `\` and `l`)

-- Let us start with some easy proofs
-- lemmas used(in order): `Fin.le_def`, `Fin.coe_sub_one`, `if_neg`, `Nat.le_sub_one_of_lt`
-- use `#check` to see what these lemmas say
lemma Fin.le_sub_one_of_lt {b x : Fin (n + 1)} (hb : b ≠ 0) (h : x < b) : x ≤ b - 1 := by
  -- why do we need the condition `hb` here?
  -- We use the tactic rw to rewrite or substitute "expressions"
  -- `rw [h]` rewrites the lemma h in the first position of occurence
  -- The first lemma, for example, is an iff statement. So we can substitute the first statement for the second.
  -- Use `rw` to rewrite the goal term using the first 3 lemmas
  -- Notice that we have an equality, which cannot be dealt with using `rw`.
  -- We can use the tactic `apply` in this situation, which will replace the goal with the hypotheses that would be needed to reach the conclusion given in the goal.
  -- Use `apply` with the last lemma, you are left with a hypothesis. Can you use the given assumption to prove the goal?
  sorry

-- used lemmas (in order): `Fin.le_def`, `Fin.coe_sub_one`, `if_neg`, `Nat.pred_eq_sub_one`, `Nat.le_pred_iff_lt`, `Fin.lt_def`, `Nat.pos_of_ne_zero`, `Fin.ext_iff`, `Fin.val_zero`
-- notice that for a proposition `p`, `¬ p` is the same as `p → False`. So one can use `intro` to get hold of `p` as a hypothesis.
-- this can also be solved using the tactics `contrapose` and `push_neg at *`, play with it if you like!
lemma Fin.lt_sub_of_le_sub_one {b x : Fin (n + 1)} (hb : b ≠ 0) (h : x ≤ b - 1) : x < b := by
sorry

-- this should now be easy!
lemma Fin.lt_sub_iff_le_sub_one {b x : Fin (n + 1)} (hb : b ≠ 0) : x ≤ b - 1 ↔ x < b :=
sorry

-- You should see some yellow squiggly lines appear in the above proofs. They are telling us that you don't actually need the assumption that `n` is nonzero for this lemma. How can we fix this?

-- Optional exercise: can you put comments on the lemmas below?

lemma pred'_lt_self {x : Fin n} (hx : 0 < x) : x - 1 < x := by
  by_contra hg
  have h₁ : x ≤ x - 1 := by
    exact Fin.not_lt.mp hg
  cases n with -- note that we are using the fact that the naturals are an inductive type here: any natural is either 0 or the successor of a smaller natural
  | zero =>
    absurd Fin.pos x
    decide
  | succ d => -- n = d + 1
    absurd (Fin.pos_iff_ne_zero' x).mp hx
    exact Fin.le_sub_one_iff.mp h₁

lemma sub_one_val_succ_lt {i : Fin n} (h1 : i.val.succ < n) (h2 : i ≠ 0) : (i - 1).val.succ < n := by
  apply lt_trans _ h1
  rw [Nat.succ_lt_succ_iff]
  simp only [Fin.val_fin_lt]
  cases' n
  · simp only [Nat.succ_eq_add_one, not_lt_zero'] at *
  · apply pred'_lt_self (Fin.pos_of_ne_zero h2)
