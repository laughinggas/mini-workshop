import MiniWorkshop.chapter1

variable {n : ℕ} [NeZero n]

-- Try to put comments everywhere, the task is to understand what is happening in this file

/-- Neighbors of a point `i`. -/
def nbrs (i : Fin n) : Finset (Fin n) := {i + 1, i - 1}

/-- Interior of a set. -/
def int' (S : Finset (Fin n)) : Finset (Fin n) := Set.toFinset ({i | nbrs i ⊆ S})

/-- Boundary of a set. -/
def bdry (S : Finset (Fin n)) := S \ (int' (S))

-- don't prove this!
-- note that `Finset.univ` on a finite type `X` is the same as the full or "universal" set `X`.
lemma bdry_compl_Nonempty (S : Finset (Fin n)) (hS : S ≠ Finset.univ ∧ S.Nonempty) : (bdry Sᶜ).Nonempty := by sorry

variable (n)

-- We wish to extract an arbitrary element from a nonempty set. We do this by using `Exists.choose`.
/-- Defines the rules of the game, where a specific choice is made in every even
  turn (corresponding to the first player), and a random choice is made from the
  boundary for every odd turn (corresponding to the second player). -/
structure game' :=
(toFun : Fin (n + 1) → Fin (n + 1))
(rule_even : ∀ (i : Fin (n + 1)) (h1 : i.val.succ < n + 1) (h2 : Even i.val)
  (h3 : 0 < i.val), toFun i ∈ bdry (Finset.image toFun (Finset.Iic (i - 1)))ᶜ)
(nempty : ∀ (i : Fin (n + 1)) (h1 : i.val.succ < n + 1), (bdry (Finset.image toFun (Finset.Iic i))ᶜ).Nonempty)
(rule_odd : ∀ (i : Fin (n + 1)) (h1 : i.val.succ < n + 1) (h2 : Odd i.val) (h3 : 0 < i.val), toFun i = Exists.choose (nempty (i - 1) (sub_one_val_succ_lt h1 (by
  intro h
  rw [h] at h3
  simp at h3))))

-- We are now constructing an instance. This means that Lean will "remember" this property, so we don't need to keep mentioning it as a hypothesis.
-- What happens if you delete this instance?
-- used lemmas (in order): `Set.Finite.fintype`, `Set.finite_iff_bddAbove`, `mem_upperBounds`, `le_of_lt`
-- tactics that can be used include `rw`, `apply`, `refine'`, `simp` and `intros`
-- Note that `refine'` can be used to separate "joint" statements: for example, `∃ a, p a`; `p ∧ q`; `p ↔ q` (which is the same as `p → q ∧ q → p`).
-- Use Ctrl+click to look at definitions/lemmas
noncomputable local instance : Fintype ({i : ℕ | i ≠ 0 ∧ Even i ∧ i < n}) := by
  sorry

/-- Subset of peices eaten by first player. -/
noncomputable def first_player_share_at_level' (g : game' n) : Finset (Fin (n + 1)) :=
{g.toFun 0} ∪ Finset.biUnion (Set.toFinset ({i : ℕ | i ≠ 0 ∧ Even i ∧ i < n + 1})) (λ i => {g.toFun i})

/-- This function tells us the pizza piece picked up at a given time.
    It takes as input `k`, the piece picked up at time 0. At time `i + 1`,
    the piece picked up is a random choice from the boundary of the complement
    of the set of pieces picked up before time `i + 1`. -/
noncomputable
def req_fun' (k : Fin (n + 1)) : Fin (n + 1) → Fin (n + 1)
  | ⟨0, _⟩ => k
  | ⟨i + 1, hi⟩ =>
    if Even i then (bdry_compl_Nonempty (Finset.biUnion Finset.univ (λ j : Fin (i + 1) => {req_fun' k j})) ⟨(Finset.card_lt_iff_ne_univ _).1
      (lt_of_le_of_lt Finset.card_biUnion_le (by simp only [Set.toFinset_singleton, Finset.card_singleton, Finset.sum_const, Finset.card_fin,
          smul_eq_mul, mul_one, Fintype.card_fin, hi])),
        Finset.Nonempty.biUnion Finset.univ_nonempty (λ x _ => by simp only [Set.toFinset_singleton,
          Finset.singleton_nonempty])⟩).choose else if (req_fun' k i) + 1 ∈ Finset.biUnion Finset.univ (λ j : Fin i => {req_fun' k j}) ∧ (req_fun' k i) - 1 ∈ (Finset.biUnion Finset.univ (λ j : Fin i => {req_fun' k j}))ᶜ then (req_fun' k i) - 1
            else (if (req_fun' k i) - 1 ∈ Finset.biUnion Finset.univ (λ j : Fin i => {req_fun' k j}) ∧ (req_fun' k i) + 1 ∈ (Finset.biUnion Finset.univ (λ j : Fin i => {req_fun' k j}))ᶜ then (req_fun' k i) + 1 else
            (bdry_compl_Nonempty (Finset.biUnion Finset.univ (λ j : Fin (i + 1) => {req_fun' k j})) ⟨(Finset.card_lt_iff_ne_univ _).1
      (lt_of_le_of_lt Finset.card_biUnion_le (by simp only [Set.toFinset_singleton, Finset.card_singleton, Finset.sum_const, Finset.card_fin,
          smul_eq_mul, mul_one, Fintype.card_fin, hi])),
        Finset.Nonempty.biUnion Finset.univ_nonempty (λ x _ => by simp only [Set.toFinset_singleton,
          Finset.singleton_nonempty])⟩).choose)
    decreasing_by
      all_goals simp_wf
      all_goals rw [Fin.lt_def]
      all_goals simp [Fin.val_natCast, Nat.mod_eq_of_lt (lt_trans (Fin.is_lt _) hi), Fin.is_lt _, Nat.mod_eq_of_lt (lt_trans Nat.le.refl hi), Nat.mod_eq_of_lt (lt_trans (Fin.is_lt _) (lt_trans Nat.le.refl hi)), lt_trans (Fin.is_lt _) Nat.le.refl]

noncomputable
def S (k : Fin (n + 1)) (i : ℕ) : Finset (Fin (n + 1)) := Finset.biUnion Finset.univ (λ j : Fin (i + 1) => {req_fun' n k j})

/-- Constructing a game where only the first point is given, and the others are chosen randomly. -/
noncomputable
def construct_game' (k : Fin (n + 1)) : game' n :=
⟨λ j => req_fun' n k j,
  λ i h1 h2 h3 => by
    sorry,
  λ i h1 => by
    apply bdry_compl_Nonempty
    simp only [ne_eq, Finset.image_nonempty, Finset.nonempty_Iic, and_true]
    intro h
    have hcard : (Finset.image (fun j ↦ req_fun' n k j) (Finset.Iic i)).card = (Finset.univ : Finset (Fin (n + 1))).card := by
      rw [h]
    simp only [Finset.card_fin] at hcard
    have h2 := @Finset.card_image_le _ _ (Finset.Iic i) (λ (j : Fin (n + 1)) ↦ req_fun' n k j) _
    rw [hcard, Fin.card_Iic] at h2
    have : (n + 1) < (n + 1) := lt_of_le_of_lt h2 h1
    simp only [Nat.succ_eq_add_one, add_lt_add_iff_right, add_le_add_iff_right,
      lt_self_iff_false] at *,
  λ i h1 h2 h3 => by
    sorry ⟩

theorem main (hn : Odd n) (f : PMF (Fin (n + 1))) : ∃ g : game' n, (PMF.toMeasure f) (first_player_share_at_level' n g) ≥ 1/2 := --(f : Finset (Fin n) → Set.Icc (0 : ℝ) 1)
by sorry
