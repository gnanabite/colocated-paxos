import tactic.basic

-- A ballot is a pair consisting a round number and a process
-- identifier. Process identifiers must be linearly ordered. Under this
-- constraint, ballots are totally ordered.
--
-- example: "fin 3" is a valid pid_t, but bool is not.
structure ballot (pid_t : Type) [linear_order pid_t] :=
  (round : ℕ) (address : pid_t)

namespace ballot

variables {pid_t : Type}  [linear_order pid_t]

-- Ballots are ordered lexicographically, and this is a total order.
def le : ballot pid_t → ballot pid_t → Prop :=
  λ b₁ b₂, b₁.round < b₂.round ∨ (b₁.round = b₂.round ∧ b₁.address ≤ b₂.address)

instance has_le : has_le (ballot pid_t) := ⟨le⟩

def lt  : ballot pid_t → ballot pid_t → Prop :=
  λ b₁ b₂, b₁.round < b₂.round ∨ (b₁.round = b₂.round ∧ b₁.address < b₂.address)

instance has_lt : has_lt (ballot pid_t) := ⟨lt⟩

lemma le_refl (b : ballot pid_t) : b ≤ b :=
begin
cases b,
right,
split; refl
end

lemma le_trans (n m k : ballot pid_t) : n ≤ m → m ≤ k → n ≤ k :=
begin
intros h1 h2,
cases n,
cases m,
cases k,
cases h1 with round1_lt address1_lt;
cases h2 with round2_lt address2_lt,
{ left, exact lt_trans round1_lt round2_lt },
{ left, rw ← address2_lt.left, exact round1_lt },
{ left, rw address1_lt.left, exact round2_lt },
right,
split,
{ exact eq.trans address1_lt.left address2_lt.left },
exact le_trans address1_lt.right address2_lt.right
end

lemma lt_iff_le_not_le (m n : ballot pid_t) : m < n ↔ (m ≤ n ∧ ¬ n ≤ m) :=
begin
cases m, cases n,
split,
{ intro hyp_less,
  split,
  { cases hyp_less with rounds addresses,
    { exact or.inl rounds },
    { exact or.inr ⟨addresses.left, le_of_lt addresses.right⟩ }},
  intro hyp_ge,
  cases hyp_less with rounds_less pids_less;
  cases hyp_ge with rounds_ge pids_ge,
  { exact lt_asymm rounds_less rounds_ge },
  { rw pids_ge.left at rounds_less,
    exact lt_irrefl m_round rounds_less },
  { rw pids_less.left at rounds_ge,
    exact lt_irrefl n_round rounds_ge },
  exact lt_irrefl m_address (lt_of_lt_of_le pids_less.right pids_ge.right)
  },
rintros ⟨hyp_le, hyp_not_le⟩,
cases hyp_le with rounds pids,
{ exact or.inl rounds },
suffices key : m_address ≠ n_address,
by { exact or.inr ⟨pids.left, lt_of_le_of_ne pids.right key⟩ },
intro pids_equal,
apply hyp_not_le,
right,
split,
{ exact eq.symm pids.left },
exact le_of_eq (eq.symm pids_equal)
end

lemma le_antisymm (n m : ballot pid_t) : n ≤ m → m ≤ n → n = m :=
begin
intros h1 h2,
cases n,
cases m,
suffices key : n_round = m_round ∧ n_address = m_address,
by { rwa [key.left, key.right] },
have rounds_eq : n_round = m_round,
by {
  apply le_antisymm,
  { cases h1,
    { exact le_of_lt h1 },
    exact le_of_eq h1.left },
  cases h2,
  { exact le_of_lt h2 },
  exact le_of_eq h2.left
},
split,
{ exact rounds_eq },
apply le_antisymm,
{ cases h1,
  { exact (ne_of_lt h1 rounds_eq).elim },
  exact h1.right },
cases h2,
{ exact (ne_of_lt h2 (eq.symm rounds_eq)).elim },
exact h2.right
end

lemma le_total (n m : ballot pid_t) : n ≤ m ∨ m ≤ n :=
begin
cases n,
cases m,
cases lt_trichotomy n_round m_round with lt ge,
{ exact or.inl (or.inl lt) },
cases ge with equal gt,
{ cases le_total n_address m_address with le ge,
  { exact or.inl (or.inr ⟨equal, le⟩) },
  exact or.inr (or.inr ⟨eq.symm equal, ge⟩) },
exact or.inr (or.inl gt),
end

instance decidable_le : ∀ b₁ b₂ : ballot pid_t, decidable (b₁ ≤ b₂) :=
begin
intros b₁ b₂,
exact or.decidable
end

instance decidable_eq : decidable_eq (ballot pid_t) :=
begin
intros b₁ b₂,
suffices key : decidable (b₁.round = b₂.round ∧ b₁.address = b₂.address),
by {
  apply decidable_of_decidable_of_iff key,
  split,
  { rintros ⟨rounds_eq, addresses_eq⟩,
    cases b₁,
    cases b₂,
    unfold ballot.round at rounds_eq,
    unfold ballot.address at addresses_eq,
    rwa [rounds_eq, addresses_eq] },
  intro hyp,
  rw hyp,
  exact ⟨eq.refl b₂.round, eq.refl b₂.address⟩
},
apply_instance
end

instance decidable_lt : ∀ b₁ b₂ : ballot pid_t, decidable (b₁ < b₂) :=
begin
intros b₁ b₂,
exact or.decidable
end

instance linear_order : linear_order (ballot pid_t) :=
{ le := ballot.le,
  le_refl := ballot.le_refl,
  le_trans := ballot.le_trans,
  le_antisymm := ballot.le_antisymm,
  le_total := ballot.le_total,
  lt := ballot.lt,
  lt_iff_le_not_le := ballot.lt_iff_le_not_le,
  decidable_lt := ballot.decidable_lt,
  decidable_eq := ballot.decidable_eq,
  decidable_le := ballot.decidable_le }


-- For any process id p and ballot b, there is a ballot belonging to p which is
-- strictly greater than b. Specifically, `next p b` is such a ballot.
--
-- NOTE(gnanabit): we could keep the round number the same if the other pid is
-- less than ours, but this is a bit easier to work with.
def next (p : pid_t) : ballot pid_t → ballot pid_t :=
  λ b, { round := b.round.succ, address := b.address }

theorem next_larger :
  ∀ (p : pid_t) (b : ballot pid_t), b < next p b :=
begin
intros p b,
left,
exact nat.lt_succ_self b.round
end

end ballot
