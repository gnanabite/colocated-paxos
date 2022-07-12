import implementation.spec.ballot

-- A proposal is a pair of a ballot with a value.
structure proposal (pid_t : Type) [linear_order pid_t] (value_t : Type) : Type :=
  (bal : ballot pid_t) (val : value_t)

namespace proposal

variables {pid_t : Type} [linear_order pid_t] {value_t : Type}

-- When merging proposals, we take the one with higher ballot number.
def merge : option (proposal pid_t value_t) → option (proposal pid_t value_t)
                                            → option (proposal pid_t value_t)
| none      none      := none
| (some p₁) none      := some p₁
| none      (some p₂) := some p₂
| (some p₁) (some p₂) := if (p₁.bal < p₂.bal) then some p₂ else some p₁

-- Gets the proposed value from an option or provides the default if no value is
-- present.
def value_or_default : option (proposal pid_t value_t) → value_t → value_t
| none     := (λ v, v)
| (some p) := (λ _, p.val)

-- The result of a merge with a some on the lhs is at least as large as the lhs.
lemma merge_ballot_ge_left
  (p_left : proposal pid_t value_t) (p_or : option (proposal pid_t value_t)) :
  ∃ res, merge (some p_left) p_or = some res ∧ res.bal ≥ p_left.bal :=
begin
cases p_or,
  case none : {
    exact ⟨p_left, by refl, le_refl p_left.bal⟩
  },
  case some : p_right {
    unfold merge,
    cases decidable.em (p_left.bal < p_right.bal),
    { rw if_pos h,
      exact ⟨p_right, by refl, le_of_lt h⟩ },
    rw if_neg h,
    exact ⟨p_left, by refl, le_refl p_left.bal⟩
  }
end

-- The result of a merge with a some on the rhs is at least as large as the rhs.
lemma merge_ballot_ge_right
  (p_or : option (proposal pid_t value_t)) (p_right : proposal pid_t value_t) :
  ∃ res, merge p_or (some p_right) = some res ∧ res.bal ≥ p_right.bal :=
begin
cases p_or,
  case none : {
    exact ⟨p_right, by refl, le_refl p_right.bal⟩
  },
  case some : p_left {
    unfold merge,
    cases decidable.em (p_left.bal < p_right.bal),
    { rw if_pos h,
      exact ⟨p_right, by refl, le_refl p_right.bal⟩ },
    rw if_neg h,
    exact ⟨p_left, by refl, le_of_not_lt h⟩
  }
end

-- Merging two proposals results in either the left one or the right one.
lemma merge_is_one_of (p_or₁ p_or₂ : option (proposal pid_t value_t)) :
  merge p_or₁ p_or₂ = p_or₁ ∨ merge p_or₁ p_or₂ = p_or₂ :=
begin
cases p_or₁,
  case none : {
    cases p_or₂,
      case none : { unfold merge, left, refl },
      case some : p₂ { unfold merge, right, refl }
  },
  case some : p₁ {
    cases p_or₂,
      case none : { unfold merge, left, refl },
      case some : p₂ {
        unfold merge,
        cases decidable.em (p₁.bal < p₂.bal),
        { right, rw if_pos h },
        left, rw if_neg h
      }
  },
end

end proposal
