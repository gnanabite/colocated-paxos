import data.finset.basic
import data.fintype.basic

-- A decidable predicate on finsets has the quorum assumption if, whenever
-- two finsets satisfy the predicate, they intersect.
class quorum_assumption {pid_t : Type} [decidable_eq pid_t]
                        (p : finset pid_t → Prop) [decidable_pred p] :=
  (intersect : (∀ (q1 q2 : finset pid_t), p q1 → p q2 → (q1 ∩ q2).nonempty))

-- For any pid_t which is a fintype, the majority predicate satisfies the quorum
-- assumption.
def majority (pid_t : Type) [fintype pid_t] (q: finset pid_t) :=
  q.card + q.card > fintype.card pid_t

variables {pid_t : Type} [fintype pid_t] [decidable_eq pid_t]

instance : decidable_pred (majority pid_t) :=
begin
intro q,
unfold majority,
exact nat.decidable_lt (fintype.card pid_t) (q.card + q.card)
end

lemma majorities_intersect :
  ∀ (q1 q2 : finset pid_t), majority pid_t q1 → majority pid_t q2 → (q1 ∩ q2).nonempty :=
begin
intros q1 q2 h1 h2,
apply finset.card_pos.mp,
unfold majority at h1 h2,
have card_sum_gt : q1.card + q2.card > fintype.card pid_t,
by {
  cases decidable.em (q1.card < q2.card),
  { calc q1.card + q2.card > q1.card + q1.card : nat.add_lt_add_left h q1.card
                       ... > fintype.card pid_t : h1 },
  rw not_lt at h,
  calc q1.card + q2.card ≥ q2.card + q2.card : nat.add_le_add_right h q2.card
                     ... > fintype.card pid_t : h2
},
have card_union_le : (q1 ∪ q2).card ≤ fintype.card pid_t,
by {
  rw ← finset.card_univ,
  apply finset.card_le_of_subset,
  intros x unused,
  exact finset.mem_univ x
},
clear h1 h2,
have inclusion_exclusion := finset.card_union_add_card_inter q1 q2,
have key :=
  calc fintype.card pid_t + 0 = fintype.card pid_t : nat.add_zero (fintype.card pid_t)
                          ... < q1.card + q2.card : card_sum_gt
                          ... = (q1 ∪ q2).card + (q1 ∩ q2).card : eq.symm inclusion_exclusion
                          ... ≤ fintype.card pid_t + (q1 ∩ q2).card :
                                             nat.add_le_add_right card_union_le (q1 ∩ q2).card,
exact lt_of_add_lt_add_left key
end

instance : quorum_assumption (majority pid_t) := { intersect := majorities_intersect }
