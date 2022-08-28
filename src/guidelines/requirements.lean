import data.fintype.basic
import data.finset.basic

import guidelines.definitions
import guidelines.protocol

variables {sys_state_t pid_t ballot_t value_t : Type}
  [linear_order ballot_t] [decidable_eq pid_t]

structure requirements
  (proto : protocol sys_state_t)
  (defs : paxos_defs sys_state_t pid_t ballot_t value_t) :=
  (quorums_intersect :
    ∀ q₁ q₂, defs.quorum q₁ → defs.quorum q₂ → (q₁ ∩ q₂).nonempty)
  (none_proposed_at_init :
    ∀ state ballot value, proto.init state → ¬defs.proposed state ballot value)
  (proposed_stable :
    ∀ ballot value,
      proto.stable (λ state, defs.proposed state ballot value))
  (proposals_unique :
    ∀ ballot v₁ v₂,
      proto.invariant (λ state,
        defs.proposed state ballot v₁ → defs.proposed state ballot v₂ → v₁ = v₂))
  (at_most_one_proposal_per_step :
    ∀ s',
      proto.invariant (λ state,
        proto.next state s' →
          ∃ b v, ∀ bal val, defs.proposed s' bal val →
                 (defs.proposed state bal val ∨ (bal = b ∧ val = v))))
  (curr_increases :
    ∀ process s',
      proto.invariant (λ state,
        proto.next state s' → defs.curr state process ≤ defs.curr s' process))
  (stored_ballot_increases :
    ∀ process prop s',
      proto.invariant (λ state,
        proto.next state s' →
          defs.stored state process = some prop →
            ∃ prop', defs.stored s' process = some prop' ∧ prop.b ≤ prop'.b))
  (stored_is_proposed :
    ∀ process prop,
      proto.invariant (λ state,
        defs.stored state process = some prop →
          defs.proposed state prop.b prop.v))
  (new_votes_ge_curr_ballot :
    ∀ process ballot s',
      proto.invariant (λ state,
        proto.next state s' →
          defs.voted s' process ballot →
            defs.voted state process ballot ∨ defs.curr state process ≤ ballot))
  (voted_imp_proposed :
    ∀ process ballot,
      proto.invariant (λ state,
        defs.voted state process ballot →
          ∃ value, defs.proposed state ballot value))
  (voted_le_stored :
    ∀ process ballot,
      proto.invariant (λ state,
        defs.voted state process ballot →
          ∃ prop, defs.stored state process = some prop ∧ ballot ≤ prop.b))
  (majority_have_upper_interval_if_proposed :
    ∀ ballot value,
      (proto_with_intervals_recorded defs proto).invariant (λ state,
        defs.proposed state.fst ballot value →
        ∃ (q : finset pid_t)
             (promised_prop : pid_t → option (proposal ballot_t value_t)),
          defs.quorum q ∧
          (∀ (a ∈ q),
            {interval . lower := (promised_prop a), upper := ballot} ∈ state.snd a) ∧
          (∀ (a ∈ q) prop_a, promised_prop a = some prop_a → prop_a.b < ballot) ∧
          ((∀ (a ∈ q), promised_prop a = none) ∨
           (∃ (a ∈ q) prop_a,
             promised_prop a = some prop_a ∧
             (∀ (a' ∈ q) prop_a', promised_prop a' = some prop_a' → prop_a'.b ≤ prop_a.b) ∧
             prop_a.v = value))))

namespace requirements

variables {proto : protocol sys_state_t} {defs : paxos_defs sys_state_t pid_t ballot_t value_t}

lemma none_stored_at_init (reqs_sat : requirements proto defs) :
    ∀ state process, proto.init state → defs.stored state process = none :=
begin
intros state process is_init,
have key : ∀ (prop : proposal ballot_t value_t), defs.stored state process = some prop
  → defs.proposed state prop.b prop.v,
by { intro prop, exact reqs_sat.stored_is_proposed process prop state ⟨0, is_init⟩ },
cases defs.stored state process with stored,
{ refl },
specialize key stored (by refl),
exact absurd key (reqs_sat.none_proposed_at_init state stored.b stored.v is_init)
end

lemma all_lower_proposed (reqs_sat : requirements proto defs) :
  ∀ process, (proto_with_intervals_recorded defs proto).invariant
    (λ state, ∀ (i ∈ state.snd process) prop,
      (interval.lower i) = some prop →
        defs.proposed state.fst prop.b prop.v) :=
begin
intro process, rw protocol.prove_invariant, split,
{ intros lift_s lift_s_init i i_is_start_interval prop i_lower_is_some, exfalso,
  cases lift_s_init with s_init init_intervals_is_singleton,
  specialize init_intervals_is_singleton process,
  rw init_intervals_is_singleton at i_is_start_interval,
  rw set.mem_singleton_iff at  i_is_start_interval,
  rw i_is_start_interval at i_lower_is_some,
  rw reqs_sat.none_stored_at_init lift_s.fst process s_init at i_lower_is_some,
  injection i_lower_is_some },
rintros u u_r w hu ⟨u₁_n_w₁, fact⟩ i i_in_w_history prop i_lower_is_prop,
rw fact process at i_in_w_history, cases i_in_w_history,
{ apply (λ goal, reqs_sat.proposed_stable prop.b prop.v u.fst w.fst goal u₁_n_w₁),
  exact hu i i_in_w_history prop i_lower_is_prop },
rw set.mem_singleton_iff at i_in_w_history, rw i_in_w_history at i_lower_is_prop,
have w_r : (proto_with_intervals_recorded defs proto).reachable w,
by { cases u_r with k hk, exact ⟨k.succ, u, hk, ⟨u₁_n_w₁, fact⟩⟩ },
exact reqs_sat.stored_is_proposed process prop w.fst
  (reachable_in_proto_with_intervals_recorded_implies_first_reachable defs proto w w_r)
  i_lower_is_prop
end

lemma all_upper_le_curr (reqs_sat : requirements proto defs) :
  ∀ process, (proto_with_intervals_recorded defs proto).invariant
    (λ state, ∀ (i ∈ state.snd process) b,
      (interval.upper i) = b → b ≤ defs.curr state.fst process) :=
begin
intro process, rw protocol.prove_invariant, split,
{ intros lift_s lift_s_init i i_is_start_interval b i_upper_eq_b,
  cases lift_s_init with s_init init_intervals_is_singleton,
  specialize init_intervals_is_singleton process,
  rw init_intervals_is_singleton at i_is_start_interval,
  rw set.mem_singleton_iff at  i_is_start_interval,
  rw i_is_start_interval at i_upper_eq_b,
  rw ← i_upper_eq_b },
rintros u u_r w hu ⟨u₁_n_w₁, fact⟩ i i_in_w_history b i_upper_eq_b,
rw fact process at i_in_w_history, cases i_in_w_history,
{ apply le_trans (hu i i_in_w_history b i_upper_eq_b),
  apply (λ goal, reqs_sat.curr_increases process w.fst u.fst goal u₁_n_w₁),
  exact reachable_in_proto_with_intervals_recorded_implies_first_reachable defs proto u u_r },
rw set.mem_singleton_iff at i_in_w_history, rw i_in_w_history at i_upper_eq_b,
rw ← i_upper_eq_b
end

lemma none_voted_in_interval (reqs_sat : requirements proto defs) :
  ∀ process ballot, (proto_with_intervals_recorded defs proto).invariant
    (λ state, ∀ i ∈ state.snd process, defs.voted state.fst process ballot →
      (∃ prop, interval.lower i = some prop ∧ ballot ≤ prop.b) ∨ i.upper ≤ ballot)
  :=
begin
intros process ballot, rw protocol.prove_invariant, split,
{ intros lift_s lift_s_init i i_first_interval process_voted, exfalso,
  rcases reqs_sat.voted_imp_proposed process ballot lift_s.fst
    ⟨0, lift_s_init.left⟩ process_voted with ⟨value, bal_val_proposed⟩,
  exact reqs_sat.none_proposed_at_init lift_s.fst ballot value lift_s_init.left
    bal_val_proposed },
intros lift_u lift_u_reachable lift_w h_lift_u lift_u_next_lift_w i
  i_in_history process_voted,
rw lift_u_next_lift_w.right process at i_in_history,
have already_voted_or_new_vote := reqs_sat.new_votes_ge_curr_ballot
  process ballot lift_w.fst lift_u.fst
  (reachable_in_proto_with_intervals_recorded_implies_first_reachable
    defs proto lift_u lift_u_reachable)
  lift_u_next_lift_w.left process_voted,
cases i_in_history; cases already_voted_or_new_vote with already_voted new_vote,
{ exact h_lift_u i i_in_history already_voted },
{ right, exact le_trans
  (reqs_sat.all_upper_le_curr process lift_u lift_u_reachable i
    i_in_history i.upper (by refl)) new_vote },
{ left, rw set.mem_singleton_iff at i_in_history, rw i_in_history,
  rcases reqs_sat.voted_le_stored process ballot lift_u.fst
    (reachable_in_proto_with_intervals_recorded_implies_first_reachable
      defs proto lift_u lift_u_reachable) already_voted
    with ⟨prop_u, stored_at_u, ballot_le_stored_u⟩,
  rcases reqs_sat.stored_ballot_increases process prop_u lift_w.fst lift_u.fst
    (reachable_in_proto_with_intervals_recorded_implies_first_reachable
      defs proto lift_u lift_u_reachable) lift_u_next_lift_w.left stored_at_u
    with ⟨prop_w, stored_at_w, ballot_le_stored_w⟩,
  exact ⟨prop_w, stored_at_w, le_trans ballot_le_stored_u ballot_le_stored_w⟩ },
left, rw set.mem_singleton_iff at i_in_history, rw i_in_history,
apply (λ goal, reqs_sat.voted_le_stored process ballot lift_w.fst goal process_voted),
rcases reachable_in_proto_with_intervals_recorded_implies_first_reachable
      defs proto lift_u lift_u_reachable with ⟨k, hk⟩,
exact ⟨k.succ, lift_u.fst, hk, lift_u_next_lift_w.left⟩
end

end requirements
