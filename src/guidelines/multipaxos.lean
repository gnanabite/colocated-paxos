import data.finset.basic

import guidelines.protocol
import guidelines.definitions
import guidelines.requirements
import guidelines.proof

namespace multipaxos

structure state_defs (sys_state_t pid_t slot_t ballot_t value_t : Type) :=
  (curr : sys_state_t → pid_t → ballot_t)
  (stored : sys_state_t → pid_t → slot_t → option (proposal ballot_t value_t))
  (proposed : sys_state_t → slot_t → ballot_t → value_t → Prop)
  (voted : sys_state_t → pid_t → slot_t → ballot_t → Prop)
  (quorum : finset pid_t → Prop)

namespace state_defs

variables {sys_state_t pid_t slot_t ballot_t value_t : Type}

def chosen_ballot
  (defs : state_defs sys_state_t pid_t slot_t ballot_t value_t) :
    sys_state_t → slot_t → ballot_t → Prop :=
  (λ state slot ballot,
    ∃ q : finset pid_t, defs.quorum q ∧
      ∀ voter ∈ q, defs.voted state voter slot ballot)

def chosen
  (defs : state_defs sys_state_t pid_t slot_t ballot_t value_t) :
    sys_state_t → slot_t → value_t → Prop :=
  (λ state slot value,
    ∃ ballot, defs.chosen_ballot state slot ballot ∧ defs.proposed state slot ballot value)

end state_defs

variables {sys_state_t pid_t slot_t ballot_t value_t : Type}

def state_with_past_intervals
  (defs : state_defs sys_state_t pid_t slot_t ballot_t value_t)
  (proto : protocol sys_state_t) : protocol (sys_state_t × (pid_t → slot_t → set (interval ballot_t value_t))) :=
{ init := (λ hist_state, proto.init hist_state.fst ∧
  (∀ p s, hist_state.snd p s =
        {{upper := defs.curr hist_state.fst p, lower := defs.stored hist_state.fst p s}})),
  next := (λ fst_state snd_state, proto.next fst_state.fst snd_state.fst ∧
  (∀ p s, snd_state.snd p s = fst_state.snd p s ∪
          {{upper := defs.curr snd_state.fst p, lower := defs.stored snd_state.fst p s}})) }

variables [linear_order ballot_t] [decidable_eq pid_t]

structure proto_constraints
  (proto : protocol sys_state_t)
  (defs : state_defs sys_state_t pid_t slot_t ballot_t value_t) :=
  (quorums_intersect :
    ∀ q₁ q₂, defs.quorum q₁ → defs.quorum q₂ → (q₁ ∩ q₂).nonempty)
  (none_proposed_at_init :
    ∀ state slot ballot value, proto.init state → ¬defs.proposed state slot ballot value)
  (proposed_stable :
    ∀ slot ballot value,
      proto.stable (λ state, defs.proposed state slot ballot value))
  (proposals_unique :
    ∀ slot ballot v₁ v₂,
      proto.invariant (λ state,
        defs.proposed state slot ballot v₁ → defs.proposed state slot ballot v₂ → v₁ = v₂))
  (at_most_one_proposal_per_slot_per_step :
    ∀ slot s',
      proto.invariant (λ state,
        proto.next state s' →
          ∃ b v, ∀ bal val, defs.proposed s' slot bal val →
                 (defs.proposed state slot bal val ∨ (bal = b ∧ val = v))))
  (curr_increases :
    ∀ process s',
      proto.invariant (λ state,
        proto.next state s' → defs.curr state process ≤ defs.curr s' process))
  (stored_ballot_increases :
    ∀ process slot prop s',
      proto.invariant (λ state,
        proto.next state s' →
          defs.stored state process slot = some prop →
            ∃ prop', defs.stored s' process slot = some prop' ∧ prop.b ≤ prop'.b))
  (stored_is_proposed :
    ∀ process slot prop,
      proto.invariant (λ state,
        defs.stored state process slot = some prop →
          defs.proposed state slot prop.b prop.v))
  (new_votes_ge_curr_ballot :
    ∀ process slot ballot s',
      proto.invariant (λ state,
        proto.next state s' →
          defs.voted s' process slot ballot →
            defs.voted state process slot ballot ∨ defs.curr state process ≤ ballot))
  (voted_imp_proposed :
    ∀ process slot ballot,
      proto.invariant (λ state,
        defs.voted state process slot ballot →
          ∃ value, defs.proposed state slot ballot value))
  (voted_le_stored :
    ∀ process slot ballot,
      proto.invariant (λ state,
        defs.voted state process slot ballot →
          ∃ prop, defs.stored state process slot = some prop ∧ ballot ≤ prop.b))
  (majority_have_upper_interval_if_proposed :
    ∀ slot ballot value,
      (state_with_past_intervals defs proto).invariant (λ state,
        defs.proposed state.fst slot ballot value →
        ∃ (q : finset pid_t)
             (promised_prop : pid_t → option (proposal ballot_t value_t)),
          defs.quorum q ∧
          (∀ (a ∈ q),
            {interval . lower := (promised_prop a), upper := ballot} ∈ state.snd a slot) ∧
          (∀ (a ∈ q) prop_a, promised_prop a = some prop_a → prop_a.b < ballot) ∧
          ((∀ (a ∈ q), promised_prop a = none) ∨
           (∃ (a ∈ q) prop_a,
             promised_prop a = some prop_a ∧
             (∀ (a' ∈ q) prop_a', promised_prop a' = some prop_a' → prop_a'.b ≤ prop_a.b) ∧
             prop_a.v = value))))

def safety (proto : protocol sys_state_t)
  (defs : state_defs sys_state_t pid_t slot_t ballot_t value_t)
  := proto.invariant (λ state, (∀ slot v v', defs.chosen state slot v → defs.chosen state slot v' → v = v'))

end multipaxos


variables {sys_state_t pid_t slot_t ballot_t value_t : Type}
          [linear_order ballot_t] [decidable_eq pid_t]
          {proto : protocol sys_state_t}
          {defs : multipaxos.state_defs sys_state_t pid_t slot_t ballot_t value_t}

theorem constraints_give_safety : multipaxos.proto_constraints proto defs → multipaxos.safety proto defs :=
begin
intro multipaxos_constraints_met,
suffices key : ∀ slot, proto.invariant (λ state, (∀ v v', defs.chosen state slot v → defs.chosen state slot v' → v = v')),
by { intros state reachable slot, exact key slot state reachable },
intro slot,
let slot_instance_defs : paxos_defs sys_state_t pid_t ballot_t value_t :=
{ curr := λ state p, defs.curr state p,
  stored := λ state p, defs.stored state p slot,
  proposed := λ state ballot value, defs.proposed state slot ballot value,
  voted := λ state p ballot, defs.voted state p slot ballot,
  quorum := defs.quorum },
let slot_instance_reqs_sat : requirements proto slot_instance_defs :=
{ quorums_intersect := multipaxos_constraints_met.quorums_intersect,
  none_proposed_at_init := λ state ballot value is_init,
    multipaxos_constraints_met.none_proposed_at_init state slot ballot value is_init,
  proposed_stable := λ ballot value,
    multipaxos_constraints_met.proposed_stable slot ballot value,
  proposals_unique := λ ballot v₁ v₂,
    multipaxos_constraints_met.proposals_unique slot ballot v₁ v₂,
  at_most_one_proposal_per_step := λ s',
    multipaxos_constraints_met.at_most_one_proposal_per_slot_per_step slot s',
  curr_increases := multipaxos_constraints_met.curr_increases,
  stored_ballot_increases := λ process prop s',
    multipaxos_constraints_met.stored_ballot_increases process slot prop s',
  stored_is_proposed := λ process prop,
    multipaxos_constraints_met.stored_is_proposed process slot prop,
  new_votes_ge_curr_ballot := λ process ballot s',
    multipaxos_constraints_met.new_votes_ge_curr_ballot process slot ballot s',
  voted_imp_proposed := λ process ballot,
    multipaxos_constraints_met.voted_imp_proposed process slot ballot,
  voted_le_stored := λ process ballot,
    multipaxos_constraints_met.voted_le_stored process slot ballot,
  majority_have_upper_interval_if_proposed := by {
    suffices key : (proto_with_intervals_recorded slot_instance_defs proto).invariant
      (λ restricted_state,
        ∃ full_state, (multipaxos.state_with_past_intervals defs proto).reachable full_state ∧
                      full_state.fst = restricted_state.fst ∧
                      restricted_state.snd = λ p, full_state.snd p slot),
    by {
      intros ballot value state reachable,
      rcases key state reachable
        with ⟨lift_state, lift_reachable, lift_state_is_lift, lift_snd_restriction_gives_snd⟩,
      rw lift_snd_restriction_gives_snd, rw ← lift_state_is_lift,
      exact multipaxos_constraints_met.majority_have_upper_interval_if_proposed
        slot ballot value lift_state lift_reachable,
    },
    rw protocol.prove_invariant,
    split,
    { intros s is_init,
      use ⟨s.fst, (λ p slot, {{upper := defs.curr s.fst p, lower := defs.stored s.fst p slot}})⟩,
      split,
      { exact ⟨0, is_init.left, by { intros p slot, refl }⟩ },
      split,
      { refl },
      rw function.funext_iff,
      exact is_init.right },
    rintros start start_reachable next ⟨lift_start, lift_reachable, lift_start_is_lift, lift_snd_restriction_gives_snd⟩ next_reachable,
    use ⟨next.fst, λ p s, lift_start.snd p s ∪
                       {{upper := defs.curr next.fst p, lower := defs.stored next.fst p s}}⟩,
    split,
    { rcases lift_reachable with ⟨n, hn⟩,
      exact ⟨n.succ, lift_start, hn, by { rw lift_start_is_lift, exact next_reachable.left },
            by { intros p s, refl }⟩ },
    split,
    { refl },
    rw function.funext_iff, intro p,
    rw next_reachable.right p, unfold prod.snd,
    rw lift_snd_restriction_gives_snd
  } },
exact requirements_give_safety slot_instance_reqs_sat
end
