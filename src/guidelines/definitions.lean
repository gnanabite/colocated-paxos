import data.finset.basic

import guidelines.protocol

structure proposal (ballot_t value_t : Type) := (b : ballot_t) (v : value_t)

structure paxos_defs (sys_state_t pid_t ballot_t value_t : Type) :=
  (curr : sys_state_t → pid_t → ballot_t)
  (stored : sys_state_t → pid_t → option (proposal ballot_t value_t))
  (proposed : sys_state_t → ballot_t → value_t → Prop)
  (voted : sys_state_t → pid_t → ballot_t → Prop)
  (quorum : finset pid_t → Prop)

namespace paxos_defs

variables {sys_state_t pid_t ballot_t value_t : Type}

def chosen_ballot
  (defs : paxos_defs sys_state_t pid_t ballot_t value_t) :
    sys_state_t → ballot_t → Prop :=
  (λ state ballot,
    ∃ q : finset pid_t, defs.quorum q ∧
      ∀ voter ∈ q, defs.voted state voter ballot)

def choosable [linear_order ballot_t]
  (defs : paxos_defs sys_state_t pid_t ballot_t value_t) :
    sys_state_t → ballot_t → Prop :=
  (λ state ballot,
    ∃ q : finset pid_t, defs.quorum q ∧
      ∀ voter ∈ q,
        defs.voted state voter ballot ∨ defs.curr state voter ≤ ballot)

def chosen
  (defs : paxos_defs sys_state_t pid_t ballot_t value_t) :
    sys_state_t → value_t → Prop :=
  (λ state value,
    ∃ ballot, defs.chosen_ballot state ballot ∧ defs.proposed state ballot value)

lemma chosen_imp_choosable {s : sys_state_t} {b : ballot_t} [linear_order ballot_t]
  (defs : paxos_defs sys_state_t pid_t ballot_t value_t) :
  defs.chosen_ballot s b → defs.choosable s b :=
begin
rintros ⟨q, q_quorum, q_voted⟩,
exact ⟨q, q_quorum,
  by {intros voter voter_in_q, left, exact q_voted voter voter_in_q }⟩
end

end paxos_defs

structure interval (ballot_t value_t : Type) :=
  (upper : ballot_t) (lower : option (proposal ballot_t value_t))

variables {sys_state_t pid_t ballot_t value_t : Type}

def proto_with_intervals_recorded
  (defs : paxos_defs sys_state_t pid_t ballot_t value_t)
  (proto : protocol sys_state_t) : protocol (sys_state_t × (pid_t → set (interval ballot_t value_t))) :=
{ init := (λ hist_state, proto.init hist_state.fst ∧
  (∀ p, hist_state.snd p =
        {{upper := defs.curr hist_state.fst p, lower := defs.stored hist_state.fst p}})),
  next := (λ fst_state snd_state, proto.next fst_state.fst snd_state.fst ∧
  (∀ p, snd_state.snd p = fst_state.snd p ∪
        {{upper := defs.curr snd_state.fst p, lower := defs.stored snd_state.fst p}})) }

lemma reachable_implies_reachable_in_proto_with_intervals_recorded
  (defs : paxos_defs sys_state_t pid_t ballot_t value_t)
  (proto : protocol sys_state_t) :
  ∀ s, proto.reachable s → ∃ lift_s, (proto_with_intervals_recorded defs proto).reachable lift_s ∧ lift_s.fst = s :=
begin
suffices : ∀ n s,
  proto.reachable_in n s →
  ∃ lift_s, (proto_with_intervals_recorded defs proto).reachable lift_s ∧ lift_s.fst = s,
by { rintros s ⟨n, hn⟩, exact this n s hn },
intro n,
induction n with k hk,
{ intros s hs,
  use ⟨s, (λ p, {{ upper := defs.curr s p, lower := defs.stored s p}})⟩,
  use ⟨0, hs, by {intro p, refl }⟩ },
rintros s ⟨u, u_reach_in_k, u_next_s⟩,
specialize hk u u_reach_in_k,
rcases hk with ⟨lift_u, ⟨j, hj⟩, lift_u_has_u⟩,
use ⟨s, (λ p, lift_u.snd p ∪ {{ upper := defs.curr s p, lower := defs.stored s p}})⟩,
split,
{ use [j.succ, lift_u, hj],
  split,
  { rw lift_u_has_u, exact u_next_s },
  intros p, refl },
refl
end

lemma reachable_in_proto_with_intervals_recorded_implies_first_reachable
  (defs : paxos_defs sys_state_t pid_t ballot_t value_t)
  (proto : protocol sys_state_t) :
  ∀ lift_s, (proto_with_intervals_recorded defs proto).reachable lift_s →
    proto.reachable lift_s.fst :=
begin
suffices : ∀ n lift_s,
  (proto_with_intervals_recorded defs proto).reachable_in n lift_s →
  proto.reachable lift_s.fst,
by { rintros lift_s ⟨n, hn⟩, exact this n lift_s hn },
intro n,
induction n with k hk,
{ intros s hs,
  use ⟨0, hs.left⟩ },
rintros lift_s ⟨lift_u, lift_u_reach_in_k, lift_u_next_lift_s⟩,
specialize hk lift_u lift_u_reach_in_k,
rcases hk with ⟨j, hj⟩,
exact ⟨j.succ, lift_u.fst, hj, lift_u_next_lift_s.left⟩
end
