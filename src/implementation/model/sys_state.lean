import implementation.model.envelope
import implementation.model.protocol
import tactic.basic
import data.set.basic

-- A sys_state contains both the state of all processes and the set of messages
-- sent by each process.
structure sys_state (pid_t pstate_t msg_t : Type)
  [protocol pid_t pstate_t msg_t] : Type :=
  (procs : pid_t → pstate_t) (network : pid_t → set(envelope pid_t msg_t))

namespace sys_state

variables {pid_t pstate_t msg_t : Type} [protocol pid_t pstate_t msg_t]

-- is_initial states that the system state matches the initial state specified
-- by the protocol.
def is_initial (s : sys_state pid_t pstate_t msg_t) : Prop :=
  ∀ p : pid_t, protocol.init p = (s.procs p, s.network p)

-- possible_next states that we can reach the state `after` from the state
-- `before` by delivering an envelope's message to one of the processes that may
-- receive the envelope. The state and network of the receiver are updated
-- accordingly, and all other states/networks are unchanged.
def possible_next (before after : sys_state pid_t pstate_t msg_t) : Prop :=
  ∃ (receiver sender : pid_t) (e ∈ before.network sender),
      envelope.deliverable_to e receiver
    ∧ after.procs receiver = (protocol.handler receiver (before.procs receiver) (envelope.msg e) sender).fst
    ∧ after.network receiver = before.network receiver ∪ (protocol.handler receiver (before.procs receiver) (envelope.msg e) sender).snd
    ∧ (∀ (p ≠ receiver), after.procs p = before.procs p)
    ∧ (∀ (p ≠ receiver), after.network p = before.network p)

lemma eq_iff_fields_eq {s1 s2 : sys_state pid_t pstate_t msg_t} :
  s1 = s2 ↔ (∀ (p : pid_t), s1.procs p  = s2.procs p) ∧
            (∀ (p : pid_t), s1.network p = s2.network p) :=
begin
split,
{ intro identical,
  rw identical,
  split; intro p; refl },
cases s1; cases s2;
intro both_eq,
unfold sys_state.procs sys_state.network at both_eq,
rwa [ (show s1_procs = s2_procs, by exact function.funext_iff.mpr both_eq.left),
      (show s1_network = s2_network, by exact function.funext_iff.mpr both_eq.right) ]
end

-- `reachable_in n s` says that s is at most `n` steps away from an initial
-- state, according to the relation `possible_next`.
def reachable_in : ℕ → sys_state pid_t pstate_t msg_t → Prop
| nat.zero     := sys_state.is_initial
| (nat.succ j) :=
    (λ (v : sys_state pid_t pstate_t msg_t),
      (∃ (u : sys_state pid_t pstate_t msg_t),
        reachable_in j u ∧ u.possible_next v) ∨ reachable_in j v)

def reachable (s : sys_state pid_t pstate_t msg_t) :=
  ∃ (num_steps : ℕ), s.reachable_in num_steps

variable [decidable_eq pid_t]

-- Messages are only added to the network sets.
lemma ntwk_subset {e : envelope pid_t msg_t} {u v : sys_state pid_t pstate_t msg_t} {p : pid_t} :
  (e ∈ u.network p) → (u.possible_next v) → (e ∈ v.network p) :=
begin
intro he,
rintros ⟨receiver, sender, _, _, _, _, ntwk_change, _, same⟩,
cases decidable.em (p = receiver),
{ rw h at he ⊢, rw ntwk_change, left, exact he },
rw same p h, exact he
end

end sys_state
