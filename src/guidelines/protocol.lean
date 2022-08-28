import tactic.basic

structure protocol (sys_state_t : Type) :=
  (init : sys_state_t → Prop)
  (next : sys_state_t → sys_state_t → Prop)

namespace protocol

variable {sys_state_t : Type}

def reachable_in (proto : protocol sys_state_t) : ℕ → sys_state_t → Prop
| 0       := proto.init
| (n + 1) := (λ curr, (∃ prev, reachable_in n prev ∧ proto.next prev curr))

def reachable (proto : protocol sys_state_t) (s : sys_state_t) :=
  ∃ n, reachable_in proto n s

def invariant (proto : protocol sys_state_t) (predicate : sys_state_t → Prop) :=
  ∀ s, reachable proto s → predicate s

def stable (proto : protocol sys_state_t) (predicate : sys_state_t → Prop) :=
  ∀ s s', predicate s → proto.next s s' → predicate s'

lemma prove_invariant {predicate : sys_state_t → Prop}
  {proto : protocol sys_state_t}:
  proto.invariant predicate ↔
  (∀ s, proto.init s → predicate s) ∧
  proto.invariant (λ s, ∀ u, predicate s → proto.next s u → predicate u) :=
begin
split,
{ intro hyp,
  split,
  { intros s s_init, exact hyp s ⟨0, s_init⟩ },
  rintros s ⟨n, s_r_in_n⟩ u __ s_next_u,
  exact hyp u ⟨n.succ, s, s_r_in_n, s_next_u⟩ },
rintros ⟨holds_at_init, inductive_step⟩,
suffices : ∀ n s, proto.reachable_in n s → predicate s,
by { rintros s ⟨n, hn⟩, exact this n s hn },
intros n,
induction n with k hk,
{ intros s s_r_zero, exact holds_at_init s s_r_zero },
rintros s ⟨u, u_r_k, u_next_s⟩,
exact inductive_step u ⟨k, u_r_k⟩ s (hk u u_r_k) u_next_s
end

end protocol
