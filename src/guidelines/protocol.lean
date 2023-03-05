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

def reachable_in_from (proto : protocol sys_state_t) (src : sys_state_t) : ℕ → sys_state_t → Prop
| 0       := (λ dst, dst = src)
| (n + 1) := (λ dst, (∃ intermediate, reachable_in_from n intermediate ∧
                                      proto.next intermediate dst))

def reachable_from (proto : protocol sys_state_t) (src dst : sys_state_t) :=
  ∃ n, reachable_in_from proto src n dst

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

lemma reachable_from_reachable_is_reachable (proto : protocol sys_state_t) :
  ∀ s s', proto.reachable s → proto.reachable_from s s' → proto.reachable s' :=
begin
suffices : ∀ s, proto.reachable s → ∀ n s', proto.reachable_in_from s n s' → proto.reachable s',
by { rintros s s' reachable_s ⟨n, s'_reachable_from_s_in_n⟩, exact this s reachable_s n s' s'_reachable_from_s_in_n },
intros s reachable_s n,
induction n with k hk,
{ intros s' hs',
  have : s' = s := hs', rw this, exact reachable_s },
rintros s'' ⟨s', s'_reachable_from_s_in_k, s''_follows_s'⟩,
rcases (hk s' s'_reachable_from_s_in_k) with ⟨j, hj⟩,
exact ⟨j.succ, s', hj, s''_follows_s'⟩
end

lemma stability_applies_to_reachable_from (predicate : sys_state_t → Prop)
  (proto : protocol sys_state_t) :
  proto.stable predicate → ∀ s s', proto.reachable_from s s' → predicate s → predicate s' :=
begin
intro stability,
suffices : ∀ n s, predicate s → ∀ s', proto.reachable_in_from s n s' → predicate s',
by {
  rintros s s' ⟨n, hn⟩ predicate_at_s,
  exact this n s predicate_at_s s' hn },
intros n s predicate_at_s, induction n with k hk,
{ intros s' h, have : s' = s := h, rw this, exact predicate_at_s },
rintros s'' ⟨s', s'_reachable_in_k, s''_follows_s'⟩,
exact stability s' s'' (hk s' s'_reachable_in_k) s''_follows_s',
end

end protocol
