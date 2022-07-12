import implementation.model.sys_state

namespace predicate

variables {pid_t pstate_t msg_t : Type} [protocol pid_t pstate_t msg_t]

-- An invariant is a predicate on states which holds at all reachable states.
def invariant (p : sys_state pid_t pstate_t msg_t → Prop) : Prop :=
  ∀ (s : sys_state pid_t pstate_t msg_t), s.reachable → p s

-- A predicate is stable if, whenever it holds at u and v can be stepped-to from
-- u, the predicate also holds at v.
def stable (p : sys_state pid_t pstate_t msg_t → Prop) : Prop :=
  (∀ (u v : sys_state pid_t pstate_t msg_t), p u → u.possible_next v → p v)

-- An inductive invariant is an stable predicate which holds at the initial
-- state.
def inductive_invariant (p : sys_state pid_t pstate_t msg_t → Prop) : Prop :=
  (∀ (s : sys_state pid_t pstate_t msg_t), s.is_initial → p s) ∧
    stable p

-- Any inductive invariant is an invariant.
lemma ind_inv_is_inv {p : sys_state pid_t pstate_t msg_t → Prop} :
  inductive_invariant p → invariant p :=
begin
rintro ⟨initial, inductive_step⟩,
suffices key : ∀ (n : ℕ) (s : sys_state pid_t pstate_t msg_t), s.reachable_in n → p s,
by {
  intro s,
  rintros ⟨n, reachable_in_n_steps⟩,
  exact key n s reachable_in_n_steps },
intro n,
induction n with k hk,
{ exact initial },
intros s hyp,
cases hyp with step_required step_not_required,
{ rcases step_required with ⟨u, reach_u_in_k, s_is_u_next⟩,
  exact inductive_step u s (hk u reach_u_in_k) s_is_u_next },
exact hk s step_not_required
end

-- Stronger invariants imply weaker ones.
lemma invariants_imply {stronger weaker : sys_state pid_t pstate_t msg_t → Prop} :
  (∀ (s : sys_state pid_t pstate_t msg_t), stronger s → weaker s) →
     invariant stronger → invariant weaker :=
begin
intros strength inv_stronger s reachable,
exact strength s (inv_stronger s reachable)
end

-- A predicate is an invariant whenever it is an inductive invariant (as long as
-- we restrict only to reachable states).
--
-- NOTE(gnanabit): It is not true that invariant inv ↔ inductive_invariant inv,
-- specifically the → direction.
lemma inv_iff_ind_inv (inv : sys_state pid_t pstate_t msg_t → Prop) :
  invariant inv ↔ inductive_invariant (λ s, s.reachable ∧ inv s) :=
begin
split,
{ intro hyp,
  split,
  { intros s hs,
    have s_r : s.reachable := ⟨0, hs⟩,
    exact ⟨s_r, hyp s s_r⟩ },
  intros u v,
  rintros ⟨⟨steps_r, u_r⟩, inv_u⟩,
  intro u_pn_v,
  have v_r : v.reachable := ⟨steps_r.succ, or.inl ⟨u, u_r, u_pn_v⟩⟩,
  exact ⟨v_r, hyp v v_r⟩ },
intro hyp,
suffices key : ∀ (s : sys_state pid_t pstate_t msg_t), s.reachable ∧ inv s → inv s,
by { exact invariants_imply key (ind_inv_is_inv hyp) },
intros s hs,
exact hs.right
end

-- This result allows us to use all already-proven invariants in the inductive
-- step.
theorem use_any_invariant (p : sys_state pid_t pstate_t msg_t → Prop) :
  invariant p ↔
    (∀ (s : sys_state pid_t pstate_t msg_t), s.is_initial → p s) ∧
    (∀ (u v : sys_state pid_t pstate_t msg_t), u.reachable → p u → u.possible_next v → v.reachable → p v) :=
begin
rw inv_iff_ind_inv,
split,
{ intro hyp,
  split,
  { intros s hs,
    exact (hyp.left s hs).right },
  intros u v u_r p_u u_pn_v h_v,
  exact (hyp.right u v ⟨u_r, p_u⟩ u_pn_v).right },
rintros ⟨h_init, h_step⟩,
split,
{ intros s hs,
  exact ⟨⟨0, hs⟩, h_init s hs⟩ },
intros u v,
rintros ⟨u_r, p_u⟩,
intro u_pn_v,
have key : v.reachable,
  by { cases u_r with steps_r u_r, exact ⟨steps_r.succ, or.inl ⟨u, u_r, u_pn_v⟩⟩ },
exact ⟨key, by { exact h_step u v u_r p_u u_pn_v key }⟩,
end

end predicate
