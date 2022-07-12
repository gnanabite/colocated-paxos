import implementation.model.predicate
import implementation.model.sys_state
import implementation.spec.main
import implementation.proof.misc

-- This file contains proofs about proposers (or what can be associated with
-- them in our co-located Paxos implementation).
--
-- NOTE(gnanabit): comments are omitted for facts that are "obvious" or not
-- particularly revealing about paxos.

variables {pid_t : Type} [linear_order pid_t] [fintype pid_t] {value_t : Type}
          {is_quorum : finset pid_t → Prop} [decidable_pred is_quorum]
          [quorum_assumption is_quorum] {vals : pid_t → value_t}

-- The ballot b has been proposed with value v if there is a server who has sent
-- a p2a with this proposal.
def proposed
  (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t))
  (b : ballot pid_t) (v : value_t) :=
  ∃ (proposer : pid_t) (e ∈ s.network proposer),
    (envelope.msg e) = message.p2a {bal := b, val := v}

lemma proposed_stable (b : ballot pid_t) (v : value_t) : predicate.stable
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    proposed s b v) :=
begin
intros u w holds_at_u u_pn_w,
rcases holds_at_u with ⟨proposer, proposal_env, sent_by_proposer, is_proposal⟩,
exact ⟨proposer, proposal_env, sys_state.ntwk_subset sent_by_proposer u_pn_w, is_proposal⟩,
end

def proposed_by
  (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t))
  (b : ballot pid_t) (proposer : pid_t) :=
  ∃ (v : value_t) (e ∈ s.network proposer),
    (envelope.msg e) = message.p2a {bal := b, val := v}

lemma none_proposed_at_init
  (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t))
  (hs : s.is_initial) : ∀ (b : ballot pid_t) (p : pid_t), ¬proposed_by s b p :=
begin
intros b p,
rintros ⟨v, e, he, e_is_proposal⟩,
specialize hs p,
unfold protocol.init at hs,
injection hs with unused key, clear unused,
rw ← key at he,
cases he,
{ rw he at e_is_proposal, injection e_is_proposal },
rw set.mem_singleton_iff at he,
rw he at e_is_proposal,
injection e_is_proposal
end

-- If a proposer p proposed ballot b, then p is the address of b.
lemma proposer_is_ballot_address : predicate.invariant
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    ∀ (b : ballot pid_t) (p : pid_t), proposed_by s b p → b.address = p) :=
begin
suffices key : predicate.inductive_invariant
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    ∀ (b : ballot pid_t) (p : pid_t), proposed_by s b p → b.address = p),
by { exact predicate.ind_inv_is_inv key },
split,
{ intros s hs b p wrong,
  exact (none_proposed_at_init s hs b p wrong).elim },
intros u w hu,
rintros ⟨receiver, sender, e, _h1, _h2, _h3, w_receiver, _h4, w_not_receiver⟩,
clear_,
unfold proposed_by,
intros b p,
cases decidable.em (p = receiver),
swap,
{ rw w_not_receiver p h,
  intro hyp,
  exact hu b p hyp },
cases e with msg __;
unfold envelope.msg at w_receiver,
clear __,
rintros ⟨v, e, he, e_is_proposal⟩,
rw h at he,
rw w_receiver at he,
cases he,
{ apply hu,
  rw h,
  unfold proposed_by,
  use [v, e, he, e_is_proposal] },
rw h,
rcases p2a_emitted e_is_proposal he with ⟨p_or, __, receiver_ballot_address, __, __, e_is⟩,
clear_,
rw e_is at e_is_proposal,
injection e_is_proposal with proposals_match,
injection proposals_match with ballots_match,
rw ballots_match at receiver_ballot_address,
exact receiver_ballot_address
end

private lemma proposer_sends_to_all_but_self : predicate.invariant
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    ∀ (b : ballot pid_t) (proposer : pid_t) (e ∈ s.network proposer)
      (v : value_t),
      (envelope.msg e) = message.p2a {bal := b, val := v} →
        e.sent_to = target.exclude proposer) :=
begin
suffices key : predicate.inductive_invariant
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    ∀ (b : ballot pid_t) (proposer : pid_t) (e ∈ s.network proposer)
      (v : value_t),
        (envelope.msg e) = message.p2a {bal := b, val := v} →
          e.sent_to = target.exclude proposer),
by { exact predicate.ind_inv_is_inv key },
split,
{ intros s hs b proposer e he v e_msg_eq,
  exact (none_proposed_at_init s hs b proposer ⟨v, e, he, e_msg_eq⟩).elim },
intros u w hu u_pn_w b proposer e he v e_msg_eq,
rcases u_pn_w with ⟨receiver, sender, e', he', deliverable, proc_change, ntwk_change, rest_same⟩,
cases decidable.em (proposer = receiver),
swap,
{ rw rest_same.right proposer h at he,
  exact hu b proposer e he v e_msg_eq },
clear rest_same proc_change,
rw h at he ⊢,
clear h proposer,
rw ntwk_change at he, clear ntwk_change,
cases he,
{ exact hu b receiver e he v e_msg_eq },
rcases p2a_emitted e_msg_eq he with ⟨_, _, _, _, _, key⟩,
rw key
end

-- If a process p proposed ballot b, then p's current ballot is at least as
-- large as b.
lemma proposer_ballot_ge : predicate.invariant
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    ∀ (b : ballot pid_t) (p : pid_t), proposed_by s b p → b ≤ (s.procs p).curr) :=
begin
suffices key : predicate.inductive_invariant
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    ∀ (b : ballot pid_t) (p : pid_t), proposed_by s b p → b ≤ (s.procs p).curr),
by { exact predicate.ind_inv_is_inv key },
split,
{ intros s hs b p wrong,
  exact (none_proposed_at_init s hs b p wrong).elim },
intros u w inv_u u_pn_w,
intros b p,
have ballot_le := ballot_nondecreasing p u_pn_w,
rcases u_pn_w with ⟨receiver, sender, e, he, deliverable, proc_change, ntwk_change, proc_same, ntwk_same⟩,
rintros ⟨v, e_del, he_del, e_del_is_vote⟩,
cases decidable.em (p = receiver),
swap,
{ rw ntwk_same p h at he_del,
  unfold proposed_by at inv_u,
  calc b ≤ (u.procs p).curr : inv_u b p ⟨v, e_del, he_del, e_del_is_vote⟩
     ... ≤ (w.procs p).curr : ballot_le },
rw h at he_del ballot_le ⊢,
clear h p,
rw ntwk_change at he_del,
cases he_del,
{ calc b ≤ (u.procs receiver).curr : inv_u b receiver ⟨v, e_del, he_del, e_del_is_vote⟩
     ... ≤ (w.procs receiver).curr : ballot_le },
rcases p2a_emitted e_del_is_vote he_del with ⟨p_or, _, _, _, _, key⟩,
rw key at e_del_is_vote,
injection e_del_is_vote with contents_same,
injection contents_same with ballots_same,
calc b = (u.procs receiver).curr : eq.symm ballots_same
   ... ≤ (w.procs receiver).curr : ballot_le
end

private lemma not_proposed_without_quorum : predicate.invariant
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    ∀ (p : pid_t), ¬is_quorum (s.procs p).followers → ¬proposed_by s (s.procs p).curr p) :=
begin
rw predicate.use_any_invariant,
split,
{ intros s hs p unimportant wrong,
  exact (none_proposed_at_init s hs (s.procs p).curr p wrong).elim },
intros u w u_reachable not_proposed_wo_quorum_at_u,
rintros ⟨receiver, sender, e, he, deliverable, proc_change, ntwk_change, rest_same⟩,
intro w_reachable,
have ballot_le := ballot_nondecreasing receiver
                  ⟨receiver, sender, e, he, deliverable, proc_change, ntwk_change, rest_same⟩,
have proposed_le_at_u := proposer_ballot_ge u u_reachable,
intro p,
cases decidable.em (p = receiver),
swap,
{ rw rest_same.left p h,
  unfold proposed_by,
  rw rest_same.right p h,
  exact not_proposed_wo_quorum_at_u p },
clear rest_same,
rw h,
clear h p,
intro hyp,
rintros ⟨v, e', he', e'_msg_eq⟩,
rw ntwk_change at he', clear ntwk_change,
rw le_iff_lt_or_eq at ballot_le,
cases ballot_le with ballot_lt ballot_eq,
{ have key : ¬proposed_by u (w.procs receiver).curr receiver,
  by { intro wrong,
      exact not_lt_of_ge (proposed_le_at_u (w.procs receiver).curr receiver wrong) ballot_lt },
  cases he',
  { exact key ⟨v, e', he', e'_msg_eq⟩ },
  clear key,
  have key := network_change receiver (u.procs receiver) e.msg sender e' he',
  cases e.msg,
    case p1a : mb {
      cases key;
      rw key.right at e'_msg_eq;
      injection e'_msg_eq
    },
    case p1b : mb p_or {
      cases key.right.right.right.right with e'_eq e'_eq,
      { clear key,
        rw e'_eq at e'_msg_eq,
        injection e'_msg_eq with props_same,
        injection props_same with ballots_same,
        exact ne_of_lt ballot_lt ballots_same },
      rw e'_eq at e'_msg_eq,
      injection e'_msg_eq
    },
    case p2a : p {
      cases key;
      rw key.right at e'_msg_eq;
      injection e'_msg_eq
    },
    case p2b : mb acc {
      exact key.elim
    },
    case preempt : {
      rw key.right at e'_msg_eq,
      injection e'_msg_eq
    }
  },
rw ← ballot_eq at e'_msg_eq,
cases he',
{ suffices cond : ¬is_quorum (u.procs receiver).followers,
  by {
    apply not_proposed_wo_quorum_at_u receiver cond,
    exact ⟨v, e', he', e'_msg_eq⟩ },
  have key := state_change receiver (u.procs receiver) e.msg sender,
  cases key,
  { rw key at proc_change,
    rw proc_change at hyp,
    exact hyp },
  cases e,
  cases e_msg,
    case p1a : b {
      cases key with ballot_increased made_larger,
      rw made_larger at proc_change,
      rw proc_change at ballot_eq,
      exact (ne_of_lt ballot_increased ballot_eq).elim,
    },
    case p1b : b p_or {
      cases key,
      { cases key with ballot_increased made_larger,
        rw made_larger at proc_change,
        rw proc_change at ballot_eq,
        exact (ne_of_lt ballot_increased ballot_eq).elim },
      cases key;
      exact key.right.right.left
    },
    case p2a : p {
      cases key with ballot_ge made_larger,
      clear ballot_ge,
      have p_bal_eq : p.bal = (u.procs receiver).curr,
      by {
        rw made_larger at proc_change,
        rw proc_change at ballot_eq,
        exact eq.symm ballot_eq
      },
      have p_bal_addr_ne_receiver: p.bal.address ≠ receiver,
      by {
        have ballot_address_is_sender : p.bal.address = sender,
        by {
          apply proposer_is_ballot_address u u_reachable p.bal sender,
          exact ⟨p.val, {msg := message.p2a p, sent_to := e_sent_to}, he,
          by { cases p, refl }⟩,
        },
        suffices key : sender ≠ receiver,
        by {
          rw ballot_address_is_sender,
          exact key
        },
        suffices key : e_sent_to = target.exclude sender,
        by { rw key at deliverable, exact deliverable },
        apply proposer_sends_to_all_but_self u u_reachable p.bal sender
              {msg := message.p2a p, sent_to := e_sent_to} he p.val,
        cases p, refl
      },
      have p_bal_addr_eq_receiver := proposer_is_ballot_address u u_reachable
                                     (u.procs receiver).curr receiver ⟨v, e', he', e'_msg_eq⟩,
      rw ← p_bal_eq at p_bal_addr_eq_receiver,
      exact (p_bal_addr_ne_receiver p_bal_addr_eq_receiver).elim
    },
    case p2b : mb acc {
      cases key with ballot_gt updated,
      rw updated at proc_change,
      rw proc_change at ballot_eq,
      exact (ne_of_lt ballot_gt ballot_eq).elim
    },
    case preempt : {
      rw key.right at proc_change,
      clear key,
      rw proc_change at ballot_eq,
      exact (ne_of_lt (ballot.next_larger receiver (u.procs receiver).curr) ballot_eq).elim
    }
  },
rcases p2a_emitted e'_msg_eq he' with
  ⟨p_or, e_msg_is, receiver_still_leader, began_wo_quorum, ended_w_quorum, emitted_just⟩,
suffices key : (w.procs receiver).followers = (u.procs receiver).followers ∪ {sender},
by { rw key at hyp, exact hyp ended_w_quorum },
rw proc_change,
rw e_msg_is,
unfold protocol.handler server.handle_p1b,
rw if_neg (lt_irrefl _),
rw if_neg (not_not.mpr receiver_still_leader),
rw if_neg (lt_irrefl _),
rw if_neg (show ¬(is_quorum (u.procs receiver).followers ∨
                  sender ∈ (u.procs receiver).followers), by {
  intro cond,
  cases cond with cond cond,
  { exact began_wo_quorum cond },
  have key : (u.procs receiver).followers ∪ {sender} = (u.procs receiver).followers,
  by {
    rw finset.union_eq_left_iff_subset,
    rw finset.singleton_subset_iff,
    exact cond
  },
  rw key at ended_w_quorum,
  exact began_wo_quorum ended_w_quorum
}),
rw if_pos ended_w_quorum
end

-- If two proposals have the same ballot, they have the same value.
--
-- The proof is by induction using predicates we've already proven.
--
-- Nothing is proposed at the initial state.
--
-- If the fact holds at u and two values are proposed with b at some state w
-- following from u, then the proposals are issued by the same proposer. Either
-- the proposer issued both proposals in u, in which case we apply the inductive
-- hypothesis, or one proposal was issued in u and the other was just issued in
-- the step (there are two ways in which that might happen, and they're
-- symmetric), or both proposals were issued in the last step.
--
-- * In the case that one proposal was issued at u and the other was only issued
-- as a result of the last step, it should be impossible, because when a server
-- proposes a value in a step, it has no quorum before it sends the proposal,
-- and therefore it could not have sent a proposal in step u under the required
-- ballot.
--
-- * In the case that both proposals were issued in the last step, only one
-- proposal is issued at a time, so both are the same proposal.
theorem proposals_unique : predicate.invariant
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    ∀ (b : ballot pid_t) (v₁ v₂ : value_t), proposed s b v₁ → proposed s b v₂ → v₁ = v₂) :=
begin
rw predicate.use_any_invariant,
split,
{ intros s hs b v _ proposed_at_initial,
  rcases proposed_at_initial with ⟨proposer, e, he, e_is_proposal⟩,
  exfalso, apply none_proposed_at_init s hs b proposer,
  exact ⟨v, e, he, e_is_proposal⟩ },
intros u w u_reachable unique_at_u u_pn_w w_reachable b v₁ v₂ hp₁ hp₂,
specialize unique_at_u b v₁ v₂,
rcases u_pn_w with ⟨receiver, sender, e, he, deliverable, proc_change, ntwk_change, rest_same⟩,
cases hp₁ with proposer₁ hp₁,
cases hp₂ with proposer₂ hp₂,
have prop₁_eq := proposer_is_ballot_address w w_reachable b proposer₁ ⟨v₁, hp₁⟩,
rw ← prop₁_eq at hp₁,
have prop₂_eq := proposer_is_ballot_address w w_reachable b proposer₂ ⟨v₂, hp₂⟩,
rw ← prop₂_eq at hp₂,
clear prop₁_eq prop₂_eq proposer₁ proposer₂,
cases decidable.em (b.address = receiver),
swap,
{ rw rest_same.right b.address h at hp₁ hp₂,
  exact unique_at_u ⟨b.address, hp₁⟩ ⟨b.address, hp₂⟩ },
clear rest_same,
rw h at hp₁ hp₂, clear h,
rcases hp₁ with ⟨e₁, he₁, e₁_msg_eq⟩,
rcases hp₂ with ⟨e₂, he₂, e₂_msg_eq⟩,
rw ntwk_change at he₁ he₂,
cases he₁; cases he₂,
{ exact unique_at_u ⟨receiver, e₁, he₁, e₁_msg_eq⟩ ⟨receiver, e₂, he₂, e₂_msg_eq⟩ },
{ rcases p2a_emitted e₂_msg_eq he₂ with ⟨_, _, _, no_quorum, _, e₂_is⟩,
  have ballots_match : (u.procs receiver).curr = b,
  by { rw e₂_is at e₂_msg_eq, injection e₂_msg_eq with key, injection key },
  clear e₂_is e₂_msg_eq he₂ e₂,
  rw ← ballots_match at e₁_msg_eq,
  exfalso,
  apply not_proposed_without_quorum u u_reachable receiver no_quorum,
  exact ⟨v₁, e₁, he₁, e₁_msg_eq⟩ },
{ rcases p2a_emitted e₁_msg_eq he₁ with ⟨_, _, _, no_quorum, _, e₁_is⟩,
  have ballots_match : (u.procs receiver).curr = b,
  by { rw e₁_is at e₁_msg_eq, injection e₁_msg_eq with key, injection key },
  clear e₁_is e₁_msg_eq he₁ e₁,
  rw ← ballots_match at e₂_msg_eq,
  exfalso,
  apply not_proposed_without_quorum u u_reachable receiver no_quorum,
  exact ⟨v₂, e₂, he₂, e₂_msg_eq⟩ },
rcases p2a_emitted e₁_msg_eq he₁ with ⟨p₁, e_has_p₁, __, __, __, key₁⟩,
rcases p2a_emitted e₂_msg_eq he₂ with ⟨p₂, e_has_p₂, __, __, __, key₂⟩,
clear_,
have proposals_match : p₁ = p₂,
by { injection eq.trans (eq.symm e_has_p₁) e_has_p₂ },
have val₁ : v₁ = proposal.value_or_default (proposal.merge (u.procs receiver).accepted p₁)
                                           (vals receiver),
by {
  rw key₁ at e₁_msg_eq,
  injection e₁_msg_eq with fact,
  injection fact with _ goal,
  exact eq.symm goal },
have val₂ : v₂ = proposal.value_or_default (proposal.merge (u.procs receiver).accepted p₂)
                                           (vals receiver),
by {
  rw key₂ at e₂_msg_eq,
  injection e₂_msg_eq with fact,
  injection fact with _ goal,
  exact eq.symm goal },
rw val₁,
rw val₂,
rw proposals_match
end
