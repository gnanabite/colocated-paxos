import implementation.model.predicate
import implementation.model.sys_state
import implementation.spec.main
import implementation.proof.misc
import implementation.proof.proposer

-- This file contains proofs about voters (or what can be associated with
-- them in our co-located Paxos implementation).
--
-- NOTE(gnanabit): comments are omitted for facts that are "obvious" or not
-- particularly revealing about paxos.

variables {pid_t : Type} [linear_order pid_t] [fintype pid_t] {value_t : Type}
          {is_quorum : finset pid_t → Prop} [decidable_pred is_quorum]
          [quorum_assumption is_quorum] {vals : pid_t → value_t}

-- A server's ballot is always larger than or equal to the ballot in the
-- proposal it has stored in `accepted` (if such a proposal exists).
--
-- Similarly, the ballot in a p1b is always larger than the proposal stored in
-- the p1b.
lemma current_ge_accepted_ballot : predicate.invariant
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    (∀ (p : pid_t) (prop : proposal pid_t value_t),
      (s.procs p).accepted = some prop → prop.bal ≤ (s.procs p).curr) ∧
    (∀ (p : pid_t) (e ∈ s.network p) (b : ballot pid_t) (prop : proposal pid_t value_t),
      (envelope.msg e) = message.p1b b (option.some prop) → prop.bal ≤ b)) :=
begin
suffices : predicate.inductive_invariant _,
by { exact predicate.ind_inv_is_inv this },
split,
{ intros s hs,
  split;
  intro p;
  specialize hs p;
  unfold protocol.init at hs;
  injection hs with start_proc start_network,
  { rw ← start_proc,
    intro prop,
    trivial },
  rw ← start_network,
  intros e he b prop contradicts_he,
  cases he,
  { rw he at contradicts_he, injection contradicts_he },
  rw set.mem_singleton_iff at he,
  rw he at contradicts_he, injection contradicts_he },
intros u v,
rintros ⟨servers_satisfy, promises_satisfy⟩,
intro u_pn_v,
have to_split := u_pn_v,
rcases to_split with ⟨receiver, sender, e, he, deliverable, proc_change, ntwk_change, same⟩,
split;
intro p;
cases decidable.em (p = receiver),
{ clear same,
  intro prop,
  rw h, clear h p,
  rw proc_change,
  have delta := state_change receiver (u.procs receiver) e.msg sender,
  cases delta,
  { rw delta, exact servers_satisfy receiver prop },
  cases e,
  cases e_msg,
    case p1a : b {
      cases delta with new_ballot_larger b_is_new_ballot,
      rw b_is_new_ballot,
      intro hyp,
      apply le_of_lt,
      calc prop.bal ≤ (u.procs receiver).curr : servers_satisfy receiver prop hyp
                ... < b                       : new_ballot_larger
    },
    case p1b : b p_or {
      cases delta,
      { cases delta with new_ballot_larger b_is_new_ballot,
        rw b_is_new_ballot,
        intro hyp,
        apply le_of_lt,
        calc prop.bal ≤ (u.procs receiver).curr : servers_satisfy receiver prop hyp
                  ... < b : new_ballot_larger },
      cases delta,
      { rw delta.right.right.right.right,
        intro hyp,
        have key : prop.bal = (u.procs receiver).curr,
        by {
          injection hyp with key,
          rw ← key
        },
        rw key },
      rw delta.right.right.right.right.right,
      intro hyp,
      cases proposal.merge_is_one_of (u.procs receiver).accepted p_or,
      { rw h at hyp,
        exact servers_satisfy receiver prop hyp },
      rw h at hyp,
      rw delta.left,
      apply promises_satisfy sender {msg := message.p1b b p_or, sent_to := e_sent_to} he b prop,
      rw ← hyp
    },
    case p2a : p {
      cases delta with new_ballot_larger b_is_new_ballot,
      rw b_is_new_ballot,
      intro hyp,
      have key : p = prop, by { injection hyp },
      rw key
    },
    case p2b : b acc {
      cases delta with new_ballot_larger b_is_new_ballot,
      rw b_is_new_ballot,
      intro hyp,
      apply le_of_lt,
      calc prop.bal ≤ (u.procs receiver).curr : servers_satisfy receiver prop hyp
                ... < b : new_ballot_larger
    },
    case preempt : {
      cases delta with ballot_not_from_self ballot_is_next,
      rw ballot_is_next,
      intro hyp,
      apply le_of_lt,
      calc prop.bal ≤ (u.procs receiver).curr : servers_satisfy receiver prop hyp
                ... < ballot.next receiver (u.procs receiver).curr : ballot.next_larger receiver (u.procs receiver).curr,
    }},
{ rw same.left p h, exact servers_satisfy p },
{ rw h, clear h p,
  intros e' he' b prop e'_msg_eq,
  rw ntwk_change at he',
  cases he',
  { exact promises_satisfy receiver e' he' b prop e'_msg_eq },
  rcases p1b_emitted e'_msg_eq he' with ⟨b', e_msg_is, accepted_unchanged, b_is_max⟩,
  calc prop.bal ≤ (u.procs receiver).curr : servers_satisfy receiver prop accepted_unchanged
            ... ≤ b                       : by { rw ← b_is_max,
                                                 exact le_max_left (u.procs receiver).curr b'} },
rw same.right p h, exact promises_satisfy p
end

-- Any stored proposal has been proposed in some p2a (a stored proposal is one in either a p1b
-- or in a server's `accepted` field).
lemma accepted_means_issued : predicate.invariant
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    (∀ (p : pid_t) (prop : proposal pid_t value_t),
      (s.procs p).accepted = some prop → proposed s prop.bal prop.val) ∧
    (∀ (p : pid_t) (e ∈ s.network p) (b : ballot pid_t) (prop : proposal pid_t value_t),
      (envelope.msg e) = message.p1b b (option.some prop) → proposed s prop.bal prop.val))
  :=
begin
suffices : predicate.inductive_invariant _,
by { exact predicate.ind_inv_is_inv this },
split,
{ intros s hs,
  split;
  intro p;
  specialize hs p;
  unfold protocol.init at hs;
  injection hs with start_proc start_network,
  { rw ← start_proc,
    intro prop,
    trivial },
  rw ← start_network,
  intros e he b prop contradicts_he,
  cases he,
  { rw he at contradicts_he, injection contradicts_he },
  rw set.mem_singleton_iff at he,
  rw he at contradicts_he, injection contradicts_he },
intros u v,
rintros ⟨accepted_satisfies, promises_satisfy⟩,
intro u_pn_v,
have to_split := u_pn_v,
rcases to_split with ⟨receiver, sender, e, he, deliverable, proc_change, ntwk_change, same⟩,
split;
intro p;
cases decidable.em (p = receiver),
{ rw h,
  clear h p,
  rw proc_change,
  intros prop h_prop,
  suffices key : proposed u prop.bal prop.val ∨
    (∃ e' ∈ (protocol.handler receiver (u.procs receiver) e.msg sender).snd,
       envelope.msg e' = message.p2a prop),
  by {
    cases key,
    { exact proposed_stable prop.bal prop.val u v key u_pn_v },
    { rcases key with ⟨e', he', e'_msg_is⟩,
      use [receiver, e'],
      split,
      { rw ntwk_change, right, exact he' },
      rw e'_msg_is, cases prop, refl },
  },
  have acc_unchanged_enough : (protocol.handler receiver (u.procs receiver) e.msg sender).fst.accepted = (u.procs receiver).accepted → proposed u prop.bal prop.val ∨
    (∃ e' ∈ (protocol.handler receiver (u.procs receiver) e.msg sender).snd,
       envelope.msg e' = message.p2a prop), by {
    intro hyp, left, rw hyp at h_prop, exact accepted_satisfies receiver prop h_prop
  },
  have key := state_change receiver (u.procs receiver) e.msg sender,
  cases key,
  { left, rw key at h_prop, exact accepted_satisfies receiver prop h_prop  },
  cases e,
  cases e_msg,
    case p1a : b { apply acc_unchanged_enough, rw key.right },
    case p1b : b p_or {
      cases key,
      { apply acc_unchanged_enough, rw key.right },
      cases key,
      { right,
        clear acc_unchanged_enough,
        rcases key with ⟨same_bal, bal_from_self, u_no_qrm, v_has_qrm, state_change⟩,
        have prop_eq: { proposal . bal := (u.procs receiver).curr,
                            val := proposal.value_or_default
                                     (proposal.merge (u.procs receiver).accepted p_or)
                                     (vals receiver)} = prop, by {
          rw state_change at h_prop, injection h_prop
        },
        use {envelope . msg := message.p2a prop,
                      sent_to := target.exclude receiver},
        split,
        { rw ← prop_eq,
          unfold protocol.handler server.handle_p1b,
          rw if_neg (show ¬(u.procs receiver).curr < b, by { rw same_bal, exact lt_irrefl b }),
          rw if_neg (show ¬(u.procs receiver).curr.address ≠ receiver,
                     by { rw decidable.not_not, rw same_bal, exact bal_from_self }),
          rw if_neg (show ¬(u.procs receiver).curr > b, by { rw same_bal, exact lt_irrefl b }),
          rw if_neg (show ¬(is_quorum (u.procs receiver).followers ∨
                     sender ∈ (u.procs receiver).followers),
                     by {
                       rw not_or_distrib,
                       split,
                       { exact u_no_qrm },
                       intro cond,
                       have fact : (u.procs receiver).followers ∪ {sender} = (u.procs receiver).followers,
                       by {
                         rw finset.union_eq_left_iff_subset,
                         rw finset.singleton_subset_iff,
                         exact cond
                       },
                       apply u_no_qrm,
                       rw ← fact,
                       exact v_has_qrm
                     }),
          rw if_pos v_has_qrm,
          left, refl },
      refl },
      rw key.right.right.right.right.right at h_prop,
      clear key acc_unchanged_enough,
      left,
      cases proposal.merge_is_one_of (u.procs receiver).accepted p_or;
      rw h at h_prop,
      { exact accepted_satisfies receiver prop h_prop },
      apply promises_satisfy sender {msg := message.p1b b p_or, sent_to := e_sent_to} he b prop,
      rw ← h_prop
    },
    case p2a : p {
      clear acc_unchanged_enough,
      rw key.right at h_prop, clear key,
      left,
      have key : prop = p, by { injection h_prop with fact, exact eq.symm fact },
      rw key,
      use [sender, {msg := message.p2a p, sent_to := e_sent_to}, he],
      cases p, refl
    },
    case p2b : b acc { apply acc_unchanged_enough, rw key.right  },
    case preempt : { apply acc_unchanged_enough, rw key.right },
  },
{ rw same.left p h,
  have ind_hyp := accepted_satisfies p,
  intros prop key,
  exact proposed_stable prop.bal prop.val u v (accepted_satisfies p prop key) u_pn_v },
{ rw h, clear same h p,
  rw ntwk_change, clear ntwk_change proc_change,
  intros e' he' b p e'_is_1b,
  cases he',
  { exact proposed_stable p.bal p.val u v
          (promises_satisfy receiver e' he' b p e'_is_1b) u_pn_v },
  rcases p1b_emitted e'_is_1b he' with ⟨b', e_msg_is, accepted_unchanged, b_is_max⟩,
  exact proposed_stable p.bal p.val u v
        (accepted_satisfies receiver p accepted_unchanged) u_pn_v },
rw same.right p h,
intros e' he' b prop e'_is_promise,
have ind_hyp := promises_satisfy p e' he' b prop e'_is_promise,
exact proposed_stable prop.bal prop.val u v ind_hyp u_pn_v
end


-- The ballot in a server's `accepted` field only ever increases. That is, if at
-- some point a server has accepted a proposal, then it will always have a
-- proposal in `accepted` and moreover the proposal ballot will be at least as
-- large as what's currently stored.
lemma accepted_ballot_nondecreasing {p : pid_t} {prop_u : proposal pid_t value_t}
  (u v : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t))
  (u_r : u.reachable) (h_uv : u.possible_next v)
  (h_u : (u.procs p).accepted = some prop_u) :
  ∃ (prop_v : proposal pid_t value_t), (v.procs p).accepted = some prop_v ∧ prop_u.bal ≤ prop_v.bal :=
begin
rcases h_uv with ⟨receiver, sender, e, he, deliverable, proc_change, ntwk_change, same⟩,
cases decidable.em (p = receiver),
swap,
{ exact ⟨prop_u, by { rw same.left p h, exact h_u }, by refl⟩ },
rw h at h_u ⊢,
clear h p,
rw proc_change,
have key := state_change receiver (u.procs receiver) e.msg sender,
cases key,
{ exact ⟨prop_u, by { rw key, exact h_u }, by refl⟩ },
cases e.msg,
  case p1a : b {
    rw key.right,
    exact ⟨prop_u, h_u, by refl⟩
  },
  case p1b : b p_or {
    cases key,
    { rw key.right,
      exact ⟨prop_u, h_u, by refl⟩ },
    cases key,
    { rw key.right.right.right.right,
      use { bal := (u.procs receiver).curr,
            val := proposal.value_or_default (proposal.merge (u.procs receiver).accepted p_or)
                                 (vals receiver) },
      exact ⟨by refl, (current_ge_accepted_ballot u u_r).left receiver prop_u h_u⟩ },
    rw key.right.right.right.right.right,
    rw h_u,
    exact proposal.merge_ballot_ge_left prop_u p_or
  },
  case p2a : pr {
    cases key with pr_bal_ge_curr update_w_pr,
    exact ⟨pr, by { rw update_w_pr }, by { exact le_trans
      ((current_ge_accepted_ballot u u_r).left receiver prop_u h_u)
      pr_bal_ge_curr }⟩,
  },
  case p2b : b accepted {
    rw key.right,
    exact ⟨prop_u, h_u, by refl⟩
  },
  case preempt : {
    rw key.right,
    exact ⟨prop_u, h_u, by refl⟩
  }
end

-- If a server issued a p1b promising not to accept anything with ballot less
-- than b, then its `curr` ballot will always be at least b.
lemma ballot_ge_any_promised (voter : pid_t)
  (b_promised : ballot pid_t) (p_or : option (proposal pid_t value_t)) : predicate.invariant
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    (∃ e ∈ s.network voter, envelope.msg e = message.p1b b_promised p_or) →
      (s.procs voter).curr ≥ b_promised) :=
begin
suffices : predicate.inductive_invariant _,
by { exact predicate.ind_inv_is_inv this},
split,
{ intros s hs,
  rintros ⟨e, he, e_is_promise⟩,
  specialize hs voter,
  injection hs with __ key, clear_, rw ← key at he,
  cases he,
  { rw he at e_is_promise, injection e_is_promise },
  rw set.mem_singleton_iff at he,
  rw he at e_is_promise, injection e_is_promise },
intros u v hu u_pn_v,
rintros ⟨e, he, e_is_promise⟩,
rcases (show _, by exact u_pn_v) with ⟨receiver, sender, e', he', deliverable, proc_change, ntwk_change, rest_same⟩,
cases decidable.em (voter = receiver),
swap,
{ rw rest_same.left voter h,
  rw rest_same.right voter h at he,
  exact hu ⟨e, he, e_is_promise⟩ },
clear rest_same,
rw ← h at proc_change ntwk_change deliverable, clear h receiver,
rw ntwk_change at he,
cases he,
{ apply le_trans (hu ⟨e, he, e_is_promise⟩),
  exact ballot_nondecreasing voter u_pn_v },
rcases p1b_emitted e_is_promise he with ⟨b', e'_is, accepted_is, is_max⟩,
rw e'_is at proc_change, rw proc_change,
unfold protocol.handler server.handle_p1a,
cases decidable.em ((u.procs voter).curr < b'),
{ rw if_pos h,
  unfold max max_default at is_max,
  rw if_neg (not_le_of_gt h) at is_max,
  rw is_max, exact le_refl _ },
rw if_neg h,
unfold max max_default at is_max,
rw if_pos (le_of_not_gt h) at is_max,
rw is_max,
exact le_refl _
end

def voted_ballot
  (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t))
  (voter : pid_t) (b : ballot pid_t) :=
  ∃ e ∈ s.network voter, (envelope.msg e) = message.p2b b tt

lemma voted_imp_proposed (voter : pid_t) (b : ballot pid_t) : predicate.invariant
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    voted_ballot s voter b → ∃ v, proposed s b v) :=
begin
suffices : predicate.inductive_invariant _,
by { exact predicate.ind_inv_is_inv this },
split,
{ intros s hs, rintros ⟨ev, h_ev, ev_vote⟩,
  specialize hs voter,
  injection hs with __ key, clear_,
  rw ← key at h_ev,
  cases h_ev,
  { rw h_ev at ev_vote, injection ev_vote },
  rw set.mem_singleton_iff at h_ev,
  rw h_ev at ev_vote, injection ev_vote },
intros u w hu u_pn_w,
rcases (show _, by exact u_pn_w) with ⟨receiver, sender, e, he, deliverable, proc_change, ntwk_change, proc_same, ntwk_same⟩, clear deliverable proc_same,
intro h_voted,
unfold voted_ballot at h_voted,
cases decidable.em (voter = receiver),
swap,
{ rw ntwk_same voter h at h_voted,
  rcases hu h_voted with ⟨v, proposed_at_u⟩,
  exact ⟨v, proposed_stable b v u w proposed_at_u u_pn_w⟩ },
clear ntwk_same,
rw ← h at ntwk_change proc_change, clear h receiver,
rw ntwk_change at h_voted,
rcases h_voted with ⟨e', he', e'_msg_is_vote⟩,
cases he',
{ rcases hu ⟨e', he', e'_msg_is_vote⟩ with ⟨v, proposed_at_u⟩,
  exact ⟨v, proposed_stable b v u w proposed_at_u u_pn_w⟩ },
have event := p2b_emitted e'_msg_is_vote he',
cases event,
{ rcases event with ⟨p_or, e_msg_is, bal_from_self, u_no_qrm, v_has_qrm, rest⟩,
  have ntwk_delta_eq : (protocol.handler voter (u.procs voter) e.msg sender).snd = {{msg := message.p2a
                {bal := (u.procs voter).curr,
                 val := proposal.value_or_default (proposal.merge (u.procs voter).accepted p_or) (vals voter)},
       sent_to := target.exclude voter},
        {msg := message.p2b (u.procs voter).curr tt, sent_to := target.just voter}},
  by {
    rw e_msg_is,
    unfold protocol.handler server.handle_p1b,
    rw if_neg (lt_irrefl _),
    rw if_neg (show ¬(u.procs voter).curr.address ≠ voter,
               by { rw decidable.not_not, exact bal_from_self }),
    rw if_neg (lt_irrefl _),
    rw if_neg (show ¬(is_quorum (u.procs voter).followers ∨
               sender ∈ (u.procs voter).followers),
               by {
                 rw not_or_distrib,
                 split,
                 { exact u_no_qrm },
                 intro cond,
                 have fact : (u.procs voter).followers ∪ {sender} = (u.procs voter).followers, 
                 by {
                   rw finset.union_eq_left_iff_subset,
                   rw finset.singleton_subset_iff,
                   exact cond
                 },
                 apply u_no_qrm,
                 rw ← fact,
                 exact v_has_qrm
               }),
      rw if_pos v_has_qrm },
  use proposal.value_or_default (proposal.merge (u.procs voter).accepted p_or) (vals voter),
  use voter,
  use {msg := message.p2a
                {bal := (u.procs voter).curr,
                 val := proposal.value_or_default (proposal.merge (u.procs voter).accepted p_or) (vals voter)},
       sent_to := target.exclude voter},
  split,
  { rw ntwk_change, right,
    rw ntwk_delta_eq, left, refl },
  suffices : (u.procs voter).curr = b, by { rw this },
  rw rest at e'_msg_is_vote, injection e'_msg_is_vote },
rcases event with ⟨⟨p_bal, p_val⟩, e_msg_is, p_bal_larger⟩,
use [p_val, sender, e, sys_state.ntwk_subset he u_pn_w],
rw e_msg_is,
suffices : p_bal = b, by { rw this },
rw e_msg_is at he',
unfold protocol.handler server.handle_p2a at he',
rw if_pos p_bal_larger at he',
rw set.mem_singleton_iff at he',
rw he' at e'_msg_is_vote,
injection e'_msg_is_vote
end

-- In a same vein to `ballot_ge_any_promised`, if a server voted for a ballot b,
-- then it will always have a proposal stored where the proposal's ballot is at
-- least b.
lemma accepted_ge_any_voted (voter : pid_t) (b : ballot pid_t): predicate.invariant
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    voted_ballot s voter b →
      ∃ p, (s.procs voter).accepted = some p ∧ p.bal ≥ b) :=
begin
rw predicate.use_any_invariant,
split,
{ intros s hs,
  rintros ⟨e, he, e_is_vote⟩,
  specialize hs voter,
  unfold protocol.init at hs,
  injection hs with __ network, clear_,
  rw ← network at he,
  cases he,
  { rw he at e_is_vote, injection e_is_vote },
  rw set.mem_singleton_iff at he,
  rw he at e_is_vote, injection e_is_vote },
intros u v u_r hu u_pn_v v_r,
rcases (show _, by exact u_pn_v) with ⟨receiver, sender, e', he', deliverable, proc_change, ntwk_change, rest_same⟩,
rintros ⟨ev, h_ev, ev_vote⟩,
cases decidable.em (voter = receiver),
swap,
{ rw rest_same.left voter h,
  rw rest_same.right voter h at h_ev,
  exact hu ⟨ev, h_ev, ev_vote⟩ },
rw ← h at proc_change ntwk_change deliverable,
clear rest_same h receiver,
rw ntwk_change at h_ev,
cases h_ev,
{ rcases hu ⟨ev, h_ev, ev_vote⟩ with ⟨p, hp, p_ge_b⟩,
  rcases accepted_ballot_nondecreasing u v u_r u_pn_v hp with ⟨prop_v, middle, right_for_trans⟩,
  exact ⟨prop_v, middle, le_trans p_ge_b right_for_trans⟩ },
cases p2b_emitted ev_vote h_ev,
{ rcases h with ⟨p_or, e'_msg_is, active, no_start_quorum, end_w_quorum, ev_is⟩,
  use {bal := (u.procs voter).curr,
       val := proposal.value_or_default (proposal.merge (u.procs voter).accepted p_or) (vals voter)},
  rw e'_msg_is at proc_change, clear e'_msg_is,
  rw proc_change,
  unfold protocol.handler server.handle_p1b,
  rw if_neg (lt_irrefl _),
  rw if_neg (decidable.not_not.mpr active),
  rw if_neg (lt_irrefl _),
  rw if_neg (show ¬(is_quorum (u.procs voter).followers ∨ sender ∈ (u.procs voter).followers),
    by {
      rw not_or_distrib,
      split,
      { exact no_start_quorum },
      intro cond,
      have fact : (u.procs voter).followers ∪ {sender} = (u.procs voter).followers,
      by {
        rw finset.union_eq_left_iff_subset,
        rw finset.singleton_subset_iff,
        exact cond
      },
      apply no_start_quorum,
      rw ← fact,
      exact end_w_quorum
    }),
  rw if_pos end_w_quorum,
  split,
  { refl },
  apply ge_of_eq,
  rw ev_is at ev_vote,
  injection ev_vote },
rcases h with ⟨p, e'_msg_is, p_bal_larger⟩,
rw e'_msg_is at proc_change h_ev, clear e'_msg_is,
use p,
rw proc_change,
unfold protocol.handler server.handle_p2a,
rw if_pos p_bal_larger,
split,
{ refl },
unfold protocol.handler server.handle_p2a at h_ev,
rw if_pos p_bal_larger at h_ev,
rw set.mem_singleton_iff at h_ev,
rw h_ev at ev_vote,
injection ev_vote with key __,
exact ge_of_eq key
end

-- If a server sent a p1b with ballot b and wrote that no ballot was stored,
-- then it will never vote for any proposal with ballot less than b.
--
-- If a server sent a p1b with ballot b and wrote that its highest stored was
-- (some p), then it will never vote for any proposal with a ballot larger than
-- p.bal and less than b.
theorem none_voted_between_p1b : predicate.invariant
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    ∀ (voter : pid_t) (b_voted b_promised : ballot pid_t)
      (p_or : option (proposal pid_t value_t)),
      voted_ballot s voter b_voted →
        (∃ e ∈ s.network voter, envelope.msg e = message.p1b b_promised p_or) →
          b_voted ≥ b_promised ∨
          ∃ p, p_or = some p ∧ b_voted ≤ p.bal) :=
begin
suffices intros_before :
  ∀ (voter : pid_t) (b_voted b_promised : ballot pid_t) (p_or : option (proposal pid_t value_t)),
    predicate.invariant
    (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
       voted_ballot s voter b_voted →
         (∃ (e ∈ s.network voter), envelope.msg e = message.p1b b_promised p_or) →
           (b_voted ≥ b_promised ∨
             ∃ p, p_or = some p ∧ b_voted ≤ p.bal)),
by { intros u u_r voter b_voted b_promised p_or,
     exact intros_before voter b_voted b_promised p_or u u_r },
intros voter b_voted b_promised p_or,
rw predicate.use_any_invariant,
split,
{ intros s hs,
  rintros ⟨e, he, e_is_vote⟩,
  specialize hs voter,
  unfold protocol.init at hs,
  injection hs with __ network, clear_,
  rw ← network at he,
  cases he,
  { rw he at e_is_vote, injection e_is_vote },
  rw set.mem_singleton_iff at he,
  rw he at e_is_vote, injection e_is_vote },
intros u w u_r hu u_pn_w w_r,
rintros ⟨ev, h_ev, ev_vote⟩,
rintros ⟨ep, h_ep, ep_promise⟩,
rcases (by exact u_pn_w) with ⟨receiver, sender, e', he', deliverable, proc_change, ntwk_change, rest_same⟩,
cases decidable.em (voter = receiver),
swap,
{ rw rest_same.right voter h at h_ev h_ep,
  exact hu ⟨ev, h_ev, ev_vote⟩ ⟨ep, h_ep, ep_promise⟩ },
clear rest_same,
rw ← h at proc_change ntwk_change deliverable, clear h receiver,
rw ntwk_change at h_ev h_ep,
cases h_ep; cases h_ev,
{ exact hu ⟨ev, h_ev, ev_vote⟩ ⟨ep, h_ep, ep_promise⟩ },
{ left,
  have key := ballot_ge_any_promised voter b_promised p_or u u_r ⟨ep, h_ep, ep_promise⟩,
  cases p2b_emitted ev_vote h_ev,
  { rcases h with ⟨p_or, _, _, _, _, ev_is⟩,
    rw ev_is at ev_vote,
    have fact : (u.procs voter).curr = b_voted, by { injection ev_vote },
    rw fact at key, exact key },
  rcases h with ⟨p, e'_is, p_larger⟩,
  rw e'_is at h_ev,
  unfold protocol.handler server.handle_p2a at h_ev,
  rw if_pos p_larger at h_ev,
  rw set.mem_singleton_iff at h_ev,
  rw h_ev at ev_vote,
  injection ev_vote with fact __, clear_,
  rw ← fact,
  exact le_trans key p_larger },
{ right,
  rcases p1b_emitted ep_promise h_ep with ⟨b', _, key, _⟩,
  rcases accepted_ge_any_voted voter b_voted u u_r ⟨ev, h_ev, ev_vote⟩ with ⟨p, fact, p_bal_ge⟩,
  use p,
  split,
  { rw ← key, exact fact },
  exact p_bal_ge
  },
rcases p1b_emitted ep_promise h_ep with ⟨b', e'_msg_is, _, _⟩,
rw e'_msg_is at h_ev,
unfold protocol.handler server.handle_p1a at h_ev,
cases decidable.em ((u.procs voter).curr < b'),
{ rw if_pos h at h_ev,
  rw set.mem_singleton_iff at h_ev,
  rw h_ev at ev_vote,
  injection ev_vote },
rw if_neg h at h_ev,
rw set.mem_singleton_iff at h_ev,
rw h_ev at ev_vote,
injection ev_vote
end
