import implementation.model.predicate
import implementation.model.sys_state
import implementation.spec.main
import implementation.proof.proposer
import implementation.proof.voter

-- This file contains proofs about the interaction between proposers and voters;
-- it's essentially all about the p1b phase. While the proposer.lean and
-- voter.lean files say some things about what a server does in isolation, this
-- file explains what each node can tell about other nodes in the system based
-- off of its `.followers` field.

variables {pid_t : Type} [linear_order pid_t] [fintype pid_t] {value_t : Type}
          {is_quorum : finset pid_t → Prop} [decidable_pred is_quorum]
          [quorum_assumption is_quorum] {vals : pid_t → value_t}

-- If a server `proposer` is active (meaning its current ballot b has itself as
-- the address), then all followers are either (i) the `proposer` itself or (ii)
-- a server who has sent a p1b with ballot b to `proposer`; if (iii) the
-- proposer's p1b has a stored accepted field (`some acptd`), then the
-- `proposer` has stored an accepted field with ballot at least as large as
-- `acptd.bal`.
lemma followers_sent_p1b : predicate.invariant
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    ∀ (proposer : pid_t), (s.procs proposer).curr.address = proposer →
      ∀ (follower ∈ (s.procs proposer).followers),
        (follower = proposer) ∨
        (∃ (e ∈ s.network follower),
          (envelope.msg e) = message.p1b (s.procs proposer).curr none) ∨
        (∃ (e ∈ s.network follower) (prop : proposal pid_t value_t),
          (envelope.msg e) = message.p1b (s.procs proposer).curr (some prop) ∧
          ∃ (stored : proposal pid_t value_t),
            (s.procs proposer).accepted = some stored ∧ prop.bal ≤ stored.bal))
  :=
begin
rw predicate.use_any_invariant,
split,
{ intros s hs proposer __ follower follower_in,
  left,
  have key : (s.procs proposer).followers = {proposer},
  by { specialize hs proposer, unfold protocol.init at hs, injection hs with key, rw ← key },
  rw key at follower_in,
  exact finset.mem_singleton.mp follower_in },
intros u v u_r hu u_pn_v,
rcases (show _, by exact u_pn_v) with ⟨receiver, sender, e, he, deliverable, proc_change, ntwk_change, rest_same⟩,
intros __ proposer, clear __,
cases decidable.em (proposer = receiver),
swap,
{ rw rest_same.left proposer h,
  intros hyp follower is_follower,
  cases hu proposer hyp follower is_follower with is_left is_right,
  { exact or.inl is_left },
  cases is_right with is_middle is_right,
  { right, left,
    rcases is_middle with ⟨e, he, e_is⟩,
    exact ⟨e, sys_state.ntwk_subset he u_pn_v, e_is⟩ },
  right, right,
  rcases is_right with ⟨e, he, e_is⟩,
  exact ⟨e, sys_state.ntwk_subset he u_pn_v, e_is⟩ },
rw h,
clear h proposer,
rw proc_change,
have diff := state_change receiver (u.procs receiver) e.msg sender,
cases diff,
{ rw diff, intros active follower is_follower,
  specialize hu receiver active follower is_follower,
  cases hu,
  { left, exact hu },
  cases hu,
  { rcases hu with ⟨e, he, e_is_1b⟩,
    right, left, exact ⟨e, sys_state.ntwk_subset he u_pn_v, e_is_1b⟩ },
  rcases hu with ⟨e, he, e_is_1b⟩,
  right, right, exact ⟨e, sys_state.ntwk_subset he u_pn_v, e_is_1b⟩ },
cases e,
cases e_msg,
  case p1a : {
    intro unused,
    rw diff.right, clear diff,
    intros follower is_follower,
    exact is_follower.elim
  },
  case p1b : b p_or {
    cases diff,
    { intro unused, rw diff.right, clear diff,
      intros follower is_follower,
      exact is_follower.elim },
    rw (show
      (protocol.handler receiver (u.procs receiver) (message.p1b b p_or) sender).fst.followers
    = (u.procs receiver).followers ∪ {sender},
    by {
      cases diff,
      { rw diff.right.right.right.right },
      rw diff.right.right.right.right.right }),
    rw (show
      (protocol.handler receiver (u.procs receiver) (message.p1b b p_or) sender).fst.curr
    = (u.procs receiver).curr,
    by {
      cases diff,
      { rw diff.right.right.right.right },
      rw diff.right.right.right.right.right }),
    intro hyp,
    have m_bal_is_curr : (u.procs receiver).curr = b, by { cases diff; exact diff.left },
    specialize hu receiver hyp,
    intros follower is_follower,
    rw finset.mem_union at is_follower,
    cases is_follower,
    { cases (hu follower is_follower) with h h,
      { exact or.inl h },
      cases h with h h,
      { right, left,
        rcases h with ⟨e, he, e_is⟩,
        exact ⟨e, sys_state.ntwk_subset he u_pn_v, e_is⟩ },
      right, right,
      rcases h with ⟨e, he, prop, e_is, stored, u_recv_has_stored, stored_ge_prop⟩,
      rcases accepted_ballot_nondecreasing u v u_r u_pn_v u_recv_has_stored
        with ⟨prop_v, stored, new_stored_ge⟩,
      exact ⟨e, sys_state.ntwk_subset he u_pn_v, prop, e_is, prop_v,
            by { rw ← proc_change, exact stored }, le_trans stored_ge_prop new_stored_ge⟩ },
    rw finset.mem_singleton at is_follower,
    rw is_follower,
    right,
    cases p_or,
      case none : {
        left,
        exact ⟨{msg := message.p1b b none, sent_to := e_sent_to},
                sys_state.ntwk_subset he u_pn_v, by { rw m_bal_is_curr }⟩
      },
      case some : p {
        right,
        use {msg := message.p1b b (some p), sent_to := e_sent_to},
        use sys_state.ntwk_subset he u_pn_v,
        use p,
        split,
        { rw m_bal_is_curr },
        rw ← proc_change,
        cases diff,
        { rw proc_change, rw diff.right.right.right.right,
          use {bal := (u.procs receiver).curr,
               val := proposal.value_or_default
                        (proposal.merge (u.procs receiver).accepted (some p))
                        (vals receiver)},
          split,
          { refl },
          rw diff.left,
          apply (current_ge_accepted_ballot u u_r).right sender
                {msg := message.p1b b (some p), sent_to := e_sent_to} he b p,
          refl },
        rw proc_change, rw diff.right.right.right.right.right,
        clear diff,
        exact proposal.merge_ballot_ge_right (u.procs receiver).accepted p
      }
  },
  case p2a : b {
    rw diff.right, clear diff,
    intros hyp follower is_follower,
    exact is_follower.elim
  },
  case p2b : b acc {
    rw diff.right, clear diff,
    intros hyp follower is_follower,
    exact is_follower.elim
  },
  case preempt : {
    rw diff.right, clear diff,
    intros hyp follower is_follower,
    exact is_follower.elim
  },
end

-- quorum_promised says the same fact above but without requiring that the node is active.
def quorum_promised
  (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t))
  (b : ballot pid_t)
  := ∃ promisers, is_quorum promisers ∧
      ∀ (promiser ∈ promisers),
        (promiser = b.address) ∨
        (∃ (e ∈ s.network promiser),
          (envelope.msg e) = message.p1b b none) ∨
        (∃ (e ∈ s.network promiser) (prop : proposal pid_t value_t),
          (envelope.msg e) = message.p1b b (some prop) ∧
          ∃ (stored : proposal pid_t value_t),
            (s.procs b.address).accepted = some stored ∧ prop.bal ≤ stored.bal)

-- This says that when restricted to reachable states, quorum_promised is
-- stable.
private lemma quorum_promised_restricted_stable (b : ballot pid_t) : predicate.stable
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    s.reachable ∧ quorum_promised s b) :=
begin
intros u v,
rintros ⟨u_r, promisers, h_promisers, promisers_satisfies⟩,
intro u_pn_v,
split,
{ cases u_r with u_steps u_reachable_in,
  exact ⟨u_steps.succ, or.inl ⟨u, u_reachable_in, u_pn_v⟩⟩ },
use [promisers, h_promisers],
intros promiser promiser_in,
specialize promisers_satisfies promiser promiser_in,
cases promisers_satisfies,
{ left, exact promisers_satisfies, },
right,
cases promisers_satisfies,
{ left,
  rcases promisers_satisfies with ⟨e, he, e_msg_is⟩,
  exact ⟨e, sys_state.ntwk_subset he u_pn_v, e_msg_is⟩ },
{ right,
  rcases promisers_satisfies with ⟨e, he, prop, e_msg_is, stored, is_stored, ge_proposed⟩,
  use [e, sys_state.ntwk_subset he u_pn_v, prop, e_msg_is],
  rcases accepted_ballot_nondecreasing u v u_r u_pn_v is_stored with ⟨prop_w, w_is_stored, w_larger⟩,
  exact ⟨prop_w, w_is_stored, le_trans ge_proposed w_larger⟩ }
end

-- A proposal may only be issued if a quorum promised to accept the proposal.
theorem proposed_imp_majority_sent_p1b : predicate.invariant
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    ∀ (b : ballot pid_t) (v : value_t), proposed s b v → quorum_promised s b) :=
begin
rw predicate.use_any_invariant,
split,
{ intros s hs b v,
  rintros ⟨proposer, e, he, e_msg_is⟩,
  exact (none_proposed_at_init s hs b proposer ⟨v, e, he, e_msg_is⟩).elim },
intros u w u_r hu u_pn_w w_r b v,
rintros ⟨proposer, y, hy, y_msg_is⟩,
rcases (show _, by exact u_pn_w) with ⟨receiver, sender, e, he, deliverable, proc_change, ntwk_change, proc_same, ntwk_same⟩,
cases decidable.em (proposer = receiver),
swap,
{ rw ntwk_same proposer h at hy,
  specialize hu b v ⟨proposer, y, hy, y_msg_is⟩,
  exact (quorum_promised_restricted_stable b u w ⟨u_r, hu⟩ u_pn_w).right },
clear proc_same ntwk_same,rw ← h at proc_change ntwk_change deliverable,
clear h receiver,
rw ntwk_change at hy,
cases hy,
{ specialize hu b v ⟨proposer, y, hy, y_msg_is⟩,
  exact (quorum_promised_restricted_stable b u w ⟨u_r, hu⟩ u_pn_w).right },
rcases p2a_emitted y_msg_is hy with ⟨p_or, e_msg_is, proposer_bal_address_is, began_no_quorum, ends_w_quorum, y_is⟩,
have conditions : (w.procs proposer).curr = (u.procs proposer).curr ∧ is_quorum (w.procs proposer).followers,
by {
  rw proc_change, rw e_msg_is,
  unfold protocol.handler server.handle_p1b,
  rw if_neg (lt_irrefl _),
  rw if_neg (decidable.not_not.mpr proposer_bal_address_is),
  rw if_neg (lt_irrefl _),
  rw if_neg (show ¬(is_quorum (u.procs proposer).followers ∨
                  sender ∈ (u.procs proposer).followers),
            by {
              intros hyp, cases hyp,
              { exact began_no_quorum hyp },
              have fact : (u.procs proposer).followers ∪ {sender} = (u.procs proposer).followers, by {
                rw finset.union_eq_left_iff_subset,
                rw finset.singleton_subset_iff,
                exact hyp
              },
              rw fact at ends_w_quorum, exact began_no_quorum ends_w_quorum
            }),
  rw if_pos ends_w_quorum,
  split,
  { refl },
  exact ends_w_quorum },
cases conditions with curr_unchanged followers_are_quorum,
use [(w.procs proposer).followers, followers_are_quorum],
have antecedent : (w.procs proposer).curr.address = proposer,
by { rw curr_unchanged, exact proposer_bal_address_is },
suffices : (w.procs proposer).curr = b,
by {
  intros promiser hyp_promiser,
  have key := followers_sent_p1b w w_r proposer antecedent promiser hyp_promiser,
  rw this at key,
  have fact : proposer = b.address, by { rw ← antecedent, rw this },
  rw ← fact,
  exact key
},
rw curr_unchanged,
rw y_is at y_msg_is,
injection y_msg_is with proposals_eq,
injection proposals_eq
end

