import implementation.model.predicate
import implementation.spec.main
import implementation.proof.misc
import implementation.proof.proposer
import implementation.proof.voter
import implementation.proof.acceptor_voter_relation

-- This file contains the proof of the safety of the paxos algorithm.
--
-- In the spirit of Paxos Made Simple, it may help to read comments from the
-- bottom (the main proof) to the top.

variables {pid_t : Type} [linear_order pid_t] [fintype pid_t] {value_t : Type}
          {is_quorum : finset pid_t → Prop} [decidable_pred is_quorum]
          [quorum_assumption is_quorum] {vals : pid_t → value_t}

def choosable
  (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t))
  (b : ballot pid_t) :=
  ∃ (possible_voters : finset pid_t), is_quorum possible_voters ∧
     ∀ voter ∈ possible_voters, voted_ballot s voter b ∨ (s.procs voter).curr ≤ b

def chosen_ballot
  (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t))
  (b : ballot pid_t) :=
  ∃ (voters : finset pid_t), is_quorum voters ∧
     ∀ voter ∈ voters, voted_ballot s voter b

def chosen
  (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t))
  (v : value_t) :=
  ∃ (b : ballot pid_t), proposed s b v ∧ chosen_ballot s b

def safety
  (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)) :=
  ∀ (v v' : value_t), chosen s v → chosen s v' → v = v'

lemma chosen_imp_choosable
  {s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)}
  {b : ballot pid_t}:
  chosen_ballot s b → choosable s b :=
begin
rintros ⟨voters, quorum, all_voted⟩,
exact ⟨voters, quorum, by { intros voter hyp_voter, left, exact all_voted voter hyp_voter }⟩
end

-- This shows that choosable is reverse stable. Choosable is definitely not
-- stable: the ballot on a server in the quorum may increase above the ballot in
-- question for choosability.
lemma choosable_reverse_stable
  {u w : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)}
  {b : ballot pid_t}:
  u.possible_next w → choosable w b → choosable u b :=
begin
intro u_pn_w,
rcases (show _, by exact u_pn_w) with ⟨receiver, sender, e, he, deliverable, proc_change, ntwk_change, proc_same, ntwk_same⟩,
rintros ⟨possible_voter, quorum, may_vote_at_w⟩,
use [possible_voter, quorum],
intros voter h_voter,
specialize may_vote_at_w voter h_voter,
cases may_vote_at_w,
swap,
{ right, exact le_trans (ballot_nondecreasing voter u_pn_w) may_vote_at_w },
rcases may_vote_at_w with ⟨v, hv, v_is_vote⟩,
cases decidable.em (voter = receiver),
swap,
{ rw ntwk_same voter h at hv,
  left, exact ⟨v, hv, v_is_vote⟩ },
clear proc_same ntwk_same,
rw ← h at proc_change ntwk_change deliverable,
clear h receiver,
rw ntwk_change at hv,
cases hv,
{ left, exact ⟨v, hv, v_is_vote⟩ },
cases p2b_emitted v_is_vote hv with proposal_step acceptor_step,
{ right, apply le_of_eq,
  rcases proposal_step with ⟨_, _, _, _, _, v_is⟩,
  rw v_is at v_is_vote,
  injection v_is_vote },
right,
rcases acceptor_step with ⟨p, e_is_proposal, prop_bal_larger⟩,
suffices : p.bal = b, by { rw this at prop_bal_larger, exact prop_bal_larger },
rw e_is_proposal at hv,
unfold protocol.handler server.handle_p2a at hv,
rw [if_pos prop_bal_larger, set.mem_singleton_iff] at hv,
rw hv at v_is_vote,
injection v_is_vote
end

-- It's tricky to prove that any value proposed under a higher ballot than a
-- chosen ballot has the same value as the one proposed with the chosen ballot,
-- because a lower ballot may be chosen after a proposal is issued (there's a
-- relatively straightforward example with 3 servers, which I omit at least for now).
--
-- Instead, we prove that at every state, if a ballot b *may* be chosen and the
-- ballot has been proposed with value v, then any value v' proposed with a
-- ballot b' > b satisfies v' = v. This idea of "may be chosen" is called
-- `choosable` above; it says that there's a quorum where each server in the
-- quorum has either already voted for b or is not yet prohibited from voting for b.
--
-- We then use induction with all invariants we have proven so far. At a high
-- level, here is the idea.
--
-- In the base case, nothing is proposed, so there is nothing to prove.
--
-- In the inductive step, we have states u and w where u can transition to w; we
-- assume b is choosable at w, that b v is proposed at w, and that b' > b and
-- (b', v') is also proposed at w.  Choosability is "reverse stable" -- the
-- choosability of b at w implies that b was also choosable at u. On the other
-- hand, since (b', v') was proposed at w, the proposer of b' must have
-- communicated with a quorum who sent back p1bs with ballot b' -- in fact, this
-- must have happened by state u. Every member of this quorum has ballot at
-- least b' > b in state u, so one of them must have voted for b (as otherwise
-- they would all be prohibited from voting for b). This server's p1b must
-- reflect the proposal (b, v), so the proposer of b', having heard and merged
-- this p1b, will end up with a stored proposal with ballot b'' at least b. As
-- this proposal was issued, b'' must have been proposed with value v, so b' is
-- proposed with value v; hence v = v'.
lemma proposed_higher_than_chosen_has_same_val : predicate.invariant
  (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
    ∀ (b : ballot pid_t) (v : value_t),
      chosen_ballot s b → proposed s b v →
      ∀ (b' > b) (v' : value_t),
        proposed s b' v' → v = v') :=
begin
suffices fact : ∀ (b₁ : ballot pid_t) (v₁ : value_t), predicate.invariant
    (λ (s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)),
      choosable s b₁ →
        proposed s b₁ v₁ →
         ∀ (b₂ : ballot pid_t), b₂ > b₁ → ∀ (v₂ : value_t), proposed s b₂ v₂ → v₁ = v₂),
by { intros s s_r b₁ v₁ cond, exact fact b₁ v₁ s s_r (chosen_imp_choosable cond) },
intros b₁ v₁,
rw predicate.use_any_invariant,
split,
{ intros s hs __,
  rintros ⟨proposer, proposed_by_proposer⟩,
  exfalso,
  exact none_proposed_at_init s hs b₁ proposer ⟨v₁, proposed_by_proposer⟩ },
intros u w u_r hu u_pn_w w_r b₁_choosable_w b₁_v₁_proposed_w b₂ ballot_order v₂ b₂_v₂_proposed_w,
rcases (show _, by exact u_pn_w) with
  ⟨receiver, sender, e, he, deliverable, proc_change, ntwk_change, procs_same, ntwks_same⟩,
have b₁_choosable : choosable u b₁ := choosable_reverse_stable u_pn_w b₁_choosable_w,
have already_proposed_or_currently_proposed : proposed u b₂ v₂ ∨ ∃ e' ∈ (protocol.handler receiver (u.procs receiver) e.msg sender).snd, (envelope.msg e') = message.p2a {bal := b₂, val := v₂},
by {
  rcases b₂_v₂_proposed_w with ⟨proposer, e', he', e'_msg_is⟩,
  cases decidable.em (proposer = receiver),
  swap,
  { left, rw ntwks_same proposer h at he',
    exact ⟨proposer, e', he', e'_msg_is⟩ },
  rw h at he', clear h proposer,
  rw ntwk_change at he',
  cases he',
  { left, exact ⟨receiver, e', he', e'_msg_is⟩ },
  right, exact ⟨e', he', e'_msg_is⟩,
},
cases already_proposed_or_currently_proposed with b₂_v₂_proposed just_emitted,
{ clear proc_change ntwk_change procs_same ntwks_same he deliverable e,
  suffices b₁_v₁_proposed : proposed u b₁ v₁,
  by { exact hu b₁_choosable b₁_v₁_proposed b₂ ballot_order v₂ b₂_v₂_proposed },
  rcases proposed_imp_majority_sent_p1b u u_r b₂ v₂ b₂_v₂_proposed
    with ⟨promisers, promisers_are_quorum, promisers_made_promise⟩,
  rcases b₁_choosable
    with ⟨possible_voters, possible_voters_are_quorum, possible_voters_may_vote⟩,
  rcases quorum_assumption.intersect promisers possible_voters promisers_are_quorum possible_voters_are_quorum with ⟨a, a_in_inter⟩,
  rw finset.mem_inter at a_in_inter, cases a_in_inter with a_promised a_may_vote,
  specialize possible_voters_may_vote a a_may_vote,
  cases possible_voters_may_vote,
  { rcases voted_imp_proposed a b₁ u u_r possible_voters_may_vote with ⟨v', v'_proposed_u⟩,
    rw proposals_unique w w_r b₁ v₁ v' b₁_v₁_proposed_w (proposed_stable b₁ v' u w v'_proposed_u u_pn_w),
    exact v'_proposed_u },
  specialize promisers_made_promise a a_promised,
  exfalso,
  apply not_le_of_gt ballot_order,
  suffices : b₂ ≤ (u.procs a).curr,
  by { exact le_trans this possible_voters_may_vote },
  cases promisers_made_promise,
  { rw promisers_made_promise,
    apply proposer_ballot_ge u u_r b₂ b₂.address,
    rcases b₂_v₂_proposed with ⟨p, proposed_by_p⟩,
    rw proposer_is_ballot_address u u_r b₂ p ⟨v₂, proposed_by_p⟩,
    exact ⟨v₂, proposed_by_p⟩ },
  have fact : ∃ (e ∈ u.network a) p_or, envelope.msg e = message.p1b b₂ p_or, by {
    cases promisers_made_promise,
    { rcases promisers_made_promise with ⟨e, he, e_is⟩,
      exact ⟨e, he, none, e_is⟩ },
    rcases promisers_made_promise with ⟨e, he, prop, e_is, _⟩,
    exact ⟨e, he, some prop, e_is⟩ },
  rcases fact with ⟨e, he, p_or, e_promises_p_or⟩,
  exact ballot_ge_any_promised a b₂ p_or u u_r ⟨e, he, e_promises_p_or⟩ },
rcases just_emitted with ⟨ep, h_ep, ep_is_proposal⟩,
rcases p2a_emitted ep_is_proposal h_ep with ⟨acked_p_or, e_msg_eq, active, __, v_has_quorum, ep_is⟩, clear __,
have b₁_v₁_proposed : proposed u b₁ v₁,
by {
  rcases b₁_v₁_proposed_w with ⟨proposer, ep1, h_ep1, ep1_is_prop⟩,
  cases decidable.em (proposer = receiver) with cond cond,
  swap,
  { rw ntwks_same proposer cond at h_ep1,
    exact ⟨proposer, ep1, h_ep1, ep1_is_prop⟩ },
  rw cond at h_ep1, clear cond proposer,
  rw ntwk_change at h_ep1,
  cases h_ep1,
  { exact ⟨receiver, ep1, h_ep1, ep1_is_prop⟩ },
  rcases p2a_emitted ep1_is_prop h_ep1 with ⟨acked_p1_or, p1_or_cond, _, _, _, ep1_is⟩,
  have fact : acked_p_or = acked_p1_or, by { rw e_msg_eq at p1_or_cond, injection p1_or_cond },
  rw ep_is at ep_is_proposal,
  rw ep1_is at ep1_is_prop,
  rw fact at ep_is_proposal,
  injection eq.trans (eq.symm ep1_is_prop) ep_is_proposal with props_same,
  injection props_same with ballots_same,
  exfalso, exact (ne_of_lt ballot_order) ballots_same
},
suffices : v₁ = proposal.value_or_default (proposal.merge (u.procs receiver).accepted acked_p_or)
                                (vals receiver),
by {
  rw this,
  rw ep_is at ep_is_proposal,
  injection ep_is_proposal with proposals_match,
  injection proposals_match
},
suffices : ∃ stored, (proposal.merge (u.procs receiver).accepted acked_p_or) = some stored ∧ stored.val = v₁,
by {
  rcases this with ⟨stored, merge_eq, merged_val⟩,
  rw merge_eq,
  unfold proposal.value_or_default,
  exact eq.symm merged_val
},
suffices : ∃ stored, (proposal.merge (u.procs receiver).accepted acked_p_or) = some stored ∧ stored.bal ≥ b₁,
by {
  rcases this with ⟨stored, merge_eq, stored_bal_larger⟩,
  use [stored, merge_eq],
  cases proposal.merge_is_one_of (u.procs receiver).accepted acked_p_or with is_from is_from;
  rw is_from at merge_eq,
  { have stored_proposed_at_u := (accepted_means_issued u u_r).left receiver stored merge_eq,
    cases le_iff_lt_or_eq.mp stored_bal_larger,
    { specialize hu b₁_choosable b₁_v₁_proposed stored.bal h stored.val stored_proposed_at_u,
      exact eq.symm hu },
    rw h at b₁_v₁_proposed_w,
    exact proposals_unique w w_r stored.bal stored.val v₁ (proposed_stable stored.bal stored.val u w stored_proposed_at_u u_pn_w) b₁_v₁_proposed_w },
  have stored_proposed_at_u : proposed u stored.bal stored.val, by
  { apply (accepted_means_issued u u_r).right sender e he (u.procs receiver).curr stored,
    rw e_msg_eq, rw merge_eq },
  cases le_iff_lt_or_eq.mp stored_bal_larger,
  { specialize hu b₁_choosable b₁_v₁_proposed stored.bal h stored.val stored_proposed_at_u,
    exact eq.symm hu },
  rw h at b₁_v₁_proposed_w,
  exact proposals_unique w w_r stored.bal stored.val v₁ (proposed_stable stored.bal stored.val u w stored_proposed_at_u u_pn_w) b₁_v₁_proposed_w
},
have u_curr_ballot_is_b₂: (u.procs receiver).curr = b₂, by {
  rw ep_is at ep_is_proposal,
  injection ep_is_proposal with proposals_eq,
  injection proposals_eq
},
clear ep_is ep_is_proposal h_ep ep procs_same ntwks_same,
rcases b₁_choosable with ⟨poss_voters, poss_voters_quorum, all_voted_or_may_vote⟩,
rcases quorum_assumption.intersect poss_voters ((u.procs receiver).followers ∪ {sender}) poss_voters_quorum v_has_quorum with ⟨a, a_in_both⟩,
rw finset.mem_inter at a_in_both,
cases a_in_both with a_is_possible_voter a_is_follower,
specialize all_voted_or_may_vote a a_is_possible_voter, clear a_is_possible_voter,
rw finset.mem_union at a_is_follower,
clear poss_voters_quorum poss_voters,
cases a_is_follower,
swap,
{ rw finset.mem_singleton at a_is_follower,
  cases all_voted_or_may_vote with voted impossible,
  { rw ← a_is_follower at he,
    cases none_voted_between_p1b u u_r a b₁ (u.procs receiver).curr acked_p_or voted
                                 ⟨e, he, e_msg_eq⟩,
    { rw u_curr_ballot_is_b₂ at h, exact (not_le_of_lt ballot_order h).elim, },
    rcases h with ⟨p, ack_eq, p_bal_ge⟩,
    rw ack_eq,
    rcases proposal.merge_ballot_ge_right (u.procs receiver).accepted p
      with ⟨stored, stored_eq, stored_ge⟩,
    exact ⟨stored, stored_eq, le_trans p_bal_ge stored_ge⟩ },
  exfalso,
  have key := ballot_ge_any_promised sender (u.procs receiver).curr acked_p_or u u_r ⟨e, he, e_msg_eq⟩,
  rw a_is_follower at impossible,
  rw u_curr_ballot_is_b₂ at key,
  exact not_le_of_lt ballot_order (le_trans key impossible) },
have fact := followers_sent_p1b u u_r receiver active a a_is_follower,
clear a_is_follower,
cases fact,
{ rw fact at all_voted_or_may_vote, clear fact a,
  cases all_voted_or_may_vote with voted impossible,
  { rcases accepted_ge_any_voted receiver b₁ u u_r voted
      with ⟨old_stored, old_stored_eq, old_stored_ge⟩,
    rw old_stored_eq, clear old_stored_eq,
    rcases proposal.merge_ballot_ge_left old_stored acked_p_or
      with ⟨stored, stored_eq, stored_ge⟩,
    exact ⟨stored, stored_eq, le_trans old_stored_ge stored_ge⟩ },
  rw u_curr_ballot_is_b₂ at impossible,
  exfalso,
  exact not_le_of_lt ballot_order impossible },
cases fact,
{ exfalso,
  cases all_voted_or_may_vote with impossible impossible,
  { cases none_voted_between_p1b u u_r a b₁ (u.procs receiver).curr none impossible fact,
    { rw u_curr_ballot_is_b₂ at h,
      exact not_le_of_lt ballot_order h },
    rcases h with ⟨_, bad, _⟩, injection bad },
  have key := ballot_ge_any_promised a (u.procs receiver).curr none u u_r fact,
  rw u_curr_ballot_is_b₂ at key,
  exact not_le_of_lt ballot_order (le_trans key impossible) },
rcases fact with ⟨e', he', prop, e'_msg_eq, old_stored, accepted_eq_old_stored, old_stored_ge⟩,
rw accepted_eq_old_stored,
cases all_voted_or_may_vote with voted impossible,
{ cases none_voted_between_p1b u u_r a b₁ (u.procs receiver).curr (some prop) voted ⟨e', he', e'_msg_eq⟩,
  { rw u_curr_ballot_is_b₂ at h,
    exact (not_le_of_lt ballot_order h).elim },
  rcases h with ⟨p, p_eq_prop_tmp, p_ge_bal⟩,
  have p_eq_prop : prop = p, by { injection p_eq_prop_tmp },
  rw ← p_eq_prop at p_ge_bal,
  clear p_eq_prop_tmp p_eq_prop p,
  rcases proposal.merge_ballot_ge_left old_stored acked_p_or
    with ⟨stored, stored_eq, ge_old_stored⟩,
  exact ⟨stored, stored_eq, le_trans p_ge_bal (le_trans old_stored_ge ge_old_stored)⟩ },
exfalso,
have key := ballot_ge_any_promised a (u.procs receiver).curr (some prop) u u_r ⟨e', he', e'_msg_eq⟩,
rw u_curr_ballot_is_b₂ at key,
exact not_le_of_lt ballot_order (le_trans key impossible)
end

-- The safety of paxos: if two values are chosen at a state, then both values are the same.
--
-- The argument is as follows: the values are chosen because two proposals are
-- chosen. If the proposals have the same ballot, then they have the same value
-- and we are done.
--
-- So assume they don't have the same ballot; then all we need to show is that
-- if two proposals are chosen and one has a higher ballot than the other, then
-- the two proposals have the same value. To do that, it suffices to show that
-- if b < b' are ballots proposed with values v and v', and ballot b is chosen,
-- then v = v' (regardless of whether ballot b' is chosen). This is shown in
-- proposed_higher_than_chosen_has_same_val.
theorem at_most_one_value_chosen : predicate.invariant
  (λ s : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t),
    safety s) :=
begin
intros u u_r v v',
rintros ⟨b, proposed_b_v, chosen_b⟩,
rintros ⟨b', proposed_b'_v', chosen_b'⟩,
cases lt_trichotomy b b' with b_lt_b' b_ge_b',
swap,
cases b_ge_b' with b_eq_b' b_gt_b',
{ have proposed_b_v' : proposed u b v', by { rw b_eq_b', exact proposed_b'_v' },
  exact proposals_unique u u_r b v v' proposed_b_v proposed_b_v' },
swap,
{ exact proposed_higher_than_chosen_has_same_val
        u u_r b v chosen_b proposed_b_v b' b_lt_b' v' proposed_b'_v' },
symmetry,
exact proposed_higher_than_chosen_has_same_val
      u u_r b' v' chosen_b' proposed_b'_v' b b_gt_b' v proposed_b_v
end
