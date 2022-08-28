import guidelines.definitions
import guidelines.protocol
import guidelines.requirements
import data.finset.basic

variables {sys_state_t pid_t ballot_t value_t : Type}
          [linear_order ballot_t] [decidable_eq pid_t]

def safety (proto : protocol sys_state_t) (defs : paxos_defs sys_state_t pid_t ballot_t value_t)
  := proto.invariant (λ state, (∀ v v', defs.chosen state v → defs.chosen state v' → v = v'))

variables {proto : protocol sys_state_t} {defs : paxos_defs sys_state_t pid_t ballot_t value_t}

lemma proposed_higher_than_chosen_has_same_val
  (reqs_sat : requirements proto defs) : proto.invariant (λ state,
    ∀ b v,
      defs.chosen_ballot state b → defs.proposed state b v →
      ∀ (b' > b) v', defs.proposed state b' v' → v = v') :=
begin
suffices fact : proto.invariant
  (λ state, ∀ b v,
    defs.choosable state b → defs.proposed state b v →
      ∀ (b' > b) v', defs.proposed state b' v' → v = v'),
by {
  intros state state_r b v cond,
  exact fact state state_r b v (defs.chosen_imp_choosable cond)
},
rw protocol.prove_invariant,
split,
{ intros s s_init b v __ proposed_s_b_v,
  exfalso, exact reqs_sat.none_proposed_at_init s b v s_init proposed_s_b_v },
intros u u_reachable w inv_at_u u_n_w b v b_choosable
  b_v_proposed_at_w b' b'_gt_b v' b'_v'_proposed_at_w,

have b_choosable_at_u : defs.choosable u b, by {
  rcases b_choosable with ⟨q, q_quorum, all_q_voted_or_may_vote⟩,
  use [q, q_quorum],
  intros voter voter_in_q, specialize all_q_voted_or_may_vote voter voter_in_q,
  cases all_q_voted_or_may_vote with voted_in_w curr_in_w_le_b,
  { exact reqs_sat.new_votes_ge_curr_ballot voter b w u u_reachable u_n_w voted_in_w },
  right, exact le_trans (reqs_sat.curr_increases voter w u u_reachable u_n_w) curr_in_w_le_b
},

specialize inv_at_u b v b_choosable_at_u,

rcases reqs_sat.at_most_one_proposal_per_step w u u_reachable u_n_w with ⟨bp, vp, hyp⟩,
cases hyp b' v' b'_v'_proposed_at_w,
{ have b_v_proposed : defs.proposed u b v, by {
    rcases reqs_sat.at_most_one_proposal_per_step w u u_reachable u_n_w with ⟨b_p, v_p, fact⟩,
    cases fact b' v' b'_v'_proposed_at_w with fact_prime fact_prime,
    { clear fact,
      rcases reachable_implies_reachable_in_proto_with_intervals_recorded defs proto u u_reachable
        with ⟨lift_u, lift_u_reachable, lift_u_is_lift⟩,
      have key := reqs_sat.majority_have_upper_interval_if_proposed b' v' lift_u lift_u_reachable,
      rw lift_u_is_lift at key,
      specialize key fact_prime,
      rcases key with ⟨q, promised, q_quorum, all_quorum_promised, rest⟩, clear rest,
      rcases b_choosable_at_u with ⟨q', q'_quorum, all_q'_may_vote⟩,
      rcases reqs_sat.quorums_intersect q q' q_quorum q'_quorum with ⟨a, a_in_both⟩,
      rw finset.mem_inter at a_in_both, cases a_in_both with a_promised a_may_vote,
      specialize all_quorum_promised a a_promised,
      specialize all_q'_may_vote a a_may_vote,
      cases all_q'_may_vote with h impossible,
      { rcases reqs_sat.voted_imp_proposed a b u u_reachable h with ⟨v'', hv''⟩,
        have vals_eq := reqs_sat.proposals_unique b v v'' w
          (by { cases u_reachable with k hk, exact ⟨k.succ, u, hk, u_n_w⟩}) b_v_proposed_at_w
          (reqs_sat.proposed_stable b v'' u w hv'' u_n_w),
        rw vals_eq, exact hv'' },
      rw ← lift_u_is_lift at impossible,
      have := le_trans
        (reqs_sat.all_upper_le_curr a lift_u lift_u_reachable
           {upper := b', lower := promised a} all_quorum_promised b' (by refl))
        impossible,
      exact absurd this (not_le_of_lt b'_gt_b) },
    cases fact b v b_v_proposed_at_w with fact_orig fact_orig,
    { exact fact_orig },
    exact absurd (eq.trans fact_orig.left (eq.symm fact_prime.left)) (ne_of_lt b'_gt_b) },
  exact inv_at_u b_v_proposed b' b'_gt_b v' h },
rw ← h.left at hyp, rw ← h.right at hyp, clear h bp vp,

have w_reachable : proto.reachable w,
by { rcases u_reachable with ⟨k, hk⟩, exact ⟨k.succ, u, hk, u_n_w⟩ },

rcases reachable_implies_reachable_in_proto_with_intervals_recorded defs proto w w_reachable
      with ⟨lift_w, lift_w_reachable, lift_w_is_lift⟩,

have key := reqs_sat.majority_have_upper_interval_if_proposed b' v' lift_w lift_w_reachable,
rw lift_w_is_lift at key,
specialize key b'_v'_proposed_at_w,
rcases key with ⟨q, promised, q_quorum, promised_is_lower_endpoint,
                    promised_lt_b', v'_is_max_val⟩,
rcases b_choosable with ⟨q', q'_quorum, q'_can_vote⟩,
rcases reqs_sat.quorums_intersect q q' q_quorum q'_quorum with ⟨a, a_in_both⟩,
rw finset.mem_inter at a_in_both,
cases a_in_both with a_promised a_voted,
specialize q'_can_vote a a_voted, clear a_voted q_quorum q'_quorum,
have a_voted : defs.voted w a b, by {
  cases q'_can_vote,
  { exact q'_can_vote },
  have key := reqs_sat.all_upper_le_curr a lift_w lift_w_reachable
    {upper := b', lower := promised a} (promised_is_lower_endpoint a a_promised) b' (by refl),
  rw lift_w_is_lift at key,
  exact absurd (le_trans key q'_can_vote) (not_le_of_lt b'_gt_b)
}, clear q'_can_vote q',


have key := reqs_sat.none_voted_in_interval a b lift_w lift_w_reachable {upper := b', lower := promised a} (promised_is_lower_endpoint a a_promised),
rw lift_w_is_lift at key,
specialize key a_voted,
cases key, swap,
{ exact absurd b'_gt_b (not_lt_of_le key) },
rcases key with ⟨prop_a, prop_a_is_lower, prop_a_bal_ge_b⟩,
unfold interval.lower at prop_a_is_lower,

cases v'_is_max_val with impossible,
{ specialize impossible a a_promised, rw prop_a_is_lower at impossible, injection impossible },

rcases v'_is_max_val
  with ⟨max, max_in_quorum, p_max, p_max_is_prop_for_max, p_max_highest_bal, p_max_v_is_v'⟩,
specialize p_max_highest_bal a a_promised prop_a prop_a_is_lower,
specialize promised_lt_b' max max_in_quorum p_max p_max_is_prop_for_max,

have p_max_proposed_at_w : defs.proposed w p_max.b p_max.v, by {
  specialize promised_is_lower_endpoint max max_in_quorum,
  rw p_max_is_prop_for_max at promised_is_lower_endpoint,
  have := reqs_sat.all_lower_proposed max lift_w lift_w_reachable {upper := b', lower := some p_max} promised_is_lower_endpoint p_max (by refl),
  rw lift_w_is_lift at this, exact this
},

cases le_iff_lt_or_eq.mp (le_trans prop_a_bal_ge_b p_max_highest_bal) with is_lt is_eq, swap,
{ rw ← is_eq at p_max_proposed_at_w,
  have := reqs_sat.proposals_unique b v p_max.v w w_reachable b_v_proposed_at_w p_max_proposed_at_w,
  exact eq.trans this p_max_v_is_v' },

specialize inv_at_u
  (by { cases (hyp b v b_v_proposed_at_w) , { exact h }, exact absurd h.left (ne_of_lt b'_gt_b) }),
specialize inv_at_u p_max.b is_lt p_max.v,
specialize inv_at_u
  (by { cases (hyp p_max.b p_max.v p_max_proposed_at_w), { exact h }, exact absurd h.left (ne_of_lt promised_lt_b') }),

exact eq.trans inv_at_u p_max_v_is_v'
end

theorem requirements_give_safety : requirements proto defs → safety proto defs :=
begin
intro reqs_sat,
intros s reach_s v v' v_chosen v'_chosen,
rcases v_chosen with ⟨b, b_chosen, b_v_prop⟩,
rcases v'_chosen with ⟨b', b'_chosen, b'_v'_prop⟩,
cases lt_trichotomy b b' with is_lt is_eq_or_is_lt,
{ exact proposed_higher_than_chosen_has_same_val reqs_sat s reach_s b v b_chosen b_v_prop b' is_lt v' b'_v'_prop },
cases is_eq_or_is_lt with is_eq is_lt,
{ apply reqs_sat.proposals_unique b v v' s reach_s b_v_prop,
  rw is_eq, exact b'_v'_prop },
exact eq.symm (proposed_higher_than_chosen_has_same_val reqs_sat s reach_s b' v' b'_chosen b'_v'_prop b is_lt v b_v_prop)
end
