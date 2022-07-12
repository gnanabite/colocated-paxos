import data.fintype.basic
import implementation.model.protocol
import implementation.model.sys_state
import implementation.spec.message
import implementation.spec.server

instance paxos_protocol (pid_t : Type) [linear_order pid_t] [fintype pid_t] (value_t : Type)
                        (is_quorum : finset pid_t → Prop) [decidable_pred is_quorum]
                        [quorum_assumption is_quorum]
                        (vals : pid_t → value_t) :
         protocol pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t) :=
{ init := λ (p : pid_t),
       ({curr := {round := 0, address := p}, accepted := none, followers := {p}},
         {{msg := message.p1a {round := 0, address := p}, sent_to := target.exclude p},
          {msg := message.preempt, sent_to := target.just p}}),
  handler := λ (receiver : pid_t) (s : server pid_t value_t is_quorum vals)
               (m : message pid_t value_t) (sender : pid_t),
             message.cases_on m
               (λ b : ballot pid_t, s.handle_p1a is_quorum vals sender b)
               (λ (b : ballot pid_t) (p : option (proposal pid_t value_t)),
                 s.handle_p1b is_quorum vals receiver sender b p)
               (λ (p : proposal pid_t value_t), s.handle_p2a is_quorum vals receiver sender p)
               (λ (b : ballot pid_t) (unused : bool), s.handle_p2b is_quorum vals b)
               (s.handle_preempt is_quorum vals receiver) }

variables {pid_t : Type} [linear_order pid_t] [fintype pid_t] {value_t : Type}
          {is_quorum : finset pid_t → Prop} [decidable_pred is_quorum]
          [quorum_assumption is_quorum] {vals : pid_t → value_t}

lemma state_change
  (receiver : pid_t) (s : server pid_t value_t is_quorum vals) (m : message pid_t value_t)
  (sender : pid_t) :
  (protocol.handler receiver s m sender).fst = s ∨
  message.cases_on m
    (λ b : ballot pid_t,
      (s.curr < b) ∧ (protocol.handler receiver s m sender).fst = {curr := b, accepted := s.accepted, followers := ∅})
    (λ (b : ballot pid_t) (p_or : option (proposal pid_t value_t)),
      ((s.curr < b) ∧ (protocol.handler receiver s m sender).fst = {curr := b, accepted := s.accepted, followers := ∅})
      ∨ (s.curr = b ∧ b.address = receiver ∧
          ¬is_quorum s.followers ∧
          is_quorum (s.followers ∪ {sender}) ∧
        (protocol.handler receiver s m sender).fst =
          { curr := s.curr,
            accepted := some
              {bal := s.curr,
                val := proposal.value_or_default (proposal.merge s.accepted p_or)
                                                 (vals receiver)},
            followers := s.followers ∪ {sender}})
      ∨ (s.curr = b ∧ b.address = receiver ∧
          ¬is_quorum s.followers ∧ sender ∉ s.followers ∧
          ¬is_quorum (s.followers ∪ {sender}) ∧
        (protocol.handler receiver s m sender).fst =
          { curr := s.curr,
            accepted := proposal.merge s.accepted p_or,
            followers := s.followers ∪ {sender}}))
    (λ (p : proposal pid_t value_t),
      p.bal ≥ s.curr ∧ (protocol.handler receiver s m sender).fst = {curr := p.bal, accepted := some p, followers := ∅})
    (λ (b : ballot pid_t) (unused : bool),
      b > s.curr ∧ (protocol.handler receiver s m sender).fst = {curr := b, accepted := s.accepted, followers := ∅})
    (s.curr.address ≠ receiver ∧ (protocol.handler receiver s m sender).fst = {curr := ballot.next receiver s.curr, accepted := s.accepted, followers := ∅}) :=
begin
unfold protocol.handler,
cases m,
  case p1a : b {
    unfold server.handle_p1a,
    cases decidable.em (s.curr < b) with cond cond,
    { rw if_pos cond, right, exact ⟨cond, by refl⟩ },
    rw if_neg cond, left, refl
  },
  case p1b : b p_or {
    unfold server.handle_p1b,
    cases decidable.em (s.curr < b) with cond cond1,
    { rw if_pos cond, right, left, exact ⟨cond, by refl⟩ },
    rw if_neg cond1,
    cases decidable.em (s.curr.address ≠ receiver) with cond cond2,
    { rw if_pos cond, left, refl},
    rw if_neg cond2,
    rw decidable.not_not at cond2,
    cases decidable.em (s.curr > b) with cond cond3,
    { rw if_pos cond, left, refl},
    rw if_neg cond3,
    have u_receiver_ballot_is_b := eq_of_le_of_not_lt (le_of_not_gt cond3) cond1,
    clear cond1 cond3,
    have b_from_receiver: b.address = receiver, by { rw u_receiver_ballot_is_b at cond2, exact cond2 },
    clear cond2,
    cases decidable.em (is_quorum s.followers ∨ sender ∈ s.followers) with cond cond1,
    { rw if_pos cond, left, refl },
    rw if_neg cond1,
    rw not_or_distrib at cond1,
    cases cond1 with u_not_quorum u_sender_not_voted,
    cases decidable.em (is_quorum (s.followers ∪ {sender}))
      with v_has_quorum v_no_quorum,
    { rw if_pos v_has_quorum,
      right, right, left,
      exact ⟨u_receiver_ballot_is_b, b_from_receiver, u_not_quorum, v_has_quorum, by refl⟩ },
    rw if_neg v_no_quorum, right, right, right,
    exact ⟨u_receiver_ballot_is_b, b_from_receiver, u_not_quorum, u_sender_not_voted, v_no_quorum, by refl⟩
  },
  case p2a : p {
    unfold server.handle_p2a,
    cases decidable.em (p.bal ≥ s.curr) with cond cond,
    { rw if_pos cond, right, exact ⟨cond, by refl⟩ },
    rw if_neg cond, left, refl
  },
  case p2b : b acc {
    unfold server.handle_p2b,
    cases decidable.em (b > s.curr) with cond cond,
    { rw if_pos cond, right, exact ⟨cond, by refl⟩ },
    rw if_neg cond, left, refl
  },
  case preempt : {
    unfold server.handle_preempt,
    cases decidable.em (s.curr.address = receiver) with cond cond,
    { rw if_pos cond, left, refl },
    rw if_neg cond, right,
    exact ⟨cond, by refl⟩
  }
end

lemma network_change
  (receiver : pid_t) (s : server pid_t value_t is_quorum vals) (m : message pid_t value_t)
  (sender : pid_t) :
  ∀ e ∈ (protocol.handler receiver s m sender).snd,
  (message.cases_on m
    (λ b : ballot pid_t,
      (s.curr < b ∧ e = {msg := message.p1b b s.accepted, sent_to := target.just sender}) ∨
      (s.curr ≥ b ∧ e = {msg := message.p1b s.curr s.accepted, sent_to := target.just sender}))
    (λ (b : ballot pid_t) (p_or : option (proposal pid_t value_t)),
      s.curr = b ∧ b.address = receiver ∧
      ¬is_quorum s.followers ∧
      is_quorum (s.followers ∪ {sender}) ∧
      ( e = { msg := message.p2a
          { bal := s.curr,
            val := proposal.value_or_default (proposal.merge s.accepted p_or) (vals receiver)},
            sent_to := target.exclude receiver} ∨
        e = {msg := message.p2b s.curr tt, sent_to := target.just receiver}))
    (λ (p : proposal pid_t value_t),
      (p.bal ≥ s.curr ∧ e = {msg := message.p2b p.bal tt, sent_to := target.just sender}) ∨
      (p.bal < s.curr ∧ e = {msg := message.p2b s.curr ff, sent_to := target.just sender}))
    (λ (b : ballot pid_t) (unused : bool), false)
    (s.curr.address ≠ receiver ∧ e = {msg := message.p1a (ballot.next receiver s.curr), sent_to := target.exclude receiver}) : Prop) :=
begin
unfold protocol.handler,
cases m,
  case p1a : b {
    unfold server.handle_p1a,
    cases decidable.em (s.curr < b) with cond cond,
    { rw if_pos cond, intros e he, left,
      exact ⟨cond, by { rw set.mem_singleton_iff at he, exact he }⟩ },
    rw if_neg cond, intros e he, right,
    exact ⟨le_of_not_gt cond, by { rw set.mem_singleton_iff at he, exact he }⟩
  },
  case p1b : b p_or {
    unfold server.handle_p1b,
    cases decidable.em (s.curr < b) with cond cond1,
    { rw if_pos cond, intros e he, exact he.elim },
    rw if_neg cond1,
    cases decidable.em (s.curr.address ≠ receiver) with cond cond2,
    { rw if_pos cond, intros e he, exact he.elim },
    rw if_neg cond2,
    rw decidable.not_not at cond2,
    cases decidable.em (s.curr > b) with cond cond3,
    { rw if_pos cond, intros e he, exact he.elim },
    rw if_neg cond3,
    have u_receiver_ballot_is_b := eq_of_le_of_not_lt (le_of_not_gt cond3) cond1,
    clear cond1 cond3,
    have b_from_receiver: b.address = receiver, by { rw u_receiver_ballot_is_b at cond2, exact cond2 },
    clear cond2,
    cases decidable.em (is_quorum s.followers ∨ sender ∈ s.followers) with cond cond1,
    { rw if_pos cond, intros e he, exact he.elim },
    rw if_neg cond1,
    rw not_or_distrib at cond1,
    cases cond1 with u_not_quorum u_sender_not_voted,
    cases decidable.em (is_quorum (s.followers ∪ {sender}))
      with v_has_quorum v_no_quorum,
    { rw if_pos v_has_quorum,
      intros e he,
      cases he,
      { exact ⟨u_receiver_ballot_is_b, b_from_receiver, u_not_quorum, v_has_quorum, or.inl he⟩ },
      rw set.mem_singleton_iff at he,
      exact ⟨u_receiver_ballot_is_b, b_from_receiver, u_not_quorum, v_has_quorum, or.inr he⟩ },
    rw if_neg v_no_quorum,
    intros e he, exact he.elim
  },
  case p2a : p {
    unfold server.handle_p2a,
    cases decidable.em (p.bal ≥ s.curr) with cond cond,
    { rw if_pos cond, intros e he, left, rw set.mem_singleton_iff at he, exact ⟨cond, he⟩ },
    rw if_neg cond, intros e he, right, rw set.mem_singleton_iff at he,
    exact ⟨lt_of_not_ge cond, he⟩
  },
  case p2b : b acc {
    unfold server.handle_p2b,
    cases decidable.em (b > s.curr) with cond cond,
    { rw if_pos cond, intros e he, exact he.elim },
    rw if_neg cond, intros e he, exact he.elim
  },
  case preempt : {
    unfold server.handle_preempt,
    cases decidable.em (s.curr.address = receiver) with cond cond,
    { rw if_pos cond, intros e he, exact he.elim },
    rw if_neg cond, intros e he,
    rw set.mem_singleton_iff at he,
    exact ⟨cond, he⟩
  }
end

lemma p1b_emitted {u : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)}
  {receiver sender : pid_t} {m : message pid_t value_t}
  {e : envelope pid_t (message pid_t value_t)} {b_e : ballot pid_t}
  {p_or : option (proposal pid_t value_t)}
  (e_is_promise : e.msg = message.p1b b_e p_or)
  (he : e ∈ (protocol.handler receiver (u.procs receiver) m sender).snd) :
  ∃ b, m = message.p1a b ∧ (u.procs receiver).accepted = p_or ∧
    max (u.procs receiver).curr b = b_e :=
begin
have delta := network_change receiver (u.procs receiver) m sender e he,
cases m,
  case p1a : mb {
    cases delta,
    { use mb,
      split,
      { refl },
      split,
      { rw delta.right at e_is_promise, injection e_is_promise },
      unfold max max_default,
      rw if_neg (not_le_of_gt delta.left),
      rw delta.right at e_is_promise, injection e_is_promise },
    use mb,
    split,
    { refl },
    split,
    { rw delta.right at e_is_promise, injection e_is_promise },
    unfold max max_default,
    rw if_pos delta.left,
    rw delta.right at e_is_promise, injection e_is_promise
  },
  case p1b : mb p_or {
    cases delta.right.right.right.right with e_is e_is;
    rw e_is at e_is_promise;
    injection e_is_promise
  },
  case p2a : p {
    cases delta;
    rw delta.right at e_is_promise;
    injection e_is_promise
  },
  case p2b : {
    exact delta.elim
  },
  case preempt : {
    rw delta.right at e_is_promise,
    injection e_is_promise
  },
end

lemma p2a_emitted {u : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)}
  {receiver sender : pid_t} {m : message pid_t value_t}
  {e : envelope pid_t (message pid_t value_t)} {b : ballot pid_t} {v : value_t}
  (e_is_proposal : e.msg = message.p2a {bal := b, val := v})
  (he : e ∈ (protocol.handler receiver (u.procs receiver) m sender).snd) :
  ∃ (p_or : option (proposal pid_t value_t)),
    m = (message.p1b (u.procs receiver).curr p_or) ∧
    (u.procs receiver).curr.address = receiver ∧
    ¬is_quorum (u.procs receiver).followers ∧
    is_quorum ((u.procs receiver).followers ∪ {sender}) ∧
    e = {msg := message.p2a
              {bal := (u.procs receiver).curr,
               val := proposal.value_or_default (proposal.merge (u.procs receiver).accepted p_or) (vals receiver)},
        sent_to := target.exclude receiver} :=
begin
have delta := network_change receiver (u.procs receiver) m sender e he,
cases m,
  case p1a : mb {
    cases delta;
    rw delta.right at e_is_proposal;
    injection e_is_proposal
  },
  case p1b : mb p_or {
    rcases delta with ⟨delta₁, delta₂, delta₃, delta₄, e_oneof⟩,
    cases e_oneof,
    swap,
    { rw e_oneof at e_is_proposal, injection e_is_proposal },
    use p_or,
    exact ⟨by { rw delta₁ }, by { rw ← delta₁ at delta₂, exact delta₂}, delta₃, delta₄, e_oneof⟩
  },
  case p2a : p {
    cases delta;
    rw delta.right at e_is_proposal;
    injection e_is_proposal
  },
  case p2b : {
    exact delta.elim
  },
  case preempt : {
    rw delta.right at e_is_proposal, injection e_is_proposal
  },
end

lemma p2b_emitted {u : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)}
  {receiver sender : pid_t} {m : message pid_t value_t}
  {e : envelope pid_t (message pid_t value_t)} {b : ballot pid_t}
  (e_is_proposal : e.msg = message.p2b b tt)
  (he : e ∈ (protocol.handler receiver (u.procs receiver) m sender).snd) :
  (∃ (p_or : option (proposal pid_t value_t)),
    m = (message.p1b (u.procs receiver).curr p_or) ∧
    (u.procs receiver).curr.address = receiver ∧
    ¬is_quorum (u.procs receiver).followers ∧
    is_quorum ((u.procs receiver).followers ∪ {sender}) ∧
    e = {msg := message.p2b (u.procs receiver).curr tt, sent_to := target.just receiver}) ∨
  ∃ (p : proposal pid_t value_t), m = message.p2a p ∧ p.bal ≥ (u.procs receiver).curr :=
begin
have delta := network_change receiver (u.procs receiver) m sender e he,
cases m,
  case p1a : mb {
    cases delta;
    rw delta.right at e_is_proposal;
    injection e_is_proposal
  },
  case p1b : mb p_or {
    rcases delta with ⟨delta₁, delta₂, delta₃, delta₄, e_oneof⟩,
    cases e_oneof,
    swap,
    { left,
      exact ⟨p_or, by { rw delta₁ }, by { rw delta₁, exact delta₂ }, delta₃, delta₄, e_oneof⟩ },
    rw e_oneof at e_is_proposal, injection e_is_proposal
  },
  case p2a : p {
    cases delta,
    { right, exact ⟨p, by refl, delta.left⟩ },
    rw delta.right at e_is_proposal,
    injection e_is_proposal with __ true_is_false,
    injection true_is_false
  },
  case p2b : {
    exact delta.elim
  },
  case preempt : {
    rw delta.right at e_is_proposal, injection e_is_proposal
  },
end
