import implementation.model.envelope
import implementation.model.target
import implementation.spec.ballot
import implementation.spec.proposal
import implementation.spec.message
import implementation.spec.quorum_assumption

structure server (pid_t : Type) [linear_order pid_t] (value_t : Type)
                 (is_quorum : finset pid_t → Prop) [decidable_pred is_quorum]
                 [quorum_assumption is_quorum] (vals : pid_t → value_t) :=
  (curr : ballot pid_t) (accepted : option (proposal pid_t value_t))
  (followers : finset pid_t)

namespace server

variables {pid_t : Type} [linear_order pid_t] {value_t : Type}
          (is_quorum : finset pid_t → Prop) [decidable_pred is_quorum]
          [quorum_assumption is_quorum] (vals : pid_t → value_t)

def handle_p1a (s : server pid_t value_t is_quorum vals) (sender : pid_t) (b : ballot pid_t) :
  (server pid_t value_t is_quorum vals) × set (envelope pid_t (message pid_t value_t)) :=
if (s.curr < b) then
  -- Start following the ballot b.
  ({curr := b, accepted := s.accepted, followers := ∅},
    {{msg := message.p1b b s.accepted, sent_to := target.just sender}})
else
  -- Explicitly reject the ballot.
  (s, {{msg := message.p1b s.curr s.accepted, sent_to := target.just sender}})

def handle_p1b (s : server pid_t value_t is_quorum vals) (receiver : pid_t) (sender : pid_t)
               (b : ballot pid_t) (p : option (proposal pid_t value_t)) :
  (server pid_t value_t is_quorum vals) × set (envelope pid_t (message pid_t value_t)) :=
if (s.curr < b) then
  -- Rejection of our ballot (or a more recent one than ours); follow the ballot
  -- and send nothing
  ({curr := b, accepted := s.accepted, followers := ∅}, ∅)
else if (s.curr.address ≠ receiver) then
  -- We have already been rejected; nothing to do.
  (s, ∅)
else if (s.curr > b) then
  -- Received p1b is for an old ballot; ignore.
  (s, ∅)
else if (is_quorum s.followers ∨ sender ∈ s.followers) then
  -- we are already leader, or the sender already follows us; ignore.
  (s, ∅)
else if (is_quorum (s.followers ∪ {sender})) then
  -- We have heard P1Bs from a majority of servers (including ourself, even
  -- though we technically didn't send a p1b to ourself). We may therefore
  -- propose a value according to the paxos constraint (if any value was
  -- mentioned by an acceptor, propose the value with the highest ballot). 
  --
  -- In practice we would not send the p2b to ourself, but our implementation
  -- doesn't specify how nodes learn. p2bs are no-ops and we only use them to
  -- say that a quorum voted for the value.
  ({curr := s.curr,
    accepted := some {
      bal := s.curr,
      val := proposal.value_or_default (proposal.merge s.accepted p) (vals receiver) },
    followers := s.followers ∪ {sender}},
    {{msg := message.p2a {
          bal := s.curr,
          val := proposal.value_or_default (proposal.merge s.accepted p) (vals receiver) },
      sent_to := target.exclude receiver},
     {msg := message.p2b s.curr tt,
      sent_to := target.just receiver}})
else
  -- Don't yet have P1Bs from a majority; merge their accepted value and record
  -- they follow us.
  ({curr := s.curr, accepted := proposal.merge s.accepted p,
    followers := s.followers ∪ {sender}}, ∅)

def handle_p2a (s : server pid_t value_t is_quorum vals) (receiver : pid_t) (sender : pid_t)
               (p : proposal pid_t value_t):
  (server pid_t value_t is_quorum vals) × set (envelope pid_t (message pid_t value_t)) :=
if p.bal ≥ s.curr then
  -- We are permitted to accept the p2a, so tell them that we accept and update
  -- our state accordingly.
  ({curr := p.bal, accepted := some p, followers := ∅},
    {{msg := message.p2b p.bal tt, sent_to := target.just sender}})
else
  -- We must reject the message and leave our state unchanged.
  (s, {{msg := message.p2b s.curr ff, sent_to := target.just sender}})

def handle_p2b (s : server pid_t value_t is_quorum vals)
               (b : ballot pid_t):
  (server pid_t value_t is_quorum vals) × set (envelope pid_t (message pid_t value_t)) :=
if b > s.curr then
  -- This is a rejection; start following their ballot.
  ({curr := b, accepted := s.accepted, followers := ∅}, ∅)
else
  -- Not necessarily a rejection; do nothing. In practice, we would check that
  -- the ballot matches ours and that the p2b is an accept; then we'd add
  -- it to a set of servers who voted for our ballot, etc.
  (s, ∅)

def handle_preempt (s : server pid_t value_t is_quorum vals) (receiver : pid_t) :
  (server pid_t value_t is_quorum vals) × set (envelope pid_t (message pid_t value_t)) :=
if s.curr.address = receiver then
  -- We are currently active, so do not try to re-preempt.
  (s, ∅)
else
  -- Start trying to get elected.
  ({curr := ballot.next receiver s.curr, accepted := s.accepted, followers := ∅},
    {{msg := message.p1a (ballot.next receiver s.curr),
      sent_to := target.exclude receiver}})

end server
