import implementation.spec.ballot
import implementation.spec.proposal

-- A message is one of the four types of standard paxos message, or a preempt
-- message.
--
-- Compared to PMMC, a P2B contains a boolean in addition to a ballot to avoid
-- the cycling rejections issue outlined in the end of the CSE 452 Section 5
-- slides. PMMC avoids this issue by providing a different server address for
-- each leader process, but we don't allow this.
--
-- A preempt message is a very dumb timer. It can be delivered at any time to
-- induce a server to try to get itself elected. A server sends a preempt
-- message to itself on init. The idea is that if an elected leader were to die,
-- another server would eventually handle the preempt message to itself, and
-- this server would then be elected.
inductive message (pid_t : Type) [linear_order pid_t] (value_t : Type) : Type
| p1a : ballot pid_t → message
| p1b : ballot pid_t → option (proposal pid_t value_t) → message
| p2a : proposal pid_t value_t → message
| p2b : ballot pid_t → bool → message
| preempt : message
