# Implementation

This repository separately has an implementation of co-located single-instance
paxos, and a proof of its safety. It suggests that the common combination
outlined in the "Problem" section of the main README is safe.

This proof was written before the guidelines were added, hence the argument may
be hard to read. It also shows some of the downsides of these one-off proofs;
one would need to specify the system state (and in this example, our system
state omits important things like timers), specify the protocol (in this
example, we didn't include heartbeats or even learning when a value is chosen),
so it's hard to see if your specific protocol is safe.

TODO(gnanabit): determine whether the single-instance implementation should be
made public.

TODO(gnanabit): for the proof of safety of the implementation, consider proving
the guidelines instead of doing the entire proof. On the other hand, leaving it
as-is may be useful as an example of the reasoning one would need to go through
to prove the safety of a specific implementation, which may make it clearer why
the guidelines are useful for students.
