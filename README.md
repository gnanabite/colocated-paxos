# Guidelines for Co-Located Paxos

## Goal

To provide a collection of constraints on a co-located paxos-based protocol such
that

- it is reasonable for a student to check that their protocol meets the
  constraints
- the constraints imply that the protocol meets the safety requirement of
  consensus

## Problem

Many papers about Paxos focus on a particular implementation and prove its
correctness. Typically, they describe three separate roles (proposer, acceptor,
and listener), describe the messages that each role sends and receives (and how
the role reacts in respond to the message), and then prove the correctness of
this implementation.  Some examples of this are:

- [Paxos Made Simple](https://lamport.azurewebsites.net/pubs/paxos-simple.pdf)
- [Paxos Made Moderately Complex](https://www.cs.cornell.edu/courses/cs7412/2011sp/paxos.pdf)
- [Formal Verification of Multi-Paxos for Distributed Consensus](https://arxiv.org/pdf/1606.01387.pdf)

However, in many practical implementations, these roles are combined. The Paxos
Made Moderately Complex paper mentions this in the "Colocation"
section. Google's
[description](https://static.googleusercontent.com/media/research.google.com/en//archive/paxos_made_live.pdf)
of their implementation says that the protocol is run with a set of replicas who
may become coordinator, implying that the roles are colocated.

In the University of Washington's CSE 452
[dslabs](https://github.com/emichael/dslabs) assignments, the roles must be
co-located. However, it can be tricky to understand what state is safe to
combine.

To take a concrete example, the 452 section
[slides](https://docs.google.com/presentation/d/1PWlJVWjjVnGwpRDI4JYV5War1FuAkIRUDdTumXUCtoQ/edit#slide=id.gda0ea562cb_0_0)
for Paxos suggest merging logs as you receive them while becoming
leader. Therefore, common combination in 452 implementations is to store only a
single log, and when receiving p1b accept messages from other nodes, the log
from the p1b is merged into the log of the receiver. However, doing this may
mean that a server stores a proposal which it promised not to accept. Hence
without making a change to the definition of "voted", this protocol would no
longer be safe. It turns out that this change is safe as long as you change the
definition of "voted" to be "has sent a p2b message for the ballot", but
reasoning about this is, in my opinition, not trivial -- one needs to basically
redo the entire proof of the safety of Paxos with these new definitions.

With additional concepts like timers, heartbeats, etc., it can be quite tricky
for students to reason about whether their protocol is safe. This explains the
need to meet the goal outlined above.

A **non**-goal of the project is to give constraints that an implementation
*must* meet in order to meet the consensus safety requirement. There are many
consensus algorithms, and Paxos is the only one whose details I am familiar
with. However, I would guess (with no evidence) that most dslabs implementations
of Paxos meet these constraints.

## Approach

This repository has guidelines for both single-instance and multi-instance
paxos.

We describe the files in the `src/guidelines` directory in the order that they
should be read.

`protocol.lean` describes the high-level concept of a "protocol"; it specifies
the initial "system state(s)" and when one system state follows from
another. You might consider it an incredibly basic discussion of [transition
systems](https://courses.cs.washington.edu/courses/cse452/22wi/lecture/L4/). This
does not say anything about Paxos.

`definitions.lean` describes what a system state must have in a "co-located
paxos-like protocol". This includes concepts like current ballots, stored
proposals, definitions of "proposed", "voted", and "quorum". Note that while we
require that these definitions exist, we don't actually make any requirements
about them. For example, we do not say anything about messages; we don't say
anything about how ballots are constructed. We require that ballots are ordered
and that a proposal is a pair of a ballot and a value, but that's about it. From
this, we define "chosen", along with a variety of other definitions which are
useful for the proof.

`requirements.lean` describes the constraints that a protocol should satisfy in
terms of the definitions made for system states. For example, "the current
ballot of a process is nondecreasing", "any stored proposal has been
proposed". It also has some basic consequences of these constraints. Once again,
it doesn't specify a particular implementation -- the definitions of proposed,
voted, ballot, etc., are as general as they were in `definitions.lean`.

`proof.lean` shows that if we have system states that have the definitions in
`definitions.lean`, and if we have a protocol on these system states that
satisfies the requirements outlined in `requirements.lean`, then the resulting
protocol will meet the consensus safety requirements.

`multipaxos.lean` proves the associated results for multipaxos where the same
current ballot is used for all slots. The proof is to show that the
single-instance paxos requirements are met for each slot, hence each slot is
safe.

It's likely this has already been done, but I haven't found a paper or lecture
notes that describes this. If you find one, please feel free to link it.
