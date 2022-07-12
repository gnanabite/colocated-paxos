import implementation.model.predicate
import implementation.model.sys_state
import implementation.spec.main

variables {pid_t : Type} [linear_order pid_t] [fintype pid_t] {value_t : Type}
          {is_quorum : finset pid_t → Prop} [decidable_pred is_quorum]
          [quorum_assumption is_quorum] {vals : pid_t → value_t}

-- For each process, the current ballot will never decrease when taking a step.
lemma ballot_nondecreasing
  {u v : sys_state pid_t (server pid_t value_t is_quorum vals) (message pid_t value_t)}
  (p : pid_t) : u.possible_next v → (u.procs p).curr ≤ (v.procs p).curr :=
begin
rintros ⟨receiver, sender, e, he, deliverable, proc_change, ntwk_change, procs_same, ntwks_same⟩,
cases decidable.em (p = receiver),
swap,
{ rw procs_same p h },
rw h, clear h p procs_same ntwks_same ntwk_change,
rw proc_change,
have key := state_change receiver (u.procs receiver) e.msg sender,
cases key,
{ rw key },
cases e.msg,
  case p1a : b {
    rw key.right, exact le_of_lt key.left
  },
  case p1b : b p_or {
    cases key,
    { rw key.right, exact le_of_lt key.left },
    cases key,
    { rw key.right.right.right.right },
    rw key.right.right.right.right.right
  },
  case p2a : pr {
    rw key.right, exact key.left
  },
  case p2b : b accepted {
    rw key.right, exact le_of_lt key.left
  },
  case preempt : {
    rw key.right,
    exact le_of_lt (ballot.next_larger receiver (u.procs receiver).curr)
  }
end
