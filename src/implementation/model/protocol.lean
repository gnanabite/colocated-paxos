import implementation.model.envelope

-- A protocol specifies how the processes in a system respond to messages.
--
-- It must provide `init`, which specifies is how each process in the system is
-- initialized, and `handler`, which specifies how processes respond to
-- messages.
--
-- The argument to `init` is the pid of the process being initialized.
--
-- The arguments to handler are in the following order: receiver pid, receiver
-- state when receiving message, message delivered, sender of message.
--
-- The return values for both methods are pairs; the first element is the
-- resulting state of the process; the second element is the set of messages
-- sent by the process (as envelopes).
class protocol (pid_t : Type) (pstate_t : Type) (msg_t : Type) :=
  (init : pid_t → (pstate_t × set (envelope pid_t msg_t)))
  (handler : pid_t → pstate_t → msg_t → pid_t → (pstate_t × set (envelope pid_t msg_t)))

-- NOTE(gnanabit): it would probably be more general to first define a system
-- state, and then define protocol with two fields: (i) a predicate which says
-- whether a sys_state can be an initial state, and (ii) a relation on
-- sys_states which says whether we can transition from one state to
-- another. However, this definition is enough for our purposes.
