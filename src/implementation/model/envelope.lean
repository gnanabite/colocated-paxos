import implementation.model.target

-- An envelope represents message contents and receiver of the message.
structure envelope (pid_t : Type) (msg_t : Type) : Type :=
  (msg : msg_t) (sent_to : target pid_t)

namespace envelope

variables {pid_t msg_t : Type}

-- `e.deliverable_to receiver` is the proposition "the message may be
-- delivered to the receiver", meaning that the target of the envelope
-- matches the receiver.
def deliverable_to (e : envelope pid_t msg_t) (receiver : pid_t) : Prop :=
  e.sent_to.matches receiver

end envelope
