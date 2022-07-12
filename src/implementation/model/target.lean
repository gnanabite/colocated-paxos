-- A target specifies all `pid_t`s that may receive a message.
--
-- Messages may be sent to all processes (corresponding to `target.all`) or to
-- just one process (corresponding to `target.just p` where `p` is the `pid_t`
-- of the receiving process)
inductive target (pid_t : Type) : Type
| just : pid_t → target
| exclude : pid_t → target

namespace target

variable {pid_t : Type}

-- If `t` is a `target pid_t` and `p` is a `pid_t`, then `t.matches p` is the
-- proposition that "t specifies p as a receiver".
def matches : target pid_t → pid_t → Prop
| (just p₀)    p := p₀ = p
| (exclude p₀) p := p₀ ≠ p

end target

lemma just_self_matches {pid_t : Type} (p : pid_t) : (target.just p).matches p :=
begin
exact eq.refl p
end
