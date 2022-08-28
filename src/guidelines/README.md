# TODOs

- `majority_have_upper_interval_if_proposed` might be somewhat confusing.
- Put this in a format which is readable for students. Lean is unlikely to be
  understood by most students. I also don't have much Lean experience, so the
  raw proofs may not be very helpful even for folks who can read it.
  - One option: a simple lean-to-text variant of definitions.lean and
    requirements.lean. These text variants perhaps don't need to be as
    precise. For example, rather than carefully describing a "protocol with
    interval history", we could say "if at some point in the past, this server
    stored proposal `p` and had current ballot `b`, then..."
