"""Shared project constants."""

QUICKCHECK_TACTIC = (
    "unfold_external_all; (first | done | quickcheck "
    "(config := { Quickcheck.Configuration.adaptive with "
    "enableSafeNorm := true, maxSize := 16, quiet := true }))"
)

LEAN_REPL_LINE_OFFSET = 2
