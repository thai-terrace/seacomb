# Changelog

All notable changes to this crate are documented here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

## [0.2.0] - 2026-09-24

### Changed

- API improvements:
  - Add `Filter::add_rule_exact`, which matches only the syscall's own number
    and not its x86 `socketcall`/`ipc` multiplexed form. `Rule` gains a
    `no_mux` field for this.
  - Error types now implement `std::error::Error` via `thiserror` and are
    `#[non_exhaustive]`. `Error::InvalidErrno` carries the rejected value.
  - New errors: `Error::InvalidMuxConditions` and `Error::NoArch` (returned by
    `Filter::install` when no architecture is enabled).

### Security

- Fix some potential security issues:
  - On x86, a rule for an `ipc` subcall now matches on the low 16 bits of the
    call number, as the kernel does. Before, setting the high bits of the
    call number bypassed the rule.
  - On x86, a rule with argument conditions for a `socketcall`/`ipc` subcall
    (e.g. `bind`) silently did not apply to the multiplexed call. Such rules are
    now rejected with `Error::InvalidMuxConditions`; use
    `Filter::add_rule_exact` to match the direct syscall only.

### Fixed

- On x86_64, syscall number -1 (used by tracers to skip a syscall) is no longer
  treated as a bad-arch x32 syscall.

## [0.1.0] - 2026-09-23 [YANKED]

- Initial release of seacomb.

[Unreleased]: https://github.com/thai-terrace/seacomb/compare/v0.2.0...HEAD
[0.2.0]: https://github.com/thai-terrace/seacomb/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/thai-terrace/seacomb/releases/tag/v0.1.0
