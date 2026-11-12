# CI caches each installer it downloads, keyed on its pins, and checks the file's SHA-256 on every run

Status: accepted
Tier: implementation; area: process

## Context

CI's setup steps download three installers: `rustup-init` in the `rust`
and `cross` jobs, the elan tarball in the `lean` and `cross` jobs and in
`pages.yml`, and the Verus zip in the `rust` job. Each step checks the file
against a SHA-256 written in the workflow (ADR-2026-10-30-1030,
ADR-2026-10-29-2135, ADR-2026-11-03-0809). #152 added retries to these
downloads (#151), but a long outage still fails a suite, and every run
pays for six downloads. On 2026-11-05 the human asked in
[#160](https://github.com/pmatos/funk/issues/160) for the three installer
downloads to be cached, so that a run downloads one only on a cache miss.

Facts:

- A run on a pull request restores caches saved on its own ref or on
  `main`; a run on `main` restores only caches saved on `main`.
- When two jobs of one run miss the same key, both try to save it, and
  one fails to reserve it.
- `actions/cache` reads its own step's `env` in its `with`.
- `.github/workflows/ci.yml` held 16,986 of its 20,000 bytes
  (ADR-2026-10-28-0724). The new steps written inline took it to about
  20,500.

## Decision

- **One cache per installer**, holding only the downloaded file in
  `RUNNER_TEMP`: `rustup-init`, `elan.tar.gz` or `verus.zip`. The key is
  `<tool>-installer-<os>-<version>-<sha256>`, with `rustup`, `elan` or
  `verus` as the tool, so a bump of either pin is a miss.
- **The pins stay in the workflow**, twice in each copy: in the `env` of
  the step `Restore the <tool> installer`, for the key, and of the step
  `Install <tool>` right after it. A bump edits both.
- **`scripts/ci-install.sh rustup|elan|verus` runs each install step.**
  It downloads the installer only when the restore step found no copy,
  with #152's retries; it checks the file against its SHA-256 on every
  run, hit or miss, before using it, so a bad cached file fails the step;
  then it installs the tool as the inline step did. The script keeps
  `ci.yml` within its budget and holds one copy of each download command.
- **One job saves each cache**: `rust` saves the rustup and Verus
  installers, and `lean` saves elan's. `cross` and `pages.yml` only
  restore, with `actions/cache/restore`. A save step follows its install
  step and runs only on a miss and only when that step passed, so the
  cache holds only a file that passed its check. One saver per key means
  two jobs of one run never race to save it; the savers are the jobs that
  already save the Rust and Lean toolchains (ADR-2026-11-05-1408).
  `pages.yml` deploys, so it never saves a cache
  ([spec-site.md](../decisions/spec-site.md#publishing-the-site)).
- **Unchanged**: the toolchain installs (`rustup toolchain install`,
  `elan toolchain install`), `apt-get`, `uvx`, Lake's fetches and every
  other cache.

## Alternatives

- **The pins in the job's `env`**, read by both steps: one copy per job,
  but every later step of the job, the toolchain installs and the hooks
  included, would see `RUSTUP_VERSION` and the other pins.
- **`actions/cache` in every job**, restoring and saving at the end of the
  job: the jobs that share a key would race to save it, and `pages.yml`
  would save.
- **The download kept inline in each step**: `ci.yml` would pass 20,000
  bytes.

## Consequences

- A warm run downloads none of the three installers. A run after a bump,
  or the first on a pull request when `main` has no cache yet, downloads
  as before in each job that misses, `cross` included when it reaches the
  step before `rust` or `lean` has saved.
- A cached file that fails its check fails the step on every run until a
  bump changes the key or the cache entry is deleted.
- This refines ADR-2026-10-30-1030, ADR-2026-10-29-2135 and
  ADR-2026-11-03-0809, whose jobs download and check each installer: they
  now check it on every run and download it on a miss. It refines
  ADR-2026-11-05-1408, which lists CI's caches and which job saves each,
  and the Pages workflow
  ([spec-site.md](../decisions/spec-site.md#publishing-the-site)), whose
  `pages.yml` copies the Lean setup steps:
  the copies are now four steps, without the save.
