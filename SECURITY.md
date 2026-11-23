# Security Policy

## Reporting a vulnerability

This repository is a public Lean 4 / Mathlib formalization. It contains no production service
and no user data, but it does contain CI workflows, scripts and (potentially) credentials in
history. If you find a security issue — a leaked credential, a workflow injection vector, an
unsafe script, or anything else — **please do not open a public issue**.

Report it privately in one of these ways:

1. Open a private security advisory:
   <https://github.com/3y3y3y-huaiji/mahler32/security/advisories/new>
2. Or email the maintainer (Su MingKai) at **<sumingkai1@outlook.com>** (also listed on
   <https://orcid.org/0009-0008-2312-6913>), with `mahler32 security` in the subject.

Please include: the affected file or workflow, a reproduction (command or link), and the
potential impact. We aim to acknowledge reports within a few days.

## Credential handling

`scripts/check_no_secrets.py` is run by the pre-commit hook and by CI over the tracked tree. It
refuses submission-token fields, authorization bearer headers, GitHub/AWS/Slack token prefixes,
PEM private keys, stray root-level `.json` files and symlinks.

If a credential ever reaches a commit, treat it as compromised immediately: revoke it at the
issuer **first**, then clean the tree. Rewriting history does not reach forks, caches or
already-fetched clones, so revocation is the only reliable mitigation.

## Scope

- **In scope:** workflow permissions / action pinning, secret leakage, injection in `scripts/`,
  supply-chain risk in `.github/`.
- **Out of scope:** the mathematical statements themselves (those are checked by the Lean kernel
  and the axiom audit, not by this policy).
