# AGENTS.md — rules for anyone (or anything) committing here

This repository is public and is submitted to a registry, so a mistake in a
commit is expensive to undo. The rules below are mechanical on purpose: they
are enforced by `scripts/check_no_secrets.py`, by a pre-commit hook and by CI,
so they do not depend on anyone remembering them.

---

## 1. Stage files by name. Never `git add -A`, `git add .` or `git commit -a`

Every commit names its paths:

```bash
git add lakefile.lean Mahler32/Basic.lean
git commit -F - <<'MSG'
...
MSG
```

A blanket add sweeps up whatever happens to be in the working tree — generated
output, downloaded reports, editor backups, and, on 2026-11-20, a Palomar
submission response containing a live `access_token`, which then went to a
public repository. The cost of typing the paths is a few seconds; the cost of
the alternative was a leaked credential and a withdrawn submission.

## 2. Every response body, token and one-off file lives outside the repository

Write HTTP responses, `pending_secret`s, `access_token`s, downloaded run
artifacts and anything else produced by a tool to the system temporary
directory — `/tmp` on POSIX, `%TEMP%` on Windows. Never inside the repository,
not even briefly: `git add -A` does not care how briefly.

```bash
TMP=$(mktemp -d)                       # /tmp/... on POSIX
curl -sS -o "$TMP/submit.json" ...     # never ./submit.json
```

On Windows shells that rewrite paths, pass the Windows form explicitly
(`cygpath -w /tmp`) or set `MSYS_NO_PATHCONV=1`; a silently misplaced `-o`
target is how the first intake response was lost.

## 3. Nothing that looks like a credential is committed

`scripts/check_no_secrets.py` refuses, in the staged set (pre-commit) or in the
tracked tree (CI):

- content matching `access_token`, `pending_secret`, `Bearer <credential>`,
  GitHub tokens (`ghp_`, `gho_`, `github_pat_`), AWS key ids, Slack tokens, or
  PEM private keys;
- any `.json` file at the repository root other than `comparator.json` and
  `lake-manifest.json`;
- the scratch names the submission flow writes (`.submit*.json`,
  `.verify*.json`, `.status.json`, `.review.json`, `st.json`, …);
- symlinks.

If a credential does reach a commit: treat it as compromised immediately,
invalidate it at the issuer **first** (here: `POST /withdraw` on the
submission), then clean the tree. Rewriting history is secondary — it does not
reach forks, caches or already-fetched clones.

## 4. The gates

Local, once per clone:

```bash
git config core.hooksPath .githooks
```

CI runs the same script over the tracked tree as its first job, so a commit
that bypasses the hook still cannot merge green. `git commit --no-verify` exists
and is allowed only when the hook itself is broken, never to push a file past
it; say so in the commit message if you use it.

## 5. SSOT 强联动表 — 改一个 Lean 模块，就同时改这四处

`scripts/verify_ssot.py` 在 CI 里机械校验下表；缺一处即红。它不是提醒，是门禁。

| 你改了什么 | 必须同时更新 | 校验点 |
| :-- | :-- | :-- |
| 新增/重命名 `Mahler32/*.lean` | `Mahler32Core.lean`（import） | 从 `Mahler32Core` 可传递到达 |
| 同上 | `AuditAxioms.lean`（`#print axioms` + 模块名） | 每个模块都被审计 |
| 同上 | `SpecCheck.lean`（`example … := rfl/exact`） | 每个模块都有定义/签名锁 |
| 同上 | `README.md`（模块清单表） | 每个 `Mahler32/*.lean` 路径都登记 |
| 改 `lean-toolchain` | `formalization.yaml`、`README.md` | 两处版本号与 `lean-toolchain` 完全一致 |
| 改任何被论文引用的定理名 | `papers/*/main.tex` 的 theorem-to-Lean 表 | 论文追踪表与 `#print axioms` 同名 |
| 纠偏旧误判 | 同步 `README.md`、`papers/` | `STALE_PHRASES` 黑名单不得命中 |

论文追踪表是 `papers/paper1_transcendence/main.tex` 与
`papers/paper2_zero_entropy_fluid/main.tex` 末尾的 Lean 声明表；改了定理名却不改它，
等于把未验证的声明留在论文里。

## 6. Lean work

The Lean-specific rules (proof golfing, `snake_case`/`UpperCamelCase`, the style
script, `lake build -KwarningAsError=true`) are unchanged and are documented in
`docs/MAHLER32_REVIEW.md` §6. `Challenge.lean` is the only file allowed to
contain `sorry`; `Mahler32/Basic.lean` must build with none.
