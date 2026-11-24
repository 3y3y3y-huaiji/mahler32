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
- any `.json` file at the repository root other than `comparator.json`,
  `lake-manifest.json` and `.zenodo.json`;
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

Lightweight gates (`check_no_secrets.py`, `verify_ssot.py`,
`generate_certificates.py`, `actionlint`) are cheap enough to run locally on
every change; the heavy Lean work (`lake build`, `#lint`, `leanchecker`, nanoda)
is left to GitHub Actions rather than run in the sandbox.

## 5. SSOT 强联动：这些依赖是**双向**的

`scripts/verify_ssot.py` 机械校验下面每一条；`⇄` 表示“任一侧改动都必须同步另一侧”：

- `lean-toolchain` ⇄ `formalization.yaml` 的 `toolchain.lean/mathlib` ⇄ `README.md` 版本行
- `Mahler32/*.lean` ⇄ `Mahler32Core.lean`（import，可传递）⇄ `AuditAxioms.lean`
  （每个模块都要有 `#print axioms`）⇄ `SpecCheck.lean`（每个模块都要有 `rfl`/`exact` 锁）
  ⇄ `README.md`（每个 `Mahler32/*.lean` 路径都要登记）
- `papers/*/main.tex` 的 theorem-to-Lean 表 ⇄ `AuditAxioms.lean` 里的同名 `#print axioms`
- 纠偏旧误判 ⇄ `README.md`、`papers/`（`STALE_PHRASES` 不得命中）

所以“只改锁文件不改实现”或“只改实现不改锁文件”都会红：门禁校验的是两边同时存在。

## 6. Lean work

The Lean-specific rules (proof golfing, `snake_case`/`UpperCamelCase`, the style
script, `lake build -KwarningAsError=true`) are unchanged and are documented in
`docs/MAHLER32_REVIEW.md` §6. `Challenge.lean` is the only file allowed to
contain `sorry`; `Mahler32/Basic.lean` must build with none.

Proofs default to `grind`; fall back to `omega`, `ring` or `simp` only where
`grind` does not apply or a lighter tactic closes the goal directly.

## 7. 提交流程：开 PR，不要直推 `main`/`master`

1. 从最新 `main` 开临时分支：`git switch -c trae/<topic> origin/main`。
2. 本地跑轻量门禁：`check_no_secrets.py --tree`、`verify_ssot.py`、
   `generate_certificates.py --verify`；装了 actionlint 再跑 `actionlint`。
3. 按第 1 条显式 `git add <file> …`，提交后 `git push -u origin HEAD` 推分支。
4. 开 PR 到 `main`（`gh pr create --base main --head trae/<topic>`），写清
   “为什么改、改了哪些模块、联动更新了哪些文件”。
5. 等 `guards.yml` / `lean_build.yml` / `papers.yml` 全绿；需要独立内核复核时给 PR
   加 `run-independent-kernel` 标签。
6. 只在 PR 上合并（squash）；合并后 `pr-cleanup.yml` 自动删除临时分支。

PR 分类：`lean_build.yml` 的 `classify` 对 `pull_request` 分类**整个 PR**
（`merge-base(base, head) .. head`），对 `push` 只分类**最近一次推送**；纯文档推送跳过
`Build and Verify`。只要碰到 `*.lean`、`lakefile.lean`、`lean-toolchain`、
`lake-manifest.json`、`comparator.json`、`AuditAxioms*`、`SpecCheck*`、`check_axioms.py`、
`generate_certificates.py`、`verify_all.sh`、`lean_build.yml`，或者任何不在文档白名单里的
路径（包括新脚本），就全量重跑。

特性分支只通过 PR 跑 `lean_build.yml`（它不再监听 `trae/**` 的 push），同一次提交不会
跑两遍；`main`/`master` 的 push 仍然全量跑。

直推 `main`/`master`、`git add -A`、`git commit --no-verify` 都不属于提交流程。
