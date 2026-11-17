/- ======================================================================
/- CHRONOLOGICAL LABEL — #0039 / 1133
/-    Path         : handoff/NEW_GITHUB_BOOTSTRAP.md
/-    Ref          : main
/-    First-commit : 2026-08-14 21:44:31 +0530
/-    Last-commit  : 2026-08-14 21:44:31 +0530
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- ====================================================================== -/

<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #0039 / 1132
<!--    Path         : handoff/NEW_GITHUB_BOOTSTRAP.md
<!--    Ref          : main
<!--    First-commit : 2026-08-14 21:44:31 +0530  (83dd56f)
<!--    Last-commit  : 2026-08-14 21:44:31 +0530  (83dd56f)
<!--    Total commits: 1
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/1] 2026-08-14 21:44:31 +0530  83dd56f  (ker07-dev)
<!--        Import Sol inline surgery handoff and GST graph workspace
<!-- ====================================================================== -->

# New GitHub bootstrap — ker07-dev

The connected GitHub account is `ker07-dev` and currently has no repositories.

The ChatGPT GitHub connector available in this session can populate/edit an existing repository,
but does not expose the GitHub API operations for creating the first repository or creating a Codespace.

## One-time GitHub UI bootstrap

1. On GitHub, click **New repository**.
2. Owner: **ker07-dev**
3. Repository name: **erdos-ternary2-proof**
4. Visibility: **Private**
5. Initialize with a README so `main` exists.
6. Create the repository.
7. Ensure the ChatGPT GitHub app/connection has access to this new private repository.

After that, ChatGPT can populate the repository through the connector.

## Codespace

Once files are uploaded, GitHub → **Code** → **Codespaces** → **Create codespace on main**.
The repository already contains `.devcontainer/devcontainer.json`; its `postCreateCommand` runs
`scripts/setup-comparator.sh`, which installs Lean dependencies and builds Comparator.

Then the verification commands are:

```bash
bash scripts/audit.sh
bash scripts/run-comparator.sh
```

Comparator configuration:

```json
{
  "challenge_module": "Challenge",
  "solution_module": "Solution",
  "theorem_names": ["erdos_ternary_2"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": false
}
```
