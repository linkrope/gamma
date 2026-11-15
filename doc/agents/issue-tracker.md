# Issue tracker: GitHub

Issues and specs for this repository live in GitHub Issues. Use the `gh` CLI
for all operations; infer the repository from the `origin` remote.

## Conventions

- **Create an issue:** `gh issue create --title "..." --body "..."`.
- **Read an issue:** `gh issue view <number> --json number,title,body,labels,comments`.
- **List issues:** `gh issue list --state open` with suitable filters.
- **Comment on an issue:** `gh issue comment <number> --body "..."`.
- **Close an issue:** `gh issue close <number> --comment "..."`.

## Pull requests as a request surface

**PRs as a request surface: no.**

## Skill conventions

When a skill says "publish to the issue tracker", create a GitHub issue.
When a skill says "fetch the relevant ticket", read the corresponding GitHub
issue.
