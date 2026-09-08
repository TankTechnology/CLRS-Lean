# English-Only Repository Design

## Objective

Use English consistently in repository-controlled collaboration records and text while preserving the technical content of the CLRS formalization.

## Scope

The policy covers commit messages, branch names, pull requests, issues, source comments, maintenance documents, audit records, release notes, and other tracked text. It applies to the current tree and to all commits reachable from maintained local and remote branches.

Existing commit messages that contain Chinese will be rewritten. Because this changes commit identifiers, the original refs must be backed up outside the repository before any remote update. Remote branches will be updated with explicit leases so an unexpected concurrent push aborts the operation.

GitHub issue titles and bodies that contain Chinese will be translated in place. Closed pull-request refs are controlled by GitHub and cannot be force-updated directly; maintained branch history and visible issue metadata are the authoritative cleanup targets.

## Enforcement

A repository checker will scan:

- tracked text files for CJK ideographs;
- commit subjects and bodies reachable from the selected Git refs;
- branch names for non-ASCII characters.

The checker will be part of `scripts/check_repository.py`, so the established repository verification command enforces the policy. Unit tests will cover clean input, text violations, commit-message violations, branch-name violations, binary files, and useful diagnostics.

## Migration and Recovery

The migration has four guarded stages:

1. Create a Git bundle containing every local and remote branch before rewriting.
2. Translate current tracked text and GitHub issue metadata.
3. Rewrite the known Chinese commit messages with a deterministic old-message-to-new-message map.
4. Verify the new graph and force-push each maintained remote branch with its previously observed object ID as a lease.

The bundle path, old-to-new commit map, and old/new remote branch tips will be retained outside the repository for recovery and review.

## Validation

Completion requires the language checker, the full repository checker, the Lean build, the trust gate, and the Pages-equivalent site build to pass from the rewritten `main`. A final remote fetch must confirm that GitHub branch tips match the locally verified rewritten tips.
