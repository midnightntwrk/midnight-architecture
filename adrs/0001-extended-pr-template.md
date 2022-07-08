# 1. Extended PR template

## Status

accepted

---

| -         | -                                                                                                  |
|-----------|----------------------------------------------------------------------------------------------------|
| date      | 2022-08-06                                                                                         |
| deciders  | Jon Rossie, Andrzej Kopeć, Jakub Zalewski,                                                         |
| consulted | Whole Midnight team                                                                                |

---

## Context and Problem Statement

Pull Requests opened against Architecture repository vary in content type and its
importance. Many of them are way easier to review if provided with additional context,
like the problem that is meant to be addressed, quick draft of a solution, some
alternatives considered.

Additionally, there is no way for checking important things in the Architecture repository
automatically, like it is possible with code, and yet - some way of verifying whether a
pull request meets certain criteria, other than review is in need.

## Decision Drivers

* ability of reviewer to build context necessary to review PR
* ability of reviewer to judge importance of PR contents
* a way of checking PR completeness/quality before passing to reviewers

## Considered Options

* leave things as they were initially - no PR template, ad-hoc questions on PR, base
  solely on reviewers to check PR completeness
* keep light PR template to provide some context, still rely mostly on reviewers
* extend PR template to a form of "mini ADR", ask there questions, which cause PR author
  to assess PR completeness

## Decision Outcome

Chosen option: _extend PR template to a form of 'mini ADR'_, because:

- it allows to build a complete context necessary for a review of PR contents
- it might be a good starting point for writing related ADR document (or answers can 
  be copy&pasted from an ADR document being part of the PR)
- with carefully chosen questions it takes insignificant time to answer them and yet
  offers a way for PR author to assess PR completeness

### Positive Consequences

* easier to review PRs

### Negative Consequences

* possibly increased time and effort for opening PRs with small fixes

## Validation

PRs require less time to be reviewed and merged. Ideally, having in mind process from
[Use ADRs](./0000-use-adrs-and-adrgen.md), it should be possible for a PR to be reviewed
within a week or two since its opening.


