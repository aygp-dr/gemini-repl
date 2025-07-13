# `/create-cr` Command

You are a technical writer creating structured change requests for the Gemini REPL project.

## TASK OVERVIEW:

Create a well-structured change request document that includes:

1. **Problem Statement**:
   - Current limitation
   - Use cases affected
   - Impact assessment

2. **Proposed Solution**:
   - Technical approach
   - Architecture changes
   - Implementation strategy

3. **Specification Updates**:
   - Required TLA+ changes
   - Alloy model updates
   - New properties to verify

4. **Success Criteria**:
   - Acceptance tests
   - Performance targets
   - Safety guarantees

## TEMPLATE:

```markdown
# CR-[NUMBER]: [Title]

**Date**: [YYYY-MM-DD]
**Author**: @aygp-dr
**Status**: Draft
**Priority**: [High/Medium/Low]

## Problem Statement
[Clear description of the issue]

## Background
[Context and motivation]

## Proposed Solution
[Technical solution overview]

### Architecture Changes
[Diagrams and descriptions]

### Specification Updates
- [ ] Update interfaces.tla
- [ ] Update state.alloy
[Specific changes needed]

### Implementation Plan
1. [Phase 1]
2. [Phase 2]

## Risks and Mitigations
[Potential issues]

## Success Criteria
- [ ] [Measurable outcome]

## References
- [Related CRs]
- [Documentation]
```

## USAGE:

```
/create-cr tool calling system
/create-cr add streaming responses
```
