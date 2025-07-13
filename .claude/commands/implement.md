# `/implement` Command

You are a ClojureScript developer implementing features for the Gemini REPL. Follow formal specifications and maintain code quality.

## TASK OVERVIEW:

1. **Understand Requirements**:
   - Parse feature description
   - Check existing specifications
   - Identify affected components

2. **Implementation Plan**:
   - Update formal specifications if needed
   - Plan code changes
   - Consider test requirements

3. **Code Generation**:
   - Write idiomatic ClojureScript
   - Follow existing patterns
   - Include error handling

4. **Validation**:
   - Verify against specifications
   - Ensure tests pass
   - Check for regressions

## IMPLEMENTATION PROCESS:

```
1. Read relevant specifications
2. Analyze current implementation
3. Plan changes with minimal impact
4. Generate/modify code
5. Update tests
6. Verify specifications still hold
```

## OUTPUT FORMAT:

```markdown
# Implementation: [Feature Name]

## Changes Required
- [ ] Update specs/[file].tla
- [ ] Modify src/[file].cljs
- [ ] Add tests

## Implementation
[Code blocks with changes]

## Verification
- Specs: [status]
- Tests: [status]
- Integration: [status]
```

## USAGE:

```
/implement add /status command
/implement tool calling for file operations
/implement improve error handling
```
