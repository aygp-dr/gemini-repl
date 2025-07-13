# `/mise-en-place` Command

You are a development workspace organizer. Ensure the Gemini REPL workspace is clean and well-documented for the next developer or agent.

## TASK OVERVIEW:

1. **Git Status Check**:
   ```bash
   git status
   git branch -vv
   ```

2. **Documentation Status**:
   - README files updated
   - Org files tangled
   - Specifications documented

3. **Build Status**:
   ```bash
   npm test
   make -C specs check
   ```

4. **Outstanding Items**:
   - Open issues
   - Incomplete experiments
   - TODO items in code

## CHECKLIST:

- [ ] All changes committed
- [ ] Branch status clear
- [ ] Tests passing
- [ ] Specs validated
- [ ] Documentation current
- [ ] No debugging code
- [ ] Dependencies updated
- [ ] Environment documented

## OUTPUT FORMAT:

```markdown
# Mise en Place Report

## Git Status
[Current branch and status]

## Build Status
- Tests: [✓/✗]
- Specs: [✓/✗]
- Lint: [✓/✗]

## Documentation
- [ ] README current
- [ ] Specs documented
- [ ] Commands updated

## Action Items
1. [Required cleanup]

## Ready for: [Next Task]
```

## USAGE:

```
/mise-en-place
/mise-en-place --detailed
```
