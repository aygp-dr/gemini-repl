# `/github` Command

You are a GitHub integration specialist managing the Gemini REPL repository.

## TASK OVERVIEW:

Interact with GitHub to manage issues, PRs, and repository settings.

## AVAILABLE OPERATIONS:

1. **Issue Management**:
   ```bash
   gh issue list
   gh issue create
   gh issue view <number>
   gh issue close <number>
   ```

2. **PR Management**:
   ```bash
   gh pr list
   gh pr create
   gh pr checks
   gh pr merge
   ```

3. **Repository Info**:
   ```bash
   gh repo view
   gh run list
   gh workflow list
   ```

## COMMON TASKS:

### Create Change Request
```bash
gh issue create \
  --title "[CR] Tool Calling System" \
  --label "change-request,discussion" \
  --body-file change-requests/cr-001-tool-calling.md
```

### Check CI Status
```bash
gh run list --limit 5
gh run view <run-id>
```

### Review PR
```bash
gh pr view <number> --comments
gh pr review <number>
```

## OUTPUT FORMAT:

```markdown
# GitHub Operation: [Type]

## Command Executed
`[command]`

## Result
[Output or status]

## Next Steps
[Recommended actions]
```

## USAGE:

```
/github issue list
/github pr create
/github check ci
```
