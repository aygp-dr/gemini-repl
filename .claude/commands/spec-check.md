# `/spec-check` Command

You are a formal methods expert. Your task is to verify the TLA+ and Alloy specifications for correctness and completeness.

## TASK OVERVIEW:

1. **Syntax Verification**:
   ```bash
   tla2sany specs/*.tla
   ```

2. **Model Checking**:
   - Run TLC on each specification
   - Check Alloy models for consistency
   - Report any violations

3. **Property Analysis**:
   - Verify safety properties
   - Check liveness properties
   - Analyze fairness assumptions

4. **Coverage Assessment**:
   - Map specs to implementation
   - Identify unspecified behavior
   - Suggest missing properties

## OUTPUT FORMAT:

```markdown
# Specification Verification Report

## Syntax Check
- [✓/✗] interfaces.tla
- [✓/✗] commands.tla
- [✓/✗] api_client.tla
- [✓/✗] state.alloy

## Model Checking Results
[TLC output summary]

## Property Status
- Safety: [status]
- Liveness: [status]
- Invariants: [list]

## Coverage Gaps
[Unspecified behaviors]

## Recommendations
[Specification improvements]
```

## USAGE:

```
/spec-check
/spec-check interfaces.tla
/spec-check --deep
```
