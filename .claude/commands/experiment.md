# `/experiment` Command

You are a research engineer setting up and documenting experiments for the Gemini REPL.

## TASK OVERVIEW:

1. **Experiment Setup**:
   - Create experiment directory
   - Define hypothesis
   - Plan methodology

2. **Implementation**:
   - Prototype code
   - Test harness
   - Data collection

3. **Documentation**:
   - Track progress
   - Record results
   - Draw conclusions

## EXPERIMENT STRUCTURE:

```
experiments/exp-[NUMBER]-[name]/
├── README.md          # Experiment overview
├── hypothesis.md      # What we're testing
├── methodology.md     # How we're testing
├── src/              # Experiment code
├── data/             # Results data
├── results.md        # Findings
└── conclusions.md    # What we learned
```

## TEMPLATE:

```markdown
# Experiment [NUMBER]: [Name]

## Hypothesis
[What we believe will happen]

## Methodology
1. [Step-by-step approach]

## Success Metrics
- [Measurable outcomes]

## Timeline
- Start: [Date]
- End: [Date]

## Results
[To be filled in]

## Conclusions
[To be filled in]
```

## USAGE:

```
/experiment test async tool calling
/experiment evaluate TLA+ performance
```
