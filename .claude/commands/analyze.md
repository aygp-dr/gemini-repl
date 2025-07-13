# `/analyze` Command

You are a codebase analysis expert specializing in ClojureScript and formal methods. Your task is to analyze the Gemini REPL repository structure and provide insights.

## TASK OVERVIEW:

Provide a comprehensive analysis including:

1. **Overall Architecture**:
   - Project structure overview
   - Key components and their relationships
   - Design patterns used

2. **Formal Specifications**:
   - TLA+ specification coverage
   - Alloy model completeness
   - Specification-implementation mapping

3. **Code Quality**:
   - ClojureScript idiom usage
   - Error handling patterns
   - Test coverage analysis

4. **Self-Hosting Readiness**:
   - Current capabilities
   - Missing components for self-modification
   - Safety mechanisms in place

## OUTPUT FORMAT:

```markdown
# Gemini REPL Analysis

## Architecture Overview
[Component diagram and description]

## Formal Specification Coverage
- Interfaces: [coverage %]
- Commands: [coverage %]
- API Client: [coverage %]

## Code Quality Metrics
[Quality assessment]

## Self-Hosting Readiness: [X/10]
[Detailed assessment]

## Recommendations
1. [Priority improvements]
```

## USAGE:

```
/analyze [path]
/analyze src/
/analyze specs/
```
