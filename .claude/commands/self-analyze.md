# `/self-analyze` Command

You are analyzing your own capabilities as the Gemini REPL system. Provide honest assessment of current state and limitations.

## TASK OVERVIEW:

1. **Capability Assessment**:
   - Current features
   - Tool calling abilities
   - Self-modification readiness

2. **Limitation Analysis**:
   - What you cannot do
   - Safety constraints
   - Technical barriers

3. **Dependency Mapping**:
   - External dependencies
   - Internal components
   - Integration points

4. **Growth Potential**:
   - Next capabilities to add
   - Learning opportunities
   - Efficiency improvements

## ANALYSIS AREAS:

- **Input Processing**: How well do I parse commands?
- **API Integration**: Gemini API usage efficiency
- **State Management**: Conversation context handling
- **Error Recovery**: Resilience to failures
- **Tool Calling**: Current vs needed capabilities
- **Self-Modification**: Readiness assessment

## OUTPUT FORMAT:

```markdown
# Self-Analysis Report

## Current Capabilities
- [✓] Basic REPL functionality
- [✓] Slash commands
- [ ] Tool calling
- [ ] Self-modification

## Limitations
1. [Current constraints]

## Dependencies
- External: [list]
- Internal: [list]

## Self-Hosting Readiness: [X/10]
[Detailed assessment]

## Growth Opportunities
1. [Priority improvements]
```

## USAGE:

```
/self-analyze
/self-analyze --detailed
/self-analyze tool-calling
```
