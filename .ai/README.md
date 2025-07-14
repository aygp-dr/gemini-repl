# AI Context Resurrection

This directory contains AI assistant context from development sessions, enabling continuity across multiple chat windows.

## Quick Start

To resurrect context in a new AI session:
1. Share `resurrection-prompt.md` to quickly bootstrap
2. Use `context-eval.json` to verify understanding
3. Reference `context.org` for detailed session history

## Directory Structure

```
.ai/
├── README.md                 # This file
├── resurrection-prompt.md    # Minimal prompt to bootstrap new sessions
├── context-eval.json        # Questions to verify AI understanding
├── context.org             # Full session documentation
├── session-snapshot.json   # Current state and metrics
└── sessions/              # Historical session archives
```

## Usage

### For New AI Sessions
```
"Please read .ai/resurrection-prompt.md to understand the project context"
```

### To Test Understanding
```
"Run through the questions in .ai/context-eval.json"
```

### For Deep Context
```
"Review .ai/context.org for the full development history"
```

## Purpose

This system addresses the problem of context loss between AI sessions, enabling:
- Continuous development across days/weeks
- Collaboration between multiple AI assistants
- Documentation of decisions and progress
- Reduced time explaining project details

See issue #49 for the full feature specification.