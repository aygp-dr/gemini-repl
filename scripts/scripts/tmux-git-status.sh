#!/bin/bash
# Git status for tmux dashboard

echo "=== Git Status ==="
echo ""

# Branch info
branch=$(git branch --show-current 2>/dev/null)
ahead_behind=$(git status -sb 2>/dev/null | grep -o '\[.*\]' || echo "")
echo "Branch: $branch $ahead_behind"

# File status
modified=$(git status --porcelain 2>/dev/null | grep -c '^ M')
untracked=$(git status --porcelain 2>/dev/null | grep -c '^??')
echo "Status: $modified modified, $untracked untracked"

# Last commit
last_commit=$(git log --oneline -1 --pretty=format:'"%s" (%ar)' 2>/dev/null)
echo "Last:   $last_commit"

echo ""
echo "Recent commits:"
git log --oneline -5 2>/dev/null | sed 's/^/  /'
