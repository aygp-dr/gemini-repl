#!/bin/bash
# GitHub status for tmux dashboard

echo "=== GitHub Status ==="
echo ""

# Cache file to avoid rate limits
CACHE_FILE="/tmp/gemini-repl-gh-cache"
CACHE_AGE=$((60)) # 60 seconds

# Check cache age
if [ -f "$CACHE_FILE" ]; then
    cache_time=$(stat -f %m "$CACHE_FILE" 2>/dev/null || stat -c %Y "$CACHE_FILE" 2>/dev/null)
    current_time=$(date +%s)
    age=$((current_time - cache_time))
    
    if [ $age -lt $CACHE_AGE ]; then
        cat "$CACHE_FILE"
        exit 0
    fi
fi

# Generate fresh data
{
    echo "Open Issues: $(gh issue list --state open --json number | jq length)"
    gh issue list --state open --limit 3 | sed 's/^/  /'
    echo ""
    echo "Active PRs: $(gh pr list --state open --json number | jq length 2>/dev/null || echo "0")"
    gh pr list --state open --limit 3 2>/dev/null | sed 's/^/  /' || echo "  No open PRs"
} | tee "$CACHE_FILE"
