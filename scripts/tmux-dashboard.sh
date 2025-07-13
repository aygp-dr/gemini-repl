#!/usr/bin/env bash
# scripts/tmux-dashboard.sh
# Tmux Development Dashboard for Gemini REPL

SESSION="gemini-repl-dev"

# Kill existing session if requested
if [ "$1" = "--restart" ]; then
    tmux kill-session -t $SESSION 2>/dev/null
fi

# Check if session exists
if tmux has-session -t $SESSION 2>/dev/null; then
    echo "Session $SESSION already exists. Attaching..."
    tmux attach-session -t $SESSION
    exit 0
fi

echo "Creating Gemini REPL dashboard..."

# Create new session with main REPL pane
tmux new-session -d -s $SESSION -n dashboard

# Pane 0: Main REPL (top left - 60%)
tmux send-keys "gmake run" C-m

# Pane 1: System monitor (top right - 40%)
tmux split-window -h -p 40
tmux send-keys "htop || top" C-m

# Pane 2: Git status (middle left)
tmux select-pane -t 0
tmux split-window -v -p 50
tmux send-keys "watch -n 5 -t 'git status -sb && echo && git log --oneline -5'" C-m

# Pane 3: GitHub issues/PRs (middle right)
tmux select-pane -t 1
tmux split-window -v -p 50
tmux send-keys "watch -n 60 -t 'echo \"=== Issues ===\"; gh issue list --limit 5; echo; echo \"=== PRs ===\"; gh pr list'" C-m

# Pane 4: Log monitor (bottom left)
tmux select-pane -t 2
tmux split-window -v -p 50
tmux send-keys "tail -f /tmp/gemini.fifo | jq '.'" C-m

# Pane 5: Spec verification (bottom right)
tmux select-pane -t 3
tmux split-window -v -p 50
tmux send-keys "watch -n 300 -t 'gmake verify'" C-m

# Focus on main REPL pane
tmux select-pane -t 0

echo ""
echo "Dashboard ready!"
echo "Attach with: tmux attach -t $SESSION"
echo "Detach with: Ctrl-b d"
echo "Kill with:   tmux kill-session -t $SESSION"

# Attach to session
tmux attach-session -t $SESSION
