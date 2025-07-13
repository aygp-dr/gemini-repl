#!/bin/bash
# Tmux Development Dashboard for Gemini REPL

SESSION="gemini-repl-dev"
SCRIPTS_DIR="$(dirname "$0")/scripts"

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Function to print status
status() {
    echo -e "${GREEN}✓${NC} $1"
}

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

# Create required scripts directory
mkdir -p $SCRIPTS_DIR

echo -e "${BLUE}Creating Gemini REPL dashboard...${NC}"

# Create new session with main REPL pane
tmux new-session -d -s $SESSION -n dashboard -c "$(pwd)"
status "Session created: $SESSION"

# Configure main REPL pane (0)
tmux send-keys -t $SESSION:0.0 'echo "Starting REPL... (Press Enter to begin)"' C-m
tmux send-keys -t $SESSION:0.0 'read -p "Press Enter to start REPL or Ctrl-C to use pane manually: " && gmake run' C-m
status "REPL started in pane 0"

# Split horizontally for system monitor (top right - 40%)
tmux split-window -t $SESSION:0.0 -h -p 40
tmux send-keys -t $SESSION:0.1 "$SCRIPTS_DIR/tmux-monitor.sh" C-m
status "System monitor active"

# Split vertically for git status (middle left)
tmux select-pane -t $SESSION:0.0
tmux split-window -t $SESSION:0.0 -v -p 50

# Split horizontally for GitHub status (middle right)
tmux split-window -t $SESSION:0.2 -h -p 50
tmux send-keys -t $SESSION:0.3 "watch -n 60 -t '$SCRIPTS_DIR/tmux-github.sh'" C-m
status "GitHub monitor initialized"

# Configure git status pane
tmux send-keys -t $SESSION:0.2 "watch -n 5 -t '$SCRIPTS_DIR/tmux-git-status.sh'" C-m
status "Git status watching"

# Split for bottom panes
tmux select-pane -t $SESSION:0.2
tmux split-window -t $SESSION:0.2 -v -p 50

# Split bottom for commands pane
tmux split-window -t $SESSION:0.4 -h -p 50

# Configure test/build output pane
tmux send-keys -t $SESSION:0.4 'echo "Test/Build output. Press 1 for tests, 2 for build watch:"' C-m
tmux send-keys -t $SESSION:0.4 'read -n1 choice && case $choice in 1) npm test -- --watch;; 2) gmake dev;; *) echo "Manual mode";; esac' C-m
status "Test watcher ready"

# Configure command menu pane
tmux send-keys -t $SESSION:0.5 "$SCRIPTS_DIR/tmux-menu.sh" C-m
status "Command menu ready"

# Create monitor script
cat > "$SCRIPTS_DIR/tmux-monitor.sh" << 'EOF'
#!/bin/bash
# System monitor for tmux dashboard

while true; do
    clear
    echo "=== System Monitor ==="
    echo ""
    
    # CPU usage
    cpu=$(top -bn1 | grep "Cpu(s)" | awk '{print $2}' | cut -d'%' -f1)
    printf "CPU:  "
    awk -v val="$cpu" 'BEGIN { 
        filled = int(val/10); 
        for(i=1;i<=10;i++) printf (i<=filled) ? "█" : "░" 
    }'
    printf " %.0f%%\n" "$cpu"
    
    # Memory usage
    mem_info=$(free -m | awk 'NR==2{printf "%.0f %.0f %.0f", $3, $2, ($3/$2)*100}')
    mem_used=$(echo $mem_info | cut -d' ' -f1)
    mem_total=$(echo $mem_info | cut -d' ' -f2)
    mem_percent=$(echo $mem_info | cut -d' ' -f3)
    
    printf "MEM:  "
    awk -v val="$mem_percent" 'BEGIN { 
        filled = int(val/10); 
        for(i=1;i<=10;i++) printf (i<=filled) ? "█" : "░" 
    }'
    printf " %d%% (%sM/%sM)\n" "$mem_percent" "$mem_used" "$mem_total"
    
    # Disk usage
    disk_info=$(df -h / | awk 'NR==2{print $5 " " $3 " " $2}' | sed 's/%//')
    disk_percent=$(echo $disk_info | cut -d' ' -f1)
    disk_used=$(echo $disk_info | cut -d' ' -f2)
    disk_total=$(echo $disk_info | cut -d' ' -f3)
    
    printf "DISK: "
    awk -v val="$disk_percent" 'BEGIN { 
        filled = int(val/10); 
        for(i=1;i<=10;i++) printf (i<=filled) ? "█" : "░" 
    }'
    printf " %d%% (%s/%s)\n" "$disk_percent" "$disk_used" "$disk_total"
    
    echo ""
    echo "PROC: $(pgrep -c node) node, $(pgrep -c java) java"
    echo "LOAD: $(uptime | awk -F'load average:' '{print $2}')"
    
    sleep 2
done
EOF
chmod +x "$SCRIPTS_DIR/tmux-monitor.sh"

# Create git status script
cat > "$SCRIPTS_DIR/tmux-git-status.sh" << 'EOF'
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
EOF
chmod +x "$SCRIPTS_DIR/tmux-git-status.sh"

# Create GitHub status script
cat > "$SCRIPTS_DIR/tmux-github.sh" << 'EOF'
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
EOF
chmod +x "$SCRIPTS_DIR/tmux-github.sh"

# Create command menu script
cat > "$SCRIPTS_DIR/tmux-menu.sh" << 'EOF'
#!/bin/bash
# Command menu for tmux dashboard

while true; do
    clear
    echo "=== Quick Commands ==="
    echo "[1] Start/Restart REPL"
    echo "[2] Run all tests"
    echo "[3] Check specifications"
    echo "[4] Build production"
    echo "[5] Create issue"
    echo "[6] Show mise-en-place"
    echo "[7] List open issues"
    echo "[8] Git status"
    echo "[9] Run dev server"
    echo "[0] Refresh dashboard"
    echo ""
    echo -n "Select: "
    
    read -n1 choice
    echo ""
    
    case $choice in
        1)
            echo "Restarting REPL..."
            tmux send-keys -t gemini-repl-dev:0.0 C-c
            sleep 1
            tmux send-keys -t gemini-repl-dev:0.0 "gmake run" C-m
            ;;
        2)
            echo "Running tests..."
            npm test
            echo "Press any key to continue..."
            read -n1
            ;;
        3)
            echo "Checking specifications..."
            gmake verify
            echo "Press any key to continue..."
            read -n1
            ;;
        4)
            echo "Building production..."
            gmake build
            echo "Press any key to continue..."
            read -n1
            ;;
        5)
            echo "Creating issue..."
            gh issue create
            ;;
        6)
            echo "Running mise-en-place..."
            gmake verify && git status
            echo "Press any key to continue..."
            read -n1
            ;;
        7)
            gh issue list
            echo "Press any key to continue..."
            read -n1
            ;;
        8)
            git status
            echo "Press any key to continue..."
            read -n1
            ;;
        9)
            echo "Starting dev server in pane 0..."
            tmux send-keys -t gemini-repl-dev:0.0 C-c
            sleep 1
            tmux send-keys -t gemini-repl-dev:0.0 "gmake dev" C-m
            ;;
        0)
            tmux send-keys -t gemini-repl-dev:0.1 C-c
            tmux send-keys -t gemini-repl-dev:0.1 "$SCRIPTS_DIR/tmux-monitor.sh" C-m
            ;;
        *)
            echo "Invalid choice"
            sleep 1
            ;;
    esac
done
EOF
chmod +x "$SCRIPTS_DIR/tmux-menu.sh"

# Select the main REPL pane
tmux select-pane -t $SESSION:0.0

echo ""
echo -e "${GREEN}Dashboard ready!${NC}"
echo ""
echo "Attach with: tmux attach -t $SESSION"
echo "Detach with: Ctrl-b d"
echo "Kill with:   tmux kill-session -t $SESSION"