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
