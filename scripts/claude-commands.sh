#!/bin/sh
#!/bin/sh
# Quick access to Claude commands

COMMAND_DIR=".claude/commands"

list_commands() {
    echo "Available Claude commands:"
    for cmd in $COMMAND_DIR/*.md; do
        basename "$cmd" .md | sed 's/^/  \//'
    done
}

show_command() {
    cmd_file="$COMMAND_DIR/$1.md"
    if [ -f "$cmd_file" ]; then
        head -20 "$cmd_file"
    else
        echo "Command not found: $1"
        list_commands
    fi
}

case "$1" in
    list)
        list_commands
        ;;
    show)
        show_command "$2"
        ;;
    *)
        echo "Usage: $0 {list|show <command>}"
        ;;
esac
