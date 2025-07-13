#!/bin/sh
#!/bin/sh
# GitHub PR management utilities

case "$1" in
    list)
        echo "=== Open Pull Requests ==="
        gh pr list --state open
        ;;
        
    checks)
        pr="${2:-@me}"
        echo "=== PR Checks Status ==="
        gh pr checks "$pr"
        ;;
        
    create)
        branch=$(git branch --show-current)
        if [ "$branch" = "main" ]; then
            echo "Cannot create PR from main branch"
            exit 1
        fi
        gh pr create --fill
        ;;
        
    review)
        pr="${2:-@me}"
        gh pr review "$pr"
        ;;
        
    *)
        echo "Usage: $0 {list|checks|create|review} [pr-number]"
        ;;
esac
