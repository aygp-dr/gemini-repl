#!/bin/sh
#!/bin/sh
# GitHub issue management utilities

case "$1" in
    list-open)
        echo "=== Open Issues ==="
        gh issue list --state open
        ;;
        
    list-crs)
        echo "=== Open Change Requests ==="
        gh issue list --state open --label change-request
        ;;
        
    create-cr)
        title="$2"
        if [ -z "$title" ]; then
            echo "Usage: $0 create-cr <title>"
            exit 1
        fi
        gh issue create --title "[CR] $title" \
            --label "change-request,discussion" \
            --template change_request.yml
        ;;
        
    create-bug)
        gh issue create --template bug_report.yml
        ;;
        
    create-feature)
        gh issue create --template feature_request.yml
        ;;
        
    *)
        echo "Usage: $0 {list-open|list-crs|create-cr|create-bug|create-feature}"
        ;;
esac
