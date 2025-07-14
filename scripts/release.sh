#!/bin/sh
# Release helper script for Gemini REPL

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Function to print colored output
print_info() {
    printf "${BLUE}ℹ️  %s${NC}\n" "$1"
}

print_success() {
    printf "${GREEN}✅ %s${NC}\n" "$1"
}

print_warning() {
    printf "${YELLOW}⚠️  %s${NC}\n" "$1"
}

print_error() {
    printf "${RED}❌ %s${NC}\n" "$1"
}

# Function to show usage
usage() {
    cat << EOF
Usage: $0 [patch|minor|major]

Create a new release of Gemini REPL

Arguments:
  patch  - Increment patch version (0.0.X)
  minor  - Increment minor version (0.X.0)
  major  - Increment major version (X.0.0)

If no argument is provided, patch release is created by default.

This script will:
  1. Run all tests and linting
  2. Bump the version in package.json
  3. Build the release
  4. Create a git tag
  5. Generate release notes
  6. Create a release archive
  7. Optionally push to GitHub and create a release

Example:
  $0 patch    # Create version 0.1.1 from 0.1.0
  $0 minor    # Create version 0.2.0 from 0.1.0
  $0 major    # Create version 1.0.0 from 0.1.0
EOF
}

# Check for help flag
if [ "$1" = "-h" ] || [ "$1" = "--help" ]; then
    usage
    exit 0
fi

# Determine release type
RELEASE_TYPE="${1:-patch}"

case "$RELEASE_TYPE" in
    patch|minor|major)
        ;;
    *)
        print_error "Invalid release type: $RELEASE_TYPE"
        echo ""
        usage
        exit 1
        ;;
esac

print_info "Starting $RELEASE_TYPE release process..."

# Run the make target
if command -v gmake >/dev/null 2>&1; then
    MAKE_CMD="gmake"
else
    MAKE_CMD="make"
fi

$MAKE_CMD release-"$RELEASE_TYPE"

# Get the new version
VERSION=$(node -p "require('./package.json').version")

print_success "Release v$VERSION created!"
echo ""

# Ask if user wants to push
printf "Would you like to push to GitHub now? [y/N] "
read -r PUSH_CONFIRM

if [ "$PUSH_CONFIRM" = "y" ] || [ "$PUSH_CONFIRM" = "Y" ]; then
    print_info "Pushing to GitHub..."
    git push && git push --tags
    print_success "Pushed to GitHub"
    
    # Check if gh is available
    if command -v gh >/dev/null 2>&1; then
        printf "Would you like to create a GitHub release? [y/N] "
        read -r RELEASE_CONFIRM
        
        if [ "$RELEASE_CONFIRM" = "y" ] || [ "$RELEASE_CONFIRM" = "Y" ]; then
            print_info "Creating GitHub release..."
            
            # Generate release notes to file
            LAST_TAG=$(git describe --tags --abbrev=0 HEAD^ 2>/dev/null || echo "")
            if [ -z "$LAST_TAG" ]; then
                COMMITS=$(git log --oneline --pretty=format:"- %s")
            else
                COMMITS=$(git log "$LAST_TAG"..HEAD --oneline --pretty=format:"- %s")
            fi
            
            cat > RELEASE_NOTES.md << EOF
## Release v$VERSION

### Changes
$COMMITS

### Installation
\`\`\`bash
tar -xzf gemini-repl-$VERSION.tar.gz
cd gemini-repl-$VERSION
npm install
gmake run
\`\`\`

### Requirements
- Node.js 14+
- npm or yarn
- Gemini API key

### Configuration
Copy \`.env.example\` to \`.env\` and add your Gemini API key.
EOF
            
            gh release create "v$VERSION" "gemini-repl-$VERSION.tar.gz" \
                --title "Release v$VERSION" \
                --notes-file RELEASE_NOTES.md
            
            rm -f RELEASE_NOTES.md
            print_success "GitHub release created!"
            echo ""
            print_info "View release at: https://github.com/$(git remote get-url origin | sed 's/.*github.com[:\/]\(.*\)\.git/\1/')/releases/tag/v$VERSION"
        fi
    else
        print_warning "GitHub CLI (gh) not found. Install it to create releases automatically."
    fi
else
    print_info "Skipping push. To push later, run:"
    echo "  git push && git push --tags"
    echo ""
    print_info "To create a GitHub release:"
    echo "  gh release create v$VERSION gemini-repl-$VERSION.tar.gz \\"
    echo "    --title \"Release v$VERSION\" \\"
    echo "    --generate-notes"
fi