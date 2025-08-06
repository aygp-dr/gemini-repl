# Gemini REPL Makefile
# For FreeBSD, use gmake

# Project configuration
PROJECT_NAME := gemini-repl
PROJECT_ROOT := $(shell pwd)

# Tool versions
TLA_VERSION := 1.8.0
ALLOY_VERSION := 5.1.0

# Local tool paths
TOOLS_DIR := tools/formal-methods
TLA_JAR := $(TOOLS_DIR)/tla2tools.jar
ALLOY_JAR := $(TOOLS_DIR)/alloy.jar

# Phony targets
.PHONY: help all install verify run dev build clean test test-repl test-cljs spec-check verify-alloy verify-tla banner lint lint-cljs lint-shell install-lint-tools check-lint-tools release release-patch release-minor release-major emacs emacs-restart

# Default target
all: help

# Help target
help:
	@echo "Gemini REPL - Available targets:"
	@echo ""
	@echo "  gmake help          - Show this help message"
	@echo "  gmake install       - Install all dependencies and tools"
	@echo "  gmake verify        - Verify all specifications"
	@echo "  gmake verify-tla    - Verify TLA+ specifications"
	@echo "  gmake verify-alloy  - Verify Alloy specifications"
	@echo "  gmake run           - Run the REPL"
	@echo "  gmake dev           - Start development server with live reload"
	@echo "  gmake build         - Build production version"
	@echo "  gmake test          - Run all tests"
	@echo "  gmake test-cljs     - Run ClojureScript unit tests"
	@echo "  gmake test-repl     - Run interactive REPL tests"
	@echo "  gmake banner        - Generate ASCII art banner"
	@echo "  gmake lint          - Run all linting (ClojureScript + shell)"
	@echo "  gmake lint-cljs     - Lint ClojureScript files"
	@echo "  gmake lint-shell    - Lint shell scripts"
	@echo "  gmake clean         - Clean build artifacts"
	@echo "  gmake dashboard     - Start tmux development dashboard"
	@echo "  gmake emacs         - Start Emacs in tmux for Clojure development"
	@echo "  gmake emacs-restart - Restart Emacs tmux session"
	@echo "  gmake release       - Create a new patch release"
	@echo "  gmake release-minor - Create a new minor release"
	@echo "  gmake release-major - Create a new major release"
	@echo ""
	@echo "Tool targets:"
	@echo "  gmake $(TLA_JAR)   - Download TLA+ tools"
	@echo "  gmake $(ALLOY_JAR) - Download Alloy analyzer"

# Install all dependencies
install: node_modules $(TLA_JAR) $(ALLOY_JAR)
	@echo "✅ All dependencies installed"

# Node modules dependency
node_modules: package.json
	@echo "Installing npm dependencies..."
	npm install
	@touch node_modules

# Create tools directory
$(TOOLS_DIR):
	@mkdir -p $@

# Download TLA+ tools (file target, depends on directory)
$(TLA_JAR): | $(TOOLS_DIR)
	@echo "Downloading TLA+ tools $(TLA_VERSION)..."
	cd $(TOOLS_DIR) && \
		fetch -o tla2tools.jar https://github.com/tlaplus/tlaplus/releases/download/v$(TLA_VERSION)/tla2tools.jar

# Download Alloy analyzer (file target, depends on directory)
$(ALLOY_JAR): | $(TOOLS_DIR)
	@echo "Downloading Alloy analyzer $(ALLOY_VERSION)..."
	cd $(TOOLS_DIR) && \
		fetch -o alloy.jar https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v$(ALLOY_VERSION)/org.alloytools.alloy.dist.jar

# Verify all specifications
verify: verify-tla verify-alloy
	@echo "✅ All specifications verified"

# Verify TLA+ specifications (depends on jar)
verify-tla: $(TLA_JAR)
	@echo "=== Verifying TLA+ Specifications ==="
	@for spec in specs/*.tla; do \
		if [ -f "$$spec" ]; then \
			echo -n "  Checking $$(basename $$spec)... "; \
			if java -cp $(TLA_JAR) tla2sany.SANY "$$spec" >/dev/null 2>&1; then \
				echo "✓"; \
			else \
				echo "✗"; \
				java -cp $(TLA_JAR) tla2sany.SANY "$$spec"; \
				exit 1; \
			fi; \
		fi; \
	done

# Verify Alloy specifications (depends on jar)
verify-alloy: $(ALLOY_JAR)
	@echo "=== Verifying Alloy Specifications ==="
	@for spec in specs/*.als specs/*.alloy; do \
		if [ -f "$$spec" ]; then \
			echo "  Found: $$spec"; \
		fi; \
	done
	@echo "  (Run 'java -jar $(ALLOY_JAR) <spec>' to check individually)"

# Run the REPL
run:
	@if [ ! -f .env ]; then \
		echo "Error: .env file not found"; \
		echo "Copy .env.example to .env and add your API key"; \
		exit 1; \
	fi
	./scripts/run.sh

# Start tmux development dashboard
dashboard:
	./scripts/tmux-dashboard.sh

# Restart dashboard
dashboard-restart:
	./scripts/tmux-dashboard.sh --restart

# Start Emacs in tmux for Clojure development
emacs:
	@echo "🚀 Starting Emacs environment for $(PROJECT_NAME)..."
	@# Create Emacs config if it doesn't exist
	@if [ ! -f $(PROJECT_NAME).el ]; then \
		echo "Creating $(PROJECT_NAME).el configuration..."; \
		echo ";; $(PROJECT_NAME) Emacs configuration" > $(PROJECT_NAME).el; \
		echo "(setq project-name \"$(PROJECT_NAME)\")" >> $(PROJECT_NAME).el; \
		echo "(setq project-root \"$(PROJECT_ROOT)\")" >> $(PROJECT_NAME).el; \
		echo "" >> $(PROJECT_NAME).el; \
		echo ";; Package setup" >> $(PROJECT_NAME).el; \
		echo "(require 'package)" >> $(PROJECT_NAME).el; \
		echo "(add-to-list 'package-archives '(\"melpa\" . \"https://melpa.org/packages/\") t)" >> $(PROJECT_NAME).el; \
		echo "(package-initialize)" >> $(PROJECT_NAME).el; \
		echo "" >> $(PROJECT_NAME).el; \
		echo ";; Install required packages if not present" >> $(PROJECT_NAME).el; \
		echo "(dolist (package '(cider clojure-mode paredit org))" >> $(PROJECT_NAME).el; \
		echo "  (unless (package-installed-p package)" >> $(PROJECT_NAME).el; \
		echo "    (package-refresh-contents)" >> $(PROJECT_NAME).el; \
		echo "    (package-install package)))" >> $(PROJECT_NAME).el; \
		echo "" >> $(PROJECT_NAME).el; \
		echo ";; Clojure setup" >> $(PROJECT_NAME).el; \
		echo "(add-hook 'clojure-mode-hook #'paredit-mode)" >> $(PROJECT_NAME).el; \
		echo "(add-hook 'cider-repl-mode-hook #'paredit-mode)" >> $(PROJECT_NAME).el; \
		echo "" >> $(PROJECT_NAME).el; \
		echo ";; CIDER configuration" >> $(PROJECT_NAME).el; \
		echo "(setq cider-cljs-lein-repl" >> $(PROJECT_NAME).el; \
		echo "      \"(do (require 'shadow.cljs.devtools.api)" >> $(PROJECT_NAME).el; \
		echo "           (shadow.cljs.devtools.api/nrepl-select :repl))\")" >> $(PROJECT_NAME).el; \
		echo "" >> $(PROJECT_NAME).el; \
		echo ";; Start in project root" >> $(PROJECT_NAME).el; \
		echo "(cd project-root)" >> $(PROJECT_NAME).el; \
		echo "" >> $(PROJECT_NAME).el; \
		echo ";; Display startup message" >> $(PROJECT_NAME).el; \
		echo "(message \"$(PROJECT_NAME) environment loaded. Use M-x cider-jack-in-cljs to start REPL\")" >> $(PROJECT_NAME).el; \
	fi
	@# Check if tmux session exists
	@if tmux has-session -t $(PROJECT_NAME) 2>/dev/null; then \
		echo "⚠️  Tmux session '$(PROJECT_NAME)' already exists"; \
		echo "   Attaching to existing session..."; \
		tmux attach-session -t $(PROJECT_NAME); \
	else \
		echo "📺 Starting tmux session '$(PROJECT_NAME)' with Emacs..."; \
		tmux new-session -d -s $(PROJECT_NAME) "emacs -nw -Q -l $(PROJECT_NAME).el"; \
		echo "📍 TTY: $$(tmux list-panes -t $(PROJECT_NAME) -F '#{pane_tty}')"; \
		echo ""; \
		echo "✅ Emacs started in tmux session '$(PROJECT_NAME)'"; \
		echo ""; \
		echo "📋 Quick commands:"; \
		echo "  Attach:  tmux attach -t $(PROJECT_NAME)"; \
		echo "  Detach:  C-b d"; \
		echo "  Kill:    tmux kill-session -t $(PROJECT_NAME)"; \
		echo ""; \
		echo "🔧 Emacs Clojure commands:"; \
		echo "  M-x cider-jack-in-cljs    - Start ClojureScript REPL"; \
		echo "  C-c C-e                   - Evaluate expression"; \
		echo "  C-c C-k                   - Load current buffer"; \
		echo "  C-c C-z                   - Switch to REPL"; \
		echo ""; \
		tmux attach-session -t $(PROJECT_NAME); \
	fi

# Restart Emacs tmux session
emacs-restart:
	@echo "🔄 Restarting Emacs session for $(PROJECT_NAME)..."
	@tmux kill-session -t $(PROJECT_NAME) 2>/dev/null || true
	@$(MAKE) emacs

# Development mode with live reload
dev: install
	@echo "🚀 Starting development mode with live reload..."
	@if ! command -v nodemon >/dev/null 2>&1; then \
		echo "📦 Installing nodemon..."; \
		npm install -g nodemon; \
	fi
	@echo "🔄 Starting REPL with auto-restart on file changes..."
	@GEMINI_LOG_ENABLED=true nodemon --watch src/ --watch target/ --ext cljs,js target/repl.js

# Build production version
build:
	npm run build

# ClojureScript unit tests
test-cljs:
	@echo "=== Running ClojureScript tests ==="
	@if command -v npx >/dev/null 2>&1; then \
		npx shadow-cljs compile test && node target/test.js; \
	else \
		echo "Error: npx not found"; \
		exit 1; \
	fi

# Run all tests
test: test-cljs test-repl
	@echo "✅ All tests completed"

# Run interactive REPL tests using expect
test-repl: build
	@echo "Running REPL interactive tests..."
	@if [ ! -f .env ] || ! grep -q GEMINI_API_KEY .env; then \
		echo "⚠️  Warning: GEMINI_API_KEY not found in .env file"; \
		echo "   Some tests may be skipped"; \
	fi
	@if command -v expect >/dev/null 2>&1; then \
		./scripts/test-repl.exp; \
	else \
		echo "Error: 'expect' command not found"; \
		echo "Install expect to run interactive tests"; \
		exit 1; \
	fi

# Generate ASCII art banner
resources/:
	mkdir -p resources

resources/repl-banner.txt: resources/
	@echo "Generating REPL banner..."
	@if command -v toilet >/dev/null 2>&1; then \
		toilet -f future "Gemini REPL" > $@; \
		echo "" >> $@; \
		echo "  🤖 Self-Hosting ClojureScript REPL" >> $@; \
		echo "  📝 Logging enabled via GEMINI_LOG_ENABLED" >> $@; \
		echo "  🔍 Type /help for commands" >> $@; \
		echo "" >> $@; \
		echo "✅ Generated banner at $@"; \
	else \
		echo "Warning: toilet not found, creating simple banner"; \
		echo "Gemini REPL" > $@; \
		echo "==========" >> $@; \
		echo "" >> $@; \
		echo "🤖 Self-Hosting ClojureScript REPL" >> $@; \
		echo "📝 Logging enabled via GEMINI_LOG_ENABLED" >> $@; \
		echo "🔍 Type /help for commands" >> $@; \
		echo "" >> $@; \
	fi

banner: resources/repl-banner.txt

# Main lint target
lint: lint-cljs lint-shell
	@echo "✅ All linting completed"

# ClojureScript linting
lint-cljs:
	@echo "=== Linting ClojureScript files ==="
	@if command -v clj-kondo >/dev/null 2>&1; then \
		clj-kondo --lint src/ test/ --config '{:output {:format :text}}' --fail-level error; \
	else \
		echo "Warning: clj-kondo not found. Skipping ClojureScript linting."; \
		echo "Install clj-kondo: https://github.com/clj-kondo/clj-kondo/blob/master/doc/install.md"; \
	fi

# Shell script linting
lint-shell:
	@echo "=== Linting shell scripts ==="
	@if command -v shellcheck >/dev/null 2>&1; then \
		find scripts/ -name "*.sh" -exec shellcheck {} \; || exit 1; \
	else \
		echo "Warning: shellcheck not found. Install: pkg install shellcheck"; \
		exit 1; \
	fi

# Install linting tools
install-lint-tools:
	@echo "Installing linting tools..."
	@if command -v npm >/dev/null 2>&1; then \
		npm install -g @clj-kondo/clj-kondo; \
	fi
	@if command -v pkg >/dev/null 2>&1; then \
		pkg install shellcheck; \
	elif command -v apt >/dev/null 2>&1; then \
		apt install shellcheck; \
	elif command -v brew >/dev/null 2>&1; then \
		brew install shellcheck; \
	fi
	@echo "✅ Linting tools installed"

# Check if tools are available
check-lint-tools:
	@echo "Checking linting tools..."
	@command -v clj-kondo >/dev/null 2>&1 && echo "✅ clj-kondo available" || echo "❌ clj-kondo missing"
	@command -v shellcheck >/dev/null 2>&1 && echo "✅ shellcheck available" || echo "❌ shellcheck missing"

# Check specifications (alias for verify)
spec-check: verify

# Clean build artifacts
clean:
	rm -rf target/ dist/ .shadow-cljs/ node_modules/
	@echo "✅ Build artifacts cleaned"

# Deep clean including tools
distclean: clean
	rm -rf $(TOOLS_DIR)
	@echo "✅ All artifacts and tools removed"

# Release targets
release: release-patch

release-patch: _release-precheck _release-bump-patch _release-create

release-minor: _release-precheck _release-bump-minor _release-create

release-major: _release-precheck _release-bump-major _release-create

# Internal release helpers
_release-bump-patch:
	@echo "📦 Bumping patch version..."
	@npm version patch --no-git-tag-version

_release-bump-minor:
	@echo "📦 Bumping minor version..."
	@npm version minor --no-git-tag-version

_release-bump-major:
	@echo "📦 Bumping major version..."
	@npm version major --no-git-tag-version

_release-create: build test-cljs lint
	@echo "🚀 Creating release..."
	@VERSION=$$(node -p "require('./package.json').version"); \
	echo "📋 Version: $$VERSION"; \
	echo ""; \
	echo "📝 Preparing release artifacts..."; \
	rm -rf dist/; \
	mkdir -p dist/; \
	echo ""; \
	echo "🔨 Building release version..."; \
	npx shadow-cljs release release; \
	echo ""; \
	echo "📦 Creating release archive..."; \
	tar -czf "gemini-repl-$$VERSION.tar.gz" \
		--exclude='.env' \
		--exclude='*.log' \
		--exclude='node_modules' \
		--exclude='target' \
		--exclude='.shadow-cljs' \
		--exclude='.git' \
		dist/ \
		src/ \
		test/ \
		specs/ \
		scripts/ \
		resources/ \
		package.json \
		package-lock.json \
		shadow-cljs.edn \
		Makefile \
		README.org \
		LICENSE \
		.env.example || exit 1; \
	echo ""; \
	echo "📋 Committing version bump..."; \
	git add package.json package-lock.json; \
	git commit -m "chore(release): bump version to $$VERSION" --trailer "Co-Authored-By: Claude <noreply@anthropic.com>" || exit 1; \
	echo ""; \
	echo "🏷️  Creating git tag..."; \
	git tag -a "v$$VERSION" -m "Release v$$VERSION" || exit 1; \
	echo ""; \
	echo "📝 Generating release notes..."; \
	LAST_TAG=$$(git describe --tags --abbrev=0 HEAD^ 2>/dev/null || echo ""); \
	if [ -z "$$LAST_TAG" ]; then \
		COMMITS=$$(git log --oneline --pretty=format:"- %s"); \
	else \
		COMMITS=$$(git log $$LAST_TAG..HEAD --oneline --pretty=format:"- %s"); \
	fi; \
	echo "## Release v$$VERSION"; \
	echo ""; \
	echo "### Changes"; \
	echo "$$COMMITS"; \
	echo ""; \
	echo "### Installation"; \
	echo '```bash'; \
	echo "tar -xzf gemini-repl-$$VERSION.tar.gz"; \
	echo "cd gemini-repl-$$VERSION"; \
	echo "npm install"; \
	echo "gmake run"; \
	echo '```'; \
	echo ""; \
	echo "✅ Release v$$VERSION created successfully!"; \
	echo ""; \
	echo "📤 Next steps:"; \
	echo "  1. Review the changes"; \
	echo "  2. Push to GitHub: git push && git push --tags"; \
	echo "  3. Create GitHub release:"; \
	echo "     gh release create v$$VERSION gemini-repl-$$VERSION.tar.gz \\"; \
	echo "       --title \"Release v$$VERSION\" \\"; \
	echo "       --notes-file RELEASE_NOTES.md"; \
	echo ""

_release-precheck:
	@echo "🔍 Pre-release checks..."
	@if [ -n "$$(git status --porcelain)" ]; then \
		echo "❌ Error: Working directory has uncommitted changes"; \
		echo "   Please commit or stash your changes before releasing"; \
		exit 1; \
	fi
	@if ! command -v gh >/dev/null 2>&1; then \
		echo "⚠️  Warning: GitHub CLI (gh) not found"; \
		echo "   Install with: pkg install gh"; \
	fi
	@echo "✅ Pre-release checks passed"
