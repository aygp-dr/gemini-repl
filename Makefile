# Gemini REPL Makefile
# For FreeBSD, use gmake

# Tool versions
TLA_VERSION := 1.8.0
ALLOY_VERSION := 5.1.0

# Local tool paths
TOOLS_DIR := tools/formal-methods
TLA_JAR := $(TOOLS_DIR)/tla2tools.jar
ALLOY_JAR := $(TOOLS_DIR)/alloy.jar

# Phony targets
.PHONY: help all install verify run dev build clean test test-repl spec-check verify-alloy verify-tla banner lint lint-cljs lint-shell install-lint-tools check-lint-tools

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
	@echo "  gmake test          - Run tests"
	@echo "  gmake test-repl     - Run interactive REPL tests"
	@echo "  gmake banner        - Generate ASCII art banner"
	@echo "  gmake lint          - Run all linting (ClojureScript + shell)"
	@echo "  gmake lint-cljs     - Lint ClojureScript files"
	@echo "  gmake lint-shell    - Lint shell scripts"
	@echo "  gmake clean         - Clean build artifacts"
	@echo "  gmake dashboard     - Start tmux development dashboard"
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

# Run tests
test: test-repl
	@echo "Running tests..."
	@if [ -f package.json ] && grep -q "test" package.json; then \
		npm test; \
	else \
		echo "No tests configured"; \
	fi

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
		clj-kondo --lint src/ test/ --config '{:output {:format :text}}' || exit 1; \
	else \
		echo "Warning: clj-kondo not found. Install: npm install -g @clj-kondo/clj-kondo"; \
		exit 1; \
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
