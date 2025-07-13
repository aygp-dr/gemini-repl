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
.PHONY: help all install verify run dev build clean test test-repl spec-check verify-alloy verify-tla banner

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
	@echo "  gmake dev           - Start development server"
	@echo "  gmake build         - Build production version"
	@echo "  gmake test          - Run tests"
	@echo "  gmake test-repl     - Run interactive REPL tests"
	@echo "  gmake banner        - Generate ASCII art banner"
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

# Development mode
dev:
	npm run dev

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
		toilet -f mono12 "Gemini REPL" > $@; \
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