# Gemini REPL Makefile
# For FreeBSD, use gmake

.PHONY: help all install verify-tools run dev build clean test spec-check

# Default target
all: help

# Help target
help:
	@echo "Gemini REPL - Available targets:"
	@echo ""
	@echo "  gmake help          - Show this help message"
	@echo "  gmake install       - Install all dependencies and tools"
	@echo "  gmake verify-tools  - Verify formal methods tools are installed"
	@echo "  gmake run           - Run the REPL"
	@echo "  gmake dev           - Start development server"
	@echo "  gmake build         - Build production version"
	@echo "  gmake test          - Run tests"
	@echo "  gmake spec-check    - Check formal specifications"
	@echo "  gmake clean         - Clean build artifacts"
	@echo ""
	@echo "Setup targets:"
	@echo "  gmake install-npm   - Install Node.js dependencies"
	@echo "  gmake install-tla   - Install TLA+ tools"
	@echo "  gmake install-alloy - Install Alloy analyzer"

# Install all dependencies
install: install-npm install-tla install-alloy verify-tools
	@echo "✅ All dependencies installed"

# Install npm dependencies
install-npm:
	@echo "Installing npm dependencies..."
	npm install

# Install TLA+ tools
install-tla:
	@echo "Installing TLA+ tools..."
	@mkdir -p ~/tools/formal-methods
	@if [ ! -f ~/tools/formal-methods/tla2tools.jar ]; then \
		echo "Downloading TLA+ tools..."; \
		cd ~/tools/formal-methods && \
		fetch -o tla2tools.jar https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar; \
	else \
		echo "TLA+ tools already installed"; \
	fi

# Install Alloy
install-alloy:
	@echo "Installing Alloy analyzer..."
	@mkdir -p ~/tools/formal-methods
	@if [ ! -f ~/tools/formal-methods/alloy.jar ]; then \
		echo "Downloading Alloy..."; \
		cd ~/tools/formal-methods && \
		fetch -o alloy.jar https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v5.1.0/org.alloytools.alloy.dist.jar; \
	else \
		echo "Alloy already installed"; \
	fi

# Verify tools are working
verify-tools:
	@echo "=== Verifying Tools ==="
	@echo -n "Node.js: "
	@node --version || echo "❌ Not found"
	@echo -n "npm: "
	@npm --version || echo "❌ Not found"
	@echo -n "Java: "
	@java -version 2>&1 | head -1 || echo "❌ Not found"
	@echo ""
	@echo "Formal methods tools:"
	@if [ -f ~/tools/formal-methods/tla2tools.jar ]; then \
		echo "✅ TLA+ jar found"; \
		if command -v tlc >/dev/null 2>&1; then \
			echo "✅ tlc wrapper available"; \
		else \
			echo "❌ tlc wrapper not in PATH"; \
		fi; \
	else \
		echo "❌ TLA+ jar not found - run: gmake install-tla"; \
	fi
	@if [ -f ~/tools/formal-methods/alloy.jar ]; then \
		echo "✅ Alloy jar found"; \
		if command -v alloy >/dev/null 2>&1; then \
			echo "✅ alloy wrapper available"; \
		else \
			echo "❌ alloy wrapper not in PATH"; \
		fi; \
	else \
		echo "❌ Alloy jar not found - run: gmake install-alloy"; \
	fi

# Run the REPL
run:
	@if [ ! -f .env ]; then \
		echo "Error: .env file not found"; \
		echo "Copy .env.example to .env and add your API key"; \
		exit 1; \
	fi
	./scripts/run.sh

# Development mode
dev:
	npm run dev

# Build production version
build:
	npm run build

# Run tests
test:
	@echo "Running tests..."
	@if [ -f package.json ] && grep -q "test" package.json; then \
		npm test; \
	else \
		echo "No tests configured"; \
	fi

# Check specifications
spec-check: verify-tools
	@if [ -f ~/tools/formal-methods/tla2tools.jar ]; then \
		./check-specs.sh; \
	else \
		echo "Error: TLA+ tools not installed"; \
		echo "Run: gmake install-tla"; \
		exit 1; \
	fi

# Clean build artifacts
clean:
	rm -rf target/ dist/ .shadow-cljs/ node_modules/
	@echo "✅ Build artifacts cleaned"