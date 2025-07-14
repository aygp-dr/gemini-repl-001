.PHONY: help setup build dev run test clean lint verify install banner dashboard release-patch release-minor release-major

help:
	@echo "Available targets:"
	@echo "  install  - Install npm dependencies"
	@echo "  setup    - Create directory structure"
	@echo "  build    - Build the project"
	@echo "  dev      - Start development server"
	@echo "  run      - Run the REPL"
	@echo "  test     - Run tests"
	@echo "  lint     - Run linter"
	@echo "  verify   - Verify formal specifications"
	@echo "  banner   - Generate ASCII banner"
	@echo "  dashboard - Launch tmux development dashboard"
	@echo "  clean    - Clean build artifacts"
	@echo ""
	@echo "Release targets:"
	@echo "  release-patch - Create patch release (0.0.x)"
	@echo "  release-minor - Create minor release (0.x.0)"
	@echo "  release-major - Create major release (x.0.0)"

install:
	@npm install
	@echo "Dependencies installed"

setup:
	@bash create-dirs.sh
	@echo "Directory structure created"

resources/:
	@mkdir -p resources/

banner: resources/
	@if command -v toilet >/dev/null 2>&1; then \
		toilet -f future "GEMINI REPL" > resources/repl-banner.txt; \
		echo "Banner generated"; \
	else \
		echo "GEMINI REPL v0.1.0" > resources/repl-banner.txt; \
		echo "==================" >> resources/repl-banner.txt; \
		echo "Banner created (toilet not available)"; \
	fi

build: install banner
	@npm run build

dev: install
	@if command -v nodemon >/dev/null 2>&1; then \
		GEMINI_LOG_ENABLED=true nodemon --watch src --watch target --ext cljs,js --exec "make run"; \
	else \
		npm install -g nodemon && \
		GEMINI_LOG_ENABLED=true nodemon --watch src --watch target --ext cljs,js --exec "make run"; \
	fi

run: build
	@bash scripts/run.sh

test: install
	@npm test
	@if command -v expect >/dev/null 2>&1; then \
		echo "Running REPL tests..."; \
		./scripts/test-repl.exp; \
	else \
		echo "Expect not installed, skipping REPL tests"; \
	fi

lint:
	@echo "Linting ClojureScript files..."
	@npx clj-kondo --lint src test || true

verify:
	@echo "Running formal verification..."
	@$(MAKE) -C specs verify

clean:
	@npm run clean
	@rm -rf node_modules
	@echo "Cleaned build artifacts"

dashboard:
	@bash scripts/tmux-dashboard.sh

# Release targets
release-patch: release-prep
	@bash scripts/release.sh patch

release-minor: release-prep
	@bash scripts/release.sh minor

release-major: release-prep
	@bash scripts/release.sh major

release-prep:
	@echo "Checking for uncommitted changes..."
	@git diff-index --quiet HEAD -- || (echo "Error: Uncommitted changes found" && exit 1)
	@echo "Running tests..."
	@$(MAKE) test
	@echo "Running lint..."
	@$(MAKE) lint
	@echo "Building project..."
	@$(MAKE) build
