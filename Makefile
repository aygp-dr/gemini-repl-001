.PHONY: help setup build dev run test clean lint verify install banner

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
	@echo "  clean    - Clean build artifacts"

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
		toilet -f mono12 "GEMINI REPL" > resources/repl-banner.txt; \
		echo "Banner generated"; \
	else \
		echo "GEMINI REPL v0.1.0" > resources/repl-banner.txt; \
		echo "==================" >> resources/repl-banner.txt; \
		echo "Banner created (toilet not available)"; \
	fi

build: install banner
	@npm run build

dev: install
	@npm run dev

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
