.PHONY: help setup build dev run test clean lint verify install

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
	@echo "  clean    - Clean build artifacts"

install:
	@npm install
	@echo "Dependencies installed"

setup:
	@bash create-dirs.sh
	@echo "Directory structure created"

build: install
	@npm run build

dev: install
	@npm run dev

run: build
	@bash scripts/run.sh

test: install
	@npm test

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
