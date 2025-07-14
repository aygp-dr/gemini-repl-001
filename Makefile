.PHONY: help build test clean setup verify

help:
	@echo "Available targets:"
	@echo "  setup    - Create directory structure"
	@echo "  build    - Build the project"
	@echo "  test     - Run tests"
	@echo "  verify   - Verify formal specifications"
	@echo "  clean    - Clean build artifacts"

setup:
	@bash create-dirs.sh
	@echo "Directory structure created"

build:
	@echo "Build target - to be implemented"

test:
	@echo "Test target - to be implemented"

verify:
	@echo "Verification target - to be implemented"

clean:
	@rm -rf target/ dist/ tmp/*
	@echo "Cleaned build artifacts"
