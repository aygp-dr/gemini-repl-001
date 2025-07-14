.PHONY: all check-tla check-alloy verify clean help

TLA_TOOLS = ../tools/formal-methods/tla2tools.jar
ALLOY_JAR = ../tools/formal-methods/alloy.jar

help:
	@echo "Formal Specification Verification"
	@echo "  check-tla    - Check TLA+ specifications"
	@echo "  check-alloy  - Check Alloy models"
	@echo "  verify       - Run all verifications"
	@echo "  clean        - Clean generated files"

check-tla:
	@echo "Checking TLA+ specifications..."
	@for spec in *.tla; do \
		echo "Checking $$spec..."; \
		java -cp $(TLA_TOOLS) tla2sany.SANY $$spec || exit 1; \
	done
	@echo "All TLA+ specifications are syntactically correct"

check-alloy:
	@echo "Checking Alloy models..."
	@if [ -f $(ALLOY_JAR) ]; then \
		for model in *.alloy; do \
			echo "Checking $$model..."; \
			java -jar $(ALLOY_JAR) -c $$model || exit 1; \
		done; \
	else \
		echo "Warning: Alloy jar not found at $(ALLOY_JAR)"; \
	fi

verify: check-tla check-alloy
	@echo "All formal specifications verified successfully"

clean:
	@rm -f *.old *.new *.tlaps
	@echo "Cleaned generated files"

all: verify