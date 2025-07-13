# Makefile for formal specifications

.PHONY: all check-syntax check-tla check-alloy clean

TLA_SPECS := $(wildcard *.tla)
ALLOY_SPECS := $(wildcard *.als)

all: check-syntax

check-syntax: check-tla check-alloy

check-tla: $(TLA_SPECS)
	@echo "=== Checking TLA+ Specifications ==="
	@for spec in $(TLA_SPECS); do \
		echo "Checking $$spec..."; \
		tla2sany $$spec || exit 1; \
	done
	@echo "✓ All TLA+ specs passed syntax check"

check-alloy: $(ALLOY_SPECS)
	@echo "=== Alloy Specifications ==="
	@for spec in $(ALLOY_SPECS); do \
		echo "Found: $$spec"; \
	done
	@echo "Run 'make run-alloy SPEC=<filename>' to check a specific spec"

run-tlc:
	@if [ -z "$(SPEC)" ]; then \
		echo "Usage: make run-tlc SPEC=<filename>"; \
		exit 1; \
	fi
	tlc $(SPEC)

run-alloy:
	@if [ -z "$(SPEC)" ]; then \
		echo "Usage: make run-alloy SPEC=<filename>"; \
		exit 1; \
	fi
	alloy $(SPEC)

clean:
	rm -f *.old *.tex *.dvi *.pdf
	rm -rf states/
