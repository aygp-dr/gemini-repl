#!/bin/sh
# Check all formal specifications in the project

echo "=== Formal Specification Checker ==="
echo

# Check if tools are available
check_tool() {
    if ! command -v "$1" >/dev/null 2>&1; then
        echo "ERROR: $1 not found. Please run SPECS-SETUP.org first."
        exit 1
    fi
}

check_tool tlc
check_tool tla2sany
check_tool alloy

# Check TLA+ specifications
echo "Checking TLA+ specifications..."
for spec in specs/*.tla; do
    if [ -f "$spec" ]; then
        printf "  Checking %s... " "$(basename "$spec")"
        if tla2sany "$spec" >/dev/null 2>&1; then
            echo "✓"
        else
            echo "✗"
            tla2sany "$spec"
            exit 1
        fi
    fi
done

echo
echo "All specifications checked successfully!"
echo
echo "To run model checking: tlc specs/interfaces.tla"
echo "To open Alloy: alloy specs/state.alloy"