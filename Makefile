# Makefile for MathLogic

# Default target
all:
	@echo "Use 'make verify' to run the verification script"

# Run the verification script
verify:
	python3 tests/verify_syntax.py

# Run the tests
run_tests:
	python3 -m unittest discover tests

test: run_tests

