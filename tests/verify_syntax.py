#!/usr/bin/env python3

import os
import re

# Define the directory to verify
DIR_TO_VERIFY = "/botworkspace/MathLogic"

# Define the file extensions to check
FILE_EXTENSIONS = [".py", ".ml", ".txt"]

# Define the patterns to check for syntax errors
PATTERNS = [
    r"def\s+\w+\(.*\):\s*$",  # Function definitions
    r"class\s+\w+:",  # Class definitions
    r"import\s+\w+",  # Import statements
    r"from\s+\w+\s+import\s+\w+",  # From import statements
    r"if\s+.*:",  # If statements
    r"for\s+.*in\s+.*:",  # For loops
    r"while\s+.*:",  # While loops
    r"try:",  # Try blocks
    r"except\s+.*:",  # Except blocks
    r"finally:",  # Finally blocks
    r"with\s+.*:",  # With statements
    r"#.*",  # Comments
    r"\w+\s*=\s*.*",  # Variable assignments
    r"\w+\(.*\)",  # Function calls
    r"\w+\.\w+\(.*\)",  # Method calls
    r"\w+\.\w+",  # Attribute access
    r"\w+\[.*\]",  # List indexing
    r"\w+\{.*\}",  # Dictionary access
    r"\w+\s*\+\s*\w+",  # Addition
    r"\w+\s*-\s*\w+",  # Subtraction
    r"\w+\s*\*\s*\w+",  # Multiplication
    r"\w+\s*/\s*\w+",  # Division
    r"\w+\s*%\s*\w+",  # Modulus
    r"\w+\s*\*\*\s*\w+",  # Exponentiation
    r"\w+\s*&\s*\w+",  # Bitwise AND
    r"\w+\s*\|\s*\w+",  # Bitwise OR
    r"\w+\s*\^\s*\w+",  # Bitwise XOR
    r"\w+\s*<<\s*\w+",  # Left shift
    r"\w+\s*>>\s*\w+",  # Right shift
    r"\w+\s*==\s*\w+",  # Equality
    r"\w+\s*!=\s*\w+",  # Inequality
    r"\w+\s*<\s*\w+",  # Less than
    r"\w+\s*<=\s*\w+",  # Less than or equal to
    r"\w+\s*>\s*\w+",  # Greater than
    r"\w+\s*>=\s*\w+",  # Greater than or equal to
    r"\w+\s*and\s*\w+",  # Logical AND
    r"\w+\s*or\s*\w+",  # Logical OR
    r"\w+\s*not\s*\w+",  # Logical NOT
    r"\w+\s*in\s*\w+",  # Membership
    r"\w+\s*not\s+in\s*\w+",  # Non-membership
    r"\w+\s*is\s*\w+",  # Identity
    r"\w+\s*is\s+not\s*\w+",  # Non-identity
    r"lambda\s+.*:",  # Lambda functions
    r"yield\s+.*",  # Yield statements
    r"raise\s+.*",  # Raise statements
    r"assert\s+.*",  # Assert statements
    r"break",  # Break statements
    r"continue",  # Continue statements
    r"pass",  # Pass statements
    r"return\s+.*",  # Return statements
    r"del\s+.*",  # Delete statements
    r"global\s+.*",  # Global statements
    r"nonlocal\s+.*",  # Nonlocal statements
    r"@\w+",  # Decorators
    r"\w+\s*=\s*lambda\s+.*:",  # Lambda assignments
    r"\w+\s*=\s*yield\s+.*",  # Yield assignments
    r"\w+\s*=\s*raise\s+.*",  # Raise assignments
    r"\w+\s*=\s*assert\s+.*",  # Assert assignments
    r"\w+\s*=\s*break",  # Break assignments
    r"\w+\s*=\s*continue",  # Continue assignments
    r"\w+\s*=\s*pass",  # Pass assignments
    r"\w+\s*=\s*return\s+.*",  # Return assignments
    r"\w+\s*=\s*del\s+.*",  # Delete assignments
    r"\w+\s*=\s*global\s+.*",  # Global assignments
    r"\w+\s*=\s*nonlocal\s+.*"  # Nonlocal assignments
]

# Function to verify the syntax of a file
def verify_file(file_path):
    with open(file_path, 'r') as file:
        content = file.read()
        for pattern in PATTERNS:
            if not re.search(pattern, content):
                print(f"Pattern not found in {file_path}: {pattern}")

# Function to verify the syntax of all files in a directory
def verify_directory(directory):
    for root, _, files in os.walk(directory):
        for file in files:
            if any(file.endswith(ext) for ext in FILE_EXTENSIONS):
                file_path = os.path.join(root, file)
                verify_file(file_path)

# Verify the syntax of all files in the directory
verify_directory(DIR_TO_VERIFY)
