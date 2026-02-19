#!/usr/bin/env python3
"""
glossary_checker.py - Validate test documentation completeness

Cross-checks test functions extracted from source files against the
TESTS_GLOSSARY_OF_ALL_TESTS.md documentation. Identifies missing entries,
inconsistencies, and potential tautologies.

Usage:
    python3 glossary_checker.py
"""

import os
import re
import json
from pathlib import Path
import sys

GLOSSARY_PATH = 'seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md'
TEST_INVENTORY = 'test_inventory.json'


def parse_glossary():
    """Parse the markdown glossary file to extract documented tests."""
    if not os.path.exists(GLOSSARY_PATH):
        print(f"❌ Error: Glossary not found at {GLOSSARY_PATH}")
        return {}
    
    with open(GLOSSARY_PATH, 'r', encoding='utf-8') as f:
        content = f.read()
    
    documented_tests = {}
    
    # Parse suite index table
    suite_pattern = r'\|\s*(\d+)\s*\|\s*([^|]+)\s*\|\s*`([^`]+)`'
    matches = re.findall(suite_pattern, content)
    
    for suite_num, suite_name, source_file in matches:
        suite_name = suite_name.strip()
        source_file = source_file.strip()
        
        # Store suite info
        if source_file not in documented_tests:
            documented_tests[source_file] = {
                'suite_num': int(suite_num),
                'suite_name': suite_name,
                'tests': []
            }
    
    # Parse individual test tables (after each "## Suite N:" header)
    suite_section_pattern = r'## Suite \d+:.*?\n\n(?:.*?\n)*?\| # \| Line \| Test Description'
    suite_sections = re.finditer(suite_section_pattern, content, re.MULTILINE)
    
    # Extract test function names from detailed tables
    # Pattern: Line numbers followed by test names/descriptions
    test_line_pattern = r'\|\s*\d+\s*\|\s*L?\d+\s*\|\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*\|'
    
    for section in suite_sections:
        section_text = section.group(0)
        test_matches = re.findall(test_line_pattern, section_text)
        
        # Try to associate with a file
        # This is approximate - in practice, the glossary structure needs
        # consistent patterns for reliable parsing
        for test_name in test_matches:
            if test_name.startswith('test_'):
                # Add to the first matching documented file
                # (This is simplified - real implementation should track context)
                for file_key in documented_tests:
                    documented_tests[file_key]['tests'].append(test_name)
                    break
    
    return documented_tests


def check_for_tautologies(file_path):
    """Scan test file for potential tautology assertions."""
    tautologies = []
    
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
        
        # Patterns that indicate tautologies
        tautology_patterns = [
            r'assert\(1\s*==\s*1\)',
            r'assert\(true\)',
            r'assert\(TRUE\)',
            r'ASSERT\(1\s*==\s*1\)',
            r'ASSERT\(true\)',
            r'CHECK\("[^"]*",\s*1\s*==\s*1\)',
            r'CHECK\("[^"]*",\s*true\)',
        ]
        
        for line_num, line in enumerate(lines, 1):
            for pattern in tautology_patterns:
                if re.search(pattern, line, re.IGNORECASE):
                    tautologies.append({
                        'line': line_num,
                        'content': line.strip()
                    })
    
    except Exception as e:
        print(f"Warning: Could not scan {file_path} for tautologies: {e}")
    
    return tautologies


def main():
    print("🔍 Checking test documentation completeness...\n")
    
    # Load test inventory
    if not os.path.exists(TEST_INVENTORY):
        print(f"⚠️  Warning: Test inventory not found at {TEST_INVENTORY}")
        print("    Run: python3 test_chunker.py first to generate inventory")
        sys.exit(1)
    
    with open(TEST_INVENTORY, 'r') as f:
        extracted_tests = json.load(f)
    
    print(f"📊 Loaded {len(extracted_tests)} test functions from source files")
    
    # Parse glossary
    print(f"📖 Parsing glossary: {GLOSSARY_PATH}")
    documented_tests = parse_glossary()
    
    documented_count = sum(len(suite['tests']) for suite in documented_tests.values())
    print(f"📝 Found {len(documented_tests)} documented suites with {documented_count} tests\n")
    
    # Cross-check: Find tests in source but not in glossary
    documented_names = set()
    for suite in documented_tests.values():
        documented_names.update(suite['tests'])
    
    extracted_names = {test['name'] for test in extracted_tests}
    
    missing_in_glossary = extracted_names - documented_names
    extra_in_glossary = documented_names - extracted_names
    
    # Find undocumented files
    documented_files = set(documented_tests.keys())
    extracted_files = {test['file'] for test in extracted_tests}
    
    # Normalize paths for comparison
    def normalize_path(p):
        return str(Path(p)).replace('\\', '/')
    
    documented_files_norm = {normalize_path(f) for f in documented_files}
    extracted_files_norm = {normalize_path(f) for f in extracted_files}
    
    undocumented_files = []
    for extracted_file in sorted(extracted_files_norm):
        # Check if this file appears in any documented path
        found = False
        for doc_file in documented_files_norm:
            if extracted_file.endswith(doc_file) or doc_file.endswith(os.path.basename(extracted_file)):
                found = True
                break
        if not found:
            undocumented_files.append(extracted_file)
    
    # Scan for tautologies
    print("🔬 Scanning for potential tautologies...")
    files_with_tautologies = []
    
    for test in extracted_tests[:20]:  # Sample first 20 files to avoid slowdown
        tautologies = check_for_tautologies(test['file'])
        if tautologies:
            files_with_tautologies.append({
                'file': test['file'],
                'tautologies': tautologies
            })
    
    # Report findings
    print("\n" + "="*70)
    print("📋 VALIDATION REPORT")
    print("="*70 + "\n")
    
    issues_found = False
    
    if undocumented_files:
        issues_found = True
        print("⚠️  ISSUE 1: Undocumented Test Files")
        print(f"   The following {len(undocumented_files)} test files are not documented in the glossary:\n")
        for file in undocumented_files:
            # Count tests in this file
            count = sum(1 for t in extracted_tests if normalize_path(t['file']) == file)
            print(f"   - {file} ({count} test functions)")
        print()
    
    if missing_in_glossary:
        issues_found = True
        print(f"⚠️  ISSUE 2: Test Functions Missing from Glossary")
        print(f"   Found {len(missing_in_glossary)} test functions in source not documented:\n")
        # Show first 20
        for name in sorted(list(missing_in_glossary))[:20]:
            # Find file
            test_info = next((t for t in extracted_tests if t['name'] == name), None)
            if test_info:
                print(f"   - {name} ({Path(test_info['file']).name})")
        if len(missing_in_glossary) > 20:
            print(f"   ... and {len(missing_in_glossary) - 20} more")
        print()
    
    if files_with_tautologies:
        issues_found = True
        print("⚠️  ISSUE 3: Potential Tautologies Detected")
        print(f"   Found suspicious assertions in {len(files_with_tautologies)} files:\n")
        for item in files_with_tautologies:
            print(f"   {Path(item['file']).name}:")
            for taut in item['tautologies'][:3]:  # Show first 3
                print(f"     Line {taut['line']}: {taut['content']}")
        print()
    
    # Count discrepancy
    total_source = len(extracted_tests)
    total_glossary = documented_count
    
    if total_source != total_glossary:
        issues_found = True
        print(f"⚠️  ISSUE 4: Count Mismatch")
        print(f"   Source files: {total_source} test functions")
        print(f"   Glossary:     {total_glossary} documented tests")
        print(f"   Difference:   {abs(total_source - total_glossary)}")
        print()
    
    if not issues_found:
        print("✅ All checks passed! Documentation is consistent.\n")
        return 0
    else:
        print("="*70)
        print("\n📝 Recommended Actions:")
        print("  1. Document undocumented test files in glossary")
        print("  2. Add missing test function entries to appropriate suites")
        print("  3. Review and fix tautologies with meaningful assertions")
        print("  4. Re-run this checker after updates\n")
        return 1


if __name__ == '__main__':
    sys.exit(main())
