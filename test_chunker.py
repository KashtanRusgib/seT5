#!/usr/bin/env python3
"""
test_chunker.py - Extract test FUNCTIONS and generate batch plans

Parses test files for test function definitions (not individual assertions),
assigns sequential IDs to all test functions, and generates batch plans for
AI-assisted test generation while managing context windows.

Usage:
    python3 test_chunker.py                    # Extract all tests
    python3 test_chunker.py --range 5371 6000  # Focus on specific range
"""

import os
import re
import json
from pathlib import Path
import argparse

# Configuration
TEST_DIRS = ['tests/', 'tools/compiler/tests/']
TARGET_TESTS = 6000
BATCH_SIZE = 50

# Test function regex patterns
TEST_FUNCTION_PATTERNS = [
    re.compile(r'^\s*static\s+void\s+(test_[a-zA-Z0-9_]+)\s*\(', re.MULTILINE),
    re.compile(r'^\s*void\s+(test_[a-zA-Z0-9_]+)\s*\(', re.MULTILINE),
    re.compile(r'^\s*static\s+int\s+(test_[a-zA-Z0-9_]+)\s*\(', re.MULTILINE),
    re.compile(r'^\s*int\s+(test_[a-zA-Z0-9_]+)\s*\(', re.MULTILINE),
]


def extract_test_functions(file_path):
    """Extract all test function names from a C test file."""
    functions = []
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
            
            # Find all test function definitions
            for pattern in TEST_FUNCTION_PATTERNS:
                matches = pattern.findall(content)
                functions.extend(matches)
            
            # Remove duplicates while preserving order
            seen = set()
            unique_functions = []
            for func in functions:
                if func not in seen:
                    seen.add(func)
                    unique_functions.append(func)
            
            return unique_functions
    except Exception as e:
        print(f"Warning: Could not parse {file_path}: {e}")
        return []


def extract_all_tests():
    """Extract all test functions from repository with metadata."""
    tests = []
    test_id = 1
    
    for test_dir in TEST_DIRS:
        if not os.path.exists(test_dir):
            print(f"Warning: Directory {test_dir} not found")
            continue
        
        # Walk directory tree
        for root, dirs, files in os.walk(test_dir):
            # Skip backup and generated directories
            dirs[:] = [d for d in dirs if d not in ['build', '.git', '__pycache__']]
            
            for filename in sorted(files):
                if not filename.endswith('.c'):
                    continue
                
                file_path = os.path.join(root, filename)
                
                # Extract test functions
                functions = extract_test_functions(file_path)
                
                for func_name in functions:
                    tests.append({
                        'id': test_id,
                        'name': func_name,
                        'file': file_path,
                        'suite': filename.replace('.c', '').replace('test_', ''),
                    })
                    test_id += 1
    
    return tests


def assign_theme(test_id):
    """Assign a thematic area for batch generation based on test ID range."""
    themes = [
        (1, 1000, "Core ternary operations and arithmetic"),
        (1001, 2000, "Memory safety and allocation"),
        (2001, 3000, "IPC and capabilities"),
        (3001, 4000, "Scheduler and concurrency"),
        (4001, 5000, "Hardware integration and patents"),
        (5001, 5100, "Ternary memory allocation/boundaries"),
        (5101, 5200, "IPC with Unknown states (K3 logic)"),
        (5201, 5300, "Scheduler in mixed-radix contexts"),
        (5301, 5400, "Hardware ALU/TALU operations"),
        (5401, 5500, "Side-channel resistance"),
        (5501, 5600, "Epistemic logic and hesitation"),
        (5601, 5700, "Guardian trit stability"),
        (5701, 5800, "TCAM and network search"),
        (5801, 5900, "Formal verification tie-ins"),
        (5901, 6000, "Integration and regression"),
    ]
    
    for start, end, theme in themes:
        if start <= test_id <= end:
            return theme
    
    return "General testing"


def generate_batch_plan(tests, start_id, end_id):
    """Generate batch plan for AI-assisted test generation."""
    # Filter tests in range
    range_tests = [t for t in tests if start_id <= t['id'] <= end_id]
    
    # Determine how many tests need to be generated
    existing = len(range_tests)
    needed = (end_id - start_id + 1) - existing
    
    print(f"\n=== Batch Plan for Tests {start_id}-{end_id} ===")
    print(f"Existing tests: {existing}")
    print(f"Tests to generate: {needed}")
    
    if needed <= 0:
        print("✅ Range fully covered!")
        return range_tests
    
    # Split into batches
    batches = []
    current_id = start_id + existing
    
    while current_id <= end_id:
        batch_end = min(current_id + BATCH_SIZE - 1, end_id)
        theme = assign_theme(current_id)
        
        batches.append({
            'batch_num': len(batches) + 1,
            'start_id': current_id,
            'end_id': batch_end,
            'count': batch_end - current_id + 1,
            'theme': theme,
        })
        
        current_id = batch_end + 1
    
    # Generate task files for each batch
    os.makedirs('test_generation_tasks', exist_ok=True)
    
    for batch in batches:
        task_file = f"test_generation_tasks/batch_{batch['start_id']}_{batch['end_id']}.md"
        
        with open(task_file, 'w') as f:
            f.write(f"# Test Generation Batch {batch['batch_num']}\n\n")
            f.write(f"**Range**: Tests {batch['start_id']}-{batch['end_id']}\n")
            f.write(f"**Count**: {batch['count']} tests\n")
            f.write(f"**Theme**: {batch['theme']}\n\n")
            f.write("## Instructions\n\n")
            f.write("Generate C test functions following the seT5/seT6 patterns:\n\n")
            f.write("1. Use pattern: `static void test_name(void) { ... }`\n")
            f.write("2. Include meaningful property checks (no tautologies)\n")
            f.write("3. Focus on ternary logic properties (K3, Unknown handling)\n")
            f.write("4. Test edge cases: overflow, underflow, Unknown propagation\n")
            f.write("5. Use existing test harness (CHECK/ASSERT macros)\n\n")
            f.write("## Example Tests\n\n")
            f.write("Reference existing tests in the same thematic area.\n")
            f.write("See tests/test_sigma9.c, tests/test_sel4_ternary.c for patterns.\n\n")
            f.write("## Output\n\n")
            f.write(f"Create: `tests/test_batch_{batch['start_id']}_{batch['end_id']}.c`\n")
            f.write(f"Document in: `seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md`\n")
        
        print(f"  Batch {batch['batch_num']}: {batch['start_id']}-{batch['end_id']} ({batch['count']} tests) - {batch['theme']}")
        print(f"    Task file: {task_file}")
    
    return batches


def main():
    parser = argparse.ArgumentParser(description='Extract test functions and generate batch plans')
    parser.add_argument('--range', nargs=2, type=int, metavar=('START', 'END'),
                        help='Focus on specific test ID range')
    parser.add_argument('--output', default='test_inventory.json',
                        help='Output file for test inventory (default: test_inventory.json)')
    args = parser.parse_args()
    
    print("🔍 Extracting test functions from seT5/seT6...")
    tests = extract_all_tests()
    
    print(f"\n📊 Summary:")
    print(f"  Total test functions found: {len(tests)}")
    print(f"  Target: {TARGET_TESTS}")
    
    if len(tests) >= TARGET_TESTS:
        print(f"  ✅ Already at or above target! Current: {len(tests)}, Target: {TARGET_TESTS}")
    else:
        print(f"  📝 Need to generate: {TARGET_TESTS - len(tests)} more tests")
    
    # Save inventory
    with open(args.output, 'w') as f:
        json.dump(tests, f, indent=2)
    print(f"\n💾 Saved inventory to {args.output}")
    
    # Generate batch plan if requested or needed
    if args.range:
        start_id, end_id = args.range
        generate_batch_plan(tests, start_id, end_id)
    elif len(tests) < TARGET_TESTS:
        # Auto-generate plan for remaining tests
        start_id = len(tests) + 1
        end_id = TARGET_TESTS
        generate_batch_plan(tests, start_id, end_id)
    
    # Show test distribution by file
    print(f"\n📁 Test Distribution:")
    file_counts = {}
    for test in tests:
        file_counts[test['file']] = file_counts.get(test['file'], 0) + 1
    
    # Show top 10 files by test count
    sorted_files = sorted(file_counts.items(), key=lambda x: x[1], reverse=True)[:10]
    for file, count in sorted_files:
        print(f"  {count:4d} tests: {file}")


if __name__ == '__main__':
    main()
