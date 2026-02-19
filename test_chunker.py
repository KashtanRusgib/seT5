#!/usr/bin/env python3
# test_chunker.py — Script to chunk test verification into batches for AI sessions
# Extracts test names from source files, assigns sequential IDs, filters for range 5371-6000, and splits into batches.

import re
import os
import json

def extract_test_names(file_path):
    """Extract test names from a test file."""
    names = []
    with open(file_path, 'r') as f:
        content = f.read()
        # Find CHECK calls or function names; adjust for custom harness
        matches = re.findall(r'CHECK\("([^"]+)"', content)
        names.extend(matches)
    return names

def main():
    test_dir = 'tests/'
    tests = []
    current_id = 1
    for file in sorted(os.listdir(test_dir)):
        if file.endswith('.c'):
            names = extract_test_names(os.path.join(test_dir, file))
            for name in names:
                tests.append({'id': current_id, 'name': name, 'file': file})
                current_id += 1

    print(f"Total extracted tests: {len(tests)}")

    # Filter for range 5371-6000 (if exists)
    target_tests = [t for t in tests if 5371 <= t['id'] <= 6000]
    if not target_tests:
        print("No tests in 5371-6000; planning for additions starting from 5016.")
        # For planning, create placeholders
        for i in range(5016, 6001):
            target_tests.append({'id': i, 'name': f'placeholder_test_{i}', 'file': 'future.c'})
    else:
        print(f"Tests in range: {len(target_tests)}")

    # Split into batches of 50
    batch_size = 50
    batches = [target_tests[i:i + batch_size] for i in range(0, len(target_tests), batch_size)]

    for idx, batch in enumerate(batches):
        with open(f'batch_{idx+1}.json', 'w') as f:
            json.dump(batch, f, indent=2)
        print(f"Batch {idx+1}: {len(batch)} tests ({batch[0]['id']}-{batch[-1]['id']}) saved to batch_{idx+1}.json")

if __name__ == '__main__':
    main()