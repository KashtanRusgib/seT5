#!/usr/bin/env python3
# glossary_checker.py — Automate checks for test glossary documentation
# Parses test sources for names, checks against TESTS_GLOSSARY_OF_ALL_TESTS.md.

import re
import os
import pandas as pd
from io import StringIO

def extract_test_names():
    """Extract all test names from test source files."""
    names = set()
    for root, dirs, files in os.walk('tests/'):
        for file in files:
            if file.endswith('.c'):
                with open(os.path.join(root, file), 'r') as f:
                    content = f.read()
                    matches = re.findall(r'CHECK\("([^"]+)"', content)
                    names.update(matches)
    return sorted(names)

def check_glossary(names, glossary_path='seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md'):
    """Check if names are in the glossary."""
    with open(glossary_path, 'r') as f:
        md_content = f.read()
    table_start = md_content.find('| Test ID |')
    if table_start == -1:
        print("Glossary table not found.")
        return []
    table = md_content[table_start:]
    df = pd.read_csv(StringIO(table), sep='|', skiprows=1, engine='python')
    df.columns = df.columns.str.strip()
    if 'Name' not in df.columns:
        print("Name column not found in glossary.")
        return []
    glossary_names = set(df['Name'].dropna())
    missing = [name for name in names if name not in glossary_names]
    return missing

def main():
    print("Extracting test names from sources...")
    names = extract_test_names()
    print(f"Found {len(names)} test names.")

    print("Checking glossary...")
    missing = check_glossary(names)
    if missing:
        print(f"Missing from glossary: {missing}")
    else:
        print("All tests documented in glossary.")

if __name__ == '__main__':
    main()