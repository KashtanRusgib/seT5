# -*- coding: utf-8 -*-
"""
seT6 Documentation Configuration — Sphinx + Doxygen (Breathe)

Generates API docs from Doxygen-annotated C headers and proof stubs.
Supports C and Rust (via domains) for the seT6 ternary compiler project.

Build: cd docs && sphinx-build -b html . _build/html

Reference: seL4 documentation style (sel4.systems)

SPDX-License-Identifier: GPL-2.0
"""

# -- Project information ---------------------------------------------------

project = 'seT6 — Secure Embedded Ternary Microkernel'
copyright = '2026, seT6 Contributors'
author = 'seT6 AI Swarm'
version = '0.1.0'
release = '0.1.0-phase1'

# -- General configuration -------------------------------------------------

extensions = [
    'sphinx.ext.autodoc',
    'sphinx.ext.todo',
    'sphinx.ext.mathjax',
    'sphinx.ext.viewcode',
]

# Breathe configuration (Doxygen integration) — enable when breathe installed
# extensions.append('breathe')
# breathe_projects = { 'seT6': '../doxygen/xml' }
# breathe_default_project = 'seT6'

primary_domain = 'c'
highlight_language = 'c'

# -- Source settings --------------------------------------------------------

templates_path = ['_templates']
exclude_patterns = ['_build', 'Thumbs.db', '.DS_Store']
source_suffix = '.rst'
master_doc = 'index'

# -- HTML output ------------------------------------------------------------

html_theme = 'alabaster'
html_theme_options = {
    'description': 'Formally verified ternary microkernel based on seL4',
    'github_user': 'KashtanRusgib',
    'github_repo': 'seT6',
    'github_button': True,
    'fixed_sidebar': True,
}
html_static_path = ['_static']

# -- MathJax configuration (Kleene notation macros) ------------------------

mathjax3_config = {
    'tex': {
        'macros': {
            'tand': r'\wedge',
            'tor':  r'\vee',
            'tnot': r'\neg',
            'unk':  r'\mathbf{U}',
            'trit': r'\mathtt{trit}',
        }
    }
}

# -- TODO extension ---------------------------------------------------------

todo_include_todos = True
