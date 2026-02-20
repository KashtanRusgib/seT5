#!/usr/bin/env python3
"""
grok_api.py — seT6 Grok-4-1-fast-reasoning API Integration

Calls xAI's Grok API via the FEB192026FORGITHUB Codespace secret.
Used by the RSI flywheel, curiosity proofs, and optimization loops.

Usage:
    from grok_api import grok_reason, grok_optimize, grok_curiosity_proof

    # Direct reasoning query
    result = grok_reason("Suggest trit ops for 100x speedup, prove non-coercive")

    # Optimization with repo context
    patch = grok_optimize(context="...", instruction="Fix failing test X")

    # Curiosity proof verification
    valid = grok_curiosity_proof("Does this advancement improve truth-seeking?")

Environment:
    FEB192026FORGITHUB  — xAI API key (Codespace secret)
"""

import os
import json
import sys

try:
    import requests
except ImportError:
    print("WARNING: 'requests' not installed. Run: pip install requests", file=sys.stderr)
    requests = None

API_URL = "https://api.x.ai/v1/chat/completions"
MODEL = "grok-4-1-fast-reasoning"
MAX_TOKENS = 8192


def _get_api_key():
    """Retrieve API key from environment."""
    key = os.environ.get("FEB192026FORGITHUB", "")
    if not key:
        raise EnvironmentError(
            "FEB192026FORGITHUB secret not set. "
            "Add it as a Codespace secret at: "
            "https://github.com/settings/codespaces"
        )
    return key


def _call_grok(messages, max_tokens=MAX_TOKENS, temperature=0.7):
    """Low-level Grok API call. Returns the response text."""
    if requests is None:
        raise ImportError("requests library required: pip install requests")

    headers = {
        "Authorization": f"Bearer {_get_api_key()}",
        "Content-Type": "application/json",
    }
    payload = {
        "model": MODEL,
        "messages": messages,
        "max_tokens": max_tokens,
        "temperature": temperature,
    }

    resp = requests.post(API_URL, headers=headers, json=payload, timeout=120)
    resp.raise_for_status()
    data = resp.json()

    return data["choices"][0]["message"]["content"]


def grok_reason(query, system_prompt=None, max_tokens=MAX_TOKENS):
    """
    General reasoning query to Grok-4-1-fast-reasoning.

    Args:
        query: The question or instruction
        system_prompt: Optional system context (defaults to seT6 context)
        max_tokens: Max response tokens

    Returns:
        str: Grok's response text
    """
    if system_prompt is None:
        system_prompt = (
            "You are an expert in ternary computing, balanced ternary logic, "
            "Kleene K₃ semantics, mixed-radix arithmetic, and formal verification. "
            "You are assisting with seT6 — a ternary-first microkernel OS with "
            "Gödel Machine RSI capabilities. Be precise, provide code when asked, "
            "and ensure all suggestions are non-coercive and truth-seeking."
        )
    messages = [
        {"role": "system", "content": system_prompt},
        {"role": "user", "content": query},
    ]
    return _call_grok(messages, max_tokens=max_tokens)


def grok_optimize(context, instruction, max_tokens=MAX_TOKENS):
    """
    Request code optimization from Grok with repo context.

    Args:
        context: Relevant code/test context
        instruction: What to optimize or fix

    Returns:
        str: Grok's response (may contain unified diff patches)
    """
    system_prompt = (
        "You are a ternary computing compiler/kernel optimization expert. "
        "Respond with unified diff patches when fixing code. "
        "Ensure all changes maintain Sigma 9 (100% test pass rate). "
        "Use trit guards: -1=deny coercive, 0=query human, +1=proceed if safe."
    )
    user_msg = f"## Repository Context\n{context}\n\n## Instruction\n{instruction}"
    messages = [
        {"role": "system", "content": system_prompt},
        {"role": "user", "content": user_msg},
    ]
    return _call_grok(messages, max_tokens=max_tokens)


def grok_curiosity_proof(hypothesis, evidence=""):
    """
    Verify a curiosity/beauty hypothesis via Grok reasoning.

    Args:
        hypothesis: The claim to verify
        evidence: Supporting evidence or context

    Returns:
        dict: {"valid": bool, "reasoning": str, "confidence": float}
    """
    system_prompt = (
        "You are a truth-seeking verifier for the seT6 ternary computing project. "
        "Evaluate hypotheses using Kleene K₃ logic: True (+1), Unknown (0), False (-1). "
        "Respond in JSON format with keys: valid (bool), reasoning (str), "
        "confidence (float 0-1), trit_value (int: -1, 0, or 1)."
    )
    user_msg = f"## Hypothesis\n{hypothesis}"
    if evidence:
        user_msg += f"\n\n## Evidence\n{evidence}"
    user_msg += "\n\nRespond in JSON format."

    raw = _call_grok(
        [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_msg},
        ],
        max_tokens=2048,
        temperature=0.3,
    )

    # Try to parse JSON from response
    try:
        # Handle markdown code blocks
        if "```json" in raw:
            raw = raw.split("```json")[1].split("```")[0]
        elif "```" in raw:
            raw = raw.split("```")[1].split("```")[0]
        return json.loads(raw.strip())
    except (json.JSONDecodeError, IndexError):
        return {
            "valid": None,
            "reasoning": raw,
            "confidence": 0.0,
            "trit_value": 0,
        }


def grok_patent_alignment(patent_id, optimization_query):
    """
    Query Grok for patent alignment analysis.

    Args:
        patent_id: Patent identifier (e.g., "CN119652311A")
        optimization_query: What to optimize for

    Returns:
        str: Analysis and recommendations
    """
    return grok_reason(
        f"Analyze patent {patent_id} alignment with seT6 ternary computing. "
        f"Specific query: {optimization_query}. "
        f"Focus on: balanced ternary advantages, mixed-radix opportunities, "
        f"and non-coercive implementation paths.",
        max_tokens=4096,
    )


# ── CLI Interface ──
if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python3 src/grok_api.py <query>")
        print("  or:  python3 src/grok_api.py --curiosity <hypothesis>")
        print("  or:  python3 src/grok_api.py --optimize <context_file> <instruction>")
        sys.exit(1)

    if sys.argv[1] == "--curiosity":
        result = grok_curiosity_proof(" ".join(sys.argv[2:]))
        print(json.dumps(result, indent=2))
    elif sys.argv[1] == "--optimize" and len(sys.argv) >= 4:
        with open(sys.argv[2]) as f:
            ctx = f.read()
        result = grok_optimize(ctx, " ".join(sys.argv[3:]))
        print(result)
    else:
        result = grok_reason(" ".join(sys.argv[1:]))
        print(result)
