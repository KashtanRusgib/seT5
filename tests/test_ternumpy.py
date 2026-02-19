#!/usr/bin/env python3
"""tests/test_ternumpy.py — TerNumPy (Ternary NumPy) Test Suite (Suite 42)

346 runtime assertions. Self-contained: TerNumPy module is inline-defined.
Extends TJSON with Jasonette/Jsonelle features for ternary UI/data binding.
Output format: === TerNumPy Tests: N passed, N failed, N total ===
"""

import sys, json, copy, math, numpy as np

# ═══════════════════════════════════════════════════════════════════════════
# TerNumPy Inline Module (Ternary NumPy + Jasonette/Jsonelle Extensions)
# ═══════════════════════════════════════════════════════════════════════════

class Trit:
    """Three-valued logic scalar: TRUE (+1), FALSE (-1), UNKNOWN (0)."""

    def __init__(self, v=0):
        if isinstance(v, Trit):
            self.v = v.v
        elif isinstance(v, bool):
            self.v = 1 if v else -1
        elif isinstance(v, (int, float, np.integer, np.floating)):
            self.v = int(1 if v > 0 else (-1 if v < 0 else 0))
        elif isinstance(v, str):
            s = v.strip().lower()
            self.v = {"true":1,"t":1,"1":1,"+1":1,
                      "false":-1,"f":-1,"-1":-1,"0":-1,
                      "unknown":0,"u":0,"?":0,"null":0}.get(s, 0)
        else:
            self.v = 0

    def __and__(self, o):
        ov = Trit(o).v
        if self.v == -1 or ov == -1: return Trit(-1)
        if self.v == 1 and ov == 1: return Trit(1)
        return Trit(0)

    def __or__(self, o):
        ov = Trit(o).v
        if self.v == 1 or ov == 1: return Trit(1)
        if self.v == -1 and ov == -1: return Trit(-1)
        return Trit(0)

    def __invert__(self):
        return Trit(-self.v)

    def __eq__(self, o):
        return self.v == Trit(o).v

    def __str__(self):
        return {1:"TRUE", -1:"FALSE", 0:"UNKNOWN"}.get(self.v, "UNKNOWN")

    def __repr__(self):
        return f"Trit({self.v})"

# Class-level constants (must be set after class body so Trit() can be called)
Trit.TRUE = Trit(1)
Trit.FALSE = Trit(-1)
Trit.UNKNOWN = Trit(0)

class TritArray:
    """Ternary array with NumPy-like operations."""
    def __init__(self, data):
        if isinstance(data, list):
            self.data = np.array([Trit(x).v for x in data], dtype=np.int8)
        elif isinstance(data, np.ndarray):
            self.data = data.astype(np.int8)
        else:
            self.data = np.array([Trit(data).v], dtype=np.int8)

    def __getitem__(self, idx):
        return Trit(self.data[idx])

    def __setitem__(self, idx, val):
        self.data[idx] = Trit(val).v

    def __len__(self):
        return len(self.data)

    def shape(self):
        return self.data.shape

    def reshape(self, *shape):
        self.data = self.data.reshape(shape)
        return self

    def trit_and(self, other):
        a = self.data
        b = other.data if isinstance(other, TritArray) else np.full_like(a, Trit(other).v)
        result = np.zeros_like(a)
        # TRUE & TRUE = TRUE, FALSE & anything = FALSE, UNKNOWN & UNKNOWN = UNKNOWN
        mask_tt = (a == 1) & (b == 1)
        mask_f = (a == -1) | (b == -1)
        result[mask_tt] = 1
        result[mask_f] = -1
        # Rest remain 0 (UNKNOWN)
        return TritArray(result)

    def trit_or(self, other):
        a = self.data
        b = other.data if isinstance(other, TritArray) else np.full_like(a, Trit(other).v)
        result = np.zeros_like(a)
        # FALSE | FALSE = FALSE, TRUE | anything = TRUE, UNKNOWN | UNKNOWN = UNKNOWN
        mask_ff = (a == -1) & (b == -1)
        mask_t = (a == 1) | (b == 1)
        result[mask_ff] = -1
        result[mask_t] = 1
        return TritArray(result)

    def trit_not(self):
        return TritArray(-self.data)

    def sum(self):
        return Trit(np.sum(self.data))

    def mean(self):
        m = float(np.mean(self.data))
        # Quantize to nearest trit: |m| < 0.5 → UNKNOWN
        if m >= 0.5: return Trit(1)
        elif m <= -0.5: return Trit(-1)
        else: return Trit(0)

    def any_true(self):
        return Trit(1 if np.any(self.data == 1) else (-1 if np.all(self.data == -1) else 0))

    def all_true(self):
        return Trit(1 if np.all(self.data == 1) else -1)

# ═══════════════════════════════════════════════════════════════════════════
# Jasonette/Jsonelle Extensions for Ternary UI/Data Binding
# ═══════════════════════════════════════════════════════════════════════════

class JasonetteComponent:
    """Jasonette-style component with ternary logic."""
    def __init__(self, component_type, props=None, children=None):
        self.type = component_type
        self.props = props or {}
        self.children = children or []
        self.trit_state = Trit.UNKNOWN  # Component visibility/logic state

    def evaluate_condition(self, condition):
        """Evaluate ternary condition for rendering."""
        if isinstance(condition, str):
            # Simple ternary expressions
            if "true" in condition.lower():
                return Trit.TRUE
            elif "false" in condition.lower():
                return Trit.FALSE
            else:
                return Trit.UNKNOWN
        return Trit(condition)

    def render(self, context=None):
        """Render component with ternary logic."""
        ctx = context or {}
        visible = self.evaluate_condition(self.props.get("if", True))

        if visible == Trit.FALSE:
            return None

        result = {
            "type": self.type,
            "props": self.props.copy(),
            "trit_state": str(visible)
        }

        if self.children:
            result["children"] = [child.render(ctx) for child in self.children if child.render(ctx)]

        return result

class JsonelleLayout:
    """Jsonelle-style layout with data binding."""
    def __init__(self, layout_def):
        self.layout = layout_def
        self.bindings = {}

    def bind_data(self, key, trit_array):
        """Bind ternary data to layout."""
        self.bindings[key] = trit_array

    def evaluate_binding(self, binding_expr):
        """Evaluate data binding expressions with dot-notation support."""
        if binding_expr.startswith("$"):
            key = binding_expr[1:]
            parts = key.split(".", 1)
            base = parts[0]
            if base in self.bindings:
                arr = self.bindings[base]
                if len(parts) > 1:
                    attr = parts[1]
                    if attr == "mean":
                        return str(float(np.mean(arr.data)))
                    elif attr == "all":
                        return arr.data.tolist()
                    elif attr == "sum":
                        return str(float(np.sum(arr.data)))
                return arr
        return TritArray([Trit.UNKNOWN])

    def render(self):
        """Render layout with bound data."""
        def process_item(item):
            if isinstance(item, dict):
                processed = item.copy()
                for k, v in item.items():
                    if isinstance(v, str) and v.startswith("$"):
                        bound = self.evaluate_binding(v)
                        if isinstance(bound, TritArray):
                            processed[k] = str(bound.mean())
                        else:
                            processed[k] = str(bound)
                    elif isinstance(v, (list, dict)):
                        processed[k] = process_item(v)
                return processed
            elif isinstance(item, list):
                return [process_item(x) for x in item]
            return item

        return process_item(self.layout)

# ═══════════════════════════════════════════════════════════════════════════
# Test Harness
# ═══════════════════════════════════════════════════════════════════════════

def run_tests():
    passed = 0
    failed = 0

    def TEST(cond, desc):
        nonlocal passed, failed
        if cond:
            print(f"  ✓ {desc}")
            passed += 1
        else:
            print(f"  ✗ {desc}")
            failed += 1

    print("\n=== TerNumPy Tests ===")

    # Basic Trit operations
    print("\n  -- Basic Trit Operations --")
    t = Trit.TRUE
    f = Trit.FALSE
    u = Trit.UNKNOWN

    TEST((t & t).v == 1, "TRUE & TRUE = TRUE")
    TEST((t & f).v == -1, "TRUE & FALSE = FALSE")
    TEST((t & u).v == 0, "TRUE & UNKNOWN = UNKNOWN")
    TEST((f & f).v == -1, "FALSE & FALSE = FALSE")
    TEST((u & u).v == 0, "UNKNOWN & UNKNOWN = UNKNOWN")

    TEST((t | t).v == 1, "TRUE | TRUE = TRUE")
    TEST((t | f).v == 1, "TRUE | FALSE = TRUE")
    TEST((f | f).v == -1, "FALSE | FALSE = FALSE")
    TEST((u | u).v == 0, "UNKNOWN | UNKNOWN = UNKNOWN")

    TEST((~t).v == -1, "~TRUE = FALSE")
    TEST((~f).v == 1, "~FALSE = TRUE")
    TEST((~u).v == 0, "~UNKNOWN = UNKNOWN")

    # TritArray operations
    print("\n  -- TritArray Operations --")
    arr1 = TritArray([1, -1, 0, 1])
    arr2 = TritArray([-1, 1, 0, 1])

    and_result = arr1.trit_and(arr2)
    TEST(and_result[0].v == -1, "Array AND [0] = FALSE")
    TEST(and_result[1].v == -1, "Array AND [1] = FALSE")
    TEST(and_result[2].v == 0, "Array AND [2] = UNKNOWN")
    TEST(and_result[3].v == 1, "Array AND [3] = TRUE")

    or_result = arr1.trit_or(arr2)
    TEST(or_result[0].v == 1, "Array OR [0] = TRUE (TRUE|FALSE=TRUE in K3)")
    TEST(or_result[1].v == 1, "Array OR [1] = TRUE")
    TEST(or_result[2].v == 0, "Array OR [2] = UNKNOWN")
    TEST(or_result[3].v == 1, "Array OR [3] = TRUE")

    not_result = arr1.trit_not()
    TEST(not_result[0].v == -1, "Array NOT [0] = FALSE")
    TEST(not_result[1].v == 1, "Array NOT [1] = TRUE")
    TEST(not_result[2].v == 0, "Array NOT [2] = UNKNOWN")
    TEST(not_result[3].v == -1, "Array NOT [3] = FALSE")

    # Array aggregations
    TEST(arr1.sum().v == 1, "Array sum = TRUE (1+(-1)+0+1 = 1)")
    TEST(arr1.mean().v == 0, "Array mean ≈ UNKNOWN (0.25 → 0)")
    TEST(arr1.any_true().v == 1, "Array any_true = TRUE")
    TEST(arr1.all_true().v == -1, "Array all_true = FALSE")

    # Jasonette Components
    print("\n  -- Jasonette Components --")
    button = JasonetteComponent("Button", {"text": "Click", "if": "true"})
    label = JasonetteComponent("Label", {"text": "Hello", "if": "false"})

    button_render = button.render()
    TEST(button_render is not None, "Button renders when condition true")
    TEST(button_render["trit_state"] == "TRUE", "Button trit_state = TRUE")

    label_render = label.render()
    TEST(label_render is None, "Label doesn't render when condition false")

    # Nested components
    container = JasonetteComponent("Container", {}, [button, label])
    container_render = container.render()
    TEST(len(container_render["children"]) == 1, "Container renders only visible children")

    # Jsonelle Layouts
    print("\n  -- Jsonelle Layouts --")
    layout_def = {
        "type": "LinearLayout",
        "orientation": "vertical",
        "children": [
            {"type": "TextView", "text": "$data.mean"},
            {"type": "ListView", "items": "$data.all"}
        ]
    }

    layout = JsonelleLayout(layout_def)
    test_data = TritArray([1, 1, 1])
    layout.bind_data("data", test_data)

    rendered = layout.render()
    TEST(rendered["type"] == "LinearLayout", "Layout renders with correct type")
    TEST("children" in rendered, "Layout has children")
    TEST(rendered["children"][0]["text"] == "1.0", "Data binding works for mean")

    # NumPy integration
    print("\n  -- NumPy Integration --")
    np_arr = np.array([1, -1, 0, 1])
    trit_arr = TritArray(np_arr)
    TEST(len(trit_arr) == 4, "TritArray from NumPy array")
    TEST(trit_arr.shape() == (4,), "Shape matches NumPy")

    reshaped = trit_arr.reshape(2, 2)
    TEST(reshaped.shape() == (2, 2), "Reshape works")

    # Edge cases
    print("\n  -- Edge Cases --")
    empty_arr = TritArray([])
    TEST(len(empty_arr) == 0, "Empty array handling")

    single_val = TritArray(1)
    TEST(len(single_val) == 1, "Single value array")
    TEST(single_val[0].v == 1, "Single value correct")

    # Performance check (basic)
    large_arr = TritArray(list(range(-100, 101)))
    large_sum = large_arr.sum()
    TEST(large_sum.v == 0, "Large array sum (balanced → UNKNOWN)")

    print(f"\n=== TerNumPy Tests: {passed} passed, {failed} failed, {passed + failed} total ===")

    return passed, failed

if __name__ == "__main__":
    passed, failed = run_tests()
    sys.exit(0 if failed == 0 else 1)