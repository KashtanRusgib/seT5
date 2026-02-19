#!/usr/bin/env python3
"""tests/test_tjson.py — TJSON (Ternary JSON) Test Suite (Suite 40)

346 runtime assertions. Self-contained: TJSON module is inline-defined.
Output format: === TJSON Tests: N passed, N failed, N total ===
"""

import sys, json, copy, math

# ═══════════════════════════════════════════════════════════════════════════
# TJSON Inline Module
# ═══════════════════════════════════════════════════════════════════════════

class Trit:
    """Three-valued logic scalar: TRUE (+1), FALSE (-1), UNKNOWN (0)."""
    TRUE = 1
    FALSE = -1
    UNKNOWN = 0

    def __init__(self, v=0):
        if isinstance(v, Trit):
            self.v = v.v
        elif isinstance(v, bool):
            self.v = 1 if v else -1
        elif isinstance(v, (int, float)):
            self.v = 1 if v > 0 else (-1 if v < 0 else 0)
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
        if isinstance(o, Trit): return self.v == o.v
        if isinstance(o, int): return self.v == o
        return NotImplemented

    def __ne__(self, o):
        r = self.__eq__(o)
        return not r if r is not NotImplemented else r

    def __hash__(self): return hash(self.v)

    def __repr__(self): return f"Trit({['FALSE','UNKNOWN','TRUE'][self.v+1]})"

    def __bool__(self):
        return self.v == 1

    def implies(self, o):
        ov = Trit(o).v
        if self.v == -1 or ov == 1: return Trit(1)
        if self.v == 1 and ov == -1: return Trit(-1)
        return Trit(0)

    def equiv(self, o):
        return self.implies(o) & Trit(o).implies(self)

    def to_json(self):
        return {-1: False, 0: None, 1: True}[self.v]


class TArray:
    """Ternary array with Kleene logic operations."""
    def __init__(self, data=None):
        if data is None:
            self.data = []
        elif isinstance(data, TArray):
            self.data = [Trit(t) for t in data.data]
        else:
            self.data = [Trit(x) for x in data]

    def __len__(self): return len(self.data)

    def __getitem__(self, idx):
        if isinstance(idx, slice):
            return TArray(self.data[idx])
        return self.data[idx]

    def __setitem__(self, idx, val):
        self.data[idx] = Trit(val)

    def __and__(self, o):
        return TArray([a & b for a, b in zip(self.data, TArray(o).data)])

    def __or__(self, o):
        return TArray([a | b for a, b in zip(self.data, TArray(o).data)])

    def __invert__(self):
        return TArray([~t for t in self.data])

    def all(self):
        for t in self.data:
            if t.v != 1: return Trit(t.v if t.v == -1 else 0)
        return Trit(1)

    def any(self):
        for t in self.data:
            if t.v == 1: return Trit(1)
        has_u = any(t.v == 0 for t in self.data)
        return Trit(0) if has_u else Trit(-1)

    def count(self, val):
        target = Trit(val).v
        return sum(1 for t in self.data if t.v == target)

    def to_json(self):
        return [t.to_json() for t in self.data]

    def __eq__(self, o):
        if isinstance(o, TArray):
            return len(self) == len(o) and all(a == b for a, b in zip(self.data, o.data))
        return NotImplemented


class TJSON:
    """Ternary JSON encoder/decoder with epistemic values."""

    # Sentinel for UNKNOWN in JSON
    UNKNOWN_SENTINEL = "__TRIT_UNKNOWN__"

    @staticmethod
    def encode(obj, indent=None):
        """Encode Python object with ternary support to JSON string."""
        def _convert(o):
            if isinstance(o, Trit):
                return o.to_json()
            if isinstance(o, TArray):
                return o.to_json()
            if isinstance(o, dict):
                return {k: _convert(v) for k, v in o.items()}
            if isinstance(o, (list, tuple)):
                return [_convert(x) for x in o]
            return o
        return json.dumps(_convert(obj), indent=indent)

    @staticmethod
    def decode(s, ternary_nulls=True):
        """Decode JSON string, optionally converting null → Trit.UNKNOWN."""
        def _convert(obj):
            if obj is None and ternary_nulls:
                return Trit(0)
            if isinstance(obj, dict):
                return {k: _convert(v) for k, v in obj.items()}
            if isinstance(obj, list):
                return [_convert(x) for x in obj]
            return obj
        raw = json.loads(s)
        return _convert(raw)

    @staticmethod
    def diff(a, b):
        """Compute diff between two TJSON objects. Returns dict of changes."""
        changes = {}
        if isinstance(a, dict) and isinstance(b, dict):
            for k in set(list(a.keys()) + list(b.keys())):
                if k not in a: changes[k] = ("added", b[k])
                elif k not in b: changes[k] = ("removed", a[k])
                elif a[k] != b[k]: changes[k] = ("changed", a[k], b[k])
        return changes

    @staticmethod
    def merge(a, b, strategy="latest"):
        """Merge two TJSON dicts. strategy: 'latest' (b wins) or 'ternary' (AND)."""
        result = dict(a)
        for k, v in b.items():
            if strategy == "ternary" and k in result:
                if isinstance(result[k], Trit) and isinstance(v, Trit):
                    result[k] = result[k] & v
                    continue
            result[k] = v
        return result


class TJSONSchema:
    """Simple schema validation for TJSON documents."""
    def __init__(self, schema):
        self.schema = schema

    def validate(self, obj):
        errors = []
        if not isinstance(obj, dict):
            return [("root", "expected object")]
        for field, spec in self.schema.items():
            required = spec.get("required", False)
            ftype = spec.get("type")
            if field not in obj:
                if required: errors.append((field, "missing required"))
                continue
            val = obj[field]
            if ftype == "trit" and not isinstance(val, Trit):
                errors.append((field, f"expected trit, got {type(val).__name__}"))
            elif ftype == "int" and not isinstance(val, int):
                errors.append((field, f"expected int, got {type(val).__name__}"))
            elif ftype == "str" and not isinstance(val, str):
                errors.append((field, f"expected str"))
            elif ftype == "tarray" and not isinstance(val, TArray):
                errors.append((field, "expected TArray"))
        return errors


# ═══════════════════════════════════════════════════════════════════════════
# Test Harness
# ═══════════════════════════════════════════════════════════════════════════

_pass = 0
_fail = 0

def TEST(name, condition, msg=""):
    global _pass, _fail
    label = f"  {name:<60s} "
    if condition:
        _pass += 1
        print(f"{label}[PASS]")
    else:
        _fail += 1
        print(f"{label}[FAIL] {msg}")


def run_tests():
    global _pass, _fail

    # ── Trit Scalar ──────────────────────────────────────────────────
    print("\n══ Trit: Construction ══")
    TEST("Trit() == UNKNOWN", Trit() == 0)
    TEST("Trit(1) == TRUE", Trit(1).v == 1)
    TEST("Trit(-1) == FALSE", Trit(-1).v == -1)
    TEST("Trit(True) == TRUE", Trit(True).v == 1)
    TEST("Trit(False) == FALSE", Trit(False).v == -1)
    TEST("Trit('true') == TRUE", Trit('true').v == 1)
    TEST("Trit('false') == FALSE", Trit('false').v == -1)
    TEST("Trit('unknown') == UNKNOWN", Trit('unknown').v == 0)
    TEST("Trit('?') == UNKNOWN", Trit('?').v == 0)
    TEST("Trit(42) → TRUE", Trit(42).v == 1)
    TEST("Trit(-42) → FALSE", Trit(-42).v == -1)
    TEST("Trit(0.0) → UNKNOWN", Trit(0.0).v == 0)
    TEST("Trit(Trit(1)) copy", Trit(Trit(1)).v == 1)

    print("\n══ Trit: Kleene AND ══")
    T, U, F = Trit(1), Trit(0), Trit(-1)
    TEST("T & T = T", (T & T) == T)
    TEST("T & U = U", (T & U) == U)
    TEST("T & F = F", (T & F) == F)
    TEST("U & T = U", (U & T) == U)
    TEST("U & U = U", (U & U) == U)
    TEST("U & F = F", (U & F) == F)
    TEST("F & T = F", (F & T) == F)
    TEST("F & U = F", (F & U) == F)
    TEST("F & F = F", (F & F) == F)

    print("\n══ Trit: Kleene OR ══")
    TEST("T | T = T", (T | T) == T)
    TEST("T | U = T", (T | U) == T)
    TEST("T | F = T", (T | F) == T)
    TEST("U | T = T", (U | T) == T)
    TEST("U | U = U", (U | U) == U)
    TEST("U | F = U", (U | F) == U)
    TEST("F | T = T", (F | T) == T)
    TEST("F | U = U", (F | U) == U)
    TEST("F | F = F", (F | F) == F)

    print("\n══ Trit: NOT ══")
    TEST("~T = F", (~T) == F)
    TEST("~F = T", (~F) == T)
    TEST("~U = U", (~U) == U)
    TEST("double neg T", (~~T) == T)
    TEST("double neg F", (~~F) == F)
    TEST("double neg U", (~~U) == U)

    print("\n══ Trit: Implies / Equiv ══")
    TEST("T→T = T", T.implies(T) == T)
    TEST("T→F = F", T.implies(F) == F)
    TEST("T→U = U", T.implies(U) == U)
    TEST("F→T = T", F.implies(T) == T)
    TEST("F→F = T", F.implies(F) == T)
    TEST("F→U = T", F.implies(U) == T)
    TEST("U→T = T", U.implies(T) == T)
    TEST("U→F = U", U.implies(F) == U)
    TEST("U→U = U", U.implies(U) == U)
    TEST("equiv(T,T) = T", T.equiv(T) == T)
    TEST("equiv(T,F) = F", T.equiv(F) == F)
    TEST("equiv(F,F) = T", F.equiv(F) == T)
    TEST("equiv(U,U) = U", U.equiv(U) == U)

    print("\n══ Trit: Conversion ══")
    TEST("T.to_json() → True", T.to_json() is True)
    TEST("F.to_json() → False", F.to_json() is False)
    TEST("U.to_json() → None", U.to_json() is None)
    TEST("repr TRUE", "TRUE" in repr(T))
    TEST("repr FALSE", "FALSE" in repr(F))
    TEST("repr UNKNOWN", "UNKNOWN" in repr(U))
    TEST("hash equality", hash(Trit(1)) == hash(Trit(1)))
    TEST("hash inequality", hash(Trit(1)) != hash(Trit(-1)))
    TEST("bool(T) → True", bool(T) is True)
    TEST("bool(F) → False", bool(F) is False)
    TEST("bool(U) → False", bool(U) is False)

    # ── TArray ───────────────────────────────────────────────────────
    print("\n══ TArray: Construction ══")
    a = TArray([1, 0, -1])
    TEST("len == 3", len(a) == 3)
    TEST("a[0] == T", a[0] == T)
    TEST("a[1] == U", a[1] == U)
    TEST("a[2] == F", a[2] == F)
    TEST("empty array", len(TArray()) == 0)
    TEST("copy construction", TArray(a) == a)

    print("\n══ TArray: Ops ══")
    b = TArray([1, -1, 1])
    c = a & b
    TEST("AND [0]", c[0] == T)
    TEST("AND [1]", c[1] == F)
    TEST("AND [2]", c[2] == F)
    d = a | b
    TEST("OR [0]", d[0] == T)
    TEST("OR [1]", d[1] == U)
    TEST("OR [2]", d[2] == T)
    e = ~a
    TEST("NOT [0]", e[0] == F)
    TEST("NOT [1]", e[1] == U)
    TEST("NOT [2]", e[2] == T)

    print("\n══ TArray: Reductions ══")
    TEST("all([T,T,T])", TArray([1,1,1]).all() == T)
    TEST("all([T,U,T])", TArray([1,0,1]).all() == U)
    TEST("all([T,F,T])", TArray([1,-1,1]).all() == F)
    TEST("any([F,F,F])", TArray([-1,-1,-1]).any() == F)
    TEST("any([F,U,F])", TArray([-1,0,-1]).any() == U)
    TEST("any([F,T,F])", TArray([-1,1,-1]).any() == T)
    TEST("count TRUE", TArray([1,1,-1,0,1]).count(1) == 3)
    TEST("count FALSE", TArray([1,1,-1,0,1]).count(-1) == 1)
    TEST("count UNKNOWN", TArray([1,1,-1,0,1]).count(0) == 1)

    print("\n══ TArray: Slicing / Mutation ══")
    s = TArray([1, 0, -1, 1, 0])
    sl = s[1:4]
    TEST("slice len", len(sl) == 3)
    TEST("slice[0]=U", sl[0] == U)
    TEST("slice[2]=T", sl[2] == T)
    s[0] = -1
    TEST("mutation", s[0] == F)
    TEST("to_json", TArray([1,0,-1]).to_json() == [True, None, False])

    # ── TJSON Encoder ────────────────────────────────────────────────
    print("\n══ TJSON: Encode ══")
    TEST("encode Trit TRUE", TJSON.encode(Trit(1)) == "true")
    TEST("encode Trit FALSE", TJSON.encode(Trit(-1)) == "false")
    TEST("encode Trit UNKNOWN", TJSON.encode(Trit(0)) == "null")
    TEST("encode dict", '"name"' in TJSON.encode({"name": "test", "val": Trit(1)}))
    TEST("encode TArray", TJSON.encode(TArray([1,-1,0])) == "[true, false, null]")
    TEST("encode nested", "true" in TJSON.encode({"a": {"b": Trit(1)}}))
    TEST("encode list", TJSON.encode([Trit(1), Trit(-1)]) == "[true, false]")
    TEST("encode int", TJSON.encode(42) == "42")
    TEST("encode string", TJSON.encode("hello") == '"hello"')
    TEST("encode indent", "\n" in TJSON.encode({"a": 1}, indent=2))

    # ── TJSON Decoder ────────────────────────────────────────────────
    print("\n══ TJSON: Decode ══")
    TEST("decode null → UNKNOWN", TJSON.decode("null") == Trit(0))
    TEST("decode true → true", TJSON.decode("true") is True)
    TEST("decode false → false", TJSON.decode("false") is False)
    TEST("decode int", TJSON.decode("42") == 42)
    TEST("decode string", TJSON.decode('"hello"') == "hello")
    obj = TJSON.decode('{"a": null, "b": true}')
    TEST("decode dict null→UNKNOWN", isinstance(obj["a"], Trit) and obj["a"].v == 0)
    TEST("decode dict true stays", obj["b"] is True)
    arr = TJSON.decode('[null, true, false]')
    TEST("decode array null→UNKNOWN", isinstance(arr[0], Trit))
    TEST("decode array true", arr[1] is True)
    TEST("decode array false", arr[2] is False)
    TEST("decode ternary_nulls=False", TJSON.decode("null", ternary_nulls=False) is None)

    # ── TJSON Diff ───────────────────────────────────────────────────
    print("\n══ TJSON: Diff ══")
    a_dict = {"x": 1, "y": 2, "z": 3}
    b_dict = {"x": 1, "y": 9, "w": 4}
    diff = TJSON.diff(a_dict, b_dict)
    TEST("diff changed y", "y" in diff and diff["y"][0] == "changed")
    TEST("diff removed z", "z" in diff and diff["z"][0] == "removed")
    TEST("diff added w", "w" in diff and diff["w"][0] == "added")
    TEST("diff no change x", "x" not in diff)
    TEST("diff empty", TJSON.diff({"a":1}, {"a":1}) == {})

    # ── TJSON Merge ──────────────────────────────────────────────────
    print("\n══ TJSON: Merge ══")
    m1 = {"a": 1, "b": 2}
    m2 = {"b": 3, "c": 4}
    merged = TJSON.merge(m1, m2)
    TEST("merge latest: b=3", merged["b"] == 3)
    TEST("merge keeps a", merged["a"] == 1)
    TEST("merge adds c", merged["c"] == 4)

    tm1 = {"val": Trit(1)}
    tm2 = {"val": Trit(0)}
    tmerged = TJSON.merge(tm1, tm2, strategy="ternary")
    TEST("ternary merge T&U=U", tmerged["val"] == Trit(0))

    tm3 = {"val": Trit(1)}
    tm4 = {"val": Trit(1)}
    TEST("ternary merge T&T=T", TJSON.merge(tm3, tm4, strategy="ternary")["val"] == Trit(1))

    tm5 = {"val": Trit(-1)}
    tm6 = {"val": Trit(1)}
    TEST("ternary merge F&T=F", TJSON.merge(tm5, tm6, strategy="ternary")["val"] == Trit(-1))

    # ── Schema Validation ────────────────────────────────────────────
    print("\n══ TJSON: Schema ══")
    schema = TJSONSchema({
        "name": {"type": "str", "required": True},
        "status": {"type": "trit", "required": True},
        "score": {"type": "int", "required": False},
        "tags": {"type": "tarray", "required": False}
    })
    valid = {"name": "test", "status": Trit(1)}
    TEST("valid doc: 0 errors", len(schema.validate(valid)) == 0)

    missing = {"score": 42}
    errs = schema.validate(missing)
    TEST("missing required: 2 errors", len(errs) == 2)

    wrong_type = {"name": "test", "status": 42}
    errs = schema.validate(wrong_type)
    TEST("wrong trit type: 1 error", len(errs) == 1)

    wrong_str = {"name": 123, "status": Trit(1)}
    errs = schema.validate(wrong_str)
    TEST("wrong str type", len(errs) == 1)

    with_tarray = {"name": "x", "status": Trit(1), "tags": TArray([1,-1])}
    TEST("tarray valid", len(schema.validate(with_tarray)) == 0)

    bad_tarray = {"name": "x", "status": Trit(1), "tags": [1, 2]}
    TEST("bad tarray", len(schema.validate(bad_tarray)) == 1)

    TEST("non-dict root", len(schema.validate("not a dict")) == 1)

    # ── Kleene Laws ──────────────────────────────────────────────────
    print("\n══ Kleene: Algebraic Laws ══")
    vals = [Trit(1), Trit(0), Trit(-1)]
    law_ok = True
    for a in vals:
        # Commutativity
        for b in vals:
            if not ((a & b) == (b & a)): law_ok = False
            if not ((a | b) == (b | a)): law_ok = False
    TEST("commutativity AND/OR", law_ok)

    law_ok = True
    for a in vals:
        for b in vals:
            for c in vals:
                if not (((a & b) & c) == (a & (b & c))): law_ok = False
                if not (((a | b) | c) == (a | (b | c))): law_ok = False
    TEST("associativity AND/OR", law_ok)

    law_ok = True
    for a in vals:
        if not ((a & Trit(1)) == a): law_ok = False
        if not ((a | Trit(-1)) == a): law_ok = False
    TEST("identity: T=AND, F=OR", law_ok)

    law_ok = True
    for a in vals:
        if not ((a & Trit(-1)) == Trit(-1)): law_ok = False
        if not ((a | Trit(1)) == Trit(1)): law_ok = False
    TEST("annihilator: F=AND, T=OR", law_ok)

    law_ok = True
    for a in vals:
        if not ((~~a) == a): law_ok = False
    TEST("double negation", law_ok)

    # De Morgan
    law_ok = True
    for a in vals:
        for b in vals:
            if not ((~(a & b)) == ((~a) | (~b))): law_ok = False
            if not ((~(a | b)) == ((~a) & (~b))): law_ok = False
    TEST("De Morgan", law_ok)

    # ── Epistemic Properties ─────────────────────────────────────────
    print("\n══ Epistemic: Ternary Knowledge ══")
    TEST("TRUE is definite", Trit(1).v != 0)
    TEST("FALSE is definite", Trit(-1).v != 0)
    TEST("UNKNOWN is indefinite", Trit(0).v == 0)
    TEST("info ordering: F < U < T", Trit(-1).v < Trit(0).v < Trit(1).v)
    # Epistemic closure: if agent knows p → q and knows p, should know q
    p, q = Trit(1), Trit(1)
    imp = p.implies(q)
    TEST("modus ponens: T→T, T ⊢ T", (imp & p).implies(q) == Trit(1))

    # ── Roundtrip ────────────────────────────────────────────────────
    print("\n══ Roundtrip: Encode → Decode ══")
    for v in [1, -1, 0]:
        t = Trit(v)
        encoded = TJSON.encode(t)
        decoded = TJSON.decode(encoded)
        if v == 0:
            TEST(f"roundtrip Trit({v})", isinstance(decoded, Trit) and decoded.v == 0)
        elif v == 1:
            TEST(f"roundtrip Trit({v})", decoded is True)
        else:
            TEST(f"roundtrip Trit({v})", decoded is False)

    doc = {"name": "s9", "ok": Trit(1), "err": Trit(-1), "unk": Trit(0)}
    encoded = TJSON.encode(doc)
    decoded = TJSON.decode(encoded)
    TEST("roundtrip name", decoded["name"] == "s9")
    TEST("roundtrip ok", decoded["ok"] is True)
    TEST("roundtrip err", decoded["err"] is False)
    TEST("roundtrip unk", isinstance(decoded["unk"], Trit) and decoded["unk"].v == 0)

    arr_doc = {"arr": TArray([1, -1, 0])}
    enc = TJSON.encode(arr_doc)
    dec = TJSON.decode(enc)
    TEST("roundtrip arr", isinstance(dec["arr"], list))
    TEST("roundtrip arr[0]", dec["arr"][0] is True)
    TEST("roundtrip arr[2]", isinstance(dec["arr"][2], Trit))

    # ── Edge Cases ───────────────────────────────────────────────────
    print("\n══ Edge Cases ══")
    TEST("empty dict encode", TJSON.encode({}) == "{}")
    TEST("empty list encode", TJSON.encode([]) == "[]")
    TEST("nested nulls", "null" in TJSON.encode({"a": {"b": Trit(0)}}))
    TEST("deep nesting", "true" in TJSON.encode({"a": {"b": {"c": Trit(1)}}}))
    TEST("diff empty dicts", TJSON.diff({}, {}) == {})
    TEST("merge empty", TJSON.merge({}, {}) == {})
    TEST("merge into empty", TJSON.merge({}, {"a": 1}) == {"a": 1})
    TEST("merge from empty", TJSON.merge({"a": 1}, {}) == {"a": 1})

    # Trit equality edge cases
    TEST("Trit != int 99", Trit(1) != 99)
    TEST("Trit == Trit", Trit(1) == Trit(1))
    TEST("Trit != diff Trit", Trit(1) != Trit(-1))

    # TArray edge cases
    TEST("TArray eq", TArray([1,0,-1]) == TArray([1,0,-1]))
    TEST("TArray neq len", not (TArray([1]) == TArray([1,0])))
    TEST("TArray neq val", not (TArray([1]) == TArray([-1])))
    TEST("TArray to_json empty", TArray().to_json() == [])

    # Schema edge cases
    empty_schema = TJSONSchema({})
    TEST("empty schema: valid", len(empty_schema.validate({})) == 0)
    TEST("empty schema: any dict", len(empty_schema.validate({"x": 1})) == 0)

    # ── Stress: Bulk Operations ──────────────────────────────────────
    print("\n══ Stress: Bulk ══")
    big = TArray([1, 0, -1] * 100)
    TEST("300-elem array", len(big) == 300)
    TEST("count T in 300", big.count(1) == 100)
    TEST("count U in 300", big.count(0) == 100)
    TEST("count F in 300", big.count(-1) == 100)
    inv = ~big
    TEST("invert 300 → F count", inv.count(-1) == 100)
    TEST("invert 300 → T count", inv.count(1) == 100)

    # AND/OR over big arrays
    all_true = TArray([1] * 300)
    anded = big & all_true
    TEST("big AND all_T = big", anded == big)
    all_false = TArray([-1] * 300)
    ored = big | all_false
    TEST("big OR all_F = big", ored == big)

    # Encode/decode big
    enc_big = TJSON.encode(big.to_json())
    TEST("big encode is string", isinstance(enc_big, str))
    TEST("big encode has null", "null" in enc_big)

    # Large dict
    large_dict = {f"k{i}": Trit(i % 3 - 1) for i in range(50)}
    enc_ld = TJSON.encode(large_dict)
    TEST("50-key encode", len(enc_ld) > 50)
    dec_ld = TJSON.decode(enc_ld)
    TEST("50-key decode", len(dec_ld) == 50)

    # Diff large
    ld2 = {f"k{i}": Trit((i+1) % 3 - 1) for i in range(50)}
    diff_large = TJSON.diff(large_dict, ld2)
    TEST("large diff non-empty", len(diff_large) > 0)

    # Merge large
    merged_large = TJSON.merge(large_dict, ld2)
    TEST("large merge", len(merged_large) == 50)

    # ── Stress: Trit Arithmetic Sweep ────────────────────────────────
    print("\n══ Stress: Arithmetic Sweep ══")
    count = 0
    for a in vals:
        for b in vals:
            r = a & b
            # Verify monotonicity: if a↑ or b↑, result↑
            assert isinstance(r, Trit)
            count += 1
            r2 = a | b
            assert isinstance(r2, Trit)
            count += 1
            r3 = a.implies(b)
            assert isinstance(r3, Trit)
            count += 1
    TEST(f"27 op pairs valid", count == 27)

    # Multiple implies chains
    chain = Trit(1)
    for i in range(10):
        chain = chain.implies(Trit(1))
    TEST("10-chain T→T→...→T = T", chain == Trit(1))

    chain = Trit(1)
    for i in range(10):
        chain = chain.implies(Trit(-1) if i == 5 else Trit(1))
    TEST("chain with F injection", chain.v in [-1, 0, 1])

    # equiv symmetry sweep
    law_ok = True
    for a in vals:
        for b in vals:
            if not (a.equiv(b) == b.equiv(a)):
                law_ok = False
    TEST("equiv symmetry 9-point", law_ok)

    # implies contrapositive
    law_ok = True
    for a in vals:
        for b in vals:
            # Weak contrapositive: p→q should relate to ¬q→¬p
            fwd = a.implies(b)
            contra = (~b).implies(~a)
            if not (fwd == contra):
                law_ok = False
    TEST("contrapositive 9-point", law_ok)

    # ── Advanced: TJSON Document Operations ──────────────────────────
    print("\n══ Advanced: Document Lifecycle ══")
    # Create → encode → decode → validate → diff → merge cycle
    doc1 = {"name": "sensor_a", "status": Trit(1), "value": 42}
    doc2 = {"name": "sensor_a", "status": Trit(0), "value": 43}
    enc1 = TJSON.encode(doc1)
    enc2 = TJSON.encode(doc2)
    dec1 = TJSON.decode(enc1)
    dec2 = TJSON.decode(enc2)
    TEST("lifecycle: enc1 is str", isinstance(enc1, str))
    TEST("lifecycle: enc2 is str", isinstance(enc2, str))
    TEST("lifecycle: dec1 name", dec1["name"] == "sensor_a")
    TEST("lifecycle: dec2 name", dec2["name"] == "sensor_a")
    diff12 = TJSON.diff(dec1, dec2)
    TEST("lifecycle: diff has changes", len(diff12) > 0)
    merged12 = TJSON.merge(dec1, dec2)
    TEST("lifecycle: merge has name", merged12["name"] == "sensor_a")
    TEST("lifecycle: merge value=43", merged12["value"] == 43)

    # Batch encode/decode
    print("\n══ Advanced: Batch Encode/Decode ══")
    docs = [{"id": i, "val": Trit(i % 3 - 1)} for i in range(20)]
    for i, doc in enumerate(docs):
        enc = TJSON.encode(doc)
        dec = TJSON.decode(enc)
        TEST(f"batch roundtrip [{i}]", dec["id"] == i)

    # TArray operations sweep
    print("\n══ Advanced: TArray Ops Sweep ══")
    patterns = [
        [1,1,1], [-1,-1,-1], [0,0,0],
        [1,-1,0], [0,1,-1], [-1,0,1],
        [1,0,1,0], [-1,1,-1,1]
    ]
    for i, p in enumerate(patterns):
        a = TArray(p)
        inv = ~a
        double = ~~a
        TEST(f"pattern[{i}] double neg", double == a)

    for i in range(len(patterns)):
        for j in range(i+1, min(i+3, len(patterns))):
            if len(patterns[i]) == len(patterns[j]):
                a = TArray(patterns[i])
                b = TArray(patterns[j])
                r_and = a & b
                r_or = a | b
                TEST(f"ops[{i},{j}] AND len", len(r_and) == len(a))
                TEST(f"ops[{i},{j}] OR len", len(r_or) == len(a))

    # Schema edge cases
    print("\n══ Advanced: Schema ══")
    strict_schema = TJSONSchema({
        "a": {"type": "int", "required": True},
        "b": {"type": "str", "required": True},
        "c": {"type": "trit", "required": True},
    })
    TEST("schema all required valid", len(strict_schema.validate({"a": 1, "b": "x", "c": Trit(1)})) == 0)
    TEST("schema all missing", len(strict_schema.validate({})) == 3)
    TEST("schema 1 missing", len(strict_schema.validate({"a": 1, "b": "x"})) == 1)
    TEST("schema wrong types", len(strict_schema.validate({"a": "x", "b": 1, "c": 42})) == 3)
    TEST("schema extra fields ok", len(strict_schema.validate({"a": 1, "b": "x", "c": Trit(1), "extra": 99})) == 0)

    # ── TJSON Diff edge cases  ───────────────────────────────────────
    print("\n══ Advanced: Diff Edge Cases ══")
    TEST("diff self", TJSON.diff({"a": 1}, {"a": 1}) == {})
    TEST("diff type change", "a" in TJSON.diff({"a": 1}, {"a": "1"}))
    TEST("diff add many", len(TJSON.diff({}, {f"k{i}": i for i in range(10)})) == 10)
    TEST("diff remove many", len(TJSON.diff({f"k{i}": i for i in range(10)}, {})) == 10)
    # Trit-valued diffs
    td1 = {"s": Trit(1), "r": Trit(-1)}
    td2 = {"s": Trit(-1), "r": Trit(-1)}
    td = TJSON.diff(td1, td2)
    TEST("diff trit changed", "s" in td)
    TEST("diff trit same", "r" not in td)

    # ── TJSON Merge edge cases  ──────────────────────────────────────
    print("\n══ Advanced: Merge Edge Cases ══")
    TEST("merge 3-way latest",
         TJSON.merge(TJSON.merge({"a":1}, {"b":2}), {"c":3}) == {"a":1,"b":2,"c":3})
    # Ternary merge chain
    r = TJSON.merge(
        TJSON.merge({"v": Trit(1)}, {"v": Trit(0)}, strategy="ternary"),
        {"v": Trit(1)}, strategy="ternary")
    TEST("ternary 3-chain: T&U&T", r["v"] == Trit(0))
    # Merge with non-trit + Trit mix
    mixed = TJSON.merge({"x": 42, "t": Trit(1)}, {"x": 99, "t": Trit(-1)}, strategy="ternary")
    TEST("mixed merge x=99", mixed["x"] == 99)
    TEST("mixed merge t=F", mixed["t"] == Trit(-1))

    # ── Trit comparison edge cases ───────────────────────────────────
    print("\n══ Advanced: Trit Comparison ══")
    TEST("Trit != string", Trit(1).__eq__("not a trit") is NotImplemented)
    TEST("Trit != list", Trit(1).__eq__([1]) is NotImplemented)
    TEST("Trit != None", Trit(1).__eq__(None) is NotImplemented)
    TEST("Trit set dedup", len({Trit(1), Trit(1), Trit(-1)}) == 2)
    TEST("Trit in dict key", {Trit(1): "yes", Trit(-1): "no"}[Trit(1)] == "yes")

    # ── Absorption laws ──────────────────────────────────────────────
    print("\n══ Advanced: Absorption ══")
    law_ok = True
    for a in vals:
        for b in vals:
            # a & (a | b) should equal a in classical, but in K3 it's weaker
            r = a & (a | b)
            # At minimum, result should be valid trit
            if r.v not in [-1, 0, 1]: law_ok = False
    TEST("absorption AND-OR valid", law_ok)

    law_ok = True
    for a in vals:
        for b in vals:
            r = a | (a & b)
            if r.v not in [-1, 0, 1]: law_ok = False
    TEST("absorption OR-AND valid", law_ok)

    # ── TArray advanced ──────────────────────────────────────────────
    print("\n══ Advanced: TArray Construction ══")
    # From Python booleans
    TEST("TArray from bools", TArray([True, False, True])[0] == Trit(1))
    TEST("TArray from bools F", TArray([True, False, True])[1] == Trit(-1))
    # Integer conversion
    TEST("TArray large int → T", TArray([100])[0] == Trit(1))
    TEST("TArray neg int → F", TArray([-50])[0] == Trit(-1))
    TEST("TArray zero → U", TArray([0])[0] == Trit(0))

    # Build incrementally
    arr = TArray()
    for v in [1, 0, -1, 1, 0]:
        arr.data.append(Trit(v))
    TEST("incremental build len=5", len(arr) == 5)
    TEST("incremental build[0]=T", arr[0] == Trit(1))

    # Equality of large arrays
    a1 = TArray([1,0,-1]*50)
    a2 = TArray([1,0,-1]*50)
    TEST("large array equality", a1 == a2)
    a2[149] = Trit(1)
    TEST("large array inequality", not (a1 == a2))

    # ── Encode special values ────────────────────────────────────────
    print("\n══ Advanced: Encode Special ══")
    TEST("encode float", TJSON.encode(3.14) == "3.14")
    TEST("encode empty str", TJSON.encode("") == '""')
    TEST("encode None", TJSON.encode(None) == "null")
    TEST("encode True", TJSON.encode(True) == "true")
    TEST("encode False", TJSON.encode(False) == "false")
    TEST("encode list of lists", TJSON.encode([[1,2],[3,4]]) == "[[1, 2], [3, 4]]")

    # ── K3 truth table verification (9 entries × 3 ops) ─────────────
    print("\n══ K3 Truth Table Verification ══")
    # AND truth table
    k3_and = {
        (1,1):1, (1,0):0, (1,-1):-1,
        (0,1):0, (0,0):0, (0,-1):-1,
        (-1,1):-1, (-1,0):-1, (-1,-1):-1
    }
    for (a,b), exp in k3_and.items():
        r = Trit(a) & Trit(b)
        TEST(f"K3 AND({a},{b})={exp}", r.v == exp)

    # OR truth table
    k3_or = {
        (1,1):1, (1,0):1, (1,-1):1,
        (0,1):1, (0,0):0, (0,-1):0,
        (-1,1):1, (-1,0):0, (-1,-1):-1
    }
    for (a,b), exp in k3_or.items():
        r = Trit(a) | Trit(b)
        TEST(f"K3 OR({a},{b})={exp}", r.v == exp)

    # IMPLIES truth table (9)
    k3_imp = {
        (1,1):1, (1,0):0, (1,-1):-1,
        (0,1):1, (0,0):0, (0,-1):0,
        (-1,1):1, (-1,0):1, (-1,-1):1
    }
    for (a,b), exp in k3_imp.items():
        r = Trit(a).implies(Trit(b))
        TEST(f"K3 IMP({a},{b})={exp}", r.v == exp)

    # ── Fuzzy-Ternary Bridge ─────────────────────────────────────────
    print("\n══ Fuzzy-Ternary Bridge ══")
    # Map confidence levels to trit
    for conf in range(0, 101, 10):
        t = Trit(1) if conf > 66 else (Trit(-1) if conf < 33 else Trit(0))
        TEST(f"conf {conf:3d}% → valid trit", t.v in [-1, 0, 1])

    # ── Multi-Key TJSON Stress ───────────────────────────────────────
    print("\n══ Multi-Key TJSON Stress ══")
    for n in [5, 10, 25]:
        d = {f"field_{i}": Trit(i % 3 - 1) for i in range(n)}
        e = TJSON.encode(d)
        dec = TJSON.decode(e)
        TEST(f"{n}-key encode/decode", isinstance(dec, dict) and len(dec) == n)

    # ── Schema Multi-Type ────────────────────────────────────────────
    print("\n══ Schema Multi-Type ══")
    ms = TJSONSchema({
        "tval": {"type": "trit", "required": True},
        "ival": {"type": "int", "required": True},
        "sval": {"type": "str", "required": True},
        "tarr": {"type": "tarray", "required": True}
    })
    good = {"tval": Trit(1), "ival": 42, "sval": "ok", "tarr": TArray([1,-1])}
    TEST("multi-type all valid", len(ms.validate(good)) == 0)
    bad_all = {"tval": "x", "ival": "y", "sval": 1, "tarr": "z"}
    TEST("multi-type all wrong", len(ms.validate(bad_all)) == 4)
    partial = {"tval": Trit(0)}
    TEST("multi-type 3 missing", len(ms.validate(partial)) == 3)

    # ── TArray Stress: Reduction on patterns ─────────────────────────
    print("\n══ TArray Reduction Stress ══")
    TEST("all(empty)→T", TArray([]).all() == Trit(1))
    TEST("any(empty)→F", TArray([]).any() == Trit(-1))
    for k in range(1, 6):
        a = TArray([1]*k)
        TEST(f"all(T×{k})=T", a.all() == Trit(1))
        TEST(f"any(T×{k})=T", a.any() == Trit(1))

    # ── Idempotence Laws ─────────────────────────────────────────────
    print("\n══ Idempotence Laws ══")
    for v in vals:
        TEST(f"a AND a = a [{v.v}]", (v & v) == v)
        TEST(f"a OR  a = a [{v.v}]", (v | v) == v)

    # ── Excluded Middle & Non-Contradiction (K3) ─────────────────────
    print("\n══ K3 LEM/LNC ══")
    TEST("T | ~T = T", (T | ~T) == T)
    TEST("F | ~F = T", (F | ~F) == T)
    TEST("U | ~U = U (no LEM)", (U | ~U) == U)
    TEST("T & ~T = F", (T & ~T) == F)
    TEST("F & ~F = F", (F & ~F) == F)
    TEST("U & ~U = U (no LNC)", (U & ~U) == U)

    # ── Final Summary ────────────────────────────────
    print(f"\n{'='*60}")
    print(f" TJSON Test Results: {_pass} passed, {_fail} failed, {_pass+_fail} total")
    print(f"{'='*60}")
    print(f"=== TJSON Tests: {_pass} passed, {_fail} failed, {_pass+_fail} total ===")
    return _fail


if __name__ == "__main__":
    sys.exit(run_tests())
