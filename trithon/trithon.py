# Trithon — Python CFFI Bindings for seT5 Balanced Ternary
# SPDX-License-Identifier: GPL-2.0

"""
Trithon: Python interface to seT5 balanced ternary operations.

Provides:
  - Trit scalar type with Kleene K₃ logic
  - TritArray: NumPy-compatible ternary arrays
  - DOT_TRIT, FFT_STEP, RADIX_CONV operations
  - QEMU noise simulation for hardware testing
  - Optional C extension (libtrithon.so) for native performance

Usage:
    from trithon import Trit, TritArray

    a = Trit.TRUE
    b = Trit.UNKNOWN
    print(a & b)         # Kleene AND → Unknown
    print(a | b)         # Kleene OR  → True
    print(~a)            # Kleene NOT → False

    arr = TritArray([1, 0, -1, 1, 0])
    print(arr.dot(arr))  # DOT product
"""

from __future__ import annotations
from enum import IntEnum
from typing import List, Optional, Sequence, Union
import array
import ctypes
import os
import struct


# ---- C Extension (optional, built from trithon_ext.c) ------------------

_lib = None
_LIB_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'libtrithon.so')

def _load_native():
    """Try to load libtrithon.so for native trit ops."""
    global _lib
    if _lib is not None:
        return _lib
    try:
        lib = ctypes.CDLL(_LIB_PATH)
        # Scalar ops
        for fn in ('trithon_and', 'trithon_or', 'trithon_not',
                    'trithon_implies', 'trithon_equiv',
                    'trithon_inc', 'trithon_dec',
                    'trithon_consensus', 'trithon_accept_any',
                    'trithon_mul', 'trithon_div', 'trithon_pow'):
            getattr(lib, fn).argtypes = [ctypes.c_int8] * (2 if fn != 'trithon_not' and fn != 'trithon_inc' and fn != 'trithon_dec' else 1)
            getattr(lib, fn).restype = ctypes.c_int8
        # Array ops
        lib.trithon_dot.argtypes = [ctypes.POINTER(ctypes.c_int8),
                                     ctypes.POINTER(ctypes.c_int8),
                                     ctypes.c_int]
        lib.trithon_dot.restype = ctypes.c_int
        lib.trithon_dot_sparse.argtypes = [ctypes.POINTER(ctypes.c_int8),
                                            ctypes.POINTER(ctypes.c_int8),
                                            ctypes.c_int, ctypes.c_int, ctypes.c_int]
        lib.trithon_dot_sparse.restype = ctypes.c_int
        lib.trithon_mr_dot.argtypes = [ctypes.POINTER(ctypes.c_int8),
                                        ctypes.POINTER(ctypes.c_int8),
                                        ctypes.c_int]
        lib.trithon_mr_dot.restype = ctypes.c_int
        lib.trithon_version.argtypes = []
        lib.trithon_version.restype = ctypes.c_int
        _lib = lib
        return lib
    except OSError:
        return None

# Attempt load at import time (graceful fallback)
_load_native()

def native_available() -> bool:
    """Check if the C extension is loaded."""
    return _lib is not None


class Trit(IntEnum):
    """Balanced ternary trit: {-1, 0, +1} with Kleene K₃ semantics."""
    FALSE   = -1
    UNKNOWN =  0
    TRUE    =  1

    # Kleene AND = min
    def __and__(self, other: 'Trit') -> 'Trit':
        if _lib:
            return Trit(_lib.trithon_and(self.value, Trit(other).value))
        return Trit(min(self.value, Trit(other).value))

    # Kleene OR = max
    def __or__(self, other: 'Trit') -> 'Trit':
        if _lib:
            return Trit(_lib.trithon_or(self.value, Trit(other).value))
        return Trit(max(self.value, Trit(other).value))

    # Kleene NOT = negation
    def __invert__(self) -> 'Trit':
        if _lib:
            return Trit(_lib.trithon_not(self.value))
        return Trit(-self.value)

    # Cyclic increment F→U→T→F
    def inc(self) -> 'Trit':
        if _lib:
            return Trit(_lib.trithon_inc(self.value))
        return Trit((self.value + 2) % 3 - 1)

    # Cyclic decrement T→U→F→T
    def dec(self) -> 'Trit':
        if _lib:
            return Trit(_lib.trithon_dec(self.value))
        return Trit(self.value % 3 - 1)

    # Consensus = Kleene AND (named alias for clarity)
    def consensus(self, other: 'Trit') -> 'Trit':
        if _lib:
            return Trit(_lib.trithon_consensus(self.value, Trit(other).value))
        return self & other

    # Accept-any = Kleene OR (named alias for clarity)
    def accept_any(self, other: 'Trit') -> 'Trit':
        if _lib:
            return Trit(_lib.trithon_accept_any(self.value, Trit(other).value))
        return self | other

    # Balanced ternary multiplication
    def __mul__(self, other: 'Trit') -> 'Trit':
        if _lib:
            return Trit(_lib.trithon_mul(self.value, Trit(other).value))
        return Trit(self.value * Trit(other).value)

    # Balanced ternary division: a / b = a * b for non-zero b
    def __truediv__(self, other: 'Trit') -> 'Trit':
        o = Trit(other)
        if _lib:
            return Trit(_lib.trithon_div(self.value, o.value))
        if o.value == 0:
            return Trit(0)  # div by Unknown → Unknown
        return Trit(self.value * o.value)

    # Balanced ternary exponentiation
    def __pow__(self, other: 'Trit') -> 'Trit':
        o = Trit(other)
        if _lib:
            return Trit(_lib.trithon_pow(self.value, o.value))
        if o.value == 0:
            return Trit(1)   # anything^0 = T
        if self.value == 0:
            return Trit(0)   # U^anything = U
        if self.value == 1:
            return Trit(1)   # T^anything = T
        # self.value == -1
        return Trit(-1)      # F^{T or F} = F

    def __repr__(self) -> str:
        names = {-1: 'F', 0: 'U', 1: 'T'}
        return f"Trit.{names[self.value]}"


class TritArray:
    """
    Array of balanced ternary trits with NumPy-like operations.

    Internally stored as a Python array of signed bytes.
    Each element is one of {-1, 0, +1}.

    Compatible with NumPy via __array_interface__ when numpy is available.
    """

    __slots__ = ('_data',)

    def __init__(self, data: Union[Sequence[int], 'TritArray', None] = None,
                 size: int = 0):
        if data is not None:
            if isinstance(data, TritArray):
                self._data = array.array('b', data._data)
            else:
                validated = []
                for v in data:
                    if v not in (-1, 0, 1):
                        raise ValueError(f"Invalid trit value: {v}")
                    validated.append(v)
                self._data = array.array('b', validated)
        else:
            self._data = array.array('b', [0] * size)

    @classmethod
    def splat(cls, value: int, size: int) -> 'TritArray':
        """Create array filled with a single trit value."""
        if value not in (-1, 0, 1):
            raise ValueError(f"Invalid trit value: {value}")
        return cls([value] * size)

    @classmethod
    def from_int(cls, value: int, width: int = 12) -> 'TritArray':
        """Convert integer to balanced ternary (Avizienis algorithm)."""
        trits = []
        v = value
        for _ in range(width):
            r = v % 3
            if r == 2:
                r = -1
                v = (v + 1) // 3
            else:
                v = v // 3
            trits.append(r)
        return cls(trits)

    def to_int(self) -> int:
        """Convert balanced ternary array back to integer."""
        result = 0
        for i in range(len(self._data) - 1, -1, -1):
            result = result * 3 + self._data[i]
        return result

    # ---- Properties ----

    def __len__(self) -> int:
        return len(self._data)

    def __getitem__(self, idx: int) -> Trit:
        return Trit(self._data[idx])

    def __setitem__(self, idx: int, value: int) -> None:
        if value not in (-1, 0, 1):
            raise ValueError(f"Invalid trit value: {value}")
        self._data[idx] = value

    def __repr__(self) -> str:
        chars = {-1: 'F', 0: 'U', 1: 'T'}
        s = ''.join(chars[t] for t in self._data)
        return f"TritArray([{s}])"

    def __eq__(self, other: object) -> bool:
        if isinstance(other, TritArray):
            return self._data == other._data
        return NotImplemented

    # ---- Kleene K₃ Operations (element-wise) ----

    def kleene_and(self, other: 'TritArray') -> 'TritArray':
        """Element-wise Kleene AND (min)."""
        if len(self) != len(other):
            raise ValueError("Array length mismatch")
        return TritArray([min(a, b) for a, b in zip(self._data, other._data)])

    def kleene_or(self, other: 'TritArray') -> 'TritArray':
        """Element-wise Kleene OR (max)."""
        if len(self) != len(other):
            raise ValueError("Array length mismatch")
        return TritArray([max(a, b) for a, b in zip(self._data, other._data)])

    def kleene_not(self) -> 'TritArray':
        """Element-wise Kleene NOT (negation)."""
        return TritArray([-t for t in self._data])

    # Operator overloads
    def __and__(self, other: 'TritArray') -> 'TritArray':
        return self.kleene_and(other)

    def __or__(self, other: 'TritArray') -> 'TritArray':
        return self.kleene_or(other)

    def __invert__(self) -> 'TritArray':
        return self.kleene_not()

    # ---- Multi-Radix Operations ----

    def dot(self, other: 'TritArray') -> int:
        """
        Balanced ternary dot product.
        DOT = Σ (a_i * b_i) where * is balanced ternary multiplication.
        Uses C extension (libtrithon.so) when available for native speed.
        """
        if len(self) != len(other):
            raise ValueError("Array length mismatch")
        if _lib:
            a_arr = (ctypes.c_int8 * len(self))(*self._data)
            b_arr = (ctypes.c_int8 * len(other))(*other._data)
            return _lib.trithon_dot(a_arr, b_arr, len(self))
        return sum(a * b for a, b in zip(self._data, other._data))

    def dot_sparse(self, other: 'TritArray', n: int = 4, m: int = 2) -> int:
        """
        N:M structured sparsity dot product.
        In each N-element block, at most M elements are non-zero.
        Uses C extension when available.
        """
        if len(self) != len(other):
            raise ValueError("Array length mismatch")
        if _lib:
            a_arr = (ctypes.c_int8 * len(self))(*self._data)
            b_arr = (ctypes.c_int8 * len(other))(*other._data)
            return _lib.trithon_dot_sparse(a_arr, b_arr, len(self), n, m)
        acc = 0
        for i in range(0, len(self._data), n):
            block = self._data[i:i+n]
            nonzero = sum(1 for t in block if t != 0)
            if nonzero <= m:
                # Sparse path: only multiply non-zero elements
                for j, t in enumerate(block):
                    if t != 0 and i + j < len(other._data):
                        acc += t * other._data[i + j]
            else:
                # Dense path
                for j, t in enumerate(block):
                    if i + j < len(other._data):
                        acc += t * other._data[i + j]
        return acc

    def fft_step(self, offset: int = 0) -> 'TritArray':
        """
        Radix-3 butterfly on 3 consecutive trits starting at offset.
        Y0 = X0 + X1 + X2  (mod 3, clamped to {-1,0,1})
        Y1 = X0 + ω·X1 + ω²·X2
        Y2 = X0 + ω²·X1 + ω·X2

        ω = cyclic rotation in {-1, 0, 1}
        """
        result = TritArray(self)
        if offset + 3 > len(self._data):
            return result

        x0, x1, x2 = self._data[offset], self._data[offset+1], self._data[offset+2]

        # Twiddle: ω = rotate (-1→0→1→-1)
        def rotate(v: int) -> int:
            return (v + 2) % 3 - 1

        def rotate2(v: int) -> int:
            return rotate(rotate(v))

        def clamp(v: int) -> int:
            return max(-1, min(1, v))

        y0 = clamp(x0 + x1 + x2)
        y1 = clamp(x0 + rotate(x1) + rotate2(x2))
        y2 = clamp(x0 + rotate2(x1) + rotate(x2))

        result._data[offset]     = y0
        result._data[offset + 1] = y1
        result._data[offset + 2] = y2
        return result

    # ---- Conversion ----

    def to_bytes(self) -> bytes:
        """Pack trits into 2-bit encoding: 00=F, 01=U, 11=T."""
        packed = 0
        for i, t in enumerate(self._data):
            enc = {-1: 0b00, 0: 0b01, 1: 0b11}[t]
            packed |= (enc << (2 * i))
        nbytes = (len(self._data) * 2 + 7) // 8
        return packed.to_bytes(nbytes, 'little')

    @classmethod
    def from_bytes(cls, data: bytes, count: int) -> 'TritArray':
        """Unpack 2-bit encoded trits."""
        packed = int.from_bytes(data, 'little')
        trits = []
        decode = {0b00: -1, 0b01: 0, 0b11: 1, 0b10: 0}  # 10 = fault → U
        for i in range(count):
            enc = (packed >> (2 * i)) & 0b11
            trits.append(decode[enc])
        return cls(trits)

    # ---- NumPy Integration ----

    @property
    def __array_interface__(self) -> dict:
        """NumPy array interface for zero-copy interop."""
        return {
            'shape': (len(self._data),),
            'typestr': '<i1',  # signed 8-bit
            'data': (self._data.buffer_info()[0], False),
            'version': 3,
        }

    def to_numpy(self):
        """Convert to NumPy array (requires numpy)."""
        import numpy as np
        return np.array(self._data, dtype=np.int8)

    @classmethod
    def from_numpy(cls, arr) -> 'TritArray':
        """Create TritArray from NumPy array."""
        return cls(arr.tolist())

    # ---- Statistics ----

    def sparsity(self) -> float:
        """Fraction of Unknown (zero) elements."""
        if len(self._data) == 0:
            return 0.0
        zeros = sum(1 for t in self._data if t == 0)
        return zeros / len(self._data)

    def census(self) -> dict:
        """Count of each trit value."""
        return {
            'F': sum(1 for t in self._data if t == -1),
            'U': sum(1 for t in self._data if t == 0),
            'T': sum(1 for t in self._data if t == 1),
        }


# ---- QEMU Noise Simulator (Pure Python) --------------------------------

class QEMUNoise:
    """
    Python-side QEMU ternary noise simulator.
    Mirrors include/set5/qemu_trit.h for testing without C compilation.
    """

    def __init__(self, model: str = 'none', seed: int = 42, prob_ppm: int = 1000):
        self.model = model
        self.seed = seed & 0xFFFFFFFF
        self.prob_ppm = prob_ppm
        self.total_reads = 0
        self.faults = 0

    def _xorshift32(self) -> int:
        x = self.seed
        x ^= (x << 13) & 0xFFFFFFFF
        x ^= (x >> 17)
        x ^= (x << 5) & 0xFFFFFFFF
        self.seed = x
        return x

    def read(self, value: int) -> int:
        """Apply noise to a single trit read."""
        self.total_reads += 1
        if self.model == 'none':
            return value

        r = self._xorshift32()
        if self.model == 'uniform':
            if (r % 1_000_000) < self.prob_ppm:
                self.faults += 1
                return 0  # Unknown
        elif self.model == 'cosmic':
            if (r % 1_000_000) < (self.prob_ppm // 10):
                self.faults += 1
                return 0
        return value

    def read_array(self, arr: TritArray) -> TritArray:
        """Apply noise to each element of a TritArray."""
        return TritArray([self.read(t) for t in arr._data])


# ---- Self-test ---------------------------------------------------------

def _self_test():
    """Quick self-test of Trithon module (pure Python + C extension)."""
    import sys

    T, U, F = Trit.TRUE, Trit.UNKNOWN, Trit.FALSE

    # Report C extension status
    if native_available():
        ver = _lib.trithon_version()
        print(f"Trithon: C extension loaded (libtrithon.so v{ver // 100}.{ver % 100:02d})")
    else:
        print("Trithon: pure Python mode (libtrithon.so not found)")

    # Kleene logic
    assert (T & T) == T
    assert (T & U) == U
    assert (T & F) == F
    assert (T | U) == T
    assert (U | F) == U
    assert (~T) == F
    assert (~U) == U
    assert (~F) == T

    # Multiplication
    assert (F * F) == T  # (-1)*(-1) = 1
    assert (F * T) == F  # (-1)*(1) = -1
    assert (U * T) == U  # 0*1 = 0

    # Inc / Dec (cyclic)
    assert T.inc() == F   # +1 wraps to -1
    assert F.inc() == U   # -1 → 0
    assert U.inc() == T   # 0 → +1
    assert T.dec() == U   # +1 → 0
    assert U.dec() == F   # 0 → -1
    assert F.dec() == T   # -1 wraps to +1

    # Consensus / Accept-any (named aliases)
    assert T.consensus(T) == T
    assert T.consensus(F) == F
    assert T.consensus(U) == U
    assert T.accept_any(F) == T
    assert F.accept_any(F) == F
    assert U.accept_any(F) == U

    # TritArray
    a = TritArray([1, 0, -1, 1, 0])
    b = TritArray([1, 1, 1, -1, 0])

    # Dot product
    dot = a.dot(b)
    assert dot == (1*1 + 0*1 + (-1)*1 + 1*(-1) + 0*0)  # 1+0-1-1+0 = -1

    # Sparse dot
    dot_s = a.dot_sparse(b, n=4, m=2)
    # Sparse skips zeros, same result for non-zero elements
    assert isinstance(dot_s, int)

    # Kleene ops
    c = a & b
    assert c[0] == Trit.TRUE   # min(1,1)
    assert c[1] == Trit.UNKNOWN  # min(0,1)

    d = a | b
    assert d[0] == Trit.TRUE
    assert d[2] == Trit.TRUE   # max(-1,1)

    # Integer conversion
    arr = TritArray.from_int(42)
    assert arr.to_int() == 42

    arr = TritArray.from_int(-13)
    assert arr.to_int() == -13

    # Packing
    packed = a.to_bytes()
    restored = TritArray.from_bytes(packed, len(a))
    assert restored == a

    # Sparsity
    sparse = TritArray.splat(0, 32)
    assert sparse.sparsity() == 1.0
    dense = TritArray.splat(1, 32)
    assert dense.sparsity() == 0.0

    # FFT
    fft_in = TritArray([1, -1, 0])
    fft_out = fft_in.fft_step(0)
    assert len(fft_out) == 3

    # QEMU noise
    noise = QEMUNoise('uniform', seed=42, prob_ppm=100000)
    flipped = 0
    for _ in range(1000):
        if noise.read(1) != 1:
            flipped += 1
    assert flipped > 0

    # Division
    assert Trit(1) / Trit(1) == Trit.TRUE      # T/T = T
    assert Trit(1) / Trit(-1) == Trit.FALSE    # T/F = F
    assert Trit(-1) / Trit(-1) == Trit.TRUE    # F/F = T
    assert Trit(0) / Trit(1) == Trit.UNKNOWN   # U/T = U
    assert Trit(1) / Trit(0) == Trit.UNKNOWN   # T/U = U (div by zero)

    # Exponentiation
    assert Trit(1) ** Trit(1) == Trit.TRUE     # T^T = T
    assert Trit(1) ** Trit(0) == Trit.TRUE     # T^U = T
    assert Trit(-1) ** Trit(1) == Trit.FALSE   # F^T = F
    assert Trit(-1) ** Trit(0) == Trit.TRUE    # F^U = T
    assert Trit(0) ** Trit(1) == Trit.UNKNOWN  # U^T = U
    assert Trit(0) ** Trit(0) == Trit.TRUE     # U^U = T (0^0=1)

    # C extension specific tests (only if loaded)
    if native_available():
        # Multi-radix DOT via seT5 engine
        a32 = TritArray.splat(1, 32)
        b32 = TritArray.splat(1, 32)
        a_arr = (ctypes.c_int8 * 32)(*a32._data)
        b_arr = (ctypes.c_int8 * 32)(*b32._data)
        mr_dot = _lib.trithon_mr_dot(a_arr, b_arr, 32)
        assert mr_dot == 32, f"MR dot(all T, all T) expected 32, got {mr_dot}"

        # IMPLIES, EQUIV
        assert _lib.trithon_implies(1, 1) == 1   # T→T = T
        assert _lib.trithon_implies(1, -1) == -1  # T→F = F
        assert _lib.trithon_implies(-1, 1) == 1   # F→T = T
        assert _lib.trithon_equiv(1, 1) == 1      # T≡T = T
        assert _lib.trithon_equiv(1, -1) == -1    # T≡F = F

        print("Trithon: C extension tests PASSED")

    print("Trithon: all self-tests PASSED")


if __name__ == '__main__':
    _self_test()
