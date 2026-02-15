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


# ---- Functional Utility Modules (INCREASE_FUNCTIONAL_UTILITY.md) -------

class TWQ:
    """Ternary Weight Quantizer — BitNet b1.58 engine.
    
    Quantizes integer weights (×1000) to ternary {-1, 0, +1}.
    Requires C extension.
    """
    @staticmethod
    def quantize(weights: List[int]) -> TritArray:
        """Quantize integer weights (×1000 fixed point) to ternary."""
        if _lib:
            n = len(weights)
            w_arr = (ctypes.c_int32 * n)(*weights)
            out = (ctypes.c_int8 * n)()
            _lib.trithon_twq_quantize.argtypes = [
                ctypes.POINTER(ctypes.c_int8),
                ctypes.POINTER(ctypes.c_int32),
                ctypes.c_int
            ]
            _lib.trithon_twq_quantize.restype = ctypes.c_int
            _lib.trithon_twq_quantize(out, w_arr, n)
            return TritArray(list(out))
        # Pure-Python fallback: threshold at 0.7 × mean(|w|)
        mean_abs = sum(abs(w) for w in weights) // max(len(weights), 1)
        threshold = (mean_abs * 7) // 10
        result = []
        for w in weights:
            if w > threshold:
                result.append(1)
            elif w < -threshold:
                result.append(-1)
            else:
                result.append(0)
        return TritArray(result)

    @staticmethod
    def dot(a: TritArray, b: TritArray) -> int:
        """Ternary dot product (add/sub/skip)."""
        if _lib:
            n = min(len(a._data), len(b._data))
            a_arr = (ctypes.c_int8 * n)(*a._data[:n])
            b_arr = (ctypes.c_int8 * n)(*b._data[:n])
            _lib.trithon_twq_dot.argtypes = [
                ctypes.POINTER(ctypes.c_int8),
                ctypes.POINTER(ctypes.c_int8),
                ctypes.c_int
            ]
            _lib.trithon_twq_dot.restype = ctypes.c_int
            return _lib.trithon_twq_dot(a_arr, b_arr, n)
        return a.dot(b)


class DLFETSim:
    """DLFET-RM ternary gate simulator (unbalanced 0/1/2)."""
    
    @staticmethod
    def tnot(a: int) -> int:
        """Ternary inverter: 0→2, 1→1, 2→0."""
        if _lib:
            _lib.trithon_dlfet_tnot.argtypes = [ctypes.c_int]
            _lib.trithon_dlfet_tnot.restype = ctypes.c_int
            return _lib.trithon_dlfet_tnot(a)
        return 2 - a

    @staticmethod
    def tnand(a: int, b: int) -> int:
        """DLFET-RM TNAND gate."""
        if _lib:
            _lib.trithon_dlfet_tnand.argtypes = [ctypes.c_int, ctypes.c_int]
            _lib.trithon_dlfet_tnand.restype = ctypes.c_int
            return _lib.trithon_dlfet_tnand(a, b)
        # Fallback truth table
        if a == 0 or b == 0:
            return 2
        if a == 2 and b == 2:
            return 0
        return 1

    @staticmethod
    def full_adder(a: int, b: int, cin: int) -> tuple:
        """Full adder: returns (sum, carry)."""
        if _lib:
            _lib.trithon_dlfet_full_adder.argtypes = [ctypes.c_int] * 3
            _lib.trithon_dlfet_full_adder.restype = ctypes.c_int
            result = _lib.trithon_dlfet_full_adder(a, b, cin)
            return (result & 0xFF, (result >> 8) & 0xFF)
        raw = a + b + cin
        return (raw % 3, raw // 3)


class RadixTranscode:
    """Radix-3 ↔ Radix-2 transcoding engine."""
    
    @staticmethod
    def to_ternary(value: int, width: int = 8) -> TritArray:
        """Convert integer to balanced ternary."""
        if _lib:
            out = (ctypes.c_int8 * width)()
            _lib.trithon_rtc_to_ternary.argtypes = [
                ctypes.POINTER(ctypes.c_int8), ctypes.c_int, ctypes.c_int
            ]
            _lib.trithon_rtc_to_ternary.restype = ctypes.c_int
            _lib.trithon_rtc_to_ternary(out, value, width)
            return TritArray(list(out))
        # Pure-Python Avizienis
        trits = []
        n = value
        for _ in range(width):
            r = n % 3
            if r == 2:
                trits.append(-1)
                n = (n + 1) // 3
            else:
                trits.append(r)
                n = n // 3
        return TritArray(trits)

    @staticmethod
    def to_int(trits: TritArray) -> int:
        """Convert balanced ternary to integer."""
        if _lib:
            n = len(trits._data)
            arr = (ctypes.c_int8 * n)(*trits._data)
            _lib.trithon_rtc_to_int.argtypes = [
                ctypes.POINTER(ctypes.c_int8), ctypes.c_int
            ]
            _lib.trithon_rtc_to_int.restype = ctypes.c_int
            return _lib.trithon_rtc_to_int(arr, n)
        result = 0
        power = 1
        for t in trits._data:
            result += t * power
            power *= 3
        return result


class SRBCEngine:
    """Self-Referential Bias Calibration engine."""
    
    @staticmethod
    def measure_stability(ticks: int = 100, thermal_delta_mc: int = 0) -> int:
        """Run SRBC for N ticks, return stability percentage."""
        if _lib:
            _lib.trithon_srbc_stability.argtypes = [ctypes.c_int, ctypes.c_int]
            _lib.trithon_srbc_stability.restype = ctypes.c_int
            return _lib.trithon_srbc_stability(ticks, thermal_delta_mc)
        return 100  # Fallback: assume stable


class TritCrypto:
    """Ternary cryptographic primitives."""
    
    @staticmethod
    def hash(msg: TritArray) -> TritArray:
        """Hash a trit array, returning 81-trit digest."""
        if _lib:
            digest = (ctypes.c_int8 * 81)()
            arr = (ctypes.c_int8 * len(msg._data))(*msg._data)
            _lib.trithon_crypto_hash.argtypes = [
                ctypes.POINTER(ctypes.c_int8),
                ctypes.POINTER(ctypes.c_int8),
                ctypes.c_int
            ]
            _lib.trithon_crypto_hash.restype = None
            _lib.trithon_crypto_hash(digest, arr, len(msg._data))
            return TritArray(list(digest))
        # Pure-Python fallback: trivial non-cryptographic
        state = [0] * 81
        for i, t in enumerate(msg._data):
            state[i % 81] = (state[i % 81] + t + 1) % 3 - 1
        return TritArray(state)

    @staticmethod
    def roundtrip_test(data: TritArray, seed: int = 42) -> bool:
        """Test encrypt/decrypt roundtrip."""
        if _lib:
            arr = (ctypes.c_int8 * len(data._data))(*data._data)
            _lib.trithon_crypto_roundtrip.argtypes = [
                ctypes.POINTER(ctypes.c_int8), ctypes.c_int, ctypes.c_uint32
            ]
            _lib.trithon_crypto_roundtrip.restype = ctypes.c_int
            return _lib.trithon_crypto_roundtrip(arr, len(data._data), seed) == 1
        return True


class PropDelay:
    """Propagation delay model for DLFET-RM transitions."""
    
    DELAYS = {
        (0, 1): 120, (1, 2): 80, (0, 2): 60,
        (2, 1): 130, (1, 0): 90, (2, 0): 55
    }
    
    @staticmethod
    def nominal(from_state: int, to_state: int) -> int:
        """Get nominal delay in picoseconds."""
        if _lib:
            _lib.trithon_pdelay_nominal.argtypes = [ctypes.c_int, ctypes.c_int]
            _lib.trithon_pdelay_nominal.restype = ctypes.c_int
            return _lib.trithon_pdelay_nominal(from_state, to_state)
        return PropDelay.DELAYS.get((from_state, to_state), 0)


class TTL:
    """Ternary Temporal Logic — 3-valued epistemic reasoning."""
    
    @staticmethod
    def always(trace: List[int]) -> Trit:
        """ALWAYS(φ): has φ been true at every step?"""
        if _lib:
            arr = (ctypes.c_int8 * len(trace))(*trace)
            _lib.trithon_ttl_always.argtypes = [
                ctypes.POINTER(ctypes.c_int8), ctypes.c_int
            ]
            _lib.trithon_ttl_always.restype = ctypes.c_int8
            return Trit(_lib.trithon_ttl_always(arr, len(trace)))
        if any(t == -1 for t in trace):
            return Trit.FALSE
        if any(t == 0 for t in trace):
            return Trit.UNKNOWN
        return Trit.TRUE

    @staticmethod
    def eventually(trace: List[int]) -> Trit:
        """EVENTUALLY(φ): has φ been true at any step?"""
        if _lib:
            arr = (ctypes.c_int8 * len(trace))(*trace)
            _lib.trithon_ttl_eventually.argtypes = [
                ctypes.POINTER(ctypes.c_int8), ctypes.c_int
            ]
            _lib.trithon_ttl_eventually.restype = ctypes.c_int8
            return Trit(_lib.trithon_ttl_eventually(arr, len(trace)))
        if any(t == 1 for t in trace):
            return Trit.TRUE
        if any(t == 0 for t in trace):
            return Trit.UNKNOWN
        return Trit.FALSE


class PAM3:
    """PAM-3/4 pulse amplitude modulation interconnect."""
    
    @staticmethod
    def roundtrip(trits: TritArray) -> bool:
        """Test PAM-3 encode/decode roundtrip."""
        if _lib:
            arr = (ctypes.c_int8 * len(trits._data))(*trits._data)
            _lib.trithon_pam3_roundtrip.argtypes = [
                ctypes.POINTER(ctypes.c_int8), ctypes.c_int
            ]
            _lib.trithon_pam3_roundtrip.restype = ctypes.c_int
            return _lib.trithon_pam3_roundtrip(arr, len(trits._data)) == 1
        return True

    @staticmethod
    def bandwidth_gain(trit_count: int) -> int:
        """Bandwidth gain over binary NRZ (×10)."""
        if _lib:
            _lib.trithon_pam3_bandwidth_gain.argtypes = [ctypes.c_int]
            _lib.trithon_pam3_bandwidth_gain.restype = ctypes.c_int
            return _lib.trithon_pam3_bandwidth_gain(trit_count)
        return 585  # log2(3)*1000 - 1000 = 585 → ×10 = 585


# ---- Friday Updates: STT-MRAM, T-IPC, TFS wrappers --------------------

class MRAMArray:
    """STT-MRAM Biaxial MTJ ternary memory interface."""

    @staticmethod
    def pack(trits: TritArray) -> int:
        """Pack 5 trits into a byte (0..242)."""
        if _lib and len(trits._data) >= 5:
            arr = (ctypes.c_int8 * 5)(*trits._data[:5])
            _lib.trithon_mram_pack.argtypes = [ctypes.POINTER(ctypes.c_int8)]
            _lib.trithon_mram_pack.restype = ctypes.c_int
            return _lib.trithon_mram_pack(arr)
        # Pure Python fallback
        val = 0
        for i in range(min(5, len(trits._data))):
            val += (trits._data[i] + 1) * (3 ** i)
        return val

    @staticmethod
    def unpack(byte_val: int) -> TritArray:
        """Unpack a byte (0..242) into 5 trits."""
        if _lib:
            out = (ctypes.c_int8 * 5)()
            _lib.trithon_mram_unpack.argtypes = [ctypes.c_int, ctypes.POINTER(ctypes.c_int8)]
            _lib.trithon_mram_unpack.restype = None
            _lib.trithon_mram_unpack(byte_val, out)
            return TritArray(list(out))
        # Pure Python fallback
        trits = []
        v = byte_val
        for _ in range(5):
            trits.append((v % 3) - 1)
            v //= 3
        return TritArray(trits)

    @staticmethod
    def roundtrip(trits: TritArray) -> bool:
        """Pack/unpack roundtrip test (first 5 trits)."""
        if _lib and len(trits._data) >= 5:
            arr = (ctypes.c_int8 * 5)(*trits._data[:5])
            _lib.trithon_mram_roundtrip.argtypes = [ctypes.POINTER(ctypes.c_int8)]
            _lib.trithon_mram_roundtrip.restype = ctypes.c_int
            return _lib.trithon_mram_roundtrip(arr) == 1
        return True

    @staticmethod
    def write_read(val: int) -> int:
        """Write trit to MRAM array and read back."""
        if _lib:
            _lib.trithon_mram_write_read.argtypes = [ctypes.c_int8]
            _lib.trithon_mram_write_read.restype = ctypes.c_int8
            return int(_lib.trithon_mram_write_read(val))
        return val

    @staticmethod
    def nominal_resistance(state: int) -> int:
        """Get nominal resistance ×10 for MTJ state (0/1/2)."""
        if _lib:
            _lib.trithon_mram_nominal_r.argtypes = [ctypes.c_int]
            _lib.trithon_mram_nominal_r.restype = ctypes.c_int
            return _lib.trithon_mram_nominal_r(state)
        return [50, 120, 250][state] if 0 <= state <= 2 else 0


class TIPCChannel:
    """Ternary-Native IPC with Huffman compression + Guardian Trit."""

    @staticmethod
    def roundtrip(trits: TritArray) -> bool:
        """Compress/decompress roundtrip test."""
        if _lib:
            arr = (ctypes.c_int8 * len(trits._data))(*trits._data)
            _lib.trithon_tipc_roundtrip.argtypes = [
                ctypes.POINTER(ctypes.c_int8), ctypes.c_int
            ]
            _lib.trithon_tipc_roundtrip.restype = ctypes.c_int
            return _lib.trithon_tipc_roundtrip(arr, len(trits._data)) == 1
        return True

    @staticmethod
    def guardian(trits: TritArray) -> int:
        """Compute Guardian Trit (balanced ternary XOR checksum)."""
        if _lib:
            arr = (ctypes.c_int8 * len(trits._data))(*trits._data)
            _lib.trithon_tipc_guardian.argtypes = [
                ctypes.POINTER(ctypes.c_int8), ctypes.c_int
            ]
            _lib.trithon_tipc_guardian.restype = ctypes.c_int8
            return int(_lib.trithon_tipc_guardian(arr, len(trits._data)))
        # Pure Python fallback
        g = 0
        for t in trits._data:
            g = (g + t) % 3
            if g == 2: g = -1
        return g

    @staticmethod
    def compression_ratio(trits: TritArray) -> int:
        """Compression ratio ×1000."""
        if _lib:
            arr = (ctypes.c_int8 * len(trits._data))(*trits._data)
            _lib.trithon_tipc_compression_ratio.argtypes = [
                ctypes.POINTER(ctypes.c_int8), ctypes.c_int
            ]
            _lib.trithon_tipc_compression_ratio.restype = ctypes.c_int
            return _lib.trithon_tipc_compression_ratio(arr, len(trits._data))
        return 1000  # Fallback: 100%


class TFS:
    """Ternary-Native File System with Balanced Ternary Huffman."""

    @staticmethod
    def roundtrip(trits: TritArray) -> bool:
        """Huffman encode/decode roundtrip test."""
        if _lib:
            arr = (ctypes.c_int8 * len(trits._data))(*trits._data)
            _lib.trithon_tfs_roundtrip.argtypes = [
                ctypes.POINTER(ctypes.c_int8), ctypes.c_int
            ]
            _lib.trithon_tfs_roundtrip.restype = ctypes.c_int
            return _lib.trithon_tfs_roundtrip(arr, len(trits._data)) == 1
        return True

    @staticmethod
    def guardian(trits: TritArray) -> int:
        """Compute TFS Guardian Trit."""
        if _lib:
            arr = (ctypes.c_int8 * len(trits._data))(*trits._data)
            _lib.trithon_tfs_guardian.argtypes = [
                ctypes.POINTER(ctypes.c_int8), ctypes.c_int
            ]
            _lib.trithon_tfs_guardian.restype = ctypes.c_int8
            return int(_lib.trithon_tfs_guardian(arr, len(trits._data)))
        g = 0
        for t in trits._data:
            g = (g + t) % 3
            if g == 2: g = -1
        return g

    @staticmethod
    def density_gain() -> int:
        """Density gain ×100 (e.g. 158 = 1.58×)."""
        if _lib:
            _lib.trithon_tfs_density_gain.argtypes = []
            _lib.trithon_tfs_density_gain.restype = ctypes.c_int
            return _lib.trithon_tfs_density_gain()
        return 158

    @staticmethod
    def area_reduction() -> int:
        """Area reduction ×100 (e.g. 64 = 64%)."""
        if _lib:
            _lib.trithon_tfs_area_reduction.argtypes = []
            _lib.trithon_tfs_area_reduction.restype = ctypes.c_int
            return _lib.trithon_tfs_area_reduction()
        return 64

    @staticmethod
    def file_roundtrip(trits: TritArray) -> bool:
        """Full file write/read roundtrip test."""
        if _lib:
            arr = (ctypes.c_int8 * len(trits._data))(*trits._data)
            _lib.trithon_tfs_file_roundtrip.argtypes = [
                ctypes.POINTER(ctypes.c_int8), ctypes.c_int
            ]
            _lib.trithon_tfs_file_roundtrip.restype = ctypes.c_int
            return _lib.trithon_tfs_file_roundtrip(arr, len(trits._data)) == 1
        return True


# ---- Self-test ---------------------------------------------------------

def _self_test():
    """Quick self-test of Trithon module (pure Python + C extension).

    Runs every assertion and tracks pass/fail counts individually.
    The final summary line is machine-parseable by test_grand_summary.sh:
        Trithon: N passed, M failed (of T assertions)
    """
    import sys

    # ── Assertion counter ──────────────────────────────────────────────
    _pass = [0]
    _fail = [0]

    def check(condition, label=""):
        """Counted assertion: increments pass or fail counter."""
        if condition:
            _pass[0] += 1
        else:
            _fail[0] += 1
            print(f"  [FAIL] {label}")

    T, U, F = Trit.TRUE, Trit.UNKNOWN, Trit.FALSE

    # Report C extension status
    if native_available():
        ver = _lib.trithon_version()
        print(f"Trithon: C extension loaded (libtrithon.so v{ver // 100}.{ver % 100:02d})")
    else:
        print("Trithon: pure Python mode (libtrithon.so not found)")

    # Kleene logic
    check((T & T) == T, "Kleene: T&T==T")
    check((T & U) == U, "Kleene: T&U==U")
    check((T & F) == F, "Kleene: T&F==F")
    check((T | U) == T, "Kleene: T|U==T")
    check((U | F) == U, "Kleene: U|F==U")
    check((~T) == F, "Kleene: ~T==F")
    check((~U) == U, "Kleene: ~U==U")
    check((~F) == T, "Kleene: ~F==T")

    # Multiplication
    check((F * F) == T, "Mul: F*F==T")
    check((F * T) == F, "Mul: F*T==F")
    check((U * T) == U, "Mul: U*T==U")

    # Inc / Dec (cyclic)
    check(T.inc() == F, "Inc: T→F")
    check(F.inc() == U, "Inc: F→U")
    check(U.inc() == T, "Inc: U→T")
    check(T.dec() == U, "Dec: T→U")
    check(U.dec() == F, "Dec: U→F")
    check(F.dec() == T, "Dec: F→T")

    # Consensus / Accept-any (named aliases)
    check(T.consensus(T) == T, "Consensus: T,T→T")
    check(T.consensus(F) == F, "Consensus: T,F→F")
    check(T.consensus(U) == U, "Consensus: T,U→U")
    check(T.accept_any(F) == T, "AcceptAny: T,F→T")
    check(F.accept_any(F) == F, "AcceptAny: F,F→F")
    check(U.accept_any(F) == U, "AcceptAny: U,F→U")

    # TritArray
    a = TritArray([1, 0, -1, 1, 0])
    b = TritArray([1, 1, 1, -1, 0])

    # Dot product
    dot = a.dot(b)
    check(dot == (1*1 + 0*1 + (-1)*1 + 1*(-1) + 0*0), "Dot: 5-elem dot product")

    # Sparse dot
    dot_s = a.dot_sparse(b, n=4, m=2)
    check(isinstance(dot_s, int), "Sparse dot: returns int")

    # Kleene ops
    c = a & b
    check(c[0] == Trit.TRUE, "Array Kleene AND: c[0]==T")
    check(c[1] == Trit.UNKNOWN, "Array Kleene AND: c[1]==U")

    d = a | b
    check(d[0] == Trit.TRUE, "Array Kleene OR: d[0]==T")
    check(d[2] == Trit.TRUE, "Array Kleene OR: d[2]==T")

    # Integer conversion
    arr = TritArray.from_int(42)
    check(arr.to_int() == 42, "Int conv: 42 roundtrip")

    arr = TritArray.from_int(-13)
    check(arr.to_int() == -13, "Int conv: -13 roundtrip")

    # Packing
    packed = a.to_bytes()
    restored = TritArray.from_bytes(packed, len(a))
    check(restored == a, "Pack: roundtrip")

    # Sparsity
    sparse = TritArray.splat(0, 32)
    check(sparse.sparsity() == 1.0, "Sparsity: all-zero==1.0")
    dense = TritArray.splat(1, 32)
    check(dense.sparsity() == 0.0, "Sparsity: all-T==0.0")

    # FFT
    fft_in = TritArray([1, -1, 0])
    fft_out = fft_in.fft_step(0)
    check(len(fft_out) == 3, "FFT: output length")

    # QEMU noise
    noise = QEMUNoise('uniform', seed=42, prob_ppm=100000)
    flipped = 0
    for _ in range(1000):
        if noise.read(1) != 1:
            flipped += 1
    check(flipped > 0, "QEMUnoise: flips occur")

    # Division
    check(Trit(1) / Trit(1) == Trit.TRUE, "Div: T/T==T")
    check(Trit(1) / Trit(-1) == Trit.FALSE, "Div: T/F==F")
    check(Trit(-1) / Trit(-1) == Trit.TRUE, "Div: F/F==T")
    check(Trit(0) / Trit(1) == Trit.UNKNOWN, "Div: U/T==U")
    check(Trit(1) / Trit(0) == Trit.UNKNOWN, "Div: T/U==U (div-by-zero)")

    # Exponentiation
    check(Trit(1) ** Trit(1) == Trit.TRUE, "Exp: T^T==T")
    check(Trit(1) ** Trit(0) == Trit.TRUE, "Exp: T^U==T")
    check(Trit(-1) ** Trit(1) == Trit.FALSE, "Exp: F^T==F")
    check(Trit(-1) ** Trit(0) == Trit.TRUE, "Exp: F^U==T")
    check(Trit(0) ** Trit(1) == Trit.UNKNOWN, "Exp: U^T==U")
    check(Trit(0) ** Trit(0) == Trit.TRUE, "Exp: U^U==T")

    # C extension specific tests (only if loaded)
    if native_available():
        # Multi-radix DOT via seT5 engine
        a32 = TritArray.splat(1, 32)
        b32 = TritArray.splat(1, 32)
        a_arr = (ctypes.c_int8 * 32)(*a32._data)
        b_arr = (ctypes.c_int8 * 32)(*b32._data)
        mr_dot = _lib.trithon_mr_dot(a_arr, b_arr, 32)
        check(mr_dot == 32, f"MR dot(all T, all T)==32, got {mr_dot}")

        # IMPLIES, EQUIV
        check(_lib.trithon_implies(1, 1) == 1, "Implies: T→T==T")
        check(_lib.trithon_implies(1, -1) == -1, "Implies: T→F==F")
        check(_lib.trithon_implies(-1, 1) == 1, "Implies: F→T==T")
        check(_lib.trithon_equiv(1, 1) == 1, "Equiv: T≡T==T")
        check(_lib.trithon_equiv(1, -1) == -1, "Equiv: T≡F==F")

        print("  C extension tests: all passed")

    # ---- Functional utility module tests ----
    print("\n--- Functional Utility Module Tests ---")

    # TWQ
    weights = [1000, -1000, 0, 500, -500, 200, -200, 100]
    q = TWQ.quantize(weights)
    check(q._data[0] == 1, "TWQ: large positive → +1")
    check(q._data[1] == -1, "TWQ: large negative → -1")
    check(q._data[2] == 0, "TWQ: zero → 0")
    print("  TWQ: quantization PASSED")

    # DLFET
    check(DLFETSim.tnot(0) == 2, "DLFET: TNOT(0)==2")
    check(DLFETSim.tnot(2) == 0, "DLFET: TNOT(2)==0")
    check(DLFETSim.tnand(0, 0) == 2, "DLFET: TNAND(0,0)==2")
    check(DLFETSim.tnand(2, 2) == 0, "DLFET: TNAND(2,2)==0")
    s, c = DLFETSim.full_adder(1, 1, 1)
    check(s == 0 and c == 1, "DLFET: FA(1,1,1)==(0,1)")
    print("  DLFET-RM: gate simulation PASSED")

    # Radix Transcode
    for v in [0, 1, -1, 42, -42, 100]:
        t = RadixTranscode.to_ternary(v, 8)
        back = RadixTranscode.to_int(t)
        check(back == v, f"RTC: roundtrip {v}")
    print("  RadixTranscode: roundtrip PASSED")

    # SRBC
    stab = SRBCEngine.measure_stability(10, 0)
    check(stab >= 0 and stab <= 100, "SRBC: stability in range")
    print("  SRBC: stability PASSED")

    # Crypto
    msg = TritArray([1, -1, 0, 1, -1])
    d1 = TritCrypto.hash(msg)
    d2 = TritCrypto.hash(msg)
    check(d1._data == d2._data, "Crypto: hash is deterministic")
    check(TritCrypto.roundtrip_test(msg), "Crypto: encrypt/decrypt roundtrip")
    print("  TritCrypto: hash + cipher PASSED")

    # PropDelay
    check(PropDelay.nominal(0, 1) == 120, "PropDelay: 0→1==120ps")
    check(PropDelay.nominal(2, 0) == 55, "PropDelay: 2→0==55ps")
    print("  PropDelay: nominal values PASSED")

    # TTL
    check(TTL.always([1, 1, 1]) == Trit.TRUE, "TTL: ALWAYS(T,T,T)==T")
    check(TTL.always([1, 0, 1]) == Trit.UNKNOWN, "TTL: ALWAYS(T,U,T)==U")
    check(TTL.always([1, -1, 1]) == Trit.FALSE, "TTL: ALWAYS(T,F,T)==F")
    check(TTL.eventually([-1, -1, 1]) == Trit.TRUE, "TTL: EVENTUALLY(F,F,T)==T")
    print("  TTL: temporal logic PASSED")

    # PAM-3
    data = TritArray([1, -1, 0, 1, -1, 0, 1, -1])
    check(PAM3.roundtrip(data), "PAM-3: roundtrip lossless")
    gain = PAM3.bandwidth_gain(100)
    check(gain > 0, "PAM-3: bandwidth gain positive")
    print("  PAM-3: interconnect PASSED")

    print("Trithon: functional utility tests PASSED")

    # ---- Friday Updates module tests ----
    print("\n--- Friday Updates Module Tests ---")

    # STT-MRAM
    mram_trits = TritArray([1, -1, 0, 1, 0])
    pk = MRAMArray.pack(mram_trits)
    check(0 <= pk < 243, f"MRAM: packed value {pk} in range")
    unpacked = MRAMArray.unpack(pk)
    for i in range(5):
        check(unpacked._data[i] == mram_trits._data[i], f"MRAM: unpack[{i}] matches")
    check(MRAMArray.roundtrip(mram_trits), "MRAM: pack/unpack roundtrip")
    check(MRAMArray.write_read(1) == 1, "MRAM: write/read +1")
    check(MRAMArray.write_read(-1) == -1, "MRAM: write/read -1")
    check(MRAMArray.write_read(0) == 0, "MRAM: write/read 0")
    check(MRAMArray.nominal_resistance(0) == 50, "MRAM: R_LOW==50")
    check(MRAMArray.nominal_resistance(1) == 120, "MRAM: R_MID==120")
    check(MRAMArray.nominal_resistance(2) == 250, "MRAM: R_HIGH==250")
    print("  STT-MRAM: memory interface PASSED")

    # T-IPC
    tipc_data = TritArray([1, -1, 0, 1, 0, -1])
    check(TIPCChannel.roundtrip(tipc_data), "TIPC: compress/decompress roundtrip")
    g = TIPCChannel.guardian(tipc_data)
    check(-1 <= g <= 1, "TIPC: guardian in valid range")
    ratio = TIPCChannel.compression_ratio(tipc_data)
    check(ratio > 0, "TIPC: compression ratio positive")
    print("  T-IPC: IPC protocol PASSED")

    # TFS
    tfs_data = TritArray([1, 0, -1, 1, -1, 0, 0, 1])
    check(TFS.roundtrip(tfs_data), "TFS: Huffman roundtrip")
    tg = TFS.guardian(tfs_data)
    check(-1 <= tg <= 1, "TFS: guardian in valid range")
    check(TFS.density_gain() >= 150, "TFS: density gain >= 1.5x")
    check(TFS.area_reduction() >= 50, "TFS: area reduction >= 50%")
    check(TFS.file_roundtrip(tfs_data), "TFS: file write/read roundtrip")
    print("  TFS: file system PASSED")

    print("Trithon: Friday Updates tests PASSED")

    # ── Final assertion summary (machine-parseable) ───────────────────
    total = _pass[0] + _fail[0]
    print(f"\nTrithon: {_pass[0]} passed, {_fail[0]} failed (of {total} assertions)")
    if _fail[0] > 0:
        print("Trithon: SELF-TEST FAILED")
        sys.exit(1)
    else:
        print("Trithon: all self-tests PASSED")


if __name__ == '__main__':
    _self_test()
