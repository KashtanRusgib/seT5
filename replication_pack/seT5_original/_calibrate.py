#!/usr/bin/env python3
"""Quick calibration: find the right term count for 5-10s pi benchmark."""
import time, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ternbench.ternbench import machin_pi_binary

results = []
for n in [6000, 7000, 8000]:
    t0 = time.perf_counter()
    machin_pi_binary(n)
    elapsed = time.perf_counter() - t0
    results.append(f"{n}: {elapsed:.2f}s")

with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '_calibrate_results.txt'), 'w') as f:
    for r in results:
        f.write(r + '\n')
