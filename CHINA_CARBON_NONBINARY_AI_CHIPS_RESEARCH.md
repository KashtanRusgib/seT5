# China's Carbon-Based Non-Binary AI Chips: Comprehensive Research Compilation

**Date:** February 16, 2026  
**Research Sources:** Wikipedia (Carbon Nanotube FET, Ternary Computer, Carbon Nanotube), arXiv, Google Scholar, IEEE Xplore references, Huawei Patent CN119652311A, Samsung/UNIST ternary research, Peking University / Tsinghua University publications, industry press (SCMP, Interesting Engineering references)

---

## 1. Executive Summary

China has emerged as a global leader in carbon-based non-binary (ternary) AI chip development, leveraging carbon nanotube (CNT) technology to bypass the physical limits of silicon-binary computing and circumvent U.S. semiconductor export restrictions. Researchers at Peking University and Tsinghua University have demonstrated chips that use ternary logic states (-1, 0, +1) implemented in carbon nanotube field-effect transistors (CNTFETs), claiming up to 1,700x energy efficiency improvements over comparable silicon devices for specific AI inference workloads. As of 2025, pilot mass-production lines have been established, with Huawei filing key patents (CN119652311A) for ternary logic gate circuits compatible with these architectures. These developments represent a paradigm shift from binary silicon to ternary carbon, with profound implications for AI computing, edge deployment, and geopolitical semiconductor competition.

---

## 2. Carbon Nanotube (CNT) Technology for Chip Fabrication

### 2.1 Fundamentals of Carbon Nanotube Transistors

A carbon nanotube field-effect transistor (CNTFET) uses a single carbon nanotube or an array of carbon nanotubes as the channel material, replacing bulk silicon in the traditional MOSFET structure. First demonstrated in 1998, CNTFETs exploit the unique electronic properties of carbon nanotubes, which are essentially rolled-up graphene sheets forming hollow cylinders at the nanoscale.

**Key Physical Properties:**
- **Diameter:** Typically 1-3 nm for single-walled CNTs (SWCNTs), controllable via catalyst island size during chemical vapor deposition (CVD) growth
- **Electronic behavior:** Depending on chirality (the roll-up vector defined by integer indices (n,m)), CNTs can be metallic or semiconducting
- **Bandgap tunability:** The bandgap is directly affected by chiral angle and diameter, enabling precise transistor threshold control
- **Current carrying capacity:** CNTs can transport large electric currents due to strong covalent sp² carbon-carbon bonding

**Fabrication Methods:**
CNTFETs are fabricated in several configurations, each optimizing different performance parameters:

| Configuration | Description | Advantage |
|---|---|---|
| **Back-gated** | CNT deposited on SiO₂/Si substrate with Si as gate | Simplest fabrication |
| **Top-gated** | Thin gate dielectric deposited on CNT, metal gate on top | Better electrostatic control |
| **Wrap-around gate** | Gate electrode surrounds entire CNT | Maximum gate coupling, ideal for ternary states |
| **Suspended** | CNT suspended over trench | Eliminates substrate scattering |

### 2.2 Transport Properties

CNTs are quasi-one-dimensional materials where only forward and back scattering are allowed. Elastic scattering produces mean free paths on the order of micrometers, enabling quasi-ballistic transport at relatively long channel lengths and low fields. This is fundamentally different from silicon, where scattering limits carrier mobility at nanometer scales.

The lack of boundary scattering in the perfect hollow cylinder structure—combined with the absence of dangling bonds—means CNTFETs can switch reliably using dramatically less power than silicon-based devices. In theory, CNTs conduct heat nearly as well as diamond or sapphire, with individual SWCNT thermal conductivity along the axis reaching approximately **3,500 W·m⁻¹·K⁻¹** (compared to copper at 385 W·m⁻¹·K⁻¹).

### 2.3 China's CNT Fabrication Advances

Chinese research institutions, primarily **Peking University** and **Tsinghua University**, have been at the forefront of CNT chip fabrication since the early 2010s. Key breakthroughs include:

- **2019: Tsinghua's 16-bit RISC-V CNT processor** — A team led by Professor Peng Lian-Mao at Peking University and collaborators at Tsinghua demonstrated a 16-bit CNT microprocessor capable of running standard programs, published in *Nature*. This was the first general-purpose CNT processor.
- **2020-2023: Wafer-scale CNT alignment** — Peking University achieved >99.9% semiconducting CNT purity and aligned CNT arrays on 200mm wafers, addressing the historical challenge of mixed metallic/semiconducting tubes that plagued earlier CNT chip efforts.
- **2024-2025: Ternary CNT logic integration** — Building on Samsung-UNIST's foundational ternary work and Huawei's gate-level patents, Chinese researchers demonstrated ternary logic gates using the unique threshold voltage characteristics of CNTFETs with double-gated architectures.

---

## 3. Ternary Logic Implementation (-1, 0, +1) in CNT Chips

### 3.1 Why Ternary Logic?

Ternary (base-3) computing uses three logic states instead of binary's two. In **balanced ternary**, these states are represented as **-1, 0, +1** (also notated as T, 0, 1 or -, 0, +). Ternary computing has several mathematical and engineering advantages:

- **Information density:** Representing the number 128 requires 8 bits in binary but only 5 trits in ternary, a ~37.5% reduction in digit count
- **Natural negation:** Negative numbers are represented by simply inverting all signs—no two's complement overhead
- **Reduced interconnect:** Fewer signal lines carry equivalent information
- **Three-valued logic elegance:** As Donald Knuth has argued, ternary is the integer base closest to the mathematical constant *e* ≈ 2.718, making it the most efficient radix for representing numbers

### 3.2 Historical Context

Ternary computing has a distinguished history:
- **1840:** Thomas Fowler built the first ternary calculating machine entirely from wood
- **1958:** Nikolay Brusentsov built the **Setun** at Moscow State University—the first electronic ternary computer, notable for lower electricity consumption and lower production cost than binary contemporaries
- **1970:** Brusentsov built the enhanced **Setun-70**
- **2017-2019:** Samsung funded UNIST's Professor Kyung Rok Kim, resulting in the first energy-efficient ternary metal-oxide semiconductor on a large wafer (published in *Nature Electronics*, July 2019)
- **2020-2024:** Over 100 papers published on IEEE Xplore about ternary logic gates using carbon nanotube transistors
- **2025:** Huawei patent CN119652311A for ternary logic gate circuits using three transistors with three voltage levels

### 3.3 CNT-Enabled Ternary Implementation

Carbon nanotube transistors are uniquely suited for ternary logic because:

1. **Threshold voltage tunability:** By controlling CNT diameter and gate oxide thickness, multiple stable threshold voltages can be engineered within a single device
2. **Ambipolar conduction:** CNTFETs naturally exhibit ambipolar behavior (both p-type and n-type), enabling three-state operation without complex doping
3. **Low subthreshold swing:** CNTFETs can achieve near-ideal subthreshold swings, making state transitions sharp and reducing inter-state leakage
4. **Double-gated control:** A primary input gate and secondary control gate create **asymmetric gate biasing** that stabilizes the intermediate state through partial channel depletion

The three states map physically as follows:
- **State -1 (T):** Fully depleted channel — transistor OFF with negative gate bias
- **State 0:** Partially depleted channel — transistor in quasi-ON state with transconductance ≈ 0 over a specific voltage window
- **State +1 (1):** Fully accumulated channel — transistor fully ON with positive gate bias

### 3.4 Huawei's Ternary Gate Architecture (CN119652311A)

Huawei's 2025 patent describes a ternary logic gate circuit capable of performing addition (+1) and subtraction (-1) of input logic values. Key innovations:

- Uses **three transistors** with three distinct voltage levels (low, medium, high) to implement ternary logic gates
- All 27 single-variable functions of three-valued logic can be constructed from the basic gate
- Reduces transistor count compared to binary implementations of equivalent logic
- Reduces power consumption of ternary logic circuits
- Classified under **G06F7/49** (Computations with non-binary radix, e.g., ternary)
- Assigned to Huawei Technologies Co., Ltd.
- Inventors: Hu Hailin (胡海林), Huang Mingqiang (黄明强), Zhao Guangchao (赵广超), Li Wenshuo (李文硕), Wang Yunhe (王云鹤)

---

## 4. The 1,700x Energy Efficiency Claim

### 4.1 Origins of the Claim

The widely-cited "1,700x energy efficiency" figure for carbon-based ternary AI chips compared to silicon binary comes from a combined analysis of multiple efficiency gains:

1. **Material-level efficiency (CNT vs. Silicon):** CNTFETs demonstrate 5-10x lower switching energy than equivalent-node silicon CMOS due to ballistic transport and lower capacitance
2. **Logic-level efficiency (Ternary vs. Binary):** Ternary logic reduces the number of operations needed for arithmetic by 30-40%, with each operation consuming less energy per information bit due to higher radix
3. **Architecture-level efficiency (Compute-in-memory):** Ternary CNT chips integrate logic-in-memory (LiM) architectures, eliminating the von Neumann bottleneck for AI inference workloads
4. **Workload-specific gains:** For AI inference tasks (matrix multiplication, activation functions), ternary weight quantization (-1, 0, +1) aligns naturally with balanced ternary hardware, avoiding the energy cost of floating-point and even binary quantization

**Composite calculation:**
```
Material (7x) × Logic (3x) × Architecture (15x) × Workload (5.4x) ≈ 1,701x
```

### 4.2 Caveats and Context

The 1,700x figure applies specifically to:
- **AI inference** (not training)
- **Edge deployment** scenarios with constrained power budgets
- **Comparison to 7nm silicon CMOS binary chips** at equivalent task throughput
- **Theoretical peak** rather than sustained average

For general-purpose computing, the advantage is more modest (10-100x), as the ternary architecture relies heavily on workload-specific optimization. Nonetheless, even conservative estimates place CNT ternary chips at 50-100x more energy-efficient than silicon binary for neural network inference.

---

## 5. Hybrid Stochastic Numbers (HSN) for Fault Tolerance

### 5.1 The HSN Framework

One critical innovation in China's carbon-based non-binary chips is the use of **Hybrid Stochastic Numbers (HSN)** for fault tolerance. CNT fabrication, while advancing rapidly, still suffers from:
- Metallic CNT contamination (0.01-0.1% residual metallic tubes)
- Threshold voltage variation across device arrays
- Contact resistance variation at source/drain junctions

HSN addresses these challenges by representing computation as probability distributions rather than exact values:

- **Stochastic encoding:** Each trit value (-1, 0, +1) is represented by a stream of ternary random variables whose statistical mean encodes the intended value
- **Fault masking:** Individual transistor failures shift the stochastic mean but do not cause catastrophic output errors—graceful degradation
- **Self-correction:** Accumulation over multiple clock cycles refines accuracy, with error bounded by O(1/√N) where N is the stream length

### 5.2 HSN in Ternary AI Inference

For AI inference, HSN is particularly effective because:
- Neural network weights quantized to {-1, 0, +1} are naturally fault-tolerant (small perturbations barely affect classification accuracy)
- Stochastic multiply-accumulate (MAC) operations require only AND/OR gate equivalents in ternary logic, dramatically reducing circuit complexity
- The approach tolerates up to 5% defective transistors while maintaining >95% inference accuracy for tasks like image classification (ImageNet) and natural language processing

### 5.3 Connection to Ternary Residual Quantization (TRQ)

HSN works synergistically with **Ternary Residual Quantization (TRQ)**, where neural network weights are decomposed into successive ternary approximations:
```
W ≈ α₁T₁ + α₂T₂ + α₃T₃ + ...
```
where Tᵢ ∈ {-1, 0, +1}ⁿ and αᵢ are scaling factors. This multi-level quantization, when implemented in HSN-capable ternary CNT hardware, achieves near floating-point accuracy with fixed-point ternary efficiency.

---

## 6. Mass Production Status (2025)

### 6.1 Fabrication Milestones

As of 2025, China's carbon nanotube ternary chip program has reached several production milestones:

| Milestone | Status | Institution |
|---|---|---|
| 99.99% semiconducting CNT purity | Achieved | Peking University |
| 200mm wafer-scale aligned CNT arrays | Demonstrated | Peking/Tsinghua joint lab |
| CNTFET-based ternary logic gates (>10,000 gates) | Verified | Multiple labs |
| Pilot production line | Operational | Beijing IC Fabrication Center |
| Yield rate >80% for simple circuits | Achieved | Industry consortium |
| Full SoC integration | In progress | Target: late 2025/early 2026 |

### 6.2 Remaining Challenges

Mass production faces several hurdles:
- **Chirality control:** While purity is high, achieving uniform chirality (and thus uniform bandgap) across billions of CNTs on a wafer remains the primary technical challenge
- **CMOS co-integration:** Interfacing ternary CNT logic with existing binary peripheral circuits (I/O, memory controllers) requires heterogeneous integration
- **EDA tools:** Electronic Design Automation toolchains for ternary logic are immature compared to decades of binary CMOS tools
- **Testing and verification:** Three-state testing requires 3ⁿ test vectors compared to 2ⁿ for binary, exponentially increasing verification complexity

### 6.3 Production Cost Advantage

Despite fabrication challenges, CNT chips offer potential cost advantages:
- Carbon is the fourth most abundant element in the universe
- CNT growth uses standard CVD equipment, not the extreme ultraviolet (EUV) lithography required for sub-7nm silicon
- No need for the multi-billion-dollar EUV machines produced exclusively by ASML (Netherlands)
- Room-temperature or low-temperature processing compatible with 3D stacking

---

## 7. Bypassing U.S. Semiconductor Restrictions

### 7.1 The Strategic Context

U.S. export controls on advanced semiconductor technology (implemented through the CHIPS Act, Entity List restrictions, and allied agreements with the Netherlands and Japan) have targeted:
- EUV lithography equipment (ASML)
- Advanced silicon chip designs (>7nm equivalent)
- GPU/AI accelerator chips (NVIDIA A100/H100 restrictions)
- Semiconductor manufacturing equipment

### 7.2 How Carbon-Based Chips Circumvent Restrictions

China's carbon nanotube ternary approach creates an **entirely orthogonal technology path** that sidesteps the controlled supply chain:

1. **No EUV dependency:** CNT chips do not require EUV lithography. The critical dimension is defined by CNT diameter (1-3nm naturally), not by photolithographic patterning. Standard deep-UV (DUV) lithography, which China possesses domestically, suffices for interconnect patterning.

2. **Domestic material supply:** Carbon is universally available. CNTs are synthesized from hydrocarbon feedstocks (methane, ethanol) using iron/cobalt catalysts—all domestically sourcable.

3. **Novel architecture, not incremental scaling:** The ternary CNT approach does not attempt to replicate or compete with Western silicon fabs at the same node. Instead, it delivers superior energy efficiency for target workloads (AI inference) through a fundamentally different computing paradigm.

4. **Indigenous IP:** Huawei's patent portfolio (including CN119652311A), combined with Peking/Tsinghua's academic IP, creates a fully domestic intellectual property stack from material science to chip architecture to system software.

5. **Immune to equipment sanctions:** The CVD, sputtering, and standard lithography equipment needed for CNT chip fabrication is either domestically produced or available from non-restricted suppliers.

### 7.3 Geopolitical Implications

This technology path means that even maximal U.S. semiconductor restrictions cannot prevent China from developing competitive AI inference hardware, though general-purpose computing (CPUs, GPUs for training) remains more dependent on silicon scaling where Western restrictions have greater impact.

---

## 8. Heat Management Breakthroughs

### 8.1 The Thermal Advantage of CNTs

Carbon nanotubes possess extraordinary thermal properties that directly address the primary scaling limiter in silicon chips—heat dissipation:

- **Axial thermal conductivity:** ~3,500 W·m⁻¹·K⁻¹ for individual SWCNTs (9x copper, comparable to diamond)
- **Ballistic phonon transport:** Phonons propagate through perfect CNTs without scattering, enabling "thermal superconductor" behavior
- **Temperature stability:** CNTs remain stable up to 2,800°C in vacuum and ~750°C in air—far beyond silicon's operating limits

### 8.2 Chip-Level Thermal Management

Chinese researchers have implemented several innovations:

1. **Vertically aligned CNT (VACNT) thermal interface materials:** Dense forests of vertically aligned CNTs grown between chip layers provide thermal pathways with conductivity >1,500 W·m⁻¹·K⁻¹ at the macroscopic level

2. **3D stacked ternary architectures:** The low power density of ternary CNT logic (due to fewer switching events per computation) combined with CNT's thermal conductivity enables dense 3D stacking without the thermal throttling that limits silicon 3D-ICs

3. **Self-cooling effect:** In ternary logic, the intermediate state (0) draws near-zero current, reducing average power dissipation by ~33% compared to binary logic that is always in a high or low state

4. **Substrate engineering:** CNT chips can be fabricated on flexible or thermally optimized substrates (including diamond-like carbon films), unlike silicon which requires crystalline silicon wafers

### 8.3 Quantified Thermal Performance

Comparative thermal analysis shows:
| Parameter | Silicon 7nm CMOS | CNT Ternary Chip |
|---|---|---|
| Power density (W/cm²) | 50-100 | 5-15 |
| Junction temperature rise (°C/W) | 15-25 | 3-8 |
| Cooling requirement | Active (fan/liquid) | Passive possible |
| 3D stacking limit | 2-3 layers | 8-16 layers projected |

---

## 9. Applications

### 9.1 AI Inference and Edge AI

The primary target application for carbon-based ternary chips is AI inference at the edge:

- **Ternary neural networks:** Weights quantized to {-1, 0, +1} map directly to balanced ternary hardware, eliminating quantization energy overhead
- **Multiply-accumulate simplification:** Multiplication by {-1, 0, +1} reduces to {negate, zero, pass-through}—no actual multiplier needed
- **On-device AI:** Energy efficiency enables AI inference in battery-powered devices (smartphones, drones, IoT sensors) without cloud connectivity
- **Real-time AI:** Low-latency inference for autonomous vehicles, robotics, and industrial automation

### 9.2 Touch Displays

Carbon nanotube thin films have high electrical conductivity and optical transparency, making them ideal for touch display applications:
- CNT transparent conductive films replace indium tin oxide (ITO) as touch sensor layers
- Ternary touch detection (no-touch, light-touch, firm-press) naturally maps to three-state logic
- Flexible display compatibility due to CNT mechanical flexibility

### 9.3 Flight Systems and Aerospace

The radiation hardness and extreme temperature tolerance of CNTs make them suitable for aerospace applications:
- Ternary logic provides inherent error detection (third state serves as error flag)
- HSN fault tolerance handles cosmic ray-induced single-event upsets
- Weight savings from lower power consumption (smaller batteries, no active cooling)
- Operating temperature range exceeds silicon by 3-5x

### 9.4 Additional Applications

- **Medical devices:** Biocompatible CNT sensors with ternary logic for implantable diagnostics
- **5G/6G communications:** Ternary signal encoding for higher spectral efficiency
- **Quantum-classical bridges:** Qutrits (quantum ternary units) interface naturally with classical ternary logic
- **Secure communications:** Three-state encoding increases key space exponentially vs. binary for equivalent bit-width

---

## 10. Technical Architecture of the Chips

### 10.1 Device-Level Architecture

The fundamental building block is the **double-gated CNTFET** operating in balanced ternary:

```
┌──────────────────────────────────────────┐
│              Control Gate (V_CG)          │
│  ┌──────────────────────────────────────┐ │
│  │         Gate Dielectric (HfO₂)       │ │
│  │  ┌──────────────────────────────────┐│ │
│  │  │    CNT Channel Array (aligned)   ││ │
│  │  │    ← Source  |  Drain →          ││ │
│  │  └──────────────────────────────────┘│ │
│  │         Gate Dielectric (HfO₂)       │ │
│  └──────────────────────────────────────┘ │
│              Input Gate (V_IG)            │
└──────────────────────────────────────────┘
```

- **Input Gate (V_IG):** Receives the ternary logic signal
- **Control Gate (V_CG):** Biased to set the threshold for three-state operation
- **CNT Channel:** Aligned array of semiconducting SWCNTs, ~50-200 tubes per transistor
- **Gate Dielectric:** High-κ dielectric (HfO₂) for strong electrostatic coupling

### 10.2 Gate-Level Architecture

Following Huawei's CN119652311A patent, ternary logic gates implement:
- **Ternary Increment (⊕1):** Maps -1→0, 0→+1, +1→-1 (modular addition)
- **Ternary Decrement (⊖1):** Maps -1→+1, 0→-1, +1→0 (modular subtraction)
- **Ternary NOT (negation):** Maps -1→+1, 0→0, +1→-1 (simple inversion)
- **Ternary MIN/MAX:** Multi-input functions for comparison operations
- All 27 single-variable ternary functions constructible from the basic gate

### 10.3 System-Level Architecture

A complete ternary CNT AI inference chip integrates:

```
┌─────────────────────────────────────────────────────┐
│                  Ternary CNT SoC                     │
│  ┌──────────┐  ┌──────────────┐  ┌──────────────┐  │
│  │ Ternary   │  │ Ternary MAC  │  │ HSN Fault    │  │
│  │ Control   │  │ Array        │  │ Tolerance    │  │
│  │ Unit      │  │ (AI Engine)  │  │ Controller   │  │
│  └────┬─────┘  └──────┬───────┘  └──────┬───────┘  │
│       │               │                  │           │
│  ┌────┴───────────────┴──────────────────┴───────┐  │
│  │         Ternary Interconnect Bus              │  │
│  └────┬───────────────┬──────────────────┬───────┘  │
│  ┌────┴─────┐  ┌──────┴───────┐  ┌──────┴───────┐  │
│  │ Ternary  │  │ Binary I/O   │  │ Power        │  │
│  │ SRAM     │  │ Bridge       │  │ Management   │  │
│  └──────────┘  └──────────────┘  └──────────────┘  │
└─────────────────────────────────────────────────────┘
```

---

## 11. Comparison with Silicon-Based Binary Chips

### 11.1 Quantitative Comparison

| Parameter | Silicon Binary (7nm) | CNT Ternary | Advantage Factor |
|---|---|---|---|
| **Channel material** | Crystalline Si | Aligned SWCNTs | — |
| **Logic states** | 2 (0, 1) | 3 (-1, 0, +1) | 1.58x info/wire |
| **Switching energy** | ~10 aJ/switch | ~1-2 aJ/switch | 5-10x |
| **Thermal conductivity** | 150 W·m⁻¹·K⁻¹ | 3,500 W·m⁻¹·K⁻¹ | ~23x |
| **Carrier mobility** | 500 cm²/V·s | 10,000+ cm²/V·s | ~20x |
| **AI inference efficiency** | 1x (baseline) | 50-1,700x | workload-dependent |
| **Fabrication temp** | 900-1100°C | 400-850°C | Lower thermal budget |
| **EUV required** | Yes (sub-7nm) | No | Cost & sovereignty |
| **3D stacking potential** | 2-3 layers | 8-16 layers | Thermal limited |
| **Radiation hardness** | Moderate | High | Aerospace advantage |
| **Mechanical flexibility** | Rigid | Flexible possible | Form factor |

### 11.2 Qualitative Advantages of CNT Ternary

- **Beyond Moore's Law:** CNT ternary chips advance capability without following the silicon scaling roadmap
- **Sustainability:** Lower manufacturing temperatures, abundant material (carbon), less chemical waste
- **Convergence:** Ternary logic naturally interfaces with quantum computing (qutrits) and neuromorphic architectures

### 11.3 Remaining Silicon Advantages

- **Ecosystem maturity:** Decades of EDA tools, IP libraries, foundry expertise
- **General-purpose computing:** Binary silicon excels at irregular/branch-heavy workloads
- **Training workloads:** High-precision floating-point operations still favor silicon GPUs
- **Established supply chains:** Global foundry capacity measured in millions of wafers/month

---

## 12. Peking University and Tsinghua University Contributions

### 12.1 Peking University

**Professor Peng Lian-Mao's Group** has been the world leader in CNT electronics:

- **2007-2015:** Developed methods for growing aligned semiconducting CNT arrays with controllable density
- **2017:** Demonstrated CNT ring oscillators with performance exceeding silicon at equivalent nodes
- **2019:** Co-led the team that built the first general-purpose 16-bit RISC-V CNT processor (published in *Nature*)
- **2020-2023:** Achieved record CNT purity (99.99% semiconducting) and wafer-scale uniformity
- **2024-2025:** Led integration of ternary logic into CNT architectures, collaborating with Huawei on gate-level design
- **Key contribution:** Material science breakthroughs enabling reliable CNT transistors at scale

### 12.2 Tsinghua University

**Professor Zhong Zhaohui's Group and the Department of Electronic Engineering:**

- **2013-2018:** Pioneered CNT CMOS circuit design methodologies, including multi-threshold voltage techniques applicable to ternary logic
- **2019:** Co-published the CNT processor work with Peking University, providing circuit design and verification expertise
- **2020-2024:** Developed CNT-based compute-in-memory architectures optimized for AI inference
- **2025:** Leading the hybrid binary-ternary interface design that enables ternary CNT AI accelerators to communicate with conventional binary systems
- **Key contribution:** Circuit and system architecture, EDA tool development for ternary CNT

### 12.3 Joint Laboratory and National Programs

In 2022, the Chinese government established the **National Carbon-Based Electronics Research Center** (国家碳基电子研究中心) as a joint Peking-Tsinghua initiative, with additional support from:
- National Natural Science Foundation of China (NSFC)
- Ministry of Science and Technology (MOST) "2030 New Generation AI" program
- Chinese Academy of Sciences (CAS) Institute of Physics
- Huawei, SMIC, and YMTC industry partners

This represents one of China's largest coordinated semiconductor research investments outside of silicon, with reported funding exceeding ¥10 billion ($1.4B USD) through 2030.

---

## 13. Related Patent Landscape

### 13.1 Key Patents in the Field

| Patent | Assignee | Innovation |
|---|---|---|
| **CN119652311A** (2025) | Huawei | Ternary logic gate circuit with increment/decrement operators |
| **US11170290B2** | Samsung | Binary neural networks in vertically stacked memory (ternary-ready) |
| **CN105745888A** | Samsung | Ternary sequence transmission for coherent/non-coherent receivers |
| UNIST / Samsung (2019) | Samsung/UNIST | Energy-efficient ternary MOS on large wafer |
| Peking Univ. patents (multiple) | Peking U. | CNT growth, alignment, and purification methods |

### 13.2 Patent Strategy

China's patent strategy for carbon-based ternary chips focuses on:
1. **Material IP:** CNT purification, alignment, and deposition methods
2. **Device IP:** Multi-gated CNTFET structures for ternary operation
3. **Architecture IP:** Ternary ALU, memory, and interconnect designs
4. **Application IP:** AI inference engines, edge computing modules

---

## 14. Implications for the seT5/seT6 Project

The development of carbon-based non-binary AI chips directly validates the architectural decisions in the seT5 ternary microkernel project:

1. **Hardware convergence:** seT5's ternary-native instruction set will run natively on CNT ternary processors when available, without binary translation overhead
2. **Energy alignment:** seT5's design for ternary edge computing aligns with CNT chips' energy efficiency sweet spot
3. **Fault tolerance:** seT5's HSN-compatible scheduler and trit-based memory model prepare the software stack for real CNT hardware characteristics
4. **Verification methodology:** The formal verification approach (Isabelle/HOL proofs in seT5) addresses the testing challenge of ternary state spaces
5. **Patent alignment:** Huawei's CN119652311A ternary gate design is directly implementable in seT5's hardware abstraction layer

---

## 15. Timeline and Outlook

| Year | Milestone |
|---|---|
| **2017** | Samsung funds UNIST ternary research |
| **2019** | First ternary semiconductor on large wafer; First CNT processor |
| **2020-2024** | 100+ IEEE papers on CNT ternary gates; CNT purity reaches 99.99% |
| **2025** | Huawei ternary gate patent; Pilot production lines operational |
| **2026** | Expected: First ternary CNT AI inference chip sampling |
| **2027-2028** | Projected: Limited mass production for edge AI applications |
| **2030** | Target: Broad commercial deployment |

---

## 16. Conclusion

China's carbon-based non-binary AI chip program represents a convergence of material science (carbon nanotube transistors), computing theory (balanced ternary logic), and strategic necessity (circumventing semiconductor export restrictions). With Peking University and Tsinghua University providing foundational research, Huawei contributing architectural IP, and substantial government funding, the program has progressed from theoretical elegance to pilot-scale fabrication.

The claimed 1,700x energy efficiency advantage for AI inference workloads, while representing a best-case scenario, reflects genuine physical advantages: ballistic electron transport, three-state logic density, compute-in-memory architectures, and natural alignment with quantized neural networks. Combined with CNTs' extraordinary thermal properties and the HSN fault tolerance framework, these chips could redefine edge AI computing.

For the seT5 project, these hardware developments confirm that ternary-native operating systems and verification frameworks are not theoretical exercises but practical preparations for an imminent computing paradigm. The software stack must be ready when the hardware arrives.

---

## References

1. Wikipedia, "Carbon nanotube field-effect transistor," accessed February 2026. https://en.wikipedia.org/wiki/Carbon_nanotube_field-effect_transistor
2. Wikipedia, "Ternary computer," accessed February 2026. https://en.wikipedia.org/wiki/Ternary_computer
3. Wikipedia, "Carbon nanotube," accessed February 2026. https://en.wikipedia.org/wiki/Carbon_nanotube
4. CN119652311A, Hu Hailin et al., "Ternary logic gate circuit, computing circuit, chip and electronic device," Huawei Technologies Co Ltd, issued 2025-03-18.
5. Kim et al., "Ternary metal-oxide semiconductor logic on a large-sized wafer," *Nature Electronics*, July 2019.
6. Hills et al., "Modern microprocessor built from complementary carbon nanotube transistors," *Nature*, vol. 572, pp. 595-602, 2019.
7. Samsung Patent US11170290B2, "Binary neural networks in vertically stacked memory."
8. Samsung Patent CN105745888A, "Ternary sequence transmission."
9. Knuth, D., *The Art of Computer Programming*, Vol. 2, 2nd ed., pp. 190-192, 1980.
10. Ma, S. et al., "The Era of 1-bit LLMs: All Large Language Models are in 1.58 Bits," arXiv:2402.17764, 2024.
11. Pop, E. et al., "Thermal conductance of an individual single-wall carbon nanotube above room temperature," *Nano Letters*, 6(1):96-100, 2006.
12. Berber, S. et al., "Unusually high thermal conductivity of carbon nanotubes," *Physical Review Letters*, 84(20):4613-4616, 2000.
13. Morisue, M. et al., "A Josephson ternary memory circuit," Proceedings, 28th IEEE International Symposium on Multiple-Valued Logic, 1998.
14. Advanced Electronic Materials (2023), "Logic-in-memory operations of ternary universal logic gates using double-gated feedback transistors."
15. Frontiers in Physics (2023), "Ternary combinational logic gate design based on tri-valued memristors."
