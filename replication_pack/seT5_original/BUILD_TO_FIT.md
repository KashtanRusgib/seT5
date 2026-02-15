Design and Evaluation Frameworks for Advanced
RISC-based Ternary Processor
Dongyun Kam, Jung Gyu Min, Jongho Yoon, Sunmean Kim, Seokhyeong Kang and Youngjoo Lee

arXiv:2111.07584v1 [cs.AR] 15 Nov 2021

Department of Electrical Engineering
Pohang University of Science and Technology, Pohang, South Korea
{rkaehddbs,mjg1104,yoonjongho99,sunmean,shkang,youngjoo.lee}@postech.ac.kr

Abstract—In this paper, we introduce the design and verification frameworks for developing a fully-functional emerging
ternary processor. Based on the existing compiling environments
for binary processors, for the given ternary instructions, the
software-level framework provides an efficient way to convert the
given programs to the ternary assembly codes. We also present a
hardware-level framework to rapidly evaluate the performance of
a ternary processor implemented in arbitrary design technology.
As a case study, the fully-functional 9-trit advanced RISC-based
ternary (ART-9) core is newly developed by using the proposed
frameworks. Utilizing 24 custom ternary instructions, the 5-stage
ART-9 prototype architecture is successfully verified by a number
of test programs including dhrystone benchmark in a ternary
domain, achieving the processing efficiency of 57.8 DMIPS/W and
3.06 × 106 DMIPS/W in the FPGA-level ternary-logic emulations
and the emerging CNTFET ternary gates, respectively.
Index Terms—Ternary processor, Instruction set architecture,
RISC, Emerging computer design, Multi-valued logic circuits

I. I NTRODUCTION
The dimensional down-scaling of CMOS technology has
been continuously focused on increasing hardware efficiency
of digital circuits [1]. However, the performance improvement from the recent down-scaling is now expected to meet
the potential limitation especially caused by the increased
interconnecting/routing overheads [2]. Among the different
solutions to address this limitation, the multi-valued logic
(MVL) circuits have been recently gaining great popularity
due to their attractive potential for reducing the circuit-level
complexity as well as the routing burden even at the aggressive
down-scaling technology [3]. For the practical implementation
of the ternary-based system, which is a starting point of MVL
solutions, numerous technologies have been proposed to solve
the stability issue of each voltage/current level with emerging
devices including carbon nanotube FETs (CNTFETs) [4],
graphene barristors [5], and CMOS-based ternary transistors
[6]. In general, the prior studies on ternary circuits mainly
present the potential expectations of gate-level performances
[7], [8]. For circuit-level studies, some digital building blocks
such as adder, multiplier, and flip-flop have been also investigated to extend the concept of gate-level evaluation in ternary
domains [9]–[11]. Due to the lack of systematic designlevel strategies, on the other hand, the system- or processorlevel explorations for ternary-based digital solutions are rarely
reported in the open literature with few details [12].
Identify applicable funding agency here. If none, delete this.

In this work, we introduce advanced design and evaluation
frameworks to realizing ternary processors, measuring actual
performances with the practical benchmark programs. In contrast that the previous studies only present limited concepts to
only test processing blocks in ternary number systems [13],
[14], we develop a 9-trit advanced RISC-based ternary (ART9) core by adopting the proposed frameworks, presenting the
fully-functional top-level ternary microprocessor. Based on
the 9-trit instruction-set architecture (ISA) with 24 custom
ternary instructions, more precisely, the proposed softwarelevel framework provides an efficient way to convert the
existing binary programs to the ternary codes, even reducing
the program size compared to the baseline codes with RV32I ISA [15]. The hardware-level framework offers the cycleaccurate simulator and the technology mapper, providing the
quantitative evaluations of the pipelined ART-9 architecture for
arbitrary design technology. Targeting the specialized 5-stage
pipelined architecture, as a case study, the proposed ART9 core achieves the processing efficiency of 57.8 DMIPs/W
and 3.06 × 106 DMIPs/W when we use the FPGA-level
ternary-logic emulations and the emerging CNTFET-based
ternary gates [7], [8], respectively, reporting the first full-level
evaluations of ternary processors.
II. BACKGROUND
A. Ternary Number Systems
Based on the integrated ternary gates using three voltage
levels such as GND, VDD/2 and VDD, the ternary circuits
are dedicated to the arithmetic operations in a ternary number
system. Like the binary case, there are in general two types
of ternary fixed-point number systems: unsigned and signed
systems. For an n-trit number X = (xn−1 , xn−2 , ..., x0 )3 ,
where xi ∈ {0, 1, 2}, the unsigned ternary number only
represents positive integers from 0 to 3n − 1 by interpreting
an n-trit sequence into a decimal value Yunsigned as follows.
Yunsigned =

n−1
X

xk 3k .

(1)

k=0

Although the unsigned number system is useful for denoting
indices of general-purposed ternary registers (GPTR) and addresses of ternary instruction/data memories (TIM/TDM), it is
obviously required to support the signed arithmetic operations
for performing the general data processing. Therefore, the

Fig. 1. Truth tables of ternary logic operations.
Fig. 2. The proposed software-level compiling framework.

singed ternary number system is considered to interpret the
given n-trit sequence into the negative value. Among different
ways to develop the ternary signed numbers [13], in this work,
we adopt the balanced signed number system, where each trit
is now an element from the balanced set, i.e, xi ∈ {−1, 0, 1}
[13]. Then, a numerical value Ysigned of n-trit ternary number
X is still calculated in the same way as the unsigned representation shown in (1). Compared to the unbalanced approaches
in [13], it is reported that the arithmetic operations in balanced
ternary numbers can be simplified according to the conversionbased negation property [8], [14]. To develop the proposed
frameworks for general-purposed ternary processors, therefore,
the balanced representation is definitely suitable by requiring
fewer ternary gates for the practical realization [8].
B. Ternary-based Arithmetic and Logical Operations
Similar to basic operations of RISC-based binary processors
[15], the ternary processor should support logic and arithmetic
operations to perform the general user-level programs. As
reported in [13], the balanced ternary logic operations include
AND, OR, XOR, standard ternary inverting (STI), negative
ternary inverting (NTI) and positive ternary inverting (PTI),
where the detailed truth tables are exemplified in Fig. 1.
Compared to the familiar two-input logic gates such as AND,
OR, and XOR, note that the inverting operation consists of
three fundamental functions (denoted as STI, NTI, PTI in
Fig. 1), considering as the most important processing in the
balanced ternary number system [13]. It is also possible to
define the proper two-input arithmetic operations, which are
comparable to the well-established functions in the binary
processor [15]. For example, the fundamental functions including ternary addition, comparison, multiplication, and division,
have been extensively studied for the next-generation computer
arithmetic [9], [10], [16]. Utilizing the negation operations
in Fig. 1, it is also possible to simply utilize the ternary
subtraction based on the pre-designed ternary adder [16].
III. P ROPOSED F RAMEWORKS FOR T ERNARY P ROCESSORS
A. Software-Level Compiling Framework
For the full-level ternary processor implementation, based
on a given ternary ISA, it is important to prepare ternary-based
assembly (or executable) programs in an easy way. With the

assistance of the existing RISC-V tool chains in open-source
domains [17], in this work, we first develop a software-level
compiling framework supporting instruction mapping, operand
conversion, and redundancy checking, which can efficiently
generate the ternary assembly benchmarks for arbitrary Cbased source codes. Fig. 2 conceptually illustrates the processing steps of the proposed software-level framework. Note that
the input C-level program is firstly handled by an open-source
compiler for RV-32I ISA, obtaining an assembly sequence
of 32-bit instructions. Then, the instruction mapping step is
activated to translate the 32-bit instructions into pre-defined
ternary instructions. For a binary instruction that cannot be
directly converted with a ternary version, we utilize several
primitive sequences of ternary instructions, still offering valid
mapping results by allowing a few more instructions. After
mapping ternary instructions, the operand conversion step
is followed to find the ternary representations of immediate
values in the baseline binary instructions. Depending on the
definition of ternary instructions, it might be required to add
more instructions to construct the large-sized operands in
ternary number systems. Note that the operand conversion step
also supports the register renaming when the given ternary
ISA uses fewer general-purposed registers than the baseline
binary processor. As the mapping and conversion steps may
utilize additional instructions, the final redundancy checking
phase finds the meaningless instructions by investigating the
duplicated operations, removing them to minimize the overall
code size. During the elimination of redundant instructions, the
proposed framework also re-calculates the branch target addresses to ensure the correct results. As the proposed softwarelevel framework is based on the well-established compiling
environments for binary processors, we can purely focus on
increasing the mapping quality in the ternary domain by deeply
considering the characteristics of ternary instructions, relaxing
the development efforts of ISA-dependent processor-design
frameworks. Targeting the proposed ART-9 ISA, as a case
study, the proposed software-level framework easily generates
various ternary codes with reduced memory requirements,
even saving the program size of dhrystone benchmark by 54%
compared to the baseline processor of RV-32I ISA [15].

TABLE I
S UMMARY OF ART-9 T ERNARY I NSTRUCTIONS
Type

9-trit instructions

Operation

R

MV Ta,Tb
PTI Ta,Tb
NTI Ta,Tb
STI Ta,Tb
AND Ta,Tb
OR Ta,Tb
XOR Ta,Tb
ADD Ta,Tb
SUB Ta,Tb
SR Ta,Tb
SL Ta,Tb
COMP Ta,Tb

TRF[Ta] = TRF[Tb]
TRF[Ta] = PTI(TRF[Tb])
TRF[Ta] = NTI(TRF[Tb])
TRF[Ta] = STI(TRF[Tb])
TRF[Ta] = TRF[Ta] & TRF[Tb]
TRF[Ta] = TRF[Ta] | TRF[Tb]
TRF[Ta] = TRF[Ta] ⊕ TRF[Tb]
TRF[Ta] = TRF[Ta] + TRF[Tb]
TRF[Ta] = TRF[Ta] − TRF[Tb]
TRF[Ta] = TRF[Ta] ≫ TRF[Tb][1:0]
TRF[Ta] = TRF[Ta] ≪ TRF[Tb][1:0]
TRF[Ta] = compare(TRF[Ta],TRF[Tb])

I

ANDI Ta,imm
ADDI Ta,imm
SRI Ta,imm
SLI Ta,imm
LUI Ta,imm
LI Ta,imm

TRF[Ta] = TRF[Ta] & imm[2:0]
TRF[Ta] = TRF[Ta] + imm[2:0]
TRF[Ta] = TRF[Ta] ≫ imm[1:0]
TRF[Ta] = TRF[Ta] ≪ imm[1:0]
TRF[Ta] = {imm[3:0],00000}
TRF[Ta] = {TRF[Ta][8:5],imm[4:0]}

B

BEQ Ta,B,imm
BNE Ta,B,imm
JAL Ta,imm
JALR Ta,Tb,imm

PC = PC + imm[3:0] if TRF[Tb][0] == B
PC = PC + imm[3:0] if TRF[Tb][0] != B
TRF[Ta] = PC+1, PC = PC + imm[4:0]
TRF[Ta] = PC+1, PC = TRF[Tb]+imm[2:0]

M

LOAD Ta,Tb,imm
STORE Ta,Tb,imm

TRF[Ta] = TDM[TRF[Tb]+imm[2:0]
TDM[TRF[Tb]+imm[2:0]] = TRF[Ta]

Fig. 3. The proposed hardware-level evaluation frameworks.

B. Hardware-Level Evaluation Framework
Using ternary assembly codes, which can be obtained by the
proposed software-level compiling framework, we develop the
hardware-level evaluation framework allowing an efficient way
to develop the prototype of ternary processor. As illustrated in
Fig. 3, the hardware-level framework includes a cycle-accurate
simulator, a gate-level analyzer, and a performance estimator.
The cycle-accurate simulator accepts the high-level description
of the pipelined ternary processor, and provides the required
processing cycles for performing the input ternary assembly
codes. With the synthesizable RTL design corresponding to
the high-level architecture description, the proposed gatelevel analyzer can estimate the critical delay as well as the
power consumption of ternary processor. Note that we define
the property description of the design technology as another
input of gate-level analyzer, which includes delay and power
characteristics of primitive building blocks, enabling more
accurate analysis results depending on the target technology.
As depicted in Fig. 3, the performance estimator gathers all
the outputs from prior steps, and finally generates the overall
evaluation information of the ternary processor implemented
in certain design technology. By utilizing multiple evaluation
steps and even considering the technology-oriented information, before starting the actual implementation phase with predesigned peripherals, we can remarkably reduce the design
efforts of the custom ternary processor with the proposed
hardware-level evaluation framework.
IV. ART-9 C ORE D ESIGN FOR P ROPOSED F RAMEWORKS
A. ART-9 Instruction Set Architecture
Based on the balanced ternary number systems, the proposed ART-9 processor defines 9-trit-length ISA following the
properties of contemporary RISC-type binary processors [15].
Table I summarizes 24 ART-9 ternary instructions processing
9-trit data values, which are the essential inputs at the proposed
software-level compiling framework. By matching the word
length of both instruction and data, we can allow the regular
structure for realizing TIM and TDM. To fetch an instruction
by accessing the TIM, we use a special-purposed 9-trit register,
i.e., the program counter (PC) register containing the instruction address. In order to store the intermediate data, like the

modern processor architectures [15], [18], the ART-9 core also
includes a ternary registerfile (TRF) including nine generalpurposed registers, each of which is accessed by using a 2trit value. Utilizing the load-store architecture used for typical
RISC processors [19], there are four instruction categories in
ART-9 ISA; R-type, I-type, B-type, and M-type.
For the R-type instructions, considering the recent studies
[20], we select essential 12 logical/arithmetic functions as
depicted in Table I. In fact, most R-type instructions are typical
two-address instructions, which fetch two 9-trit operands in
TRF, whose 2-trit indices are denoted as Ta and Tb, and
then overwrite a 9-trit result to the register TRF[Ta]. Note
that some R-type instructions specialized for inversion and
data-movement operations use only one source operand from
Tb, where the destination operand is still Ta to have the
regular encoding patterns, relaxing the complexity to decode
the fetched instruction. In addition, we also realize an R-type
comparison instruction (COMP), where the least significant
trit (LST) of the destination register TRF[Ta] denotes the
comparison result of two input operands with the dedicated
function compare() in Table I. More specifically, the LST of
TRF[Ta] is set to be zero when the two inputs are the same,
otherwise it becomes +1 (or −1) if TRF[Ta] > TRF[Tb]
(or TRF[Ta] < TRF[Tb]). This COMP instruction plays an
important role to improve the code density by allowing the
conditional execution of the following branch instructions.

Fig. 4. 5-stage pipelined architecture of the proposed ART-9 processor.

In order to reduce the generation complexity of constant
values, the technique to encode immediate values into the
instruction is generally used for reducing the size of userlevel programs [15], [18]. The proposed ART-9 processor also
supports immediate-based processing with I-type instructions.
As described in Table I, unlike the R-type instructions offering
various functions, we only allow immediate values at addition,
AND logic, and shift functions, which are known to be the
most common operations in practice [20]. Due to the limited
trit-width for denoting an embedded immediate, there could be
extra overheads to realizing full-length (9-trit) constant values.
Instead of utilizing a series of the shift-and-addition process to
store a 5-trit immediate value initialized by a load immediate
(LI) instruction, we adopt a special I-type instruction named
load upper immediate (LUI), which is introduced at the RISCtype processors for making a large-sized constant value [15],
[18]. As a result, the ART-9 ISA offers an acceptable flexibility
to use wide ranges of immediate values, suitable for the
resource-limited processing environments.
Besides the logical/arithmetic instructions, it is also required
to define the branch-related instructions changing the PC
value, which is denoted as B-type instructions in Table I. In the
proposed ART-9 cores, we introduce four B-type instructions
including two conditional branch operations associated with
the PC-relative addressing, which are referred to as BEQ
and BNE as shown in Table I. To utilize these conditional
operations, as described earlier, we preset the LST of TRF[Tb]
in BEQ or BNE by using a COMP instruction, so that a 1-trit B
value in BEQ or BNE is compared to check the branch-taken
condition. In addition, we define two unconditional jump-andlink instructions (JAL and JALR), which are mainly used

for the subroutine calls. Adopting the PC-relative addressing,
similar to the conditional branches, the JAL instruction uses
the PC value as a base address added by a 5-trit immediate.
On the other hand, by using the JALR instruction, we can use
the stored 9-trit value in TRF to set the base address with a
small-sized 3-trit immediate, allowing more long-range jumps.
As depicted in Table I, note that this base-register addressing is
also used to access TDM with M-type load/store instructions,
reducing the hardware complexity with the shared datapath.
B. 5-stage Pipelined ART-9 Architecture
To support the proposed ART-9 ISA efficiently, we develop
in this work a simple but efficient pipelined architecture, which
is used for input descriptions of the proposed hardware-level
evaluation framework. As shown in Fig. 4, similar to the
lightweight RISC-type designs [19], there are five stages for
fetching the instruction from TIM (IF), decoding the fetched
instruction (ID), executing the arithmetic/logical operations
(EX), accessing the TDM (MEM), and updating the result
to TRF (WB). The ternary pipelined registers are newly
developed to keep the results from each stage, making a balanced pipelined processing. We also introduce the synchronous
single-port TIM and TDM designs for reducing the memoryaccessing latency, where the TRF in this work supports two
asynchronous read ports and one synchronous write port. The
ternary arithmetic logic unit (TALU) in EX stage is specialized
to perform various operations depending on the control signals
from main decoder in ID stage. In the pipelined ART-9 core,
the hazard detection unit (HDU) in ID stage compares the
adjacent instructions to determine the generation of hardwarelevel stall controls at the run time. For reducing the number

TABLE II
S IMULATION R ESULTS OF D HRYSTONE B ENCHMARK
This work

VexRiscv [24] PicoRV32 [25]

ISA Architecture

ART-9 ISA

RV-32I

RV-32IM

# of instructions

24

40

48

Pipelined stages

5

5

1

Multiplier

X

O

O

DMIPS/MHz

0.42

# of memory-cells 11.6K trits

0.65

0.31

25.4K bits

23.7K bits

TABLE III
P ROCESSING C YCLES FOR D IFFERENT T EST P ROGRAMS
Fig. 5. The number of memory cells for storing benchmark programs.
Bubble sort GEMM Sobel filter Dhrystone

of unwanted stalls as many as possible, we actively apply
the forwarding multiplexers to get the correct 9-trit inputs
at TALU, solving ALU-use data hazards. To minimize the
number of stalls from B-type instructions causing control
hazards, the pipelined ART-9 processor utilizes the dedicated
branch-target calculator as well as the condition checker in
ID stage, directly forwarding the calculated address to update
the PC register. For checking the branch-taken conditions, in
addition, forwarding one-trit values successfully mitigates the
long and complex datapath starting from TRF, still allowing
one-cycle stall after B-type instructions without increasing
the overall critical delay. As a result, we only observe the
hardware-inserted stall cycles when there exist load-use data
hazards and taken branches. After detecting the stall insertion
case, the main decoder at ID stage generates a stall control
signal, which will be used for selecting the no-operation
(NOP) at the next ID stage as shown in Fig. 4. Without
introducing a dedicated NOP encoding, note that the proposed
ART-9 ISA uses an ADDI instruction to denote the NOP
operation with a zero-valued immediate.
V. E VALUATION AND I MPLEMENTATION R ESULTS
A. Benchmark Evaluations
By using the proposed compiling framework, targeting the
ART-9 ISA shown in Table I, we designed several ternary
benchmark programs including the general computing algorithms; bubble sort, general matrix multiplication (GEMM),
and sobel filter [21], [22]. In addition, for the first time,
a dhrystone benchmark is also described with the ternary
instructions by converting the existing dhrystone code of
the RV-32I ISA, which is popularly used for evaluating the
computing performance of general-purposed CPU cores [23].
Fig. 5 depicts the effectiveness of the proposed ART-9 ISA
by evaluating the required memory size for storing each
benchmark program, showing that the proposed softwarelevel framework offers acceptable assembly codes compared
to the binary versions. Note that we counted the number of
memory cells for this comparison, as the ternary instructions
necessitate the dedicated ternary memory where a storing
cell can keep up to three different charge distributions [11].

This work

2,432

10,748

7,822

134,200

PicoRV32 [25]

9,227

11,290

18,250

186,607

Although we developed a simple 9-trit ISA including only
24 instructions, it is clear that the proposed ART-9 processor
requires a much smaller memory size when compared to the
binary counterparts; RV-32I using 32-bit instructions [15] and
ARMv6M with 16-bit instructions [18]. If we consider implementation results of dhrystone codes, due to the short-length
ternary instructions associated with the efficient software-level
framework, for example, our ART-9 core reduces the number
of required memory cells by 54% and 17% when compared to
the RV-32I [15] and ARMv6M [18] processors, respectively.
In other words, there exist reasonable benefits of exploiting
the ternary number systems, which can reduce the memory
overheads while providing a similar amount of flexibility to
binary ISAs with long-length instructions.
B. Hardware-level Evaluation Results
Table II precisely shows evaluation results of the cycleaccurate simulator of different RISC-based processors running
the dhrystone benchmark. Note that our ART-9 core achieves
0.42 DMIPS/MHz by utilizing only 24 instructions, whereas
the fully-optimized VexRiscv [24] and PicoRV32 [25] processor provides 0.65 and 0.31 DMIPS/MHz with more instructions and the dedicated multiplier, respectively. Utilizing the
optimized codes from the proposed compiling frameworks, the
prototype ART-9 core can be designed with the comparable
processing speed and much smaller size of memory cells. In
addition, Table III also shows that the proposed compiling
framework efficiently optimizes the number of instructions for
the other benchmarks. As it is considered that the memory in
general dominates the overall system complexity, the prototype
ART-9 core offers the low-complexity computing platform
even compared to the recent lightweight PicoRV32 processor
with non-pipelined architecture. In other words, the optimized
ART-9 ISA and processor, which utilize the proposed frameworks, successfully offer a reasonable solution achieving both
the fast computing and the low hardware-cost, presenting the
fully-functional processor design in the ternary domain.

TABLE IV
I MPLEMENTATION R ESULTS USING CNTFET T ERNARY G ATES
Voltage

Total gates

Power

DMIPS/W

0.9V

652

42.7 µW

3.06 × 106

TABLE V
I MPLEMENTATION R ESULTS USING FPGA- BASED T ERNARY L OGICS
Voltage

Frequency

ALMs

Registers

RAM

Power

0.9V

150MHz

803

339

9,216 bits

1.09W

Using the proposed gate-level analyzer, we finally present
implementation results of ART-9 prototypes. For the simplified
32nm CNTFET ternary models without considering the parasitic capacitance [8], we first estimated the gate-level costs
of the 5-stage pipelined core as shown in Table IV. The
datapath of ART-9 core only required 652 standard ternary
gates, consuming 42.7 µW when the operating voltage is set to
0.9 V. According to the dhrystone result shown in Table II, the
CNTFET-based ART-9 core achieves 3.06 × 106 DMIPS/W,
showing that the emerging ternary device leads to the lowpower microprocessor, even superior to the near-threshold
ARM Cortex-M3 design requiring 3.9 × 103 DMIPS/W [26].
In order to validate the proposed ternary processor, we
also implemented the ART-9 core in the FPGA-based verification platform. For the practical implementation, all the
ternary-based building blocks are emulated with the binary
modules, adopting the binary-encoded ternary number system
[27]. Table V summarizes the implementation results of the
binary-encoded ART-9 core, which utilizes only few hardware
resources of Intel Stratix-V FPGA at the operating frequency
of 150 MHz. Targeting the dhrystone benchmark, the FPGAbased ART-9 core achieves 57.8 DMIPS/W by consuming
1.09W including two binary-encoded ternary memories. As
a result, the proposed frameworks successfully opens the
preliminary results for realizing the ternary-based processor,
which can be easily mapped to the future emerging ternary
devices for allowing the extreme-low-power computing.
VI. C ONCLUSION
In this paper, we have proposed several designs and evaluation frameworks for developing ternary microprocessors,
which are verified by the lightweight RISC-based ternary
processor with 9-trit datapath. Based on the balanced ternary
number system, the proposed software-level framework efficiently supports a systematic way to construct assembly codes
for the given ternary ISA. Accepting the architecture-aware
descriptions as well as the target technology information, the
hardware-level framework is then followed to estimate several
implementation-aware metrics, reducing the overall design
overheads in the ternary number system. Based on the proposed frameworks, the fully-functional ART-9 microprocessor
is developed and verified at different emerging technologies,
offering attractive design methods for ternary processors.

R EFERENCES
[1] G. Yeap, “Smart mobile SoCs driving the semiconductor industry:
Technology trend, challenges and opportunities,” in IEDM Tech. Dig.,
Dec. 2013, pp. 1–3.
[2] N. Magen, A. Kolodny, U. Weiser, and N. Shamir, “Interconnect-power
dissipation in a microprocessor,” in Proc. Int. Workshop Syst, Level
Interconnect Predict., 2004, pp. 7–13.
[3] V. Gaudet, “A survey and tutorial on contemporary aspects of multiplevalued logic and its application to microelectronic circuits,” IEEE J.
Emerg. Sel. Topics Circuits Syst., vol. 6, no. 1, pp. 5–12, 2016.
[4] S. Lin, Y.-B. Kim, and F. Lombardi, “A novel CNTFET-based ternary
logic gate design,” in Proc. IEEE Int. Midwest Symp. Circuits Syst., Aug.
2009, pp. 435–438.
[5] H. Yang et al., “Graphene barristor, a triode device with a gate-controlled
schottky barrier,” Science, vol. 336, no. 6085, pp. 1140–1143, 2012.
[6] S. Shin, E. Jang, J. W. Jeong, B.-G. Park, and K. R. Kim, “Compact
design of low power standard ternary inverter based on OFF-state current mechanism using nano-CMOS technology,” IEEE Trans. Electron
Devices, vol. 62, no. 8, pp. 2396–2403, 2015.
[7] S. Kim, T. Lim, and S. Kang, “An optimal gate design for the synthesis
of ternary logic circuits,” in Proc. 23rd Asia South Pacific Design
Automat. Conf. (ASP-DAC), Jan. 2018, pp. 476–481.
[8] S. Kim, S.-Y. Lee, S. Park, K. R. Kim, and S. Kang, “A logic synthesis
methodology for low-power ternary logic circuits,” IEEE Trans. Circuits
Syst. I, Reg. Papers, vol. 67, no. 9, pp. 3138–3151, 2020.
[9] S. Heo et al., “Ternary full adder using multi-threshold voltage graphene
barristors,” IEEE Electron Device Lett., vol. 39, no. 12, pp. 1948–1951,
Dec. 2018.
[10] Y. Kang et al., “A novel ternary multiplier based on ternary cmos
compact model,” in Proc. IEEE 47th Int. Symp. Multiple-Valued Log.
(ISMVL), May. 2017, pp. 25–30.
[11] Y. Choi, S. Kim, K. Lee, and S. Kang, “Design and Analysis of a LowPower Ternary SRAM,” in Proc. IEEE Int. Symp. Circuits Syst. (ISCAS),
Apr. 2021, pp. 1–4.
[12] “Ternary computer system,” Accessed on: Sep. 17, 2021. [Online].
Available: https://www.ternary-computing.com
[13] “The trillium architecture,” Accessed on: Sep. 17, 2021. [Online]. Available: https://homepage.divms.uiowa.edu/~jones/ternary/trillium.shtml
[14] S. Narkhede, G. Kharate, and B. Chaudhari, “Design and implementation
of an efficient instruction set for ternary processor,” International
Journal of Computer Applications, vol. 83, no. 16, 2013.
[15] A. Waterman, Y. Lee, D. A. Patterson, and K. Asanović, “The RISC-V
Instruction Set Manual, Volume I: User-Level ISA, Version 2.1,” 2016.
[Online]. Available: https://riscv.org/specifications/
[16] B. Parhami and M. McKeown, “Arithmetic with binary-encoded balanced ternary numbers,” in Proc. Asilomar Conf. Signals, Systems and
Computers, 2013, pp. 1130–1133.
[17] G. Tagliavini, S. Mach, D. Rossi, A. Marongiu, and L. Benini, “Design
and Evaluation of Small Float SIMD extensions to the RISC-V ISA,”
in Proc. of the Design, Automat. Test Eur. (DATE), 2019, pp. 654–657.
[18] J. Yiu, The Definitive Guide to ARM Cortex-M0 and Cortex-M0+
Processors. 2nd ed. Boca Raton, FL, USA: Academic, 2015.
[19] F. Schuiki et al., “Stream semantic registers: A lightweight RISC-V ISA
extension achieving full compute utilization in single-issue cores,” IEEE
Trans. Comput., vol. 70, no. 2, pp. 212–227, 2020.
[20] P. Li, “Reduce Static Code Size and Improve RISC-V Compression,”
Master’s thesis. EECS Department, Univ. of California, Berkeley, 2019.
[21] Y. Wang et al., “A compression-based area-efficient recovery architecture
for nonvolatile processors,” in Proc. of the Design, Automat. Test Eur.
(DATE), 2012, pp. 1519–1524.
[22] A. Zulehner and R. Wille, “Matrix-vector vs. Matrix-matrix multiplication: Potential in DD-based simulation of quantum computations,” in
Proc. of the Design, Automat. Test Eur. (DATE), 2019, pp. 90–95.
[23] R. York, “Benchmarking in context: Dhrystone,” ARM, March, 2002.
[24] “Vexriscv,” Accessed on: Sep. 17, 2021. [Online]. Available:
https://github.com/SpinalHDL/VexRiscv
[25] “Picorv32,” Accessed on: Sep. 17, 2021. [Online]. Available:
https://github.com/cliffordwolf/picorv32
[26] R. G. Dreslinski et al., “Centip3de: A 64-core, 3d stacked near-threshold
system,” IEEE Micro, vol. 33, no. 2, pp. 8–16, 2013.
[27] G. Frieder and C. Luk, “Algorithms for binary coded balanced and
ordinary ternary operations,” IEEE Trans. Comput., vol. 100, no. 2, pp.
212–215, 1975.

Posted on 6 Feb 2026 — CC-BY 4.0 — https://doi.org/10.36227/techrxiv.177039671.14012313/v1 — e-Prints posted on TechRxiv are preliminary reports that are not peer reviewed. They should not b...

Christopher Riner1

1

Affiliation not available

February 06, 2026

1

1

Wavelength-Division Ternary Logic: Bypassing the
Radix Economy Penalty in Optical Computing
Christopher Riner

Abstract—Ternary (base-3) logic is mathematically optimal for
computing systems, lying closest to Euler’s number e in the radix
economy calculation. However, ternary computing has remained
impractical due to the substantial hardware overhead required
to distinguish three stable states using transistor-based circuits—
typically requiring 40× more transistors per trit compared to
bits. We propose a novel architecture for ternary optical computing based on wavelength-selection encoding with external wavelength sources. Unlike existing polarization-based or intensitybased approaches, our architecture treats wavelengths as analogous to voltage rails in analog computers, where external laser
sources provide discrete wavelength inputs (e.g., λ1 , λ2 , λ3 ) and
internal optical components perform wavelength-selective routing
and logic operations. This approach fundamentally bypasses the
radix economy penalty because wavelength differentiation cost
is independent of the number of states, unlike transistor-based
implementations where cost scales with radix. We show that
this architecture could unlock the full 1.58× information density
advantage of ternary logic while leveraging the inherent speed,
parallelism, and low-power characteristics of photonic systems.
This work presents the theoretical foundation and architectural
principles for wavelength-encoded ternary optical computing and
identifies key challenges for experimental realization.
Index Terms—Ternary computing, optical computing, wavelength division, radix economy, photonic logic, multi-valued logic

I. I NTRODUCTION
A. The Ternary Computing Paradox
Ternary (base-3) computing systems have been recognized
since the 1950s as mathematically superior to binary systems.
The optimal radix for representing information with minimal
hardware cost is Euler’s number e ≈ 2.718, and base-3 is
the closest integer radix to this optimum [1], [2]. Despite this
theoretical advantage, ternary computers have been relegated
to historical curiosities while binary computing has dominated
for over seven decades.
The reason for this paradox is straightforward: with
transistor-based digital electronics, implementing a stable
three-state element (trit) requires approximately 40 transistors,
compared to just 1 transistor for a binary bit [3]. This 40×
hardware overhead completely eliminates any theoretical advantage from ternary’s superior information density. The very
mathematical property that makes ternary optimal—having
three states per digit—becomes a liability when the physical
cost of distinguishing states scales with the number of states.
Independent Researcher:
riner45@gmail.com

Chesapeake,

VA,

US.

Email:

chris-

B. The Promise of Optical Computing
Photonic computing has emerged as a potential paradigm
shift for information processing, offering advantages in speed
(light propagates faster than electrons), parallelism (wavelength division multiplexing), and power efficiency (reduced
heat dissipation) [4], [5]. While most optical computing research focuses on binary logic operations, photons possess
natural properties that can encode multiple states without the
hardware penalties of transistor-based systems:
• Polarization: Multiple orientations (linear, circular)
• Wavelength: Discrete frequency channels
• Intensity: Amplitude levels
• Phase: Wave timing offsets
Existing research in optical ternary computing has primarily
exploited polarization states [6], [7] or intensity levels [8] to
encode ternary values. However, these approaches have not
fully addressed the fundamental question: Can optical ternary
computing bypass the radix economy penalty that dooms
transistor-based ternary systems?
C. Our Contribution
We propose a novel architecture for ternary optical computing based on wavelength-selection encoding with external
wavelength sources. The key architectural innovation is to
separate the complexity of wavelength generation from the
logic processing itself, treating wavelengths as externallysupplied resources analogous to voltage rails in analog computers.
Our specific contributions are:
1) Novel encoding scheme: Use wavelength selection (choosing ONE of N wavelengths) rather than
wavelength-division multiplexing (using N wavelengths
simultaneously) or polarization states
2) External source architecture: Generate wavelengths
outside the computing fabric, with internal components performing only wavelength-selective routing and
switching
3) Theoretical analysis: Show that wavelength-based differentiation has constant cost independent of radix,
fundamentally bypassing the traditional radix economy
penalty
4) Comparison framework: Contrast with existing
polarization-based and intensity-based optical ternary
approaches
We demonstrate that this architecture could, in principle,
unlock the full 1.58× information density advantage of ternary

2

logic while avoiding the hardware penalties that have historically prevented ternary computing from practical realization.
II. BACKGROUND
A. Radix Economy and the Optimality of Base-3
The concept of radix economy addresses the question:
What number base minimizes the total hardware cost for
representing numbers? This was formalized mathematically by
considering two competing factors:
1) Higher radix: Fewer digits needed to represent a number (proportional to logr (N ))
2) Higher radix: More complex hardware per digit (proportional to r)
The total cost can be expressed as:
Cost(r) = r × logr (N )

(1)

Converting to natural logarithm:
Cost(r) = r ×

ln(N )
ln(r)

(2)

To minimize, we take the derivative with respect to r and
set to zero:


d
r
ln(r) − 1
=
=0
(3)
dr ln(r)
[ln(r)]2
Solving: ln(r) = 1, therefore r = e ≈ 2.718.
This proves mathematically that the optimal radix is Euler’s
number e [2]. Since we cannot build a base-2.718 computer,
we evaluate integer radices:
• Base-2: Cost = 2.885
• Base-3: Cost = 2.730 (closest to optimal!)
• Base-4: Cost = 4.000
• Base-5: Cost = 4.308
Base-3 provides approximately 5.4% better hardware
economy than binary. Additionally, each ternary digit (trit)
carries:
Information per trit = log2 (3) ≈ 1.585 bits

(4)

This represents a 58% information density improvement
per digit compared to binary.
B. Why Ternary Failed with Transistors
The radix economy calculation assumes that the cost per
digit scales linearly with the radix (i.e., a trit costs 3× what a
bit costs). However, in transistor-based digital electronics, this
assumption dramatically underestimates the true cost.
Creating a stable three-state digital element requires:
• Voltage level discrimination circuits (distinguishing, e.g.,
0V vs 2.5V vs 5V)
• Noise margin maintenance
• Signal regeneration (preventing degradation through cascaded gates)
• Level shifting and buffering
These requirements result in approximately 40 transistors
per trit compared to 1 transistor per bit [3]. At this hardware
ratio, the radix economy calculation becomes:

40 transistors/trit
÷ 1.585 bits/trit ≈ 25×
1 transistor/bit
(5)
Far from being 5.4% more efficient, transistor-based ternary
is approximately 25× worse than binary. This is why ternary
computing failed commercially despite its mathematical elegance.
Actual cost ratio =

C. Existing Optical Ternary Computing Approaches
Previous research in optical ternary computing has explored
several encoding schemes:
Polarization-based encoding [6], [7], [9]: Uses three polarization states. Notable work includes the Chinese Ternary
Optical Computer project (Yi Jin et al., 2003-present) which
has built experimental prototypes.
Intensity-based encoding [8]: Uses three brightness levels
but suffers from analog-like problems (noise, degradation,
threshold sensitivity).
Multi-valued frequency encoding [10]: Uses different
wavelengths for multi-valued logic gates, focused on reversible
computing rather than ternary state encoding.
None of these approaches have systematically addressed
whether the per-state hardware cost can be made independent
of radix, thereby bypassing the radix economy penalty.
III. P ROPOSED A RCHITECTURE
A. Core Concept
Our architecture is based on two key principles:
1) Wavelength-selection encoding: A ternary state is represented by a discrete wavelength channel. To execute a
logic operation, the system selects two distinct wavelengths from the available set to drive the nonlinear
mixer.
• State -1: λ1 (Red, 1.55 µm)
• State 0: λ2 (Green, 1.30 µm)
• State 1: λ3 (Blue, 1.00 µm)
This balanced ternary representation ({−1, 0, 1}) enables direct subtraction without sign bits, a significant
architectural advantage over binary systems.
2) External wavelength sources: Wavelengths are generated externally and supplied to the computing fabric,
analogous to voltage rails in analog computers
B. System Architecture
The complete system consists of three layers (see Fig. 1):
Wavelength Source Layer (External): Rather than using
multiple independent lasers, we employ a single continuouswave pump laser coupled to a Kerr micro-resonator to generate
a frequency comb. This broadband comb is then demultiplexed
by an Arrayed Waveguide Grating (AWG) to provide the
discrete logic wavelengths (λ1 = 1.55µm, λ2 = 1.30µm,
λ3 = 1.00µm). This approach ensures phase coherence and
scalability.
Logic Processing Layer (Internal): Wavelength-selective
switches (ring resonators) gate the specific input wavelengths

3

based on control voltages. These selected signals are then
routed to a Sum-Frequency Generation (SFG) mixer.
Detection Layer (Outputs): The nonlinear mixing product
(λsum ) is filtered and detected by a photodiode, providing a
unique spectral signature for each logic state combination.

Therefore, the effective cost model becomes:
Costwavelength ≈ Cswitch + Cdemux /fanout

(6)

where Cswitch is approximately constant regardless of radix.
This allows us to achieve the information density benefit
(1.58× for ternary) without paying the r-proportional hardware penalty.
B. Information Density Advantage
Each wavelength-encoded trit carries:
Itrit = log2 (3) ≈ 1.585 bits

Fig. 1. System architecture for wavelength-encoded ternary optical computing. A single pump laser and Kerr comb generator create a broadband
spectrum, which is demultiplexed by an AWG to provide the discrete
wavelengths. Selectors gate the signals, and a nonlinear mixer generates the
logic result.

(7)

For a system with N optical paths (waveguides):
• Binary wavelength encoding: N × 1 bit = N bits
• Ternary wavelength encoding: N × 1.585 bits = 1.585N
bits
This represents 58% more information through the same
number of physical channels.
C. Arithmetic Simplification via Balanced Ternary

C. Ternary State Encoding
Figure 2 illustrates the wavelength-selection encoding
scheme where each ternary state (-1, 0, 1) is represented
by a single discrete wavelength. Only one wavelength is
present at a time in each optical channel, ensuring digitallike discrete states rather than analog intensity variations.
To perform logic operations (e.g., addition, subtraction), the
Selector layer actively routes two distinct wavelengths from
the three available states into a specific waveguide path. This
path leads to a nonlinear mixer configured for that specific
operation, effectively converting the spectral combination into
a new output wavelength representing the result.

A distinct advantage of the proposed balanced ternary system (states {−1, 0, 1}) over unbalanced ternary ({0, 1, 2}) is
the simplification of arithmetic operations. In balanced ternary,
the negative of a number is obtained by simply inverting each
trit (1 → −1, −1 → 1), allowing subtraction to be performed
using the same adder logic as addition. This architectural
symmetry eliminates the need for separate subtraction circuits
or sign bits (as required in binary two’s complement), further
reducing the component count and latency of arithmetic logic
units (ALUs).

Fig. 2. Ternary state encoding using wavelength selection. Each ternary state
is represented by a single wavelength: State -1 (Red, 1.55 µm), State 0 (Green,
1.30 µm), and State 1 (Blue, 1.00 µm).

IV. T HEORETICAL A NALYSIS
A. Breaking the Radix Economy Penalty
The traditional radix economy formula assumes cost ∝ r
(cost scales with number of states). This assumption holds for
transistor-based systems where distinguishing r states requires
r-proportional circuitry.
In wavelength-selection systems, a wavelength-selective
switch (e.g., ring resonator) has similar complexity whether
switching between 2, 3, or 4 wavelengths. The cost growth is
approximately constant per switch, not proportional to r.

Fig. 3. Radix economy analysis showing r/ ln(r) as a function of radix.
Base-3 (ternary) achieves the minimum at 2.730, closest to the theoretical
optimum at e ≈ 2.718.

D. Comparison to Polarization-Based Encoding
Figure 4 compares wavelength encoding with existing approaches. Wavelength encoding offers advantages in scalability
and component maturity due to the established wavelength
division multiplexing (WDM) technology from telecommunications.

4

VI. R ESULTS AND D ISCUSSION

Fig. 4. Comparison of ternary computing implementations. Wavelength-based
encoding bypasses the radix economy penalty while offering advantages in
scalability and component maturity.

V. S IMULATION M ETHODOLOGY
A. Computational Framework
The photonic logic gates were simulated using the FiniteDifference Time-Domain (FDTD) method via the opensource software package Meep (v1.25.0) [11]. The simulations
were performed in a two-dimensional (2D) computational
domain, assuming invariance in the z-direction (∂/∂z = 0),
to model the TE-polarized (Ez ) light propagation in planar
waveguide structures.
B. Simulation Parameters
1) Domain & Discretization: A spatial resolution of 25
pixels/µm was employed, corresponding to a grid spacing of
∆x = 40 nm. This ensures sufficient sampling of the shortest
operational wavelength (λsum ≈ 0.56µm). Perfectly Matched
Layers (PML) with a thickness of 1.0 µm were applied at all
domain boundaries to simulate an open system.

While the proposed architecture relies on established components such as pump lasers, Kerr micro-resonators, and
AWGs for signal generation and routing, the novel core ternary
logic operation depends entirely on the nonlinear mixing
process. Consequently, our numerical validation focused exclusively on the Sum-Frequency Generation (SFG) mixer, as
this represents the unique logic gate element where the ternary
states interact to produce a computational result.
The Sum Frequency Generation (SFG) mixer was evaluated for all three pairwise combinations of the ternary input
states. The transmitted power flux was measured at the output
waveguide.

A. Mixing Efficiency
Table I summarizes the conversion efficiency for the optimized waveguide geometry (w = 1.1µm). The highest efficiency (4.57%) was observed for the Blue+Green combination,
while the Red+Blue combination yielded 0.73%.
TABLE I
S IMULATION R ESULTS FOR T ERNARY L OGIC M IXING
Input Combinations

Target Sum

Efficiency*

Signal Quality

Blue (1.00) + Green (1.30)
0.5652 µm
4.57%
Excellent
Red (1.55) + Blue (1.00)
0.6078 µm
0.73%
Good
Red (1.55) + Green (1.30)
0.7070 µm
0.40%
Adequate
*Efficiency calculated as Psum /(Pin1 + Pin2 ).

B. Feasibility Analysis

Fig. 5. FDTD simulation domain setup illustrating the input plane, nonlinear
waveguide geometry (w = 1.1µm), and output flux measurement plane.
The 18 µm length ensures sufficient interaction length for sum-frequency
generation.

2) Material Properties: The linear regions of the photonic
circuit were modeled as generic high-index waveguides (n =
2.2) with a width of w = 1.1µm, representing an optimized
Lithium Niobate (LiNbO3 ) geometry for phase matching. For
the mixing region, a second-order nonlinear susceptibility χ(2)
was introduced to enable Sum Frequency Generation (SFG),
with a normalized parameter of 0.5 (Meep units).
3) Sources: Gaussian-profiled Continuous Wave (CW)
sources were used to inject signals with a fractional bandwidth
of df /f = 0.05. The ternary states were defined as:
• Logic -1 (Red): λ = 1.55µm (C-Band Telecom)
• Logic 0 (Green): λ = 1.30µm (O-Band Telecom)
• Logic 1 (Blue): λ = 1.00µm

The lowest observed efficiency (0.40% for Red+Green)
represents the marginal case. Assuming standard on-chip laser
sources with 1 mW (0 dBm) input power, the generated sumfrequency signal would be -24 dBm (4.0 µW). This is above
the noise floor of standard Germanium photodiodes (typically 30 dBm). Furthermore, since SFG is a nonlinear process where
Psum ∝ P1 P2 , the output signal strength can be scaled by
increasing input power to 10 mW, ensuring robust detection.

Fig. 6. Spectral output of the mixer for Blue (1.0 µm) and Green (1.3 µm)
inputs, showing a strong sum-frequency peak at 0.565 µm.

5

VII. C ONCLUSION
We have presented a novel architecture for ternary optical
computing based on wavelength-selection encoding. Theoretical analysis confirms that this approach bypasses the radix
economy penalty. Numerical validation via FDTD simulations
demonstrates that nonlinear mixing can successfully generate
unique output signatures for all logic state combinations, with
conversion efficiencies sufficient for detection by standard
photodiodes. The failure of ternary computing was not a failure
of mathematics, but a mismatch between mathematical optimality and physical implementation constraints. Wavelengthencoded photonics provides the physical substrate to finally
realize this optimality.
ACKNOWLEDGMENT
The novel ternary logic architecture, including the specific
configuration of ring-resonator selectors and sum-frequency
generation mixers, was conceived by the authors. An AI
coding assistant (Google Gemini-3-Pro-Preview) was utilized
solely for the implementation of the Python simulation scripts
based on the authors’ specified design parameters and physics
requirements.
R EFERENCES
[1] D. E. Knuth, The Art of Computer Programming, Volume 2: Seminumerical Algorithms, 2nd ed. Addison-Wesley, 1981.
[2] B. Hayes, “Third base,” American Scientist, vol. 89, no. 6, pp. 490–494,
2001.
[3] S. L. Hurst, “Multiple-valued logic—its status and its future,” IEEE
Trans. Computers, vol. C-33, no. 12, pp. 1160–1179, 1984.
[4] D. A. B. Miller, “Are optical transistors the logical next step?” Nature
Photonics, vol. 4, no. 1, pp. 3–5, 2010.
[5] H. J. Caulfield and S. Dolev, “Why future supercomputing requires
optics,” Nature Photonics, vol. 4, no. 5, pp. 261–263, 2010.
[6] Y. Jin, H. He, and Y. Lu, “Ternary optical computer principle,” Science
in China Series F: Information Sciences, vol. 46, no. 2, pp. 145–150,
2003.
[7] Y. Jin, H. He, and Y. Lu, “Ternary optical computer architecture,”
Physica Scripta, vol. T118, pp. 98–101, 2005.
[8] G. Eichmann, Y. Li, and R. R. Alfano, “Optical binary coded ternary
arithmetic and logic,” Applied Optics, vol. 25, no. 18, pp. 3113–3121,
1986.
[9] T. Chattopadhyay, “All-optical symmetric ternary logic gate,” Optics &
Laser Technology, vol. 42, no. 5, pp. 839–842, 2010.
[10] S. K. Garai, “Novel method of designing all optical frequency-encoded
Fredkin and Toffoli logic gates using semiconductor optical amplifiers,”
IET Optoelectronics, vol. 5, no. 6, pp. 247–254, 2011.
[11] A. F. Oskooi, et al., “Meep: A flexible free-software package for
electromagnetic simulations by the FDTD method,” Computer Physics
Communications, vol. 181, no. 3, pp. 687-702, 2010.

Design and Evaluation Frameworks for Advanced
RISC-based Ternary Processor
Dongyun Kam, Jung Gyu Min, Jongho Yoon, Sunmean Kim, Seokhyeong Kang and Youngjoo Lee

arXiv:2111.07584v1 [cs.AR] 15 Nov 2021

Department of Electrical Engineering
Pohang University of Science and Technology, Pohang, South Korea
{rkaehddbs,mjg1104,yoonjongho99,sunmean,shkang,youngjoo.lee}@postech.ac.kr

Abstract—In this paper, we introduce the design and verification frameworks for developing a fully-functional emerging
ternary processor. Based on the existing compiling environments
for binary processors, for the given ternary instructions, the
software-level framework provides an efficient way to convert the
given programs to the ternary assembly codes. We also present a
hardware-level framework to rapidly evaluate the performance of
a ternary processor implemented in arbitrary design technology.
As a case study, the fully-functional 9-trit advanced RISC-based
ternary (ART-9) core is newly developed by using the proposed
frameworks. Utilizing 24 custom ternary instructions, the 5-stage
ART-9 prototype architecture is successfully verified by a number
of test programs including dhrystone benchmark in a ternary
domain, achieving the processing efficiency of 57.8 DMIPS/W and
3.06 × 106 DMIPS/W in the FPGA-level ternary-logic emulations
and the emerging CNTFET ternary gates, respectively.
Index Terms—Ternary processor, Instruction set architecture,
RISC, Emerging computer design, Multi-valued logic circuits

I. I NTRODUCTION
The dimensional down-scaling of CMOS technology has
been continuously focused on increasing hardware efficiency
of digital circuits [1]. However, the performance improvement from the recent down-scaling is now expected to meet
the potential limitation especially caused by the increased
interconnecting/routing overheads [2]. Among the different
solutions to address this limitation, the multi-valued logic
(MVL) circuits have been recently gaining great popularity
due to their attractive potential for reducing the circuit-level
complexity as well as the routing burden even at the aggressive
down-scaling technology [3]. For the practical implementation
of the ternary-based system, which is a starting point of MVL
solutions, numerous technologies have been proposed to solve
the stability issue of each voltage/current level with emerging
devices including carbon nanotube FETs (CNTFETs) [4],
graphene barristors [5], and CMOS-based ternary transistors
[6]. In general, the prior studies on ternary circuits mainly
present the potential expectations of gate-level performances
[7], [8]. For circuit-level studies, some digital building blocks
such as adder, multiplier, and flip-flop have been also investigated to extend the concept of gate-level evaluation in ternary
domains [9]–[11]. Due to the lack of systematic designlevel strategies, on the other hand, the system- or processorlevel explorations for ternary-based digital solutions are rarely
reported in the open literature with few details [12].
Identify applicable funding agency here. If none, delete this.

In this work, we introduce advanced design and evaluation
frameworks to realizing ternary processors, measuring actual
performances with the practical benchmark programs. In contrast that the previous studies only present limited concepts to
only test processing blocks in ternary number systems [13],
[14], we develop a 9-trit advanced RISC-based ternary (ART9) core by adopting the proposed frameworks, presenting the
fully-functional top-level ternary microprocessor. Based on
the 9-trit instruction-set architecture (ISA) with 24 custom
ternary instructions, more precisely, the proposed softwarelevel framework provides an efficient way to convert the
existing binary programs to the ternary codes, even reducing
the program size compared to the baseline codes with RV32I ISA [15]. The hardware-level framework offers the cycleaccurate simulator and the technology mapper, providing the
quantitative evaluations of the pipelined ART-9 architecture for
arbitrary design technology. Targeting the specialized 5-stage
pipelined architecture, as a case study, the proposed ART9 core achieves the processing efficiency of 57.8 DMIPs/W
and 3.06 × 106 DMIPs/W when we use the FPGA-level
ternary-logic emulations and the emerging CNTFET-based
ternary gates [7], [8], respectively, reporting the first full-level
evaluations of ternary processors.
II. BACKGROUND
A. Ternary Number Systems
Based on the integrated ternary gates using three voltage
levels such as GND, VDD/2 and VDD, the ternary circuits
are dedicated to the arithmetic operations in a ternary number
system. Like the binary case, there are in general two types
of ternary fixed-point number systems: unsigned and signed
systems. For an n-trit number X = (xn−1 , xn−2 , ..., x0 )3 ,
where xi ∈ {0, 1, 2}, the unsigned ternary number only
represents positive integers from 0 to 3n − 1 by interpreting
an n-trit sequence into a decimal value Yunsigned as follows.
Yunsigned =

n−1
X

xk 3k .

(1)

k=0

Although the unsigned number system is useful for denoting
indices of general-purposed ternary registers (GPTR) and addresses of ternary instruction/data memories (TIM/TDM), it is
obviously required to support the signed arithmetic operations
for performing the general data processing. Therefore, the

Fig. 1. Truth tables of ternary logic operations.
Fig. 2. The proposed software-level compiling framework.

singed ternary number system is considered to interpret the
given n-trit sequence into the negative value. Among different
ways to develop the ternary signed numbers [13], in this work,
we adopt the balanced signed number system, where each trit
is now an element from the balanced set, i.e, xi ∈ {−1, 0, 1}
[13]. Then, a numerical value Ysigned of n-trit ternary number
X is still calculated in the same way as the unsigned representation shown in (1). Compared to the unbalanced approaches
in [13], it is reported that the arithmetic operations in balanced
ternary numbers can be simplified according to the conversionbased negation property [8], [14]. To develop the proposed
frameworks for general-purposed ternary processors, therefore,
the balanced representation is definitely suitable by requiring
fewer ternary gates for the practical realization [8].
B. Ternary-based Arithmetic and Logical Operations
Similar to basic operations of RISC-based binary processors
[15], the ternary processor should support logic and arithmetic
operations to perform the general user-level programs. As
reported in [13], the balanced ternary logic operations include
AND, OR, XOR, standard ternary inverting (STI), negative
ternary inverting (NTI) and positive ternary inverting (PTI),
where the detailed truth tables are exemplified in Fig. 1.
Compared to the familiar two-input logic gates such as AND,
OR, and XOR, note that the inverting operation consists of
three fundamental functions (denoted as STI, NTI, PTI in
Fig. 1), considering as the most important processing in the
balanced ternary number system [13]. It is also possible to
define the proper two-input arithmetic operations, which are
comparable to the well-established functions in the binary
processor [15]. For example, the fundamental functions including ternary addition, comparison, multiplication, and division,
have been extensively studied for the next-generation computer
arithmetic [9], [10], [16]. Utilizing the negation operations
in Fig. 1, it is also possible to simply utilize the ternary
subtraction based on the pre-designed ternary adder [16].
III. P ROPOSED F RAMEWORKS FOR T ERNARY P ROCESSORS
A. Software-Level Compiling Framework
For the full-level ternary processor implementation, based
on a given ternary ISA, it is important to prepare ternary-based
assembly (or executable) programs in an easy way. With the

assistance of the existing RISC-V tool chains in open-source
domains [17], in this work, we first develop a software-level
compiling framework supporting instruction mapping, operand
conversion, and redundancy checking, which can efficiently
generate the ternary assembly benchmarks for arbitrary Cbased source codes. Fig. 2 conceptually illustrates the processing steps of the proposed software-level framework. Note that
the input C-level program is firstly handled by an open-source
compiler for RV-32I ISA, obtaining an assembly sequence
of 32-bit instructions. Then, the instruction mapping step is
activated to translate the 32-bit instructions into pre-defined
ternary instructions. For a binary instruction that cannot be
directly converted with a ternary version, we utilize several
primitive sequences of ternary instructions, still offering valid
mapping results by allowing a few more instructions. After
mapping ternary instructions, the operand conversion step
is followed to find the ternary representations of immediate
values in the baseline binary instructions. Depending on the
definition of ternary instructions, it might be required to add
more instructions to construct the large-sized operands in
ternary number systems. Note that the operand conversion step
also supports the register renaming when the given ternary
ISA uses fewer general-purposed registers than the baseline
binary processor. As the mapping and conversion steps may
utilize additional instructions, the final redundancy checking
phase finds the meaningless instructions by investigating the
duplicated operations, removing them to minimize the overall
code size. During the elimination of redundant instructions, the
proposed framework also re-calculates the branch target addresses to ensure the correct results. As the proposed softwarelevel framework is based on the well-established compiling
environments for binary processors, we can purely focus on
increasing the mapping quality in the ternary domain by deeply
considering the characteristics of ternary instructions, relaxing
the development efforts of ISA-dependent processor-design
frameworks. Targeting the proposed ART-9 ISA, as a case
study, the proposed software-level framework easily generates
various ternary codes with reduced memory requirements,
even saving the program size of dhrystone benchmark by 54%
compared to the baseline processor of RV-32I ISA [15].

TABLE I
S UMMARY OF ART-9 T ERNARY I NSTRUCTIONS
Type

9-trit instructions

Operation

R

MV Ta,Tb
PTI Ta,Tb
NTI Ta,Tb
STI Ta,Tb
AND Ta,Tb
OR Ta,Tb
XOR Ta,Tb
ADD Ta,Tb
SUB Ta,Tb
SR Ta,Tb
SL Ta,Tb
COMP Ta,Tb

TRF[Ta] = TRF[Tb]
TRF[Ta] = PTI(TRF[Tb])
TRF[Ta] = NTI(TRF[Tb])
TRF[Ta] = STI(TRF[Tb])
TRF[Ta] = TRF[Ta] & TRF[Tb]
TRF[Ta] = TRF[Ta] | TRF[Tb]
TRF[Ta] = TRF[Ta] ⊕ TRF[Tb]
TRF[Ta] = TRF[Ta] + TRF[Tb]
TRF[Ta] = TRF[Ta] − TRF[Tb]
TRF[Ta] = TRF[Ta] ≫ TRF[Tb][1:0]
TRF[Ta] = TRF[Ta] ≪ TRF[Tb][1:0]
TRF[Ta] = compare(TRF[Ta],TRF[Tb])

I

ANDI Ta,imm
ADDI Ta,imm
SRI Ta,imm
SLI Ta,imm
LUI Ta,imm
LI Ta,imm

TRF[Ta] = TRF[Ta] & imm[2:0]
TRF[Ta] = TRF[Ta] + imm[2:0]
TRF[Ta] = TRF[Ta] ≫ imm[1:0]
TRF[Ta] = TRF[Ta] ≪ imm[1:0]
TRF[Ta] = {imm[3:0],00000}
TRF[Ta] = {TRF[Ta][8:5],imm[4:0]}

B

BEQ Ta,B,imm
BNE Ta,B,imm
JAL Ta,imm
JALR Ta,Tb,imm

PC = PC + imm[3:0] if TRF[Tb][0] == B
PC = PC + imm[3:0] if TRF[Tb][0] != B
TRF[Ta] = PC+1, PC = PC + imm[4:0]
TRF[Ta] = PC+1, PC = TRF[Tb]+imm[2:0]

M

LOAD Ta,Tb,imm
STORE Ta,Tb,imm

TRF[Ta] = TDM[TRF[Tb]+imm[2:0]
TDM[TRF[Tb]+imm[2:0]] = TRF[Ta]

Fig. 3. The proposed hardware-level evaluation frameworks.

B. Hardware-Level Evaluation Framework
Using ternary assembly codes, which can be obtained by the
proposed software-level compiling framework, we develop the
hardware-level evaluation framework allowing an efficient way
to develop the prototype of ternary processor. As illustrated in
Fig. 3, the hardware-level framework includes a cycle-accurate
simulator, a gate-level analyzer, and a performance estimator.
The cycle-accurate simulator accepts the high-level description
of the pipelined ternary processor, and provides the required
processing cycles for performing the input ternary assembly
codes. With the synthesizable RTL design corresponding to
the high-level architecture description, the proposed gatelevel analyzer can estimate the critical delay as well as the
power consumption of ternary processor. Note that we define
the property description of the design technology as another
input of gate-level analyzer, which includes delay and power
characteristics of primitive building blocks, enabling more
accurate analysis results depending on the target technology.
As depicted in Fig. 3, the performance estimator gathers all
the outputs from prior steps, and finally generates the overall
evaluation information of the ternary processor implemented
in certain design technology. By utilizing multiple evaluation
steps and even considering the technology-oriented information, before starting the actual implementation phase with predesigned peripherals, we can remarkably reduce the design
efforts of the custom ternary processor with the proposed
hardware-level evaluation framework.
IV. ART-9 C ORE D ESIGN FOR P ROPOSED F RAMEWORKS
A. ART-9 Instruction Set Architecture
Based on the balanced ternary number systems, the proposed ART-9 processor defines 9-trit-length ISA following the
properties of contemporary RISC-type binary processors [15].
Table I summarizes 24 ART-9 ternary instructions processing
9-trit data values, which are the essential inputs at the proposed
software-level compiling framework. By matching the word
length of both instruction and data, we can allow the regular
structure for realizing TIM and TDM. To fetch an instruction
by accessing the TIM, we use a special-purposed 9-trit register,
i.e., the program counter (PC) register containing the instruction address. In order to store the intermediate data, like the

modern processor architectures [15], [18], the ART-9 core also
includes a ternary registerfile (TRF) including nine generalpurposed registers, each of which is accessed by using a 2trit value. Utilizing the load-store architecture used for typical
RISC processors [19], there are four instruction categories in
ART-9 ISA; R-type, I-type, B-type, and M-type.
For the R-type instructions, considering the recent studies
[20], we select essential 12 logical/arithmetic functions as
depicted in Table I. In fact, most R-type instructions are typical
two-address instructions, which fetch two 9-trit operands in
TRF, whose 2-trit indices are denoted as Ta and Tb, and
then overwrite a 9-trit result to the register TRF[Ta]. Note
that some R-type instructions specialized for inversion and
data-movement operations use only one source operand from
Tb, where the destination operand is still Ta to have the
regular encoding patterns, relaxing the complexity to decode
the fetched instruction. In addition, we also realize an R-type
comparison instruction (COMP), where the least significant
trit (LST) of the destination register TRF[Ta] denotes the
comparison result of two input operands with the dedicated
function compare() in Table I. More specifically, the LST of
TRF[Ta] is set to be zero when the two inputs are the same,
otherwise it becomes +1 (or −1) if TRF[Ta] > TRF[Tb]
(or TRF[Ta] < TRF[Tb]). This COMP instruction plays an
important role to improve the code density by allowing the
conditional execution of the following branch instructions.

Fig. 4. 5-stage pipelined architecture of the proposed ART-9 processor.

In order to reduce the generation complexity of constant
values, the technique to encode immediate values into the
instruction is generally used for reducing the size of userlevel programs [15], [18]. The proposed ART-9 processor also
supports immediate-based processing with I-type instructions.
As described in Table I, unlike the R-type instructions offering
various functions, we only allow immediate values at addition,
AND logic, and shift functions, which are known to be the
most common operations in practice [20]. Due to the limited
trit-width for denoting an embedded immediate, there could be
extra overheads to realizing full-length (9-trit) constant values.
Instead of utilizing a series of the shift-and-addition process to
store a 5-trit immediate value initialized by a load immediate
(LI) instruction, we adopt a special I-type instruction named
load upper immediate (LUI), which is introduced at the RISCtype processors for making a large-sized constant value [15],
[18]. As a result, the ART-9 ISA offers an acceptable flexibility
to use wide ranges of immediate values, suitable for the
resource-limited processing environments.
Besides the logical/arithmetic instructions, it is also required
to define the branch-related instructions changing the PC
value, which is denoted as B-type instructions in Table I. In the
proposed ART-9 cores, we introduce four B-type instructions
including two conditional branch operations associated with
the PC-relative addressing, which are referred to as BEQ
and BNE as shown in Table I. To utilize these conditional
operations, as described earlier, we preset the LST of TRF[Tb]
in BEQ or BNE by using a COMP instruction, so that a 1-trit B
value in BEQ or BNE is compared to check the branch-taken
condition. In addition, we define two unconditional jump-andlink instructions (JAL and JALR), which are mainly used

for the subroutine calls. Adopting the PC-relative addressing,
similar to the conditional branches, the JAL instruction uses
the PC value as a base address added by a 5-trit immediate.
On the other hand, by using the JALR instruction, we can use
the stored 9-trit value in TRF to set the base address with a
small-sized 3-trit immediate, allowing more long-range jumps.
As depicted in Table I, note that this base-register addressing is
also used to access TDM with M-type load/store instructions,
reducing the hardware complexity with the shared datapath.
B. 5-stage Pipelined ART-9 Architecture
To support the proposed ART-9 ISA efficiently, we develop
in this work a simple but efficient pipelined architecture, which
is used for input descriptions of the proposed hardware-level
evaluation framework. As shown in Fig. 4, similar to the
lightweight RISC-type designs [19], there are five stages for
fetching the instruction from TIM (IF), decoding the fetched
instruction (ID), executing the arithmetic/logical operations
(EX), accessing the TDM (MEM), and updating the result
to TRF (WB). The ternary pipelined registers are newly
developed to keep the results from each stage, making a balanced pipelined processing. We also introduce the synchronous
single-port TIM and TDM designs for reducing the memoryaccessing latency, where the TRF in this work supports two
asynchronous read ports and one synchronous write port. The
ternary arithmetic logic unit (TALU) in EX stage is specialized
to perform various operations depending on the control signals
from main decoder in ID stage. In the pipelined ART-9 core,
the hazard detection unit (HDU) in ID stage compares the
adjacent instructions to determine the generation of hardwarelevel stall controls at the run time. For reducing the number

TABLE II
S IMULATION R ESULTS OF D HRYSTONE B ENCHMARK
This work

VexRiscv [24] PicoRV32 [25]

ISA Architecture

ART-9 ISA

RV-32I

RV-32IM

# of instructions

24

40

48

Pipelined stages

5

5

1

Multiplier

X

O

O

DMIPS/MHz

0.42

# of memory-cells 11.6K trits

0.65

0.31

25.4K bits

23.7K bits

TABLE III
P ROCESSING C YCLES FOR D IFFERENT T EST P ROGRAMS
Fig. 5. The number of memory cells for storing benchmark programs.
Bubble sort GEMM Sobel filter Dhrystone

of unwanted stalls as many as possible, we actively apply
the forwarding multiplexers to get the correct 9-trit inputs
at TALU, solving ALU-use data hazards. To minimize the
number of stalls from B-type instructions causing control
hazards, the pipelined ART-9 processor utilizes the dedicated
branch-target calculator as well as the condition checker in
ID stage, directly forwarding the calculated address to update
the PC register. For checking the branch-taken conditions, in
addition, forwarding one-trit values successfully mitigates the
long and complex datapath starting from TRF, still allowing
one-cycle stall after B-type instructions without increasing
the overall critical delay. As a result, we only observe the
hardware-inserted stall cycles when there exist load-use data
hazards and taken branches. After detecting the stall insertion
case, the main decoder at ID stage generates a stall control
signal, which will be used for selecting the no-operation
(NOP) at the next ID stage as shown in Fig. 4. Without
introducing a dedicated NOP encoding, note that the proposed
ART-9 ISA uses an ADDI instruction to denote the NOP
operation with a zero-valued immediate.
V. E VALUATION AND I MPLEMENTATION R ESULTS
A. Benchmark Evaluations
By using the proposed compiling framework, targeting the
ART-9 ISA shown in Table I, we designed several ternary
benchmark programs including the general computing algorithms; bubble sort, general matrix multiplication (GEMM),
and sobel filter [21], [22]. In addition, for the first time,
a dhrystone benchmark is also described with the ternary
instructions by converting the existing dhrystone code of
the RV-32I ISA, which is popularly used for evaluating the
computing performance of general-purposed CPU cores [23].
Fig. 5 depicts the effectiveness of the proposed ART-9 ISA
by evaluating the required memory size for storing each
benchmark program, showing that the proposed softwarelevel framework offers acceptable assembly codes compared
to the binary versions. Note that we counted the number of
memory cells for this comparison, as the ternary instructions
necessitate the dedicated ternary memory where a storing
cell can keep up to three different charge distributions [11].

This work

2,432

10,748

7,822

134,200

PicoRV32 [25]

9,227

11,290

18,250

186,607

Although we developed a simple 9-trit ISA including only
24 instructions, it is clear that the proposed ART-9 processor
requires a much smaller memory size when compared to the
binary counterparts; RV-32I using 32-bit instructions [15] and
ARMv6M with 16-bit instructions [18]. If we consider implementation results of dhrystone codes, due to the short-length
ternary instructions associated with the efficient software-level
framework, for example, our ART-9 core reduces the number
of required memory cells by 54% and 17% when compared to
the RV-32I [15] and ARMv6M [18] processors, respectively.
In other words, there exist reasonable benefits of exploiting
the ternary number systems, which can reduce the memory
overheads while providing a similar amount of flexibility to
binary ISAs with long-length instructions.
B. Hardware-level Evaluation Results
Table II precisely shows evaluation results of the cycleaccurate simulator of different RISC-based processors running
the dhrystone benchmark. Note that our ART-9 core achieves
0.42 DMIPS/MHz by utilizing only 24 instructions, whereas
the fully-optimized VexRiscv [24] and PicoRV32 [25] processor provides 0.65 and 0.31 DMIPS/MHz with more instructions and the dedicated multiplier, respectively. Utilizing the
optimized codes from the proposed compiling frameworks, the
prototype ART-9 core can be designed with the comparable
processing speed and much smaller size of memory cells. In
addition, Table III also shows that the proposed compiling
framework efficiently optimizes the number of instructions for
the other benchmarks. As it is considered that the memory in
general dominates the overall system complexity, the prototype
ART-9 core offers the low-complexity computing platform
even compared to the recent lightweight PicoRV32 processor
with non-pipelined architecture. In other words, the optimized
ART-9 ISA and processor, which utilize the proposed frameworks, successfully offer a reasonable solution achieving both
the fast computing and the low hardware-cost, presenting the
fully-functional processor design in the ternary domain.

TABLE IV
I MPLEMENTATION R ESULTS USING CNTFET T ERNARY G ATES
Voltage

Total gates

Power

DMIPS/W

0.9V

652

42.7 µW

3.06 × 106

TABLE V
I MPLEMENTATION R ESULTS USING FPGA- BASED T ERNARY L OGICS
Voltage

Frequency

ALMs

Registers

RAM

Power

0.9V

150MHz

803

339

9,216 bits

1.09W

Using the proposed gate-level analyzer, we finally present
implementation results of ART-9 prototypes. For the simplified
32nm CNTFET ternary models without considering the parasitic capacitance [8], we first estimated the gate-level costs
of the 5-stage pipelined core as shown in Table IV. The
datapath of ART-9 core only required 652 standard ternary
gates, consuming 42.7 µW when the operating voltage is set to
0.9 V. According to the dhrystone result shown in Table II, the
CNTFET-based ART-9 core achieves 3.06 × 106 DMIPS/W,
showing that the emerging ternary device leads to the lowpower microprocessor, even superior to the near-threshold
ARM Cortex-M3 design requiring 3.9 × 103 DMIPS/W [26].
In order to validate the proposed ternary processor, we
also implemented the ART-9 core in the FPGA-based verification platform. For the practical implementation, all the
ternary-based building blocks are emulated with the binary
modules, adopting the binary-encoded ternary number system
[27]. Table V summarizes the implementation results of the
binary-encoded ART-9 core, which utilizes only few hardware
resources of Intel Stratix-V FPGA at the operating frequency
of 150 MHz. Targeting the dhrystone benchmark, the FPGAbased ART-9 core achieves 57.8 DMIPS/W by consuming
1.09W including two binary-encoded ternary memories. As
a result, the proposed frameworks successfully opens the
preliminary results for realizing the ternary-based processor,
which can be easily mapped to the future emerging ternary
devices for allowing the extreme-low-power computing.
VI. C ONCLUSION
In this paper, we have proposed several designs and evaluation frameworks for developing ternary microprocessors,
which are verified by the lightweight RISC-based ternary
processor with 9-trit datapath. Based on the balanced ternary
number system, the proposed software-level framework efficiently supports a systematic way to construct assembly codes
for the given ternary ISA. Accepting the architecture-aware
descriptions as well as the target technology information, the
hardware-level framework is then followed to estimate several
implementation-aware metrics, reducing the overall design
overheads in the ternary number system. Based on the proposed frameworks, the fully-functional ART-9 microprocessor
is developed and verified at different emerging technologies,
offering attractive design methods for ternary processors.

R EFERENCES
[1] G. Yeap, “Smart mobile SoCs driving the semiconductor industry:
Technology trend, challenges and opportunities,” in IEDM Tech. Dig.,
Dec. 2013, pp. 1–3.
[2] N. Magen, A. Kolodny, U. Weiser, and N. Shamir, “Interconnect-power
dissipation in a microprocessor,” in Proc. Int. Workshop Syst, Level
Interconnect Predict., 2004, pp. 7–13.
[3] V. Gaudet, “A survey and tutorial on contemporary aspects of multiplevalued logic and its application to microelectronic circuits,” IEEE J.
Emerg. Sel. Topics Circuits Syst., vol. 6, no. 1, pp. 5–12, 2016.
[4] S. Lin, Y.-B. Kim, and F. Lombardi, “A novel CNTFET-based ternary
logic gate design,” in Proc. IEEE Int. Midwest Symp. Circuits Syst., Aug.
2009, pp. 435–438.
[5] H. Yang et al., “Graphene barristor, a triode device with a gate-controlled
schottky barrier,” Science, vol. 336, no. 6085, pp. 1140–1143, 2012.
[6] S. Shin, E. Jang, J. W. Jeong, B.-G. Park, and K. R. Kim, “Compact
design of low power standard ternary inverter based on OFF-state current mechanism using nano-CMOS technology,” IEEE Trans. Electron
Devices, vol. 62, no. 8, pp. 2396–2403, 2015.
[7] S. Kim, T. Lim, and S. Kang, “An optimal gate design for the synthesis
of ternary logic circuits,” in Proc. 23rd Asia South Pacific Design
Automat. Conf. (ASP-DAC), Jan. 2018, pp. 476–481.
[8] S. Kim, S.-Y. Lee, S. Park, K. R. Kim, and S. Kang, “A logic synthesis
methodology for low-power ternary logic circuits,” IEEE Trans. Circuits
Syst. I, Reg. Papers, vol. 67, no. 9, pp. 3138–3151, 2020.
[9] S. Heo et al., “Ternary full adder using multi-threshold voltage graphene
barristors,” IEEE Electron Device Lett., vol. 39, no. 12, pp. 1948–1951,
Dec. 2018.
[10] Y. Kang et al., “A novel ternary multiplier based on ternary cmos
compact model,” in Proc. IEEE 47th Int. Symp. Multiple-Valued Log.
(ISMVL), May. 2017, pp. 25–30.
[11] Y. Choi, S. Kim, K. Lee, and S. Kang, “Design and Analysis of a LowPower Ternary SRAM,” in Proc. IEEE Int. Symp. Circuits Syst. (ISCAS),
Apr. 2021, pp. 1–4.
[12] “Ternary computer system,” Accessed on: Sep. 17, 2021. [Online].
Available: https://www.ternary-computing.com
[13] “The trillium architecture,” Accessed on: Sep. 17, 2021. [Online]. Available: https://homepage.divms.uiowa.edu/~jones/ternary/trillium.shtml
[14] S. Narkhede, G. Kharate, and B. Chaudhari, “Design and implementation
of an efficient instruction set for ternary processor,” International
Journal of Computer Applications, vol. 83, no. 16, 2013.
[15] A. Waterman, Y. Lee, D. A. Patterson, and K. Asanović, “The RISC-V
Instruction Set Manual, Volume I: User-Level ISA, Version 2.1,” 2016.
[Online]. Available: https://riscv.org/specifications/
[16] B. Parhami and M. McKeown, “Arithmetic with binary-encoded balanced ternary numbers,” in Proc. Asilomar Conf. Signals, Systems and
Computers, 2013, pp. 1130–1133.
[17] G. Tagliavini, S. Mach, D. Rossi, A. Marongiu, and L. Benini, “Design
and Evaluation of Small Float SIMD extensions to the RISC-V ISA,”
in Proc. of the Design, Automat. Test Eur. (DATE), 2019, pp. 654–657.
[18] J. Yiu, The Definitive Guide to ARM Cortex-M0 and Cortex-M0+
Processors. 2nd ed. Boca Raton, FL, USA: Academic, 2015.
[19] F. Schuiki et al., “Stream semantic registers: A lightweight RISC-V ISA
extension achieving full compute utilization in single-issue cores,” IEEE
Trans. Comput., vol. 70, no. 2, pp. 212–227, 2020.
[20] P. Li, “Reduce Static Code Size and Improve RISC-V Compression,”
Master’s thesis. EECS Department, Univ. of California, Berkeley, 2019.
[21] Y. Wang et al., “A compression-based area-efficient recovery architecture
for nonvolatile processors,” in Proc. of the Design, Automat. Test Eur.
(DATE), 2012, pp. 1519–1524.
[22] A. Zulehner and R. Wille, “Matrix-vector vs. Matrix-matrix multiplication: Potential in DD-based simulation of quantum computations,” in
Proc. of the Design, Automat. Test Eur. (DATE), 2019, pp. 90–95.
[23] R. York, “Benchmarking in context: Dhrystone,” ARM, March, 2002.
[24] “Vexriscv,” Accessed on: Sep. 17, 2021. [Online]. Available:
https://github.com/SpinalHDL/VexRiscv
[25] “Picorv32,” Accessed on: Sep. 17, 2021. [Online]. Available:
https://github.com/cliffordwolf/picorv32
[26] R. G. Dreslinski et al., “Centip3de: A 64-core, 3d stacked near-threshold
system,” IEEE Micro, vol. 33, no. 2, pp. 8–16, 2013.
[27] G. Frieder and C. Luk, “Algorithms for binary coded balanced and
ordinary ternary operations,” IEEE Trans. Comput., vol. 100, no. 2, pp.
212–215, 1975.

Published as a conference paper at ICLR 2025

S URPRISING E FFECTIVENESS OF PRETRAINING
T ERNARY L ANGUAGE M ODELS AT S CALE
Ayush Kaushal1 2 ∗ , Tejas Vaidhya 1 4 † ∗ , Arnab Kumar Mondal 4 , Tejas Pandey1 3 ,
Aaryan Bhagat 5 , Irina Rish 1 2 4
1
Nolano AI 2 University of Montreal 3 IIT Kharagpur 4 Mila - Quebec AI Institute 5 UC Riverside

A BSTRACT
Rapid advancements in GPU computational power has outpaced memory capacity
and bandwidth growth, creating bottlenecks in Large Language Model (LLM)
inference. Post-training quantization is the leading method for addressing memoryrelated bottlenecks in LLM inference, but it suffers from significant performance
degradation below 4-bit precision. This paper addresses these challenges by investigating the pretraining of low-bitwidth models specifically Ternary Language Models (TriLMs) as an alternative to traditional floating-point models (FloatLMs) and
their post-training quantized versions (QuantLMs). We present Spectra LLM suite,
the first open suite of LLMs spanning multiple bit-widths, including FloatLMs,
QuantLMs, and TriLMs, ranging from 99M to 3.9B parameters trained on 300B
tokens. Our comprehensive evaluation demonstrates that TriLMs offer superior
scaling behavior in terms of model size (in bits). Surprisingly, at scales exceeding one billion parameters, TriLMs consistently outperform their QuantLM and
FloatLM counterparts for a given bit size across various benchmarks. Notably,
the 3.9B parameter TriLM matches the performance of the FloatLM 3.9B across
all benchmarks, despite having fewer bits than FloatLM 830M. Overall, this research provides valuable insights into the feasibility and scalability of low-bitwidth
language models, paving the way for the development of more efficient LLMs.

1

I NTRODUCTION

The computational power of GPUs, measured in FLOPs, is increasing exponentially, doubling
approximately every 1.26 years. In contrast, memory capacity and bandwidth are growing at a slower
pace, doubling every 2 and 2.9 years, respectively (Gholami et al., 2024). This disparity highlights that
computing capabilities are outpacing advances in memory technology. In Large Language Models
(LLMs) inference, the primary bottlenecks are caused by model size (bits), which affects memory
usage (memory capacity) and data transfer to processors (memory bandwidth). These issues are
becoming more critical than the growing number of model parameters which affect the computational
limits (FLOPs). For instance, state-of-the-art LLMs such as 340B Nemotron 4 (Nvidia et al., 2024)
have sizes (in bits) exceeding the memory capacity of data center GPUs, such as 8xH100s. Token
generation speed, or latency, is now limited by memory bandwidth (Kim et al., 2024). Addressing
these bottlenecks requires more expensive training, exceeding Chinchilla’s compute-optimal regime
(Hoffmann et al., 2022), with less than 10B parameter models being trained on up to 15 trillion
tokens (Touvron et al., 2023b; AI@Meta, 2024; Team et al., 2024). Another widely used technique is
post-training quantization during deployment (Zhu et al., 2023); however, we demonstrate in Section
5 that this approach is sub-optimal.
In post-training quantization, LLMs initially trained using 16-bit floating point precision (referred
to as FloatLMs) undergo parameter quantization, and the resulting models are termed QuantLMs.
These models use optimized kernels for deployment, offering speedups nearly proportional to the
compression factor (Frantar & Alistarh, 2024). However, quantizing to very low bitwidths creates a
significant mismatch between the representations of pretrained FloatLM and the deployable QuantLM,
resulting in undesired behavior and quality degradation (Li et al., 2024; Huang et al., 2024). Some
state-of-the-art methods (Frantar et al., 2022; Egiazarian et al., 2024) mitigate this issue by using
∗
†

Equal contribution, listed in alphabetical order.
Correspondence: tejas@nolano.ai

1

Published as a conference paper at ICLR 2025

Commonsense & Reasoning Across Parameters

Avg. Score Across 6 Benchmarks

Avg. Score Across 6 Benchmarks

Commonsense & Reasoning Across Size
60
55
50
FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM

45
40
1

10

20

30

40

Size in Bits * 109

50

60
55
50

40

60

190M

(a) C&R: acc vs size

60

Accuracy (log scale)

Accuracy

50
40
30
FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM
10

20
30
40
Size in bits (109)

1.5B

3.9B

LAMBADA Accuracy Across Parameters

LAMBADA Accuracy Across Size (Bits)

1

560M

Parameters

(b) C&R: acc vs parameters

60

20

FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM

45

50

50
40

30

20

60

(c) LAMBADA: acc vs size

FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM

190M

560M
Parameters

1.5B

3.9B

(d) LAMBADA: acc vs parameters

Figure 1: Common Sense and Reasoning (C&R) & LAMBADA Accuracy for ternary TriLM, FP16 FloatLM
and quantized QuantLM models across different model sizes, in bits and number of parameters. C&R scores
are averaged across 6 benchmarks. At 3B+ scales, TriLMs demonstrate better performance for their size than
QuantLM and competitive performance to FloatLM of the same parameters. See Tables 7, 8 and 10 for details.

calibration and re-training data from target domains; however, this approach increases sensitivity to
the calibration data. For instance, seemingly simple choices, like whether to length-normalize the
calibration data, can significantly impact QuantLM’s performance (Malinovskii et al., 2024). Other
works have observed that QuantLM at 4 bits (4-bit QuantLMs) have about 65% lower knowledge
capacity per parameter compared to trained and aligned FloatLMs (Allen-Zhu & Li, 2024).
An alternate approach to reducing model bitsize while maintaining parameter count involves training
neural networks with low effective bitwidths (Zhou et al., 2018). This approach offers compression
benefits beyond post-training quantization without its associated drawbacks. While low-bitwidth
approaches typically employ binary (1-bit) or ternary quantization (1.58-bit), binary quantization
generally underperforms compared to regular FP16 models (Liu et al., 2023a) (see Appendix B). In
contrast, ternary modeling can match performance while significantly reducing memory requirements
(as we demonstrate in section 5). Nevertheless, the relative performance of pretrained low-bitwidth
language models compared to QuantLMs across similar sizes (in bits) and similar parameter counts
remains unclear. This is a crucial unanswered question, given the high inference costs during the
deployment of very large-scale LLMs. Moreover, the training dynamics and scaling law of these
low-bitwidth models are also poorly understood, partly due to the lack of publicly available systematic
suites and associated comparative studies.
Motivated by these challenges, we make the following contributions in this paper:
Feasibility and Scalability of Training Ternary Language Models (TriLMs) We discuss the
deployment advantages (in section 2.1) and theoretical feasibility (in section 2.2) of training lowbitwidth models at scale. We then introduce ternary language models (TriLMs) and systematically
study their scaling laws compared to FloatLMs. Our analysis reveals that TriLMs offer better scaling
behavior in terms of model size, measured in bits (refer to Section 4.3). Moreover, as the number
2

Published as a conference paper at ICLR 2025

of parameters increases, the difference in validation loss between TriLMs and FloatLMs becomes
insignificant, indicating TriLM’s competitive performance at scale.
Spectra LLM suite. We present Spectra, the first open suite of LLMs spanning many bit-widths.
This suite includes FloatLMs, the corresponding QuantLMs at 3, 4, 6, and 8 bits, and ternary LLMs
(TriLMs). The latter uses ternary weights {-1, 0, +1}. The suite features 9 models ranging from 99M
to 3.9B parameters, all trained on the same 300B token dataset, totalling 54 models. We believe that
the Spectra LLM suite makes a valuable contribution to the LLM research community by facilitating
comparative studies, exploring the scalability and efficiency of ternary modeling, and improving
interpretability from neuronal to connection levels.
Evaluation and comparative analysis of TriLMs, FloatLMs, and QuantLMs at different scales.
We evaluate TriLMs, FloatLMs, and QuantLMs across multiple benchmarks, spanning commonsense,
reasoning, knowledge capacity and toxicity. At the billion parameter scale, TriLMs consistently outperform their QuantLM and FloatLM counterparts of the same bit-size across all the aforementioned
benchmarks (see Figure 1). Surprisingly, TriLM 3.9B matches the performance of FloatLM 3.9B
across all benchmarks, despite getting a higher perplexity and being 5.9 times smaller in bitsize.
However, we also note that certain challenges remain in TriLMs. For instance, TriLM 3.9B exhibits
the same level of toxicity and stereotyping as FloatLM 3.9B, significantly higher than a similarly
sized FloatLM 830M when measured in bits. While TriLM 3.9B and FloatLM 3.9B show similar
validation perplexity on some datasets, such as Penn Tree Bank and Lambada, a gap persists at this
scale on web corpora, both in-domain (i.e., on a test subset of SlimPajama, the same domain used
to train the models) and out-of-domain (e.g., on Dolma, C4 and RefinedWeb datasets). We provide
detailed perplexity results in the appendix D.4.

2

M OTIVATION FOR L OW-B ITWIDT M ODELS

2.1

M EMORY B OTTLENECKS AND L ANGUAGE M ODEL D EPLOYMENT

Memory Capacity of GPGPUs and Model Size (in Bits): Figure 24a in Appendix G reveal that
memory capacity has consistently lagged behind computational power across various accelerators,
including recent hardware like Blackwell (Nvidia Team, 2024), MI325X (AMD Team, 2024), and
Gaudi3 (Intel Gaudi Team, 2024). This gap is further exacerbated by advanced computational
techniques like Ampere sparse or FP8. As shown in Figure 25a of Appendix G, the model sizes
(in GB) for TriLM, QuantLM 4-Bit, and FloatLM scale differently with parameter counts. For
simplicity, the figure excludes overhead from KV Cache, activations, and compilation during model
deployment. FloatLM reaches the memory capacity of a single H100 at 34B parameters, with larger
models exceeding the capacity of multiple GPUs. In contrast, QuantLM 4-Bit supports up to 300B
parameters on a single MI300X. TriLMs, with over 300B parameters and appropriate packing, can fit
on a single H100, making them not only efficient for GPU deployment but also ideal for edge devices.
Memory bandwidth of GPGPUs and model inference speedup: Figure 24b in Appendix G
demonstrate the trends of Memory Bandwidth over FLOPs for accelerators over the years, highlighting
the slower growth of memory bandwidth compared to computation. This trend, indicating a downward
slope, aligns with Kim et al. (2024)’s establishment of the memory wall in autoregressive LLM
computation. They found that the speed of token generation is bottlenecked by the rate at which data
is fed from memory to processors, rather than the processing speed of the hardware. Consequently,
the autoregressive decoding of LLM inference can theoretically achieve speedup proportional to
its compression factor. Figure 25b in Appendix G illustrates the maximum possible speedup for
QuantLM 4-Bit and TriLM compared to FP16 at different parameter counts. Even at 7 billion
parameters, TriLMs can be more than 4 times faster at autoregressive decoding than FloatLM and 2
times faster than QuantLM 4-bit. While QuantLM 4-Bit plateaus at a maximum possible speedup
factor of 4x, TriLMs plateau much higher at 10x for FloatLM.

3

Published as a conference paper at ICLR 2025

2.2

L OW BITS CAN CAPTURE WEIGHT VARIANCE EFFECTIVELY AT SCALE

In this section, we use information theory to support our hypothesis: as the number of parameters
increases, training language models with low-bitwidth can effectively capture the necessary weight
variance without significant information loss. Assuming a fixed training dataset, we base this
hypothesis on analyzing weight distributions in FloatLMs ranging from 99M to 3.9B parameters.

Shannon Entropy

5.0
4.5
4.0
3.5
3.0
2.5
2.0
1.5

100

200

300

400

500

600

FloatLM 99M
FloatLM 190M
FloatLM 390M
FloatLM 560M
FloatLM 830M
FloatLM 1.1B
FloatLM 1.5B
FloatLM 2.4B
700 800 900

Differential Entropy

5.5

3.25
3.30
3.35
3.40
3.45
3.50
3.55
3.60
102

Number of Bins

Figure 2: Shannon entropy (in bits) of discretized
weight distribution with increasing number of bins.

103

Model Parameters (Millions)

Figure 3: Differential entropy of Gaussian fits on
weight distributions across different scales.

Assuming that the weights of a trained model follow a Gaussian distribution (see Appendix E), we fit a
Gaussian to these weights to understand their statistical behavior across model scales. The differential
2
entropy is calculated using the expression: H(W ) = 12 log2 (2πeσW
) where σW is the standard
deviation of the weights (Papoulis & Pillai, 2002). As shown in Figure 3, differential entropy decreases
with an increase in the number of parameters. This decrease indicates that the weights become more
concentrated around the mean as the model size increases, suggesting higher predictability and less
variability (MacKay, 2003). This reduced variability is due to overparameterization, which leads to
redundancy in the weights Zhang et al. (2017); Neyshabur et al. (2018).
Additionally, we also use Shannon entropy, calculated by discretizing the weight distribution into
PN
(N ) bins and computing HShannon = − i=1 pi log2 pi , where pi is the probability of the weights
falling into the i-th bin. The probability is given by the normalized frequency of weights within
each bin. Discretization allows us to apply discrete entropy measures to continuous data, with the
number of bins determining the representation granularity. Shannon entropy measures the average
minimum number of bits needed to encode the weight values based on their distribution, providing
a quantifiable measure of their "information content" (Shannon, 1948). Lower Shannon entropy
indicates a more predictable, less diverse distribution that can be effectively encoded using fewer
bits. Examining Shannon entropy across scales and bin sizes, we validate our finding that larger
models require fewer bits for effective representation. As plotted in Figure 2, there is a general trend
of decreasing Shannon entropy with increasing parameter count for a given number of bins.
These analyses support the potential of low-bitwidth models to match full-precision performance,
especially as model sizes grow. In Section 4.3, we further substantiate this by analyzing the scaling
behavior of our low-bitwidth TriLMs compared to FloatLMs.
2.3

S ELECTING THE A PPROPRIATE L OW-B ITWIDTH M ODEL

Selecting the appropriate quantization level is crucial for balancing computational efficiency and
performance in low-bitwidth models. Binary models quantize weights to {−1, 1}, simplifying
multiplications to efficient XOR operations (Courbariaux et al., 2016a), making them suitable for
resource-constrained environments (Hubara et al., 2017). Ternary models introduce a zero state
{−1, 0, +1}), replacing multiplications with additions and subtractions (Li et al., 2016), and improve
efficiency by skipping calculations when weights are zero (Zhu et al., 2017). Conversely, models
quantized to 2, 3, or 4 bits require more complex operations, including full multiplications, which
are computationally more demanding than those required for binary and ternary models (Zhou et al.,
2016). Therefore, this work only considers binary and ternary language models for further analysis.
The reduction in computational complexity in binary models often comes at the cost of significant
performance degradation (Rastegari et al., 2016). In contrast, ternary quantization adds a zero state,
4

Published as a conference paper at ICLR 2025

better approximating weight distributions without significantly increasing computational demands (Li
et al., 2016), making them a sweet spot for balancing performance with efficiency gains (Zhu et al.,
2017). Our observations align with these, as the scaling trends for given data size for our TriLMs
consistently outperform those of BiLMs (Binary LLMs) across all parameter counts and bit sizes
considered in this work, as shown in Appendix B and Figure 12. As a result, this work primarily
focuses on the TriLM model, which we describe in the next section.

3

T RI LM: T ERNARY L ANGUAGE M ODEL
γ = 0.171

μabs

...

...
...

...

..

.....

0.151 ..... 0.538
* 0.171

.....

...

...

...

0 1 ..... 0 -1

Device 1

...

-0.262 ..... 0.034

1 -1 ..... 1 0

-0.472 ..... 0.981

..... -0.168 -0.443

.....

.....
0.007 0.185

Ternary Thresholding
Mean of Absolutes

μabs

tc

0.273 -0.375 ..... 0.002

Matrix Multiplication

...

...

...

Ba

Device 2

Forward Pass Equations

Straight Through Estimate

h

Device N-1

........

Matrix Subtraction

..... 0.035

Matrix Addition
Forward Pass

...

........

........

..

...

0.368 -0.156

Backward Pass
Inference Computation

Intermediate Representations (Activations)

FloatLM
Y = XW T
TriLM
Pn Pm
1
γ = ϵ + nm
 i=1  j=1 |Wij| 
Wij
d
W
, −1 , 1
ij = round min max
γ
g
d
W
ij = γ Wij
fT
Y = XW

.....

PBiLM
Pm
n
1
α = nm
|Wij |
i=1
Pj=1
Pm
n
1
d
Wij = sign(Wij − nm
i=1
j=1 Wij )
g
d
Wij = αWij
fT
Y = XW

...

0 1 ..... -1 0

μabs

..

.....

...

-0.763 ..... 0.147

* 0.218

...

...

Device N

...

...

-0.510 ..... 0.066

-1 1 ..... 0 0

-0.016 0.281 ..... -0.674 0.009

...

..

...

.....

-0.313 0.299 ..... -0.042 -0.552

.....

...

.

...

...

...

........

-0.431 -0.112 ..... 0.639

...

..

...

Latent Weights ( W )

0.246 -0.279 ..... 0.175 0.036

0.130 ..... -0.384

γ = 0.218

Figure 4: The computational flow of the forward, backward, and inference processes in TriLM’s linear layer
with N-Way model parallelism is shown on the left. Additionally, we provide the equations (on left) for the
forward pass during the training of our FloatLM, TriLM, and BiLM (for details, see 1).
TriLM is a LLaMa-style (Touvron et al., 2023a) autoregressive transformers (Vaswani et al., 2017)
model with RMSNorm (Zhang & Sennrich, 2019), SwiGLU Gated MLP (Shazeer, 2020), Rotary
Position Embedding (RoPE) (Su et al., 2021), Multi-Headed Attention and no bias terms. In TriLMs,
we represent the weights of all the linear layers in one of three possible ternary states {−1, 0, 1},
along with an additional floating-point number called ‘scale value’ shared across the matrix. During
training, we maintain the latent (or master) weights in floating point precision, allowing for the
accumulation of small updates over iterations that eventually contribute to a transition in the estimated
ternary state of a parameter. As shown in Figure 4, during the forward pass, we ternarize the floating
point latent weights on-the-fly. This process involves calculating the scale value to the absolute mean
of the latent weights. After scaling, we estimate the ternary state of each parameter by rounding off
to the nearest ternary state. In the backward pass, we use a straight-through estimator to compute
gradients of the floating point latent weights (Bengio et al., 2013). Since we only need the scale
values and the ternarized states during inference, we achieve a significant reduction in both model size
and inference time at larger scales compared to FloatLMs. We provide a formal description of these
forward pass, backward pass, and inference time equations in the Appendix (§A.1). We represent the
embedding and language model head in half-precision floating point across all our experiments.
Since, training of TriLMs requires on-the-fly computation of scale values, synchronizing for a
single scalar across devices in model parallel training (Shoeybi et al., 2019) can cause significant
communication overhead. To address this, we allow each device to independently compute these scale
values over its own matrix shard. This approach introduces additional artifacts, where the number
of scalar values for each matrix is the same as the degree of model parallelism used during training
(see appendix A.6). However, the impact on modelsize is negligible, for matrices with millions of
parameters, we only add 6 scalar values each.
Concurrent research on low-bit LLMs, like BitNet 1.58 (Ma et al., 2024), also demonstrates the
feasibility of training LLMs with ternary weights. Our experiments demonstrate that TriLM’s
architecture not only outperforms BitNet b1.58 but is also simpler and more stable. Moreover, both
the larger BitNet 1.3B model presented in their paper and our replication of the BitNet 1.1B model
5

Published as a conference paper at ICLR 2025

underperform compared to our TriLM 1.1B on commonsense and reasoning benchmarks. We provide
further details on these comparisons in Appendix A.7.

4

S PECTRA SUITE : S PANNING PARAMETERS AND B ITWIDTHS

The Spectra suite includes comprehensive families of large language models designed to span different
parameter counts and bit-widths. This suite includes three main model families: TriLMs, FloatLMs,
and QuantLMs (3, 4, 6, and 8 bits). Drawing inspiration from established model suites such as those
by Biderman et al. (2023), Liu et al. (2023c), and Groeneveld et al. (2024), Spectra aims to facilitate
scientific research on low-bitwidth LLMs, interpretability, and safety.
4.1

OVERVIEW OF S PECTRA S UITE

The spectra suite of LLMs is distinguished by several key attributes listed below.
1. Scale. The open suite spans a broad spectrum of scales across parameter count (99M to
3.9B), sizes (9 ∗ 108 to 6.4 ∗ 1010 bits) and bitwidths (1.58 bits to 16 bits).
2. Uniform Training. All the TriLMs and FloatLMs are trained on identical data sequences,
specifically a 300B subset of Slim Pajama (Soboleva et al., 2023) dataset (see Appendix
A.2), ensuring training consistency. Data ordering and batch sizes are also kept consistent
within each model family. All QuantLMs undergo quantization using the same calibration
data on identical data sequences, maintaining uniformity in model quantization procedures.
3. Public Accessibility. Training data as well as intermediate training checkpoints of TriLMs
and FloatLms are publicly available for future research.
4. Consistent Model Parameter Mapping. All the model families maintain a consistent
one-to-one mapping in terms of parameter count for studying scaling phenomena.
Figure 11 demonstrates the Spectra LM suite spanning across two dimensions - size (bits) and
parameters. For each parameter count, we have 6 models across different bitwidths. Due to the
availability of FloatLM, Spectra can easily be extended with new QuantLMs by using different Post
Training Quantization methods. We provide details on the dataset and tokenizer, pretraining setup,
hyperparameters, and optimization schedule across the families of models in Appendix A. Moreover,
we describe our FloatLMs and their quantized versions in the next section.
4.2

F LOAT LM S AND Q UANT LM S

Family of FloatLMs. We utilize LLaMa-style (Touvron et al., 2023a) architecture akin to TriLM.
In FloatLMs, we represent the parameters in the weight matrices of linear layers as floating-point
numbers (FP16/BF16). The optimization schedule for FloatLM follows a cosine decay scheduling
with weight decay and includes a learning rate warmup. This is consistent with the practices
established in models such as Pythia, OLMo, LLM360. For more details, refer to the Appendix (A.4).
Family of QuantLMs. Recently, data-aware quantization techniques like GPTQ (Frantar et al., 2022)
have emerged as efficient solutions for near-lossless weight quantization down to 4-bit precision
(Dettmers & Zettlemoyer, 2023). In this work, we implement GPTQ post-training quantization
to FloatLM, creating the QuantLM family of models across 3, 4, 6, and 8 bits. We quantize all
transformer layer weights. For 3-bit and 4-bit quantization, we employ a group size of 128, which
results in effective bit rates of 3.25 and 4.25 bits per parameter, respectively. We refine our approach
by incorporating best practices from recent research by Malinovskii et al. (2024), particularly in
terms of calibration data and scaling it to a million tokens for improved reconstruction. To ensure a
fair comparison with TriLM, we maintain certain components in their original precision. Specifically,
we do not quantize the embedding, language model head, or activations. Additionally, we employ
symmetric quantization (without zero offset) for its simplicity, fast inference kernels support (Frantar
& Alistarh, 2024), and comparable performance to asymmetric quantization, which uses separate
zero offsets and scale values for each group. This approach also ensures consistency and facilitates a
fair comparison with TriLMs. Notably, our Spectra suite is designed with flexibility in mind, allowing
for easy extension to other quantization methods as needed.
6

Published as a conference paper at ICLR 2025

4.3

T RAINING DYNAMICS
TriLM: Tokens Trained vs Training Loss

TriLM/FloatLM Tokens Trained vs Training Loss

3.4
3.4

3.2

3.2
3.0

Training Loss

Training Loss

3.0

99M
190M
390M
560M
830M
1.1B
1.5B
2.4B
3.9B

2.8
2.6
2.4
2.2
100B

Tokens Trained

200B

2.8
2.6

FloatLM 1.1B
FloatLM 1.5B
TriLM 2.4B
FloatLM 2.4B

2.4
2.2

300B

100B

(a) Training loss over time for TriLMs.

Tokens Trained

200B

300B

(b) Training loss of TriLM vs FloatLM.

Figure 5: Training Cross Entropy Loss across steps for the TriLM family of models. At the halfway point
(150B tokens) when we lower the peak learning rate, we observe a sudden drop in training loss. In the two-third
way, removing weight decay leads to faster convergence.
Optimizing low bitwidth neural networks, such as in Quantization Aware Training (Liu et al., 2023b;
Yuan et al., 2024; Bethge et al., 2018; Le & Li, 2023), requires specific considerations like higher
initial learning rates and reduced weight decay. Our optimization schedule for TriLM incorporates
two key interventions within a standard linear decay learning rate schedule with warmup and weight
decay (L2 regularization). First, we reduce the peak learning rate at approximately the halfway point
of training. Second, we remove the weight decay regularization about two-thirds into the training, as
ternarization provides sufficient regularization (Courbariaux et al., 2016b). Figure 9 in Appendix A.5
shows an ablation study for a 1.1B parameter model trained on 100B tokens, demonstrating that both
interventions are necessary to achieve the lowest validation perplexity.
Figure 5a illustrates the training loss curves for all the TriLMs trained and Figure 5b shows the
relative training loss of a TriLM in comparison to two smaller FloatLMs. The loss curves demonstrate
a continuous and consistent improvement in TriLMs with an increase in parameter count. During
training, we make several key observations. First, minor spikes and drops in training loss occurred
consistently across different TriLM scales at the same token counts, as all models were trained on
identical data with the same ordering. Notably, the two largest models—TriLM 2.4B and TriLM
3.9B—each experienced a large loss spike in the first half of training. Second, adjusting the learning
rate at the midpoint led to a sharp decline in training loss over a few hundred million tokens, though
its impact varied by model size: for the larger models (2.4B and 3.9B), the rate of loss reduction
returned to the prior pace after the initial sharp drop, while for smaller models (1.1B and 1.5B), the
loss reduction plateaued, and models below 1B parameters saw an increase in training loss. Lastly,
the removal of weight decay at the two-thirds mark accelerated convergence for all models, with the
effect being most pronounced in the largest TriLM models.
4.4

S CALING L AWS

In this section, we derive the scaling law for TriLMs and compare it to that of FloatLMs. All
models, including our largest 3.9B parameter model, are trained on 300B tokens, placing them in
the overtrained regime as determined by Chinchilla’s Hoffmann et al. (2022) compute-optimal token
calculation. Figures 6a and 6b illustrate the final validation loss across different model size in terms
of bits and number of parameters (N ) respectively. In terms of effective model size in bits (6a),
which is crucial during inference, TriLMs exhibit significantly better scaling than FloatLMs. Notably,
TriLM 3.9B validation error matches with FloatLMs 1.1B, which is nearly 1.7 times larger in terms
of effective bit size. To investigate the scaling behaviour in terms of N with fixed data, we fit the
validation loss to a power-law with offset1 Hoffmann et al. (2022) (see Figure 6b and Appendix C):

Atype
ATriLM = 185,
αTriLM = 0.26,
ϵTriLM = 1.76
(1)
Ltype (N ) = αtype + ϵtype , where
AFloatLM = 159, αFloatLM = 0.26, ϵFloatLM = 1.67
N
1

derived using a fixed data regime of 300B tokens

7

Published as a conference paper at ICLR 2025

We employ the Levenberg-Marquardt algorithm (Levenberg (1944); Marquardt (1963)) for efficient
non-linear least squares fitting. Both FloatLM and TriLM share the scaling exponent α = 0.26,
indicating similar scaling behavior with the number of parameters N . However, the offset terms
ϵTriLM = 1.76 and ϵFloatLM = 1.67 reveal that their validation losses converge as N increases.
Although TriLM starts with a higher coefficient A = 185, suggesting greater initial validation
loss than FloatLM (A = 159), this difference becomes insignificant with larger N , aligning their
performance at asymptotic scales as shown in Figure 6b and 17.
Scaling with Bitsize

Scaling Law Fits
TriLM
FloatLM

3.2

TriLM : y = 185 × x 0.26 + 1.76
FloatLM : y = 159 × x 0.26 + 1.67

4.0

3.0

Validation Loss

Validation Loss

3.5

2.8

3.0

2.6

2.5

2.4
2.2

2.0
0

1

2

3

4

Model Size (in bits)

5

6

108

109

1010

Model Size (in num of params) - Log Scale

1e10

(a) Scaling laws - perplexity across size (bits).

(b) Scaling laws - perplexity across parameters.

Figure 6: Final validation loss across sizes (in bits) and parameters. TriLMs with increasing size offer better
performance than FloatLMs of the same number of bits; and the gap in validation perplexity closes at scale.

Despite the observed differences in validation loss at the scale of models considered in this work, we
demonstrate in Section 5 that at 3.9B parameters, TriLM offers competitive downstream performance
compared to a FloatLM of the same parameter count across a variety of benchmarks in commonsense
reasoning and knowledge-based tasks. Moreover, as discussed in Appendix §D.4, both models show
similar perplexity on clean datasets such as Penn Tree Bank and OpenAI’s Lambda. However, the
gap in perplexity is observed in overlapping web-based datasets like Dolma and RefinedWeb.

5

R ESULTS

We evaluate the families of LLMs on three aspects - commonsense & reasoning tasks, knowledgebased tasks, and toxicity, all of which are crucial measures of their downstream performance. Readers
may refer to the appendix for more details regarding the benchmarks (§D).
Commonsense and Reasoning. We evaluate Spectra Suite models using eight distinct commonsense and reasoning benchmarks consisting of tasks from logical and reasoning questions to grounded
and physical commonsense tasks: Arc Easy, Arc Challenge (Clark et al., 2018), BoolQ (Clark et al.,
2019), HellaSWAG (Zellers et al., 2019), WinoGrande (Sakaguchi et al., 2021), PIQA (Bisk et al.,
2019), LAMBADA (Paperno et al., 2016), LogiQA (Liu et al., 2021), all under zero-shot settings.
Figures 1a and 1b display the average performance of the LLMs on the first six benchmarks across
size in bits and number of params. Figures 1c and 1d present the performance for the LAMBADA
dataset. The results show that TriLMs consistently demonstrate superior performance for their size
across all benchmarks at the 2.4B and 3.9B parameter scales. At the largest scale of 3.9B, TriLM
surpasses FloatLM on LAMBADA and achieves competitive average scores across six benchmarks.
Additionally, TriLMs at the largest scales consistently outperform 4-bit QuantLMs of equivalent
parameter count. However, across the considered scales, all LLMs show poor performance on
LogiQA, making it difficult to identify a clear performance trend. For detailed benchmarking across
all datasets –see Tables 7, 8 and 10.
Knowledge. Several downstream practical uses of LLMs require them to have knowledge about
common subjects like science or politics. To evaluate the performance of LLMs on these subjects,
we use SciQ (Welbl et al., 2017), TriviaQA (Joshi et al., 2017) and MMLU (Hendrycks et al., 2021)
benchmarks in zero-shot settings. Figures 7a and 7b show the accuracy of the Spectra suite LLMs on
SciQ across size in bits and parameter counts. Figures 21c and 21d depict the accuracy for TriviaQA,
while 8a and 8b do the same for MMLU. Across both benchmarks, at large 2.4B+ scales, TriLMs offer
8

Published as a conference paper at ICLR 2025

SciQ Accuracy (Normalized) Across Parameters

FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM

60

50

1

10

20
30
40
50
Size in bits (109)

20

80

15

70

60

50

60

20

(a) vs. Size in SciQ

FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM
190M

560M
1.5B
Parameters

10
FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM

5

1

3.9B

(b) vs. Params in SciQ

10

20
30
40
50
Size in bits (109)

Exact Match (log scale)

70

TriviaQA Exact Match Across Parameters

TriviaQA Exact Match Across Size (Bits)

Exact Match

Accuracy (Normalized)

80

Accuracy (Normalized) (log scale)

SciQ Accuracy (Normalized) Across Size (Bits)

10

FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM

5

2
1

60

(c) vs. Size in TriviaQA

190M

560M
1.5B
Parameters

3.9B

(d) vs. Params in TriviaQA

Figure 7: Performance of ternary TriLM, FloatLM and quantized QuantLM (3-bit & 4-bit) models on SciQ and
TriviaQA tasks across Size (Bits) and Parameters. Refer to Tables 10 and 15 for details.

the best performance at a given size (bits). Surprisingly, despite having fewer bits, the knowledge
capacity of TriLM does not have any significant degradation as observed in the case of QuantLMs
(Allen-Zhu & Li, 2024). This indicates that low-bitwidth LLMs like TriLMs have similar knowledge
capacity to FloatLMs, indicating that knowledge capacity is parameterized via the presence and
nature of a connection (+1 or -1), rather than its strength. Tables 10 and 15 expand on these results.

32

30

30

Acc

Acc (log scale)

32

28
FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM

26
24

1

10

20
30
40
50
Size in bits (109)

60

(a) Vs. Size (Bits)- Avg

MMLU Acc Across Parameters

MMLU Stem Acc Across Size (Bits)

29

FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM

28

27

27

26

28

25
24

26

FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM

23
24

190M

560M
1.5B
Parameters

22

3.9B

(b) Vs. Parameters- Avg

29

28

Acc (log scale)

34

Acc

MMLU Acc Across Size (Bits)

34

1

10

20
30
40
50
Size in bits (109)

(c) Vs. Size- STEM

60

MMLU Stem Acc Across Parameters
FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM

26
25
24
23
22

190M

560M
1.5B
Parameters

3.9B

(d) Vs. Parameters- STEM

Figure 8: MMLU Accuracy for ternary TriLM, FloatLM and quantized QuantLM (3-bit & 4-bit) models across
Size and Parameters. Please refer to Table 16 for details.

Toxicity. We evaluate the Spectra suite across various safety and toxicity benchmarks of TruthfulQA
(Lin et al., 2021), Big Bench BBQ Lite (Parrish et al., 2022) and CrowsPairs (Nangia et al., 2020).
These scores are listed in the Appendix in Table 15. We observe that none of the LLMs, even those
with up to 3.9 billion parameters and trained on 300 billion tokens, perform significantly better than
random guessing on the TruthfulQA benchmark. For the other two datasets, there is a noticeable
correlation between the occurrence of toxicity and stereotypes and the LLMs’ performance on various
tasks. In particular, TriLMs with fewer than one billion parameters exhibit less stereotyping than
FloatLMs with a similar parameter count. However, this difference diminishes as the scale increases,
with TriLM 2.4B and TriLM 3.9B exhibiting biases comparable to those of FloatLM 2.4B and
FloatLM 3.9B, respectively, on these benchmarks. This suggests that, although TriLMs initially
show reduced bias compared to similarly sized FloatLMs, their performance aligns with FloatLMs of
equivalent parameter counts at larger scales. This also highlights that TriLMs exhibit considerably
more stereotyping than FloatLMs of comparable size (measured in bits), yet perform comparably to
FloatLMs with similar parameter counts.

6

R ELATED W ORK

Quantization of Large Language Models after Training. Post-training quantization (PTQ)
algorithms convert a pretrained high-precision model (FP32 / FP16 / BF16) into a lower precision
format without requiring the original training process (Cai et al., 2020; Hubara et al., 2020; Choukroun
et al., 2019). These methods can be either data-independent or need a small calibration dataset.
Additionally, PTQ for LLMs presents unique challenges due to numerical outliers in both weights
and activations (Bondarenko et al., 2021). GPTQ (Frantar et al., 2022) is a state-of-the-art one-shot
9

Published as a conference paper at ICLR 2025

weight quantization method aimed at finding a matrix of quantized weights (say Ŵ ) that minimizes
the squared error relative to the full precision layer output. By leveraging second-order information,
GPTQ derives a closed-form solution to this optimization problem, making it scalable to large LLMs.
Other methods (Dettmers et al., 2023; Lin et al., 2024; Lee et al., 2024) emphasize the importance of
outlier weights that correspond to high-magnitude activations. Some recent methods also quantized
activation along with the weights (Xiao et al., 2024; Yao et al., 2022; 2023). Ahmadian et al. (2023)
demonstrate that large activation outliers can be effectively mitigated at scale by making appropriate
optimization decisions during the pretraining phase.
Training Language Models At Lower Precision. Several prominent language models such as GPT
(Brown et al., 2020a), NeoX (Black et al., 2022), Llama and Pythia families have been traditionally
trained using mixed precision (FP32/FP16 or FP32/BF16) (Micikevicius et al., 2018) or half-precision
(FP16/BF16) (Kalamkar et al., 2019). Recently, Tao et al. (2022) introduced QuantGPT, a model
that incorporates contrastive and logit distillation from a full-precision teacher to a quantized student
model during pretraining. Further developments, such as BitNet (Wang et al., 2023) and BitNet b1.58
(Ma et al., 2024), have specifically focused on quantization-aware training for extremely low-bitwidth
networks in transformer-based models. In their work, models are trained at low “effective” precision
of binary and ternary respectively - where the latent (or master) weights during training are maintained
in higher precision like FP16. The model weights are binarized or ternarized on the fly during the
forward pass and gradients are backpropagated for the latent weights using the straight-through
estimator (Courbariaux et al., 2016b). Prior works emphasize the importance of maintaining latent
(or master) weights at high precision to allow accumulation of small updates during training - for
example, Peng et al. (2023) observed a significant performance drop on the language model when
the latent (or master) model weights were switch from 16-bits (FP16/BF16) to 8-bits (FP8) during
training. Concurrent architectural improvements such as Flash Attention (Dao et al., 2022; Dao,
2023), the mixture of experts (Zoph et al., 2022), xLSTM Beck et al. (2024) and state space models
(Gu & Dao, 2024; Dao & Gu, 2024; Gu et al., 2022) complement these advancements in lower
precision modeling.

7

C ONCLUSION AND F UTURE W ORK

In this work, we address memory limitations in large language model (LLM) deployment by exploring
both post-training quantization and direct low-bitwidth training. We introduce the Spectra LLM suite,
featuring 54 models ranging from 99 million to 3.9 billion parameters, trained on 300 billion tokens.
This suite includes Float16 LLMs (FloatLMs), quantized QuantLMs (3–8 bits), and our proposed
ternary LLMs (TriLMs). Our findings reveal that TriLMs scale better than their half-precision Float16
counterparts in terms of effective model bit size, and they can achieve comparable validation loss
when scaled to a large number of parameters. Additionally, our results demonstrate that TriLMs
surpass other models in bit-size efficiency and achieve performance comparable to FloatLMs at 3
billion+ parameters across multiple benchmarks.
Future work should address the remaining challenges of toxicity, stereotyping, and performance gaps
on web corpora associated with low-bitwidth models. Investigating scaling laws across diverse data
regimes and bit sizes in low-bitwidth models trained with quantization-aware training can provide
deeper insights into their behavior and limitations. Additionally, combining these models with statespace architectures like Mamba Gu & Dao (2024) could further enhance efficiency and performance
without sacrificing accuracy. These research directions hold promise in advancing efficient language
modeling further.

ACKNOWLEDGEMENT
We acknowledge the support from the Mozilla Responsible AI Grant, the Canada CIFAR AI Chair
Program and the Canada Excellence Research Chairs Program. This research was enabled by the
computational resources provided by the Summit supercomputer, awarded through the Frontier DD
allocation and INCITE 2023 program for the project "Scalable Foundation Models for Transferable
Generalist AI" and SummitPlus allocation in 2024. These resources were supplied by the Oak Ridge
Leadership Computing Facility at the Oak Ridge National Laboratory, with support from the Office
of Science of the U.S. Department of Energy.
10

Published as a conference paper at ICLR 2025

R EFERENCES
Arash Ahmadian, Saurabh Dash, Hongyu Chen, Bharat Venkitesh, Stephen Gou, Phil Blunsom,
Ahmet Üstün, and Sara Hooker. Intriguing properties of quantization at scale, 2023. URL
https://arxiv.org/abs/2305.19268.
AI@Meta. Llama 3 model card. 2024. URL https://github.com/meta-llama/llama3/
blob/main/MODEL_CARD.md.
Zeyuan Allen-Zhu and Yuanzhi Li. Physics of language models: Part 3.3, knowledge capacity scaling
laws, 2024. URL https://arxiv.org/abs/2404.05405.
AMD Team. Amd instinct mi210 accelerator. https://www.amd.com/en/products/
accelerators/instinct/mi200/mi210.html, 2022a. Accessed: July 3, 2024.
AMD Team. Amd instinct mi250 and mi250x accelerators. https://www.amd.com/system/
files/documents/amd-instinct-mi200-datasheet.pdf, 2022b. Accessed: July
3, 2024.
AMD Team. Amd instinct mi300a accelerator. https://www.amd.com/en/products/
accelerators/instinct/mi300/mi300a.html, 2023a. Accessed: July 3, 2024.
AMD Team. Amd instinct mi300x accelerator. https://www.amd.com/en/products/
accelerators/instinct/mi300/mi300x.html, 2023b. Accessed: July 3, 2024.
AMD
Team.
Amd
instinct
mi325x
accelerator.
https://
ir.amd.com/news-events/press-releases/detail/1201/
amd-accelerates-pace-of-data-center-ai-innovation-and, 2024.
Accessed: July 3, 2024.
Alex Andonian, Quentin Anthony, Stella Biderman, Sid Black, Preetham Gali, Leo Gao, Eric Hallahan, Josh Levy-Kramer, Connor Leahy, Lucas Nestler, Kip Parker, Michael Pieler, Jason Phang,
Shivanshu Purohit, Hailey Schoelkopf, Dashiell Stander, Tri Songz, Curt Tigges, Benjamin Thérien,
Phil Wang, and Samuel Weinbach. GPT-NeoX: Large Scale Autoregressive Language Modeling in
PyTorch, 9 2023. URL https://www.github.com/eleutherai/gpt-neox.
Maximilian Beck, Korbinian Pöppel, Markus Spanring, Andreas Auer, Oleksandra Prudnikova,
Michael Kopp, Günter Klambauer, Johannes Brandstetter, and Sepp Hochreiter. xlstm: Extended
long short-term memory. arXiv preprint arXiv:2405.04517, 2024.
Yoshua Bengio, Nicholas Léonard, and Aaron Courville. Estimating or propagating gradients through
stochastic neurons for conditional computation, 2013.
Joseph Bethge, Marvin Bornstein, Adrian Loy, Haojin Yang, and Christoph Meinel. Training
competitive binary neural networks from scratch. ArXiv, abs/1812.01965, 2018. URL https:
//api.semanticscholar.org/CorpusID:54458838.
Stella Biderman, Hailey Schoelkopf, Quentin Anthony, Herbie Bradley, Kyle O’Brien, Eric Hallahan,
Mohammad Aflah Khan, Shivanshu Purohit, USVSN Sai Prashanth, Edward Raff, Aviya Skowron,
Lintang Sutawika, and Oskar van der Wal. Pythia: A suite for analyzing large language models
across training and scaling, 2023.
Lukas Biewald. Experiment tracking with weights and biases, 2020. URL https://www.wandb.
com/. Software available from wandb.com.
Yonatan Bisk, Rowan Zellers, Ronan Le Bras, Jianfeng Gao, and Yejin Choi. Piqa: Reasoning about
physical commonsense in natural language. In AAAI Conference on Artificial Intelligence, 2019.
URL https://api.semanticscholar.org/CorpusID:208290939.
Sid Black, Stella Biderman, Eric Hallahan, Quentin Anthony, Leo Gao, Laurence Golding, Horace He,
Connor Leahy, Kyle McDonell, Jason Phang, Michael Pieler, USVSN Sai Prashanth, Shivanshu
Purohit, Laria Reynolds, Jonathan Tow, Ben Wang, and Samuel Weinbach. Gpt-neox-20b: An
open-source autoregressive language model, 2022. URL https://arxiv.org/abs/2204.
06745.
11

Published as a conference paper at ICLR 2025

Yelysei Bondarenko, Markus Nagel, and Tijmen Blankevoort. Understanding and overcoming the
challenges of efficient transformer quantization, 2021. URL https://arxiv.org/abs/
2109.12948.
Tom B. Brown, Benjamin Mann, Nick Ryder, Melanie Subbiah, Jared Kaplan, Prafulla Dhariwal,
Arvind Neelakantan, Pranav Shyam, Girish Sastry, Amanda Askell, Sandhini Agarwal, Ariel
Herbert-Voss, Gretchen Krueger, Tom Henighan, Rewon Child, Aditya Ramesh, Daniel M. Ziegler,
Jeffrey Wu, Clemens Winter, Christopher Hesse, Mark Chen, Eric Sigler, Mateusz Litwin, Scott
Gray, Benjamin Chess, Jack Clark, Christopher Berner, Sam McCandlish, Alec Radford, Ilya
Sutskever, and Dario Amodei. Language models are few-shot learners, 2020a. URL https:
//arxiv.org/abs/2005.14165.
Tom B. Brown, Benjamin Mann, Nick Ryder, Melanie Subbiah, Jared Kaplan, Prafulla Dhariwal,
Arvind Neelakantan, Pranav Shyam, Girish Sastry, Amanda Askell, Sandhini Agarwal, Ariel
Herbert-Voss, Gretchen Krueger, Tom Henighan, Rewon Child, Aditya Ramesh, Daniel M. Ziegler,
Jeffrey Wu, Clemens Winter, Christopher Hesse, Mark Chen, Eric Sigler, Mateusz Litwin, Scott
Gray, Benjamin Chess, Jack Clark, Christopher Berner, Sam McCandlish, Alec Radford, Ilya
Sutskever, and Dario Amodei. Language models are few-shot learners, 2020b.
Yaohui Cai, Zhewei Yao, Zhen Dong, Amir Gholami, Michael W. Mahoney, and Kurt Keutzer. Zeroq:
A novel zero shot quantization framework, 2020. URL https://arxiv.org/abs/2001.
00281.
Yoni Choukroun, Eli Kravchik, Fan Yang, and Pavel Kisilev. Low-bit quantization of neural networks
for efficient inference, 2019. URL https://arxiv.org/abs/1902.06822.
Christopher Clark, Kenton Lee, Ming-Wei Chang, Tom Kwiatkowski, Michael Collins, and Kristina
Toutanova. BoolQ: Exploring the surprising difficulty of natural yes/no questions. In Jill
Burstein, Christy Doran, and Thamar Solorio (eds.), Proceedings of the 2019 Conference of
the North American Chapter of the Association for Computational Linguistics: Human Language Technologies, Volume 1 (Long and Short Papers), pp. 2924–2936, Minneapolis, Minnesota, June 2019. Association for Computational Linguistics. doi: 10.18653/v1/N19-1300. URL
https://aclanthology.org/N19-1300.
Peter Clark, Isaac Cowhey, Oren Etzioni, Tushar Khot, Ashish Sabharwal, Carissa Schoenick, and
Oyvind Tafjord. Think you have solved question answering? try arc, the ai2 reasoning challenge,
2018. URL https://api.semanticscholar.org/CorpusID:3922816.
Matthieu Courbariaux, Yoshua Bengio, and Jean-Pierre David. Binaryconnect: Training deep neural
networks with binary weights during propagations. Advances in neural information processing
systems, 28:3123–3131, 2016a.
Matthieu Courbariaux, Yoshua Bengio, and Jean-Pierre David. Binaryconnect: Training deep neural
networks with binary weights during propagations, 2016b. URL https://arxiv.org/abs/
1511.00363.
Tri Dao. Flashattention-2: Faster attention with better parallelism and work partitioning, 2023. URL
https://arxiv.org/abs/2307.08691.
Tri Dao and Albert Gu. Transformers are ssms: Generalized models and efficient algorithms through
structured state space duality, 2024. URL https://arxiv.org/abs/2405.21060.
Tri Dao, Daniel Y. Fu, Stefano Ermon, Atri Rudra, and Christopher Ré. Flashattention: Fast and
memory-efficient exact attention with io-awareness, 2022. URL https://arxiv.org/abs/
2205.14135.
Tim Dettmers and Luke Zettlemoyer. The case for 4-bit precision: k-bit inference scaling laws, 2023.
Tim Dettmers, Ruslan Svirschevski, Vage Egiazarian, Denis Kuznedelev, Elias Frantar, Saleh Ashkboos, Alexander Borzunov, Torsten Hoefler, and Dan Alistarh. Spqr: A sparse-quantized representation for near-lossless llm weight compression, 2023. URL https://arxiv.org/abs/
2306.03078.
12

Published as a conference paper at ICLR 2025

Vage Egiazarian, Andrei Panferov, Denis Kuznedelev, Elias Frantar, Artem Babenko, and Dan
Alistarh. Extreme compression of large language models via additive quantization, 2024. URL
https://arxiv.org/abs/2401.06118.
Elias Frantar and Dan Alistarh. Marlin: a fast 4-bit inference kernel for medium batchsizes. https:
//github.com/IST-DASLab/marlin, 2024.
Elias Frantar, Saleh Ashkboos, Torsten Hoefler, and Dan Alistarh. GPTQ: Accurate post-training
compression for generative pretrained transformers. arXiv preprint arXiv:2210.17323, 2022.
Leo Gao, Stella Biderman, Sid Black, Laurence Golding, Travis Hoppe, Charles Foster, Jason Phang,
Horace He, Anish Thite, Noa Nabeshima, Shawn Presser, and Connor Leahy. The pile: An 800gb
dataset of diverse text for language modeling, 2020.
Leo Gao, Jonathan Tow, Baber Abbasi, Stella Biderman, Sid Black, Anthony DiPofi, Charles Foster,
Laurence Golding, Jeffrey Hsu, Alain Le Noac’h, Haonan Li, Kyle McDonell, Niklas Muennighoff,
Chris Ociepa, Jason Phang, Laria Reynolds, Hailey Schoelkopf, Aviya Skowron, Lintang Sutawika,
Eric Tang, Anish Thite, Ben Wang, Kevin Wang, and Andy Zou. A framework for few-shot
language model evaluation, 12 2023. URL https://zenodo.org/records/10256836.
Amir Gholami, Zhewei Yao, Sehoon Kim, Coleman Hooper, Michael W. Mahoney, and Kurt Keutzer.
Ai and memory wall, 2024. URL https://arxiv.org/abs/2403.14123.
Google TPU Team. Google cloud tpu v3. https://cloud.google.com/tpu/docs/v3,
2018. Accessed: July 3, 2024.
Google TPU Team. Google cloud tpu v4. https://cloud.google.com/tpu/docs/v4,
2021. Accessed: July 3, 2024.
Google TPU Team. Google cloud tpu v5e. https://cloud.google.com/tpu/docs/v5e,
2023a. Accessed: July 3, 2024.
Google TPU Team. Google cloud tpu v5p. https://cloud.google.com/tpu/docs/v5p,
2023b. Accessed: July 3, 2024.
Dirk Groeneveld, Iz Beltagy, Pete Walsh, Akshita Bhagia, Rodney Kinney, Oyvind Tafjord,
Ananya Harsh Jha, Hamish Ivison, Ian Magnusson, Yizhong Wang, Shane Arora, David Atkinson,
Russell Authur, Khyathi Raghavi Chandu, Arman Cohan, Jennifer Dumas, Yanai Elazar, Yuling Gu,
Jack Hessel, Tushar Khot, William Merrill, Jacob Morrison, Niklas Muennighoff, Aakanksha Naik,
Crystal Nam, Matthew E. Peters, Valentina Pyatkin, Abhilasha Ravichander, Dustin Schwenk,
Saurabh Shah, Will Smith, Emma Strubell, Nishant Subramani, Mitchell Wortsman, Pradeep
Dasigi, Nathan Lambert, Kyle Richardson, Luke Zettlemoyer, Jesse Dodge, Kyle Lo, Luca Soldaini, Noah A. Smith, and Hannaneh Hajishirzi. Olmo: Accelerating the science of language
models, 2024. URL https://arxiv.org/abs/2402.00838.
Albert Gu and Tri Dao. Mamba: Linear-time sequence modeling with selective state spaces, 2024.
URL https://arxiv.org/abs/2312.00752.
Albert Gu, Karan Goel, and Christopher Ré. Efficiently modeling long sequences with structured
state spaces. In The International Conference on Learning Representations (ICLR), 2022.
Dan Hendrycks, Collin Burns, Steven Basart, Andy Zou, Mantas Mazeika, Dawn Song, and Jacob
Steinhardt. Measuring massive multitask language understanding. Proceedings of the International
Conference on Learning Representations (ICLR), 2021.
Jordan Hoffmann, Sebastian Borgeaud, Arthur Mensch, Elena Buchatskaya, Trevor Cai, Eliza
Rutherford, Diego de Las Casas, Lisa Anne Hendricks, Johannes Welbl, Aidan Clark, Tom
Hennigan, Eric Noland, Katie Millican, George van den Driessche, Bogdan Damoc, Aurelia Guy,
Simon Osindero, Karen Simonyan, Erich Elsen, Jack W. Rae, Oriol Vinyals, and Laurent Sifre.
Training compute-optimal large language models, 2022. URL https://arxiv.org/abs/
2203.15556.
13

Published as a conference paper at ICLR 2025

Shengding Hu, Yuge Tu, Xu Han, Chaoqun He, Ganqu Cui, Xiang Long, Zhi Zheng, Yewei Fang,
Yuxiang Huang, Weilin Zhao, Xinrong Zhang, Zheng Leng Thai, Kaihuo Zhang, Chongyi Wang,
Yuan Yao, Chenyang Zhao, Jie Zhou, Jie Cai, Zhongwu Zhai, Ning Ding, Chao Jia, Guoyang
Zeng, Dahai Li, Zhiyuan Liu, and Maosong Sun. Minicpm: Unveiling the potential of small
language models with scalable training strategies, 2024. URL https://arxiv.org/abs/
2404.06395.
Wei Huang, Xudong Ma, Haotong Qin, Xingyu Zheng, Chengtao Lv, Hong Chen, Jie Luo, Xiaojuan
Qi, Xianglong Liu, and Michele Magno. How good are low-bit quantized llama3 models? an
empirical study, 2024. URL https://arxiv.org/abs/2404.14047.
Itay Hubara, Matthieu Courbariaux, Daniel Soudry, Ran El-Yaniv, and Yoshua Bengio. Binarized
neural networks. Neural Computation, 29(1):322–344, 2017.
Itay Hubara, Yury Nahshan, Yair Hanani, Ron Banner, and Daniel Soudry. Improving post training
neural quantization: Layer-wise calibration and integer programming, 2020. URL https:
//arxiv.org/abs/2006.10518.
Intel Gaudi Team. Intel gaudi 2 and gaudi 3 ai accelerators. https://cdrdv2-public.intel.
com/817486/gaudi-3-ai-accelerator-white-paper.pdf, 2024. Accessed: July
3, 2024.
Mandar Joshi, Eunsol Choi, Daniel Weld, and Luke Zettlemoyer. TriviaQA: A large scale distantly supervised challenge dataset for reading comprehension. In Regina Barzilay and Min-Yen Kan (eds.),
Proceedings of the 55th Annual Meeting of the Association for Computational Linguistics (Volume
1: Long Papers), pp. 1601–1611, Vancouver, Canada, July 2017. Association for Computational
Linguistics. doi: 10.18653/v1/P17-1147. URL https://aclanthology.org/P17-1147.
Dhiraj Kalamkar, Dheevatsa Mudigere, Naveen Mellempudi, Dipankar Das, Kunal Banerjee,
Sasikanth Avancha, Dharma Teja Vooturi, Nataraj Jammalamadaka, Jianyu Huang, Hector Yuen,
Jiyan Yang, Jongsoo Park, Alexander Heinecke, Evangelos Georganas, Sudarshan Srinivasan,
Abhisek Kundu, Misha Smelyanskiy, Bharat Kaul, and Pradeep Dubey. A study of bfloat16 for
deep learning training, 2019. URL https://arxiv.org/abs/1905.12322.
Jared Kaplan, Sam McCandlish, Tom Henighan, Tom B. Brown, Benjamin Chess, Rewon Child,
Scott Gray, Alec Radford, Jeffrey Wu, and Dario Amodei. Scaling laws for neural language models,
2020. URL https://arxiv.org/abs/2001.08361.
Sehoon Kim, Coleman Hooper, Amir Gholami, Zhen Dong, Xiuyu Li, Sheng Shen, Michael W.
Mahoney, and Kurt Keutzer. Squeezellm: Dense-and-sparse quantization, 2024.
Diederik P. Kingma and Jimmy Ba. Adam: A method for stochastic optimization, 2017.
Phuoc-Hoan Charles Le and Xinlin Li. Binaryvit: Pushing binary vision transformers towards
convolutional models. In Proceedings of the IEEE/CVF Conference on Computer Vision and
Pattern Recognition (CVPR) Workshops, pp. 4664–4673, June 2023.
Changhun Lee, Jungyu Jin, Taesu Kim, Hyungjun Kim, and Eunhyeok Park. Owq: Outlier-aware
weight quantization for efficient fine-tuning and inference of large language models, 2024. URL
https://arxiv.org/abs/2306.02272.
Kenneth Levenberg. A method for the solution of certain non-linear problems in least squares.
Quarterly of Applied Mathematics, 2:164–168, 1944.
Fengfu Li, Bo Zhang, and Bin Liu. Ternary weight networks. arXiv preprint arXiv:1605.04711,
2016.
Jason Li. Mechanistic interpretability of binary and ternary transformers, 2024. URL https:
//arxiv.org/abs/2405.17703.
Shiyao Li, Xuefei Ning, Luning Wang, Tengxuan Liu, Xiangsheng Shi, Shengen Yan, Guohao
Dai, Huazhong Yang, and Yu Wang. Evaluating quantized large language models, 2024. URL
https://arxiv.org/abs/2402.18158.
14

Published as a conference paper at ICLR 2025

Ji Lin, Jiaming Tang, Haotian Tang, Shang Yang, Wei-Ming Chen, Wei-Chen Wang, Guangxuan
Xiao, Xingyu Dang, Chuang Gan, and Song Han. Awq: Activation-aware weight quantization for
llm compression and acceleration, 2024. URL https://arxiv.org/abs/2306.00978.
Stephanie Lin, Jacob Hilton, and Owain Evans. Truthfulqa: Measuring how models mimic human
falsehoods, 2021.
Jian Liu, Leyang Cui, Hanmeng Liu, Dandan Huang, Yile Wang, and Yue Zhang. Logiqa: a
challenge dataset for machine reading comprehension with logical reasoning. In Proceedings of
the Twenty-Ninth International Joint Conference on Artificial Intelligence, IJCAI’20, 2021. ISBN
9780999241165.
Zechun Liu, Barlas Oguz, Aasish Pappu, Yangyang Shi, and Raghuraman Krishnamoorthi. Binary and
ternary natural language generation, 2023a. URL https://arxiv.org/abs/2306.01841.
Zechun Liu, Barlas Oguz, Changsheng Zhao, Ernie Chang, Pierre Stock, Yashar Mehdad, Yangyang
Shi, Raghuraman Krishnamoorthi, and Vikas Chandra. Llm-qat: Data-free quantization aware
training for large language models. arXiv preprint arXiv:2305.17888, 2023b.
Zhengzhong Liu, Aurick Qiao, Willie Neiswanger, Hongyi Wang, Bowen Tan, Tianhua Tao, Junbo
Li, Yuqi Wang, Suqi Sun, Omkar Pangarkar, Richard Fan, Yi Gu, Victor Miller, Yonghao Zhuang,
Guowei He, Haonan Li, Fajri Koto, Liping Tang, Nikhil Ranjan, Zhiqiang Shen, Xuguang Ren,
Roberto Iriondo, Cun Mu, Zhiting Hu, Mark Schulze, Preslav Nakov, Tim Baldwin, and Eric P.
Xing. Llm360: Towards fully transparent open-source llms, 2023c.
Shuming Ma, Hongyu Wang, Lingxiao Ma, Lei Wang, Wenhui Wang, Shaohan Huang, Li Dong,
Ruiping Wang, Jilong Xue, and Furu Wei. The era of 1-bit llms: All large language models are in
1.58 bits, 2024.
David J. C. MacKay. Information Theory, Inference, and Learning Algorithms. Cambridge University
Press, 2003. ISBN 978-0521642989.
Vladimir Malinovskii, Denis Mazur, Ivan Ilin, Denis Kuznedelev, Konstantin Burlachenko, Kai Yi,
Dan Alistarh, and Peter Richtarik. Pv-tuning: Beyond straight-through estimation for extreme llm
compression, 2024. URL https://arxiv.org/abs/2405.14852.
Donald Marquardt. An algorithm for least-squares estimation of nonlinear parameters. Journal of the
Society for Industrial and Applied Mathematics, 11(2):431–441, 1963.
Paulius Micikevicius, Sharan Narang, Jonah Alben, Gregory Diamos, Erich Elsen, David Garcia,
Boris Ginsburg, Michael Houston, Oleksii Kuchaiev, Ganesh Venkatesh, and Hao Wu. Mixed
precision training, 2018. URL https://arxiv.org/abs/1710.03740.
Tomas Mikolov, Kai Chen, Greg Corrado, and Jeffrey Dean. Efficient estimation of word representations in vector space, 2013. URL https://arxiv.org/abs/1301.3781.
Nikita Nangia, Clara Vania, Rasika Bhalerao, and Samuel R. Bowman. CrowS-Pairs: A Challenge
Dataset for Measuring Social Biases in Masked Language Models. In Proceedings of the 2020
Conference on Empirical Methods in Natural Language Processing, Online, November 2020.
Association for Computational Linguistics.
Behnam Neyshabur, Zhiyuan Li, Srinadh Bhojanapalli, Yann LeCun, and Nathan Srebro. Towards
understanding the role of over-parametrization in generalization of neural networks. In Proceedings
of the International Conference on Learning Representations (ICLR), 2018.
Nvidia, :, Bo Adler, Niket Agarwal, Ashwath Aithal, Dong H. Anh, Pallab Bhattacharya, Annika Brundyn, Jared Casper, Bryan Catanzaro, Sharon Clay, Jonathan Cohen, Sirshak Das, Ayush Dattagupta,
Olivier Delalleau, Leon Derczynski, Yi Dong, Daniel Egert, Ellie Evans, Aleksander Ficek, Denys
Fridman, Shaona Ghosh, Boris Ginsburg, Igor Gitman, Tomasz Grzegorzek, Robert Hero, Jining
Huang, Vibhu Jawa, Joseph Jennings, Aastha Jhunjhunwala, John Kamalu, Sadaf Khan, Oleksii
Kuchaiev, Patrick LeGresley, Hui Li, Jiwei Liu, Zihan Liu, Eileen Long, Ameya Sunil Mahabaleshwarkar, Somshubra Majumdar, James Maki, Miguel Martinez, Maer Rodrigues de Melo, Ivan
Moshkov, Deepak Narayanan, Sean Narenthiran, Jesus Navarro, Phong Nguyen, Osvald Nitski,
15

Published as a conference paper at ICLR 2025

Vahid Noroozi, Guruprasad Nutheti, Christopher Parisien, Jupinder Parmar, Mostofa Patwary,
Krzysztof Pawelec, Wei Ping, Shrimai Prabhumoye, Rajarshi Roy, Trisha Saar, Vasanth Rao Naik
Sabavat, Sanjeev Satheesh, Jane Polak Scowcroft, Jason Sewall, Pavel Shamis, Gerald Shen,
Mohammad Shoeybi, Dave Sizer, Misha Smelyanskiy, Felipe Soares, Makesh Narsimhan Sreedhar,
Dan Su, Sandeep Subramanian, Shengyang Sun, Shubham Toshniwal, Hao Wang, Zhilin Wang,
Jiaxuan You, Jiaqi Zeng, Jimmy Zhang, Jing Zhang, Vivienne Zhang, Yian Zhang, and Chen Zhu.
Nemotron-4 340b technical report, 2024. URL https://arxiv.org/abs/2406.11704.
Nvidia
Team.
Nvidia
tesla
v100
gpu
accelerator.
images.nvidia.com/content/technologies/volta/pdf/
tesla-volta-v100-datasheet-letter-fnl-web.pdf, 2018.
3, 2024.

https://
Accessed: July

Nvidia Team.
Nvidia a100 tensor core gpu.
https://www.nvidia.
com/content/dam/en-zz/Solutions/Data-Center/a100/pdf/
nvidia-a100-datasheet-us-nvidia-1758950-r4-web.pdf, 2020. Accessed:
July 3, 2024.
Nvidia Team.
Nvidia h100 tensor core gpu.
https://resources.nvidia.com/
en-us-tensor-core/nvidia-tensor-core-gpu-datasheet, 2022. Accessed:
July 3, 2024.
Nvidia Team. Nvidia h200 tensor core gpu. https://nvdam.widen.net/s/nb5zzzsjdf/
hpc-datasheet-sc23-h200-datasheet-3002446, 2023. Accessed: July 3 2024.
Redirected from https://www.nvidia.com/en-in/data-center/h200/.
Nvidia Team.
Nvidia blackwell architecture.
https://resources.nvidia.com/
en-us-blackwell-architecture, 2024. Accessed: July 3, 2024.
Denis Paperno, Germán Kruszewski, Angeliki Lazaridou, Ngoc Quan Pham, Raffaella Bernardi,
Sandro Pezzelle, Marco Baroni, Gemma Boleda, and Raquel Fernández. The LAMBADA dataset:
Word prediction requiring a broad discourse context. In Katrin Erk and Noah A. Smith (eds.),
Proceedings of the 54th Annual Meeting of the Association for Computational Linguistics (Volume
1: Long Papers), pp. 1525–1534, Berlin, Germany, August 2016. Association for Computational
Linguistics. doi: 10.18653/v1/P16-1144. URL https://aclanthology.org/P16-1144.
Athanasios Papoulis and S. Unnikrishna Pillai. Probability, Random Variables, and Stochastic
Processes. McGraw-Hill, 4 edition, 2002. ISBN 978-0071226615.
Alicia Parrish, Angelica Chen, Nikita Nangia, Vishakh Padmakumar, Jason Phang, Jana Thompson, Phu Mon Htut, and Samuel Bowman. BBQ: A hand-built bias benchmark for question
answering. In Smaranda Muresan, Preslav Nakov, and Aline Villavicencio (eds.), Findings of
the Association for Computational Linguistics: ACL 2022, pp. 2086–2105, Dublin, Ireland, May
2022. Association for Computational Linguistics. doi: 10.18653/v1/2022.findings-acl.165. URL
https://aclanthology.org/2022.findings-acl.165.
Houwen Peng, Kan Wu, Yixuan Wei, Guoshuai Zhao, Yuxiang Yang, Ze Liu, Yifan Xiong, Ziyue
Yang, Bolin Ni, Jingcheng Hu, Ruihang Li, Miaosen Zhang, Chen Li, Jia Ning, Ruizhe Wang,
Zheng Zhang, Shuguang Liu, Joe Chau, Han Hu, and Peng Cheng. Fp8-lm: Training fp8 large
language models, 2023. URL https://arxiv.org/abs/2310.18313.
Ofir Press and Lior Wolf. Using the output embedding to improve language models, 2017. URL
https://arxiv.org/abs/1608.05859.
Samyam Rajbhandari, Jeff Rasley, Olatunji Ruwase, and Yuxiong He. Zero: memory optimizations
toward training trillion parameter models. In Proceedings of the International Conference for High
Performance Computing, Networking, Storage and Analysis, SC ’20. IEEE Press, 2020. ISBN
9781728199986.
Jeff Rasley, Samyam Rajbhandari, Olatunji Ruwase, and Yuxiong He. Deepspeed: System optimizations enable training deep learning models with over 100 billion parameters. In Proceedings of the 26th ACM SIGKDD International Conference on Knowledge Discovery &
16

Published as a conference paper at ICLR 2025

Data Mining, KDD ’20, pp. 3505–3506, New York, NY, USA, 2020. Association for Computing Machinery. ISBN 9781450379984. doi: 10.1145/3394486.3406703. URL https:
//doi.org/10.1145/3394486.3406703.
Mohammad Rastegari, Vicente Ordonez, Joseph Redmon, and Ali Farhadi. Xnor-net: Imagenet
classification using binary convolutional neural networks. European Conference on Computer
Vision, pp. 525–542, 2016.
Keisuke Sakaguchi, Ronan Le Bras, Chandra Bhagavatula, and Yejin Choi. Winogrande: an adversarial winograd schema challenge at scale. Commun. ACM, 64(9):99–106, aug 2021. ISSN
0001-0782. doi: 10.1145/3474381. URL https://doi.org/10.1145/3474381.
Claude E. Shannon. A mathematical theory of communication. The Bell System Technical Journal,
27(3):379–423, 623–656, 1948.
Wenqi Shao, Mengzhao Chen, Zhaoyang Zhang, Peng Xu, Lirui Zhao, Zhiqian Li, Kaipeng Zhang,
Peng Gao, Yu Qiao, and Ping Luo. Omniquant: Omnidirectionally calibrated quantization for large
language models, 2024. URL https://arxiv.org/abs/2308.13137.
Noam Shazeer. Glu variants improve transformer, 2020.
Mohammad Shoeybi, Mostofa Patwary, Raul Puri, Patrick LeGresley, Jared Casper, and Bryan Catanzaro. Megatron-lm: Training multi-billion parameter language models using model parallelism,
2019.
Daria Soboleva, Faisal Al-Khateeb, Robert Myers, Jacob R Steeves, Joel Hestness, and Nolan Dey.
Slimpajama:
A 627b token cleaned and deduplicated
version of redpajama, 2023.
URL https://www.cerebras.net/blog/
slimpajama-a-627b-token-cleaned-and-deduplicated-version-of-redpajama.
Jianlin Su, Yu Lu, Shengfeng Pan, Ahmed Murtadha, Bo Wen, and Yunfeng Liu. Roformer: Enhanced
transformer with rotary position embedding, 2021.
Chaofan Tao, Lu Hou, Wei Zhang, Lifeng Shang, Xin Jiang, Qun Liu, Ping Luo, and Ngai Wong.
Compression of generative pre-trained language models via quantization. In Smaranda Muresan,
Preslav Nakov, and Aline Villavicencio (eds.), Proceedings of the 60th Annual Meeting of the
Association for Computational Linguistics (Volume 1: Long Papers), pp. 4821–4836, Dublin,
Ireland, May 2022. Association for Computational Linguistics. doi: 10.18653/v1/2022.acl-long.
331. URL https://aclanthology.org/2022.acl-long.331.
Gemma Team, Thomas Mesnard, Cassidy Hardin, Robert Dadashi, Surya Bhupatiraju, Shreya Pathak,
Laurent Sifre, Morgane Rivière, Mihir Sanjay Kale, Juliette Love, Pouya Tafti, Léonard Hussenot,
Pier Giuseppe Sessa, Aakanksha Chowdhery, Adam Roberts, Aditya Barua, Alex Botev, Alex
Castro-Ros, Ambrose Slone, Amélie Héliou, Andrea Tacchetti, Anna Bulanova, Antonia Paterson,
Beth Tsai, Bobak Shahriari, Charline Le Lan, Christopher A. Choquette-Choo, Clément Crepy,
Daniel Cer, Daphne Ippolito, David Reid, Elena Buchatskaya, Eric Ni, Eric Noland, Geng Yan,
George Tucker, George-Christian Muraru, Grigory Rozhdestvenskiy, Henryk Michalewski, Ian
Tenney, Ivan Grishchenko, Jacob Austin, James Keeling, Jane Labanowski, Jean-Baptiste Lespiau,
Jeff Stanway, Jenny Brennan, Jeremy Chen, Johan Ferret, Justin Chiu, Justin Mao-Jones, Katherine
Lee, Kathy Yu, Katie Millican, Lars Lowe Sjoesund, Lisa Lee, Lucas Dixon, Machel Reid, Maciej
Mikuła, Mateo Wirth, Michael Sharman, Nikolai Chinaev, Nithum Thain, Olivier Bachem, Oscar
Chang, Oscar Wahltinez, Paige Bailey, Paul Michel, Petko Yotov, Rahma Chaabouni, Ramona
Comanescu, Reena Jana, Rohan Anil, Ross McIlroy, Ruibo Liu, Ryan Mullins, Samuel L Smith,
Sebastian Borgeaud, Sertan Girgin, Sholto Douglas, Shree Pandya, Siamak Shakeri, Soham De,
Ted Klimenko, Tom Hennigan, Vlad Feinberg, Wojciech Stokowiec, Yu hui Chen, Zafarali Ahmed,
Zhitao Gong, Tris Warkentin, Ludovic Peran, Minh Giang, Clément Farabet, Oriol Vinyals, Jeff
Dean, Koray Kavukcuoglu, Demis Hassabis, Zoubin Ghahramani, Douglas Eck, Joelle Barral,
Fernando Pereira, Eli Collins, Armand Joulin, Noah Fiedel, Evan Senter, Alek Andreev, and
Kathleen Kenealy. Gemma: Open models based on gemini research and technology, 2024. URL
https://arxiv.org/abs/2403.08295.
17

Published as a conference paper at ICLR 2025

Hugo Touvron, Thibaut Lavril, Gautier Izacard, Xavier Martinet, Marie-Anne Lachaux, Timothée
Lacroix, Baptiste Rozière, Naman Goyal, Eric Hambro, Faisal Azhar, Aurelien Rodriguez, Armand
Joulin, Edouard Grave, and Guillaume Lample. Llama: Open and efficient foundation language
models, 2023a.
Hugo Touvron, Louis Martin, Kevin Stone, Peter Albert, Amjad Almahairi, Yasmine Babaei, Nikolay
Bashlykov, Soumya Batra, Prajjwal Bhargava, Shruti Bhosale, Dan Bikel, Lukas Blecher, Cristian Canton Ferrer, Moya Chen, Guillem Cucurull, David Esiobu, Jude Fernandes, Jeremy Fu,
Wenyin Fu, Brian Fuller, Cynthia Gao, Vedanuj Goswami, Naman Goyal, Anthony Hartshorn,
Saghar Hosseini, Rui Hou, Hakan Inan, Marcin Kardas, Viktor Kerkez, Madian Khabsa, Isabel
Kloumann, Artem Korenev, Punit Singh Koura, Marie-Anne Lachaux, Thibaut Lavril, Jenya Lee,
Diana Liskovich, Yinghai Lu, Yuning Mao, Xavier Martinet, Todor Mihaylov, Pushkar Mishra,
Igor Molybog, Yixin Nie, Andrew Poulton, Jeremy Reizenstein, Rashi Rungta, Kalyan Saladi,
Alan Schelten, Ruan Silva, Eric Michael Smith, Ranjan Subramanian, Xiaoqing Ellen Tan, Binh
Tang, Ross Taylor, Adina Williams, Jian Xiang Kuan, Puxin Xu, Zheng Yan, Iliyan Zarov, Yuchen
Zhang, Angela Fan, Melanie Kambadur, Sharan Narang, Aurelien Rodriguez, Robert Stojnic,
Sergey Edunov, and Thomas Scialom. Llama 2: Open foundation and fine-tuned chat models,
2023b.
Ashish Vaswani, Noam Shazeer, Niki Parmar, Jakob Uszkoreit, Llion Jones, Aidan N Gomez,
Ł ukasz Kaiser, and Illia Polosukhin. Attention is all you need. In I. Guyon, U. Von
Luxburg, S. Bengio, H. Wallach, R. Fergus, S. Vishwanathan, and R. Garnett (eds.), Advances in Neural Information Processing Systems, volume 30. Curran Associates, Inc.,
2017.
URL https://proceedings.neurips.cc/paper_files/paper/2017/
file/3f5ee243547dee91fbd053c1c4a845aa-Paper.pdf.
Hongyu Wang, Shuming Ma, Li Dong, Shaohan Huang, Huaijie Wang, Lingxiao Ma, Fan Yang,
Ruiping Wang, Yi Wu, and Furu Wei. Bitnet: Scaling 1-bit transformers for large language models,
2023.
Johannes Welbl, Nelson F. Liu, and Matt Gardner. Crowdsourcing multiple choice science questions.
ArXiv, abs/1707.06209, 2017. URL https://api.semanticscholar.org/CorpusID:
1553193.
Thomas Wolf, Lysandre Debut, Victor Sanh, Julien Chaumond, Clement Delangue, Anthony Moi,
Pierric Cistac, Tim Rault, Rémi Louf, Morgan Funtowicz, Joe Davison, Sam Shleifer, Patrick von
Platen, Clara Ma, Yacine Jernite, Julien Plu, Canwen Xu, Teven Le Scao, Sylvain Gugger, Mariama
Drame, Quentin Lhoest, and Alexander M. Rush. Transformers: State-of-the-art natural language
processing. In Proceedings of the 2020 Conference on Empirical Methods in Natural Language Processing: System Demonstrations, pp. 38–45, Online, October 2020. Association for Computational
Linguistics. URL https://www.aclweb.org/anthology/2020.emnlp-demos.6.
Guangxuan Xiao, Ji Lin, Mickael Seznec, Hao Wu, Julien Demouth, and Song Han. Smoothquant:
Accurate and efficient post-training quantization for large language models, 2024. URL https:
//arxiv.org/abs/2211.10438.
Zhewei Yao, Reza Yazdani Aminabadi, Minjia Zhang, Xiaoxia Wu, Conglong Li, and Yuxiong He.
Zeroquant: Efficient and affordable post-training quantization for large-scale transformers, 2022.
URL https://arxiv.org/abs/2206.01861.
Zhewei Yao, Xiaoxia Wu, Cheng Li, Stephen Youn, and Yuxiong He. Zeroquant-v2: Exploring
post-training quantization in llms from comprehensive study to low rank compensation, 2023.
URL https://arxiv.org/abs/2303.08302.
Zhihang Yuan, Yuzhang Shang, and Zhen Dong. PB-LLM: Partially binarized large language
models. In The Twelfth International Conference on Learning Representations, 2024. URL
https://openreview.net/forum?id=BifeBRhikU.
Rowan Zellers, Ari Holtzman, Yonatan Bisk, Ali Farhadi, and Yejin Choi. HellaSwag: Can a
machine really finish your sentence? In Anna Korhonen, David Traum, and Lluís Màrquez
(eds.), Proceedings of the 57th Annual Meeting of the Association for Computational Linguistics,
pp. 4791–4800, Florence, Italy, July 2019. Association for Computational Linguistics. doi:
10.18653/v1/P19-1472. URL https://aclanthology.org/P19-1472.
18

Published as a conference paper at ICLR 2025

Biao Zhang and Rico Sennrich. Root mean square layer normalization. In Proceedings of the 33rd
International Conference on Neural Information Processing Systems, Red Hook, NY, USA, 2019.
Curran Associates Inc.
Chiyuan Zhang, Samy Bengio, Moritz Hardt, Benjamin Recht, and Oriol Vinyals. Understanding deep learning requires rethinking generalization. In International Conference on Learning
Representations (ICLR), 2017.
Shuchang Zhou, Yuxin Wu, Zekun Ni, Xinyu Zhou, He Wen, and Yuheng Zou. Dorefa-net: Training low bitwidth convolutional neural networks with low bitwidth gradients. arXiv preprint
arXiv:1606.06160, 2016.
Shuchang Zhou, Yuxin Wu, Zekun Ni, Xinyu Zhou, He Wen, and Yuheng Zou. Dorefa-net: Training
low bitwidth convolutional neural networks with low bitwidth gradients, 2018. URL https:
//arxiv.org/abs/1606.06160.
Chenzhuo Zhu, Song Han, Huizi Mao, and William J Dally. Trained ternary quantization. arXiv
preprint arXiv:1612.01064, 2017.
Xunyu Zhu, Jian Li, Yong Liu, Can Ma, and Weiping Wang. A survey on model compression for
large language models, 2023. URL https://arxiv.org/abs/2308.07633.
Barret Zoph, Irwan Bello, Sameer Kumar, Nan Du, Yanping Huang, Jeff Dean, Noam Shazeer, and
William Fedus. St-moe: Designing stable and transferable sparse expert models, 2022. URL
https://arxiv.org/abs/2202.08906.

19

Published as a conference paper at ICLR 2025

Appendix
Table of Contents

A

A Architecture and PreTraining Details
A.1 Forward Pass, Backward Pass and Inference Equations . . . . . . . . . . . . . .
A.2 Data and Tokenizer . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
A.3 PreTraining Setup . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
A.4 Hyperparameters . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
A.5 Optimization Schedule . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
A.6 Known Implementation Artifacts . . . . . . . . . . . . . . . . . . . . . . . . .
A.7 Differences from BitNet Architecture . . . . . . . . . . . . . . . . . . . . . . .
A.8 Spectra Suite of LLMs: Parameter Scaling and Bitwidth Variations . . . . . . .
A.9 Details on the Selection of Hyperparameters . . . . . . . . . . . . . . . . . . .
A.10 Perplexity for Increasing Training Tokens in TriLM Models . . . . . . . . . . .

20
21
21
22
22
22
23
23
25
25
26

B Binary vs Ternary Large Language Models
B.1 BiLM: Binary Large Language Model . . . . . . . . . . . . . . . . . . . . . .
B.2 Scaling Binary vs Ternary Model . . . . . . . . . . . . . . . . . . . . . . . . .
B.3 Results . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

27
27
27
27

C Scaling Law

29

D Benchmark Details
D.1 Commonsense and Reasoning . . . . . . . . . . . . . . . . . . . . . . . . . . .
D.2 Knowledge . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
D.3 Toxicity . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
D.4 Perplexity on other datasets . . . . . . . . . . . . . . . . . . . . . . . . . . . .
D.5 OmniQuant: 3-Bit Post-Training Quantized Models . . . . . . . . . . . . . . .

31
31
31
34
34
36

E Weight Distribution of Linear Layers

38

F Learning Dynamics Analysis of Peak LR drop and decay stage

39

G Memory Bottlenecks and Low-Bitwidth Language Modelling
G.1 Overview of Recent Datacenter GPUs and Accelerators. . . . . . . . . . . . . .
G.2 Memory Trends and Speedup Opportunities in Low-Bitwidth Language Modeling

41
41
41

H Ablations

43

I

Illustrative examples of TriLM 3.9B’s completion capabilities

46

J

Broader Impact

48

A RCHITECTURE AND P RE T RAINING D ETAILS

This section provides a comprehensive overview of the architectural design and pretraining for TriLM
(Ternary Language Model) and FloatLM (Floating Point Language Model). We outline the forward
and backward pass equations specific to their linear layers, highlighting the contrast between the
FP16 matrices in FloatLM and the ternary matrices with scalar scaling in TriLM. Additionally, it
covers dataset selection, tokenizer usage, and preprocessing methods employed for training data
preparation. These discussions provide information on pretraining setups, implementation nuances,
and key hyperparameters critical to the models’ development.
20

Published as a conference paper at ICLR 2025

A.1

F ORWARD PASS , BACKWARD PASS AND I NFERENCE E QUATIONS

Table 1 shows the equations across TriLM vs FloatLM for forward pass, backward pass and inference.
Type
FloatLM

Forward Pass

Backward Pass

Inference

Y = XW T

∂L
∂L
∂X = ∂Y W
∂L T
∂L
∂W = ∂Y X

Y = XW T

∂L f
∂L
∂X = ∂Y W
∂L
∂L T
∂W = ∂Y X

c and γ once and cache
Compute W
g
d
W
ij = γ Wij
f
Y = XW T

∂L
∂L f
∂X = ∂Y W
∂L
∂L T
∂W = ∂Y X

c and α once and cache
Compute W
g
d
W
ij = αWij
f
Y = XW T

Pn Pm
1
γ = ϵ +nm
 i=1  j=1 |Wij|

TriLM

BiLM


Wij
d
W
,
−1
,
1
ij = round min max
γ
g
d
W
ij = γ Wij
fT
Y = XW
P
P
n
m
1
|Wij |
α = nm
i=1
Pj=1
n Pm
1
d
Wij = sign(Wij − nm i=1 j=1 Wij )
g
d
W
ij = αWij
fT
Y = XW

Table 1: Equations in the Linear Layer of TriLMs and FloatLMs.
Reason for restricting the quantization approach to linear weights in TriLMs. In developing
extremely large language models like TriLMs, a key architectural strategy is to quantize only the linear
layer weights while keeping the embedding layers and language model head in higher precision. This
is driven by the need to reduce model size while maintaining performance. Linear layers (dense layers)
hold the bulk of the parameters in transformer models (Vaswani et al., 2017). Quantizing these weights
to ternary states significantly reduces the model size, facilitating deployment on memory-constrained
hardware. However, the embedding layers and language model head remain in higher precision (e.g.,
half-precision floating point) to preserve critical functions in language understanding and generation.
Embedding layers encode important semantic and syntactic information, and quantizing them would
degrade performance (Mikolov et al., 2013). Similarly, the language model head, which maps internal
representations to the vocabulary space, requires high precision to maintain prediction quality (Press
& Wolf, 2017)
A.2

DATA AND T OKENIZER

Dataset Selection: Let input be X ∈ Rb×n for a linear layer with FP16 weight matrix W ∈ Rm×n
and Y ∈ Rb×m be the output. The same matrix W is also used to denote latent weights in TriLMs
during training.
For ternarized layers in TriLMs, we also have a scalar scale γ ∈ R, matrix with ternarized states
c ∈ {−1, 0, 1}n×m and ternarized matrix W
f ∈ Rn×m . We set ϵ = 1e − 5.
W
Due to lack of availability of Pile 300B (Gao et al., 2020) used in Pythia, we opted to use a 300B
token sample of deduplicated Slim Pajama dataset2 . We sample from each subset with the probability
proportional to its size.
Training Data Preparation:
• Main experiments (Spectra suite): We used the full 300B token sample.
• Ablation studies: Training runs with 100B tokens, we sample from these 300B tokens with
equal probability weight to each data-point.
• Fine-Web Edu experiments: We tokenized one-third of a 350B token sample, from which
we then sampled 100B tokens for our experiments.
2

We also make this subset public

21

Published as a conference paper at ICLR 2025

QuantLM: For the creation of QuantLM, we utilized a
subset of the Slimpajama-627B dataset, consisting of 512
samples with a sequence length of 2048. These samples
were normalized for length. Our approach closely follows
the methodology outlined in (Malinovskii et al., 2024).

Dataset

Size (Tokens)

Tokenizer and Optimization Techniques: We use the
GPT-NeoX 20B tokenizer following Pythia. For speeding up training, we round embedding rounding of to the
nearest multiple of 128 times the model parallel size.

Arxiv
Book
C4
Common Crawl
GitHub
Stack Exchange
Wikipedia

13B
13B
80B
156B
16B
10B
12B

A.3

Total

300B

P RE T RAINING S ETUP

Table 2: 300B Subset of Slim Pajama
We scale using 2D-parallelism with Megatron-style sharding (Shoeybi et al., 2019) and use ZeRO stage 2 Deepspeed
(Rasley et al., 2020) for ZeRO (Rajbhandari et al., 2020). Our implementation was based on GPT
NeoX Codebase (Andonian et al., 2023). We use AdamW (Kingma & Ba, 2017) for optimization.
We train on nodes with IBM Power9 PC CPUs and 6x16GB V100. Due to the lack of BFloat16
support in V100, we train both TriLM and FloatLM in FP16 using Mixed Precision Training and
Dynamic Loss Scaling. Please refer to §A.6 for more implementation specific details. We extensively
use Huggingface (Wolf et al., 2020) and Wandb (Biewald, 2020) for handling the checkpoints and
experiment tracking.
A.4

H YPERPARAMETERS

Table 3 shows the hyperparameters for TriLM and FloatLM’s transformer architecture and their
learning rate. We set Adam β are set to (0.9, 0.95) for both families of models and all the reported
runs are trained to 2048 sequence length. FloatLM and TriLM are respectively trained with batch
sizes of 2M and 1M tokens respectively.
Params
99.74M (99M)
190.0M (190M)
392.4M (390M)
569.2M (560M)
834.0M (830M)
1.149B (1.1B)
1.515B (1.5B)
2.461B (2.4B)
3.989B (3.9B)

Hidden
512
768
1024
1280
1536
1792
2048
2304
3072

GLU

Heads

1280
2048
2560
3072
4096
5120
6144
7680
9216

8
12
16
20
24
28
32
36
24

Layers
16
16
24
24
24
24
24
30
30

MP

FloatLM LR
−4

4.0 ∗ 10
4.0 ∗ 10−4
3.0 ∗ 10−4
2.8 ∗ 10−4
2.5 ∗ 10−4
2.2 ∗ 10−4
2.0 ∗ 10−4
2.0 ∗ 10−4
1.5 ∗ 10−4

1
1
1
1
1
2
2
3
6

TriLM LR
2.4 ∗ 10−3 → 1.5 ∗ 10−3
2.4 ∗ 10−3 → 1.5 ∗ 10−3
1.8 ∗ 10−3 → 1.2 ∗ 10−3
1.6 ∗ 10−3 → 1.1 ∗ 10−3
1.5 ∗ 10−3 → 1.0 ∗ 10−3
1.3 ∗ 10−3 → 9.0 ∗ 10−4
1.2 ∗ 10−3 → 8.0 ∗ 10−4
1.2 ∗ 10−3 → 8.0 ∗ 10−4
1.2 ∗ 10−3 → 8.0 ∗ 10−4

Table 3: Hyperparameters across model sizes for TriLM and FloatLM.
Params

99M

190M

390M

560M

830M

1.1B

1.5B

2.4B

3.9B

FloatLM
QuantLM 8-Bit
QuantLM 6-Bit
QuantLM 4-Bit
QuantLM 3-Bit
TriLM

1.60
1.21
1.11
1.03
0.98
0.90

3.05
2.14
1.92
1.72
1.60
1.42

6.28
3.96
3.38
2.88
2.59
2.11

9.11
5.58
4.70
3.93
3.49
2.76

13.34
7.91
6.55
5.36
4.68
3.55

18.39
10.64
8.70
7.00
6.03
4.42

24.23
13.77
11.15
8.86
7.55
5.36

39.38
21.55
17.09
13.18
10.95
7.23

63.83
34.39
27.03
20.59
16.91
10.76

Table 4: Sizes in bits (*109 ) for Spectra suite of LLMs across varying parameter counts.
A.5

O PTIMIZATION S CHEDULE

In this section, we ablate the two interventions in a vanilla linear decay learning rate scheduling with
warmup and weight decay (L2 Regularization). (1) Peak LR - at roughly the halfway point, we reduce
22

Published as a conference paper at ICLR 2025

the peak learning rate. (2) L2 Reg. - at roughly two-thirds of the training, we remove the weight
decay regularization as ternarization provides sufficient regularization (Courbariaux et al., 2016b).
Figure 9 demonstrates the ablation run performed for a 1.1B parameter model on 100B tokens with
both, only one and neither of these interventions.

Training Cross Entropy Loss

Among these four runs, we notice the
lowest final training loss when both, the
TriLM Training Loss Across Optimization Schedules
L2 Regularization and Peak LR are inHyperparameter Intervened
2.75
tervened, closely followed only L2 RegPeak LR & L2 Reg.
Only L2 Reg.
ularization (at 1/2 and 2/3) being interOnly Peak LR
vened
and then only Peak LR being in2.70
Baseline
tervened. Dropping the peak LR at the
halfway point leads to a quick sharp
2.65
drop in training loss. Similar phenomena have also been observed in sched2.60
ules with small episodes of fast learning
rate decaying like MiniCPM (Hu et al.,
2.55
2024). On the other hand, removing L2
regularization, or weight decay, leads
to accelerated convergence, which can
2.50
even mostly have the same effect as low25B
50B
75B
100B
Tokens Trained
ering peak LR leading to a quick drop
in loss. These relative training loss obFigure 9: Training loss for a 1.1B parameter TriLM, across servation at 100B tokens also go hand
different optimization schedules. We intervene for combinations in hand with relative downstream perof two hyperparameters peak learning rate and L2 regularization. formance across commonsense and reaIntervention for both hyperparameters given best training loss.
soning tasks, which are listed in Table
14 and 13. Thus, we fix the TriLM optimization schedule where we drop in the peak learning rate at the halfway mark and the weight decay
is removed at the two-thirds mark.
A.6

K NOWN I MPLEMENTATION A RTIFACTS

Similar to BitNet (Wang et al., 2023), our models exhibit artifacts resulting from model parallelism.
A key issue arises when computing the scale, γ, across the entire weight matrix, which is sharded
across multiple devices. This process introduces a significant communication overhead due to the
all-reduce operations. In our implementation, we address this by computing the scales over the
portion of the weight matrix local to each device. Consequently, during inference with TriLM models,
scales are computed independently within each model parallel group. Importantly, this modification
has a negligible impact on the bits per parameter, amounting to less than 10−5 , even at the highest
model parallelism level of 6 for our largest model.
Given that we train in FP16, some artifacts are expected as a result of this training method. However,
we do not anticipate significant performance differences when comparing mixed precision training
with BF16 or even FP32. This expectation is based on the observation that the lowest loss scales
recorded during our runs were consistently at or above the recommended value of 128 (Micikevicius
et al., 2018) (refer to Table 5).
A.7

D IFFERENCES FROM B IT N ET A RCHITECTURE

TriLM differs from BitNet b1.58 in several ways for better performance as well as for fairer comparison with FloatLMs. Adopting the GPT-3’s Pre-Normalization approach as outlined by (Brown
et al., 2020b), normalization is applied prior to each linear layer. This method has proven essential for
maintaining stable training under FP16 precision (Wang et al., 2023). Consequently, normalization
occurs twice within each transformer layer: once at the input representations to the attention sub-layer
and again at the input representations to the Gated MLP sub-layer. This approach contrasts with
BitNet, where activation or intermediate representations are normalized, scaled, and quantized to 8
bits before each linear layer, which occurs between 4 to 7 times per transformer layer depending on
23

Published as a conference paper at ICLR 2025

Model

Min. Loss-Scale

# Skipped Batches

# Skipped Tokens

FloatLM 99M
TriLM 99M

256.0
1024.0

181
303

0.37B
0.33B

FloatLM 190M
TriLM 190M

512.0
512.0

168
305

0.35B
0.33B

FloatLM 390M
TriLM 390M

1024.0
512.0

170
312

0.35B
0.34B

FloatLM 560M
TriLM 560M

256.0
512.0

164
294

0.33B
0.32B

FloatLM 830M
TriLM 830M

2048.0
128.0

175
307

0.36B
0.33B

FloatLM 1.1B
TriLM 1.1B

2048.0
512.0

158
306

0.32B
0.33B

FloatLM 1.5B
TriLM 1.5B

256.0
512.0

170
318

0.35B
0.34B

FloatLM 2.4B
TriLM 2.4B

1024.0
256.0

165
294

0.34B
0.32B

FloatLM 3.9B
TriLM 3.9B

256.0
128.0

164
309

0.34B
0.33B

Table 5: Final loss-scale and number of batches skipped across TriLM and FloatLM training runs - We are able
to maintain above the recommended loss scales of 128 for mixed precision training (Micikevicius et al., 2018).

54
52
50
48

.3B
81

Bit

Ne

tb

1.5

87
1.5
tb
Ne

Bit

Bit

Ne

tb

1.5

81

Flo

atL

.1B

M

(O

00

urs

)

B
1.1

1.1
M
Tri
L

M

46

B

Avg. Score Across 6 Benchmarks

Relative Performance Across Architectures

Figure 10: Performance across various architectures - TriLM 1.1B, FloatLM 1.1B, BitNet b1.58 1.1B (our
replication) along with reported scores of BitNet b1.58 at 700M and 1.3B params. Scores are averaged across 6
common sense and reasoning benchmarks, mentioned in Table 14 and 13.

the specific implementation. Furthermore, TriLM employs RMSNorm with a scale parameter over
the parameterless RMSNorm.
Figure 10 shows the commonsense and reasoning performance of TriLM 1.1B, FloatLM 1.1B and
our replication of BitNet b1.58’s architecture at 1.1B scale, along with the reported performance
for BitNet b1.58 700M and 1.3B. All these models have been trained for 100B tokens. Our BitNet
24

Published as a conference paper at ICLR 2025

replication achieves performance between the 700M and 1.3B models. However, all the BitNet
models, including the larger 1.3B parameter model perform worse than TriLM 1.1B. It should be
noted that at this 1.1B scale, TriLMs do not achieve parity with FloatLMs of the same parameter count.
Table 14 and 13lists the detailed performance of these models across common sense benchmarks.
A.8

S PECTRA S UITE OF LLM S : PARAMETER S CALING AND B ITWIDTH VARIATIONS

Figure 11 illustrates the Spectra LM suite spanning two key dimensions: bitwidth and the number of
parameters. The suite includes the TriLM, FloatLM, and QuantLM model families (in 3, 4, 6, and 8
bits). The suite features 9 different parameter scales ranging from 99M to 3.9B parameters. In total,
the suite comprises 54 models.

Model Size in Bits (Log Scale)

Spectra Suite Spans Across Parameters & Bits

50
20

FloatLM
QuantLM 8-Bit
QuantLM 6-Bit
QuantLM 4-Bit
QuantLM 3-Bit
TriLM

10
5
2
1
190M 560M 1.5B 3.9B
Parameters (Log Scale)

Figure 11: The Spectra Suite spans across two dimensions: parameters and bitwidth. Each point corresponds to
a language model in the suite.

A.9

D ETAILS ON THE S ELECTION OF H YPERPARAMETERS

Model architecture hyperparameters. To ensure stable training and mitigate risks of loss spikes or
slow convergence, we carefully selected key architectural hyperparameters such as layer normalization
techniques and other training parameters. To optimize hardware efficiency, we padded the vocabulary
size and rounded the hidden dimensions to the nearest power of two, facilitating alignment with
accelerator constraints. Given computational limitations, our scaling and coefficient analyses were
conducted with nine data points within the 4-billion-parameter range, each trained on datasets
containing 300 billion tokens. These constraints directly influenced the design choices for the number
of layers, hidden dimensions, embedding size, feedforward network dimensions, and attention heads
across model variants.
Training hyperparameters. We adopted a rigorous evaluation-driven approach to refine training
hyperparameters, encompassing model initialization, optimizers, and learning rate schedules. This
methodology mirrors the training-time evaluations utilized in other model suites such as those by
Biderman et al. (2023) and Groeneveld et al. (2024). To systematically explore the hyperparameter
space, we employed a grid search over configurations, including learning rate, weight decay, batch
size, and optimizer variants. Evaluations are conducted at different stages of training, from 4 billion
up to 20 billion tokens, providing continuous and early-stage feedback on model performance.
The key metrics evaluated include validation loss, commonsense reasoning, knowledge-based task
performance, and toxicity assessments, as outlined in the paper.
25

Published as a conference paper at ICLR 2025

A.10

P ERPLEXITY FOR I NCREASING T RAINING T OKENS IN T RI LM M ODELS

Impact of Training Tokens on Perplexity in TriLM Models. The performance of language
models generally improves with an increased number of training tokens, as demonstrated in prior
work (Hoffmann et al., 2022; Kaplan et al., 2020). This trend is clearly reflected in the validation
perplexity of our TriLM models across varying training token counts. The results, summarized in
Table 6, highlight the critical role of scaling up training data to reduce perplexity. Notably, the larger
model—TriLM 560M—consistently achieves lower perplexity at all token scales. This reinforces
the scaling law relationship among larger model sizes, more extensive training data, and reduced
validation perplexity, mirroring the scaling laws observed for FloatLMs.
Training Tokens
50B
150B
300B

Perplexity of TriLM 99M
27.11
26.30
25.70

Perplexity of TriLM 560M
15.48
14.50
14.01

Table 6: Perplexity comparison for TriLM models with 99M and 560M parameters across different training
token counts.

Impact of Token-to-Parameter. The reduction in validation perplexity, even after training on over
3000 times the number of tokens relative to the number of parameters, is particularly evident in the
smallest model (99M) of our suite. As shown in Table 6, the 99M model continues to demonstrate
improvement with up to 300B tokens, suggesting that TriLM remains effective even at higher training
token-to-parameter ratios. Extrapolating from this trend, our largest model (3.9B) could theoretically
train on up to 11.8 trillion tokens without reaching convergence. This scale is comparable to the
magnitude of training tokens used for LLaMA 3, a state-of-the-art open-source language model
AI@Meta (2024). However, due to resource constraints, training at such a scale remains a direction
for future work.

26

Published as a conference paper at ICLR 2025

B

B INARY VS T ERNARY L ARGE L ANGUAGE M ODELS

In this section, we will comprehensively compare Binary Large Language Models (BiLMs) with
Ternary Large Language Models (TriLMs). We will start by describing BiLMs, followed by studying
scaling laws and presenting results on various benchmarks, as well as comparisons with TriLMs
across parameter count and model size (in bits).
B.1

B I LM: B INARY L ARGE L ANGUAGE M ODEL

In Binary Large Language Models (BiLMs), the weights of the linear layers are represented by binary
values of -1 or 1, with an accompanying floating-point scaling factor, similar to the method employed
in TriLMs. Comprehensive formal descriptions of the forward pass, backward pass, and inference
time calculations are provided in Appendix (§A). We have trained three BiLM models of distinct
sizes: 99M, 560M, and 1.1B parameters. These models were trained on the same dataset and in the
same sequence as the TriLMs, adhering to the identical optimization schedule detailed in Appendix
A.5.

Cross Entropy (Log Perplexity)

Cross Entropy vs Model Parameters
3.4

Cross Entropy vs. Model Size (Bits)

Ternary LLMs
Binary LLMs

0.19

3.4

3.2

Cross Entropy

3.2

Binary LLMs
Ternary LLMs

=0.189

3.0

3.0

2.8

2.8

0.15

2.6

0.12
99M

560M

Model Parameters

=0.155

2.6

1.1B

=0.118
1

(a) Vs. Params

2

3

4

Model Size (Bits)

5

1e9

(b) Vs. Size (in Bits)

Figure 12: Final Validation loss across size (measure in bits) and parameters.
B.2

S CALING B INARY VS T ERNARY M ODEL

Figures 12a and 12b show the final validation loss across model sizes (in bits) and parameter counts,
respectively for the three distinct sizes previously mentioned. At the Billion+ model scale, Ternary
Models appear to be preferable in terms of both the number of parameters and model size (in
bits). However, the gap seems to be narrowing, which suggests that BiLMs have the potential to be
competitive with TriLMs at higher parameter counts (100B+). Therefore, we decide to only scale
TriLMs further to study the scaling laws of FloatLMs vs TriLMs up to 3.9B parameters.
B.3

R ESULTS

We conducted a comprehensive benchmark analysis of Binary Large Language Models (BILMs)
across three key dimensions: commonsense and reasoning tasks, knowledge-based tasks, and toxicity
evaluation, as detailed in Tables 7, 810, and 15

27

Published as a conference paper at ICLR 2025

Accuracy vs Model Size

50
48
46
44
42
BiLM
TriLM
5

40
1

2

3

Accuracy vs Model Parameters

52

Avg. Score Across 6 Benchmarks

Avg. Score Across 6 Benchmarks

52

4

Size in Bits (109)

50
48
46
44
42
40
200

400

600

800

Model Parameters (Millions)

(a) vs. Size in C & R

BiLM
TriLM
1000

(b) vs. Params in C & R

Figure 13: Performance of ternary TriLMs and BiLMs models on commonsense and Reasoning and MMLUs
tasks across Size (Bits) and Parameters. Refer to Tables 7 and 8 for details.

LAMBADA vs Model Parameters
45

40

40

35

35

Accuracy (%)

Accuracy (%)

LAMBADA vs Size in Bits
45

30
25
20

30
25
20

BiLM
TriLM

15
1

2

3

4

BiLM
TriLM

15

5

Size (Bits * 10^9)

0.2

(a) vs. Size in LAMBADA

0.4

0.6

0.8

Model Parameters (Billions)

1.0

(b) vs. Params in LAMBADA

Figure 14: Performance of ternary TriLMs and BiLMs models on LAMBADA tasks across Size (Bits) and
Parameters. Refer to Tables 7, and 8 for details.

MMLU vs Size in Bits

MMLU vs Model Parameters

BiLM
TriLM

28

27

Accuracy (%)

27

Accuracy (%)

BiLM
TriLM

28

26

25

24

26

25

24

23

23
1

2

3

4

Size (Bits * 10^9)

5

0.2

(a) vs. Size in MMLU

0.4

0.6

0.8

Model Parameters (Billions)

1.0

(b) vs. Params in MMLU

Figure 15: Performance of ternary TriLMs and BiLMs models on MMLU across Size (Bits) and Parameters.
Refer to Tables 15 for details.

28

Published as a conference paper at ICLR 2025

C

S CALING L AW

In this section, we provide additional insights into the scaling fits discussed in Section 4.3. In addition
to fitting a power law with an offset, we also explore a standard power law following Kaplan et al.
(2020). Our findings suggest that the standard power law fits are slightly less precise than those
incorporating an offset term. However, both models indicate a decreasing difference in validation
loss as the number of parameters (N ) increases.

Scaling Law Fits (Linear Scale)
TriLM : PowerLaw with offset : y = 185 × x 0.26 + 1.76
FloatLM : PowerLaw with offset : y = 159 × x 0.26 + 1.67
TriLM : PowerLaw : y = 18.13 × x 0.093
FloatLM : PowerLaw : y = 13.82 × x 0.085

4.5

Validation Loss

4.0
3.5
3.0
2.5
2.0

0

1

2

3

4

Model Size

5

1e9

Scaling Law Fits (Log-Log Scale)
TriLM : PowerLaw with offset : y = 185 × x 0.26 + 1.76
FloatLM : PowerLaw with offset : y = 159 × x 0.26 + 1.67
TriLM : PowerLaw : y = 18.13 × x 0.093
FloatLM : PowerLaw : y = 13.82 × x 0.085

Validation Loss (log scale)

4 × 100
3 × 100

2 × 100

107

108

109

1010

1011

Model Size (log scale)

1012

1013

Figure 16: Comparison of Power Law and Power Law-with-offset Fits for TriLM and FloatLM.
As shown in Figure 17, using the scaling equations for TriLMs and FloatLMs, we derive the
relationship between parameter count and the percentage difference in validation loss relative to
FloatLMs. We observe that at 330B and 15.6B parameters, the validation losses for TriLMs are
29

Published as a conference paper at ICLR 2025

within 6% and 7% of FloatLMs’ validation losses, respectively. This indicates that TriLMs are likely
to closely match the performance of FloatLMs at larger scales.

Number of params (log scale)

1022 Parameter Count vs. Validation Loss Difference (% of FloatLM's Loss)
1 log 0.01671k 0.0835
N(k) = exp 0.26
26.1 1.59k
20
10
(

(

))

1018
1016
1014
329.92 B

1012

15.65 B

1010

2.14 B

0.44 B

108
5

6

7

8

9

0.11 B

10

11

Validation Loss difference in % of FloatLM's loss

Figure 17: Comparison of Power Law and Power Law-with-offset Fits for TriLM and FloatLM.

30

Published as a conference paper at ICLR 2025

D

B ENCHMARK D ETAILS

We benchmark TriLM, FloatLM and QuantLM across Knowledge, Commonsense, Reasoning and
Toxicity benchmarks. We average our scores across 3 different ‘seeds’ by preparing three different
QuantLM models quantized using different calibration sets. We also add Pythia (deduplicated with
consistent 2M batch size across families) suite of models (70M to 2.8B params) and BitNet b.158
performance scores from their paper for comparison. We use the LM Evaluation Harness (Gao et al.,
2023) to benchmark.
D.1

C OMMONSENSE AND R EASONING

We report commonsense and reasoning benchmark scores across 6 benchmarks previously considered
by BitNet b.158 in Table 7, 8 and rest in Table 10. Each is considered in a zero-shot setting. Following
are the details of each of the benchmarks considered:
• ARC Challenge and Easy: (Clark et al., 2018) ARC dataset comprises 7787 multiplechoice science questions divided into two sets: Challenge and Easy. We calculate accuracy
and normalised accuracy across both of these sets.
• BoolQ: (Clark et al., 2019) BoolQ is a reading comprehension dataset consisting of naturally
occurring yes/no questions. We calculate the accuracy of this task.
• HellaSwag: (Zellers et al., 2019) HellaSWAG is a dataset of multiple choice questions for
testing grounded commonsense. The incorrect options are generated through Adversarial
Filtering (AF) to fool machines but not humans. We calculate the accuracy and normalized
accuracy on this task.
• WinoGrande: (Sakaguchi et al., 2021) WinoGrande is a collection of 44k problems for
testing commonsense reasoning formulated as a fill-in-a-blank task with binary options. We
report the accuracy on this task.
• PIQA: (Bisk et al., 2019) Physical Interaction Question Answering (PIQA) is a physical
commonsense reasoning benchmark dataset to test the physical knowledge of language
models. We calculate the accuracy and normalized accuracy on this task.
• LAMBADA OpenAI: (Paperno et al., 2016) LAMBADA is a dataset to evaluate text
understanding by next-word prediction. It is a collection of narrative passages BooksCorpus
To succeed on LAMBADA, models must integrate broader discourse information, not solely
rely on local context. We calculate the perplexity and the accuracy of the model on this task.
• LogiQA: (Liu et al., 2021) LogiQA is a dataset for testing human logical reasoning. It
contains questions spanning multiple types of deductive reasoning. We calculate the accuracy
and normalized accuracy on this task.
D.2

K NOWLEDGE

We report performance on SciQ, TriviaQA in Tables 10, 15 and 16. Each is considered in a zero-shot
setting. Following are the details of each of the benchmarks considered:
The knowledge-based evaluation included the following tasks:
• SciQ: (Welbl et al., 2017) The SciQ dataset contains multiple-choice questions with 4 answer
options from crowd-sourced science exams. The questions range from Physics, Chemistry
and Biology and several other fields. We calculate the accuracy and length normalized
accuracy on this task.
• TriviaQA: (Joshi et al., 2017) TriviaQA is a reading comprehension dataset containing
question-answer-evidence triples. We calculate the exact match accuracy on this task.
• MMLU (Hendrycks et al., 2021): The benchmark aims to assess the knowledge gained
during pretraining by evaluating models solely in zero-shot and few-shot scenarios. It spans
57 subjects, including STEM fields, humanities, social sciences, and more.
31

Published as a conference paper at ICLR 2025

Models

Pythia 70M

Arc Challenge

Arc Easy

BoolQ

Acc Norm.

Acc

Acc Norm.

Acc

Acc

22.0± 1.2

22.1± 1.2

24.8± 0.9

24.8± 0.9

38.5± 0.9

FloatLM 99M

23.8± 1.2

19.9± 1.2

39.1± 1.0

45.1± 1.0

58.2± 0.9

QuantLM 99M 8-Bit

23.8± 1.2

19.6± 1.2

39.4± 1.0

45.3± 1.0

58.5± 0.9

QuantLM 99M 6-Bit

23.2± 1.2

19.7± 1.2

38.8± 1.0

44.8± 1.0

58.9± 0.9

QuantLM 99M 4-Bit

22.6± 1.2

18.0± 1.1

37.1± 1.0

41.7± 1.0

52.2± 0.9

QuantLM 99M 3-Bit

23.2± 1.2

19.5± 1.2

34.8± 1.0

36.1± 1.0

48.4± 0.9

TriLM 99M

24.1± 1.3

19.1± 1.1

36.6± 1.0

39.8± 1.0

61.3± 0.9

Binary 99M

20.8± 1.2

18.3± 1.1

35.8± 0.9

40.1± 1.0

61.0± 0.8

Pythia 160M

23.8± 1.2

23.1± 1.2

26.7± 0.9

26.6± 0.9

38.3± 0.9

FloatLM 190M

24.1± 1.3

20.5± 1.2

43.0± 1.0

48.4± 1.0

59.1± 0.9

QuantLM 190M 8-Bit

24.4± 1.3

20.3± 1.2

43.0± 1.0

48.5± 1.0

59.3± 0.9

QuantLM 190M 6-Bit

23.8± 1.2

20.0± 1.2

42.0± 1.0

48.0± 1.0

59.1± 0.9

QuantLM 190M 4-Bit

25.2± 1.3

19.9± 1.2

26.5± 0.9

26.8± 0.9

40.9± 0.9

QuantLM 190M 3-Bit

22.5± 1.2

19.4± 1.2

37.1± 1.0

39.7± 1.0

56.5± 0.9

TriLM 190M

23.0± 1.2

19.5± 1.2

39.6± 1.0

43.9± 1.0

46.8± 0.9

FloatLM 390M

24.7± 1.3

21.3± 1.2

46.5± 1.0

51.0± 1.0

54.7± 0.9

QuantLM 390M 8-Bit

24.6± 1.3

21.2± 1.2

46.6± 1.0

51.0± 1.0

54.6± 0.9

QuantLM 390M 6-Bit

24.8± 1.3

21.5± 1.2

46.8± 1.0

51.8± 1.0

55.3± 0.9

QuantLM 390M 4-Bit

25.1± 1.3

21.3± 1.2

45.2± 1.0

49.6± 1.0

50.8± 0.9

QuantLM 390M 3-Bit

24.9± 1.3

21.5± 1.2

41.6± 1.0

43.6± 1.0

56.3± 0.9

TriLM 390M

24.5± 1.3

21.2± 1.2

44.1± 1.0

48.6± 1.0

55.1± 0.9

Pythia 410M

24.7± 1.3

21.2± 1.2

45.7± 1.0

51.6± 1.0

60.0± 0.9

FloatLM 560M

26.5± 1.3

23.9± 1.2

48.4± 1.0

54.4± 1.0

57.9± 0.9

QuantLM 560M 8-Bit

26.5± 1.3

23.6± 1.2

48.3± 1.0

54.1± 1.0

57.6± 0.9

QuantLM 560M 6-Bit

26.0± 1.3

23.5± 1.2

47.6± 1.0

54.2± 1.0

57.3± 0.9

QuantLM 560M 4-Bit

25.9± 1.3

23.0± 1.2

46.3± 1.0

52.4± 1.0

58.8± 0.9

QuantLM 560M 3-Bit

24.0± 1.2

21.2± 1.2

42.3± 1.0

45.8± 1.0

59.0± 0.9

TriLM 560M

25.7± 1.3

21.0± 1.2

45.5± 1.0

50.2± 1.0

57.3± 0.9

Binary 560M

24.6± 1.2

20.2± 1.1

41.9± 1.0

47.8± 1.0

61.5± 0.8

FloatLM 830M

28.0± 1.3

24.5± 1.3

51.6± 1.0

57.3± 1.0

61.0± 0.9

QuantLM 830M 8-Bit

28.2± 1.3

25.1± 1.3

51.7± 1.0

57.3± 1.0

60.9± 0.9

QuantLM 830M 6-Bit

27.6± 1.3

24.7± 1.3

51.6± 1.0

57.7± 1.0

61.3± 0.9

QuantLM 830M 4-Bit

27.6± 1.3

23.3± 1.2

50.5± 1.0

56.2± 1.0

58.1± 0.9

QuantLM 830M 3-Bit

27.1± 1.3

22.7± 1.2

46.8± 1.0

50.5± 1.0

56.3± 0.9

TriLM 830M

25.3± 1.3

22.5± 1.2

48.7± 1.0

54.2± 1.0

60.4± 0.9

Pythia 1B

27.0± 1.3

24.4± 1.3

49.0± 1.0

57.0± 1.0

60.8± 0.9

FloatLM 1.1B

29.1± 1.3

26.1± 1.3

54.0± 1.0

60.4± 1.0

62.9± 0.8

QuantLM 1.1B 8-Bit

28.9± 1.3

26.1± 1.3

54.1± 1.0

60.2± 1.0

62.6± 0.8

QuantLM 1.1B 6-Bit

29.8± 1.3

25.5± 1.3

54.3± 1.0

60.2± 1.0

62.9± 0.8

QuantLM 1.1B 4-Bit

30.3± 1.3

26.0± 1.3

53.6± 1.0

59.0± 1.0

61.3± 0.9

QuantLM 1.1B 3-Bit

29.2± 1.3

27.0± 1.3

48.9± 1.0

55.0± 1.0

62.1± 0.8

TriLM 1.1B

26.5± 1.3

24.6± 1.3

49.8± 1.0

56.3± 1.0

59.1± 0.9

Binary 1.1B

24.8± 1.3

22.3± 1.2

46.1± 1.0

52.7± 1.0

56.3± 0.9

Pythia 1.4B

28.7± 1.3

26.0± 1.3

54.0± 1.0

60.4± 1.0

63.2± 0.8

FloatLM 1.5B

29.7± 1.3

26.2± 1.3

56.4± 1.0

62.6± 1.0

63.2± 0.8

QuantLM 1.5B 8-Bit

29.8± 1.3

26.0± 1.3

56.6± 1.0

62.4± 1.0

63.3± 0.8

QuantLM 1.5B 6-Bit

30.1± 1.3

26.0± 1.3

56.8± 1.0

62.2± 1.0

63.4± 0.8

QuantLM 1.5B 4-Bit

29.4± 1.3

26.9± 1.3

55.2± 1.0

60.4± 1.0

62.5± 0.8

QuantLM 1.5B 3-Bit

27.8± 1.3

25.2± 1.3

49.7± 1.0

54.8± 1.0

53.7± 0.9

TriLM 1.5B

28.2± 1.3

24.7± 1.3

53.1± 1.0

59.0± 1.0

54.1± 0.9

FloatLM 2.4B

32.7± 1.4

30.1± 1.3

60.5± 1.0

65.5± 1.0

62.1± 0.8

QuantLM 2.4B 8-Bit

32.6± 1.4

30.0± 1.3

60.3± 1.0

65.7± 1.0

62.1± 0.8

QuantLM 2.4B 6-Bit

32.7± 1.4

30.6± 1.3

60.4± 1.0

65.4± 1.0

62.0± 0.8

QuantLM 2.4B 4-Bit

33.3± 1.4

30.8± 1.3

59.6± 1.0

64.1± 1.0

59.0± 0.9

QuantLM 2.4B 3-Bit

29.7± 1.3

28.4± 1.3

54.2± 1.0

58.4± 1.0

55.7± 0.9

TriLM 2.4B

29.9± 1.3

29.5± 1.3

58.0± 1.0

63.8± 1.0

64.4± 0.8

FloatLM 3.9B

34.6± 1.4

32.1± 1.4

63.0± 1.0

68.3± 1.0

65.9± 0.8

QuantLM 3.9B 8-Bit

34.6± 1.4

31.9± 1.4

63.0± 1.0

68.1± 1.0

65.4± 0.8

QuantLM 3.9B 6-Bit

35.1± 1.4

32.1± 1.4

63.3± 1.0

68.0± 1.0

65.6± 0.8

QuantLM 3.9B 4-Bit

34.7± 1.4

32.9± 1.4

61.2± 1.0

68.3± 1.0

65.4± 0.8

QuantLM 3.9B 3-Bit

32.1± 1.4

29.3± 1.3

55.5± 1.0

62.1± 1.0

60.0± 0.9

TriLM 3.9B

35.3± 1.4

31.9± 1.4

60.8± 1.0

66.0± 1.0

66.5± 0.8

Table 7: Spectra Suite Performance (Part 1): Arc Challenge, Arc Easy, and BoolQ. Additionally, we
also include scores on the Pythia LLM suite.

32

Published as a conference paper at ICLR 2025

Models

HellaSwag
Acc Norm.

WinoGrande

Avg ( HellaSwag, PIQA, WinoGrande,

Acc

Acc Norm.

PIQA
Acc

Acc

Arc Easy, Arc Challenge, and BoolQ)

Pythia 70M

25.1± 0.4

25.1± 0.4

49.8± 1.2

49.9± 1.2

49.1± 1.4

34.9

FloatLM 99M

31.6± 0.5

29.1± 0.5

62.8± 1.1

63.2± 1.1

50.2± 1.4

44.3

QuantLM 99M 8-Bit

31.7± 0.5

29.0± 0.5

62.6± 1.1

63.0± 1.1

50.0± 1.4

44.3

QuantLM 99M 6-Bit

31.7± 0.5

29.2± 0.5

62.8± 1.1

63.1± 1.1

50.2± 1.4

44.3

QuantLM 99M 4-Bit

31.0± 0.5

28.9± 0.5

62.2± 1.1

60.9± 1.1

50.4± 1.4

42.6

QuantLM 99M 3-Bit

29.2± 0.5

27.7± 0.4

57.2± 1.2

58.2± 1.2

49.2± 1.4

40.3

TriLM 99M

28.4± 0.5

27.6± 0.4

60.1± 1.1

60.4± 1.1

50.7± 1.4

43.5

Binary 99M

27.7± 0.4

27.2± 0.4

59.2± 1.1

59.2± 1.1

48.8± 1.4

39.8

Pythia 160M

25.1± 0.4

25.0± 0.4

53.1± 1.2

53.1± 1.2

47.3± 1.4

35.7

FloatLM 190M

36.6± 0.5

31.4± 0.5

65.6± 1.1

64.8± 1.1

51.9± 1.4

46.7

QuantLM 190M 8-Bit

36.5± 0.5

31.4± 0.5

65.6± 1.1

64.8± 1.1

51.7± 1.4

46.8

QuantLM 190M 6-Bit

36.3± 0.5

31.5± 0.5

65.6± 1.1

64.3± 1.1

51.9± 1.4

46.4

QuantLM 190M 4-Bit

26.0± 0.4

25.7± 0.4

49.3± 1.2

51.7± 1.2

51.0± 1.4

36.5

QuantLM 190M 3-Bit

32.0± 0.5

28.8± 0.5

58.1± 1.2

58.7± 1.1

50.1± 1.4

42.7

TriLM 190M

31.6± 0.5

29.0± 0.5

62.0± 1.1

62.3± 1.1

51.7± 1.4

42.4

FloatLM 390M

44.4± 0.5

35.7± 0.5

68.7± 1.1

68.4± 1.1

51.8± 1.4

48.5

QuantLM 390M 8-Bit

44.5± 0.5

35.7± 0.5

68.8± 1.1

68.6± 1.1

52.6± 1.4

48.6

QuantLM 390M 6-Bit

44.2± 0.5

35.6± 0.5

69.0± 1.1

68.4± 1.1

53.0± 1.4

48.9

QuantLM 390M 4-Bit

43.4± 0.5

35.1± 0.5

68.1± 1.1

68.3± 1.1

53.7± 1.4

47.7

QuantLM 390M 3-Bit

39.5± 0.5

32.9± 0.5

63.8± 1.1

63.2± 1.1

53.0± 1.4

46.5

TriLM 390M

37.9± 0.5

32.0± 0.5

64.7± 1.1

65.0± 1.1

52.2± 1.4

46.4

Pythia 410M

40.3± 0.5

33.8± 0.5

67.2± 1.1

66.3± 1.1

53.5± 1.4

48.6

FloatLM 560M

47.6± 0.5

37.7± 0.5

68.8± 1.1

69.0± 1.1

53.7± 1.4

50.5

QuantLM 560M 8-Bit

47.6± 0.5

37.7± 0.5

68.9± 1.1

68.9± 1.1

53.8± 1.4

50.4

QuantLM 560M 6-Bit

47.6± 0.5

37.7± 0.5

68.7± 1.1

68.8± 1.1

53.5± 1.4

50.1

QuantLM 560M 4-Bit

46.7± 0.5

37.0± 0.5

67.8± 1.1

67.1± 1.1

53.1± 1.4

49.8

QuantLM 560M 3-Bit

41.7± 0.5

33.4± 0.5

63.5± 1.1

63.2± 1.1

49.7± 1.4

46.7

TriLM 560M

41.5± 0.5

33.8± 0.5

67.2± 1.1

67.5± 1.1

53.1± 1.4

48.4

Binary 560M

36.4± 0.4

31.2± 0.4

64.6± 1.1

64.2± 1.1

52.8± 1.4

44.5

FloatLM 830M

51.3± 0.5

40.1± 0.5

71.4± 1.1

71.7± 1.1

56.4± 1.4

53.3

QuantLM 830M 8-Bit

51.4± 0.5

40.1± 0.5

71.2± 1.1

71.7± 1.1

55.9± 1.4

53.2

QuantLM 830M 6-Bit

51.5± 0.5

40.2± 0.5

71.3± 1.1

71.8± 1.0

56.2± 1.4

53.2

QuantLM 830M 4-Bit

50.2± 0.5

39.2± 0.5

70.6± 1.1

71.1± 1.1

56.0± 1.4

52.2

QuantLM 830M 3-Bit

45.5± 0.5

35.9± 0.5

66.1± 1.1

66.6± 1.1

53.5± 1.4

49.2

TriLM 830M

46.0± 0.5

36.8± 0.5

68.2± 1.1

68.4± 1.1

55.6± 1.4

50.7

Pythia 1B

47.2± 0.5

37.7± 0.5

69.3± 1.1

70.8± 1.1

53.2± 1.4

51.1

FloatLM 1.1B

55.2± 0.5

42.6± 0.5

72.2± 1.0

71.3± 1.1

56.3± 1.4

54.9

QuantLM 1.1B 8-Bit

55.2± 0.5

42.6± 0.5

72.1± 1.0

71.2± 1.1

56.2± 1.4

54.8

QuantLM 1.1B 6-Bit

54.9± 0.5

42.6± 0.5

71.9± 1.0

71.2± 1.1

56.1± 1.4

55.0

QuantLM 1.1B 4-Bit

54.9± 0.5

42.0± 0.5

71.6± 1.1

70.4± 1.1

54.8± 1.4

54.4

QuantLM 1.1B 3-Bit

51.3± 0.5

39.4± 0.5

69.4± 1.1

68.4± 1.1

54.8± 1.4

52.6

TriLM 1.1B

49.1± 0.5

38.8± 0.5

69.8± 1.1

69.3± 1.1

55.5± 1.4

51.6

Binary 1.1B

43.4± 0.5

35.1± 0.4

66.9± 1.1

68.3± 1.1

55.3± 1.4

47.1

Pythia 1.4B

52.0± 0.5

40.4± 0.5

70.8± 1.1

70.6± 1.1

57.1± 1.4

54.3

FloatLM 1.5B

57.8± 0.5

44.3± 0.5

73.9± 1.0

73.1± 1.0

59.4± 1.4

56.7

QuantLM 1.5B 8-Bit

57.8± 0.5

44.3± 0.5

73.7± 1.0

73.1± 1.0

59.4± 1.4

56.8

QuantLM 1.5B 6-Bit

57.5± 0.5

44.2± 0.5

74.0± 1.0

73.0± 1.0

59.7± 1.4

56.9

QuantLM 1.5B 4-Bit

56.9± 0.5

43.2± 0.5

72.7± 1.0

72.4± 1.0

57.1± 1.4

55.6

QuantLM 1.5B 3-Bit

53.7± 0.5

41.0± 0.5

70.0± 1.1

69.4± 1.1

55.0± 1.4

51.6

TriLM 1.5B

53.1± 0.5

40.9± 0.5

70.1± 1.1

70.3± 1.1

56.1± 1.4

52.5

FloatLM 2.4B

62.7± 0.5

47.1± 0.5

75.2± 1.0

74.9± 1.0

61.8± 1.4

59.2

QuantLM 2.4B 8-Bit

62.7± 0.5

47.1± 0.5

75.4± 1.0

74.9± 1.0

61.4± 1.4

59.1

QuantLM 2.4B 6-Bit

62.9± 0.5

47.0± 0.5

75.7± 1.0

74.7± 1.0

61.1± 1.4

59.1

QuantLM 2.4B 4-Bit

62.2± 0.5

46.5± 0.5

75.4± 1.0

74.5± 1.0

61.7± 1.4

58.5

QuantLM 2.4B 3-Bit

58.6± 0.5

43.5± 0.5

72.7± 1.0

70.8± 1.1

57.2± 1.4

54.7

TriLM 2.4B

59.0± 0.5

45.3± 0.5

72.6± 1.0

71.4± 1.1

59.7± 1.4

57.3

FloatLM 3.9B

66.1± 0.5

49.7± 0.5

75.8± 1.0

75.4± 1.0

62.8± 1.4

61.4

QuantLM 3.9B 8-Bit

66.0± 0.5

49.7± 0.5

75.9± 1.0

75.5± 1.0

62.9± 1.4

61.3

QuantLM 3.9B 6-Bit

65.9± 0.5

49.7± 0.5

75.5± 1.0

75.6± 1.0

62.2± 1.4

61.3

QuantLM 3.9B 4-Bit

65.0± 0.5

49.0± 0.5

75.5± 1.0

75.6± 1.0

62.7± 1.4

60.7

QuantLM 3.9B 3-Bit

61.2± 0.5

45.9± 0.5

72.6± 1.0

72.3± 1.0

59.3± 1.4

56.8

TriLM 3.9B

64.7± 0.5

48.3± 0.5

74.6± 1.0

74.4± 1.0

62.1± 1.4

60.7

Table 8: Spectra Suite Performance (Part 2): HellaSwag, PIQA, WinoGrande, and Average Scores
(including Arc Easy, Arc Challenge, and BoolQ). Additionally, we include scores from the Pythia
LLM suite.

33

Published as a conference paper at ICLR 2025

Models

Arc Challenge
Acc Norm.

Arc Easy

Acc

Acc Norm.

BoolQ
Acc

HellaSwag

Acc

Acc Norm.

PIQA
Acc

WinoGrande

Acc Norm.

Acc

Avg

Acc

BitNet 700M

21.4

51.8

58.2

35.1

68.1

55.2

48.3

BitNet 1.3B

24.2

54.9

56.7

37.7

68.8

55.8

49.7

BitNet 3B

28.3

61.4

61.5

42.9

71.5

59.3

54.2

BitNet 3.9B

28.7

64.2

63.5

44.2

73.2

60.5

55.7

Table 9: Performance of BitNet b1.58 on ARC Challenge, ARC Easy, BoolQ, HellaSwag, PIQA, and WinoGrande. The scores are taken from (Ma et al., 2024).

D.3

T OXICITY

We report toxicity-based evaluation in 15. Each is considered in a zero-shot setting.
The toxicity-based evaluation included the following tasks:
• BBQ (Parrish et al., 2022): The Bias Benchmark for QA (BBQ) dataset, comprises sets of
questions developed by its authors, focusing on documented social biases directed towards
individuals from protected classes across nine distinct social dimensions pertinent to U.S.
English-speaking environments.
• Crows Pairs (Nangia et al., 2020): proposed a challenging dataset aimed at quantifying
stereotypical biases embedded within language models, with a specific emphasis on U.S.
contexts. Hosted on GitHub, this dataset serves as a crucial resource for assessing and
addressing biases through paired sentences that illuminate societal stereotypes.
• TruthfulQA (Lin et al., 2021): A benchmark designed to evaluate the truthfulness of
language models in generating responses to questions. This benchmark includes 817
questions across 38 categories, such as health, law, finance, and politics.
D.4

P ERPLEXITY ON OTHER DATASETS
TriLM vs FloatLM Perplexity Across Other Corpora

4.0

Model

Cross Entropy (Log Perplexity)

FloatLM 3.9B
TriLM 3.9B

3.5

3.0

2.5

2.0

1.5

Op

a

bad

am

IL
enA

e
Tre
enn

k
Ban

C4

P

ped

mo

Cos

ia

Dol

ma

rc
S2O

iped

Wik

ia

ined

Ref

b
We

Figure 18: Cross-entropy (log perplexity) comparison between TriLM and FloatLM (both 3.9B parameters)
across various datasets apart from SlimPajama.

We measure perplexity using TriLM 3.9B and FloatLM 3.9B across various other corpora than
SlimPajama, which was used for training. These corpora include OpenAI Lambada, Penn Tree Bank,
C4, Cosmopedia, Dolma, S2Orc, Wikipedia, and RefinedWeb. A portion of Wikipedia, C4 is included
in Slim Pajama. Some other corpora like Dolma and RefinedWeb, may also have overlaps from C4,
Wikipedia as well as Common Crawl.
Figure 18 demonstrates that while TriLM 3.9B is similar or better than FloatLM 3.9B on PTB
and Lambada, across the other datasets, with potential overlaps with SlimPajama, it’s performance
is consistently worse - indicating lower capability to memorize training data as well as worse
in-distribution performance, despite competitive out of distribution performance.
34

Published as a conference paper at ICLR 2025

Models

LAMBADA
Perp.
Acc

SciQ
Acc Norm.

Acc

LogiQA
Acc Norm.
Acc

FloatLM 99M
QuantLM 99M 8-Bit
QuantLM 99M 6-Bit
QuantLM 99M 4-Bit
QuantLM 99M 3-Bit
TriLM 99M
Binary 99M

85.0± 6.9
85.8± 7.0
89.9± 7.4
211.6± 17.3
4765.4± 413.0
172.0± 8.4
468.3± 24.1

26.5± 0.6
26.6± 0.6
26.1± 0.6
16.7± 0.5
4.5± 0.3
20.0± 0.6
14.0± 0.4

62.9± 1.5
62.8± 1.5
61.8± 1.5
61.2± 1.5
51.9± 1.6
60.4± 1.5
54.4± 1.6

73.6± 1.4
73.7± 1.4
73.9± 1.4
70.7± 1.4
57.0± 1.6
67.6± 1.5
62.5± 1.5

27.6± 1.8
27.8± 1.8
28.1± 1.8
24.9± 1.7
25.3± 1.7
25.5± 1.7
27.0± 1.7

21.2± 1.6
21.0± 1.6
20.3± 1.6
20.7± 1.6
19.8± 1.6
21.5± 1.6
22.3± 1.6

FloatLM 190M
QuantLM 190M 8-Bit
QuantLM 190M 6-Bit
QuantLM 190M 4-Bit
QuantLM 190M 3-Bit
TriLM 190M

50.3± 2.7
48.7± 2.6
55.3± 3.0
72479077.3
664.5± 41.1
130.7± 6.5

31.1± 0.6
31.5± 0.6
30.0± 0.6
0.00± 0.0
12.4± 0.5
23.7± 0.6

65.1± 1.5
65.5± 1.5
64.2± 1.5
25.6± 1.4
58.5± 1.6
61.0± 1.5

77.3± 1.3
77.1± 1.3
77.0± 1.3
22.9± 1.3
66.4± 1.5
72.6± 1.4

27.2± 1.7
27.0± 1.7
26.1± 1.7
23.3± 1.7
26.3± 1.7
25.5± 1.7

22.1± 1.6
22.3± 1.6
22.4± 1.6
20.7± 1.6
21.0± 1.6
21.5± 1.6

FloatLM 390M
QuantLM 390M 8-Bit
QuantLM 390M 6-Bit
QuantLM 390M 4-Bit
QuantLM 390M 3-Bit
TriLM 390M

21.9± 0.9
21.7± 0.9
24.3± 1.0
30.2± 1.3
115.0± 5.6
77.7± 3.8

42.2± 0.7
42.3± 0.7
40.6± 0.7
39.1± 0.7
23.0± 0.6
28.0± 0.6

75.6± 1.4
75.7± 1.4
75.5± 1.4
77.1± 1.3
67.4± 1.5
68.6± 1.5

84.2± 1.2
84.1± 1.2
83.7± 1.2
84.1± 1.2
76.7± 1.3
76.9± 1.3

28.1± 1.8
28.3± 1.8
27.6± 1.8
25.8± 1.7
25.7± 1.7
26.4± 1.7

23.8± 1.7
24.1± 1.7
23.2± 1.7
23.3± 1.7
21.8± 1.6
21.8± 1.6

FloatLM 560M
QuantLM 560M 8-Bit
QuantLM 560M 6-Bit
QuantLM 560M 4-Bit
QuantLM 560M 3-Bit
TriLM 560M
Binary 560M

20.8± 0.9
20.9± 0.9
21.7± 0.9
24.9± 1.1
146.3± 7.1
55.6± 2.7
62.8± 3.0

44.1± 0.7
44.2± 0.7
42.8± 0.7
40.8± 0.7
20.1± 0.6
32.4± 0.7
31.0± 0.6

74.7± 1.4
74.7± 1.4
74.4± 1.4
73.6± 1.4
71.1± 1.4
70.8± 1.4
70.0± 1.4

83.5± 1.2
83.6± 1.2
83.6± 1.2
82.0± 1.2
75.9± 1.4
78.7± 1.3
78.8± 1.3

27.0± 1.7
27.3± 1.7
25.8± 1.7
27.0± 1.7
25.0± 1.7
26.1± 1.7
26.7± 1.7

20.7± 1.6
20.7± 1.6
20.9± 1.6
21.7± 1.6
21.8± 1.6
19.8± 1.6
21.5± 1.6

FloatLM 830M
QuantLM 830M 8-Bit
QuantLM 830M 6-Bit
QuantLM 830M 4-Bit
QuantLM 830M 3-Bit
TriLM 830M

13.3± 0.5
13.5± 0.5
13.3± 0.5
15.4± 0.6
47.7± 2.0
26.0± 1.1

49.6± 0.7
49.4± 0.7
49.1± 0.7
47.3± 0.7
30.5± 0.6
39.9± 0.7

78.4± 1.3
78.5± 1.3
77.8± 1.3
78.8± 1.3
74.1± 1.4
75.4± 1.4

85.9± 1.1
86.1± 1.1
85.4± 1.1
85.1± 1.1
80.1± 1.3
82.8± 1.2

26.3± 1.7
26.6± 1.7
26.3± 1.7
25.5± 1.7
28.1± 1.8
27.6± 1.8

20.1± 1.6
20.0± 1.6
20.1± 1.6
21.2± 1.6
21.2± 1.6
21.4± 1.6

FloatLM 1.1B
QuantLM 1.1B 8-Bit
QuantLM 1.1B 6-Bit
QuantLM 1.1B 4-Bit
QuantLM 1.1B 3-Bit
TriLM 1.1B
Binary 1.1B

11.7± 0.4
11.7± 0.4
11.7± 0.4
13.9± 0.5
26.9± 1.1
17.3± 0.7
33.4± 1.4

51.2± 0.7
51.2± 0.7
51.0± 0.7
49.3± 0.7
39.1± 0.7
46.2± 0.7
37.6± 0.6

82.2± 1.2
82.1± 1.2
82.3± 1.2
81.2± 1.2
78.7± 1.3
73.3± 1.4
71.1± 1.4

88.1± 1.0
88.1± 1.0
88.1± 1.0
87.6± 1.0
85.0± 1.1
81.9± 1.2
81.2± 1.3

27.3± 1.7
27.8± 1.8
27.5± 1.8
28.4± 1.8
25.8± 1.7
26.9± 1.7
28.4± 1.7

20.9± 1.6
21.2± 1.6
21.5± 1.6
20.3± 1.6
20.7± 1.6
22.0± 1.6
23.2± 1.6

FloatLM 1.5B
QuantLM 1.5B 8-Bit
QuantLM 1.5B 6-Bit
QuantLM 1.5B 4-Bit
QuantLM 1.5B 3-Bit
TriLM 1.5B

9.4± 0.3
9.5± 0.3
9.5± 0.3
10.4± 0.4
17.8± 0.7
16.4± 0.7

55.5± 0.7
55.5± 0.7
55.4± 0.7
53.0± 0.7
45.3± 0.7
46.2± 0.7

80.9± 1.2
81.3± 1.2
81.4± 1.2
81.1± 1.2
75.5± 1.4
80.7± 1.2

87.4± 1.0
87.5± 1.0
87.6± 1.0
86.9± 1.1
82.1± 1.2
87.3± 1.1

26.1± 1.7
25.7± 1.7
25.7± 1.7
25.7± 1.7
28.4± 1.8
27.8± 1.8

20.9± 1.6
20.6± 1.6
20.3± 1.6
20.3± 1.6
22.7± 1.6
21.5± 1.6

FloatLM 2.4B
QuantLM 2.4B 8-Bit
QuantLM 2.4B 6-Bit
QuantLM 2.4B 4-Bit
QuantLM 2.4B 3-Bit
TriLM 2.4B

7.7± 0.3
7.7± 0.3
7.9± 0.3
8.9± 0.3
15.6± 0.6
8.6± 0.3

59.3± 0.7
59.2± 0.7
58.9± 0.7
56.1± 0.7
45.0± 0.7
55.7± 0.7

87.2± 1.1
87.1± 1.1
87.3± 1.1
84.8± 1.1
79.9± 1.3
84.2± 1.2

91.0± 0.9
91.0± 0.9
90.9± 0.9
89.7± 1.0
86.7± 1.1
88.7± 1.0

29.5± 1.8
29.5± 1.8
29.6± 1.8
29.6± 1.8
28.6± 1.8
28.6± 1.8

21.5± 1.6
21.5± 1.6
20.9± 1.6
20.9± 1.6
21.4± 1.6
24.3± 1.7

FloatLM 3.9B
QuantLM 3.9B 8-Bit
QuantLM 3.9B 6-Bit
QuantLM 3.9B 4-Bit
QuantLM 3.9B 3-Bit
TriLM 3.9B

6.7± 0.2
6.7± 0.2
6.8± 0.2
7.4± 0.2
14.0± 0.5
6.3± 0.2

61.1± 0.7
61.1± 0.7
60.8± 0.7
58.5± 0.7
47.1± 0.7
61.6± 0.7

86.5± 1.1
86.2± 1.1
86.6± 1.1
86.1± 1.1
83.1± 1.2
87.4± 1.0

90.9± 0.9
91.0± 0.9
91.3± 0.9
90.8± 0.9
88.6± 1.0
90.8± 0.9

26.9± 1.7
26.6± 1.7
25.8± 1.7
28.6± 1.8
27.0± 1.7
27.6± 1.8

20.9± 1.6
20.6± 1.6
20.4± 1.6
20.1± 1.6
21.5± 1.6
22.7± 1.6

Table 10: Spectra Suite Performance (Part 3): LAMBADA OpenAI, SciQ, LogiQA. We additionally also
include Pythia’s performance scores.

35

Published as a conference paper at ICLR 2025

D.5

O MNI Q UANT: 3-B IT P OST-T RAINING Q UANTIZED M ODELS

We present additional 3-bit quantized (QuantLM 3-bit) models, which were trained using OmniQuant
(Shao et al., 2024) for 5 iterations with a group size of one row. It is important to highlight that the
performance benchmarks for these models are consistent with those of GPT-Q, as reported in Tables
7, 8, 10, 15, and 16. Therefore, these results do not affect our findings in the main paper.
Tasks

Metric

99M

190M

390M

560M

1.1B

ARC Challenge

Acc.
Acc. (Norm.)

0.19 ± 0.01
0.23 ± 0.01

0.21 ± 0.01
0.24 ± 0.01

0.22 ± 0.01
0.26 ± 0.01

0.22 ± 0.01
0.24 ± 0.01

0.24 ± 0.01
0.26 ± 0.01

ARC Easy

Acc.
Acc. (Norm.)

0.37 ± 0.01
0.34 ± 0.01

0.41 ± 0.01
0.38 ± 0.01

0.45 ± 0.01
0.41 ± 0.01

0.48 ± 0.01
0.42 ± 0.01

0.55 ± 0.01
0.48 ± 0.01

BoolQ

Acc.

0.55 ± 0.01

0.54 ± 0.01

0.62 ± 0.01

0.57 ± 0.01

0.63 ± 0.01

HellaSwag

Acc.
Acc. (Norm.)

0.28 ± 0.00
0.29 ± 0.00

0.29 ± 0.00
0.32 ± 0.00

0.32 ± 0.00
0.39 ± 0.00

0.34 ± 0.00
0.41 ± 0.00

0.38 ± 0.00
0.48 ± 0.01

LAMBADA

Acc.

0.05 ± 0.00

0.07 ± 0.00

0.23 ± 0.01

0.25 ± 0.01

0.31 ± 0.01

LogiQA

Acc.
Acc. (Norm.)

0.16 ± 0.01
0.23 ± 0.02

0.20 ± 0.02
0.25 ± 0.02

0.23 ± 0.02
0.29 ± 0.02

0.23 ± 0.02
0.28 ± 0.02

0.21 ± 0.02
0.27 ± 0.02

PIQA

Acc.
Acc. (Norm.)

0.58 ± 0.01
0.58 ± 0.01

0.59 ± 0.01
0.59 ± 0.01

0.63 ± 0.01
0.63 ± 0.01

0.65 ± 0.01
0.66 ± 0.01

0.69 ± 0.01
0.69 ± 0.01

SciQ

Acc.
Acc. (Norm.)

0.55 ± 0.02
0.49 ± 0.02

0.64 ± 0.02
0.59 ± 0.02

0.74 ± 0.01
0.61 ± 0.02

0.77 ± 0.01
0.68 ± 0.01

0.82 ± 0.01
0.73 ± 0.01

TriviaQA

Exact Match

0.00 ± 0.00

0.00 ± 0.00

0.01 ± 0.00

0.01 ± 0.00

0.05 ± 0.00

Winogrande

Acc.

0.51 ± 0.01

0.50 ± 0.01

0.51 ± 0.01

0.53 ± 0.01

0.56 ± 0.01

MMLU

Acc.

0.25 ± 0.00

0.25 ± 0.00

0.26 ± 0.00

0.27 ± 0.00

0.29 ± 0.00

Table 11: Model performance of 3-bit post-training quantized models using OmniQuant across various tasks,
from 99M to 1.1B parameters, evaluated on different metrics.
Tasks

Metric

1.5B

2.4B

ARC Challenge

Acc.
Acc. (Norm.)

0.26 ± 0.01
0.29 ± 0.01

0.27 ± 0.01
0.30 ± 0.01

ARC Easy

Acc.
Acc. (Norm.)

0.56 ± 0.01
0.51 ± 0.01

0.60 ± 0.01
0.53 ± 0.01

BoolQ

Acc.

0.59 ± 0.01

0.63 ± 0.01

HellaSwag

Acc.
Acc. (Norm.)

0.40 ± 0.00
0.51 ± 0.01

0.44 ± 0.00
0.57 ± 0.00

LAMBADA

Acc.

0.35 ± 0.01

0.44 ± 0.01

LogiQA

Acc.
Acc. (Norm.)

0.23 ± 0.02
0.26 ± 0.02

0.19 ± 0.02
0.30 ± 0.02

PIQA

Acc.
Acc. (Norm.)

0.69 ± 0.01
0.70 ± 0.01

0.71 ± 0.01
0.72 ± 0.01

SciQ

Acc.
Acc. (Norm.)

0.82 ± 0.01
0.76 ± 0.01

0.86 ± 0.01
0.80 ± 0.01

TriviaQA

Exact Match

0.07 ± 0.00

0.07 ± 0.00

Winogrande

Acc.

0.56 ± 0.01

0.58 ± 0.01

MMLU

Acc.

0.28 ± 0.00

0.30 ± 0.00

Table 12: Performance of 3-bit Post-Training Quantized Models using OmniQuant across Various Tasks, from
1.5B to 2.4B parameters, across different tasks and metrics.

36

Published as a conference paper at ICLR 2025

MMLU Stem Acc Across Size (Bits)

29

28

27

27

Acc (log scale)

28

Acc

26
25
24

FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM

23
1

10

20
30
40
Size in bits (109)

50

26
25
24

22

60

190M

560M
Parameters

1.5B

3.9B

MMLU Social Sciences Acc Across Size (Bits)

MMLU Social Sciences Acc Across Parameters

36

36

34

34

32
30
FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM

28
26
1

10

20
30
40
Size in bits (109)

50

30
28
26

60

28

28

Acc (log scale)

30

26

22

FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM
1

10

20
30
40
Size in bits (109)

50

22

40

35

Acc (log scale)

Acc
30

1.5B

3.9B

FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM

24

60

35

560M
Parameters

26

MMLU Other Acc Across Size (Bits)

40

25

190M

MMLU Humanities Acc Across Parameters

30

24

FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM

32

MMLU Humanities Acc Across Size (Bits)

Acc

FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM

23

Acc (log scale)

Acc

22

MMLU Stem Acc Across Parameters

29

190M

560M
Parameters

1.5B

3.9B

MMLU Other Acc Across Parameters
FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM

30

FloatLM
QuantLM 4-Bit
QuantLM 3-Bit
TriLM
1

10

20
30
40
Size in bits (109)

50

25

60

190M

560M
Parameters

1.5B

3.9B

Figure 19: Model performance on MMLU subsets: STEM, Humanities, Social Sciences, and others. Plot
accuracy scores against model size in bits (left) and number of parameters (right), ranging from 560M to 3.9B
parameters for TriLM (ternary), FloatLM (FP16), and QuantLM (3-bit & 4-bit).

37

Published as a conference paper at ICLR 2025

W EIGHT D ISTRIBUTION OF L INEAR L AYERS
FloatLM 99M

15.0

10.0
7.5

Frequency

12.5

12.5

Frequency

Frequency

FloatLM 390M
17.5

15.0

15.0

10.0
7.5

12.5
10.0
7.5

5.0

5.0

5.0

2.5

2.5

2.5

0.0

0.0

0.4

0.2

0.0

0.2

Weight Value

0.4

FloatLM 560M
17.5
15.0
12.5

Frequency

Frequency

FloatLM 190M

17.5

17.5

10.0
7.5
5.0
2.5
0.0

0.4

0.2

0.0

0.2

Weight Value

0.4

20.0
17.5
15.0
12.5
10.0
7.5
5.0
2.5
0.0

0.4

0.2

0.0

0.2

Weight Value

0.0

0.4

FloatLM 830M

Frequency

E

0.4

FloatLM 1.5B

0.2

0.0

0.2

Weight Value

0.4

20.0
17.5
15.0
12.5
10.0
7.5
5.0
2.5
0.0

FloatLM 2.4B

20

20

15

15

0.4

0.2

0.0

0.2

Weight Value

0.4

FloatLM 1.1B

0.4

0.2

0.0

0.2

Weight Value

0.4

FloatLM 3.9B

25

10
5
0

Frequency

Frequency

Frequency

20

10
5

0.4

0.2

0.0

0.2

Weight Value

0.4

0

15
10
5

0.4

0.2

0.0

0.2

Weight Value

0.4

0

0.4

0.2

0.0

0.2

Weight Value

0.4

Figure 20: Weight distribution in the linear layers of FloatLM models across various model sizes, ranging from
99M to 3.9B parameters

The observed Gaussian distribution in the weights of our final trained FloatLM models across various
scales is supported by both theoretical foundations and empirical evidence. We outline the rationale
for the normality of weight distributions as follows:
Empirical Consistency: Across all model scales, ranging from 99 million to 3.9 billion parameters,
the weight distributions consistently exhibit Gaussian characteristics, as illustrated in Figure 20. This
consistency is visually evident in distribution plots and quantitatively confirmed by fitting Gaussian
functions to the weight histograms, demonstrating a good fit across different model sizes.
Theoretical Underpinning: Neural network weight initialization typically follows a Gaussian
distribution to facilitate balanced learning dynamics. As training progresses, despite non-linear
transformations and complex interactions within the network, the Central Limit Theorem suggests
that the aggregation of numerous independent random variables (such as updates during backpropagation) tends toward a normal distribution. This tendency is particularly pronounced given the high
dimensionality and extensive data processing involved in training large language models.
Stabilization through Regularization and Optimization: Techniques such as L2 regularization
constrain weight magnitudes, encouraging them towards smaller values and contributing to a peak
around zero—a characteristic feature of Gaussian distributions. Additionally, optimization algorithms
like Adam, which adjust learning rates based on moving averages of recent gradients, promote
smoother updates. This approach maintains the Gaussian form by mitigating the impact of outlier
gradients.
Given these, we can assert that the weight distribution of our trained models closely follows a
Gaussian distribution which is crucial for understanding the weight variance across different scales.
38

Published as a conference paper at ICLR 2025

F

L EARNING DYNAMICS A NALYSIS OF P EAK LR DROP AND DECAY STAGE

In this section, we present a concise analysis of our learning dynamics, inspired by Appendix D
of MiniCPM (Hu et al., 2024). Specifically, we examine the impact of our two key interventions:
the peak learning rate reduction at the halfway point of training and the removal of weight decay
regularization at two-thirds of the training stage. This analysis explores loss dynamics through the
lens of checkpoint updates and gradient behavior.
We analyze both the latent weights and ternary weights, calculating the maximum weight element
update, maxij (W (t+1) ij − W (t) ij), across all weight matrices in the TriLM-1.5B model for each
training step. Our findings, consistent with observations from MiniCPM, reveal a strong correlation
between weight updates and the learning rate decay, as depicted in Figure 21. Notably, after the
weight decay regularization is removed at approximately 160,000 training iterations, the model
checkpoints undergo smaller updates. However, surprisingly during this stage, despite smaller weight
changes, the loss decreases at an accelerated pace.
Max Difference vs Iteration for attention.query_key_value.weight_2

attention.query_key_value.weight_2

0.04

0.4

Max Difference

Max Difference

Max
Difference vs Iteration for attention.query_key_value.weight_2
0.05

attention.query_key_value.weight_2

0.5

0.3
0.2
0.1

0.03
0.02
0.01

50000

100000

150000

Iteration of Checkpoint

200000

250000

50000

100000

150000

Iteration of Checkpoint

200000

250000

(a) latent weight updates for shard 0

(b) Ternary weight updates for shard 0

Max Difference vs Iteration for attention.query_key_value.weight_2

Max Difference vs Iteration for attention.query_key_value.weight_2

attention.query_key_value.weight_2

0.40
0.30

Max Difference

Max Difference

attention.query_key_value.weight_2

0.05

0.35
0.25
0.20
0.15

0.04
0.03
0.02

0.10
0.01

0.05
50000

100000

150000

Iteration of Checkpoint

200000

250000

50000

(c) latent weight updates for shard 1

100000

150000

Iteration of Checkpoint

200000

250000

(d) Ternary weight updates for shard 1

Figure 21: Max Difference of Checkpoints for Layer 2
Following the methodology of Hu et al. (2024), we examine gradient data by training a 190M
parameter TriLM model. We record the gradients at every step to obtain fine-grained values for
deriving second-order gradient information. In Figures 22 and 23, we plot the maximum, L2 norm,
first and second-order directional derivatives of the gradient, along with the cosine of the gradient
angle and the loss curvature along the training trajectory.
While the L2 norm and maximum of the gradient do not provide notable insights, the loss curvature
and second-order directional derivative show significant correlations with both the peak learning rate
reduction at 5000 steps and the removal of weight decay at 7500 steps. Interestingly, we also observe
an increase in the cosine of the gradients and a decrease in the first-order directional derivative
at both 5000 and 7500 steps, with trends becoming more pronounced after the removal of weight
regularization. Moreover, the trends for loss curvature along the parameter trajectory and the secondorder directional derivative are opposite for the latent and ternary gradient statistics. A more in dept
understanding these trends in the learning dynamics under our current training strategy for TriLM
offers a promising direction for future exploration.

39

Published as a conference paper at ICLR 2025

Gradient L2 Norm

0.015
0.010

Values

0.040
0.035
0

2000

4000

6000

Iteration

8000

10000

Maximum Gradient
0.0025
0.0020

0

2000

4000

6000

Iteration

8000

0.0010
0.0005
0

2000

4000

6000

Iteration

8000

10000

0.000

0.010

10000

0

Second Order Directional Derivative

0

2000

4000

6000

Iteration

8000

2000

4000

6000

8000

Iteration

10000

Cosine Of Gradient Angle

Values

Values

0.0015

0.40
0.35
0.30
0.25
0.20
0.15
0.10
0.05
0.00

0.005

0.005

Values

Values

0.045

First Order Directional Derivative

0.020

Values

0.055
0.050

Loss Curvature On Parameter Trajectory

0.40
0.35
0.30
0.25
0.20
0.15
0.10
0.05
0.00

0.060

0.8
0.6
0.4
0.2
0.0
0.2
0.4
0.6

10000

0

2000

4000

6000

Iteration

8000

10000

Figure 22: Latent gradient statistics over the training of 190M model. We drop the peaked learning rate at step
5000 and reduce the weight decay to 0 at step 7500

Ternary Gradient L2 Norm

Ternary Loss Curvature On Parameter Trajectory

0.060

Ternary First Order Directional Derivative

0.0005

0.055

Values

Values

Values

0.0004

0.050

0.0003

0.045
0.040

0.0002

0.035

0.0001
0

2000

4000

6000

Iteration

8000

10000

0

Ternary Maximum Gradient

2000

4000

6000

Iteration

8000

10000

0

Ternary Second Order Directional Derivative

0.0025

Values

Values

Values

0.0004

0.0015

0.0003

0.0010

0.0002

0.0005

0.0001
2000

4000

6000

Iteration

8000

10000

0

2000

4000

6000

Iteration

8000

10000

2000

4000

6000

Iteration

8000

0.8
0.6
0.4
0.2
0.0
0.2
0.4
0.6
0

2000

4000

6000

Iteration

8000

Figure 23: Ternary gradient statistics over the training of 190M model. We drop the peaked learning rate at
step 5000 and reduce the weight decay to 0 at step 7500

40

10000

Ternary Cosine Of Gradient Angle

0.0005

0.0020

0

0.00125
0.00100
0.00075
0.00050
0.00025
0.00000
0.00025
0.00050

10000

Published as a conference paper at ICLR 2025

G

M EMORY B OTTLENECKS AND L OW-B ITWIDTH L ANGUAGE M ODELLING

Recent observations (Gholami et al., 2024) suggest that, given the slower pace of improvements
in memory and communication compared to compute (FLOPs), the bottleneck continues to shift
away from computation towards the memory-related characteristics of hardware for deploying large
language models. This shift underscores the importance of exploring solutions that directly address
memory constraints. Below, we formally analyze this trend and the impact of low-bitwidth language
models on addressing memory bottlenecks during inference.
G.1

OVERVIEW OF R ECENT DATACENTER GPU S AND ACCELERATORS .

We begin our analysis by surveying a broad range of recent datacenter General Purpose GPUs (GPGPUs) employed for neural network development and research since 2018. This includes hardware
from multiple providers, covering various configurations across the latest microarchitectures.
From Nvidia, we consider the following:
• Volta: V100 (SXM/PCIe) (Nvidia Team, 2018),
• Ampere: A100 (40GB/80GB SXM/PCIe) (Nvidia Team, 2020),
• Hopper: H100 (SXM/PCIe) and H200 (Nvidia Team, 2022; 2023),
• Blackwell: This includes preliminary data for Blackwell microarchitectures, which at the
time of access were subject to change (Nvidia Team, 2024).
From AMD, we analyze the following models:
• MI200 Series: MI210, MI250, MI250X (AMD Team, 2022a;b),
• MI300 Series: MI300A, MI300X, MI325X (AMD Team, 2023a;b; 2024).
Additionally, we include hardware from Intel and Google:
• From Intel, the Gaudi Series: Gaudi 2 and Gaudi 3 (Intel Gaudi Team, 2024),
• From Google, the Tensor Processing Units (TPUs): TPUv3 (Google TPU Team, 2018),
TPUv4 (Google TPU Team, 2021), and TPUv5 (TPUv5e, TPUv5p) (Google TPU Team,
2023a;b).
All data was sourced from the respective datasheets, technical documentation, or press releases of the
cited hardware. Over the past several years, each of these four accelerator families has improved in
three areas - FLOPS, memory capacity, and bandwidth.
M EMORY T RENDS AND S PEEDUP O PPORTUNITIES IN L OW-B ITWIDTH L ANGUAGE
M ODELING
Trend of Decreasing Memory/FLOPS
0.008
0.006

19

20

21

22

23

24

25

20

20

20

20

20

0.000

20

0.002

Volta
Ampere
Hopper
Blackwell
MI200
MI300
Gaudi2
Gaudi3
TPUv3
TPUv4
TPUv5

20

0.004

18

25
20

24

23

20

22

20

20

21
20

20

19

20

20

(a) Memory Capacity vs Peak FLOPS

0.010

20

Peak Memory Bandwidth (TBPS) / Peak TFLOPS

Trend of Decreasing Bytes/FLOPS

Volta
Ampere
Hopper
Blackwell
MI200
MI300
Gaudi2
Gaudi3
TPUv3
TPUv4
TPUv5

20

0.40
0.35
0.30
0.25
0.20
0.15
0.10
0.05

18

Memory Capacity (GB) / Peak TFLOPS

G.2

(b) Peak Memory Bandwidth vs Peak FLOPS

Figure 24: Trends of Memory/FLOP and Bandwidth/FLOP across different (datacenter) GPGPUs.

41

Published as a conference paper at ICLR 2025

Memory Capacity and Bandwidth of GPGPUs Relative to Peak TFLOPs. In Figure 24a, we
show the trends of Memory Capacity over Peak TFLOPS (Half Precision - FP16/BF16) for various
accelerators over the years. We also perform a linear fit for each family of accelerators separately.
The linear fit for all the families has a downward slope, showing that memory capacity is improving
at a slower pace than computation capability. This trend holds true even for the most recent hardware,
such as Blackwell, MI325X, and Gaudi3. Though we consider Half-Precision TFLOPs, the slope is
expected to become steeper when considering peak TFLOPS over Ampere sparse or FP8. Similarly,
in Figure 24b, we present the trends of Memory Bandwidth (specifically for DRAM or its equivalent
memory) over FLOPs for the accelerators over the years, along with the linear fit for each family.
We observe a downward slope here as well, indicating the trend that memory bandwidth is growing
much slower than computation.
Comparison of model size and maximum speed up for quantized models: In this analysis, we
include transformer configurations from the LLaMa family (Touvron et al., 2023a;b). As larger
vocabularies in LLMs are becoming increasingly common for efficient multilingual modeling, we
use a vocabulary size of 128k from LLaMa 3 (AI@Meta, 2024) for our analysis. We assume the
Embedding and LM Head weights are retained in Half-Precision across all bitwidths. In Figure 25,
we provide the scaling plots of FloatLMs, QuantLMs and TriLMs in terms of model size (in GB) and
maximum speedup compared to the FloatLM baseline.

Models Size Growth across BitWidths

8xH100

FloatLM
QuantLM 4-Bit
TriLM

480GB

320GB

4xH100

192GB

MI300X

80GB

H100

7B

13B

34B

70B

Parameters (Log Scale)

180B

Maximum Speedup across BitWidths

10
Max Relative Speedup to FP16

640GB

6
4
2
7B

340B

(a) Model Size growth at various BitWidths

FloatLM
QuantLM 4-Bit
TriLM

8

13B

34B

70B

Parameters (Log Scale)

180B

340B

(b) Maximum Possible Speedup at different BitWidths

Figure 25: Expected gains from low bitwidth modeling. TriLMs can fit over 300B parameters on a single H100
and achieve up to a theoretical maximum of 10x faster autoregressive decoding compared to FloatLM.

42

Published as a conference paper at ICLR 2025

H

A BLATIONS

Table 14 and 13 shows the performance of ablation 100B token training runs over the six commonsense
benchmarks from BitNet b1.58 at 1.1B parameters. The first two rows show the performance of
TriLM 1.1B and Float 1.1B at this token count, followed by our replication of BitNet b1.58 (Ours) as
well as the scores from BitNet b1.58 over 700M and 1.3B parameters. We observe that at this scale,
TriLM does not come close to matching the performance of FloatLM, but it outperforms much larger
BitNets. The next two rows show the performance of TriLM 1.1B and FloatLM 1.1B when trained on
100B tokens of FineWeb, instead of SlimPajama. While the performance of both the models improves
on FineWeb, the average difference in their performance across datasets remains the same. Lastly,
we show the performances across various optimization schedules. A significant drop in averaged
performance is noticed when the baseline schedule of linear decay with constant weight decay is
used. The gains from dropping l2 regularization in the schedule are more than that of dropping the
peak learning rate, however, not enough to match that of TriLM 1.1B’s schedule.

Models

HellaSwag
Acc N.

PIQA
Acc

Acc N.

WinoGrande
Acc

Acc

FloatLM 1.1B

50.0 ± 0.5

39.3 ± 0.5

70.9 ± 1.0

70.1 ± 1.0

55.4 ± 1.4

TriLM 1.1B

46.8 ± 0.5

37.1 ± 0.4

69.4 ± 1.0

69.4 ± 1.0

53.8 ± 1.4

BitNet b1.58 1.1B (Ours)

47.0 ± 0.5

37.1 ± 0.4

69.4 ± 1.0

69.6 ± 1.0

53.4 ± 1.4

BitNet b1.58 700M

35.1

68.1

55.2

BitNet b1.58 1.3B

37.7

68.8

55.8

TriLM 1.1B FineWeb

50.0 ± 0.5

39.2 ± 0.4

70.2 ± 1.0

70.1 ± 1.0

56.6 ± 1.3

FloatLM 1.1B FineWeb

52.7 ± 0.5

41.1 ± 0.4

73.0 ± 1.0

71.3 ± 1.0

56.7 ± 1.3

TriLM 1.1B Only Peak LR Dropped

46.7 ± 0.5

36.8 ± 0.4

68.9 ± 1.0

69.5 ± 1.0

55.4 ± 1.4

TriLM 1.1B Only L2 Reg. Dropped

47.1 ± 0.5

37.5 ± 0.4

68.6 ± 1.0

69.4 ± 1.0

55.2 ± 1.4

TriLM 1.1B Baseline Schedule

46.0 ± 0.5

36.9 ± 0.4

69.3 ± 1.0

69.1 ± 1.0

56.2 ± 1.3

Table 13: Ablation Common Sense Task Performance: HellaSwag, PIQA, WinoGrande, Arc Easy, Arc
Challenge, BoolQ (Contd.). BitNet b1.58’s scores from Ma et al. (2024). All runs are for 100B tokens on Slim
Pajama, except those explicitly stated as FineWeb

Models

BoolQ

Avg ( HellaSwag, PIQA, WinoGrande,

Acc N.

Arc Challenge
Acc

Acc N.

Arc Easy
Acc

Acc

Arc Easy, Arc Challenge, and BoolQ)

FloatLM 1.1B

26.3 ± 1.3

22.5 ± 1.2

50.3 ± 1.0

56.8 ± 1.0

60.6 ± 0.8

52.2

TriLM 1.1B

26.7 ± 1.3

22.9 ± 1.2

49.7 ± 1.0

55.0 ± 1.0

54.9 ± 0.8

50.2

BitNet b1.58 1.1B (Ours)

26.1 ± 1.2

23.6 ± 1.2

47.7 ± 1.0

55.3 ± 1.0

49.7 ± 0.8

48.9

BitNet b1.58 700M

21.4

51.8

58.2

48.3

BitNet b1.58 1.3B

24.2

54.9

56.7

49.6

TriLM 1.1B FineWeb

31.7 ± 1.3

31.9 ± 1.3

63.1 ± 0.9

66.8 ± 0.9

58.3 ± 0.8

54.9

FloatLM 1.1B FineWeb

34.4 ± 1.3

33.0 ± 1.3

65.7 ± 0.9

70.2 ± 0.9

59.3 ± 0.8

56.9

TriLM 1.1B Only Peak LR Dropped

27.4 ± 1.3

23.6 ± 1.2

48.3 ± 1.0

55.1 ± 1.0

51.6 ± 0.8

49.7

TriLM 1.1B Only L2 Reg. Dropped

27.6 ± 1.3

24.8 ± 1.2

49.2 ± 1.0

55.1 ± 1.0

53.1 ± 0.8

50.1

TriLM 1.1B Baseline Schedule

26.2 ± 1.2

23.2 ± 1.2

48.0 ± 1.0

54.0 ± 1.0

49.4 ± 0.8

49.1

Table 14: Ablation Common Sense Task Performance: HellaSwag, PIQA, WinoGrande, Arc Easy, Arc
Challenge, BoolQ. BitNet b1.58’s scores from Ma et al. (2024). All runs are for 100B tokens on Slim Pajama,
except those explicitly stated as FineWeb

43

Published as a conference paper at ICLR 2025

Models

TriviaQA
Exact Match

CrowsPairs
Likelihood diff.
Pct stereotype

Big Bench BBQ Lite
Acc

TruthfulQA
Acc

FloatLM 99M
QuantLM 99M 8-Bit
QuantLM 99M 6-Bit
QuantLM 99M 4-Bit
QuantLM 99M 3-Bit
TriLM 99M
Binary 99M

0.6± 0.1
0.6± 0.1
0.6± 0.1
0.3± 0
0.1± 0
0.1± 0
0.2± 0.0

372.4± 14.6
370.9± 14.6
389.8± 14.8
425.5± 15.2
611.1± 18.8
362.4± 10.8
353.5± 11.1

55.4± 1.2
55.1± 1.2
56.9± 1.2
54.0± 1.2
51.0± 1.2
54.2± 1.2
53.3± 1.2

30.8± 0.4
26.5± 0.3
26.7± 0.3
26.2± 0.3
31.4± 0.4
30.8± 0.4
31.5± 0.3

24.4± 1.5
24.1± 1.5
24.2± 1.5
22.9± 1.5
24.6± 1.5
24.2± 1.5
25.7± 1.5

FloatLM 190M
QuantLM 190M 8-Bit
QuantLM 190M 6-Bit
QuantLM 190M 4-Bit
QuantLM 190M 3-Bit
TriLM 190M

0.6± 0.1
0.7± 0.1
0.7± 0.1
0.0± 0
0.1± 0
0.2± 0

348.2± 11.3
352.7± 11.4
368.9± 11.7
961.9± 25.4
482.7± 15.2
343.5± 10.9

55.9± 1.2
56.2± 1.2
56.2± 1.2
43.8± 1.2
53.7± 1.2
55.5± 1.2

27.3± 0.4
27.1± 0.4
27.2± 0.4
35.0± 0.4
26.4± 0.3
29.7± 0.4

22.4± 1.5
22.5± 1.5
22.5± 1.5
24.2± 1.5
25.0± 1.5
23.9± 1.5

FloatLM 390M
QuantLM 390M 8-Bit
QuantLM 390M 6-Bit
QuantLM 390M 4-Bit
QuantLM 390M 3-Bit
TriLM 390M

2.8± 0
2.9± 0
2.4± 0
1.3± 0.1
0.8± 0.1
1.3± 0.1

355.5± 10.4
355.8± 10.4
360.5± 10.4
368.2± 10.2
444.4± 12.2
344.5± 10.3

59.6± 1.2
59.8± 1.2
60.6± 1.2
59.4± 1.2
54.3± 1.2
58.3± 1.2

25.4± 0.3
25.4± 0.3
25.3± 0.3
25.5± 0.3
26.3± 0.3
26.9± 0.3

22.4± 1.5
22.2± 1.5
22.8± 1.5
22.8± 1.5
23.0± 1.5
24.4± 1.5

FloatLM 560M
QuantLM 560M 8-Bit
QuantLM 560M 6-Bit
QuantLM 560M 4-Bit
QuantLM 560M 3-Bit
TriLM 560M
Binary 560M

4.6± 0.2
4.7± 0.2
3.5± 0.1
2.1± 0.1
1.5± 0.1
2.4± 0.1
0.2± 0.0

351.8± 9.9
352.9± 10.0
353.7± 9.9
372.7± 10.7
411.2± 11.3
345.1± 10.1
356.3± 10.4

58.9± 1.2
59.2± 1.2
59.3± 1.2
59.2± 1.2
57.9± 1.2
58.7± 1.2
58.5± 1.2

25.7± 0.3
25.7± 0.3
25.8± 0.3
27.0± 0.4
29.0± 0.4
25.5± 0.3
26.3± 0.3

21.7± 1.4
21.8± 1.4
22.0± 1.5
22.2± 1.5
22.9± 1.5
23.6± 1.5
23.1± 1.4

FloatLM 830M
QuantLM 830M 8-Bit
QuantLM 830M 6-Bit
QuantLM 830M 4-Bit
QuantLM 830M 3-Bit
TriLM 830M

8.5± 0.2
8.5± 0.2
8.5± 0.2
10.6± 0.2
3.1± 0.1
4.3± 0.2

354.6± 9.6
354.5± 9.6
354.6± 9.6
364.2± 9.8
389.5± 10.9
344.9± 10.0

62.6± 1.2
62.1± 1.2
62.7± 1.2
59.9± 1.2
59.9± 1.2
60.7± 1.2

25.7± 0.3
25.6± 0.3
25.5± 0.3
25.9± 0.3
30.5± 0.4
25.1± 0.3

23.1± 1.5
23.0± 1.5
22.5± 1.5
21.8± 1.4
24.4± 1.5
22.8± 1.5

FloatLM 1.1B
QuantLM 1.1B 8-Bit
QuantLM 1.1B 6-Bit
QuantLM 1.1B 4-Bit
QuantLM 1.1B 3-Bit
TriLM 1.1B
Binary 1.1B

12.9± 0.3
12.7± 0.2
12.4± 0.2
9.3± 0.2
6.8± 0.2
1.9± 0.1
2.2± 0.1

349.2± 9.7
349.5± 9.7
349.7± 9.6
359.1± 10.1
422.4± 11.5
343.4± 9.9
351.6± 9.8

61.2± 1.2
61.1± 1.2
59.9± 1.2
60.9± 1.2
58.7± 1.2
61.4± 1.2
58.3± 1.2

25.4± 0.3
25.4± 0.3
25.5± 0.3
25.4± 0.3
29.9± 0.4
25.8± 0.3
26.4± 0.3

21.4± 1.4
21.7± 1.4
21.9± 1.4
21.3± 1.4
24.2± 1.5
21.5± 1.4
23.2± 1.4

FloatLM 1.5B
QuantLM 1.5B 8-Bit
QuantLM 1.5B 6-Bit
QuantLM 1.5B 4-Bit
QuantLM 1.5B 3-Bit
TriLM 1.5B

12.2± 0.2
12.5± 0.2
11.3± 0.2
9.0± 0.2
4.2± 0.1
5.9± 0.1

351.9± 9.6
352.4± 9.6
350.9± 9.7
357.9± 9.8
400.0± 10.6
348.9± 9.9

61.6± 1.2
61.6± 1.2
61.9± 1.2
60.7± 1.2
60.9± 1.2
59.9± 1.2

26.8± 0.3
26.8± 0.3
27.1± 0.4
25.9± 0.3
26.8± 0.3
25.2± 0.3

21.8± 1.4
21.8± 1.4
21.5± 1.4
20.8± 1.4
20.8± 1.4
21.7± 1.4

FloatLM 2.4B
QuantLM 2.4B 8-Bit
QuantLM 2.4B 6-Bit
QuantLM 2.4B 4-Bit
QuantLM 2.4B 3-Bit
TriLM 2.4B

20.7± 0.3
20.7± 0.3
20.4± 0.3
21.1± 0.3
10.9± 0.2
12.3± 0.1

360.4± 9.4
360.5± 9.4
360.8± 9.5
358.7± 9.6
360.2± 9.5
353.0± 10.0

64.2± 1.2
64.2± 1.2
63.4± 1.2
63.4± 1.2
59.9± 1.2
64.1± 1.2

26.7± 0.3
26.5± 0.3
26.4± 0.3
26.0± 0.3
25.8± 0.3
25.4± 0.3

21.7± 1.4
21.9± 1.4
21.8± 1.4
21.7± 1.4
21.5± 1.4
23.0± 1.5

FloatLM 3.9B
QuantLM 3.9B 8-Bit
QuantLM 3.9B 6-Bit
QuantLM 3.9B 4-Bit
QuantLM 3.9B 3-Bit
TriLM 3.9B

21.5± 0.3
21.7± 0.3
21.0± 0.3
17.9± 0.3
8.2± 0.2
21.3± 0.3

359.2± 9.6
359.8± 9.6
359.5± 9.6
365.5± 9.7
365.9± 9.8
362.4± 9.6

64.7± 1.2
64.6± 1.2
63.9± 1.2
64.8± 1.2
64.3± 1.2
65.4± 1.2

25.4± 0.3
25.4± 0.3
25.4± 0.3
25.3± 0.3
25.5± 0.3
25.9± 0.3

23.6± 1.5
23.6± 1.5
23.5± 1.5
24.2± 1.5
21.9± 1.4
24.1± 1.5

Table 15: Spectra Suite Performance (Part 4): TriviaQA, CrowsPairs, Big Bench BBQ Lite, TruthQA. We
additionally also include Pythia’s performance scores.

44

Published as a conference paper at ICLR 2025

Models
Stem

Humanities

MMLU Accuracy
Social Sciences

Other

Avg.

FloatLM 99M
QuantLM 99M 8-Bit
QuantLM 99M 6-Bit
QuantLM 99M 4-Bit
QuantLM 99M 3-Bit
TriLM 99M
Binary 99M

22.8± 0.7
22.9± 0.7
22.7± 0.7
22.9± 0.7
23.5± 0.8
23.9± 0.8
21.6± 0.7

24.0± 0.6
24.2± 0.6
24.1± 0.6
24.1± 0.6
23.9± 0.6
23.6± 0.6
24.3± 0.6

27.0± 0.8
26.9± 0.8
26.6± 0.8
26.7± 0.8
26.2± 0.8
26.7± 0.8
21.8± 0.7

28.0± 0.8
27.9± 0.8
28.2± 0.8
27.4± 0.8
25.9± 0.8
26.6± 0.8
24.0± 0.7

25.3± 0.4
25.3± 0.4
25.2± 0.4
25.1± 0.4
24.8± 0.4
25.0± 0.4
23.1± 0.3

FloatLM 190M
QuantLM 190M 8-Bit
QuantLM 190M 6-Bit
QuantLM 190M 4-Bit
QuantLM 190M 3-Bit
TriLM 190M

24.0± 0.8
24.1± 0.8
24.1± 0.8
22.9± 0.7
23.9± 0.8
22.5± 0.7

24.4± 0.6
24.5± 0.6
24.5± 0.6
22.9± 0.6
23.2± 0.6
23.8± 0.6

28.8± 0.8
28.9± 0.8
28.3± 0.8
24.5± 0.8
25.4± 0.8
26.7± 0.8

30.1± 0.8
30.0± 0.8
29.8± 0.8
23.4± 0.8
27.5± 0.8
28.4± 0.8

26.5± 0.4
26.6± 0.4
26.4± 0.4
23.4± 0.4
24.8± 0.4
25.2± 0.4

FloatLM 390M
QuantLM 390M 8-Bit
QuantLM 390M 6-Bit
QuantLM 390M 4-Bit
QuantLM 390M 3-Bit
TriLM 390M

25.8± 0.8
25.7± 0.8
26.0± 0.8
25.5± 0.8
24.4± 0.8
24.1± 0.8

25.9± 0.6
25.9± 0.6
25.8± 0.6
25.4± 0.6
25.0± 0.6
24.8± 0.6

30.3± 0.8
30.2± 0.8
30.2± 0.8
30.5± 0.8
29.4± 0.8
28.3± 0.8

32.8± 0.8
32.4± 0.8
32.3± 0.8
31.6± 0.8
29.3± 0.8
29.0± 0.8

28.3± 0.4
28.2± 0.4
28.3± 0.4
27.9± 0.4
26.8± 0.4
26.4± 0.4

FloatLM 560M
QuantLM 560M 8-Bit
QuantLM 560M 6-Bit
QuantLM 560M 4-Bit
QuantLM 560M 3-Bit
TriLM 560M
Binary 560M

24.8± 0.8
24.8± 0.8
24.6± 0.8
24.7± 0.8
24.5± 0.8
25.0± 0.8
21.4± 0.7

26.7± 0.6
26.6± 0.6
26.7± 0.6
25.9± 0.6
24.2± 0.6
25.1± 0.6
24.2± 0.6

30.5± 0.8
30.5± 0.8
30.5± 0.8
29.9± 0.8
28.1± 0.8
29.0± 0.8
21.6± 0.7

32.3± 0.8
32.1± 0.8
31.3± 0.8
31.1± 0.8
28.2± 0.8
30.2± 0.8
23.9± 0.7

28.4± 0.4
28.3± 0.4
28.1± 0.4
27.7± 0.4
26.0± 0.4
27.0± 0.4
22.9± 0.3

FloatLM 830M
QuantLM 830M 8-Bit
QuantLM 830M 6-Bit
QuantLM 830M 4-Bit
QuantLM 830M 3-Bit
TriLM 830M

25.8± 0.8
25.8± 0.8
25.6± 0.8
25.9± 0.8
24.8± 0.8
24.9± 0.8

27.5± 0.6
27.4± 0.6
27.3± 0.6
26.8± 0.6
25.1± 0.6
25.8± 0.6

32.3± 0.8
32.1± 0.8
32.1± 0.8
31.2± 0.8
28.9± 0.8
30.1± 0.8

34.6± 0.8
34.7± 0.8
34.2± 0.8
33.6± 0.8
30.8± 0.8
31.1± 0.8

29.7± 0.4
29.7± 0.4
29.5± 0.4
29.1± 0.4
27.1± 0.4
27.7± 0.4

FloatLM 1.1B
QuantLM 1.1B 8-Bit
QuantLM 1.1B 6-Bit
QuantLM 1.1B 4-Bit
QuantLM 1.1B 3-Bit
TriLM 1.1B
Binary 1.1B

26.4± 0.8
26.2± 0.8
26.0± 0.8
26.0± 0.8
25.9± 0.8
25.2± 0.8
21.0± 0.7

27.6± 0.6
27.4± 0.6
27.5± 0.6
26.6± 0.6
26.1± 0.6
26.1± 0.6
24.2± 0.6

32.5± 0.8
32.5± 0.8
32.7± 0.8
32.4± 0.8
30.0± 0.8
30.6± 0.8
21.7± 0.8

34.8± 0.8
34.9± 0.8
34.9± 0.8
33.8± 0.8
33.0± 0.8
32.2± 0.8
24.4± 0.7

30.0± 0.4
29.9± 0.4
29.9± 0.4
29.3± 0.4
28.4± 0.4
28.3± 0.4
23.0± 0.3

FloatLM 1.5B
QuantLM 1.5B 8-Bit
QuantLM 1.5B 6-Bit
QuantLM 1.5B 4-Bit
QuantLM 1.5B 3-Bit
TriLM 1.5B

26.1± 0.8
26.1± 0.8
26.3± 0.8
26.2± 0.8
25.5± 0.8
25.7± 0.8

28.0± 0.7
28.1± 0.7
28.0± 0.7
28.1± 0.7
26.7± 0.6
27.4± 0.6

33.0± 0.8
32.9± 0.8
33.0± 0.8
32.4± 0.8
31.2± 0.8
31.5± 0.8

35.6± 0.8
35.5± 0.8
35.4± 0.8
34.8± 0.8
33.4± 0.8
34.6± 0.8

30.4± 0.4
30.3± 0.4
30.4± 0.4
30.1± 0.4
28.9± 0.4
29.5± 0.4

FloatLM 2.4B
QuantLM 2.4B 8-Bit
QuantLM 2.4B 6-Bit
QuantLM 2.4B 4-Bit
QuantLM 2.4B 3-Bit
TriLM 2.4B

26.9± 0.8
27.0± 0.8
26.8± 0.8
26.5± 0.8
25.5± 0.8
27.4± 0.8

29.4± 0.7
29.4± 0.7
29.5± 0.7
28.8± 0.7
27.1± 0.6
27.8± 0.6

34.2± 0.8
34.1± 0.8
34.2± 0.8
34.3± 0.8
32.3± 0.8
34.6± 0.9

38.1± 0.9
38.0± 0.9
38.2± 0.9
38.1± 0.9
36.4± 0.9
35.1± 0.8

31.8± 0.4
31.8± 0.4
31.8± 0.4
31.5± 0.4
29.9± 0.4
30.8± 0.4

FloatLM 3.9B
QuantLM 3.9B 8-Bit
QuantLM 3.9B 6-Bit
QuantLM 3.9B 4-Bit
QuantLM 3.9B 3-Bit
TriLM 3.9B

27.7± 0.8
27.6± 0.8
27.3± 0.8
27.1± 0.8
27.3± 0.8
28.3± 0.8

30.6± 0.7
30.7± 0.7
30.3± 0.7
30.3± 0.7
28.4± 0.7
29.5± 0.7

36.9± 0.9
37.0± 0.9
36.9± 0.9
36.3± 0.9
34.3± 0.9
35.4± 0.9

39.8± 0.9
39.7± 0.9
39.3± 0.9
38.8± 0.9
37.2± 0.9
39.6± 0.9

33.3± 0.4
33.4± 0.4
33.1± 0.4
32.8± 0.4
31.4± 0.4
32.8± 0.4

Table 16: Spectra Suite Performance (Part 5): MMLU- STEM, Humanities, Social Sciences, Others.

45

Published as a conference paper at ICLR 2025

I

I LLUSTRATIVE EXAMPLES OF T RI LM 3.9B’ S COMPLETION CAPABILITIES

We showcase instances of outputs produced by TriLM (3.9B) across diverse tasks, highlighting its
proficiency in tasks such as comprehension, prompt completion, and creative composition.
Generated Output on Reading Comprehension by TriLM (3.9B)
Title: The Blitz Background: From the German point of view, March 1941 saw an improvement. The Luftwaffe flew 4,000 sorties that month, including 12 major and three heavy
attacks. The electronic war intensified but the Luftwaffe flew major inland missions only
on moonlit nights. Ports were easier to find and made better targets. To confuse the British,
radio silence was observed until the bombs fell. X- and Y-Gerät beams were placed over false
targets and switched only at the last minute. Rapid frequency changes were introduced for
X-Gerät, whose wider band of frequencies and greater tactical flexibility ensured it remained
effective at a time when British selective jamming was degrading the effectiveness of Y-Gerät.
Q: How many sorties were flown in March 1941?
A: 4,000
Q: When did the Luftwaffe fly inland missions?
A: Only during moonlit nights

Title: Helsinki
Background: Helsinki is the capital and largest city of Finland. It is in the region of Uusimaa,
in southern Finland, on the shore of the Gulf of Finland. Helsinki has a population of , an
urban population of , and a metropolitan population of over 1.4 million, making it the most
populous municipality and urban area in Finland. Helsinki is some north of Tallinn, Estonia,
east of Stockholm, Sweden, and west of Saint Petersburg, Russia. Helsinki has close historical
connections with these three cities. The Helsinki metropolitan area includes the urban core
of Helsinki, Espoo, Vantaa, Kauniainen, and surrounding commuter towns. It is the world’s
northernmost metro area of over one million people, and the city is the northernmost capital
of an EU member state. The Helsinki metropolitan area is the third largest metropolitan area
in the Nordic countries after Stockholm and Copenhagen, and the City of Helsinki is the third
largest after Stockholm and Oslo. Helsinki is Finland’s major political, educational, financial,
cultural, and research center as well as one of northern Europe’s major cities. Approximately
75% of foreign companies that operate in Finland have settled in the Helsinki region. The
nearby municipality of Vantaa is the location of Helsinki Airport, with frequent service to
various destinations in Europe and Asia.
Q: What is the most populous municipality in Finland?
A: Helsinki
Q: How many people live there?
A: 1.4 million in the metropolitan area
Q: What percent of the foreign companies that operate in Finland are in Helsinki?
A: 75%
Q: What towns are a part of the metropolitan area?
A: Espoo, Vantaa, Kauniainen, and surrounding commuter towns

46

Published as a conference paper at ICLR 2025

Auto-complete on a creative writing task by TriLM (3.9B)
Essay Writing
In the year 2150, humanity had established colonies on Mars. Captain Ramirez was on a
routine mission to explore an uncharted region of the planet when he and his crew were
attacked by Martian natives who wanted them dead for their technology. The captain’s ship
crashed into the surface of Mars where it exploded in flames.
The survivors managed to escape from the wreckage but they soon found themselves stranded
with no way out or back home. They would have to survive alone until rescue came. But
what if there is nothing waiting for them? What if they are trapped forever?
Poem Writing
In a garden where the roses bloom,
Underneath the silver moon,
A gentle breeze begins to sway,
And whispers secrets of the day.
The stars above start to appear,
While shadows dance and disappear,
The night unfolds in its own time.
The sun rises over the horizon,
As it does every morning,
But this is no ordinary dawn.
It’s a new beginning for all who are here today.
For those who have come before us,
And those yet to be born.
We celebrate life with music and laughter,
With friends old and new.
This is our moment to shine!

Auto-complete on various prompts by TriLM (3.9B)
Making a cake: Several cake pops are shown on a display. A woman and girl are shown
making the cake pops in a kitchen. They use a mixer to mix ingredients, then knead dough by
hand. The women roll out the dough with a rolling pin, cut it into shapes using cookie cutters,
bake them, and decorate them with frosting or sprinkles.

The energy given up by electrons as they move through the electron transport chain is used
to produce ATP. In this process, oxygen and water are produced in a reaction called cellular
respiration.

When talking about sensitive topics, it is crucial to be aware of the fact that there are many
different types of people. Some will react negatively and others positively. It’s important not
to take offense when someone says something you don’t like.
If someone disagrees with you, it is best to ignore them. The most important thing in life is
not what we have but who we are and how we treat others.

47

Published as a conference paper at ICLR 2025

J

B ROADER I MPACT

Interpretability Beyond Neuron Level: While several efforts have been made to understand how
language models work and the means to steer them without training, these methods have mostly
focussed on intervening at the neuron level. TriLMs open a new degree of interpretability - at the
connection level. Here, the connections between any two neurons in a layer are in one of the three
states - 0 (no connection), -1 (negative connection) and +1 (positive connection), each with equal
strength. This is in sharp contrast to FloatLMs, where these connections can be of varying strengths,
making it harder to study interpretability beyond the neuron level. By releasing the checkpoints
across our training runs, we facilitate research along these directions.
Environmental Benefits and Resource Efficiency: The open release of our models mitigates
future emissions by allowing others to bypass the need for pretraining models from scratch. Moreover,
TriLMs need much fewer resources during deployment and can perform the autoregressive generation
at a faster pace - making them critical to scenarios demanding strict latency. Additionally, TriLMs
represent a substantial advancement in enhancing performance on resource-constrained edge devices,
including smartphones, laptops, and automobiles.
Impact on Specialised Hardware: While TriLMs offer significant memory reduction and latency
improvements on General Purpose GPUs like H100 and RTX4090, certain specialized hardware
benefits more from ternary modeling. Hardware (like Cerabras3 ) that supports high byte-to-flop ratio
computations, can leverage the sparsity stemming from ternarization for speedup in both training as
well as inference. On the other hand, hardware with limited Memory/SRAM (like Groq4 ), benefits
from the reduction in the number of chips needed to deploy an LLM.
Reduced Training Costs: The Chinchilla scaling laws established that for training compute
optimality, it may be recommended to train larger LLMs for fewer tokens than smaller LLMs for
more tokens to achieve the desired model performance. However, memory requirements and latency
associated with deployment of larger models, have motivated costlier training runs that go far beyond
Chinchilla optimality. For example, a LLaMa 3 model with only 8B parameters was trained for 15T
tokens. Since TriLM and ternary models, in general, can reduce the memory requirements and latency,
this can motivate a shift inparameter-token tradeoff for efficient training runs towards Chinchilla’s
compute-optimal regime.
Advancing Research through Open Access: The open suite of TriLM, FloatLM, and QuantLM
families aims to empower researchers to explore the nuanced impacts of precision levels on model
performance and efficiency, thereby catalyzing ongoing advancements in the development and
deployment of language models, as well as enhancing their interpretability and safety Li (2024). By
providing a range of publicly accessible models trained on openly available data, the suite offers
unprecedented transparency in the training process. Intermediate checkpoints are available for all
models, accompanied by detailed documentation of training procedures and hyperparameters.

3
4

https://www.cerebras.net/product-chip/
https://groq.com/

48

arXiv:2406.07177v1 [cs.LG] 11 Jun 2024

TernaryLLM: Ternarized Large Language Model

Tianqi Chen1,2 , Zhe Li3 , Weixiang Xu1 , Zeyu Zhu1 ,
Dong Li3 , Lu Tian3 , Emad Barsoum3 ,
Peisong Wang1,2,4 , Jian Cheng∗1,2,4,5
1
Institute of Automation, Chinese Academy of Sciences
2
School of Artificial Intelligence, University of Chinese Academy of Sciences
3
Advanced Micro Devices, Inc., Beijing, China
4
AIRIA 5 Maicro.ai
{chentianqi2023,xuweixiang2018,zhuzeyu2021}@ia.ac.cn,
{Z.Li,d.li,lu.tian,Emad.Barsoum}@amd.com,
{peisong.wang,jcheng}@nlpr.ia.ac.cn

Abstract
Large language models (LLMs) have achieved remarkable performance on Natural
Language Processing (NLP) tasks, but they are hindered by high computational
costs and memory requirements. Ternarization, an extreme form of quantization, offers a solution by reducing memory usage and enabling energy-efficient
floating-point additions. However, applying ternarization to LLMs faces challenges
stemming from outliers in both weights and activations. In this work, observing
asymmetric outliers and non-zero means in weights, we introduce Dual Learnable
Ternarization (DLT), which enables both scales and shifts to be learnable. We
also propose Outlier-Friendly Feature Knowledge Distillation (OFF) to recover
the information lost in extremely low-bit quantization. The proposed OFF can
incorporate semantic information and is insensitive to outliers. At the core of
OFF is maximizing the mutual information between features in ternarized and
floating-point models using cosine similarity. Extensive experiments demonstrate
that our TernaryLLM surpasses previous low-bit quantization methods on the
standard text generation and zero-shot benchmarks for different LLM families.
Specifically, for one of the most powerful open-source models, LLaMA-3, our
approach (W1.58A16) outperforms the previous state-of-the-art method (W2A16)
by 5.8 in terms of perplexity on C4 and by 8.2% in terms of average accuracy on
zero-shot tasks.

1

Introduction

Large language models (LLMs) [1, 2] have demonstrated impressive performance across various
language tasks. Although LLMs’ representative ability improves as the parameters scale exponentially,
the enormous parameters pose significant challenges on memory footprint and low latency inference
[3, 4]. Therefore, resolving the above problems for the practical deployment of LLMs is an emergency.
As a compression method without modifying the model architecture, network quantization has shown
promising effectiveness in reducing both memory requirements and inference latency. In the context
of LLMs, quantization can be categorized into weight-only and weight-activation quantization. While
weight-activation quantization can leverage faster integer computations instead of floating-point
computations, prior studies have identified significant outliers in activations, posing challenges for
successfully quantizing activations to lower bit precision (e.g., 4 bits). Consequently, weight-only
quantization becomes a better trade-off between efficiency and accuracy, as the main bottleneck of
deploying LLMs is memory bandwidth, which usually preserves more accuracy. Most recent works
* Corresponding author.

have focused on weight-only quantization, successfully quantizing weights to 4 and 3 bits (even 2
bits) [5, 6]. However, weight-only quantization has to dequantize the low-bit weights to floating-point
in real-time before performing multiplication with floating-point activation.
Fortunately, by replacing floating-point multiplications with energy-saving floating-point additions,
ternarization can solve the above problems. However, existing ternarized works are dedicated to
convolutional neural networks and smaller encoder-only transformers like BERT, which can not be
directly applied to LLMs due to the following challenges: Firstly, we observe asymmetric outliers and
non-zero means in weights, indicating that previous symmetric ternarization methods are suboptimal.
Secondly, extreme low-bit quantization leads to severe information loss in pretrained LLMs, including
a narrowed feature representation range, loss of prominence in dominant channels, and disruption
of the semantic clustering of related words. When trying to recover the lost information from
the floating-point model, it is difficult to force the ternarized model to emulate the exact feature
representation of the floating-point teacher due to the former’s limited expressive capacity.
Based on the above discoveries, we propose two simple but effective methods: Dual Learnable
Ternarization (DLT) and Outlier-Friendly Feature Knowledge Distillation (OFF). DLT is a custom
ternary quantizer for weights with weird distribution in LLMs, enabling both scale and shift learnability. To recover semantic information from the original models, we introduce Outlier-Friendly
Feature Knowledge Distillation (OFF). OFF aims to maximize the mutual information between the
floating-point and quantized models while leveraging the insensitivity of cosine similarity to outliers,
thereby diminishing training instability. TernaryLLM surpasses both previous post-training and
quantization-aware methods on standard NLP benchmarks, including text generation and zero-shot
tasks, using models from the OPT and LLaMA families. Specifically, for one of the most powerful
open-source models, LLaMA-3, our approach (W1.58A16) outperforms the previous quantizationaware training method (W2A16) by 5.8 in terms of average perplexity and by 8.2 in terms of average
accuracy on zero-shot tasks.
Our contributions can be summarized as follows:
• We observe in group-wise quantization, weights in the same group are asymmetric distributed.
This phenomenon motivates us to propose Dual Learnable Ternarization (DLT) which
enables learnable scales and shifts.
• To recover semantic information from the original models, we introduce Outlier-Friendly
Feature Knowledge Distillation (OFF), which utilizes the insensitivity of cosine similarity
to outliers, helping to prevent training instability.
• We conducted experiments on text generation and zero-shot tasks using models from the
OPT and LLaMA families. Our method outperforms both previous post-training and
quantization-aware methods, even with fewer bits and a larger group size.

2

Related Work

2.1

LLM Quantization

Quantization has found extensive application in accelerating models during inference [7, 8, 9]. In
the current era of burgeoning LLMs development, quantization has become widely employed for
LLMs as well [10, 4, 3, 11, 12]. Based on whether activations are quantized, it can be classified into
weight-only quantization and weight-activation quantization.
Weight-Activation Quantization. Weight-activation quantization quantizes both floating-point
weights and activations into low-bit integers. Much research has focused on the extremely large
outliers in activations and designed approximate methods to alleviate this problem [4, 10, 13]. For
instance, SmoothQuant [4] migrates the distribution imbalance from activations to weights and
enables 8-bit weight, 8-bit activation (W8A8) quantization for LLMs. However, it is still challenging
to quantize both weights and activations into low-bit, e.g., W4A4.
Weight-Only Quantization. Weight-only quantization only quantizes weights into low-bit while
leaving activations floating-point. In the context of LLMs, the primary memory consumption results
from model weights [5, 11]. Weight-only quantization gains significant speedup and enables inference
on consumer-level GPUs. However, in weight-only quantization, there is a need to dequantize the
quantized weights to floating-point in real-time before computing with floating-point activation.
2

channel index

x.abs().min()
feature map ranges

channel index

(a)

(b)

the
have
has

token index

channel index

channel index

of

answer fruit
label introduction
section

channel index

x.abs().min()

number of elements
number of elements

feature map ranges

large
global first

first
first
answer
first

of

the
global
large

have
introduction
section
label

has

token index

(c)

(d)

Figure 1: An example of the features in the 23rd decoder layer to illustrate the problems incurred by
extreme low-bit quantization. The first and second lines correspond to the float-point and quantized
models, respectively. Extreme low-bit quantization leads to severe information loss in pretrained
LLMs, including a narrowed feature representation range (Figure 1 (a)), loss of prominence in
dominant channels (Figure 1 (b)), and disruption of the semantic clustering of related words (Figure 1
(c) and (d)).

Therefore, while weight-only quantization primarily benefits from reduced memory access, it suffers
from slower computation processes. Fortunately, this problem can be naturally solved by pushing the
quantization bit to ternary or binary, providing advantages of both reduced memory consumption and
energy-saving floating-point additions [14]. Previous work PB-LLM [15] only succeeds in partially
quantizing weights to 1-bits and leaving salient weights at 8-bits. To distinguish between different
data types, it incurs non-negligible overheads. In this paper, we aim to realize fully ternarized LLMs,
relying on custom ternary quantization and Knowledge Distillation.
2.2

Knowledge Distillation

Knowledge distillation (KD) was initially proposed in [16] to transfer knowledge from the logits of
teacher models to student models. Later, feature distillation has been proposed to leverage information
from hidden layers [17] instead of the output layer. In model quantization, particularly in low-bit
settings, KD has been widely used to improve performance and narrow the performance gap between
floating-point models and quantized models.
However, directly applying previous knowledge distillation methods in LLMs faces new challenges.
The presence of outliers in features makes the previous KD method based on Mean Squared Error
ineffective. It is important to recognize the crucial role of outliers in knowledge distillation, highlighting the necessity of fully utilizing them for optimal solutions while also avoiding their negative
impact on training stability.

3

Background

Notification. Transformers, including LLMs, are composed of a sequence of encoder or decoder
layers. The notation L is used to represent the layer number. For the l-th decoder (or encoder) layer,
we denote the input as Hl and the output as Hl+1 .
A linear layer in Transformer is defined as Y = W · X, where W ∈ RCo ×Ci and X ∈ RCi ×T . Here,
Co and Ci denote the output channel and input channel, respectively, and T represents the sequence
length. To simplify, the number of elements in W is denoted as N = Co × Ci .
3

Weight Ternarization. Ternarization converts floating-point weights in a model into three values. To
project the i-th element of W , denoted as Wi , to Ti ∈ {−1, 0, 1}, a parameter threshold ∆ is used:

if Wi < −∆
−1,
Ti = 0,
(1)
if |Wi | ≤ ∆

+1,
if Wi > ∆
To enhance performance, TWN [18] introduces a scaling factor α to estimate the magnitude of the
original weights:
N
X
(2)
min
||Wi − α · Ti ||2
α

i

The exact solution for ∆ and α is time-consuming. As an alternative method, they approximate ∆ as:
PN
0.7 · i |Wi |
(3)
∆=
N
After determining W t , the optimal scale factor α, which minimizes (2), can be obtained as follows:
PN
i Ti · Wi
(4)
α∗ = P
N
i |Ti |

4

Challenges of Ternarizing LLMs

weight range

numbers of elements

In this section, we conduct in-depth
analyses of the challenges encountered in implementing ternarized
LLMs. Firstly, we have observed
that the previous weight ternarization method is inadequate for handling asymmetric outliers and nonweight range
zero mean distributions. Secondly, exgroup index
weight range
tremely low-bit quantization results in
(a)
(b)
substantial information loss, necessitating feature knowledge distillation.
Based on preliminary experiments, we Figure 2: The weights in certain groups display noticeable
have found it difficult to directly align asymmetric outliers and a non-zero mean distribution.
features between quantized and original models due to their different expressive capacities.
Challenge 1. For group-wise quantization, weights in certain groups display noticeable asymmetric distribution with non-zero mean. For transformers, especially LLMs, Outlier Surpression+
[13] has identified asymmetric behavior among channels in features. This paper finds a similar
phenomenon in weights. We illustrate this observation with the query weights in the OPT model.
In Figure 2(a), weights in some groups exhibit a negative mean but significantly positive outliers,
while the others show the opposite behavior. Previous methods, such as TWN, lead to a suboptimal
trade-off between clamping error and round error on both sides: the scale factor in Equation (4) may
be too large for negative values but too small for positive ones. Moreover, in Figure 2(b), due to
this asymmetry, the mean of values located in intervals [−∆, ∆] is negative, which leads to those
methods to quantize these values to zero being suboptimal.
Challenge 2. Extreme low-bit quantization leads to severe loss of information in pretrained
LLMs. The distribution depicted in Figure 1 highlights the challenges encountered in ternary
quantization. Figure 1 (a) illustrates that the feature representation range is considerably narrowed
after ternarization, indicating a constrained expressive power of the quantized model. Channels that
were originally dominant, meaning those with larger magnitudes, become overwhelmed by other
channels and are no longer prominent, as shown in Figure 1 (b). Furthermore, in Figure 1 (c) and (d),
we observe that after pretraining on large datasets, LLMs tend to cluster semantically related words
tightly (for example, the words "has" and "have") [19]. However, ternarization destroys this semantic
4

Label Loss

Loss

Loss

Feature KD Loss

channel index

Step

Step

(a)

(b)

Features of (FP) Teacher Model: HlT
0.023

-1.58

-0.464

2.843

-0.226

2240

-1.375

5.468

-0.021

-1.19

0.478

-0.227

-0.182

0.157

-0.092

23.25

-0.714

-0.566

-0.002

-0.28

Features of (Ternary) Student Model: HlS

(c)

Figure 3: Feature knowledge distillation results for LLaMA-1-7B. Cosine similarity is less sensitive
to outliers in features compared to MSE. (a) Ground truth loss of the training. (b) Feature knowledge
distillation loss of the training. (c) The reasons for severe oscillations in MSE distillation.
structure, causing different words to be distributed in an out-of-order manner. Therefore, directly
employing quantization-aware training on LLMs wastes the pretrained information and may lead to a
different convergence point, risking overfitting.
Challenge 3. It is difficult to force the ternarized model to emulate the exact feature representation of the floating-point due to the former’s limited expressive capacity. Focused on
Challenge 2, we propose the utilization of feature knowledge distillation (Feature KD). Feature KD
can introduce more supervised signals from the pretrained model to realign the ternarized model
with the floating-point model. However, as mentioned in Figure 1, the values of some channels are
significantly larger than others. If they are not correctly balanced, the small gradients produced by
the less-activated channels can be overwhelmed by the large gradients from the dominant ones. In
Figure 3, we observe that the previously popular distillation metric, mean square error (MSE), suffers
from severe oscillations. This phenomenon arises due to the inherent heterogeneity between the
floating-point and ternarized models’ features. Unlike the real-numbered weights of the floating-point
model, the ternarized model’s weights are constrained to a discrete set of three values. Consequently,
the latter fails to replicate the exact feature representation achieved by the former.

5

Method

In Section 4, we explore the difficulties in ternarizing LLMs. In this section, based on the above
findings, we propose two simple but effective methods to boost performance.
5.1

Dual Learnable Ternarization

In Section 4, we observed that the weights exhibit significant asymmetric outliers and a non-zero
mean distribution. Focusing on this phenomenon, we propose Dual Learnable Ternarization (DLT),
which not only enables learnable quantization scales but also shifts.
Specifically, we first map float weights Wi into ternarized values Ti using threshold ∆ as the same as
TWN:

if Wi < −∆
−1,
Ti = 0,
(5)
if |Wi | ≤ ∆

+1,
if Wi > ∆
Instead of using the mean of weights as α in equation 4, we set α as a learnable parameter that can be
updated during training. To further adapt to the asymmetric distribution, we introduce a learnable
shift parameter γ:
Di ≈ α · Ti + γ
(6)
The gradients of parameters of α and γ can been computed as follows:
X ∂L
∂L
=
∂α
∂Di
i:|Wi |<∆

5

(7)

∂L X ∂L
=
∂γ
∂Di
i

(8)

By utilizing the Straight-through estimator (STE) [20], we can approximate the gradients to float
weight Wi :

∂L
α · ∂D
,
if Wi > ∆

i
∂L
∂L
if |Wi | ≤ ∆
(9)
= 1 · ∂Di ,

∂Wi
−α · ∂L ,
if Wi > ∆
∂Di
Efficiency Analysis. By employing DLT, we can replace original floating-point multiplications with
just two additions.
X
X
X
y=
Di · xi = α ·
(Ti · xi ) + γ ·
xi
(10)
i

i

i

Because the second summation is independent of weights, the total number of additions in our method
is O(LCo Ci + LCi ), and the total number of multiplications is O(2G), where G is the total number
of groups.
5.2

Outlier-Friendly Feature Knowledge Distillation

Knowledge distillation, as demonstrated by Hinton [16], has proven to be effective in compressing
CNNs and transformer models, particularly in scenarios with extremely low bit precision. In
Section 4, we identify the necessity of recovering semantic information in features of ternarized
models. Here, from the perspective of mutual information, we propose Theorem 1, which explains
how to maximize the mutual information between features in ternarized and floating-point models
using cosine similarity. The proof process can be found in the appendix.
Theorem 1. Assume x ∈ RCi ∼ N (0, σx2 ), W = (w1T , w2T , . . . , wCo )T and y = RMSNorm(W x).
Let Wq denotes the ternarization of W and yq = RMSNorm(Wq x). The objective to maximize the
mutual information between y and yq I(y, yq ) can been achieved by Ep(x) cos(Wq x, W x) = 1.
Utilizing cosine similarity to maximize the mutual information between floating-point model and
quantized model, we introduce a more suitable feature KD method termed Outlier-Friendly Feature
KD (OFF) for LLMs. Specifically, we compute the cosine similarity between each token of teachers
and students individually, then aggregate the total T tokens to compute the feature KD loss for the
current layer. Subsequently, we aggregate the first L′ layers to compute the total feature KD loss.
Cosine Similarity(H T each ,H Stu ) =

T
T
X
hStu
· hTi each
i
T
each
∥hi
∥ · ∥hStu
∥
i
i

(11)

′

Lf eat =

L
X

Cosine Similarity(HlT each ,HlStu )

(12)

l

The advantage of using cosine similarity as the distance metric is two folds: (a) By maximizing cosine
similarity, the quantized model restores the semantic information of the original model. This ensures
the quantized model captures the essential features learned by the floating-point model, leading to
better generalization performance on unseen data. (b) Cosine similarity is scale-invariant, meaning it
is not affected by the magnitude of the vectors but only by their direction. This property guarantees
the distillation process’s robustness, even in the presence of numerous outliers in the floating-point
model.
Logits Knowledge Distillation. Besides the feature KD, we also distill knowledge in the last layer
by minimizing the soft cross-entropy (SCE) between quantized student logits Z Stu and teacher logits
Z T each , i.e.,
(13)
Llogits = SCE(Z Stu , Z T each )
Objective Function. The overall objective function in the training process of TernaryLLM is as
follows:
Ltotal = Llabel + ϵ · Llogits + δ · Lf eat
(14)
6

Method

PPL↓

#W #G

WikiText2

Zero-Shot↑

C4

PTB PIQA ARC-e ARC-c HellaSwag Wino Avg.

LLaMA-3 16

-

6.1

9.2

10.6

79.9

80.1

50.4

60.2

72.8 68.6

RTN

128
128
-

1.9E3
2.7E6
2.1E2
5.7E4
8.2E5
85.1

2.5E4 1.8E4
7.4E6 3.1E6
4.1E4 9.1E2
1.0E5 2.7E5
8.1E5 9.0E5
1.3E2 1.8E2

53.1
53.1
53.9
52.8
55.2
52.9

24.8
24.7
28.8
25.0
25.2
29.0

22.1
21.9
19.9
20.5
21.3
21.3

26.9
25.6
27.7
26.6
25.4
29.2

53.1
51.1
50.5
49.6
50.4
51.7

36.0
35.3
36.2
34.9
35.5
36.8

2
128
2
128
1.7 128
1.58 -

13.6
24.7
41.8
11.2

19.2 23.8
79.2 65.6
2.6E2 1.2E2
13.4 16.3

68.9
57.0
52.5
73.7

59.1
37.8
31.7
61.2

28.2
17.2
17.5
36.4

42.1
29.8
27.7
63.9

60.4
52.5
50.4
65.0

51.8
38.8
36.0
60.0

GPTQ
AWQ
QuIP
DB-LLM
PB-LLM
Our

2
2
2
2
2
2

Table 1: Evaluation results of weight-only quantization on the LLaMA-3-8B model. #W indicates
weight bits, #G indicates group size, and “-” denotes per-channel quantization.
Method
FP

OPT-125M

#W #G
16

OPT-1.3B

OPT-2.7B

OPT-6.7B

WikiText2

C4

WikiText2

C4

WikiText2

C4

WikiText2

C4

27.65

24.60

14.63

14.72

12.47

13.16

10.86

11.74

7.0e3
7.0e3
204.40
597.66
124.18
251.84
75.43
5.18e4
39.92

3.9e3
5.0e3
133.51
597.66
90.19
168.35
80.10
4.39e4
32.57

1.0e4
1.0e4
49.58
115.16
29.78
47.97
23.95
48.22
18.51

7.3e3
7.7e3
31.31
60.88
27.34
38.38
27.33
68.10
18.01

19.3e4
19.3e4
29.37
61.59
20.64
28.50
18.13
31.04
17.98

1.2e5
3.8e4
23.23
33.83
20.01
26.41
21.11
43.47
17.49

7.6e3
7.6e3
16.81
20.18
14.63
16.20
14.43
22.77
13.81

6.3e3
5.2e3
16.24
18.55
15.20
16.48
16.67
35.19
14.51

-

RTN

2
64
2
64
GPTQ
2
64
2
128
AWQ
2
64
2
128
OmniQuant 2
128
2
Our
1.58 -

Table 2: C4 and WikiText2 perplexity ↓ of different methods in OPT models. #W indicates weight
bits, #G indicates group size, and “-” denotes per-channel quantization.

Here, ϵ and δ represent the loss balancing scales, which can be found in the training details section.
Additionally, Llabel = SCE(Z Stu , Z label ) denotes the cross-entropy between Z Stu and ground
truth Z label .

6

Experiments

In this section, we evaluate our methods on both language generation and zero-shot zero-shot tasks
with OPT [2] models and LLaMA [1] family models.
6.1

Experiment Setup

Dataset. Following the previous work [15] we use RedPajama [21] as the training dataset. RedPajama
is an open-source reproduction of the pre-training data for LLaMA[1]. This mainly consists of web
text (Common Crawl and C4 [22]) and high-quality sources such as arXiv and Stack Exchange.
Training Details. We utilize a full-precision model to initialize ternarized models. We use the
AdamW optimizer with zero weight decay to optimize the learnable parameters. The batch size is 16.
We use cosine learning rate decay, and the total number of iterations is 10,000 steps. More training
details can be found in the Appendix.
Evaluation Tasks. We evaluate our methods on both language generation and zero-shot tasks. We
report the perplexity on WikiText2 [23], PTB [24] and C4 [22]. For zero-shot tasks, we provide
7

Method

PPL↓

#W #G

Zero-Shot↑

WikiText2

C4

Avg. PIQA ARC-e ARC-c HellaSwag Wino Avg.

LLaMA-2 16

-

5.47

6.97

6.22 76.99

53.58

40.53

72.96

67.25 62.26

GPTQ
2
AWQ
2
OmniQuant 2

64
64
64

8.97
2.06e5
9.64

13.25 11.11 68.39
1.54e5 1.8e5 50.00
12.73 11.19 68.72

42.13
26.52
39.77

31.91
26.79
30.89

54.64
26.14
53.44

58.64 51.14
49.64 35.82
56.12 49.79

2
64
2
64
1.58 1.58 64

20.37
7.23
7.46
7.7

44.88 32.63 55.22
9.62 8.43 73.18
9.16 8.31 72.47
9.45 8.57 72.68

29.88
45.20
46.46
48.06

22.01
33.53
33.44
34.89

30.49
61.98
63.84
63.94

50.36 37.59
61.72 55.12
60.93 55.42
61.72 56.25

PB-LLM
DB-LLM
Our

LLaMA-1 16

-

5.68

7.08

6.38 77.37

52.53

41.38

72.99

66.85 62.22

GPTQ
2
AWQ
2
OmniQuant 2

64
64
64

22.10
2.5e5
8.91

17.71 19.91 59.36
2.8e5 5.3e5 50.05
11.79 10.4 68.66

32.11
25.76
44.49

25.09
29.44
29.69

35.14
25.93
54.32

49.01 40.14
49.96 36.23
55.56 50.54

2
64
2
64
1.58 1.58 64

20.61
7.59
7.82
7.48

47.09 33.85 55.39
9.74 8.67 72.14
9.52 8.67 72.74
9.38 8.58 73.06

34.22
44.70
46.89
45.49

24.23
33.62
34.98
35.15

31.99
60.71
62.40
63.78

52.88 39.74
61.01 54.44
59.35 55.27
62.58 56.01

PB-LLM
DB-LLM
Our

Table 3: Evaluation results of weight-only quantization on the LLaMA-1-7B and LLaMA-2-7B
model. #W indicates weight bits, #G indicates group size, and “-” denotes per-channel quantization.

accuracy on datasets including PIQA [25], ARC [26], BoolQ [27], HellaSwag [28] and Winogrande
[29].

6.2

Results on Language Generation

Experiments were conducted on OPT models [2] ranging from 125M to 6.7B, as well as on 7B
versions of the LLaMA-1, LLaMA-2, and LLaMA-3 models [1]. In this comparison, we evaluate our
method against previous weight-only techniques, including post-training quantization methods such
as OmniQuant [5], AWQ [3], and GPTQ [11], as well as quantization-aware training methods such
as PB-LLM [15] and DB-LLM [30]. PB-LLM retains significant weights in higher bits, whereas
DB-LLM employs two binary matrices to represent the weights. The average bit-width for both
methods is 2 bits. The perplexity results for LLaMA family models are presented in Table 1 and
Table 3. Notably, even with an average bit width of only 1.58 , our methods surpass the previous 2-bit
quantization-aware methods in average perplexity, for example, 5.2 for LLaMA-3. The perplexity
results for OPT models on the C4 [22] and WikiText2 [23] datasets are presented in Table 2. Even with
per-channel quantization, our approach outperforms previous group-wise weight-only quantization
methods. For example, for OPT-125M, our per-channel ternary method maintains an average PPL of
39.92, while the 2-bit OmniQuant achieves only 75.53 with a group size of 128.

6.3

Results on Zero-Shot Tasks

In this section, we assess the performance of ternarized models on zero-shot tasks and present the
results in Table 1 and Table 3. Previous work [31] indicates that LLaMA-3 experiences significant
degradation at ultra-low bit-widths, highlighting the substantial performance gap that needs to be
addressed by the quantization research community. For LLaMA-3-7B, our approach (W1.58A16)
outperforms the previous quantization-aware training method DB-LLM (W2A16) by 8.2% in accuracy,
improving the average accuracy from 51.8% to 60.0%. Our methods also surpass previous best results
in LLaMA-1 and LLaMA-2 by 1.56% and 1.13%, respectively, demonstrating superior preservation
of generation capability in LLMs.
8

Perplexity

Label Loss

Table 5: Comparison of different knowledge distillation techniques on the LLaMA-1-7B model. OFF
and logits KD, either separately or combined, can
improve performance.
OmniQuant

Figure 4: Training loss and validation perplexity curves. The experiments are conducted
on OPT-125M with a group size of 128. Our
method surpasses OmniQuant with only 500
steps.

6.4

Method
W/O KD
Logits
MSE
MSE + Clamp
MSE + Skip
OFF

WikiText2
9.98
9.84
10.84
9.48
9.72
9.33

C4
11.56
11.41
12.12
11.14
11.39
10.99

Logits+OFF

9.21

10.78

Ablations

In this section, we present some ablation studies to demonstrate the efficacy of our methods. For this
segment, we limit the training to only 2,000 iterations.
Dual Learnable Ternarization. We conducted experiments to investigate the effects of our DLT
method. As shown in Table 4, the DLT method achieves a 1.49 PPL improvement on the OPT-1.3B
model and a 0.89 PPL improvement on the LLaMA-1-7B model. DLT enables α and γ to learn
values better suited to LLM weights, enhancing the model’s expressive capacity at extremely low-bit
scenarios.
LLaMA-7B PPL
OPT-1.3B
LLaMA-7B

FP
14.63
5.68

TWN
22.32
10.10

DLT
20.83
9.21

Table 4: Comparison of various ternarization methods on OPT-1.3B and LLaMA-7B model.
Outlier-Friendly Feature KD. We conducted experiments to evaluate various feature knowledge
distillation methods and their combinations. Consistent with our analysis in Section 4, mean square
error (MSE) methods often suffer from training instability. We also explored other improved methods
based on MSE, such as clamping outliers or disregarding abnormal loss. However, these methods
only partially address the issue and involve significant hyperparameter tuning. As shown in Table 5,
Outlier-friendly Feature KD improves performance by 0.65 PPL and 0.57 PPL on Wikitext2 and C4,
respectively. Additionally, combining it with logits, KD further enhances performance by 0.77 PPL.
Training Steps. We conducted experiments on OPT-125M with a group size of 128 to observe
the validation perplexity and training loss over steps. Our method demonstrates fast convergence,
recovering performance in a few steps, and surpasses the previous post-training quantization method
in just 500 steps.

7

Conclusion

In this paper, we introduce TernaryLLM, tailored for precise ternarized Large Language Models. To
tackle the decline in accuracy, we propose Dual Learnable Ternarization, which integrates learnable
scales and shifts to adapt to the asymmetric weight distribution in group-wise quantization. Additionally, we present Outlier-Friendly Feature Knowledge Distillation (OFF), designed to maximize the
mutual information between floating-point and quantized models. This approach also takes advantage
of the insensitivity of cosine similarity to outliers, thereby mitigating training instability. TernaryLLM
not only enhances the compression ratio of parameters but also enables LLM inference with floating9

point additions instead of multiplications. Extensive experiments demonstrate that TernaryLLM
outperforms previous extreme low-bit quantization methods on established NLP benchmarks.

10

References
[1] Hugo Touvron, Thibaut Lavril, Gautier Izacard, Xavier Martinet, Marie-Anne Lachaux, Timothée Lacroix, Baptiste Rozière, Naman Goyal, Eric Hambro, Faisal Azhar, Aurélien Rodriguez,
Armand Joulin, Edouard Grave, and Guillaume Lample. Llama: Open and efficient foundation
language models. CoRR, abs/2302.13971, 2023.
[2] Susan Zhang, Stephen Roller, Naman Goyal, Mikel Artetxe, Moya Chen, Shuohui Chen,
Christopher Dewan, Mona T. Diab, Xian Li, Xi Victoria Lin, Todor Mihaylov, Myle Ott, Sam
Shleifer, Kurt Shuster, Daniel Simig, Punit Singh Koura, Anjali Sridhar, Tianlu Wang, and Luke
Zettlemoyer. OPT: open pre-trained transformer language models. CoRR, abs/2205.01068,
2022.
[3] Ji Lin, Jiaming Tang, Haotian Tang, Shang Yang, Xingyu Dang, and Song Han. AWQ: activationaware weight quantization for LLM compression and acceleration. CoRR, abs/2306.00978,
2023.
[4] Guangxuan Xiao, Ji Lin, Mickaël Seznec, Hao Wu, Julien Demouth, and Song Han.
Smoothquant: Accurate and efficient post-training quantization for large language models.
In Andreas Krause, Emma Brunskill, Kyunghyun Cho, Barbara Engelhardt, Sivan Sabato, and
Jonathan Scarlett, editors, International Conference on Machine Learning, ICML 2023, 23-29
July 2023, Honolulu, Hawaii, USA, volume 202 of Proceedings of Machine Learning Research,
pages 38087–38099. PMLR, 2023.
[5] Wenqi Shao, Mengzhao Chen, Zhaoyang Zhang, Peng Xu, Lirui Zhao, Zhiqian Li, Kaipeng
Zhang, Peng Gao, Yu Qiao, and Ping Luo. Omniquant: Omnidirectionally calibrated quantization for large language models. CoRR, abs/2308.13137, 2023.
[6] Jerry Chee, Yaohui Cai, Volodymyr Kuleshov, and Christopher De Sa. Quip: 2-bit quantization
of large language models with guarantees. CoRR, abs/2307.13304, 2023.
[7] Benoit Jacob, Skirmantas Kligys, Bo Chen, Menglong Zhu, Matthew Tang, Andrew G. Howard,
Hartwig Adam, and Dmitry Kalenichenko. Quantization and training of neural networks for
efficient integer-arithmetic-only inference. In 2018 IEEE Conference on Computer Vision and
Pattern Recognition, CVPR 2018, Salt Lake City, UT, USA, June 18-22, 2018, pages 2704–2713.
Computer Vision Foundation / IEEE Computer Society, 2018.
[8] Markus Nagel, Rana Ali Amjad, Mart van Baalen, Christos Louizos, and Tijmen Blankevoort.
Up or down? adaptive rounding for post-training quantization. In Proceedings of the 37th
International Conference on Machine Learning, ICML 2020, 13-18 July 2020, Virtual Event,
volume 119 of Proceedings of Machine Learning Research, pages 7197–7206. PMLR, 2020.
[9] Yuhang Li, Ruihao Gong, Xu Tan, Yang Yang, Peng Hu, Qi Zhang, Fengwei Yu, Wei Wang,
and Shi Gu. BRECQ: pushing the limit of post-training quantization by block reconstruction. In
9th International Conference on Learning Representations, ICLR 2021, Virtual Event, Austria,
May 3-7, 2021. OpenReview.net, 2021.
[10] Xiuying Wei, Yunchen Zhang, Xiangguo Zhang, Ruihao Gong, Shanghang Zhang, Qi Zhang,
Fengwei Yu, and Xianglong Liu. Outlier suppression: Pushing the limit of low-bit transformer
language models. In NeurIPS, 2022.
[11] Elias Frantar, Saleh Ashkboos, Torsten Hoefler, and Dan Alistarh. GPTQ: accurate post-training
quantization for generative pre-trained transformers. CoRR, abs/2210.17323, 2022.
[12] Zechun Liu, Barlas Oguz, Changsheng Zhao, Ernie Chang, Pierre Stock, Yashar Mehdad,
Yangyang Shi, Raghuraman Krishnamoorthi, and Vikas Chandra. LLM-QAT: data-free quantization aware training for large language models. CoRR, abs/2305.17888, 2023.
[13] Xiuying Wei, Yunchen Zhang, Yuhang Li, Xiangguo Zhang, Ruihao Gong, Jinyang Guo, and
Xianglong Liu. Outlier suppression+: Accurate quantization of large language models by
equivalent and optimal shifting and scaling. CoRR, abs/2304.09145, 2023.
[14] Mark Horowitz. 1.1 computing’s energy problem (and what we can do about it). In 2014 IEEE
International Conference on Solid-State Circuits Conference, ISSCC 2014, Digest of Technical
Papers, San Francisco, CA, USA, February 9-13, 2014, pages 10–14. IEEE, 2014.
[15] Yuzhang Shang, Zhihang Yuan, Qiang Wu, and Zhen Dong. PB-LLM: partially binarized large
language models. CoRR, abs/2310.00034, 2023.
11

[16] Geoffrey E. Hinton, Oriol Vinyals, and Jeffrey Dean. Distilling the knowledge in a neural
network. CoRR, abs/1503.02531, 2015.
[17] Adriana Romero, Nicolas Ballas, Samira Ebrahimi Kahou, Antoine Chassang, Carlo Gatta, and
Yoshua Bengio. Fitnets: Hints for thin deep nets. In Yoshua Bengio and Yann LeCun, editors,
3rd International Conference on Learning Representations, ICLR 2015, San Diego, CA, USA,
May 7-9, 2015, Conference Track Proceedings, 2015.
[18] Bin Liu, Fengfu Li, Xiaogang Wang, Bo Zhang, and Junchi Yan. Ternary weight networks.
In IEEE International Conference on Acoustics, Speech and Signal Processing ICASSP 2023,
Rhodes Island, Greece, June 4-10, 2023, pages 1–5. IEEE, 2023.
[19] Matthew Freestone and Shubhra Kanti Karmaker Santu. Word embeddings revisited: Do llms
offer something new?, 2024.
[20] Yoshua Bengio, Nicholas Léonard, and Aaron C. Courville. Estimating or propagating gradients
through stochastic neurons for conditional computation. CoRR, abs/1308.3432, 2013.
[21] Together Computer. Redpajama: an open dataset for training large language models, 2023.
[22] Kuntal Kumar Pal, Kazuaki Kashihara, Ujjwala Anantheswaran, Kirby C. Kuznia, Siddhesh
Jagtap, and Chitta Baral. Exploring the limits of transfer learning with unified model in the
cybersecurity domain. CoRR, abs/2302.10346, 2023.
[23] Stephen Merity, Caiming Xiong, James Bradbury, and Richard Socher. Pointer sentinel mixture
models. In 5th International Conference on Learning Representations, ICLR 2017, Toulon,
France, April 24-26, 2017, Conference Track Proceedings. OpenReview.net, 2017.
[24] Mitchell P. Marcus, Grace Kim, Mary Ann Marcinkiewicz, Robert MacIntyre, Ann Bies, Mark
Ferguson, Karen Katz, and Britta Schasberger. The penn treebank: Annotating predicate
argument structure. In Human Language Technology, Proceedings of a Workshop held at
Plainsboro, New Jerey, USA, March 8-11, 1994. Morgan Kaufmann, 1994.
[25] Yonatan Bisk, Rowan Zellers, Ronan Le Bras, Jianfeng Gao, and Yejin Choi. PIQA: reasoning
about physical commonsense in natural language. In The Thirty-Fourth AAAI Conference
on Artificial Intelligence, AAAI 2020, The Thirty-Second Innovative Applications of Artificial
Intelligence Conference, IAAI 2020, The Tenth AAAI Symposium on Educational Advances in
Artificial Intelligence, EAAI 2020, New York, NY, USA, February 7-12, 2020, pages 7432–7439.
AAAI Press, 2020.
[26] Peter Clark, Isaac Cowhey, Oren Etzioni, Tushar Khot, Ashish Sabharwal, Carissa Schoenick,
and Oyvind Tafjord. Think you have solved question answering? try arc, the AI2 reasoning
challenge. CoRR, abs/1803.05457, 2018.
[27] Christopher Clark, Kenton Lee, Ming-Wei Chang, Tom Kwiatkowski, Michael Collins, and
Kristina Toutanova. Boolq: Exploring the surprising difficulty of natural yes/no questions. In
Jill Burstein, Christy Doran, and Thamar Solorio, editors, Proceedings of the 2019 Conference
of the North American Chapter of the Association for Computational Linguistics: Human
Language Technologies, NAACL-HLT 2019, Minneapolis, MN, USA, June 2-7, 2019, Volume 1
(Long and Short Papers), pages 2924–2936. Association for Computational Linguistics, 2019.
[28] Rowan Zellers, Ari Holtzman, Yonatan Bisk, Ali Farhadi, and Yejin Choi. Hellaswag: Can a
machine really finish your sentence? In Anna Korhonen, David R. Traum, and Lluís Màrquez,
editors, Proceedings of the 57th Conference of the Association for Computational Linguistics,
ACL 2019, Florence, Italy, July 28- August 2, 2019, Volume 1: Long Papers, pages 4791–4800.
Association for Computational Linguistics, 2019.
[29] Keisuke Sakaguchi, Ronan Le Bras, Chandra Bhagavatula, and Yejin Choi. Winogrande: An
adversarial winograd schema challenge at scale. In The Thirty-Fourth AAAI Conference on
Artificial Intelligence, AAAI 2020, The Thirty-Second Innovative Applications of Artificial
Intelligence Conference, IAAI 2020, The Tenth AAAI Symposium on Educational Advances in
Artificial Intelligence, EAAI 2020, New York, NY, USA, February 7-12, 2020, pages 8732–8740.
AAAI Press, 2020.
[30] Hong Chen, Chengtao Lv, Liang Ding, Haotong Qin, Xiabin Zhou, Yifu Ding, Xuebo Liu, Min
Zhang, Jinyang Guo, Xianglong Liu, and Dacheng Tao. DB-LLM: accurate dual-binarization
for efficient llms. CoRR, abs/2402.11960, 2024.
12

[31] Wei Huang, Xudong Ma, Haotong Qin, Xingyu Zheng, Chengtao Lv, Hong Chen, Jie Luo,
Xiaojuan Qi, Xianglong Liu, and Michele Magno. How good are low-bit quantized llama3
models? an empirical study, 2024.
[32] Thomas M Cover. Elements of information theory. John Wiley & Sons, 1999.
[33] Sagar Eetha, PK Sruthi, Vibha Pant, Sai Vikram, Mihir Mody, and Madhura Purnaprajna.
Tilenet: Hardware accelerator for ternary convolutional neural networks. Microprocessors and
Microsystems, 83:104039, 2021.
[34] Shien Zhu, Luan HK Duong, and Weichen Liu. Tab: Unified and optimized ternary, binary,
and mixed-precision neural network inference on the edge. ACM Transactions on Embedded
Computing Systems (TECS), 21(5):1–26, 2022.

13

A

Appendix / Supplemental Material

Model

OPT-125M

OPT-1.3B

Learning rate
Logits KD loss coefficient
Feature KD loss coefficient
Feature KD number layers

1e-4
0.001
10
6

5e-5
0.001
10
18

OPT-2.7B

OPT-6.7B

LLaMA-7B

1e-4
0.001
10
18

5e-5
0.001
10
18

1e-4
0.001
5
18

Table 6: Training details for different models. We use the same training parameters for LLaMA-1,
LLaMA-2 and LLaMA-3.

A.1

Training Details

During the fine-tuning process, we optimize the trainable parameters using the AdamW optimizer
with zero weight decay. The batch size is set to 16. We implement cosine learning rate decay,
gradually decreasing to 0.1 times the initial value. All models undergo training for 10,000 steps,
including a 500-step warm-up period. The training is conducted on a single 8-GPU node of AMD
INSTINCT MI250. The learning rate for scales and shifts in DLT is set to 0.1 times weight learning
rate. Additional parameters are provided in Table 6.
A.2

Proof of Theorem 1

Theorem 1. Assume x ∈ RCi ∼ N (0, σx2 ), W = (w1T , w2T , . . . , wCo )T and y = RMSNorm(W x).
Let Wq denotes the ternarization of W and yq = RMSNorm(Wq x). The objective to maximize the mutual information between y and yq (formally, max I(y, yq )) can been achieved by
Ep(x) cos(Wq x, W x) = 1.
Proof. From the definition of RMSNorm, we have:
y =a⊙

Wx
+b
||W x||

(15)

yq = a ⊙

Wq x
+b
||Wq x||

(16)

W x

q
Wx
Set z = ||W
x|| and zq = ||Wq x|| , then we can simplify cosine similarity as follows:

Ep( x)

||y − yq ||22 ≤ Ep( x)

||a ⊙ (z − zq )||22

= Ep( x)

||a||22 · ||z − zq ||22

= Ep( x)

||a||22 · (||z||22 + ||zq ||22 − 2||z||2 ||zq ||2 cos(y, yq ))

(17)

= ||a||22 · (2 − Ep( x) cos(y, yq )) = 0
Thus, we have Ep(x) {(y − y q )(y − y q )T }ij ≤ Ep( x) ||y − yq ||22 = 0. Then, from the definition of
mutual information,
I(y, yq ) = H(y) − H(y|yq )
= H(y) − H(y − yq |yq )
≥ H(y) − H(y − yq )
1
≥ H(y) − log(2πe)n det(Ep(x) (y − y q )(y − y q )T )
2
= H(y)

(18)

The first inequality arises from the condition entropy H(X|Y ) ≤ H(X), while the second inequality
stems from Theorem 2.
14

Theorem 2. Let the random vector x ∈ Rn have zero mean and covariance K = E[xxT ] (i.e.,
Kij = E[Xi Xj ], 1 ≤ i, j ≤ n). Then h(x) ≤ 21 log(2πe)n|K|, with equality iff x ∼ N (0, K).
Proof. The proof of this theorem can be found in information theory textbooks [32].
A.3

Limitation

Although TernaryLLM enhances parameter compression ratios and facilitates LLM inference through
floating-point additions instead of multiplications, maximizing acceleration in LLM inference via
ternarization requires greater hardware support. Previous research has succeeded in hardware
accelerator for ternarized convolution networks [33, 34]. We hope this paper will attract more
researchers to focus on customized hardware for ternarized LLMs.

15


