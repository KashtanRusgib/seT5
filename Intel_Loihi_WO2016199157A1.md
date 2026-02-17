2/17/26, 11:04 AM
WO2016199157A1 - Ternary arithmetic and logic unit (alu) and ternary logic circuits - Google Patents
Patents
Ternary arithmetic and logic unit (alu) and ternary logic circuits
Abstract
A novel Ternary Arithmetic and logic Unit (TALU) comprising various logic circuit blocks, being an
essential building block of central processing unit (CPU) of computing machines means digital
WO2016199157A1
WIPO (PCT)
computers, microprocessors, microcontrollers or similar machines, is proposed in the present
invention, and for the execution of the said TALU, TRIT (ternary operator) having three discreet logic
Download PDF
Find Prior Art
Similar
levels, means 0, 1, &2 (TRIT level) levels are implemented to realize logic unit (TALU) operation. The
said implementation is achieved by the said gates using novel and dedicated combination of
transmission gates (TG), whereas the said TG comprises enhancement mode CMOS transistors
namely n-EMOS and p-EMOS having low output impedance, high input impedance and the
combination of such TG is arranged in such a way that resistance, capacitor elements are dispensed
with and the topology minimizes interconnections, reduces power consumption, decreases chip
Other languages: French
Inventor: Vijay Tulshiram INGOLE, Indira Vijay INGOLE, Ashutosh
Vijay INGOLE, Paritosh Vijay INGOLE
Current Assignee : Individual
area, increases processing speed, increases circuit ability to work at low operating voltage, reducing
output impedance, reduce noise. Following invention is described in detail with the help of Figure-1
of sheet 1 showing Plurality of 2 TRIT input TALU having n blocks in parallel.
Worldwide applications
2015 WO
Classifications
Application PCT/IN2015/000307 events
G06F7/49 Computations with a radix, other than binary, 8, 16 or decimal, e.g. ternary, negative
2015-08-03Application filed by Individual
2016-12-15Publication of WO2016199157A1
content of the data handled2017-12-11Anticipated expiration
Hide more classificationsStatusCeased
or imaginary radices, mixed radix non-linear PCM
G06F7/00 Methods or arrangements for processing data by operating upon the order or
Landscapes
Info: Non-patent citations (1) , Cited by (4), Legal events, Similar
documents, Priority and Related Applications
Engineering & Computer Science
External links: Espacenet, Global Dossier, PatentScope, Discuss
Physics & Mathematics
Show more
Claims
Hide Dependent
CLAIMS We claim :-
1. A ternary Arithmetic and logic unit (TALU) being essential building block of central processing unit (CPU) of computing machines means digital computers, microprocessors,
microcontrollers or similar machines, comprising:
a. a plurality of parallel stages of two ternary input operator (TRIT) TALU and such plurality of two ternary operated input means of forming a multi stage's, multi input ternary
operated ALU,and the said ternary having three defined discrete levels means a TRIT,
b. and the said TALU operation controlled by a single decoder comprising two TRIT OPCODE and having nine outputs and such Outputs of the said decoder controlling the
functioning of the said plurality of parallel TALU;
c. and for logic All Inclusive TAND and All inclusive TOR function operation means logic operation of the said stage and all prior stages of the said plurality of TALU;
' d. and the embodiment Adder comprises first embodiment first adder, second embodiment second adder, and third embodiment carry generator; and first input TRIT and
second input TRIT connected to first adder, first adder output TRIT connected to first input of second adder, carry from prior stage or add 1 carry to second input of the second
adder and outputted as final SUM and the said carry generator first input
'
connected to output of first adder, second input to first input TRIT, third input to second input TRIT and fourth input, to carry input from prior stage or add 1 carry gate and
outputted as final carry;
e. . and the first stage of the said TALU comprises an embodiment of present invention, ADD 1 CARRY logic gate means to get 3's compliment for two TRIT subtraction function;
f. and each stage of the said TALU comprises an embodiment of present invention, an arithmetic unit means 'adder for addition function
. and after first OPCODE command from control line of said decoder and first augends TRIT to first input, second addend TRIT second input and carry from prior one of the said
stages to third input of the said adder and resulted sum and carry outputted and the said carry inputted to next stage adder of the plurality of TALU ;
g. and subtraction operation initiated in the said adder after second OPCODE command from control line of said decoder and first minuend TRIT, second subtrahend TRIT and
carry input where minuend TRIT connected to first input, subtrahend TRIT inputted to another embodiment of the present invention, a TNOT gate and output connected to other
input and third input connected to from prior one of the said stages except for the first stage, means least significant trit TALU, of the plurality of TALU stages where said add 1
https://patents.google.com/patent/WO2016199157A1/en
1/142/17/26, 11:04 AM
WO2016199157A1 - Ternary arithmetic and logic unit (alu) and ternary logic circuits - Google Patents
carry logic gate adds carry and resulted sum and carry outputted and further for 3's complement of one of the said TRIT input connected to level 0 supply and remaining TRIT to
remaining input of the said embodiment and the said carry inputted to next stage adder of the plurality of ALU and further first minuend TRIT set to zero TRIT level, second
subtrahend
■ TRIT and carry inputted to said embodiment, 3's compliment of subtrahend outputted;
h. and subtraction operation initiated in the said adder after third OPCODE commands from control line of said decoder and second minuend TRIT, first subtrahend TRIT and
carry input where minuend TRIT connected to one input, subtrahend TRIT inputted to another embodiment of the present invention, said TNOT gate output and connected to
second input and third input connected to from prior one of the said stages except for the first stage of the plurality of TALU stages where said add 1 carry logic gate adds carry
and resulted sum and carry outputted and further for 3's complement of one of the said TRIT input connected to level 0 supply and remaining TRIT to remaining input of the said
embodiment and the said carry inputted to next stage adder of the plurality of ALU and further second minuendTRIT set to zero TRIT level; first subtrahend' TRIT and carry
inputted to said embodiment, 3's compliment of subtrahend outputted;
i. and for first logic COMPARATOR function executed by another embodiment of the present invention by comparator gate, after fourth OPCODE command from control line of
said decoder and first input TRIT connected to first input, second input, TRIT to second input of the said decoder and the result outputted, and for second logic XTOR gate
execution first input TRIT connected to first input, second input TRIT to second input of the said XTOR gate and the result outputted; j. and for logic TAND function execution by
another embodiment of the present invention by two TAND gates, after fifth OPCODE command from control line of said decoder, first TRIT connected to first input of the first
NAND gate, second TRIT connected to second input of the said TAND gate and the output of first TAND gate connected to first input of second TAND gate and the second input
connected to level 2 supply and further connected to second input of the second TAND gate to get two input TRIT TAND logic output, and the said output from second TAND
gate connected to another embodiment TNOT gate to get TNAND logic output;
k. and for logic All Inclusive TAND function execution by said embodiment of the present invention by two TAND gates, after sixth OPCODE command from control line of said
decoder, first TRIT connected to first input of the first NAND gate, second TRIT connected to second input of the said TAND gate and the output of first TAND gate connected to
first input of second TAND gate and the second input from. prior stage of the said plurality of TALU connected to second input of the said second TAND gate to get All Inclusive
TAND logic output and the said output from second TAND gate connected to another embodiment TNOT gate to get All Inclusive, TNAND logic output, 1. · and for logic TOR
function execution by another embodiment of the present invention by two TOR gates, after seventh OPCODE command from control line of said decoder and first TRIT
connected to first input of the first TOR gate, second TRIT connected to second input of the said TOR gate and the output of first TOR gate connected to first input of second
TOR gate and the second input connected to level 0 supply and further connected to second input of the said second TOR gate to get two input TRIT TOR logic output, and the
said output from second TOR gate connected to another embodiment TNOT gate to get TNOR logic output; m. and for logic All Inclusive TOR function operation by said
embodiment of the present invention by TOR gate, after eighth OPCODE command from control line of said decoder and first TRIT connected to first input of the first NOR gate,
second TRIT connected to second input of the said TOR gate and the output of first TOR gate connected to first input of second TOR gate and the second input from prior stage
of the said plurality of TALU connected to second input of the said second TOR gate to get All Inclusive TOR logic output and the said output from said TOR gate connected to
another embodiment TNOT gate to get All Inclusive TNOR logic output;
n. and after ninth OPCODE command from control line to execute NOP, operation, the all inputs TRIT connected to said plurality of ALU are disabled means level 1 supply at
control linemeans level 0 supply at control line enablesall operation of the said plurality of ALU enabled to function;
o. · and the execution of the functions as described in e,f,g,h,i,j,k,l,m and n multiplexed commands from said decoder to enable or disable, all input TRIT from first data string and
all second input TRIT from second data string, and carry from prior stage or add 1 carry, low level supply, high level supply; first output port and second output port by a single
decoder comprising two TRIT OPCODE and having nine outputs and such outputs of the said decoder controlling the functioning of the said plurality of parallel TALU;
p. and the logic operation of first even parity generator, input connected to said first input TRITstring of the stage so described and second input connected to the output of from
prior stage even parity ■ generator and the output of the said first even parity generator for the next stage of the said plurality of parallel ALU; and the logic operation of second
even parity generator, first input connected to said second input TRITstring of the stage so described and second input connected to the output of prior stage even parity
generator of the said TRIT string and the output of the said second even parity generator for the next stage of the said plurality of parallel ALU;
q. and the carry output from prior stages, first input string even parity generator and second input string even parity generator from the prior stages, All Inclusive TAND gate
output from prior stages, All Inclusive TOR gate output from prior stages outputted for the operation of next plurality of parallel ALU; further Carry output as OVERFLOW flag, All
Inclusive TOR gate output from prior stages as ALL ZERO flag outputted.
2. The embodiments as claimed in claim 1 comprises logic operators means gates comprising:
a. The first ADD 1 CARRY logic operator means gate comprises first TG and second TG in parallel and first terminal connected to level 1 supply, second terminal connected to
first terminal of third TG,'third TG connected to fourth TG and second terminal connected to level 0 supply, and the node of first TG and third TG a logic output and the negative
gate of first TG, second TG and positive gate of third TG, fourth TG connected to level 1 supply and positive gate of first TG and negative gate of fourth TG connected to decoder
control eighth output and positive gate of second TG and negative gate of third TG connected to decoder control seventh output and the said seventh, eighth output controls the
subtraction function and the said embodiment is connected to the first stage means least significant trit of the plurality of ALU; b. the second embodiment of the said plurality of
ALU as claimed in claim 1, comprises TNOT gate, and comprises first TG and second TG in series and first terminal of first TG connected to level 1 supply, second terminal of
first TG connected to first terminal of second TG, second terminal of the second TG connected to output, first terminal of third TG connected to level 2 supply, second terminal of
the third TG connected to output, first terminal of fourth TG connected to level 0 supply and second terminal of the fourth TG connected to output, and the negative gate of first
TG, second TG connected to level 0 supply, and negative gate of first TG and positive gate of second TG connected to input TRIT, positive gate of first TG connected level 2
supply, negative gate of second TG connected to input level 0 supply, negative gate of third TG connected to input TRIT, positive gate of third TG to level 1 supply, negative gate
of fourth TG connected to level 1 supply and positive gate of fourth TG connected to input TRIT; further embodiment counter clockwise rotate gate, other connection remaining
same as in the TNOT gate except first terminal of first TG connected to level 2 supply, first terminal of third TG connected to level 1 supply and first terminal of the fourth TG
connected to level 0 supply, further embodiment clockwise rotate gate, other connection remain same as in the TNOT gate except, first terminal of first TG connected to level 0
supply, first terminal of third TG connected to level 1 supply and first terminal of the fourth TG connected to level 2 supply; ! c. still another embodiment of the said plurality of
ALU as claimed in claim 1, comprises TAND gate, and comprises first TG, second TG in
'
parallel with third TG, and fourth TG in series and first terminal of first TG connected to level 1 supply, second terminal of first TG connected to level 1 supply terminal and first
terminal of second TG connected to level 1 supply, second terminal of the second TG connected to third TG, and second terminal of third TG connected to fourth TG and second
terminal of the fourth TG connected to output, fifth TG and sixth TG in series and first terminal of fifth TG connected to level 2 supply first terminal of sixth TG connected to fifth
TG and second terminal of sixth TG connected to output, first terminal of seventh TG connected to level 0 supply and second terminal of the seventh TG connected to output,
first terminal eighth TG connected to level 2 supply and second terminal of eighth TG connected to output, and positive gate of first TG and second TG connected to level 2
supply, negative gate of first TG connected to first input T IT, negative gate of second TG connected to
https://patents.google.com/patent/WO2016199157A1/en
2/142/17/26, 11:04 AM
WO2016199157A1 - Ternary arithmetic and logic unit (alu) and ternary logic circuits - Google Patents
■ second input TRIT, negative gates of third TG, fourth TG connected to level 0 supply, positive gate of third TG connected to first input TRIT, positive gate of fourth TG connected
to second input TRIT, negative gates of fifth TG and sixth TG connected to level 1 supply,, positive gate of fifth TRIT connected to first TRIT, positive gate of sixth TG connected to
second TRIT, positive gates of seventh TG and eighth TG connected to level I supply, negative gate of seventh TG connected to first input TRIT, negative gate of eighth TG
connected to second input TRIT; whereas further embodiment TNAND gate, other connection remaining same as in the TAND gate excepting first terminal of fifth TG connected
to level 0 supply in place of level 2 supply, first terminal of seventh TG connected to level 2 supply in place of level 0 supply;
d. still another embodiment of the said plurality of ALU as claimed in claim 1 , comprises TOR gate, and comprises first TG, second TG in parallel with, third TG, and fourth TG in
series and first terminal of first TG connected to level 1 supply, second terminal of first TG connected to level 1 supply, second terminal of the second TG connected to third TG,
and second terminal of third TG connected to fourth TG and second terminal of the fourth TG connected to output, fifth TG and sixth TG in series and first terminal of fifth TG
connected to level 0 supply, first terminal of sixth TG connected to fifth TG and second terminal of sixth TG connected to output, first terminal of seventh TG connected to level 2
supply and second terminal of the seventh TG connected to output, first terminal Of eighth TG connected to level 2 supply and second terminal of the eighth TG connected to
output, and negative gate of first TG and second TG connected to level 0 supply, positive gate of first TG connected to second input TRIT, positive gate of second TG connected
to first input TRIT, positive gates of third TG, fourth TG connected to level 2 supply, negative gate of third TG connected to second input TRIT, negative gate of fourth TG
connected to first input TRIT, positive gates of fifth TG and sixth TG connected to level 1 supply, negative gate of fifth TG connected to first TRIT, negative gate of sixth TG
connected to second TRIT, negative gates of seventh TG and eighth TG connected to level 1 supply, positive gate of seventh TG connected to first input TRIT, positive gate of
eighth TRIT connected to second input TRIT; whereas further embodiment TNOR gate, other connection remaining same as in the TOR gate excepting first terminal of fifth TG
connected to level 2 supply in place of level 0 supply, first terminal of seventh TG connected to level 0 supply in place of level 2 supply;
e. still another embodiment of the said plurality of ALU as claimed in claim 1, comprises XTOR gate, and comprises first TG, second TG, third TG, and fourth TG in series and first
terminal of first TG connected to level 0 supply, second terminal of first TG connected to first term inal of second TG, second terminal of the second TG connected to third TG,
and second terminal of third TG connected to fourth TG and second terminal of the fourth TG connected to output, fifth TG and sixth TG in series and first terminal of fifth TG
connected to level 0 supply, positive gates of first TG and second TG connected to level 2 supply, negative gate of first TG connected to first input TRIT, negative gates of second
TG connected to second input TRIT, negative gates of third TG and fourth TG connected to LEVEL 0 supply, positive gate of third TG connected to first input TRIT, positive gate of
the fourth TG connected to second input TRIT; first terminal of sixth TG connected to fifth TG and second terminal of sixth TG connected to output, seventh TG and eighth TG in
series and first terminal of sixth TG connected to level 0 supply, first terminal of seventh TG connected to eighth TG and second terminal of eighth TG connected to output,
positive gates of fifth TG, sixth TG connected to level 1 supply, negative gate of fifth TG connected to second input TRIT, negative gate of sixth TG connected to first input TRIT,
negative gates of seventh TG and eighth TG connected to level 1 supply, positive gate of seventh TG connected to second input TRIT, positive gate of eighth TG connected to
first input TRIT; ninth TG and tenth TG in parallel and series with eleventh TG, first terminal of ninth TG connected to level 2 supply, first terminal of tenth TG connected to level 1
supply, second terminals of ninth TG and tenth TG connected to first terminal of eleventh TG, second terminal of eleventh TG connected to output, positive gate of ninth TG
connected to second ■ input TRIT, negative gate of ninth TG connected to level 1 supply, positive gate of tenth TG connected to level 2 supply, negative gate of tenth TG
connected to second input TRIT, positive gate of eleventh TG connected to second input TRIT, negative gate of eleventh TG connected to first input TRIT; twelfth TG and
thirteenth TG in parallel and series with fourteenth TG, first terminal of twelfth TG connected to level 2 supply, first terminal of thirteenth TG connected to level 1 supply, second
terminals of twelfth TG and. thirteenth TG connected to first terminal of fourteenth TG, second terminal of fourteenth TG connected to output, positive gate of twelfth TG
connected to first input TRIT, negative gate of twelfth TG connected to level 1 supply, negative gate of thirteenth TG connected to level 2 supply, positive gate of thirteenth TG
connected to first input TRIT, positive gate of fourteenth TG connected to first input TRIT, negative gate of eleventh TG connected to second input TRIT;
f. still another embodiment of the said plurality of ALU as claimed in claim 1 , comprises COMPARATOR gate,' and comprising first TG, second TG, third TG, and fourth TG in
series and first terminal of first TG' connected to level 0 supply, second terminal of first TG connected to first terminal of second TG, second terminal of the second TG
connected to third TG, and second terminal of third TG connected to fourth TG and second terminal of the fourth TG connected to output, fifth TG and sixth TG in series and first
terminal of fifth TG connected to level 0 supply, positive gates of first TG and second TG connected to level 2 supply, negative gate of first TG connected to first input TRIT,
negative gates of second TG connected to second input TRIT, negative gates of third TG and fourth TG connected to LEVEL 0 supply, positive gate of third TG connected to first
input TRIT, positive gate of the fourth TG connected to second input TRIT; .first terminal of sixth TG connected to fifth TG and second terminal of sixth TG connected to output,
seventh TG and eighth TG in series and first terminal of sixth TG connected to level 0 supply, first terminal of seventh TG connected to eighth TG and second terminal of eighth
TG connected to output, positive gates of fifth TG, sixth TG connected to level 1 supply, negative gate of fifth TG connected to secon'd input TRIT, negative gate of sixth TG
connected to first input TRIT, negative gates of seventh TG and eighth TG connected to level 1 supply, positive gate of seventh TG connected to second input TRIT, positive gate
of eighth TG connected to first input TRIT; ninth TG and tenth TG in parallel, first terminal of ninth TG connected to level 2 supply, first terminal of tenth TG connected to level 1
supply, second terminals of ninth TG and tenth TG connected to output, negative gate of ninth TG connected to second input TRIT, positive gate of the ninth TG connected to first
input TRIT, negative gate of tenth TG connected to first input TRIT, positive gate of the tenth TG connected to second input TRIT;
g. and still another embodiment of the said plurality of ALU as claimed in claim 1, comprises adder 1, comprising first TG, second TG and third TG in series, fourth TG in parallel,
and fifth TG connected to the node of first TG, third TG, fourth TG, the second terminal of fifth TG connected to output, fist terminal of first TG connected to level 1 supply, first
terminal of second TG connected to level 0 supply, first terminal of fourth TG connected to level 2 supply, positive gate of first TG connected to first input TRIT, negative gate of
first TG connected to level 1 supply, positive gate of second TG connected to first input TRIT, negative gate of second TG connected to level 0 supply, negative gate of third ' TG
connected to first input TRIT, positive gate of third TG connected to level 2 supply, positive gate of fourth TG connected to input TRIT, negative gate of fourth TG connected to
level 1 supply, positive gate of fifth TG connected to second input TRIT, negative gate of fourth TG connected to level 1 supply, sixth TG, seventh TG and eighth TG in series, ninth
TG in parallel, and tenth TG connected to the node of sixth TG, seventh TG, eighth TG, the second terminal of tenth TG connected to output, fist terminal of sixth TG connected to
level 2 supply, first terminal of seventh TG connected to level 1 supply, first terminal of ninth TG connected to level 0 supply, positive gate of sixth TG connected to first input
TR1T, negative gate of sixth TG connected to level 1 supply, positive gate of seventh TG connected to first input TRIT, negative gate of seventh TG connected to level 0 supply,
negative gate of eighth TG connected to first input TRIT, positive gate of eighth TG connected to level 2 supply, negative gate of ninth TG connected to first input TRIT, positive
gate of ninth TG connected to level 1 supply, negative gate of tenth TG connected to second input TRIT, positive gate of tenth TG connected to level 1 supply, eleventh TG, twelfth
TG and thirteenth TG in series, fourteenth TG in parallel, and fifteenth JG in series with sixteenth TG and fifteen TG .connected to the node of eleventh TG, thirteenth TG,
fourteenth TG, the second terminal of sixteenth TG connected to output, first terminal of eleventh TG connected to level 0 supply, first terminal of twelfth TG connected to level 2
supply, first terminal of fourteenth TG connected to level 1 supply, positive gate of eleventh TG connected to first input TRIT, negative gate of eleventh TG connected to level 1
supply, positive gate of twelfth TG connected to first input TRIT, negative gate of twelfth TG connected to level 0 supply, negative gate of thirteenth TG connected to first input
TRIT, positive gate of thirteenth 'TG connected to level 2 supply, negative gate of fourteenth TG connected to first input TRIT, positive gate of fourteenth TG connected to level 1
supply, negative gate of fifteenth TG connected to level 0 supply, positive gate of fifteen TG connected to second input TRIT, positive gate of sixteenth TG connected to level 2
supply, negative gate of sixteenth TG connected to level 0 supply;
h. and still another embodiment of the said plurality of ALU as claimed in claim 1, comprises adder 2, first TG first terminal connected to output of adder 1 means SI , second
terminal of first TG connected to output, positive gate of first TG connected to level 1 supply, negative gate is connected to carry in means Cn7, second TG first terminal
connected to level 1 supply, second terminal of second TG connected to fifth TG node, positive gate of second TG connected to level 1 supply, negative terminal of the second
TG connected to SI , third TG, fourth TG, fifth TG in series, third TG first terminal connected to level 2 supply and negative gate connected to level 0. supply, fourth TG second
terminal connected to the node at first terminal of fifth TG, fourth TG positive gate connected to level 1 supply, negative gate connected to S I , sixth TG first terminal connected
to level 0 supply, second terminal to the said node, negative gate connected to level 1 supply, positive gate connected to SI, fifth TG second terminal connected to output,
negative gate connected to level 0 supply, positive gate connected to Cn;
https://patents.google.com/patent/WO2016199157A1/en
3/142/17/26, 11:04 AM
WO2016199157A1 - Ternary arithmetic and logic unit (alu) and ternary logic circuits - Google Patents
i. and still another embodiment of the said plurality of ALU as claimed in claim 1, FULL CARRY gate, comprising first TG, second TG in series, first terminal of first TG connected
to level 1 supply, negative gate connected to level 1 supply, and positive gate connected to SI, second TG second terminal connected to output, negative gate connected to level
0 supply, positive gate connected to Cn, fourth TG, fifth TG in series, first terminal of third TG connected to level 1 supply, positive gate connected to second input TRIT, fourth TG
positive gate connected to first input TRIT, negative gate connected to level 0 supply, second terminal connected to a node with fifth TG in parallel with sixth TG, fifth TG second
terminal connected to output,, negative gate connected to level 1 supply, positive gate connected to second input TRIT, sixth TRIT second terminal connected to output, positive
gate connected to second input TRIT, negative gate connected to level 1 supply;
j. and still another embodiment of the said plurality of ALU as claimed in claim 1, 2 input TRIT DECODER; comprising for first decoded output, first TG parallel with second TG
and series with third TG, fourth TG, first terminals of first TG, second TG connected to level 0 supply, second connection of fourth TG connected to level 2 supply, negative gate
of first TG connected to second input TRIT, positive gate of first TG connected to level 2 supply, second TG negative gate connected to first input TRIT, positive gate of second
TG connected to level 2 supply, third TG first terminal connected to first TG and second TG output node, negative gate of third TG connected to level 1 supply, positive gate of
third TG connected to second input TRIT, fourth TG negative gate connected to level 2 supply, positive gate of fourth TG connected to second input TRIT; and DECODER gate;
comprising for second decoded output, parallel 5th TG , 6th TG and 7th TG connected to series 8th TG, 9th TG, 10th TG; first terminals of 5th TG, 6th TG and 7th TG connected to
level 0 supply, second terminal of 10th TG connected to level 2 supply, negative gate of 5th TG connected to second input TRIT, positive gate of 5th TG connected to level 2
supply, 6th TG negative gate connected to level 1 supply, positive gate of 6th TG connected to first input TRIT, negative gate of 7th TG connected to first input TRIT, positive gate
of 5th TG connected to level 1 supply, 8th TG first terminal connected to 5th TG, 6th TG and 7th TG output node, negative gate of 8th TG connected to level 1 supply, positive gate
of 8th TG connected to second input TRIT, 9th TG negative gate connected to level 2 supply, positive gate of 9th TG connected to first 2 level supply, 10th TG negative gate
connected to level 0 supply, positive gate of 10th TG connected to first input TRIT; and DECODER gate; comprising for third decoded output, eleventh TG parallel with twelfth TG
and series with ' thirteenth TG, fourteenth TG, first terminals of eleventh TG, twelfth TG connected to level 0 supply, second connection of fourteenth TG connected to level 2
supply, negative gate of eleventh TG connected to second input TRIT, positive gate of eleventh TG connected to ievel 2 supply, twelfth TG negative gate connected to second
input TRIT, negative gate of twelfth TG connected to level 0 supply, positive gate of twelfth TG connected to second input TRIT, thirteenth TG first terminal connected to first TG
and second, TG output node, negative gate of thirteenth TG connected to first input TRIT, positive gate of thirteenth TG connected to level 1 supply, fourteenth TG negative gate
connected to level 1 supply, positive gate of fourth TG connected to second input TRIT; and DECODER gate; comprising for fourth decoded output, parallel 15th TG , 16th TG and
17th TG connected to- series 18lh TG, 19th TG, 20th TG; first terminals of 15th TG, 16th TG and 17th TG connected to level 0 supply, second terminal of 20th TG connected to level
2 supply, negative gate of 1 th TG connected to Ievel 1 supply, positive gate of 15th TG connected to second input TRIT, 16th TG negative gate connected to second input TRIT,
positive gate of 16th TG connected to Ievel I supply, negative gate of 17th TG connected to first input TRIT, positive gate of 17th TG connected to level 2 supply, 18th TG first
terminal connected to 15th TG, 16th TG and 17th TG output node, negative gate of 18th TG connected to level 1 supply, positive gate of 18th TG connected to first input TRIT,
19th TG negative gate connected to second input TRIT, positive gate of 19th TG connected to level 2 supply, 20th TG negative gate connected to Ievel 0 supply, positive gate of
10th TG connected to second input TRIT, and DECODER gate; comprising for fifth decoded output, parallel 21th TG , 22ni TG, 23th TG and 24m TG connected to series 25th TG,
26th TG, 27th TG, 28th TG; first terminals of 21st TG, 22th,TG, 23rd TG and 24th TG connected to level 0 supply, second terminal of 28th TG connected to level 2 supply, negative
gate of 21th TG connected to level 1 supply, positive gate of 21th TG connected to second input TRIT, 22th TG negative gate connected to second input TRIT, positive gate of
22th TG connected to level 1 supply, negative gate of 23th TG connected to'level 1 supply, positive gate of 23th TG connected to first input TRIT, negative gate of 24th TG
connected to first input TRIT, positive gate of 24th TG connected to level 1 supply, 25th TG first terminal connected to 21th TG, 22th TG, 23rd TG and 24th TG output node,
negative gate of 25th TG connected to second input TRIT, positive gate of 25th TG connected to level 2 supply, 26th TG negative gate connected to level 0 supply, positive gate
of 26th TG connected to level 2 supply, 27th TG negative gate connected to first input TRIT, positive gate of 27th TG connected to first input TRIT, 28th TG negative gate
connected to level 0 supply, positive gate of 28th TG connected to first input TRIT; and DECODER gate; comprising for sixth decoded output, parallel 29th TG , 30th TG and 31th
TG connected to series 32th TG, 33th TG, 34th TG; first terminals of 29th TG, 30th TG and 31th TG connected to level 0 supply, second terminal of 34th TG connected to level 2
supply, negative gate of 29th TG connected to level 1 supply, positive gate of 29th TG connected to second input TRIT, 30th TG negative gate connected to second input TRIT,
positive gate of 30th TG connected to level 1 supply, negative gate of 31th TG connected to level 0 supply, positive gate of 31th TG connected to first input TRIT, 32th TG first
terminal connected to 29th TG, 30th TG and 31th TG output node, negative gate of 32th TG connected to second input TRIT, positive gate of 32th TG connected to second input
TRIT, 33th TG negative gate connected to level 0 supply, positive gate of 33th TG connected to second input TRIT, 34th TG negative gate corinected to first input TRIT, positive
gate of 34th TG connected to level 2 supply; and DECODER gate; comprising for seventh decoded output, 35th TG parallel with 36th TG and series with 37th TG, 38th TG, first
terminals of 35th TG, 36th TG connected to level 0 supply, second connection of 38th TG connected to level 2 supply, negative gate of 35th TG connected to level 0 supply,
positive gate of 35th TG connected to second input TRIT, 36th TG negative gate connected to first input TRIT, positive gate of twelfth . TG connected to level 2 supply, 37th TG
first terminal connected to 35th TG and 36th TG output node, negative gate of 37th TG connected to second input TRIT, positive gate of 38th TG connected to level 2 supply, 38th
TG negative gate connected to level 1 supply, positive gate of 38th TG connected to first input TRIT; and DECODER gate; comprising for eighth decoded output, parallel 39th TG ,
40th TG and . 41th TG connected to series 42tH TG, 43th TG, 44th TG; first terminals of 39th TG, 40th TG and 41th TG connected to level 0 supply, second terminal of 44th TG
connected to level 2 supply, negative gate of 39th TG connected to level 0 supply, positive gate of 39th TG connected to first input TRIT, 40th TG negative gate connected to level
1 supply, positive gate of 40th TG connected to first input TRIT, negative gate of 41th TG connected to first input TRIT, positive gate of 41th TG connected to level 1 supply, 42th
TG first .terminal connected to 39th TG, 40th TG and 41th TG output node, negative gate of 42th TG connected to second input TRIT, positive gate of 42th TG connected to level 2
supply, 43th TG negative gate connected to first input TRIT, positive gate of 43th TG connected to level 2 supply, 44th TG negative gate connected to level 0 supply, positive gate
of 44th TG connected to first input TRIT; and DECODER gate; comprising for ninth decoded output, 45th TG parallel with 46th TG and series with 37th TG, 48th TG, first terminals
of 45th TG, 46th TG connected to level 0 supply, second connection of 48th TG connected to level 2 supply, negative gate of 45th TG connected to level 0 supply, positive gate of
45th TG connected to second input TRIT, 46th TG negative gate connected to level 0 supply, positive gate of 46th TG connected to first input TRIT, 47th TG first terminal
connected to 45th TG and 46th TG output node, negative gate of 47th TG connected to first input TRIT, positive gate of 47th TG connected to level 1 supply, 48th TG negative
gate connected • to second input TRIT, positive gate of 48th TG connected to level 1 supply.
3. The embodiment as claimed in claim 1 comprising TAND gate and TNOT gate combination logic may be substituted by TNAND gate.
4. The embodiment as claimed in claim 1 comprising TOR gate and TNOT gate combination logic may be substituted by TNOR gate.
5. The embodiment transmission gate means TG as claimed in claim 1 may be suitably substituted by p-ECMOS, n-ECMOS and any equivalent transistor or similar devices.
6. The execution of functions in the TALU as claimed in claim 1, the said decoder having different OPCODE.
7. The embodiment transmission gate means TG multiplexers as claimed in claim 1, wherein the one control terminal of each ECMOS device may be connected to substrate of
other device or to opposite polarity of ■ supply.
8. The TALU as claimed in claim 1 may have different function combinations.
9. The said most significant TR1T TALU as claimed in claim 1 may • function as sign TRIT.
https://patents.google.com/patent/WO2016199157A1/en
4/142/17/26, 11:04 AM
WO2016199157A1 - Ternary arithmetic and logic unit (alu) and ternary logic circuits - Google Patents
10. The unbalance ternary logic as claimed in claim 1, may be replaced by balanced ternary logic.
Description
TITLE OF INVENTION
Ternary Arithmetic and Logic Unit (ALU) and Ternary Logic Circuits
Technical field of invention:
Present invention in general relates to plurality of ternary arithmetic and logic unit (ALU) comprising plurality of ternary inputs to execute majority of arithmetic and logic
operations; particularly by implementing dedicated ternary logic circuits having optimum device count and which may be realized by semiconductor transmission gate
(TG) comprising enhancement complementary metal oxide semiconductors integrated circuits so as to provide practical means of high processing speed, high density
digital integrated circuit chip with
■ emerging semiconductor manufacturing technology.
Prior art:
Moore's law conjectured that the semiconductor transistor would double every ten years. Chip performance will double every 18 months due to higher device density and
speed (Intel Exe. quote). In order to increase speed of operation and to reduce device power consumption many manufacturing steps have been taken so far. However,
the present binary based designs appear to be pushing the technology towards physical limitations. Parallel processing though increases speed of operation, but
■ does not necessarily influence the device count. Hence there appears to be an immediate need to go in for multi level logic (MVL) to increase the speed of operation,
handle very large data and reduce relative device count. The decimal numerical system is the most widely used by civilization for arithmetic operation having a base
means radix of Ten (10) and comes under the category of Multi Valued Logic (MVL) system whereas modern computer system operates on Boolean logic having radix 2
and known as two value logic system meaning thereby a binary system. The binary system has come in vogue because of its simplicity as having only two levels or
discrete states such as high and low and can be predicted and easily implemented in electronic or other hardware for further utilities. However, attempts have been made
to develop digital machines which would operate and process a digital system operating on higher radix than 2. It is evident from the, mathematical analysis that higher
the radix more is the memory density per digit. However; it is at the cost of more complexity. Most optimum, a product of radix and number of digits, for numbering
system has been calculated to be 2.718 which happens to be the natural logarithmetic base 'e'. However, 'e' not being an integer the closest natural integer is three that
would be practically be most optimum radix. Hence attempt is made to design computing machines with radix three. For comparison if a binary logic processor is
replaced by a ternary logic processor in the present setup for the ratio of ternary information to binary information for "n" bit processor is given by the ratio (3Λη/2Λη)
means in one cycle a 32 input processor would process data equal to 32Λ1 ,5=4.29* 10Λ9. That means a Ternary processor for n=32 trit will process data 4.29 billion
times than contemporary binary 32 bit processor. As regards the component count, the ternary logic 2 input NAND gate circuits, hitherto referred to as 2 TRIT input
TNAND, requires approximately twice the number of components as in 2 bit input binary NAND and the ratio of component count for ternary logic to binary logic may be
expressed by 2*3Λη/2Λη = 0.5* (3/2)Λη, where 'n' denotes number of inputs trit or bits. It therefore may be deduced that the information processing capacity per device
increases exponentially for higher number of TRIT input logic circuits.
With advancement in electronics and the demand for high speed and large data handling processor have rendered the present binary system perhaps to its natural
limitations due to operating frequency, device voltage, device geometry, component count, transmission delay, interconnections however, parallel processing may have
the solution but there are practical limitations. It may therefore be surmise that to circumvent all present limitations of binary system, ternary logic may be the' only way
out in the present scenario to enhance computing capabilities of present day computing machines. ·
With the development of the semiconductor integrated circuit technology, the chip power consumption, the chip area, comprising device area and interconnections, have
been fundamental restricting factor for its implementation. The theory of multi-valued logic provides an effective and efficient way for decreasing the area of internal
wiring and decrease in number of devices per processing, thereby effectively decreasing chip area and enhancing data handling capacity. Owing to such advantages
attention towards ternary logic system has been focused in research for its practical implementation.
Ternary logic system is referred to by different nomenclatures such 'as tri state logic, three valued logic, 3-trit Trinary and further by its mode means state such as
balance (+1,0,-1) and unbalance (2,1,0), and still further by voltage or current supply source. The type of mode like balance or unbalance practically makes no difference
in the basic principle of operation of the said Ternary Logic. Similarly voltage source or current source makes no difference, on the logic operations of ternary system.
Conventionally a binary single input is known as 'bit' likewise ternary logic single input is referred to as 'trit' or TRIT. Due to some unique properties of enhancement
complementary metal oxide semiconductors (ECMOS), a transmission gate may be used as a switch operated by positive/ negative control input signal. The control
signal is applied to gates having very large input impedance. The device changes from high impedance to low impedance on application of suitable gate signal. The said
switch is referred to as Transmission Gate, hitherto referred to as TG and it comprises p-channel ECMOS in parallel with n- channel ECMOS having their source and drain
in parallel and thus the common source, common drain and two respective gates form a four terminal switch. Practical ternary logic operators means gates may be
realized by suitable circuit topology of such TG and TG can be replaced by suitable p-channel ECMOS and n-channel' ECMOS devices as demanded by circuit topology.
To realize various arithmetic and logic operations quite a few ternary circuits have been reported.
US patent application numbered 20140292373 Al provides for ternary t athematic circuit based on adiabatic Domino logic wherein adiabatic technology and the Domino
logic are combined to the T operation circuit to develop a ternary T arithmetic circuit based on an adiabatic Domino logic.
Commonly-assigned U.S. Pat. No. 7,565,388, which is hereby incorporated by reference herein in its entirety, describes a programmable device having logic blocks
including lookup-table based logic elements that can be configured to perform logical and arithmetic operations. In arithmetic mode, those logic elements could be
configured to perform binary addition among other functions, or, by selecting, as an input to a dedicated adder in one logic element a signal from another logic element to
perform ternary addition.
US patent application numbered 8482312 B l discloses logic block structure in an integrated circuit device that can be used to perform binary or ternary addition, as well
as other arithmetic and logical functions. Each logic module in the logic block includes a plurality of lookup tables and a plurality of dedicated adders. At least one of the
dedicated adders has a dedicated input from another logic module in the logic block to facilitate ternary arithmetic operations such as ternary addition.
The major problems associated with existing arithmetic and logic operations and ternary circuits are:
1. Certain resistance elements have been proposed which may hamper high speed operation and lead to higher power consumption.
https://patents.google.com/patent/WO2016199157A1/en
5/142/17/26, 11:04 AM
WO2016199157A1 - Ternary arithmetic and logic unit (alu) and ternary logic circuits - Google Patents
2. P-N junction means diode as circuit elements have been proposed making them not suitable for low voltage operation and having higher power consumption.
3. Certain circuits have high output resistance at mid-level logic state and may lead to erroneous outputs, and other circuits reported are inherently voltage sensitive
hence provide limited flexibility in designs.
A need is therefore felt to have a ternary logic ALU, being an essential part of any processor, comprising ternary logic circuits which can be fabricated with current VLSI
technology, having a topology in line with binary operators but having more information per trit, low component count, high input impedance, low output impedance, easy
to fabricate and faster in processing data.
Object:
1. A primary object of the present invention is to provide a novel ternary logic based plurality of arithmetic and logic unit (TALU) circuit block comprising plurality of
ternary logic operators and circuits based on contemporary fabrication techniques based on p & n ECMOS semiconductors.
2. Another object of the present invention is to provide plurality of such TALU circuit blocks in parallel and to have plurality of TRIT number to enhance the processing
capacity.
3. Another object of the present invention is to provide plurality of ternary logic operators and novel circuits so as to provide various logic circuits having low device count
such as TNOT gate, clockwise complementary gate (CWC GATE), counter clockwise complementary gate (CCWC GATE), ADD-1 CARRY GATE; TAND, TNA D, TOR, TNOR,
XTOR, COMPARATOR, 2 TRIT ADDER, 2 TRIT EVEN PARITY GENERATOR, 3's COMPLIMENT, CARRY GENERATOR, FULL ADDER; 2x9 DECODER.
4. Still another object of the invention is to implement transmission gate (TG) elements comprising combination circuit of p & n ECMOS as a basic building block for the
realization of various circuits for simplicity, reduced chip area and ease of fabrication. 5. Still another object of the invention is to provide circuits having high input
impedance and low source-sink means output impedance for large fan outputs and to minimize noise.
6. Another object of the invention is to dispense with passive component like resistance, and diodes as circuit element to eliminate parasite quiescent power losses.
7. Still further object of the invention is to minimize component count by dedicated circuits, high processing speed, lower component count per trit and inherent
fundamental properties of ternary system over binary system.
8. Still another object of the present invention is to provide more than 22 output functions with 2 TRIT OPCODE including ALL ZERO flag, OVERFLOW flag, EVEN PARITY
GENERATOR TRIT output for each OPERAND.
Further objects and features can be readily understood by any person skilled in the art by referring to the detailed description and appended claims of the invention.
STATEMENT:
Following invention provides a ternary Arithmetic and logic unit (TALU) which is a fundamental building block of central processing unit (CPU) in computer architecture,
microprocessor, microcontroller and similar computing machines, hereinafter referred to as computer, for performing basic ternary arithmetic and logic operations on the
plurality of variable TRIT operands (input/output) means having a three level discrete value pertaining to level 0 supply, level 1 supply, and level 2 supply, means as in
unbalance ternary, respectively and particularly relates to the provision of practical three valued levels generally referred to as 'trit'; and based on the instructions received
from the peripheral control blocks of central processing unit (CPU) of a computer and may pass on the results to the memory elements or other processing block
depending on the instructions meant for further processing. The ternary arithmetic and logic unit (TALU) further comprising other blocks for performing arithmetic
operation such as 1 addition, subtraction, 3's complement, 2's compliment, 3's compliment, comparator, parity generator and the logic operations such as NOP, AND
(TAND), ternary NAND (TNAND), ternary OR (TOR), All inclusive TAND, All inclusive NAND (TNAND), All inclusive TOR, All inclusive TNOR, where 'All inclusive' means the
logic data from prior stage to the logic gate under operation means operand; ternary exclusive OR (XTOR), ternary comparator,; and flags like ALL ZERO, OVERFLOW, one
even parity for each TRIT operand; a common Decoder (function select OPCODE logic), common add 1 carry block.
A said single TALU block comprises various logical circuit combinations of transmission gate (TG) as a switch comprised of enhancement complementary metal oxide
semiconductors (ECMOS), p- ECMOS, n-ECMOS, carbon nano tube (CNT) semiconductor technology so as to provide a practical means of high device density, high speed
digital processing. Further Complimentary silicon field effect transistor devices (CMOS), carbon nano tube (CNT) devices may offer distinct advantage in logic circuit
design due to low operational power, low operating voltage and higher operating speed.
It will be readily understood that the ternary ALU means TALU can be realized by implementing ternary logic circuits or gates. Other objects, features and advantages will
become apparent from detail description and appended claims to those skilled in art. BRIEF DESCRIPTION OF DRAWING:
These and other features and objects of the invention, and exemplary operating circuits embodying the principles of the present invention, are discussed in greater
details hereinafter, in association with the accompanying drawings wherein a three-valued logic operator means operand, hereinafter referred to TO or TRIT, which may be
operable with an input at any one of the three discrete voltage levels -V, Q, and +V in balance ternary; "or their equivalent levels 0, 1, and 2 in an unbalance ternary,
respectively or simply denoted by level 0 supply, level 1 supply, and level 2 supply which henceforth be referred to in the accompanying description.
Sheet 1 of 9: Figure- 1 is Plurality of 2 TRIT input TALU having plurality of n blocks in parallel;
Sheet 2 of 9: Figure-2 is the internal logic circuit blocks of a typical single TALU;
Sheet 3 of 9: Figure-3 is internal circuit of prior art Transmission Gate (TG), Figure-4 is symbol of prior art TG, Figure-5 is ADD 1 CARRY ternary gate, Figure-6 is Simple
TNOT ,gate, Figure-7 is Counter Clockwise Complementary gate (CCWC), Figure-8 is Clockwise Complementary (CWC);
Sheet 4 of 9: Figure-9 is 2 TRIT input TAND, Figure- 10 is 2 TRIT input TNAND, Figure-11 is 2 TRIT input TOR, Figure-12 is 2 TRIT input TNOR;
Sheet 5 of 9: Figure-13 is 2 TRIT input Comparator, Figiire-14 is 2 TRIT input XTOR, figure-15 is 2X9 function select Decoder;
Sheet 6 of 9: Figure-16 is 2 TRIT input first Adder (S I), Figure-17 is second adder (S2) having sum S I and carry in (Cin), Figure- 18 is Final carry generator C2 having 3
input comprising 1 input SI , and 2 inputs for generated carry CI, Cin; Figure- 19 is a FULL SUM and CARRY block diagram, Figure-20A and figure-20B comprising ternary
parity generators for 2 TR1T operand input;
Sheet 7 of 9: Figure-21A is first part internal circuit diagram of two TRIT TALU block;
Sheet 8 of 9: Figure-21B is second and remaining part internal circuit diagram of two TRIT TALU block;
Sheet 9 of 9: Figure-22 is a combined internal circuit diagram of two trit TALU block.
https://patents.google.com/patent/WO2016199157A1/en
6/142/17/26, 11:04 AM
WO2016199157A1 - Ternary arithmetic and logic unit (alu) and ternary logic circuits - Google Patents
In order and the manner in which the above-cited and other advantages and objects of the invention are obtained, a more particular description of the invention briefly
described above will be referred to, which are illustrated in the appended drawing. Understanding that these drawing depict only typical embodiment of the invention and
therefore not to be considered limiting on its scope, the invention will be described with additional specificity and details through the, use of the accompanying drawing.
Detailed description:
Sheet 1 of 9: Figure-1 shows (100) the basic block diagram of plurality of TALU comprising 'n' number 2 ternary operators, hereinafter referred to as 2 TRIT, TALU 101, 111,
121 in parallel so as to function as plurality of 'n' 2 TRIT input TALU system. The first TALU may be named as, comprising least significant trit (LST), TALU (0) 101 having 2
TRIT input 102, add 1 carrylld, and function select decoder (OPCODE) 125 having two TRITcontrol input, function outputs 103 and data output 104 and data 104 are
cascaded to TALU (1) 111 having 2 TRIT input 112, function output 113. Data output 104 may be required for processing of next means next' significant TALU (1 ). The
output data 105 from TALU (1) 111 is connected to next significant TALU (2) (not shown). In this manner the data from lower significant TALU is provided for next higher
significant TALU till the last TALU (n) is executed. TALU (n) 121 may be last TALU having TRIT (n) TRIT input 122, function output 123 and data input from TRIT (n-1) 114.
The data 124 from TALU TRIT(n) may connected to next higher TALU TRIT (n+1) (not shown) and further may be used for processing of other functions of CPU. The
decoder 125 and add 1 carry circuit being common to all plurality of said TALU the operation of TALU 100 is unified and synchronous.
Sheet 2 of 9: Figure-2 shows (140) the internal circuit of a general TALU (n) 140 in details. It comprises input TRIT port 925, two TRIT An 661 and Bn 663, OPCODE input
port 926 for function select decoder (2X9) 900 having two TRIT So 911 and SI 912, decoder bus 900A for decoder 900, input port for parity/i 661, parity^ 663, input port
for Carry (Cin) 658, input port 479 for All InclusiveTAND, input port 499 for All Inclusive TOR, output port for parityA 668, parityB 699, output port 479 for carry out (C2) ,
output port 499 forAll Inclusive TAND 480 output, output port 659 for All Inclusive TOR 460 , Multiplexed TALU function port F01201 for functions Arithmetic Output Cn+
(A+B, A-B, B-A)„ XTOR, TAND, TOR, All inclusive TAND, All Inclusive, OR; and TALU function port F02202 for outputs CARRY, Comparator Output (A=B, A>B, A<B), TNAND,
TNOR,All Inclusive, All Inclusive TNOR. The said TALU circuit comprises a function select decoder 900 having two control-inputs (OPCODE) and nine decoded output bus
900. The control input may be assigned following operational logic: Table- 1
Control input TRIT SO (91 1) and SI (912) referred to as S (SOSl) means when 91 1= level ! and 912=level 2 means OPCODE S 1.2 and referred to as SI 2; for S22 a
mathematical operation CARRY in+ (SUM (A+B) is enabled thence input TRIT An, Bn connected means multiplexed to Full Adder 922, SUM output multiplexed to F01 and-
CARRY 650multiplexed to F02. When input is OPCODE S21 , (SUM (A-B) +carry) while A>B, mathematical operation is enabled and input TRIT An is multiplexed to Full
Adder 922 and Bn is multiplexed through TNOT gate 350to 922 however, only in TALU of lowest significant trit, add 1 carry gate 360 is multiplexed to full adder 922, SUM
output multiplexed to F01 and CARRY 650 is multiplexed to F02. When input is OPCODE S20, GARRY in + SUM (B-A) mathematical operation is enabled and input TRIT Bn
is multiplexed to Full Adder 922 and An is multiplexed to 922 through TNOT gate 350 however, only in TALU of lowest significant trit add 1 carry gate360 is multiplexed to
full adder 922, SUM output multiplexed to FOl and CARRY 650 is multiplexed to F02. When input is OPCODE SI 2, XTOR Gate 600 enabled and multiplexed to 661& 663
and output multiplexed to FOl and comparator 400 is enabled and multiplexed to 661&663, output multiplexed to F02. When input is OPCODE SI 1, TAND gate 142
enabled and multiplexed to 661 & 663, and output multiplexed to FOl and to TNOT gate 350 to get TNAND, and output multiplexed to F02. When input is OPCODE S02
TOR gate 440 enabled and multiplexed to 661&663, and output multiplexed to FOl and further connected through TNOT gate 350 to execute TNOR logic and said gate
output multiplexed to F02. When input is OPCODE SOI first input TOR gate 460 enabled and multiplexed to input 661, 663 and the output from first TAND gate 480 and
479 from prior TALU stage multiplexed to second TOR gate to get All Inclusive TOR function and output multiplexed to FOl and output further multiplexed to TNOT gate
350 to get All Inclusive TNOR and multiplexed to F02.
Sheet 3 of 9: As shown in figure-3 (150), a transmission gate (TG) in all the figures described hereinafter, showing a prior art comprising an enhancement complimentary
MOSFET or hereinafter simply referred to ECMOS, all substrate p- ECMOS transistor may be connected to the highest level positive circuit supply or to the gate of n-
ECMOS transistor, and substrate n- ECMOS transistor may be connected to the lowest level or negative circuit supply or gate of p- ECMOS transistor and as shown in the
schematic diagram figure-3 (150),
and figure-4, a transmission gate (TG), a prior art, is formed by connecting source 14 of p-ECMOS 1 1 to drain 19 of n-ECMOS 18 to form a first terminal 25, hereinafter
referred to as P, similarly drain 12 of p-EMOS 1 1 connected to source 17 of n-ECMOS 18 transistor to form a common terminal 15, to form a second terminal hereinafter
referred to as N. The gate terminal 10 of p- ECMOS 11 hereinafter referred to as negative gate (Gn) and gate terminal 20 of n-EC OS 18 to form a pair of control terminals
to control the resistance of the said
'
TG such that when gate terminal 20, hereinafter referred to as positive gate (Gp), is more positive than Gn means m'ore than threshold voltage (being lower than +V) Gn,
TG goes into low resistance mode means ON state whereas, when gate terminal voltage Gn>Gp is more positive than threshold voltage or when Gn=Gp, TG goes into high
resistance mode means OFF state. Figure-4 depicts such .configuration of prior art comprising p-E OS and n-EMOS hereinafter referred to as TG and lowest voltage is
denoted by level 0 supply, mid voltage is denoted by level 1 supply, and highest voltage is denoted by level 2 supply.
Figure-5 (360) comprises an add one carry gate circuit where TG361 and TG363 are in parallel and connected to series combination of
'
TG364 and TG362. TG361 's P connected to 302, Gp to Decoder (900) output 908, Gn to 301 (IV) and N to TG364 and TG363; TG363's P connected to 301, Gp to 907, Gn
to 301 and N to P of TG364 and to output 910; TG364's P to TG361, Gp to 301, Gn to 907 and N to TG362; TG362's P to TG364, Gp to 301, Gn to 908 and N to 300. When
decoder 908 bus is level 2, only TG361 is, ON and connects bus 301 (I V) to output 910; when decoder 907 bus is level 2, only TG363 is ON and connects bus 301 (I V) to
https://patents.google.com/patent/WO2016199157A1/en
7/142/17/26, 11:04 AM
WO2016199157A1 - Ternary arithmetic and logic unit (alu) and ternary logic circuits - Google Patents
output 910; and when 908 and 907 are at level 0, TG361, TG363 are OFF while TG364 and TG362 are ON and connects 300 (0V) to output 910. The said gate is enabled
when the OPCODE command is either (A-B) or (B-A) functions, then 1 is added to 2's compliment to get 3's compliment.
Figure 6 (350) shows TNOT gate, or may' be called zero sequence circuit, comprises input TRIT661. TG354's P connected to 300 (0V), Gp to 661, Gn to 301 (I V), and N to
output 409; TG353's P connected to 301 (IV), Gn to 661, Gp to 301 (I V), and N to output 409; TG351 andnTG352 are in series, TG351 's P connected to 301 (I V), Gn to
661, Gp to 302 (2V), and N to TG352; TG352's P connected to TG351, Gn to 661, Gp to 300 (0V), and N to output 409. When 661at level 2, only TG354 conducts and
connects 300 (0V) to 409; When 661at level 0, only TG353 conducts and connects 302 (2V) to 409; When 661at level 1 , only TG351 and TG352 conduct and connects
301 to 409; thus TNOT truth table 2 is realized.
Table-2
Figure 7 shows CCW GATE 370, or may be called negative sequence circuit, comprises input TRIT 661. TG374's P connected to 300 (0V), Gp to 661, Gn to 301 (IV), and N
to output 379; TG373's P connected to 301 (I V), Gn to 661, Gp to 301 (IV), and N to output 379; TG371 and TG372 are in series, TG371 's P connected to 302 (2V), Gn to
661, Gp to 302 (2V), and N to TG372; TG372's P connected to TG371, Gp to 661, Gn to 300 (0V), and N to output 379. When 661 is at level 2, only TG374 conducts and
connects 300 (0V) to 409; When 661is at level 0, only TG373 conducts and connects 301 (IV) to 409; When 661at level 1 , only TG37I and TG372 conduct and connects
302 to 409; thus CCW gate truth table 2 is realized.
Figure 8 shows CW GATE 380, or may be called positive sequence circuit, comprises input TRIT 661. TG384's P connected to 301 (0V), Gp to 661, Gn to 302 (2V), and N to
output 489; TG383's P connected to 302 (2V), Gn to 661, Gp to 301 (IV), and N to output 489; TG381 and TG382 are in series, TG381 's P connected to 300 (0V), Gn to 661,
Gp to 302 (2V), and N to TG382; TG382's P connected to TG381 , Gp to 661, Gn to 301 (I V), and N to output 489. When 661 is at level 2, only TG384 conducts and
connects 301 (IV) to- 409; When 661 at level 0, only TG383 conducts and connects 302 (2V) to 489; When 661 =level 1, only TG381 and TG382 conduct and connects 300
to 409; thus CCW gate truth table 2 is realized.
Sheet 4 of 9: Figure-9 (420) shows a 2 input T IT TAND logic gate having first TRIT (A).661, (B) 663, supply (level 0) 300, (level 1) 301, (level 2) 302 and TG461 's P
connected to 301, Gn to 661, Gp to 302, and N to output 429; TG462's P connected to 301, Gp to 301, Gn to 601, and N to TG463; TG463 connected in series with TG6464,
TG463's Gn connected to 300, Gp to 661, N to TG464; TG464 Gn connected to 300, Gp connected to 663 and N connected to output 429; TG4645 and TG466 are in series;
TG465's P connected 302, Gp to 661, Gn to 301, and N to TG466; TG466's P connected TG465, Gp to 663, Gn to 301, and N to output 429; TG467, TG468 are in parallel;
TG467's P connected to 300, Gp to 301, Gn to 661 and N to output 429; TG468's P connected to 300, Gn connected to 663, Gp connected to 301, N connected to output
429.When TRIT 2(663) is , level 0 TG468 is ON, and/or if TRIT 1 (661) is level 0; TG467 is ON and 300 (0V) connected to output 429 whereas other TG are OFF; when 661
is level 2 and only when 663 is level 2 then TG465 and TG466 conduct and 302 connected to output 429 whereas other TG are OFF; when 661 is level 1 and only when
663 is level 1 then TG461 , TG462, TG463 and TG464 conduct and 301 is connected to output 429, whereas other TG are OFF and in this manner TAND logic as shown in
Table-3 is realized.
Table- 3
2 input T IT TAND gate
Sheet 4 of 9: Figure-10 (450) shows a 2 input TRIT TNAND logic gate having first TRIT (A) 661, second TRIT (B) 663, supply (level 0) 300, (level 1) 301, (level 2) 302 and
TG451's P connected to 301, Gn to 661, Gp to 302, and N to output 459; TG452's P connected to 301, Gp to 301, Gn to 601, and N to TG453; TG453 connected in series
with TG6454, TG453's Gn connected to 300, Gp to 661, N to TG454; TG454 Gn connected to 300, Gp connected to 663 and N connected to output 459; TG455 and TG456
are in series; TG455,'s P connected 300, Gp to 661, Gn to 301, and N to TG456; TG456's P connected TG455, Gp to 663, Gn to 301, and N to output 459; TG457, TG458 are
in parallel; TG457's P connected to 302, Gp to 301, Gn to 661 and N to output 459; TG458's P connected to 302, Gn connected to 663, Gp connected to 301, N connected
to output 459. When TRIT 2(663) is level 0 TG458 is ON, and/or if TRIT 1 (661) is level 0; TG457 is ON and 302 (2V) connected to output 459 whereas other TG are OFF;
when 661 is level 2 and only when 663 is level 2 then TG455 and TG456 conduct and 300 (0V) connected to output 459 whereas other TG are OFF; when 661 is level" 1
and only when 663 is level 1 then TG451, TG452, TG453 and TG454 conduct and 301 is connected to output 459, whereas other TG are OFF and in this manner TNAND
logic as shown in Table-4 is realized. Table- 4
2 input TRT TNAND sate
Figure-11 (440) shows a 2 input TRIT TOR logic gate having TRIT (A) 661 , (B) 663, supply (0V) 300, (IV) 301; (2V) 302 and TG488's P connected to 302, Gp to 663, Gn to
301, and N to output 449; TG487's P connected to 302, Gn to 301, Gp to 601, and N to 449; TG485 and TG486 are in series; TG485's P connected 300, Gn to 661 , Gp to
https://patents.google.com/patent/WO2016199157A1/en
8/142/17/26, 11:04 AM
WO2016199157A1 - Ternary arithmetic and logic unit (alu) and ternary logic circuits - Google Patents
'
301 , and N to TG486; TG486's P connected TG485, Gn to 663, Gp to 301, and N to output 449; TG481, TG482 are in parallel and TG483 and TG484 are in series; TG481 's P
connected to 301, Gp to 663, Gn to 300and N to TG483; TG482's P-connected to' 301, Gp to 661,Gn to 300 and N to TG483; TG483's P connected to TG481, Gp to 302, Gn
to 663, and N to TG484; TG484's P connected to TG483, Gp to 302, Gn to 661, and N to output 449. When TRIT 2(663) is level 2 thenTG487 is ON, and/or if TRIT 1 (661) is
level 2; TG488 is ON and 302 (2V) connected to output 449 while other TG are OFF; when 661 is level 0 and only when 663 is level 0 then TG485 and TG486 are ON and
300 connected to output 449 while other TG are OFF; when 661 is level 1 and only when 663 is level 1 then TG481, TG482, TG483 and TG484 conduct and 301 connected
to- output 449, while other TG are OFF and in this manner TOR logic as shown in Table-5 is realized. Table- 5
2 input TRI TOR gate
Figure-12 (430) shows a 2 input TRIT TNOR logic gate having TRIT (A) 661 , (B) 663, supply (0V) 300, (IV) 301, (2V) 302 and TG338's P connected to 302, Gp to 663, Gn to
301, and N to output 439; TG337's P connected to 300, Gn to 301, Gp to 601, and N to 339; TG335 and TG336 are in series; TG335's P connected 302, Gn to 661 , Gp to
301, and N to TG336; TG336's P connected TG335, Gn to 663, Gp to 301, and N to output 339; TG331, TG332 are in parallel and TG333 and TG334 are in series; TG331 's P
connected to 301, Gp to 663,- Gn to 300 and N to TG333; TG332's P connected to 301, Gp to 663,Gn to 300 and N to TG333; TG333's P connected to TG332, Gp to 302, Gn
to 663, and N to TG334; TG334's P connected to TG333,.Gp to 302, Gn to 661, and N to output 339. When TRIT 2(663) is level 2 thenTG337 is ON, and/or if TRIT 1 (661) is
level 2; TG338 is ON and 302 (2V) connected to output 339 while other TG are OFF; when 661 is level 0 and only when 663 is level 0 then TG335 and TG336 are O and 300
connected to output 339 while other TG are OFF; when 661 is level 1 and only when 663 is level 1 then TG331, TG332, TG333 and TG334 are ON and 301 connected to
output 339, while other TG are OFF and in this manner TNOR logic as shown in Table-,6 is realized. Table- 6
2 input TRIT TNOR gate
Sheet 5 of 9: Figure-13 (400) shows a 2 input TRIT COMPARATOR logic circuit having TRIT (A) 661, (B) 663, supply (0V) 300, (IV) 301, (2V) 302 and TG409's P connected
to 302, Gn to 661, Gp to 663, and N to output 419 and similarly TG410's P connected to 301, Gn to 663, Gp to 661, and N to output 419 and TG405's P connected to 300,
Gn to 663, Gp to 301, and N in series with TG407, TG407's P connected to TG405, Gn to 661, Gp to 301, and N to 419; and TG406's P connected to 300, Gp to 663, Gn to
301, and N in series with TG408, TG408's P connected to TG406, Gp to 661, Gn to 301, and N to 419, and further TG401, TG402, TG403, and TG404 are connected in series
respectively, TG401 's P connected to 300, Gp to 302, Gn to 661, and N-to TG402, TG402's P connected to TG401, Gp to 302, Gn to 663, and N to TG403 and TG403's P
connected to TG402, Gp to 661, Gn to 300, and N to TG404 and TG404's P to TG403, Gp to 663,· Gn to 300, and N to 419. When TO 1 (661) > T02 (663), TG409 becomes
on and connects 302 to output 419, similarly when T01 (663) > T02 (661), TG409 becomes on and connects 301 to output 419, and when f01(661)=T02=2 then TG406
and TG408 become ON, and being in series connects 300 to output 419 while remaining circuit segments are OFF and when TOl(661)=TO2=0 then TG405 and TG407
become ON, and being in series connects 300 to output 419 while remaining circuit segments are OFF, whereas when T01 (661)=T02=1 then TG401 and TG402, TG403
and TG404 become ON, and being in series connects bus 300 to output 419 while remaining circuit segments are OFF. In this manner TRUTH Table 7 is realized.
Table- 7
2 input TRl Comparator
Figure- 14 (600) shows a 2 input TRIT XTOR logic gate having TRIT (A) 661, (B) 663, supply (0V) 300, (IV) 301, (2V) 302 and TG613's P connected to 302, Gn to 661, Gp to
301, and N .in series with TG614; TG613 and TG612 are in parallel; TG612's P connected to 302, Gp to 661, Gn to 601, and in series with TG614; and TG614's P connected
toTG612 & TG613, TG614's Gn to 663, Gp to 661, and N to output 619. Similarly TG610's P connected to 301, Gn to 663, Gp to 302, and N in series with TG61 1 ; TG609
and TG610 are in parallel; TG609's P connected to 302, Gp to 663, Gn to 301, and N in series with TG61 1 ; and TG61 l 's P connected toTG609 & TG610; TG61 l 's Gp to
663, Gn to 661, and N to output 619; and TG605's P connected to 300, Gn to 663, Gp to 301, and N in series with TG607, TG607's P connected to TG605, Gn to 661, Gp to
301, and N to output 619, and TG606's P connected to 300, Gp to 663, Gn to 301, and N .in series with TG608, TG608's P connected to TG606, Gp to 661, Gn to 301, and N
to 619, and further TG601, TG602, TG603, and TG604 are connected in series respectively, TG601 's P connected to 300, Gp to 302, Gn to 661, and N to TG602, TG602's P
connected to TG601, Gp to 302, Gn to 663, and N to TG603 and TG603's P connected to TG602, Gp to 661, Gn to 300, ' and N to TG604 and TG604's M to TG603, Gp to
663, Gn to 300, and N to 619. When T01(663) > T02 (661 ), TG6T1 becomes ON and when T0663=l then TG609 is ON and connects 301 (IV) through TG611 to output 619,
in the similar manner T0661=2 then TG610 is ON and connects 302 (2V) through TG614 to output 619; likewise when TO 1(661) > T02 (663), TG612 becomes ON and
when T0661=l then TG613 is on and connects 301 (I V) through TG614 to output 619, in the similar manner T0661=2 then TG612 is ON and connects 302 (2V) through
TG614 to output 619; when T01(661)=T02=2 then TG606 and TG608 become ON, and being in series connects 300 to output 419 while remaining circuit segments are
OFF and when TOl(661)=TO2=0 then TG605 and TG607 become ON, and being in series connects bus 300 to output 419 while remaining circuit segments are OFF,
https://patents.google.com/patent/WO2016199157A1/en
9/142/17/26, 11:04 AM
WO2016199157A1 - Ternary arithmetic and logic unit (alu) and ternary logic circuits - Google Patents
whereas when T01 (661)=T02=1 then TG601 and TG602, TG603 and TG604 become ON, and being in series connects bus 300 to output 419 while remaining circuit
segments are OFF. In this manner TRUTH Table-8 is realized.
Table- 8
2 Input TR1T XTOR gate
Figure- 15 (900) comprises a 2 input TRIT Decoder logic gate having TRIT (So) 991, (SI) 912 as OPCODE control command from CPU to initiate various functions of the
said plurality of ALU I/O busand referred to as 2X9 Decoder; there are 9 decoded outputs available from the said control OPCODE. The said circuit is divided in to 9
separate circuits to give level 2 output respectively for each combination of So and SI TRIT. For of ease of understanding the circuit operation an input code XY means
So= level X (0 or 1 or 2) and Sl= level Y (0 or 1 or 2). The said circuit further comprises supply (0V) 3Q0, (I V) 301, (2V) 302 and output Bus 901 through 909. Circuit
segment 00 means 912 at level 0 and 911 at level 0, comprises TG71 Γ in parallel with TG712, connected to output 901 and to series combination of TG713 and TG714,
TG71 l's N connected to 300(0V), Gp to 911 , Gn to 300 and P to TG713; TG712's N connected to 300(0V), Gp to 912, Gn to 300 and P to TG713; TG713's N connected to
TG712 and output 901, Gn to 911, Gp to 301 and P to TG714; TG714's N connected to TG713, Gn to 912, Gp to 301 and P to 302 (2V). When OPCODE is 00, TG713 and
TG714 are ON and connects 302 to 901, while TG711 , TG712 are OFF however, for other OPCODEs at least one of TG71 1 , TG712 is ON and connects 902 to
300(0V).Circuit segment 01 means 912 at level 0 and 911 at level 1, comprises TG721 , TG722, and TG723are in parallel and in series with series combination of TG724,
TG725, and TG726; TG721 ,TG722,and TG723's N are connected to 300(0V); TG721 's Gn to 911, Gp to 301 and P to TG724 and output 902; TG722's Gp to 911, Gn to 301
and P to TG724 and output 902;TG722's Gn to 911, Gp to 301 and P to TG724 and output 902; TG723's Gp to 911, Gn to 301 and P to TG724 and output 902;TG723's Gn to
912, Gp to 300 and P to TG724 and output 902; TG724's N connected to TG721 , Gn to 912, Gp to 301 and P to TG725; TG725's N connected to TG724, Gn to 911, Gp to
302 and P to TG726; TG726's P connected to TG725, Gp to 911, Gn to 300 and P to 302 (2V). For OPCOFE 01 TG724, TG725, and TG726 are ON and connects output 902
to 302(2 V) and TG721 , TG722, and TG723 are OFF however, for other OPCODES at least one of TG721, TG722, TG723 is ON and connects 902 to 300(0V). Circuit
segment 02 means 912 at level 0 and 911 at level 2, comprises TG731 in parallel with TG732, connected to output 903 and to series combination of TG733 and TG734,
TG731's N connected to 300(0 V), Gn to 911, Gp to ' 302 and P to TG733; TG732's N connected to 300(0V), Gp to 912, Gn to 300 and P to output 903 and TG733' P is
connected to TG732, Gn to 911, Gp to 301 and P to TG734; TG734's N connected to TG733, Gn to 911, Gp to 301 and P to 302 (2V). When OPCODE is 02, TG733 and
TG734 are ON and connects 302 to 903, while TG731, TG732 are OFF however, for other OPCODES at least one of TG731, TG732 is ON and connects 902 to 300(0 V).
Circuit segment 10 means 912 at level 1 and 911 at level 0, comprises TG741 , TG742, and TG743 are in parallel and in series with series combination of TG744, TG745,
and TG746; TG741,TG742,and TG743's N are connected to 300(0V); TG741 's Gp to 91,1, Gn to 300 and P to TG744 and output 904; TG742's Gn to 912, Gp to 301 and P to
TG744 and output 904;TG743's Gp to 912, Gn to 301 and P to TG744 and output 904; TG7445s N connected to TG741, Gn.to 912, Gp to 301 and P to TG745; TG745's N
connected to TG744, Gp to 912, Gn to 300 and P to TG746; TG746's P connected to TG745, Gn to 911, Gp to 301 and P to 302 (2V). For OPCOFE 10, TG744, TG745, and
TG746 are ON and connects output 902 to 302(2 V) while TG741, TG742, and TG743 are OFF however, for other OPCODES at least one of TG741 , TG742, TG743 is ON
and connects 904 to 300(0V). Circuit segment 11 means 912 at ievei 1 and 911 at level 1, , comprises TG751, TG752, TG753 and TG754 are in parallel and in series with
series combination of TG755, TG756, TG757 and TG758; TG751,TG752, TG753and TG754's N are connected to 300(0V); TG751 's Gn to 911, Gp to 301 and P to TG755
and output 905; TG752's Gp to 911, Gn to 301 and P to TG755 and output 905; TG753's Gn to 912, Gp to 301 and P to TG754 and output ' 905; TG754's Gp to 912, Gn to
301 and P to TG754 and output 905; TG755's N connected to TG751 , Gn to 912, Gp to 302 and P to TG756; TG756's N connected to TG755, Gp to 912, Gn to 300 and P to
TG757; TG757's P connected to TG756, Gn to 911, Gp to 302 and P to TG758; TG756's P connected to TG755, Gp to 911, Gn to 300 and P to 302 , (2V): For OPCOFE 11,
TG755, TG756, TG757, and TG758 are ON and connects output 905 to 302(2V) while TG751 , TG752,TG753 and TG754 are OFF however, for other OPCODES at least one
of TG751 , TG752, TG753,TG754 is ON and connects 905 to 300(0V). Circuit segment 12 means 912 at level 1 and 911 at level 2, comprises TG761, TG762, and TG763
are in parallel and in series with series combination of TG764, TG765, and TG766; TG761 ,TG762,and TG763's N are connected to 300(0 V); TG761 's Gn to 911, Gp to 302
and P to TG764 and output 906; TG762's Gn to 912, Gp to 301 and P to TG764 and output 906;TG763's Gp to 912, Gn to 301 and P to TG764 and output 906; TG764's N
connected to TG761 , Gp to 911, Gn to 301 and P to , TG765; TG765's N connected to TG764, Gn to 912, Gp to 302 and P to TG766; TG766's P connected to TG765, Gp to
912, Gn to 301 and P to 302 (2V). For OPCOFE 12, TG764, TG765, and TG766 are ON and connects output 902 to 302(2 V) while TG761, TG762, and TG763 are OFF
however, for other OPCODES at least one of TG761, TG762, TG763 is ON and connects 906 to 300(0V). Circuit segment 20 means 912 at level 2 and 911 at level 0,
comprises TG771 in parallel with TG772, connected to output 907 and to series combination of TG773 and TG774; TG771 's N connected to 300(0V), Gp to 911, Gn to 300
and P to TG773; TG772's N connected to 300(0V), Gn to 912, Gp to ' 302 and P to output 907 and TG773' P is connected to TG772, Gn to
911, Gp to 301 and P to TG774; TG774's N connected to TG773, Gp to
912, Gn to 301 and P to 302 (2V). When OPCODE is 20, TG773 and TG774 are ON and connects 302 to 907, while TG771 , TG772 are OFF however, for other OPCODES at
least one of TG771, TG772 is ON and connects 907 to 300(0V). Circuit segment 21 means 912 at level 2 and 911 at level 1 , comprises TG781, TG782, and TG783 are in
parallel and in series with series combination of TG784, TG785, and TG786; TG781 ,TG782,and TG783's N are connected to 300(0V); TG781's Gn to 911, Gp to 302 and P
to TG784 and output 908; TG782's Gn to 912, Gp to 301 and P to XG784 and output 908;TG783's Gp to 912, Gn to
'
302 and P to TG784 and output 908; TG784's N connected to TG781, Gp to 912, Gn to 301 and P to TG785; TG785's N connected to TG784, On to 911, Gp to 302 and P to
TG786; TG786's P connected to TG785, Gp to 911, Gn to 300 and P to 302 (2V). For OPCOFE 21, TG784, TG785, and TG786 are ON and connect output 908 to 302(2V)
while TG781 , TG782, and TG783 are OFF however, for other OPCODES at least one of TG781, TG782, TG783 is ON and connects 908 to 300(0V). Circuit segment 22
means 912 at level 2 and 911 at level 2, comprises TG791 in parallel with TG792, connected to output 909 and to series combination of TG793 and TG794; TG791's N
connected to 300(0V), Gn to 911, Gp to 302 and P to TG793; TG792's N connected
'
to 300(0V), Gn to 912, Gp to 302 and P to output 909 and TG793' P is connected to TG792, Gp to 912, Gn to 301 and P to TG794; TG794's N connected to TG793, Gp to
911, Gn to 301 and P to 302 (2V). When OPCODE is 22, TG793 and TG794 are ON, connects 302 to 909, while TG791, TG792 are OFF however, for other OPCODES at least
one of TG791, TG792 is ON and connects 909 to 300(0V). In this manner Truth Table- 1 is realized.
Sheet 6 of 9: Figure-16 comprises a ternary adder means first.adder (SI) circuit comprises 2 input TR1T (A) 661 and (B) 663 and having three
■ segments comprising 663 at level 2 means first segment, 663 at level 1 means second segment, and 663 at level 0 means third segment; the first segment comprises
TG624, and parallel combination of TG621, TG625, and TG622 in series with TG623; where TG624's Gp to 663,Gn to 301 (IV), P connected to output 639, N connected
to"TG62l; TG621's P to TG624, Gn to 661, Gp to 302, N to 300(0 V); TG623's P to TG624, Gn to 661, Gp to 302, N to TG622; TG622's P to TG623, Gp to 661, Gn to 302,and N
https://patents.google.com/patent/WO2016199157A1/en
10/142/17/26, 11:04 AM
WO2016199157A1 - Ternary arithmetic and logic unit (alu) and ternary logic circuits - Google Patents
to 301(1 V); TG625's P to TG624, Gp to 661, Gn to 302,and N to 302(2V);the second segment comprises TG629 and parallel combination of TG626, TG630 and TG628 in
series with TG627; where TG629's Gn to 663,Gp to 301 (IV), P connected to output 639, N
■ connected to TG626; TG626's P to TG624, Gn to 661, Gp to 302, N to 300(0V); TG628's P to TG627, Gn to 661, .Gp to 302, N to TG627; TG627's P to 301(1 V), Gp to 661,
Gn to 300,and N to 301(1 V); TG'630'S P to TG629, Gp to 661, Gn to 302,and N to 302(2 V); the third segment comprises TG635, TG634 in series, and parallel combination
of TG631 , TG636 and TG633 in series with TG632; where TG635's Gn to 663,Gp to 302 (2V), P connected to output 639, N connected to TG634; TG634's Gp to 663,Gn to
300 (0V), N connected to TG631 ; TG631 's P to TG634, Gn to 661, Gp to 301, N to 300(0V); TG636's P to TG634, Gp to 661, Gn to 301, N to 302; TG633's P toTG634, Gn to
661, Gp to 302,and N to TG632; TG632's P connected to TG633, Gp to 661, Gn to
■ 300, and N to 301(1 V). Output of Adder 1 (Half Adder) for input TRIT A (661 ) and (B) 663 at 639 is as shown in Table-9 is realized.
Table- 9
INPUT A
CQ
HD
I0
2 input TRI ADDER
Figure- 17 comprises a ternary adder 2 (S2) means executes sum of first adder circuit and external carry in (Cn), comprises a TRIT 639 and (Cn) 658 and having two
segments comprising (Cn) 658 at level 0 means first segment and 658 at level 1 means second segment; the first segment TG641S P connected to output 649,Gp to 301,
Gn to 658 and N to 649; second segment comprises TG645 in series with parallel combination of TG642, TG646 and TG644 in series with TG643, TG645's N connected to
TG642, Gn to 300, Gp to 654 and N to output 649, TG642's P connected to TG645, Gn to 639, Gp to 301 and N to 301 (I V); TG646's P connected to TG645, Gp to 639, Gn
to 301 and N to 300 (0V); TG644's P connected to TG645, Gn to 639, G to 301 and N toTG643; TG643's P connected to TG644, Gp to 639, Gn to 300 and N to302 (2 V);
Output of Full Adder for input TRIT SI (639) and Cn (658) at 649 is as shown in Table-10, 1 1, and 12 are realized.
Table- 10
Table- 11
CARRY GENERATED FROM ADDER1
Table- 12
2 Input CARRY 2
Figure-18 comprises a final carry gate circuit having input Cn (658) from Carry Input, SI (639), TRIT 661 and TRIT 663; the first segment outputs carry from half adder and
carry in and second segment outputs generated carry from TRIT 661 and 663; TG641's P connected to output 659,Gn to 300, Gp to 658 and N to TG651 ; TG651,s P
connected to TG652, Gn to 300, Gp to 639 and N to 301 ;second segment comprises parallel TG653 and TG656 in series with TG655, TG654; TG653's N connected to
output 659, Gn to 301, Gp to 663 and P to TG655; TG656's P connected to TG655, Gp to 661, Gn to 301 and N toTG655; , TG655's N connected'to TG656, Gp to 663, Gn to
300 and N to 301. Output of Full Carry output is as shown in Table—
Table- 13
https://patents.google.com/patent/WO2016199157A1/en
11/142/17/26, 11:04 AM
WO2016199157A1 - Ternary arithmetic and logic unit (alu) and ternary logic circuits - Google Patents
FINAL CARRY 2
Figure-19 shows the full adder with final carry 670 comprising first adder (SI) circuit 620, Second Adder (S2) circuit 640 and Final carry (C2) 650 with TRIT input 91 1, 913,
Carry In (Cn) and final sum output 649, final carry 659.
Figure-20A shows an even parity generator circuit (N) for Anth TRIT (An) where input comprised TRIT An 661 and parity generator circuit output from (N-l) TMT !t 663 and
output 668 is available for (N+l) parity generator. The parity generator circuit is identical to adderl (620) except for the said TRIT input as shown. Figure-20B is identical to
figure-20A except TRIT where operator A is replaced by B operator and output is available on 669.
Table- 14
EVEN PARITY GENERATOR FOR OPERAND
Sheet 7 of 9 and Sheet 8 of 9: Figiire-21 A and figure-21B show a typical internal circuit diagram of TALU being one stage of plurality of TALU as shown in figure- 1. It
comprises basic logic gates means circuit as described in terms of blocks in figure-2 (140). It comprises full adder with carry (670) figure- 16, add 1 carry (360) figure-5,
inverter means TNOT (350) figure-6, XTOR 600 figure-14, comparator 400 figure-13, TAND 420 figuere-9, TOR 440 figure-1 1, Parity 600 figure-20A & figure-20B, decoder
(2X9) 900 figure- 15. The least significant trit (LST) ALU circuit block is different than higher trit circuit blocks and it comprises additional function add J carry block
which may not be needed in higher trit TALU, further OPCODE decoder is common for plurality of ALU hence it may be associated with LST. Each TALU stage comprises
input port for inputting 2 TRIT denoted by An arid Bn where n may have values from 0 to the desired number, input port for OPCODE means 2 TRrT SO, SI, 2 output
multiplexed port 201 (F01), 202 (F02) for outputting provided. Supply voltage 300 (level 0 supply), 301 (level 1 supply), and 303(level 2 supply) are provided for the
functioning of various devices, circuits and gates. The said TALU block 150 shall be described with various OPCODE logic input. When S0=0, S1=0, 901 (DO) output, is
level 2, it executes NOP operation.
When S0=2, SI =2, decoder 909 output is' high to execute function (A+B) and it switches ON TGI 18, TG119.TG120, TGI 21, TG 27, TGI 25 and TG118, TG1 19 connect input
An, Bn respectively to full adder 105 whereas carry input from lower trit (n-1) 658 is directly connected to 105 and the output sum and carry thus obtained is connected
through TG127 to port F02, TG125 to FOlrespectively while carry 659 is available for further operation of the next trit (n+1). When S0=2, Sl = l, 908 output is high to
execute function is (A-B and A>B) and it switches ON TGI 16, TGI 17,TG124,TG125, TG128, TG126 and( add 1 carry360 to 105 only in case of AO, B0 means least
significant trit ALU) and TGI 16 connects input An to 105, and to have 3's complement and add 1 operation, Bn to TNOT 106 and through TG124 and TG125 to full adder
105 whereas carry input from lower trit (n-1) 658 is directly connected to 105 and the output sum and carry thus obtained is connected through TG I 28 to port F02, TGI
26 to FOl respectively while carry 659 is available for further operation of the next trit (n+1). When S0=2, S1=0, 907 output is high to execute function (B-A for B>A) and it
switches ON TGI 15, TG 1 12,TG 122,TG 123 TGI 12, TG I 1 1 and (add 1 carry 360 to 105 only in case of AO, B0 means least significant trit ALU) and TGI 22 connects
input Bn to 105, and to have 3's complement and add 1 operation, , An to ΤΝΌΤ 107 and through TGI 15 and TGI 12 to full adder 105 whereas carry input. from lower trit
(n-1) 658 is directly connected to 105 and the output sum and carry thus obtained is connected through TGI 12 to port F02, TGI 1 1 to FOl respectively while carry 659 is
available for further operation of the next trit (n+1). When S0=1 , SI =2, 906 output is high to execute functions (XTOR and Comparator) and it switches ON TGI 13, TGI 14,
TGI 32. TGI 13 and TGI 14 connect input An and Bn to XTOR gate 500 and its output is connected to F01 through TG 132, similarly TG 133 and TGI 13 connect input An
and Bn to Comparator gate 400 and its output is connected to F01 through TG 133. When S0=1 , Sl=l , 905 output is high to execute functions (TAND and TNAND gate)
and it switches ON TG137, TG139, TG141, TG143 whereas TG135 is already ON. TG137 and TG139 connect input An and Bn to TAND gate 144, and further connected to
first input of TAND gate 145 and second input through TG135 and said input is connected to 302 (2V) supply bus' and being high, does not have any effect on the output
146 of TOR 145 and the said outputl 46 is connected to F01 through TG143 and further to TNOT gate 147 to F02 through TG141. When S0=i; S1=0, 904 output is high to
execute functions All inclusive TAND and All inclusive TNAND gate, means such operation which includes prior stage output, means AO through An and B0 through Bn
and it switches ON TGI 36, TGI 38, TG 140, TG144, TG142 and switches of TG135. TG138 and TG140 connect input An and Bn to said TAND gate 144, and the output is
connected to second TAND gate 147. Second TAND gate 145 gate second input is connected the output of similar circuit from previous TRIT circuit through TG 136
whereas TG135 is switched OFF, hence the output 146 is the TAND logic of the said trit An and Bn as well as all lower trits and in this manner All inclusive TAND gate is
executed and the said output is multiplexed to Fol through TG 144 and further 146 is made available to next higher trit (n+1 ) operation on 479. Further the said output
146 is connected to ΤΝΌΤ gate 147 to realize All Inclusive TNAND gate operation and is multiplexed to F02 through TG I 42. When S0=0, S 1=2, 903 output is high to
execute functions (TOR and TNOR gate) and it switches ON TG 153, TG155, TG 162, TG196 whereas TGI 51 is already ON. TGI 53 and TGI 55 connect input An and Bn to
TOR gate 164, and gate 164 output is further connected to first input of TOR gate 165 and second input through TGI 51 and said input
■ is connected to 300 (0V) supply bus and being low, does not have any effect on the output 166 of TOR 165 and the said outputl46 is connected to FOl through TGI 43
and further to TNOT gate 147 to F02 through TG141. When S0=0, Sl=l , 902 output is high to execute functions INCLUSIVE TOR and All inclusive TNOR gate,' means such
operation which includes all lower significant trits means AO through An and BO through Bn and it switches ON TG 54, TGI 56, TGI 62, TGI 96, TGI 52 and switches OFF
TGI 35. TGI 54 and TGI 56 connect input An and Bn to said TOR gate 165, and its output is connected first input of second TOR gate 165. Second input of Second TAND
gate 145 is connected the output of similar circuit from previous TRIT circuit through TG152
■ whereas TGI 51 is switched OFF, hence the output 166 is the TAND logic of the said trit An and Bn as well as all lower trits and in this manner All Inclusive TAND gate is
realized and the said output is multiplexed to FOl through TG 162 and further 166 is made available for next higher trit (n+1) operation on 499. Further the said output 166
is connected to TNOT gate 167 to realize All Inclusive TNAND gate operation and is multiplexed to FOl through TG 195.The TALU circuit further comprises two EVEN
PARITY GENERATOR (PG) 130 and 131 for An and Bn TRIT respectively. It comprises Adder 1 (Half Adder) 130 having first input 661 from next lower TRIT (n-1) PG and
second input from An 661 and output 668 is made available for next trit
https://patents.google.com/patent/WO2016199157A1/en
12/142/17/26, 11:04 AM
WO2016199157A1 - Ternary arithmetic and logic unit (alu) and ternary logic circuits - Google Patents
■ (n+1) operation. In the same manner Half Adder 131 having first input 661 from next lower trit (n-1) PG and second input from Bn 661 and output 669 is made available
for next higher trit (n+1 ) PG operation. Further ALL ZERO may be detected by All Inclusive TOR gate out put on 499. Data OVERFLOW may be detected by Carry out put on
659.
Sheet 9 of 9: Figure-22 shows a combined circuit of TALU as shown in figure-21A and figure-21B to highlight novel connectivity of plurality of parallel TALU.
Additional advantages and modification will readily occur to those skilled in art. Therefore, the invention in its broader aspect is not limited to Specific details and
representative embodiments shown and described herein. Accordingly various modifications may be made without departing from the spirit or scope of the general
invention concept as defined by the appended claims and their equivalents.
Non-Patent Citations (1)
Title
A. P. DHANDE ET AL.: "Design And Implementation Of 2 Bit Ternary ALU Slice", 3RD INTERNATIONAL CONFERENCE: SCIENCES OF ELECTRONIC, TECHNOLOGIES OF
INFORMATION AND TELECOMMUNICATIONS, 17 March 2005 (2005-03-17), rch 17-21, 2005, TUNISIA, pages 1 - 11, XP055334631, Retrieved from the Internet
<URL:http://www.setit.rnu.tn/last_edition/setit2005/electronique/312.pdf.> *
* Cited by examiner, † Cited by third party
Cited By (4)
Publication numberPriority datePublication dateAssigneeTitle
RU2681702C1 *2018-06-142019-03-12Российская Федерация, от имени которой выступает ФОНД
ПЕРСПЕКТИВНЫХ ИССЛЕДОВАНИЙArithmetic-logic apparatus
and a method for converting
data using such device
US10545727B22018-01-082020-01-28International Business Machines CorporationArithmetic logic unit for
single-cycle fusion operations
RU2810609C1 *2023-07-122023-12-28Федеральное государственное бюджетное образовательное
учреждение высшего образования "Саратовский национальный
исследовательский государственный университет имени Н.Г.
Чернышевского"Sequential divider of trinity
integers
WO2025060996A1 *2023-09-182025-03-27华为技术有限公司Ternary logic gate circuit,
calculation circuit, chip, and
electronic device
Family To Family Citations
* Cited by examiner, † Cited by third party, ‡ Family to family citation
Similar Documents
PublicationPublication DateTitle
Saxena et al.2013Analysis of low power, area-efficient and high speed fast adder
Levi et al.2012High speed dual mode logic carry look ahead adder
Gladshtein2011Quantum-dot cellular automata serial decimal adder
Sarkar et al.2018Comparison of various adders and their VLSI implementation
WO2016199157A12016-12-15Ternary arithmetic and logic unit (alu) and ternary logic circuits
Sam et al.2023Design of low power pass transistor logic based adders for multiplier in 90nm cmos process
Janwadkar et al.2018Design and performance evaluation of hybrid full adder for extensive PDP reduction
CN111313890B2022-06-17High-performance approximate full adder gate-level unit
Degawa et al.2004A single-electron-transistor logic gate family for binary, multiple-valued and mixed-mode logic
Ajitha et al.2017An enhanced high-speed multi-digit BCD adder using quantum-dot cellular automata
KR20050100924A2005-10-20Arithmetic and logic unit using haff adder
Dattatraya et al.2013Modified Carry Select Adder using Binary Adder as a BEC-1
Dubey et al.2014Implementation Of an arithmetic logic using area efficient carry look-ahead adder
Venishetty et al.2021Design of power efficient, high-speed 4-bit comparator in UMC 180 nm technology
JP2004265204A2004-09-24Look-ahead circuit and adder circuit using the same
https://patents.google.com/patent/WO2016199157A1/en
13/142/17/26, 11:04 AM
WO2016199157A1 - Ternary arithmetic and logic unit (alu) and ternary logic circuits - Google Patents
Mishra et al.2011On the design of high-performance CMOS 1-bit full adder circuits
US20210019114A12021-01-21Configurable non-volatile arithmetic memory operators
JP7802253B12026-01-19Bidirectional logic element, arithmetic device, and arithmetic method
Chandrahash et al.2014Ripple Carry Adder Desig
Ilamathi et al.2021High-Speed And Area-Efficient 16, 64-Bit Digital Comparator
Meshram et al.2015Designed Implementation of Modified Area Efficient Enhanced Square Root Carry Select Adder
Amizhdhu et al.2018Comparative analysis of 32-bit CSLA based on CMOS and GDI logic
Au et al.2002A (4: 2) adder for unified GF (p) and GF (2 n) Galois field multipliers
Bhuvaneshwari et al.2023Low Power CMOS GDI Full-adder Design
Boda et al.2015Multiplexer-Based Design of Adders/Subtractors and Logic Gates for Low Power VLSI Applications
Priority And Related Applications
Applications Claiming Priority (2)
ApplicationFiling date
IN2258MU20152015-06-11
IN2258/MUM/20152015-06-11
Title
Legal Events
DateCodeTitleDescription
2017-01-25121Ep: the epo has been informed by wipo that ep was designated in this applicationRef document number: 15894861
Country of ref document: EP
Kind code of ref document: A1
2017-12-12NENPNon-entry into the national phaseRef country code: DE
2018-07-04122Ep: pct application non-entry in european phaseRef document number: 15894861
Country of ref document: EP
Kind code of ref document: A1
Data provided by IFI CLAIMS Patent Services
About
Send Feedback
https://patents.google.com/patent/WO2016199157A1/en
Public Datasets
Terms
Privacy Policy
Help
14/14
