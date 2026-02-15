Tekum: Balanced Ternary Tapered Precision
Real Arithmetic

arXiv:2512.10964v1 [cs.ET] 25 Nov 2025

Laslo Hunhold
Parallel and Distributed Systems Group
University of Cologne, Cologne, Germany
hunhold@uni-koeln.de

Abstract In light of recent hardware advances, it is striking that real
arithmetic in balanced ternary logic has received almost no attention in
the literature. This is particularly surprising given ternary logic’s promising properties, which could open new avenues for energy-efficient computing and offer novel strategies for overcoming the memory wall.
This paper revisits the concept of tapered precision arithmetic, as used in
posit and takum formats, and introduces a new scheme for balanced ternary logic: tekum arithmetic. Several fundamental design challenges are
addressed along the way. The proposed format is evaluated and shown to
exhibit highly promising characteristics. In many respects, it outperforms
both posits and takums. As ternary hardware matures, this work represents a crucial step toward unlocking the full potential of real-number
computation in ternary systems, laying the groundwork for a new class
of number formats designed from the ground up for a new category of
next-generation hardware.

Keywords: tekum arithmetic · balanced ternary logic · tapered precision ·
real arithmetic · floating-point arithmetic · posit arithmetic · takum arithmetic

1

Introduction

Computer science is a comparatively young scientific discipline. The first programmable computers were constructed little more than eighty years ago, Zuse’s
Z3 in 1941 and the ENIAC by Mauchly and Eckert in 1946. These early machines were based on the binary system, which has since shaped the foundations
of computer science. The prevailing perception of computers is that, at their core,
they operate through states of ‘on’ or ‘off’. Decades of research and development
have refined and optimised the design of binary computers.
History, however, can narrow perspective. A lesser-known paradigm of computation is ternary logic. Instead of two states, ternary logic uses three; instead
of binary digits (bits), one has ternary digits (trits), where a single trit contains
log2 (3) ≈ 1.58 bits of information. The motivation for considering such systems
lies in the concept of radix economy, the cost of representing a positive integer

2

L. Hunhold

n ∈ N1 in a given base b ∈ R+ . This cost is defined as C(b, n) := ⌊logb (n) + 1⌋ · b,
namely the number of digits required to represent n in base b, multiplied by
the base b itself [11]. Intuitively, larger bases produce shorter representations
but incur greater hardware complexity, whereas smaller bases ease implementation but require more digits. It can be shown analytically that base e ≈ 2.718
minimises cost asymptotically, with 3 being the nearest integer. If one assumes
that base size correlates with hardware complexity, ternary arithmetic therefore
offers the most balanced trade-off between circuit complexity and representational efficiency. By contrast, binary arithmetic simplifies circuit design, but at
the expense of higher representational cost and greater communication overhead.
Hardware investigations have compared binary and ternary implementations.
While ternary circuits achieve comparable computational speed, they typically
require more logic; for example, a ternary adder needs approximately 62 % more
circuitry, even accounting for the higher information density of trits [15]. This
finding has often been cited as a reason to dismiss ternary logic. Yet, such dismissal warrants reconsideration in light of modern computing trends: the dominant bottleneck today is not raw computational speed, but memory bandwidth
[2, 5]. Under these conditions, ternary logic acquires renewed relevance. Recent
advances, such as ternary deep neural networks and carbon nanotube transistors,
which operative natively in ternary, further strengthen its value proposition.
The full potential of ternary computation emerges when digits are chosen
from {−1, 0, 1} rather than {0, 1, 2}. This balanced ternary system is unique to
odd bases and may appear unfamiliar, given the dominance of even bases such
as 2, 8, 10, 16, and 64, or historically base 60. In balanced ternary, the digit
−1 is commonly denoted by a special symbol, here written as T. For instance, 2
is represented as 1T (1 · 3 + (−1) · 1), and −4 as TT ((−1) · 3 + (−1) · 1). This
representation has several appealing properties: integers are inherently signed,
and perfectly symmetric around zero, without unlike two’s complement binary
integers. Negation is achieved simply by inverting digits, and rounding is the
same as truncation, eliminating the need for carries. Knuth has described it as
‘perhaps the prettiest number system of all’ [16, p. 207].
Balanced ternary has been studied mainly in the context of integers. Realnumber representations, such as floating-point formats, remain surprisingly underexplored. One might expect that properties such as rounding by truncation
could mitigate issues inherent in binary floating-point arithmetic, where carries
complicate rounding. Yet the literature is sparse. The only notable proposal is
ternary27 by O’Hare [21], which is heavily inspired by IEEE 754. Although
it achieves a favourable dynamic range, its design is inefficient, wasting many
representations. This inefficiency is more detrimental in ternary than in binary
arithmetic, as each trit carries more information than a bit. While the IEEE
854-1987 standard specifies radix-independent floating-point numbers, it does
not address balanced bases.
Given current hardware developments, it is undesirable for theoretical progress to lag behind practical advances. This paper therefore revisits balanced
ternary real arithmetic and makes the following contributions. After introducing

Tekum: Balanced Ternary Tapered Precision Arithmetic

3

the fundamentals of balanced ternary in Section 2, we identify key design challenges in Section 3 that up to the design of takums [12] were insurmountable. We
then propose a new balanced ternary number format, tekum, in Section 4, and
evaluate its properties in Section 5.1, before drawing conclusions in Section 6.

2

Balanced Ternary

In this section we introduce balanced ternary and all the tools necessary to
define and analyse the subsequently introduced tekum arithmetic. We follow a
formal approach given the unintuitiveness compared to standard binary logic.
Additionally, this paper is more or less an inaugural paper on balanced ternary
real arithmetic, and it’s helpful to suggest a notation for this nascent field.
Definition 1 (balanced ternary strings). Let n ∈ N0 . The set of n-trit baln
anced ternary strings is defined as Tn := {T, 0, 1} with T := −1 . By convention
Tn ∋ t := (tn−1 , . . . , t0 ) =: tn−1 · · · t0 .
The first thing we notice is that, compared to posits and takums, we denote
ternary strings with bold lowercase letters instead of uppercase letters. This is
more in line with the common notation for vectors in mathematics and computer
science.
Definition 2 (concatenation). Let m, n ∈ N0 , t ∈ Tm and u ∈ Tn . The
concatenation of t and u is defined as t +
+ u := (tm−1 , . . . , t0 , un−1 , . . . , u0 ) ∈
Tm+n .
This concatenation operator is distinct from the more relaxed, overloaded concatenation notation with parentheses.
Definition
3 (integer mapping). Let n ∈ N0 . The integer mapping intn : Tn →
 1 n
Pn−1
− 2 (3 − 1), . . . , 12 (3n − 1) is defined as intn (t) := i=0 ti 3i .
Unlike with two’s complement binary integers, there is no explicit sign bit. Instead the sign is indicated by the most significant non-zero trit, and there is
no concept of an unsigned integer in balanced ternary. The range of integer
values follows from the finite geometric series obtained with the extremal values intn (T . . . T) and intn (1 . . . 1), and is perfectly symmetric around zero (unlike
two’s complement integers).
Definition 4 (negation). Let n ∈ N0 and t ∈ Tn . The negation of t is defined
as −t := (−tn−1 , . . . , −t0 ).
By construction we can see that it holds intn (−t) = − intn (t), making it welldefined. The negation operation outlines another distinctive difference between
two’s complement binary and balanced ternary integers: Whereas to negate the
underlying integral value you need to negate all bits and add one with the former,
which is expensive in hardware due to the carry-chain, negation in balanced
ternary is a very cheap, entrywise operation.

4

L. Hunhold

Definition 5 (addition and subtraction). Let n ∈ N0 and t, u ∈ Tn . The
addition of t and u is defined with s := intn (t) + intn (u) as


1 n
1 n

s + 2 (3 + 1) s < − 2 (3 − 1)


1 n
1 n
t + u := intinv
(1)
n  s − 2 (3 + 1) s > 2 (3 − 1)  .


s
otherwise
The subtraction of t and u is defined as t − u := t + (−u).
Despite the complex appearance, the addition is merely defined here as a fixedsize operation, taking two n-trit inputs and yielding an n-trit output, discarding
any carries that might occur due to over- or underflow and using the inverse
integer mapping to obtain the ternary string. If carries should be taken into
account, the inputs need to be extended to n + 1-trit strings before the addition.
Especially notable is the definition of the subtraction: Given negation is so cheap,
you can define it in terms of the addition.
Definition 6 (modulus). Let n ∈ N0 and t ∈ Tn . The modulus of t is defined
as
(
−t intn (t) < 0
(2)
|t| :=
t
intn (t) ≥ 0.
With these definitions in place we can proceed with the derivation of the tekum
arithmetic.

3

The Three Filters

In this section, we derive the central contribution of this paper: a new ternary
real arithmetic. As outlined in the introduction, the current state of the art in
ternary real arithmetic is surprisingly underdeveloped. This may be attributed
in part to the relatively small number of arithmetic designers worldwide, as well
as the limited training and interest in ternary hardware to date. However, a
closer examination of recently established design criteria for number formats
reveals three possible consecutive filters that may have led previous researchers
to attempt, and ultimately abandon, the pursuit of a new format.
The term filter is borrowed from Robert Hanson’s notion of the ‘Great
Filter’, which refers to the fundamental developmental barriers a civilisation
must overcome, proposed to explain the (apparent) absence of advanced extraterrestrial life in the universe [9]. Here, we adapt the term ‘filter’ to describe
conceptual or technical barriers that have likely hindered the development of a
proper ternary real arithmetic. We outline and reflect on these filters throughout the derivation, highlighting how each is encountered and overcome in the
formulation of our format.
Fundamentally, the design of a real number format involves defining a mapping between discrete representations (in this case, trit strings) and a corresponding set of real values. This set is constructed as a subset of the real numbers R, often extended with additional non-number representations. The most

Tekum: Balanced Ternary Tapered Precision Arithmetic

5

∞

−1

NaR
1

0

Figure 1: A visualisation of the real wheel algebra with the customary positioning
of the bottom element NaR in the center as a ‘wheel hub’ that distinguishes it
from the projectively extended real numbers.

common such extension is the affinely extended real numbers, R ∪ {−∞, +∞}.
A less common alternative is the projectively extended real numbers, R ∪ {∞},
where division by zero is well-defined.
Further extensions typically include one or more special representations to
denote undefined or invalid values. These are commonly referred to as NaN
(not a number) or NaR (not a real), and are used to represent non-real complex numbers or domain violations (e.g. ln(−1)). While IEEE 754 floating-point
numbers are based on the affinely extended real numbers and have multiple
NaN representations, formats such as posits and takums instead exclude explicit
representations of infinity and use a single NaR for both infinities and non-real
numbers.
This was not always the case for posits. Early versions of the posit format only
included a single infinity non-number representation [7, 18]. However, this was
later revised in the draft standard [8], which removed the infinity representation
in favour of a single NaR. The rationale for this decision is that the encoding
scheme only permits a single special non-numeric value, and the practical utility
of being able to propagate NaR in computations to signal error conditions was
deemed to outweigh the mathematical elegance of a single infinity. The takum
format subsequently adopted this revised approach [12].
The most mathematically complete and elegant alternative would be a set of
represented values that includes both ∞ and NaR. Such a structure does exist
in the form of the wheel algebra applied to reals, R ∪{∞, NaR} [4]. In this framework, one defines ∞ := 1/0 and NaR := 0/0, where NaR is referred to as the
‘bottom element’. The wheel algebra supports multiplication and inversion across
all its elements, offering a closed and consistent model for arithmetic. Figure 1
illustrates a common visualisation of the wheel algebra: a circle representing the
extended real values, with NaR at the centre, resembling a wheel with a hub.
The numbers 1 and −1 are explicitly included as fixed points under inversion
(reflection of the circle across the x-axis), just as 0 and ∞ serve as fixed points
under negation (reflection across the y-axis).

L. Hunhold

T0

NaR

−1

T0
0
T01

NaR
T1

1T

T

TT

−1

T1T
T10
1
T1 T
0T

111

NaR
TTT

0
10
10T
1T1
1T0
1T
01 T
1

1

0
01 T
01
001

01

0T

1

110
11
10 T
1

11

0T
0
0T
1
00T

1

∞
TT0

∞
1
TT T
T0

∞

10

6

000

0

00

0

0

0

(a) n = 1

(b) n = 2

(c) n = 3

Figure 2: Mapping of ternary strings of lengths n ∈ {1, 2, 3} to the real wheel
algebra.

In light of the mathematical elegance of the real wheel algebra, one might
naturally ask why formats such as posits and takums do not include both ∞
and NaR. If we consider discretising this set, we would ideally require an equal
number of values in each quadrant of the wheel so that both negation and inversion map represented values back into the set. In other words, after assigning
the five fundamental elements, NaR, −1, 0, 1, and ∞, the remaining number of
unassigned states must be divisible by four.
In binary representations, this condition can never be satisfied. The total
number of states is a power of two (and thus even), and subtracting the five
fixed elements yields an odd number, which cannot be evenly divided by four.
Ternary strings, on the other hand, have a total number of states equal to a
power of three, which is always odd. Subtracting five from an odd number yields
an even result, raising the question: could this make the construction viable?
We assign the bottom element, NaR, to the lexicographically smallest balanced ternary integer, T · · · T, ensuring that it is also the smallest element under
comparison. This approach is consistent with the total ordering predicate introduced in the 2019 revision of the IEEE 754 standard, which similarly defines
NaN as smaller than all real numbers [13, §5.10]. Proceeding in increasing order,
we assign the remaining values such that 0 · · · 0 always maps to zero, and the
lexicographically largest balanced ternary integer, 1 · · · 1, maps to ∞. The result
of this assignment scheme for n ∈ {1, 2, 3} is illustrated in Figure 2.
3.1

Filter 1: Asymmetry

The attentive reader may have already observed that while the assignment illustrated in Figure 2 works well for n ∈ {1, 2}, it introduces an asymmetry for
n = 3: the upper quadrants contain five elements, whereas the lower quadrants
contain six. This irregularity marks the first filter in our derivation process. It
stems from the fact that ternary strings do not yield state counts as conveniently
structured as in the binary case, where the total number of states is 2n for n
bits, and the number of assignable values per quadrant, namely (2n − 4)/4 (after

Tekum: Balanced Ternary Tapered Precision Arithmetic

7

reserving the four special elements NaR, −1, 0, and 1), is always an integer,
specifically 2n−2 − 1.
In contrast, no such regularity emerges for 3n − 5 (or 3n − 4 if we omit ∞).
Nevertheless, a single viable path is shown in the following
Proposition 1. Let n ∈ N0 . It holds 4 | (32n − 5) and 4 ∤ (3n − 4).
Proof. With a ≡ b (mod c) → an ≡ bn (mod c) for a, b, c ∈ Z via [1, Lemma 5.2c]
it holds
4 | (32n − 5) ⇔ 32n − 5 ≡ 0

(mod 4)

(3)

⇔ 9n ≡ 5

(mod 4)

(4)

n

(mod 4)

(5)

(mod 4)

(6)

⇔9 ≡1
n

n

⇔9 ≡1
⇐9≡1

(mod 4).

(7)

We can also show
4 | (3n − 4) ⇔ 3n − 4 ≡ 0

(mod 4) ⇔ 3n ≡ 0

however 3n is never divisible by four as it’s odd.

(mod 4) ⇔ 4 | 3n ,

(8)
⊔
⊓

This proposition demonstrates two key points. First, it confirms that a meaningful ternary discretisation of the real wheel algebra is indeed possible, provided
that n is even. Second, it highlights that reserving only four special elements, the
approach taken by posits and takums, can never yield a symmetric distribution,
and thus is fundamentally unsuitable for this purpose. We therefore proceed
under the assumption that n is even and use the assignment as outlined earlier.
3.2

Filter 2: Misfit Tool

Despite having overcome the first filter, and having settled on the general approach to restrict n to even numbers, we have yet to define the mapping rule
for the values within each quadrant beyond the fundamental elements. This
mapping should ideally follow the tapered precision paradigm. However, here
we encounter the second filter: the prefix strings used in posit arithmetic cannot be translated directly into ternary logic, rendering them an ill-suited tool for
ternary arithmetic. Similarly, takum’s fixed-size regime offers no straightforward
adaptation to the ternary case.
Let us first consider a positive trit string t ∈ {0 · · · 01, . . . , 1 · · · 10}. Our aim
is to process this string in such a way that it yields a meaningful mapping to
the positive real numbers. The initial observation is that, given the extreme
cases 0 · · · 0 (representing 0) and 1 · · · 1 (representing ∞), and knowing that all
quadrants contain the same number of elements, the value 1 must lie exactly in
the middle. The corresponding ternary sequence for 1 is 1T · · · 1T, since 1T+1T =
11 holds, a property that extends to any trit string of even length. Given that

8

L. Hunhold

1 corresponds to exponent zero, a natural approach is to subtract 1T · · · 1T from
t. This yields zero when t = 1T · · · 1T, a positive value when t lies in the upper
quadrant (1, ∞), and a negative value when t is in the lower quadrant (0, 1).
By construction, the expression (t − 1T · · · 1T) lies within the integer set
{T1 · · · T10T, . . . , 1T · · · 1T01}. We can now employ the takum approach, using
a fixed number of trits to encode the so-called ‘regime’ value, which serves as
the parameter for a variable-length exponent. Although this may seem counterintuitive given, after all, the regime values appear to be evenly spaced, the key
insight is that each additional trit used for the exponent reduces the number
of trits available for encoding the fraction. As a result, the number density decreases by a factor of three for each trit allocated to the exponent, thus realising
tapered precision.
The number of trits allocated to the regime represents a trade-off: fewer regime trits allow for higher maximum precision, but at the expense of the number
of representable regime values. We now explore this design choice in more detail.
If we assign the first two trits of t − 1T · · · 1T to represent the regime, the regime trits fall within the range {T1, . . . , 1T}, corresponding to the integer interval
{−2, . . . , 2}. In contrast, assigning the first four trits as regime results in a range
of {T1T1, . . . , 1T1T}, mapping to the integer interval {−20, . . . , 20}, a range far
exceeding the requirements for encoding exponent lengths. A compromise is to
use three regime trits, yielding a regime range of {T1T, . . . , 1T1}, corresponding to the integer interval {−7, . . . , 7}. This choice offers a balanced trade-off
between exponent flexibility and precision. The precise role of the regime value
in variable-length exponent encoding will be discussed later.
The final aspect to address is the treatment of negative trit strings t ∈
{T · · · T0, . . . , 0 · · · 0T}. A straightforward approach is to compute the modulus |t|
and process the result. This is justified by the symmetry of the representation:
both upper quadrants (−∞, −1) and (1, ∞) correspond to the same positive
exponents, while the lower quadrants (−1, 0) and (0, 1) share the same negative
exponents. The only difference lies in the sign. Thus, for all trit strings t ∈ Tn ,
we shall compute |t| − 1T · · · 1T and assign the first three trits to be the regime
trits r. As we ‘anchor’ the trits onto a workable representation, we give the
following corresponding
Definition 7 (anchor function). Let n ∈ 2N0 . The anchor function ancn : Tn →
Tn is defined as ancn (t) = |t| − 1T · · · 1T.
An illustration of the proposed mapping for n = 4 is provided in Figure 3. At
this point, we can confidently conclude that we have found a way to make the
tool, namely the takum approach, fit again, overcoming the second filter in the
process.
3.3

Filter 3: Excess

Having set the number of regime trits to three, after excluding the alternative
choices of two and four, the next stage is to actually investigate the format we
obtain from this approach. As mentioned before, a straightforward approach is

Tekum: Balanced Ternary Tapered Precision Arithmetic

9

Table 1: Overview of mappings from regime values to exponent trit counts.
r
c(r)

|r|

0

1

2

3

4

5

000T ··· T 001T ··· T 01TT ··· T 010T ··· T 011T ··· T 1TTT ··· T
anc(t)
0001 ··· 1 0011 ··· 1 01T1 ··· 1 0101 ··· 1 0111 ··· 1 1TT1 ··· 1
c
0
emin
emax
int(e) 0 .. 0
b
0
e
0 .. 0
lg(3e ) 0 .. 0

c
0
emin
emax
max(0,
int(e) 0 .. 0
|r| − 1)
b
0
e
0 .. 0
lg(3e ) 0 .. 0

6

7

1T0T ··· T
1T01 ··· 1

1T1T ··· T
1T1T ··· 1T01

1
2
3
4
5
6
7
T
TT
TTT
TTTT
TTTTT
TTTTTT
TTTTTTT
1
11
111
1111
11111
111111
T1T1T1T
−1 .. 1
−4 .. 4 −13 .. 13 −40 .. 40 −121 .. 121 −364 .. 364 −1093 .. −547
2
8
26
80
242
728
2186
1 .. 3
4 .. 12
13 .. 39 40 .. 120 121 .. 363 364 .. 1092 1093 .. 1639
0.5 .. 1.4 1.9 .. 5.7 6.2 .. 19 19 .. 57 58 .. 173
174 .. 521 521 .. 782
0

1
2
3
4
T
TT
TTT
TTTT
1
11
111
1111
0 .. 0
−1 .. 1 −4 .. 4
−13 .. 13 −40 .. 40
1
3
9
27
81
1 .. 1
2 .. 4
5 .. 13
14 .. 40 41 .. 121
0.5 .. 0.5 1.0 .. 1.9 2.4 .. 6.2 6.7 .. 19 20 .. 58

5
6
TTTTT
TTTTTT
11111
T1T1T1
−121 .. 121 −364 .. −182
243
729
122 .. 364 365 .. 547
58 .. 174
174 .. 261

c
0
emin
emax
int(e) 0 .. 0
b
0
e
0 .. 0
lg(3e ) 0 .. 0

0

1
1
2
3
T
T
TT
TTT
1
1
11
111
0 .. 0
−1 .. 1 −1 .. 1
−4 .. 4
−13 .. 13
1
3
6
12
30
1 .. 1
2 .. 4
5 .. 7
8 .. 16
17 .. 43
0.5 .. 0.5 1.0 .. 1.9 2.4 .. 3.3 3.8 .. 7.6 8.1 .. 21

4
TTTT
1111
−40 .. 40
84
44 .. 124
21 .. 59

5
TTTTT
T1T1T
−121 .. −61
246
125 .. 185
60 .. 88

c
0
emin
emax
max(0,
int(e) 0 .. 0
|r| − 2)
b
0
e
0 .. 0
e
lg(3 ) 0 .. 0

0

0

1
2
3
T
TT
TTT
1
11
111
0 .. 0
0 .. 0
−1 .. 1
−4 .. 4
−13 .. 13
1
2
4
10
28
1 .. 1
2 .. 2
3 .. 5
6 .. 14
15 .. 41
0.5 .. 0.5 1.0 .. 1.0 1.4 .. 2.4 2.9 .. 6.7 7.1 .. 20

4
TTTT
1111
−40 .. 40
82
42 .. 122
20 .. 58

5
TTTTT
T1T1T
−121 .. −61
244
123 .. 183
59 .. 87

c
0
emin
emax
int(e) 0 .. 0
b
0
e
0 .. 0
lg(3e ) 0 .. 0

0

0

1
1
2
T
T
TT
1
1
11
0 .. 0
0 .. 0
−1 .. 1
−1 .. 1
−4 .. 4
1
2
4
7
13
1 .. 1
2 .. 2
3 .. 5
6 .. 8
9 .. 17
0.5 .. 0.5 1.0 .. 1.0 1.4 .. 2.4 2.9 .. 3.8 4.3 .. 8.1

3
TTT
111
−13 .. 13
31
18 .. 44
8.6 .. 21

4
TTTT
T1T1
−40 .. −20
85
45 .. 65
21 .. 31

c
0
emin
emax
max(0,
int(e) 0 .. 0
|r| − 3)
b
0
e
0 .. 0
lg(3e ) 0 .. 0

0

0

0

1
2
T
TT
1
11
0 .. 0
0 .. 0
0 .. 0
−1 .. 1
−4 .. 4
1
2
3
5
11
1 .. 1
2 .. 2
3 .. 3
4 .. 6
7 .. 15
0.5 .. 0.5 1.0 .. 1.0 1.4 .. 1.4 1.9 .. 2.9 3.3 .. 7.2

3
TTT
111
−13 .. 13
29
16 .. 42
7.6 .. 20

4
TTTT
T1T1
−40 .. −20
83
43 .. 63
21 .. 30

c
0
emin
emax
gamma int(e) 0 .. 0
b
0
e
0 .. 0
lg(3e ) 0 .. 0

0

0

0

2
TT
11
−4 .. 4
14
10 .. 18
4.8 .. 8.6

3
TTT
T1T
−13 .. −7
32
19 .. 25
9.1 .. 12

alpha

beta

1
1
T
T
1
1
0 .. 0
0 .. 0
0 .. 0
−1 .. 1
−1 .. 1
1
2
3
5
8
1 .. 1
2 .. 2
3 .. 3
4 .. 6
7 .. 9
0.5 .. 0.5 1.0 .. 1.0 1.4 .. 1.4 1.9 .. 2.9 3.3 .. 4.3

10

L. Hunhold

→ 6
TTT0 → 1T01
6
1T00 → 6
TTT1 → T0T → 5
→ 1 T1 → 5
T
TT0T
1
→
5
0 → 1TT0 → 4
TT0
TT
4
→
1T 1 →
01
4
TT
→ 011 0 →
→ 3
1
1T
TT 0 → 01 1T →
1 1
1
TT 1 → 0 10
1
→ 0
TT TT →
T0 T0
T0

1111
6 ← 1T01 ←
1110
6 ←
6 ← 1T00 ← 11
1T
5 ← 1T0T
←1
5
1T
101
5 ← 1 T1 ←
110
4 ← TT0
0
←
4 ← 1T
11
4 ← 0 TT
0T
3 ← 0 111 ←
← 0 11
← 11T
1
0
01 11
← 11
01 T ← 1 T0
1T
← 1
T
0
10 11
10

∞

NaR
TTTT

1T
10 01
← 10 0
00 ← 100
01 0T ←
0T
1 1
10
0
←
T
1
3 ← 01 T0 ← 10T
3 ← 01
←
0
2 ← 1TT
10T
2 ← 0 11 ←
0TT
2
00
←1
←
0
1
1
00
11
1 ← 001T ← 1T
1 ←
1T10
0 ← 0001 ←
0 ← 0000 ← 1T1T
0 ← 000T ←
1T01
−1
−1 ← 00T1 ←
1T00
− ← 00
−21 ← 0 T0 ← 1
T0T
− ← 0TT
←
− 2
0
1TT
− 2 ← T11
1
←
− 3 ← 0T1
1
3 ← 0T 0 ←
TT
0
← 0 1T
1
T
TT
0T 01 ←
T
00 ← 01
11
← 01
1
01
0
1T

1

01
01 00
1
T
← 0
10
0T ← 0
1
0T TT1 ← 01T
0
0
←
← 0 T
1T
T
0
3 ← 0 TT
T
− 4 ← 0T 11 ← 01T
− 4 ← T1
0←
− 4
011
− 5 ← T11 T ← 0
− 5 ← T11
0010
−5 ←
1←
− ← T10
001T
−6 ← T100 ←
−6
← 0001
−6 ← T10T
0000

0T
0T 0T
00 →
0T
→ 0
0
0T 1 → 0 T0
1
T T
0T T → 0T T1 →
10
T
→ 3
→ 0TT 0 →
0T
−
11
T1 T → 4−
4−
→
11
00T
T → T110 → 4−
→ 5−
T1
00T0
→ T 1 T → 5−
00T1 → 101 → 5−
T100 → 6−
6−
000T → T10T
→ 6−

−1

T0
T
T0 1
→
0
T0 T → 0
00
1
T0
→ 01 00
01
0
→
→ 01T T →
T0
1T
01 1 → 3
3
→
T0
T01
0 → 01TT → 2
001 → 2
T 011
2
1
→0
→
T1TT → 010 → 1
1
001T
T1T0 → 0001 → 1
→ 0
T1T1 → 0000 → 0
→ 0
T10T → 000T → 1−
00T1
1−
T100 → 0T0 → 1−
→ 0 TT → 2−
T 101
00 1 → 2−
→
1
T
0T 0 → 2−−
T 11
1
3 −
→
0T 1T →
10
→ 3
T1
→
T
11 → 0 T01 0 →
1
T
0 0
T
TT
0T 0 → 0
T
→
0T T1
T
0

0

Figure 3: Mapping of ternary strings t of length 4 to the real wheel algebra.
The values of anc4 (t) are given, with the first three trits, designated as the
regime trits r, highlighted accordingly. The corresponding regime values r are
also indicated, partially with suffixed signs for better visual consistency.

to take the modulus of the regime value r ∈ {−7, . . . , 7} and use it as the count
c of exponent trits e following after the regime bits. With a careful selection of
biases b added to the value int(e) represented by the exponent trits we obtain
a consecutive sequence of exponent values e. Please refer to the first row block
of Table 1 to observe the derivation of biases and outcome in terms of exponent
values for each regime.
We notice a big issue: This approach yields an obviously excessive dynamic
range of 10±782 . But what is a good general purpose dynamic range? The first
work setting a rough bound is by Quevedo, who remarks ‘No he señalado límite
al valor del exponente; pero es evidente que en todos los cálculos usuales será
menor de ciento’ (I have not set a limit on the value of the [base-10] exponent,
but it is clear that in all usual calculations it will be less than one hundred;
translation by the author) [23, pp. 582 sq.]. A more thorough investigation in
[12, Section 1.2] makes the case for a dynamic range of 10±55 . While one can go
into the multitude of application-specific arithmetic, for which there is almost
no lower bound on dynamic range, the author would like to make the case that

Tekum: Balanced Ternary Tapered Precision Arithmetic

11

if someone builds general-purpose, dedicated hardware, the arithmetic shall be
as well.
To tame the excessive dynamic range yielded by choosing c(r) = |r|, we
consider the parametric liberties we have in this case. The mapping c(r) shall
be non-decreasing and start at zero. An additional justifiable constraint is that
consecutive counts should only differ by zero or one. These constraints limit
the choices of c(r), and the first six are given in Table 1: Three mappings are
straightforward shifts, where we only ‘start counting’ after a certain threshold is
exceeded. Until then the regimes only represent a single exponent value. Given
are also three more special mappings called ‘alpha’, ‘beta’ and ‘gamma’, where
after the skip the counting is not linear, but actually tapered itself by repeating
the count one for two times.
Overall we can see, in terms of dynamic ranges, a wide selection, going all
the way down to 10±12 . Given we explored all possible, reasonable choices of
c(r) within this range we can say with confidence that this parametric space
has been exhausted. While max(0, |r| − 1) still has an excessive dynamic range
of 10±261 , the choices beta, max(0, |r| − 3) and gamma have insufficient general
purpose dynamic ranges 10±31 , 10±30 and 10±12 respectively. Only remaining
as candidates are alpha and max(0, |r| − 2) with similar dynamic ranges 10±88
and 10±87 respectively, both satisfying both the Quevedo limit of 10100 and
the lower bound 1055 derived in [12]. The final choice falls on max(0, |r| − 2), as
it has higher precision for smaller values, which should always take precedence
over the rarer ‘outer’ numbers.

4

Tekum Definition

In this section, we introduce the tekum format, building upon the observations
made in the previous section. The term ‘tekum’ is derived from a combination of
‘ternary’ and ‘takum’, reflecting the two foundational pillars of its design. First,
the format is based on a balanced ternary representation. Second, it follows the
design principles of takum, most notably its limited dynamic range. The name
‘takum’ itself originates from the Icelandic phrase ‘takmarkað umfang’, which
translates to ‘limited range’. On this basis, we obtain the following format:
Definition 8 (tekum encoding). Let n ∈ 2N1 with n ≥ 8. Any t ∈ Tn with
r+
+e+
+ f := ancn (t) of the form
exponent

fraction

r

e

f

3

c

p

12

L. Hunhold

Table 2: Overview of the tekum arithmetic colour scheme.
colour identifier OKLCH
regime

CIELab

HEX (sRGB)

(50%, 0.09, 220) (42.44, −20.42, −21.18) #046F87

exponent (50%, 0.09, 335) (40.72, 27.23, −13.9)

#834F78

fraction

#636363

(50%, 0.00, 0)

(42.00, 0.00, 0.00)

with regime trits r, exponent trits e, fraction trits f , and
s := sign(intn (t))
r := int3 (r) ∈ {−7, . . . , 7}
c := max(0, |r| − 2) ∈ {0, . . . , 5}
p := n − c − 3 ∈ {n − 8, . . . , n − 3}
j
k
b := sign(r) · 3|r|−2 + 1
= sign(r) · (0, 1, 2, 4, 10, 28, 82, 244)|r|
e := intc (e) + b ∈ {−183, . . . , 183}
f := 3

−p

intp (f ) ∈ (−0.5, 0.5)

: sign
: regime value
: exponent trit count

(10)

: fraction trit count

(12)

: exponent bias

(13)

: exponent value

(14)

: fraction value

(15)

(9)
(11)

encodes the tekum value

NaR



0
θn (t) :=

∞



s · (1 + f ) · 3e

r+
+e+
+ f = T···T
r+
+e+
+ f = 0···0
(16)
r+
+e+
+ f = 1···1
otherwise

with θ : Tn 7→ {NaR, 0, ∞}∪± 0.5 · 3−183 , 1.5 · 3183 . Without loss of generality,
any trit string shorter than 8 trits with an even, positive number of trits is
also included in the definition by matching the special cases (NaR, 0, and ∞)
respectively and expanding r+
+e+
+f with zeros in non-special cases. The case n =
1, which only covers the special cases, is also trivially included. By convention,
NaR and ∞ are defined to be smaller and larger than any other represented
value, respectively.
We also introduce a tekum colour scheme, prioritising uniformity in both lightness and chroma within the perceptually uniform OKLCH colour space [17].
Detailed colour definitions are delineated in Table 2.
Just as with the posit and takum formats, the tekum format can also be
expressed as a logarithmic number system by renaming the fraction trits as
mantissa trits, denoted by m, and correspondingly the fraction value as m, the
mantissa value. In this case, the fourth expression in (16) becomes s·3e+m . Since
the transition from binary to ternary is already a sufficiently radical step, we

Tekum: Balanced Ternary Tapered Precision Arithmetic

13

refrain from introducing a different base for the logarithmic format and retain
base 3. In this way, both the linear and logarithmic tekum formats share the
same overall numerical properties, with the logarithmic form serving merely
as an implementation detail. Within the scope of this work we do not pursue
logarithmic tekums further, but simply note the possibility.
Particular attention may be drawn to the floating-point representation (1 +
f )·3e . Although it may appear counterintuitive, it is indeed correct. This becomes
evident when considering its value range, (0.5 · 3e , 1.5 · 3e ). Notably, the upper
bound 1.5 · 3e is equal to 0.5 · 3e+1 , thereby connecting seamlessly to the adjacent
range (0.5 · 3e+1 , 1.5 · 3e+1 ).
As an illustrative example, Table 3 presents the decoding of all positive 4-trit
tekums, including a complete account of the intermediate quantities. Even at this
limited size, tekums already exhibit a substantial dynamic range, approaching
the recommended general-purpose range of 10±55 derived in [12]. Nevertheless,
the format warrants further evaluation with respect to its numerical properties.
This forms the focus of the following section.

5

Evaluation

Before evaluating tekums against other formats, it is first necessary to consider
the general principles required for fair comparisons between binary and ternary
systems.
5.1

Comparing Binary with Ternary

As noted in the introduction, a trit contains approximately 1.58 bits of information. This difference must be accounted for when comparing binary and ternary
formats. For example, when displaying a quantity relative to a bit count n, the
ternary dataset must be scaled accordingly.
A particular challenge arises when conducting benchmarks between formats,
where such simple rescaling is not possible. The standard binary widths of
number formats are 8, 16, 32, and 64 bits. A direct comparison between an
8-bit format and an 8-trit format would be misleading, as the latter possesses
38 = 6561 representations in contrast to only 28 = 256. By dividing the binary bit widths 8, 16, 32, and 64 by log2 (3) ≈ 1.58, one obtains approximately
5.0, 10.1, 20.2, and 40.4, which are naturally matched by the integers 5, 10, 20,
and 40. These represent the trit counts of ternary strings with approximately
equivalent information content.
The difficulty arises at 8 bits: tekums are defined only for even trit counts,
meaning a 5-trit tekum cannot be used. One possible approach is to evaluate both
4-trit and 6-trit variants and present both results, noting that an ‘imaginary’ 5trit tekum would fall somewhere in between. For higher precisions, however,
suitable matches can be found at the even trit counts of 10, 20, and 40, thereby
enabling more direct comparisons.

14

L. Hunhold

Table 3: Tekum decoding table for n = 4, pruned to positive numbers.
t
000T
0000
0001
001T
0010
0011
01TT
01T0
01T1
010T
0100
0101
011T
0110
0111
1TTT
1TT0
1TT1
1T0T
1T00
1T01
1T1T
1T10
1T11
10TT
10T0
10T1
100T
1000
1001
101T
1010
1011
11TT
11T0
11T1
110T
1100
1101
111T
1110
1111

int4 (t)

s anc4 (t) r

−1 −1 T10T
0
1 1 T10T
2 1 T100
3 1 T101
4 1 T11T
5 1 T110
6 1 T111
7 1 0TTT
8 1 0TT0
9 1 0TT1
10 1 0T0T
11 1 0T00
12 1 0T01
13 1 0T1T
14 1 0T10
15 1 0T11
16 1 00TT
17 1 00T0
18 1 00T1
19 1 000T
20 1 0000
21 1 0001
22 1 001T
23 1 0010
24 1 0011
25 1 01TT
26 1 01T0
27 1 01T1
28 1 010T
29 1 0100
30 1 0101
31 1 011T
32 1 0110
33 1 0111
34 1 1TTT
35 1 1TT0
36 1 1TT1
37 1 1T0T
38 1 1T00
39 1 1T01
40

r o e

b

e p f

T10 −6 4 T000 −82 −109 0

f 1+f
0.0

T10 −6 4 T000 −82 −109 0
0.0
T10 −6 4 0000 −82 −82 0
0.0
T10 −6 4 1000 −82 −55 0
0.0
T11 −5 3 T00 −28 −37 0
0.0
T11 −5 3 000 −28 −28 0
0.0
T11 −5 3 100 −28 −19 0
0.0
0TT −4 2 T0 −10 −13 0
0.0
0TT −4 2 00 −10 −10 0
0.0
0TT −4 2 10 −10 −7 0
0.0
0T0 −3 1 T
−4 −5 0
0.0
0T0 −3 1 0
−4 −4 0
0.0
0T0 −3 1 1
−4 −3 0
0.0
0T1 −2 0
−2 −2 1 T −0.3
0T1 −2 0
−2 −2 1 0 0.0
0T1 −2 0
−2 −2 1 1 0.3
00T −1 0
−1 −1 1 T −0.3
00T −1 0
−1 −1 1 0 0.0
00T −1 0
−1 −1 1 1 0.3
000 0 0
0
0 1 T −0.3
000 0 0
0
0 1 0 0.0
000 0 0
0
0 1 1 0.3
001 1 0
1
1 1 T −0.3
001 1 0
1
1 1 0 0.0
001 1 0
1
1 1 1 0.3
01T 2 0
2
2 1 T −0.3
01T 2 0
2
2 1 0 0.0
01T 2 0
2
2 1 1 0.3
010 3 1 T
4
3 0
0.0
010 3 1 0
4
4 0
0.0
010 3 1 1
4
5 0
0.0
011 4 2 T0
10
7 0
0.0
011 4 2 00
10
10 0
0.0
011 4 2 10
10
13 0
0.0
1TT 5 3 T00
28
19 0
0.0
1TT 5 3 000
28
28 0
0.0
1TT 5 3 100
28
37 0
0.0
1T0 6 4 T000 82
55 0
0.0
1T0 6 4 0000 82
82 0
0.0
1T0 6 4 1000 82 109 0
0.0

θ4 (t)

1.0 −9.9 × 10−53
0
1.0 9.9 × 10−53
1.0 7.5 × 10−40
1.0 5.7 × 10−27
1.0 2.2 × 10−18
1.0 4.4 × 10−14
1.0 8.6 × 10−10
1.0
6.3 × 10−7
1.0
1.7 × 10−5
1.0
4.6 × 10−4
1.0
4.1 × 10−3
1.0
1.2 × 10−2
1.0
3.7 × 10−2
0.7
7.4 × 10−2
1.0
1.1 × 10−1
1.3
1.5 × 10−1
0.7
2.2 × 10−1
1.0
3.3 × 10−1
1.3
4.4 × 10−1
0.7
6.7 × 10−1
1.0
1.0
1.3
1.3
0.7
2.0
1.0
3.0
1.3
4.0
0.7
6.0
1.0
9.0
1.3
1.2 × 101
1.0
2.7 × 101
1.0
8.1 × 101
1.0
2.4 × 102
1.0
2.2 × 103
1.0
5.9 × 104
1.0
1.6 × 106
1.0
1.2 × 109
1.0
2.3 × 1013
1.0
4.5 × 1017
1.0
1.7 × 1026
1.0
1.3 × 1039
1.0
1.0 × 1052
∞

Tekum: Balanced Ternary Tapered Precision Arithmetic

15

-(non-fraction length)/bits

−4
Tekum (1.58 bits/trit)
ternary27 (1.58 bits/trit)
Takum
Posit
bfloat16/float32
float64

−6
−8
−10
−12
−14
−80

−60

−40

−20

0

20

40

60

80

log10 (|x|)

Figure 4: The number of non-fraction bits, which can be considered as overhead,
relative to the represented value x in a selection of floating-point formats. The
y-axis is inverted, thus meaning that higher values mean less overhead.

5.2

Format

Posits consist of five bit fields (sign bit, regime bits, regime terminator bit,
exponent bits, and fraction bits). Takums are structurally similar, also requiring
five fields (sign bit, direction bit, regime bits, characteristic bits, and fraction
bits). In contrast, tekums are considerably simpler, comprising only three trit
fields: regime trits, exponent trits, and fraction trits. This simplicity may not
only facilitate formal analysis but could also prove advantageous for hardware
implementation.
5.3

Accuracy

The first aspect of analysis concerns the accuracy of the tekum format. Following
the approach taken in [12], one may consider the number of bits required to
encode the sign and exponent of a given number x > 0, which can be interpreted
as the overhead of encoding. The larger this overhead, the fewer fraction bits
remain available. To enable comparison between binary and ternary formats, the
overhead in trits for ternary formats is multiplied by log2 (3).
The results are shown in Figure 4. It is immediately evident that ternary27
performs poorly, owing to its excessive waste of representations. The spike on
the left is the result of a mechanism akin to subnormals; however, the effect is
limited and occurs in an irrelevant region of numbers close to 10−60 .

16

L. Hunhold

80

log10 (dynamic range)

60
40

Tekum (1.58 bits/trit)
ternary27 (1.58 bits/trit)
Takum
Posit
IEEE 754 normal
IEEE 754 subnormal
OFP8 E4M3
OFP8 E5M2
bfloat16

20
0
-20
-40
-60
-80
24

8

16

32
bit string length n

64

Figure 5: Dynamic range relative to the bit string length n for tekum, (linear)
takum, posit and a selection of floating-point formats.

In contrast, tekums perform favourably. Compared to both posits and (linear)
takums, tekums exhibit a region of highest accuracy of similar size to posits. This
addresses a weakness of takums, which display a sharp drop in precision around
the centre. Notably, tekums also achieve a significantly broader region of equal
or superior precision compared with bfloat16 and float32. In addition, tekums
retain the same desirable logarithmic tapering property as takums.

5.4

Dynamic Range

The dynamic range results, shown in Figure 5, largely confirm expectations, as
the tekum dynamic range was explicitly designed to be 10±87 . Although this
range exceeds the previously identified minimum recommended general-purpose
dynamic range of 10±55 , it remains comfortably within the bound suggested by
Quevedo. Owing to the tapered precision property, only a small fraction of
values extend beyond 10±55 .
It is also noteworthy that, as with takums, the dynamic range of tekums
increases rapidly at low precisions, quickly reaching its maximum, which is a
desirable feature. The ternary27 format also achieves a general-purpose dynamic range, but this range is asymmetric due to its inclusion of subnormal
representations.

Tekum: Balanced Ternary Tapered Precision Arithmetic

5.5

17

Formal Analysis

Building upon the discussion of the format’s properties, we now turn to the
formal analysis and validation of the tekum format in terms of its fundamental
characteristics, following the same methodology as applied to the takum format
in [12, Section 4.5]. We begin by showing that there exist no redundant encodings, as stated in the following proposition.
Proposition 2 (Uniqueness). Let n ∈ 2N1 and t, u ∈ Tn . It holds
θn (t) = θn (u) ⇒ t = u.

(17)

Proof. Assume θn (t) = θn (u). By construction, it follows that t = u for the
special cases θn (t), θn (u) ∈ {0, ∞, NaR}. Hence, it remains to consider the nonspecial case, for which we define θn (t) := s·(1+f )·3e and θn (u) := s̃·(1+ f˜)·3ẽ .
Given θn (t) = θn (u), we can immediately deduce s = s̃, since (1+f ), (1+ f˜),
ẽ
3 , and 3e are all positive. Moreover, as (1 + f ), (1 + f˜) ∈ (0.5, 1.5), both f = f˜
and e = ẽ are uniquely determined. By construction, (s, e, f ) = (s̃, ẽ, f˜) implies
t = u.
⊔
⊓
Although this is a straightforward result, it highlights that, by design, no ternary
representations are wasted on redundant encodings. We now proceed to show
that ternary negation of a tekum corresponds to negating its numerical value.
Proposition 3 (Negation). Let n ∈ 2N1 and t ∈ Tn with θn (t) ∈
/ {NaR, ∞}.
It holds
θn (−t) = − θn (t).
(18)
Proof. The only special case, namely t = 0 · · · 0, is trivial, given θn (−0 · · · 0) =
θn (0 · · · 0) = 0 holds. Furthermore, it holds that
ancn (−t) = | − t| − 1T · · · 1T = |t| − 1T · · · 1T = ancn (t),

(19)

which implies that t and −t share the same r, e, and f , and thus the same
fraction value f and exponent value e. The only distinction between them lies
in their signs s, which are opposite, yielding the desired result.
⊓
⊔
Another result concerns the ternary monotonicity of tekums, which is formalised
as follows.
Proposition 4 (Monotonicity). Let n ∈ 2N1 and t, u ∈ Tn . It holds
intn (t) < intn (u) ⇒ θn (t) < θn (u).

(20)

Proof. We first consider the special cases. By convention, NaR is smaller than
any other represented tekum value, which means that NaR < θn (u) holds. It
also holds intn (T · · · T) < intn (u), and T · · · T is the ternary representation of
NaR. Hence, monotonicity is satisfied for NaR. An analogous argument applies
to ∞, which by convention is larger than any other represented tekum value and
has the ternary representation 1 · · · 1, thereby establishing monotonicity for ∞.

18

L. Hunhold

We now turn to the non-special cases. By Proposition 3, it suffices to prove
the result for t and u with intn (t) > 0 and intn (u) > 0, as intn (0 · · · 0) = 0 and
θn (0 · · · 0) = 0 < θn (t), θn (u). The objective can be further reduced to showing
that, for any t ∈ {0 · · · 01, . . . , 1 · · · 01},
θn (t) < θn (t + 0 · · · 01),

(21)

i.e. the successive monotonicity of the positive non-special cases.
We denote ancn (t) := r +
+e+
+ f and ancn (t + 0 · · · 01) := r̃ +
+ ẽ +
+ f˜, where
tildes denote the components of the incremented ternary vector. For intn (t) > 0,
we have |t| = t, and in particular, provided there is no overflow,
ancn (t + 0 · · · 01) = ancn (t) + 0 · · · 01.

(22)

Hence, the field r +
+e+
+ f is incremented, and to establish monotonicity, we
must examine how this affects r, e and f .
Although we work in balanced ternary, carries may still occur, analogous
to the binary case. We therefore distinguish cases depending on whether the
increment affects only f , or whether a carry propagates into e. The latter occurs
precisely when f = 1 · · · 1, in which case we have f˜ = T · · · T, leading to an
additional case distinction on e. In all cases, s̃ = s.
Following this scheme, as the first case we assume f ̸= 1 · · · 1. It then holds
r̃ = r, ẽ = e and f˜ = f + 3−p > f , in particular ẽ = e. It follows that
θn (t + 0 · · · 01) = s̃ · (1 + f˜)3ẽ = s · (1 + f˜)3e > s · (1 + f )3e = θn (t),

(23)

which was to be shown.
The second case is f = 1 · · · 1 and e ̸= 1 · · · 1. Then f˜ = T · · · T and r̃ = r,
which implies r̃ = r, c̃ = c, p̃ = p, b̃ = b, and ẽ = e + 1 since the exponent field
increments without overflowing. As f˜ = −f , we have f˜ = −f , and thus
θn (t + 0 · · · 01) = s̃ · (1 + f˜)3ẽ = s · (1 − f )3e+1 > s · (1 + f )3e = θn (t), (24)
as required.
The third case is r ̸= 1 · · · 1, e = 1 · · · 1 and f = 1 · · · 1. Then f˜ = T · · · T (so
˜
f = −f ) and ẽ = T · · · T. In particular, r̃ = r + 1, hence b̃ > b. By construction,
the bias is chosen such that each exponent range is distinct for every regime. We
can therefore deduce ẽ > e, and it follows that
θn (t + 0 · · · 01) = s · (1 − f )3ẽ ≥ s · (1 − f )3e+1 > s · (1 + f )3e = θn (t), (25)
as required.
There is no fourth case where all trit fields are 1 · · · 1, as t is explicitly at most
1 · · · 01. Thus, all possibilities have been exhausted, completing the proof.
⊔
⊓
The significance of this result lies in the fact that there exists a direct correspondence between the ordering of ternary integer and tekum representations.
This property, also present for posits and takums, offers a notable implementation advantage: the same logic used for integer comparison can be employed

Tekum: Balanced Ternary Tapered Precision Arithmetic

19

for floating-point comparison, even eliminating the need for explicit special-case
handling of NaR and ∞.
A particularly noteworthy aspect in the context of tekums is that both NaR
and ∞ integrate seamlessly into this framework. Since tekums constitute the
first balanced ternary real number system, the introduction of a second special
value, ∞, in addition to NaR, posed a potential risk of breaking monotonicity.
Remarkably, however, the structure remains fully consistent, an elegant and
non-trivial property of the format.
We now turn to the next aspect, namely rounding. Balanced ternary exhibits
the elegant property that rounding an integer is equivalent to simply truncating it. This can be seen by considering an arbitrary real number expressed in
balanced ternary as the sum of an integral and a fractional part,
∞
X
i=0

ai 3i +

∞
X

bi 3−(i+1) ,

(26)

i=0

with a, b ∈ T∞ , which we wish to round to the nearest integer. The outcome
depends solely on the fractional part, which in the binary case lies in the interval
[0, 1), necessitating a distinction between the intervals [0, 0.5), exactly 0.5, and
(0.5, 1).
In the balanced ternary case, however, the fractional part lies in the
P∞interval
(−0.5, 0.5), meaning the nearest integer is always the integral part i=0 ai 3i .
In other words, rounding amounts to unconditionally truncating the fractional
part. The question is how this property translates to tekums, which would benefit
from such stable rounding behaviour. For this, we provide the following:
Proposition 5 (Truncation is Rounding). Let n ∈ 2N3 , t ∈ Tn with θ(t) ∈
/
{NaR, ∞} and a := ancn (t) ∈ Tn . It holds
ancinv
n (an−1 · · · a2 ) = arg min(| θ(t) − θ(u)|).

(27)

u∈Tn−2

In other words, for a given n-trit tekum, the closest (n−2)-trit tekum is obtained
by truncating its anchor by two trits and converting it back to a tekum (using
t’s sign). Since the conversion between a tekum and its anchor is lossless, this
property generalises to any truncation of the anchor, provided the anchor remains
at least four trits long to avoid truncating the regime trits.
Proof. Within the scope of the anchor, we are not restricted to even trit counts,
and may therefore consider the effect of truncating a single trit. Let
a=r+
+e+
+ f,

(28)

and denote all truncated quantities with a tilde. Since truncation never occurs
within the regime trits, we only distinguish between truncating an exponent trit
and truncating a fraction trit. In both cases, the sign s remains unchanged.
In the first case, truncating a trit from the fraction yields f˜, which represents
the closest integer to f . Consequently, f˜ is the closest representable value to f ,

20

L. Hunhold

and since e is unchanged, the tekum value
s · (1 + f˜) · 3ẽ = s · (1 + f˜) · 3e

(29)

is optimally close to θ(t), as required.
In the second case, we truncate a trit from the exponent trits. It holds f =
f˜ = 0. As the regime trits remain unchanged, both the bias and the number of
exponent trits are preserved (b = b̃, c = c̃). The truncated exponent
ẽ = intc (ẽ) + b

(30)

is the closest representable integer to e, and the tekum value s · 3ẽ is therefore
the optimal approximation of θ(t).
⊓
⊔
To give an example, consider rounding t = 01TTT1TT (ancn (t) = 001T1110, s = 1,
r = 1, c = 0, p = 5, b = 1, e = 1, f = 3−5 · (−42) ≈ −0.173, θ(t) ≈ 1.654) to four
trits. We truncate the anchor to the four trits 001T and obtain the tekum 1T11,
which represents the value 2.0 and is the closest representation (see Table 3).
This property has far-reaching implications despite the small computational
overhead of determining the anchor. Conversion between precisions is essentially
cost-free, requiring only the truncation or extension of the anchor. Well-known
issues in binary floating-point arithmetic, such as inaccuracies due to ‘double
rounding’, do not arise here: Truncation can be performed in any number of
steps with identical results.
5.6

Hardware Implementation

Ternary logic hardware remains in its infancy and is largely orthogonal to contemporary chip design. The theoretical advantages of ternary logic are substantial, offering higher information density, owing to its superior radix economy,
which is particularly relevant in the context of the memory wall that constrains
computer performance, and consequently reduced circuit and interconnect complexity, lower power dissipation, and potentially faster operational speeds.
Historically, apart from binary computers that merely emulate trits using
two bits each, such as the Setun and Setun 70 computers [3], proposals for
genuine ternary computers have relied on alternative technologies. These include
Josephson junctions [20] and optical computing, where dark represents zero
and two orthogonal polarisations of light encode T and 1 [14]. However, such
approaches never progressed beyond experimental prototypes.
Ternary computing has recently attracted renewed interest for two main
reasons: advances in ternary large-language models (LLMs) and developments
in Carbon Nanotube Field-Effect Transistors (CNTFETs). In the former case,
single trits are used to represent weights within deep neural networks, with
notable examples including BitNet [19, 24] and proposals for ternary hardware
implementations of neural networks [25]. Regarding CNTFETs, hundreds of publications in recent years have addressed advances ranging from general logic gates
[6, 22] to arithmetic units such as adders [10].

Tekum: Balanced Ternary Tapered Precision Arithmetic

21

In the context of implementing takums, a particular significance is attributed
to an adder dedicated to adding T1 · · · T1 for computing the anchor function ancn ,
which is central to decoding and rounding tekums. This capability could enable
more efficient circuit designs tailored to the tekum format.
It is noteworthy that the recent AI revolution may not only have catalysed
the exploration of novel arithmetic formats, but could also indirectly foster a
transition from binary to ternary computing.

6

Conclusion

This paper has introduced tekum, a novel balanced ternary real arithmetic
format, derived from three fundamental design challenges and evaluated against
rigorous criteria for fair comparison between binary and ternary representations.
Our analysis has demonstrated that tekums possess highly favourable numerical properties, not only in terms of precision and dynamic range, but also
in offering features unique to the ternary domain. Unlike their binary counterparts, posits and takums, tekums simultaneously accommodate both ∞ and
NaR, while retaining the simplicity of negation by flipping the underlying trit
string. Perhaps most strikingly, tekums enable rounding by truncation, a property that eradicates at a stroke some notorious problems of rounding in binary
arithmetic: double rounding errors, cascading carries in hardware, and the attendant inefficiencies.
Taken together, these properties position tekums not merely as a curiosity,
but as a radical and compelling alternative to established binary real number
formats. They demonstrate that balanced ternary arithmetic is not only viable,
but potentially transformative. While substantial work remains, tekums stand
as a bold step towards a new numerical foundation for future ternary computing,
a foundation that could redefine the very architecture of computation itself.

References
[1]

Tom M. Apostol. Introduction to Analytic Number Theory. 1st ed. Undergraduate Texts in Mathematics. New York, NY, USA: Springer New York,
1976. doi: 10.1007/978-1-4757-5579-4.
[2] Peter A. Boncz, Stefan Manegold and Martin L. Kersten. ‘Database Architecture Optimized for the New Bottleneck: Memory Access’. In: Proceedings of the 25th International Conference on Very Large Data Bases.
VLDB ’99. San Francisco, CA, USA: Morgan Kaufmann Publishers Inc.,
Sept. 1999, pp. 54–65. isbn: 1558606157. doi: 10.5555/645925.671364.
[3] Nikolay Petrovich Brusentsov and José Ramil Alvarez. ‘Ternary Computers: The Setun and the Setun 70’. In: Perspectives on Soviet and Russian Computing. Ed. by John Impagliazzo and Eduard Proydakov. Berlin,
Heidelberg, Germany: Springer Berlin Heidelberg, 2011, pp. 74–80. doi:
10.1007/978-3-642-22816-2_10.

22

[4]

[5]
[6]

[7]

[8]

[9]

[10]

[11]
[12]

[13]
[14]

[15]

[16]

L. Hunhold

Jesper Carlström. ‘Wheels – on Division by Zero’. In: Mathematical Structures in Computer Science 14 (Jan. 2004), pp. 143–184. doi: 10.1017/
S0960129503004110.
Amir Gholami et al. ‘AI and Memory Wall’. In: IEEE Micro 44.3 (2024),
pp. 33–39. doi: 10.1109/MM.2024.3373763.
Namineni Gireesh, Shaik Javid Basha and Ahmed Elbarbary. ‘CNTFETbased digital arithmetic circuit designs in ternary logic with improved performance’. In: e-Prime - Advances in Electrical Engineering, Electronics
and Energy 7 (2024). doi: https://doi.org/10.1016/j.prime.2024.
100427.
John L. Gustafson and Isaac Yonemoto. ‘Beating Floating Point at Its Own
Game: Posit Arithmetic’. In: Supercomputing Frontiers and Innovations
4.2 (June 2017), pp. 71–86. doi: 10.14529/jsfi170206.
John L. Gustafson et al. ‘Standard for Posit™ Arithmetic (2022)’. Mar.
2022. url: https://web.archive.org/web/20220603115338/https:
//posithub.org/docs/posit_standard-2.pdf.
Robin Hanson. ‘The Great Filter – Are We Almost Past It?’ Fairfax, VA,
USA, Sept. 1998. url: https://web.archive.org/web/20250906181317/
https://mason.gmu.edu/~rhanson/greatfilter.html.
Marzieh Hashemipour, Reza Faghih Mirzaee and Keivan Navi. ‘21T Ternary Full Adder Based on Capacitive Threshold Logic and Carbon Nanotube
FETs’. In: IEEE Transactions on Nanotechnology 23 (2024), pp. 338–345.
doi: 10.1109/TNANO.2024.3386825.
Brian Hayes. ‘Third Base’. In: American Scientist 89.6 (Dec. 2001), pp. 490–
494. doi: 10.1511/2001.40.490.
Laslo Hunhold. ‘Beating Posits at Their Own Game: Takum Arithmetic’.
In: Next Generation Arithmetic. 5th International Conference, CoNGA
2024, Sydney, NSW, Australia, February 20–21, 2024, Proceedings. Vol. 14666.
Lecture Notes in Computer Science. Sydney, NSW, Australia: Springer
Nature Switzerland, Oct. 2024. doi: 10.1007/978-3-031-72709-2_1.
IEEE Standard for Floating-Point Arithmetic. July 2019. doi: 10.1109/
IEEESTD.2019.8766229.
Yi Jin, Huacan He and Yangtian Lü. ‘Ternary Optical Computer Principle’. In: Science in China Series F: Information Sciences 46.2 (Apr.
2003), pp. 145–150. issn: 1862-2836. doi: 10.1360/03yf9012. url: https:
//link.springer.com/article/10.1360/03yf9012.
Douglas W. Jones. ‘The Ternary Manifesto’. Apr. 2012. url: https://
web.archive.org/web/20250815213618/https://homepage.cs.uiowa.
edu/~dwjones/ternary/.
Donald Ervin Knuth. Seminumerical Algorithms. 3rd ed. Vol. 2. The Art
of Computer Programming. Boston, MA, USA: Addison Wesley Longman,
1997. isbn: 978-0-201-89684-8. url: https://dl.acm.org/doi/10.5555/
270146.

Tekum: Balanced Ternary Tapered Precision Arithmetic

[17]

[18]

[19]
[20]

[21]
[22]

[23]

[24]
[25]

23

Chris Lilley. ‘Color on the Web’. In: Fundamentals and Applications of
Colour Engineering. John Wiley & Sons, Ltd, 2023. Chap. 16, pp. 271–
291. isbn: 9781119827214. doi: 10.1002/9781119827214.ch16.
Peter Lindstrom, Scott Lloyd and Jeffrey Hittinger. ‘Universal Coding of
the Reals: Alternatives to IEEE Floating Point’. In: CoNGA ’18 (Mar.
2018). doi: 10.1145/3190339.3190344.
Shuming Ma et al. ‘BitNet b1.58 2B4T Technical Report’. In: (Apr. 2025),
pp. 1–14. arXiv: 2504.12285 [cs.CL].
M. Morisue et al. ‘A Josephson Ternary Memory Circuit’. In: Proceedings.
1998 28th IEEE International Symposium on Multiple- Valued Logic (Cat.
No.98CB36138). 1998, pp. 19–24. doi: 10.1109/ISMVL.1998.679270.
Rory O’Hare. ‘Ternary27: A Balanced Ternary Floating Point Format’.
Sept. 2021. doi: 10.5281/zenodo.16575889.
Kumar R. Santhosh and Munibyarappa Roopa. ‘The Designing of Carbon Nanotube FET Based Encoder Using Ternary Logic’. In: 2024 Global
Conference on Communications and Information Technologies (GCCIT).
2024, pp. 1–6. doi: 10.1109/GCCIT63234.2024.10862332.
Leonardo Torres Quevedo. ‘Automática: Complemento de la Teoría de las
Máquinas’. In: Revista de Obras Públicas 2043 (Nov. 1914), pp. 575–583.
url: https://quickclick.es/rop/pdf/publico/1914/1914_tomoI_
2043_01.pdf.
Hongyu Wang et al. ‘BitNet: Scaling 1-bit Transformers for Large Language Models’. In: (Oct. 2023), pp. 1–14. arXiv: 2310.11453 [cs.CL].
Xuehao Zhu et al. ‘High-Performance Ternary Logic Circuits and Neural
Networks Based on Carbon Nanotube Source-Gating Transistors’. In: Science Advances 11.2 (2025). doi: 10.1126/sciadv.adt1909.

2/14/26, 9:50 PM

A magical land where rounding equals truncation

Navigation

A magical land where
rounding equals truncation
Posted on 23 January 2025 by John
Rounding numbers has a surprising amount of detail. It may seem trivial but, as
with most things, there is a lot more to consider than is immediately obvious. I
expect there have been hundreds if not thousands of pages devoted to rounding in
IEEE journals.
An example of the complexity of rounding is what William Kahan called The
Tablemaker’s Dilemma: there is no way in general to know in advance how
accurately you’ll need to compute a number in order to round it correctly.
Rounding can be subtle in any number system, but there is an alternative number
system in which it is a little simpler than in base 10. It’s base 3, but with a twist.
Instead of using 0, 1, and 2 as “digits”, we use −1, 0, and 1. This is known as the
balanced ternary system: ternary because of base 3, and balanced because the
digits are symmetrical about 0.
We need a symbol for −1. A common and convenient choice is to use T. Think of
moving the minus sign from in front of a 1 to on top of it. Now we could denote the
number of hours in a day as 10T0 because

https://www.johndcook.com/blog/2025/01/23/balanced-ternary-rounding/

1/4

2/14/26, 9:50 PM

A magical land where rounding equals truncation

A more formal way of a describing balanced ternary representation of a number x
is a set of coefficients tk such that

with the restriction that each tk is in the set {−1, 0, 1}.
Balanced ternary representation has many interesting properties. For example,
positive and negative numbers can all be represented without a minus sign. See,
for example, Brain Hayes’ excellent article Third Base. The property we’re interested
in here is that to round a balanced ternary number to the nearest integer, you
simply lop off the fractional part. Rounding is the same as truncation. To see this,
note that the largest possible fractional part is a sequence of all 1s, which
represents ½:

Similarly, the most negative possible fractional part is a sequence of all Ts, which
represents −½. So unless the fractional part is exactly equal to ½, truncating the
fractional part rounds to the nearest integer. If the fractional part is exactly ½ then
there is no nearest integer but two integers that are equally near.

Related posts

Floating point: Everything old is new again
The hardest logarithm to compute
Math’s base 32 vs Linux’s base 32
The base with the largest decibel

Categories :
Tags :

Math

Computing
Number systems

https://www.johndcook.com/blog/2025/01/23/balanced-ternary-rounding/

2/4

2/14/26, 9:50 PM

A magical land where rounding equals truncation

Bookmark the

permalink

Previous Post
Duplicating Hankel plot from A&S

Next Post
Double rounding

Search …
Search

John D. Cook, PhD

https://www.johndcook.com/blog/2025/01/23/balanced-ternary-rounding/

3/4

2/14/26, 9:50 PM

A magical land where rounding equals truncation

My colleagues and I have decades of consulting experience helping
companies solve complex problems involving data privacy, applied math,
and statistics.
Let’s talk. We look forward to exploring the opportunity to help your
company too.

JOHN D. COOK
© All rights reserved.
Search …
SEARCH

(832) 422-8646
EMAIL

https://www.johndcook.com/blog/2025/01/23/balanced-ternary-rounding/

4/4

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

Standard Ternary Logic
Part of http://homepage.cs.uiowa.edu/~dwjones/ternary/
by Douglas W. Jones
THE UNIVERSITY OF IOWA Department of Computer Science
Disclaimer: Nobody but the author endorses the use of the notation described here, although in general, the notations used by
researchers in this field are abysmally bad and the author would like it if others accepted his proposed notation.
©2012 Douglas W. Jones; revised 2016. Permission is hereby granted to make unrestricted use of the schematic diagrams
presented here for any purpose including derivative works; there are no restrictions on linking to this web page.

Abstract
Although considerable work on implementing ternary logic functions has been done, no standard notation
has emerged. The notation proposed here follows from conventional Boolean logic augmented by the third
value of Kleene logic, unknown. Where ternary functions are analogous to Boolean functions, parallel
notations are used. New notations are introduced where there are no analogous Boolean functions, and the
notation given here provides for mixing Boolean and ternary logic, where this makes sense. The
presentation ends with a discussion of minimization.
1. Ternary Constants
2. Monadic Operators
1. Buffers and Drivers
2. Negation
3. Increment and Decrement
4. Decoders
5. Clamps
3. Diadic Operators
1. Min or And
2. Max or Or
3. Antimin and Antimax
4. Exclusive Or
5. Sum
6. Consensus
7. Accept Anything
8. Comparison
4. Minimization
1. The Canonical Sum of Products
2. Combining Minterms
3. Shorthand Notation
4. Evaluating the Complexity of the Result

1. Ternary Constants
Kleene logic augments the conventional true and false of Boolean logic with a third value, unknown
[Fitting, 1994]. Various authors have suggested the assignment of different numerical equivalents to these
values. Here, we adopt the following:
https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

1/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

truth value numeric short form
true
+1
+
unknown
0
0
false
–1
–
ternary values
The primary motivation for this choice of numeric values is that it directly supports balanced ternary
encoding of numeric values, an encoding system that requires the trits (ternary digits) to have the values +1,
0 and –1. In addition, it meets the comfortable requirement that true be greater than false, and it permits an
equivalence between logical negation and integer negation.
All is not perfect, however. For unsigned ternary numbers, we would prefer the values 0, 1 and 2, and users
of conventional Boolean logic have a deeply ingrained desire to have false represented by zero and true by
one, suggesting that, perhaps, unknown should be two. In a more abstract lattice-theoretic sense, true and
false are both greater than unknown in that they convey more information. To complete the lattice (and move
to 4-valued logic) we could even add an overspecified value that is greater than both true and false
[Muskens, 1999]. Here, we simply ignore these alternatives while reserving the right to use alternative
orderings and numeric interpretations whenever that is convenient.
Our use of the symbols +, 0 and – to abbreviate +1, 0 and -1 follows [Alexander, 1964].

2. Monadic Operators
In conventional Boolean logic, there are a total of four (2 squared) monadic (single argument) functions,
three of which are trivial:
input false identity not true
false false false true true
true false true false true
Monadic Boolean functions
The false function always returns false, ignoring its arguments. Similarly the true function always returns
true, ignoring its arguments. A third trivial function, identity always returns its arguments unchanged. In
electrical engineering, buffers, drivers and repeaters implement this function. The single nontrivial function
is not, which inverts its input, returning false when given true and visa versa.
The move to Ternary increases the number of monadic functions from 4 to 27 (3 cubed) of which four are
trivial, three constant value functions and an identity function. All of these functions are enumerated here:
input 0 1 2 3 4 5 6 7 8 9 A B C D E F G H K M N P R T V X Z
– –0+–0+– 0+– 0 + – 0 + – 0 + – 0 + – 0 + – 0 +
0 –––00 0+++– – – 0 0 0 + + + – – – 0 0 0 + + +
+ ––––– – – – –0 0 0 0 0 0 0 0 0 + + + + + + + + +
enumerating the monadic ternary functions

https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

2/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

Functions 0, D, and Z are the trivial constant valued functions false, unknown, and true. This enumeration
uses the digit sequence of the standard heptavintimal notation.
In threshold logic, the input i is multiplied by a constant k and then compared to two thresholds t+ and t–. If
ki ≥ t+, the output is +1. If ki ≤ t–, the otuput is -1. Otherwise, the output is 0. Only 17 of the monadic
operators can be computed by threshold logic:
0 1 234 5 6789ABC D EFG H KMN P RTV X Z
k 0 -1 -1 -1 -1
-1 1
1 0 -1
-1 1
1 1
1 1 0
t+ 1 2 1 2 1
02
2 1 1
0 1
1 1
0 0 0
t– 0 0 0 -1 -1
-1 0
-1 -1 -2
-2 0
-1 -2 -1 -2 -1
threshold implementations of monadic functions
Threshold implementations of the constant-valued functions are foolish but are included above for the sake
of completeness. This discussion of threshold logic follows the outline given in [Merrill 1965].

2.1 Buffers and Drivers
The identity function, function P in the enumeration, is realized in hardware in the form of non-inverting
drivers and buffers. In logic diagrams, this function is indicated by the conventional symbol for a driver or
non-inverting amplifier, with an added triangle to mark it as a ternary device.
a
–
0
+

c
–
0
+

c=a

Buffers and Drivers

2.2 Negation
Function 5 in the enumeration above is the ternary equivalent of the Boolean not function. Here, we refer to
this function as the ternary negation or neg function. This inverts its input, returning false when given true
and visa versa, while leaving unknown inputs unchanged. In logic diagrams, inversion is indicated by the
conventional symbol for a Boolean inverter, with an added triangle to mark it as a ternary device.
a
–
0
+

c
+
0
–

c=–a
Negation

Note that, as with Boolean inverters, the symbol is composed of the symbol for a simple buffer or amplifier,
with a bubble on the output indicating inversion. Here, we will never use the bubble to mean anything other
than a fully symmetrical inversion. Numerous authors have proposed practical realizations of ternary
inverters, among them [Doostaregan, Moaiyeri Navi and Hashemipour, 2010; Gorde, 2010; Lin Kim and
Lombardi, 2009; Maley and Walsh, 1972; Mouftah, 1978 Wu and Prosser, 1990].

https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

3/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

Many of these authors refer to realizations of the negation function as the standard ternary inverters or STIs
because there are several other ternary functions that can be implemented as variations on the inverter.
Functions 2, and 8 in our enumeration have been referred to as the negative threshold inverter or NTIs and
positive threshold inverter or PTIs because they invert the true and false values while treating the unknown
input value as either true (NTI) or false (PTI). These can be considered ternary to Boolean conversion
functions because they have purely two-valued outputs.
input NTI PTI
–
+
+ NTI( a ) = (a = –1)
0
–
+ PTI( a ) = – (a = +1)
+
–
–
Alternative Inverters
Some approaches to building ternary logic in hardware lead to realizations of the PTI and NTI functions as
trivial variations on the standard inverter, but in actual use, these functions are not used for inversion, but
rather, they are used as decoders, as discussed in Section 2.4. Furthermore, their outputs are strictly twovalued and therefore, properly speaking, they can be seen as ternary to Boolean converters.

2.3 Increment and Decrement
In Boolean logic, the inverter may be thought of as incrementing or decrementing its argument modulo 2. In
ternary logic, the modulo 3 increment and decrement functions are quite distinct from inversion. These
functions, numbers 7 and B in our enumeration, have been called rotate up and down, as well as cycle and
inverse cycle, with extraordinarily obscure notations, as documented by [Connelly, 2008]. Here, we use the
following notation:
a
–
0
+

c
0
+
–

c = (a + 1)
Increment

a
–
0
+

c
+
–
0

c = (a – 1)
Decrement

The graphical notation given above borrows elements of the traditional Boolean notation for the exclusiveor gate, because of the strong relationship between that operation and modulo-2 addition.
Strictly speaking, we do not need both of these functions, since:
(a – 1) = ((a + 1) + 1) = –(–a + 1)
Note that negation plus increment can be used, in combination, to implement any of the ternary functions
that deliver some permutation of their inputs as outputs; these are also known as reversable functions, since
https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

4/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

each permutation function has some other permutation as its inverse. In our enumeration, functions 7
(increment) and B (decrement) are inverses. Functions 5 (negation), F (unnamed) and M (unnamed) are all
their own inverses, since each of them exchanges two values while leaving the third unchanged. Function P
(identity) is also its own inverse, in a trivial sense, rounding out the 6 possible permutations functions on a
3-valued variable. The exercise of computing the unnamed functions F and M using only negation plus
increment is left as an exercise for the reader.
It is worth noting that the increment and decrement functions cannot be implemented by threshold logic.

2.4 Decoders
Functions 2, 6, and K in our enumeration output true when their input has a specific truth value, and false
otherwise. These functions, can be used to construct decoders, and we refer to them here as decoding
functions, ignoring the PTI and NTI notation and the bizarre superscript notation used by [Mouftah, 1976].
We use the following notation for these functions:
a
–
0
+

c
+
–
–

c = (a = –1)
Is false (NTI)

a
–
0
+

c
–
+
–

c = (a = 0)
Is unknown

a
–
0
+

c
–
–
+

c = (a = +1)
Is true

In the above, note the use of the triangle to indicate that these are ternary functions. The crossbar on the
outputs indicates that the output is strictly two valued, or in other words, the value unknown never appears
on the crossed line. Thus, the C output may be used as an input to a compatible Boolean gate, and when it is
an input to a Ternary gate, the realization of that gate may be simplified because of the lack of a middle
value.
Note that we use the equals sign (=) in two distinct ways: When used at the outer level, we use it to assert
the identity of the expressions on the lefthand and righthand side of the symbol. When used in a parenthetic
expression, we use it for Boolean comparison. In the latter context, we may also use the not-equals sign (≠)
in its conventional Boolean sense.
Strictly speaking, we do not need all of these functions, since:
(a = –1) = (– a = +1) = ((a – 1) = +1)
https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

5/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

(a = 0) = ((a + 1) = +1)
In many cases, we will need to decode two or three of the possible values on a ternary variable. [Kumar and
Priya, 2010] gives a practical implementation of such a decoder, although using an incompatible notation.
The following notation is used here:

Decoder
Functions V, N, and 8 in our enumeration are the inverses of the decoding functions given above. As in
Boolean logic, we use a bubble on the output of a function to indicate inversion, so function 8 can be given
as:
a
–
0
+

c
+
+
–

c = – (a = +1) = (a ≠ +1)
Is not true (PTI)

It is worth noting that the is unknown decoder function cannot be implemented by threshold logic.

2.4 Clamps
There are cases where data in the range from true to false must be converted into the range true to unknown
or unknown to false. Functions C and R in our enumeration do this, but we will not introduce specific
notation for these. Instead, we will use diadic operators do describe these functions.
a
–
0
+

c
–
0
0

c = (a ∧ 0)
Clamp down

a
–
0
+

c
0
0
+

c = (a ∨ 0)
Clamp up

Note that these clamp functions can be extended to diadic and higher fan-in, and that, in implementation,
they may be built by using simple logic gates with output circuitry modified to limit the output swing.

3. Diadic Operators
In conventional Boolean logic, a two input truth table has 4 rows, where each row of the output can take on
two values, giving 16 (that is, 2 to the 4th power) possible functions of 2 variables. With only 16 functions,
https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

6/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

we could reasonably enumerate and name all of them. Of these we usually name only a few, notably the and
and or functions, but also nand, nor and exclusive or.
In ternary logic, a two input truth table has 9 rows, where each row of the output can take on three values,
giving 19,683 (that is, 3 to the 9th power) possible functions of 2 variables. Clearly, this is too many
functions to enumerate, but as with Boolean logic, a few of these functions are worthy of naming.
In threshold logic, each input ij is multiplied by a constant kj and then the inputs are summed and then
compared to two thresholds t+ and t–. If the sum is t+ or greater, the output is +1. If the sum is t–, the output
is –1. According to [Merrill 1965], 471 of the 19,683 diadic ternary operators can be computed using
threshold logic. Given that this is a distinct minority, we will make special note of the cases where threshold
logic can be used in the functions listed below.

3.1 Min or And
It is natural to extend the Boolean and function to a ternary function by declaring that the result is true only
if both inputs are true, false if any input is false, and unknown otherwise. Given that the ternary values are
ordered so that false is less than unknown, which is less than true, the and operator can also be thought of as
returning the minimum of its two operands.
b
– 0 +
– – – –
a 0 – 0 0
+ – 0 +
c

c = (a ∧ b) = min(a, b)

And or Minimum
Here, we adopt the conventional Boolean graphical notation, adding a triangle to the symbol for an and gate
as a badge to indicate the corresponding ternary function. As in Boolean logic, the min function is
commutative and associative, so we may freely take the minimum of any number of terms without
specifying the order of operations, and in graphical notation, we may add any number of extra inputs to the
min symbol instead of drawing a tree of diadic gates.

3.2 Max or Or
Similarly, it is natural to extend the Boolean or function to ternary by declaring that the result is true if any
input is true, false only if both inputs are false, and unknown otherwise. Given the usual ordering of ternary
values where false is less than unknown, which is less than true, the or operator returns the maximum of its
two operands.
b
– 0 +
– – 0 +
a 0 0 0 +
+ + + +
c

c = (a ∨ b) = max(a, b)

Or or Maximum

https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

7/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

Again, we have adopted the conventional Boolean notation, badging the or symbol with a triangle to
indicate that it is a ternary function. As with Boolean logic, the max function is commutative and
associative, so we need not specify the order of operations when combining multiple terms and we may add
extra inputs to the max symbol when used in graphical form.
Note that, as in Boolean logic, DeMorgan's laws still hold in ternary:
(a ∨ b) = – ( – a ∧ – b) or min(a, b) = – max(– a, – b)
(a ∧ b) = – ( – a ∨ – b) or max(a, b) = – min(– a, – b)
As a result, we do not need both the max and min operators, since we can use either one of them, augmented
with negation to make the other.
Also, as in Boolean logic, the and and or functions are distributive:
(a ∨ (b ∧ c)) = ((a ∨ b) ∧ (a ∨ c)) or max(a, min(b, c)) = min(max(a, b), max(a, c))
(a ∧ (b ∨ c)) = ((a ∧ b) ∨ (a ∧ c)) or min(a, max(b, c)) = max(min(a, b), min(a, c))
There is one significant difference between Boolean and ternary logic that these functions introduce: In
Boolean logic, the and, or and not functions taken together form a basis for the entire algebra; that is, any
Boolean function can be expressed solely in terms of these three functions. In fact, because of DeMorgan's
laws, and plus not are sufficient, without the need for or. With ternary logic, there are many functions that
cannot be expressed in terms of min plus max and negation.
Using just min, max and negation, we cannot implement the decoding functions such as is true or is false,
nor can we implement decrement. It turns out, however, that adding any one of these functions to the mix
provides a sufficient basis for building all of the others. The proof is a fun exercise.

3.3 Antimin and Antimax
Hardware implementatios of conventional Boolean logic frequently make it easier to implement the
inverting versions of and and or. This leads naturally to giving these functions their own names, nand and
nor, along with graphical symbols for use in logic diagrams. Several of the proposals for implementing
ternary logic have the same property, leading to the natural use of inverted versions of the min and max
functions, called anti min and anti max. The graphical and algebraic notations for these follow naturally
from the notations introduced above.
b
– 0 +
– + + +
a 0 + 0 0
+ + 0 –
c

c = – (a ∧ b)

Nand or Antimin
b
– 0 +
– + 0 –
a 0 0 0 –
+ – – –
c

https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

c = – (a ∨ b)

8/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

Nor or Antimax
Of course, as in Boolean logic, there is no formal need for these functions.

3.4 Exclusive Or
As with the not function, the exclusive-or function of Boolean algebra has several analogs in the Ternary
realm. Perhaps the least useful of these is the one that follows directly from the conventonal assignment of
values in Kleene logic. If the unknown value is excluded, this version of exclusive or behaves exactly like its
Boolean prototype:
b
– 0 +
– – 0 +
a 0 0 0 0
+ + 0 –
c

c = (a ⊕ b) = xor(a, b)

Ternary Exclusive Or
The notation used here is exactly that of Boolean logic, with a triangle brand on the logic symbol to indicate
that it is ternary. Of course, as in Boolean logic, there is no formal need for this function, since it can be
computed from functions we have already defined:
(a ⊕ b) = ( (a ∧ – b) ∨ (b ∧ – a) )
The exclusive-or function is associative and commutative, but unlike the min and max functions, there is no
natural way to build exclusive-or gates that permits natural expansion to more than two inputs. Therefore,
we will always use the exclusive-or function with just two arguments.

3.5 Sum
In Boolean logic, one use of exclusive or is to compute the modulo 2 sum of two one-bit binary values. The
ternary exclusive-or function defined above does not compute this sum, but we can define a modulo-3 sum
operator that does:
b
– 0 +
– + – 0
a 0 – 0 +
+ 0 + –
c

c = (a + b)

Modulo-3 Sum
We adopt a graphical notation that includes elements borrowed from the Boolean exclusive-or symbol,
badged with a trinagle to indicate a ternary function, but we make a point of adding details that make the
symbol entirely different. In algebraic notation, we use the conventional addition operator, relying on the
global constraint that all values are constrained, modulo 3, to the range from –1 to +1.
The utility of this operator was understood as far back as 1964 [Alexander, 1964]. In that early presentation,
the symbol ⊕ was used, while the inverted exclusive-or operator was described as ternary multiplication and
designated by the symbol ⊗.
https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

9/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

This operator can, of course, be implemented using the operators we have already defined. It is, therefore,
not strictly necessary.
(a + b) = ( (a = –1) ∧ (b – 1) ) ∨ ( (a = 0) ∧ (b) ) ∨ ( (a = +1) ∧ (b + 1) )

In the above, note that the a input effectively controls a 3-input multiplexor that passes either the b input
deccremented, unchanged, or incremented to the output. The sum of products cascade works in ternary logic
exactly the way it works in Boolean logic. Also note that the internal control lines from the decoder to the
min gates in the multiplexor have been marked with crosses at both ends to indicate that they are twovalued.
The above implementation of the modulo-3 sum from simpler gates is ad hoc. As in Boolean logic, we can
implement any ternary function using a canonical sum of products (see Section 4.1).
(a + b) = ( (a = –1) ∧ (b = –1) ∧ +1)
∨ ( (a = –1) ∧ (b = +1) ∧ 0)
∨ ( (a = 0) ∧ (b = 0) ∧ 0)
∨ ( (a = 0) ∧ (b = +1) ∧ +1)
∨ ( (a = +1) ∧ (b = –1) ∧ 0)
∨ ( (a = +1) ∧ (b = 0) ∧ +1)

In the canonical sum of products, there could have been as many as 9 minterms, because there are two 3valued inputs. The minterms with output values of false (-1) were eliminated, leaving only 6 minterms. In
Boolean logic, each minterm would have had just two inputs, but here, we added a third input to each, a
constant indicating the value of the function when that minterm is selected.
https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

10/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

In the logic diagram, we noted which logic values were simple Boolean values by crossing each end of the
corresponding line. Where all the inputs of a logic gate are Boolean, the output of that gate is also Boolean,
so we noted this by omitting the triangle badge. As a result, we determined that compatible Boolean gates
could be used to compute three of the minterms, those corresponding to the true (+1) outputs of the
function. The gates used for the other minterms also have two-valued output, but these are clamped in the
range between false and unknown. Only the final max gate that is used to combine the minterms is a fully
general ternary logic gate.
The sum function is associative and commutative, but as with the exclusive-or function, there is no natural
way to build sum gates with more than two inputs. Therefore, we will always use the sum function with just
two arguments.

3.6 Consensus
In Boolean logic, the inverse of exclusive or is true when the two inputs are the same, and false when they
are different. There are several natural extensions of this idea to ternary logic. One of them is the logical
consensus of a set of variables, which is true if all are true, false if all are false, and otherwise unknown:
b
– 0 +
– – 0 0
a 0 0 0 0
+ 0 0 +
c

c = (a ⊠ b) = cons(a, b)

Consensus
The graphical notation given here includes elements borrowed from the symbols for the Boolean exclusiveor and and gates, badged with the ternary triangle. The similarity to and can be seen by considering the
unknown and false values to be equivalent.
The circled times symbol ⊗ has been used for the consensus operator in 4-valued logic, along with the
circled plus symbol ⊕ for its dual, the accept anything or gullibility operator [Fitting, 1994; Muskens, 1999;
Jacobsz, 2011]. Unfiortunately, the latter symbol has long been used for the exclusive or operator in Boolean
algebra, and our intent here is to build, wherever possible, on analogous Boolean operators. Therefore, we
cannot use ⊕ to mean anything but the ternary analog of exclusive-or. This precludes using it for the ternary
accept anything operator and suggests that we should not use ⊗ for consensus. Instead, we opt to use a
squared times ⊠ and and squared plus ⊞ for consensus and accept anything.
A survey of the literature of ternary logic shows that electrical engineers and computer architects exploring
this logic have not, in general, made any use of the consensus operator, yet it is extremely useful in
constructing arithmetic circuits operating on balanced-ternary numbers, and there is no reason to believe that
it cannot be easily implemented using typical digital electronics.
The consensus function is both commutitave and associative, and there are useful distributive laws that
apply:
((a ⊠ b) ⊠ c) = (a ⊠ (b ⊠ c))
(a ⊠ (b ∧ c)) = ((a ⊠ b) ∧ (a ⊠ c))
(a ⊠ (b ∨ c)) = ((a ⊠ b) ∨ (a ⊠ c))
(a ∧ (b ⊠ c)) = ((a ∧ b) ⊠ (a ∧ c))
https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

11/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

(a ∨ (b ⊠ c)) = ((a ∨ b) ⊠ (a ∨ c))
This operator can be expressed as a canonical sum of products as follows:
(a ⊠ b) = ( (a = –1) ∧ (b = 0) ∧ 0)
∨ ( (a = –1) ∧ (b = +1) ∧ 0)
∨ ( (a = 0) ∧ (b = –1) ∧ 0)
∨ ( (a = 0) ∧ (b = 0) ∧ 0)
∨ ( (a = 0) ∧ (b = +1) ∧ 0)
∨ ( (a = +1) ∧ (b = –1) ∧ 0)
∨ ( (a = +1) ∧ (b = 0) ∧ 0)
∨ ( (a = +1) ∧ (b = +1) ∧ +1)
In Section 4, we will discuss how to systematically minimise this extraordinarily long-winded description of
the function, giving the following result:
(a ⊠ b) = ( a ∧ b ) ∨ ( (a ≠ –1) ∧ 0 ) ∨ ( (b ≠ –1) ∧ 0 )

Unlike exclusive or and sum, there are natural implementations of the ternary consensus function that are as
simple as those that have been widely tested for the max and min functions. Therefore, there is little reason
to implement consensus using the canonical sum of products. Furthermore, these implementations extend
naturally to more than two inputs, so it is reasonable to take advantage of the fact that consensus is both
commutative and associative and use consensus functions with more than two inputs. Here is a schematic
for a resistor-MOSFET inverting consensus gate using the notation of Wu and Prosser, 1990:

c = –(a ⊠ b)

Inverting consensus
In this gate, if the a and b inputs are both below the lower threshold voltage, the upper transistors turn on
and the c output is pulled high. Similarly, if the a and b inputs are both above the upper threshold voltage,
the lower transistors turn on and the c output is pulled low. In all other circumstances, the resistor pulls the c
output toward the middle voltage between the two thresholds. The fan-in of this gate design is limited by the
https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

12/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

number of MOSFETs that may be connected in series; it appears safe to assume that fan-in values exceeding
4 are achievable.
Threshold logic can be used to compute the consensus function using multipliers of +1 on each input and
thresholds of +2 and –2, although practical hardware realizations using multipliers of 0.5 and thresholds of
+1 and –1 are more likely.

3.6 Accept Anything
In four-valued logic, the dual of consensus is an operator usually known as gullibility or accept anything.
Where consensus requires that both inputs agree before it asserts anything but unknown, the accept anything
operator declares an unknown conclusion only if both inputs are unknown or actively disagree. Otherwise, it
jumps to a conclusion from any non-unknown input available to it. While the dual nature of consensus and
accept anything is not evident when we conflate the top and bottom values of four-valued logic into a single
unknown value, a somewhat useful accept anything operator can be defined in ternary logic:
b
– 0 +
– – – 0
a 0 – 0 +
+ 0 + +
c

c = (a ⊞ b) = any(a, b)

Accept anything
The schematic symbol for accept anything reflects the fact that this operator is to or as consensus is to and.
The similarity to exclusive or is deliberate, but with sufficient differences that confusion with that operator
should be unlikely.
The accept anything operator participates in two useful distributive rules:
(a ⊞ (b ∧ c)) = ((a ⊞ b) ∧ (a ⊞ c))
(a ⊞ (b ∨ c)) = ((a ⊞ b) ∨ (a ⊞ c))
However, this ternary accept anything operator is not associative, and it does not participate in other
distributive rules:
((a ⊞ b) ⊞ c) ≠ (a ⊞ (b ⊞ c))
(a ∧ (b ⊞ c)) ≠ ((a ∧ b) ⊞ (a ∧ c))
(a ∨ (b ⊞ c)) ≠ ((a ∨ b) ⊞ (a ∨ c))
(a ⊞ (b ⊠ c)) ≠ ((a ⊞ b) ⊠ (a ⊞ c))
(a ⊠ (b ⊞ c)) ≠ ((a ⊠ b) ⊞ (a ⊠ c))
Threshold logic can be used to compute the accept-anything function using multipliers of +1 on each input
and thresholds of +1 and –1, although practical hardware realizations using multipliers of 0.5 and thresholds
of +0.5 and –0.5 are more likely.

3.7 Comparison
The monadic decoding functions have a natural diadic counterpart, simple comparison for equality. As with
its monadic counterpart, this function of two ternary values has a Boolean value. It is true only if the two
arguments are identical:
https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

13/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

b
– 0 +
– + – –
a 0 – + –
+ – – +
c

c = (a = b)

Equality
The notation given here follows naturally from the notation used for the monadic decoding functions.
Expressing this as an canonical sum of products and minimization are left as exercises for the reader.
Note that the equality operator in Boolean logic is the inverse of the exclusive-or operator. This is not the
case here! In Kleene logic the inverse exclusive-or operator answers the question "are the two operands
equal, to the best of your knowledge?" To this question we can only give a definitive answer if all the inputs
are either true or false. In contrast, the equality operator defined here considers two unknown inputs to be
equal.

4. Minimization
Minimization of ternary logic can be done by generalizing on the conventional minimization algorithm for
Boolean logic. Given an arbitrary function, we begin by expressing it as a truth table, from which we derive
the canonical sum of products. We then merge minterms in order to find a minimal cover for the function.
Unfortunately, the visual shortcut represented by Karnaugh maps does not work for ternary functions of
more than 2 variables, and as with Boolean algebra, the basic optimization problem has exponential
complexity in the number of variables.

4.1 The Canonical Sum of Products
Consider the consensus function described in Section 3.6. Here is the truth table given previously for that
function, with the cells numbered so we can refer to them in what follows:
b
– 0 +
– – 0 0
a 0 0 0 0
+ 0 0 +
⊠

b
– 0 +
– 0 1 2
a 0 3 4 5
+ 6 7 8

cells

Truth table for consensus with cell numbering
Each cell in the truth table can be represented by one minterm in a sum-of-products expression of the
function, as follows:
(a ⊠ b) = ( (a = –1) ∧ (b = –1) ∧ –1)
∨ ( (a = –1) ∧ (b = 0) ∧ 0)
∨ ( (a = –1) ∧ (b = +1) ∧ 0)
∨ ( (a = 0) ∧ (b = –1) ∧ 0)
∨ ( (a = 0) ∧ (b = 0) ∧ 0)
∨ ( (a = 0) ∧ (b = +1) ∧ 0)
∨ ( (a = +1) ∧ (b = –1) ∧ 0)
https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

—0
—1
—2
—3
—4
—5
—6
14/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

∨ ( (a = +1) ∧ (b = 0) ∧ 0)
∨ ( (a = +1) ∧ (b = +1) ∧ +1)

—7
—8

Each row in the above sum-of products is called a minterm because it is the min of several subsidiary terms.
For a 2-input ternary function, the minterms will all have 3 subsidiary terms. Two of these decode the values
of the two input variables, while the third is the value taken from the output cell of the truth table
corresponding to those input values.
For clarity, we have included all 9 minterms for the two-input function we are working with. Note, however,
that one of those minterms will always be false (–1), term number 0. We never need to write out this term,
since it never contributes anything to the value of the function. Omitting this term gives us the canonical
sum of products representation of our function:
(a ⊠ b) = ( (a = –1) ∧ (b = 0) ∧ 0)
∨ ( (a = –1) ∧ (b = +1) ∧ 0)
∨ ( (a = 0) ∧ (b = –1) ∧ 0)
∨ ( (a = 0) ∧ (b = 0) ∧ 0)
∨ ( (a = 0) ∧ (b = +1) ∧ 0)
∨ ( (a = +1) ∧ (b = –1) ∧ 0)
∨ ( (a = +1) ∧ (b = 0) ∧ 0)
∨ ( (a = +1) ∧ (b = +1) ∧ +1)

—1
—2
—3
—4
—5
—6
—7
—8

It is interesting to note that all of the signals from the input decoders to the column of min gates in any
circuit organized as a sum of products are all two-valued. This leads to straightforward implementations of
any terny-to-Boolean and Boolean-to-ternary logic function:
For ternary-to-Boolean conversion, just use purely Boolean logic on the right hand (output) side of the
sum of products.
https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

15/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

For Boolean-to-ternary conversion, just use purely Boolean logic on the left left hand (input) side of
the sum of products.
It is also fair to speculate that the use of Boolean signals between the input decoders and the min gates is
likely less than optimal. There ought to be a systematic methodology for developing minimal
implementations of ternary functions that takes full advantage of ternary logic throughout instead of
descending to an intermediate Boolean layer.

4.2 Combining Minterms
Simplification of the function begins by searching the table of minterms, examining every triplet of 3 terms
that differ in exactly one of the inputs to the function and have the same output. For a 2-input function, the
triplets we are interested in are: Minterms {0,3,6} {1,4,7} and {2,5,8}, since these differ in only the value of
the first variable, and minterms {0,1,2}, {3,4,5} and {6,7,8}, since they differ only in the value of the
second variable. In the event that there are minterms for which the function's output is irrelevant, these can
be taken to be equal to every other value where such equality would allow terms to be combined.
For each of these triplets where the output is the same, do the following: Introduce a new minterm omitting
the variable that differs, and with the constant representing the function's output set to the minimum value of
the outputs of the minterms being combined, and also mark all of the combined minterms that have that
same output value. The marking is to indicate that those combined minterms are covered by the new one.
For our example, as we begin work, we get the following result after two such reductions:
(a ⊠ b) = ( (a = –1) ∧ (b = 0) ∧ 0)
∨ ( (a = –1) ∧ (b = +1) ∧ 0)
∨ ( (a = 0) ∧ (b = –1) ∧ 0)
∨ ( (a = 0) ∧ (b = 0) ∧ 0)
∨ ( (a = 0) ∧ (b = +1) ∧ 0)
∨ ( (a = +1) ∧ (b = –1) ∧ 0)
∨ ( (a = +1) ∧ (b = 0) ∧ 0)
∨ ( (a = +1) ∧ (b = +1) ∧ +1)
∨ ( (b = 0) ∧ 0)
∨ ( (a = 0) ∧ 0)

—1*
—2
—3*
— 4 **
—5*
—6
—7*
—8
— 1, 4, 7
— 3, 4, 5

In the above, we have reduced one column (minterms {1,4,7}) and one row (minterms {3,4,5}) of our
original truth table. As a result, minterm 4 has been covered twice. The minterms covered by the two
reductions we made had all of their outputs the same, so all of the covered minterms have been marked with
a star. All of these reductions would have been permitted in conventional Boolean logic minimization.
We can make two more reductions that do not have identical outputs and would not, therefore, have been
permitted in Boolean logic. In these cases, we only star the minterms that have outputs identical to the
output of the reduced term:
(a ⊠ b) = ( (a = –1) ∧ (b = 0) ∧
∨ ( (a = –1) ∧ (b = +1) ∧
∨ ( (a = 0) ∧ (b = –1) ∧
∨ ( (a = 0) ∧ (b = 0) ∧
∨ ( (a = 0) ∧ (b = +1) ∧
∨ ( (a = +1) ∧ (b = –1) ∧

0)
0)
0)
0)
0)
0)

https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

—1*
—2*
—3*
— 4 **
— 5 **
—6*
16/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

∨ ( (a = +1) ∧ (b = 0) ∧ 0)
∨ ( (a = +1) ∧ (b = +1) ∧ +1)
∨ ( (b = 0) ∧ 0)
∨ ( (b = +1) ∧ 0)
∨ ( (a = 0) ∧ 0)
∨ ( (a = +1) ∧ 0)

— 7 **
—8
— 1, 4, 7
— 2, 5, 8
— 3, 4, 5
— 6, 7, 8

If our function had more input variables, we would repeat the above steps comparing our reduced minterms
with each other in order to see if any of them could be combined. When we make such combinations, we
follow the exact same rules, starring the terms that were combined.
Once all minterms that can be combined are combined, we eliminate all of the starred terms, since each of
them is covered by one of the reduced minterms. This gives us the following result:
(a ⊠ b) = ( (a = +1) ∧ (b = +1) ∧ +1)
∨ ( (b = 0) ∧ 0)
∨ ( (b = +1) ∧ 0)
∨ ( (a = 0) ∧ 0)
∨ ( (a = +1) ∧ 0)

—8
— 1, 4, 7
— 2, 5, 8
— 3, 4, 5
— 6, 7, 8

When there are more inputs to the function, it is possible that one or more of the combined minterms may be
entirely covered by other combined minterms. In such cases, these redundant minterms may be eliminated,
although eliminating these redundant minterms may lead to glitches in the output of a function when one of
its inputs changes, leading to potentially undesirable behavior in sequential circuits.
We can perform one more reduction. If two of our combined minterms have the same output and differ in
just one input variable, we can replace them with a single minterm that replaces two comparisons for
equality with one comparison for inequality. This gives us the following:
(a ⊠ b) = ( (a = +1) ∧ (b = +1) ∧ +1)
∨ ( (b ≠ –1) ∧ 0)
∨ ( (a ≠ –1) ∧ 0)

—8
— 1, 4, 7, 2, 5, 8
— 3, 4, 5, 6, 7, 8

This optimization is not guaranteed to pay off. For example, if we end up needing both (a=+1) and (a≠+1),
the need for an extra decoding function could offset the elimination of a minterm.
https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

17/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

There are some final optimizations: Wherever we included the literal true in a minterm, we can eliminate it.
In addition, in rare cases such as this example, we can replace ((a=+1)∧(b=+1)) with (a∧b). This is only
possible when the truth table for the entire function covers the truth table for the min function -- that is, all
of the minterms of the function in question have output values greater than or equal to the corresponding
terms of the min function. The net result of applying these two optimizations is:
(a ⊠ b) = ( a ∧ b)
∨ ( (b ≠ –1) ∧ 0)
∨ ( (a ≠ –1) ∧ 0)

—8
— 1, 4, 7, 2, 5, 8
— 3, 4, 5, 6, 7, 8

Drawing this in circuit diagram form, we get the following optimized result:

The minimization rules given here are comparable to the rules given in [Yoeli and Rosenfeld, 1965]. That
work presents both 2 and 3 variable analogs of Karnaugh maps as well as tabular methods. [Kumar and
Priya, 2010] also attempted to apply Karnaugh maps to ternary functions, but then focused on a completely
different approach to minimization, attempting to minimize the number of multiplexors needed in a
multiplexor tree implementation of a ternary function. This may be useful on occasion, but in general, the
pure sum of products solutions produced by the tabular methods given here will produce faster logic
because the number of gate delays is always three, a delay for decoding followed by one delay for the
minterms and then the final max operation used to combine the minterms.

4.3 Shorthand Notation
The exercise above was done using algebraic notation, but it is easier to do this with truth tables. We start
with a conventional truth table for the function, with the rows numbered:
inputs outputs
a b a⊠b
– –
–
0
– 0
0
1
– +
0
2
0 –
0
3
0 0
0
4
0 +
0
5
+ –
0
6
+ 0
0
7
+ +
+
8
Truth table for consensus
Now, we begin to identify triples of rows in the truth table that have the same output for all three values of
one of the input variables. When we find such a triplet of rows, we star those rows and add a new row at the
https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

18/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

bottom, keeping a record, with each added rows, of what rows it covers. After two such steps, we have the
following:
inputs outputs
a b a⊠b
– –
–
0
– 0
0
1 *
– +
0
2
0 –
0
3*
0 0
0
4**
0 +
0
5*
+ –
0
6
+ 0
0
7 *
+ +
+
8
0
0
3,4,5
0
0
1,4,7
Table for consensus, after two steps
The reason we put a star on each of the new rows is to keep track of which rows above were combined to
make that row. We also added a horizontal line separating the original truth table from the new rows.
The next step is less obvious. Here, identify triples of rows in the truth table that have outputs of either 0 or
+1 for all three values of one of the input variables. In these cases, we mark the rows with an asterisk where
the output is 0 and with an x where the output is +1, and we add a new row at the bottom, again, eliminating
the input variable that allowed the combination and giving it an output of 0. We can do this twice:
inputs outputs
a b a⊠b
– –
–
0
– 0
0
1 *
– +
0
2 *
0 –
0
3*
0 0
0
4**
0 +
0
5* *
+ –
0
6 *
+ 0
0
7 **
+ +
+
8 xx
0
0
3,4,5
0
0
1,4,7
+
0
6,7,8
+
0
2,5,8
Table for consensus, after four steps
There are no more input eliminations possible in our example, so we can now re-write the table, dropping all
of the rows that have outputs of –1 and also dropping all of the starred rows. The rows marked with x marks
must be retained in order to force an output of +1 where one of the new rows would otherwise output a zero.
We also eliminate all of our bookkeeping comments at this point, giving the following simplified table:
inputs outputs
a b a⊠b
+ +
+
0
0
https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

19/20

2/14/26, 10:00 PM

Douglas W. Jones on Ternary Logic

inputs outputs
a b a⊠b
0
0
+
0
+
0
Table for consensus, after row
elimination
If we had more variables, we might be able to repeat the same basic process on the new rows of the table,
combining some of them to eliminate additional input variables. If we did that, we would add an additional
horizontal line dividing the results of the second elimination round from the first.
At this point, we have the optimal sum-of-products form, identical to the version with 5 minterms that we
already derived using algebraic notation. We could also have applied a more graphical approach, analogous
to the Karnaugh maps used with Boolean logic, but this would not generalized to functions of more than 2
variables (just as Karnaugh maps generalize poorly to functions of more than 4 variables). The payback for
using 2-variable Karnaugh is so small that we ignore the possibility.

4.4 Evaluating the Complexity of the Result
When ternary functions are expressed in sum-of-products form, it is important to note that all of the min
gates used to decode the minterms are actually simple Boolean and gates. The variable inputs to these gates
are all Boolean, either true or false, with the unknown value excluded. Where the constant input is +1, the
output is also Boolean. Where the constant input is 0, this does not require the use of a ternary min, rather,
the constant input serves to clamp the output between false (-1) and unknown (0). As such, an and gate with
its output limited to this range is all that is required.
From this, we conclude that our sum-of-products methodology only requires a single ternary max gate for
each output, plus ternary to Boolean decoders for each input. As a result, when comparing the Boolean logic
realization of some higher-level function with its ternary realization, the number of minterms in the Boolean
version can be directly compared with the number of minterms in the Ternary version.

https://homepage.divms.uiowa.edu/~jones/ternary/logic.shtml

20/20

www.ietdl.org
Published in IET Computers & Digital Techniques
Received on 12th September 2013
Revised on 19th June 2014
Accepted on 29th July 2014
doi: 10.1049/iet-cdt.2013.0133

ISSN 1751-8601

Truncated ternary multipliers
Behrooz Parhami
Department of Electrical and Computer Engineering, University of California, Santa Barbara, CA 93106-9560, USA
E-mail: parhami@ece.ucsb.edu

Abstract: Balanced ternary number representation and arithmetic, based on the symmetric radix-3 digit set {−1, 0, +1}, has been
studied at various times in the history of computing. Among established advantages of balanced ternary arithmetic are
representational symmetry, favourable error characteristics and rounding by truncation. In this study, we show an additional
advantage: that of lower-error truncated multiplication with the same relative cost reduction as in truncated binary multipliers.

1

Introduction

Binary, and more generally radix-2h, arithmetic is
predominant in digital systems, to the extent that we seldom
question its superiority or optimality. Decimal arithmetic,
which until recently was mostly implemented by means of
software, has emerged as a candidate for hardware
realisation, with a variety of proposed representations,
algorithms and design methods [1]. Radices other than
2h and 10 have been mostly ignored.
Early in the history of electronic computers, the choice of
number representation radix was given much attention, with
the binary system prevailing at the end [2, 3]. Historically,
ternary (radix-3) representation came quite close to being
chosen over binary as the preferred method, eventually
losing by a narrow margin. It was argued that under some
fairly realistic assumptions about circuit cost and latency,
the radix 3 is closer to the theoretically optimal radix e than
any other integer radix. However, practical engineering
considerations favoured radix-2 over radix-3 [4].
Despite the negative outcome above, the Setun computer,
working with balanced ternary arithmetic, was built in 1958
at Moscow State University and found to be quite usable
and competitive [5]. The TERNAC computer [6],
implemented at State University of New York, Buffalo in
1973, emulated ternary arithmetic operations by representing
each ternary number as two binary numbers, one positive
and the other negative. Other ternary arithmetic systems and
projects, in simple or extended form, have appeared [7–11].
Most such proposals envisage multivalued signals to encode
the digit values in balanced or standard ternary.
Unfortunately, multivalued signalling and logic, extensively
studied within a research community with conferences and a
specialised journal, and practically available for decades, has
proven uncompetitive in most instances.
The history of a balanced ternary number system and
arithmetic goes further back than the efforts just cited. In
1820, John Leslie [12] presented methods for computing in
any radix, with an arbitrary digit set. Two decades later,
Augustin Cauchy discussed signed-digit numbers in various
IET Comput. Digit. Tech., 2015, Vol. 9, Iss. 2, pp. 101–105
doi: 10.1049/iet-cdt.2013.0133

bases and Leon Lalanne followed by expounding on the
virtues of balanced ternary numbers. In 1840, Thomas
Fowler (1777–1843), a contemporary of Charles Babbage,
chose balanced ternary to build his calculating machine in
England [13].
A balanced ternary fraction x = (x−1 x−2… x−k)three, with
each xi being from the digit set {−1, 0, +1}, denotes the
value Σ−k ≤ i ≤ − 1 xi3i. Values of such k-digit fractions go
from −(1 − 3–k)/2 to (1 − 3–k)/2, a fully symmetric range
approximated by (−0.5, 0.5). Negation, or change of sign,
is a digit-wise operation. Addition of balanced ternary digits
produces a sum and a carry, both of which are of the same
kind. The product of two such digits is similarly a balanced
ternary digit. Thus, ternary arithmetic produces block
diagrams that are identical to the corresponding binary
operations: only circuit-level details within digit-operators
change. Balanced ternary arithmetic has favourable error
characteristics compared with binary. Chopping produces a
maximum error of <1/2 ulp (where ‘ulp’, or ‘unit in least
position’, is r −k when we keep k fractional digits in radix-r
representation), leading to simpliﬁed rounding in
ﬂoating-point arithmetic.
The foregoing history and list of advantages provide
motivation for investigating other potential beneﬁts of
balanced ternary arithmetic. In this paper, we expose one
such advantage in performing truncated multiplication.
Before proceeding with the main topic of truncated
multiplication, we should note that the implementation of
radix-3 arithmetic with its three-valued digits does not
necessarily entail using ternary logic [14], in the same way
that decimal or other higher-radix arithmetic systems do not
necessitate the use of ten-valued or other non-standard
signalling and logic devices. Even though ternary logic is a
good match to the digit set used in balanced ternary
arithmetic, implementations with binary logic are likely to
be more practical and cost-effective in the near future.
Research on ternary logic has subsided since its peak in the
1980s, which included the study of low-power metal-oxide
semiconductor (MOS) variants [15], but there has been a
steady stream of new results over the past three decades,
101

& The Institution of Engineering and Technology 2015

www.ietdl.org
both with mature IC technologies (e.g. [16]) and with less
conventional and emerging nanotechnologies (e.g. [17]).

2

Denoting 1/r by z, the sums within square brackets can be
replaced by their closed-form equivalents
z + z2 + z3 + · · · + zk = z(1 − zk )/(1 − z)

Truncated binary multiplication

Array and tree multipliers for k-bit fractional operands x and y
typically begin by generating the k 2 bitwise product terms xiyj
and then proceed to compress these bits into two rows of bits
(carry-save result) for ﬁnal processing by a carry-propagate
adder [18]. The ﬁnal exact result is a 2k-bit fraction. If we
need a k-bit fraction as the ﬁnal product, as is the case in
many signal processing applications, then the 2k-bit result
can be rounded to a k-bit result to obtain the most precise
possible k-bit value. Alternatively, if a slight error in the
ﬁnal k-bit product is tolerable, some of the discarded k bits
at the lower end of the exact 2k-bit result can be ignored
(not produced) to save on the compression and ﬁnal
addition costs [19]. This strategy often reduces latency and
power dissipation as well [20].
Referring to Fig. 1, which depicts an 8 × 8 fractional binary
multiplication, we note that up to half of the bitwise product
terms to the right of the grey vertical line can be dropped at
the cost of a few ulps of error in the ﬁnal result. If we
simply do not produce those dots, that are collectively
worth 8 ulp/2 + 7 ulp/4 + 6 ulp/8 + 5 ulp/16 + 4 ulp/32 + 3
ulp/64 + 2 ulp/128 + ulp/256 = 7.004 ulp, we can reduce the
cost, latency and power requirements of the multiplier at the
expense of losing <4 bits of precision in the worst case.
The expected error would be about 7.004/4 ulp = 1.751 ulp,
a precision loss of a tad under 2 bits.
More generally, for a k × k fractional multiplication, with
the partial product terms truncated after position −k, the
maximum error εmax, in units of ulp, is
1max = k/2 + (k − 1)/22 + (k − 2)/23 + · · · + 1/2k


= k 1/2 + 1/22 + 1/23 + · · · + 1/2k


− (1/4) 1 + 2/2 + 3/22 + · · · + (k − 1)/2k−2
Instead of evaluating the expression above, it is easier for our
needs later in this paper to evaluate the more general radix-r
version, where the maximum magnitude of a dropped dot is
m, and then setting r = 2 and m = 1.


1max = m k/r + (k − 1)/r2 + (k − 2)/r3 + · · · + 1/rk


= mk 1/r + 1/r2 + 1/r3 + · · · + 1/rk


− (m/r2 ) 1 + 2/r + 3/r2 + · · · + (k − 1)/rk−2

1 + 2z + 3z2 + · · · + (k − 1)zk−2


= d z + z2 + z3 + · · · + zk−1 /dz


= d z(1 − zk−1 )/(1 − z) /dz


= 1 + (k − 1)zk − kzk−1 /(1 − z)2
Substituting the closed-form expressions above, with z
replaced by 1/r, we can simplify εmax to


1max = m k/(r − 1) − 1/(r − 1)2 + r−k /(r − 1)2

For binary arithmetic, we have r = 2 and m = 1, leading to the
following special case of (*), again in units of ulp
1max (r:2, c:0) = k − 1 + 2−k
The notation ‘c:0’ in the preceding equation means that no
column to the right of the ulp column is formed or
evaluated in the truncated multiplier.
The preceding result shows that the maximum error for
truncated binary multiplication is ∼k − 1, when k is
relatively large, and that for k = 8, the max-error expression
evaluates to 8 − 1 + 2−8 = 7.004 ulp (0.02736 in absolute
terms), matching our earlier result.
Instead of dropping all dots to the right of the ulp column,
we can keep a few columns and drop the rest, in an effort to
reduce the amount of error at the expense of more hardware/
energy and greater latency. For example, if we keep only the
ulp/2 column and drop the rest, the previously calculated
worst-case error is reduced by k/2 ulp, but then we incur an
error of up to ulp/2 when we round off the additional
product bit produced past the ulp column to derive the ﬁnal
k-bit result. Thus, the max error in this case is about half
the previous value
1max (r:2, c:1) = k − 1 + 2−k − k/2 + 1/2 = (k − 1)/2 + 2−k
For the preceding example, the maximum error is 3.504 ulp
for k = 8. This represents a loss of about 2 bits in precision.
The average error in this case is 3.504/4 ulp = 0.851 ulp, a
tad <1 bit loss in precision. The effect of the average or
maximum
error
on
computation
results
is
application-dependent and has been studied by various
researchers in different application contexts [21–23]. An
alternative is to use ﬁxed error compensation to transform
an asymmetric error range [0, ε] to a nearly symmetric
range [−γ, ε − γ], where the worst-case error magnitude is
max(γ, ε − γ), or to use variable compensation to reduce the
error even further. We will discuss these approaches after
discussing ternary multiplication.

3

Fig. 1 Truncated 8 × 8 binary multiplication
102
& The Institution of Engineering and Technology 2015

(∗)

Truncated ternary multiplication

In discussing ternary arithmetic, we opt to represent the three
digit values as N(−1), Z(0), and P(+1) to distinguish digit
values from possible encodings of these values, which may
involve the use of posibits in {0, 1} and negabits in {−1,
0} [24]. Thus, whereas −1 is one of the two possible values
IET Comput. Digit. Tech., 2015, Vol. 9, Iss. 2, pp. 101–105
doi: 10.1049/iet-cdt.2013.0133

www.ietdl.org
of a single negabit, the ternary digit N may have a 2-bit
encoding consisting of a negabit and a posibit. Using the
negabit/posibit scheme, N will be encoded as 10, Z as 00 or
11 and P as 01.
Given that the product of two balanced ternary digits is a
balanced ternary digit (Fig. 2), the multiplication dot
diagram in Fig. 1 remains valid for balanced ternary
multiplication. In fact, the balanced ternary number system
is the only non-binary representation for which the
preceding statement can be made.
If we simply do not produce the dots to the right of the grey
vertical line, that are collectively worth no more than 8 ulp/3
+ 7 ulp/9 + 6 ulp/27 + 5 ulp/81 + 4 ulp/243 + 3 ulp/729 + 2
ulp/2187 + ulp/6561 = 3.750 ulp in magnitude, we can
reduce the cost, latency and power requirements of the
multiplier at the expense of losing the equivalent of about 3
bits of precision in the worst case. Thus, the error because
of truncation is in [−3.750, 3.750] ulp, having the expected
or mean value 0.
More generally, for a k′ × k′ fractional multiplication
truncated after the k′th position, the maximum error
magnitude, in units of ulp, is obtained from (*) as
′

1max (r:3, c:0) = k ′ /2 − 1/4 + 3−k /4
We have used k′ instead of k to denote the number of radix-3
digits to account for the fact that, with comparable dynamic
ranges, radix-2 and radix-3 representations possess different
widths; more on this point later.
The result above shows that the maximum error is ∼k′/2 −
1/4 ulp when k′ is relatively large and that for k′ = 8, the
max-error expression evaluates to 8/2 − 1/4 + 3−8 = 3.750,
matching our earlier result.
Instead of dropping all the dots appearing to the right of
the ulp column, we can keep a few columns and drop the
rest to reduce the amount of error at the cost of more
hardware and greater latency. For example, if we keep
only the ulp/3 column and drop the rest, the previously
calculated worst-case error is reduced by k/3 ulp, but then
we incur an error of up to ulp/2 when we round off the
additional product bit produced past the ulp column.
Thus, the max error in this case is about one-third of the
previous value
1max (r:3, c:1) = k ′ /6 + 1/4 + 2−k

′

This error is 1.587 ulp for k′ = 8. This represents a loss that is
less than the equivalent of 2 bits in precision. The average
error in this case is still 0, given that both the values
dropped and the rounding error are symmetric.

4

Error compensation

In the case of truncated binary multiplication, the error is
uniformly negative, because the dropped bits make the

Fig. 2 Truth table for balanced ternary multiplication
IET Comput. Digit. Tech., 2015, Vol. 9, Iss. 2, pp. 101–105
doi: 10.1049/iet-cdt.2013.0133

result smaller. Referring to the truncated multiplication of
Fig. 1 with worst-case error of εmax (r:2, c:0) = 7.004 ulp,
adding 4 ulp to the result, via inserting a constant ‘1’ in the
column of weight 4 ulp, modiﬁes the error to fall in the
range [−3.004, 4.000], which has a 75.1% smaller
worst-case magnitude. This is an example of constant error
compensation [25].
In the previous example, the error compensation consisted
of inserting a single bit in the partial-product matrix, thus
having a negligible impact on cost and speed. The error
compensation constant 3.5 ulp, or 11.1 ulp in binary, would
make the ﬁnal error more symmetric but it requires the
insertion of 3 bits, including a bit in the position just past
the least-signiﬁcant bit, a position not being formed in this
particular example. The point is that reduction of error
comes with non-trivial costs in terms of circuit complexity
and latency, which must be carefully weighed against the
gain in accuracy.
A number of variable error compensation methods have
also been considered in which the compensation varies
according to some of the operand bits, making the
compensation adaptive and the ﬁnal error smaller [26–32].
Variable compensation often entails analysing average or
mean-square error, rather than maximum or worst-case
error. The latter approach to reducing the expected error
is acceptable in some applications but may create
problems in others. It is possible to base variable
compensating term(s) on the worst-case error, but there is
no simple procedure or algorithm, other than an
exhaustive analysis, to determine the compensation term
(s). It is worth noting that the area cost, latency and
energy penalty for variable compensation methods
increases with a reduction of the target error and tends to
be greater if fully symmetric errors are desired.
In balanced ternary truncated multipliers, constant error
compensation does not make sense because the error is
already symmetric. Variable compensation, however, can be
helpful if the compensation value is of the opposite sign of
the prevailing error. Unlike the binary case, however, such
a compensation scheme cannot be based on a small, ﬁxed
number of digits in the two operands. Intuitively, this is
because positive digits when multiplied by negative digits
produce negative digits. Thus, positive high-order digits in
one operand provide no clue as to the signs of the product
digits to be dropped.
Take the MSDs x−1 and y−1 of the two operands, for
example. In truncated binary multiplication, the values of
x−1 and y−1 are correlated with the density of 1s in the
truncated portion, enabling the designer to insert x−1 and/or
y−1 in appropriate columns to (partially) compensate for the
dropped value. In truncated ternary multiplication, it is
quite possible for the dropped value to be negative despite
both x−1 and y−1 being Ps. So, neither the values of the
MSDs nor the signs of the operands can be used to predict
the sign of the error.
For the 4 × 4 truncated ternary multiplication of Fig. 3, in
which x−1 = y−1 = P, the total worth of the dropped bits is
negative: (−4)3−1 + (−1)3−2 + (+1)3−4 ulp = −1.432 ulp.
This is only slightly less than the maximum possible
negative error −(k/2 − 1/4 + 3−k/4) = −1.753 ulp. We thus
conclude that the signs of MSDs in the two operands, or
the signs of the operands themselves, cannot be used to
predict the direction of the error resulting from truncation.
As a result, variable compensation schemes for ternary
multiplication are likely to be more involved than in the
binary case.
103

& The Institution of Engineering and Technology 2015

www.ietdl.org
Table 1 Maximum error values for radices 2–10

Fig. 3 Example truncated 4 × 4 ternary multiplication

5

r

k″

εmax

106δmax

2
3
4
5
6
7
8
9
10

16.000
10.095
8.000
6.891
6.190
5.699
5.333
5.047
4.816

15.000
4.798
10.222
6.641
10.782
8.299
11.863
9.844
13.069

228.9
73.2
156.0
101.3
164.4
126.7
181.1
150.3
199.6

Generalisation and discussion

Our study of truncated ternary multiplication has revealed yet
another advantage of balanced ternary number representation
and arithmetic: that of smaller and symmetric error in
truncated multipliers. The error reduction, which is
comparable with the amount provided by compensation
schemes in truncated binary multipliers, is achieved at no
added cost, latency or power.
One may think that the advantage arises from the higher
radix and is not speciﬁc to balanced ternary representation.
To show that such a supposition is false, we consider the
(nearly) balanced radix-r digit set [1 − r/2, r/2] if r is even
and [(1 − r)/2, (r − 1)/2] if r is odd. The magnitude of the
product of two digits will reach the maximum value r 2/4
and (r − 1)2/4 in the two cases, respectively. Substituting in
(*), we obtain the following radix-r error in units of ulp
′′

1max (r, c:0) = [r2 /(r −1)2 ][k ′′ (r −1)−1+r−k ]/4, if r is even
′′

1max (r, c:0) = [k ′′ (r −1)−1+r−k ]/4,

if r is odd

Again, the use of k″ in lieu of k in radix-2 and k′ in radix-3 is
to remind us of the fact that the number width depends on r.
We see that the error in units of ulp increases nearly
linearly with the radix-r. However, given that k″ and thus
ulp = r −k″ changes with the radix, it is more appropriate to
compare the absolute errors δmax(r, c:0), given by

dmax (r, c:0) = 1max (r, c:0)r−k

′′

A ﬁnal observation to allow us to numerically compare
absolute errors is that the number k″ of digits in radix-r is
related to the number k of digits in radix-2 by
k ′′ = k( ln 2/ ln r) = 0.693k/ ln r
Putting the last four equations together, we tabulate the
worst-case magnitude of the absolute error for radices 2
through 10 for k = 16 in Table 1. We note that the
maximum error grows as the radix is increased, with odd
radices always being better than the adjacent even radices.
The error advantage of odd radices arises from a smaller
maximum product m, as evident from the two equations for
εmax for even and odd radices. An earlier version of this
paper also included comparisons with k″ (usually not an
integer) rounded to the nearest integer. However, given that
such comparisons between representations of different
precisions is unfair as well as misleading (because of the
more or less random rounding directions and errors for
various values of k), these comparisons were dropped in the
ﬁnal version at the suggestion of the referees. It is hoped
that a more detailed comparative study can be conducted in
104
& The Institution of Engineering and Technology 2015

future to further understanding of the relative merits of
various radices and associated digit sets in designing
truncated multipliers.
The analysis presented so far and reﬂected in the results of
Table 1 is admittedly quite primitive, because it takes only the
maximum error into account. However, unless cost proves to
be a highly non-linear function of the dynamic range, our
conclusions should be safe.
We next present an approximate analysis that shows the
cost and delay of a multiplier with operands in a desired
dynamic range to be increasing functions of the radix-r.
This fact, along with the error results of Table 1, suggests
that there is no point in going beyond r = 3, given increases
in error, cost and delay. Binary multipliers used in practice
have circuit complexity on the order of k 2, or O(k 2) in
complexity theory notation. Asymptotically faster multiplier
designs are known [18], but the constants hidden by the
asymptotic notation make them impractical for
run-of-the-mill multipliers. Their advantages begin to show
up for operands that are hundreds of bits wide, where
truncation schemes do not make sense. In going from k-bit
radix-2 to k″-bit radix-r operands, the cost of forming the
partial products remains virtually the same, as the reduced
value of k″2 relative to k 2 is wiped out by the increase of
the complexity of digit multiplication circuitry from 1
(a single AND gate in radix-2) to O(log2 r) = O(k″2/k 2),
where log r is the number of bits in the binary
representation of a radix-r digit. The rest of the process,
that is, the compression of partial-product bits, increases in
complexity, except in radix-3 with a symmetric digit set,
and in delay, because the product of two radix-r digits,
being two digits wide, doubles the height of the matrix to
be compressed [18].
Based on the foregoing discussion, the fact that balanced
ternary arithmetic offers advantages over both r = 2 and r > 3
is evident from Table 1. Looking at the δmax values in the
last column, which are better indicators of merit than εmax
(stated in units of ulp), we see a factor of 228.9/73.2 = 3.13
improvement in error over radix-2 and a factor of 101.3/73.2
= 1.38 improvement over the next best high-radix truncated
multipliers. Even though one would not choose ternary
arithmetic based solely on advantages in truncated
multiplication, this additional beneﬁt is signiﬁcant and
should be considered in future research on high-radix
arithmetic.

6

Conclusions

A number of advantages of radix-3 arithmetic have been
discovered and explored over the years, including smaller
and symmetric computation errors and ease of rounding.
IET Comput. Digit. Tech., 2015, Vol. 9, Iss. 2, pp. 101–105
doi: 10.1049/iet-cdt.2013.0133

www.ietdl.org
We have pointed out an additional advantage of balanced
ternary arithmetic over other radices, including the
prevalent binary representation, in the design of truncated
multipliers, making it even more attractive for low-cost and/
or low-energy application domains.
One complication with ternary arithmetic arises from the
fact that the sign of a balanced ternary number depends on
all of its digits in the worst case (leading 0s must be
ignored and the sign of the ﬁrst non-zero digit taken as the
number’s sign). However, circuits and design methods
developed in connection with binary signed-digit numbers
[33] can be adapted for this purpose.
We have not offered any hardware implementation or exact
cost/latency modelling in this paper. One reason is that
implementations can be quite varied, with various
organisational choices inﬂuenced by technology (binary
against multivalued logic) as well as application
requirements and characteristics. We hope to be able to
report on hardware implementation and modelling in the
near future, beginning with gate- and transistor-level
combinatorial models of the kind used by Acharyya et al.
[34]. Over time, combined cost/latency/accuracy/energy
models will be developed to allow design choices based on
cost-effectiveness and other composite criteria.
Finally, our analysis uses the simplifying, pessimistic
assumption that all dropped terms can have the worst-case
value simultaneously. This simplifying assumption can
create needlessly large error bounds. More detailed analyses
and computer simulations can be used to derive sharper
bounds for speciﬁc applications and/or implementation
technologies [32].

7

Acknowledgment

Comments by anonymous referees in two rounds of review
led to improvements in content and presentation, including
the inclusion of Table 1 and several new references. The
author is grateful to the referees for their contributions.

8

References

1 Wang, L.K., Erle, M.A., Tsen, C., Schwarz, E., Schulte, M.J.: ‘A survey
of hardware designs for decimal arithmetic’, IBM J. Res. Dev., 2010, 54,
(2), pp. 8:1–8:15
2 von Neumann, J.: ‘First draft of a report on the EDVAC’, IEEE Ann.
Hist. Comput., 1993, 15, (4), pp. 27–75. [Reproduction of the original
1945 report]
3 Burks, A.W., Goldstine, H.H., von Neumann, J.: ‘Preliminary
discussion of the logical design of an electronic computing
instrument’ (Institute for Advanced Study Report, 1947, 2nd edn.)
4 Hayes, B.: ‘Third base’, Am. Sci., 2001, 89, (6), pp. 490–494
5 Klimenko, S.V.: ‘Computer science in Russia: a personal view’, IEEE
Ann. Hist. Comput., 1999, 29, (3), pp. 16–30
6 Frieder, G.: ‘Ternary computers – part 1: motivation & part 2:
emulation’. Proc. Fifth Workshop Microprogramming, 1972, pp. 83–89
7 Halpern, I., Yoeli, M.: ‘Ternary arithmetic unit’, Proc. IEE, 1968, 115,
(10), pp. 1385–1388
8 Eichmann, G., Li, Y., Alfano, R.R.: ‘Optical binary coded ternary
arithmetic and logic’, Appl. Opt., 1986, 25, (18), pp. 3113–3121
9 Stakhov, A.: ‘Brousentsov’s ternary principle, Bergman’s number
system and ternary mirror-symmetrical arithmetic’, Comput. J., 2002,
45, pp. 221–236

IET Comput. Digit. Tech., 2015, Vol. 9, Iss. 2, pp. 101–105
doi: 10.1049/iet-cdt.2013.0133

10 Gundersen, H., Berg, Y.: ‘A novel balanced ternary adder using
recharged semi-ﬂoating gate devices’. Proc. IEEE Int. Symp.
Multivalued Logic, 2006, pp. 18–21
11 Gundersen, H., Berg, Y.: ‘A balanced ternary multiplication circuit
using recharged semi-ﬂoating gate devices’. Proc. 24th Norchip Conf.,
2006, pp. 205–208
12 Leslie, J.: ‘The philosophy of arithmetic: exhibiting a progressive view
of the theory and practice of calculation’ (1820, 2nd edn.) William and
Charles Tait
13 Glusker, M., Hogan, D.M., Vass, P.: ‘The ternary calculating machine of
Thomas Fowler’, Ann. Hist. Comput., 2005, 27, (3), pp. 4–22
14 Parhami, B., McKeown, M.: ‘Arithmetic with binary-encoded balanced
ternary numbers’. Proc. 47th Asilomar Conf. Signals, Systems, and
Computers, 2013, pp. 1130–1133
15 Balla, P.C., Antoniou, A.: ‘Low power dissipation MOS ternary logic
family’, IEEE J. Solid-State Circuits, 1984, 19, (5), pp. 739–749
16 Wu, W.W., Prosser, F.P.: ‘CMOS ternary logic circuits’, IEE Proc.
Circuits Devices Syst., 1990, 137, (1), pp. 21–27
17 Lin, S., Kim, Y.-B., Lombardi, F.: ‘CNTFET-based design of ternary
logic gates and arithmetic circuits’, IEEE Trans. Nanotechnol., 2011,
10, (2), pp. 217–225
18 Parhami, B.: ‘Computer arithmetic: algorithms and hardware designs’
(Oxford, 2010, 2nd edn.)
19 Swartzlander, E.E.: ‘Truncated multiplication with approximate
rounding’. Proc. 33rd Asilomar Conf. Signals, Systems, and
Computers, 1999, pp. 1480–1483
20 Schulte, M.J., Stine, J.E., Jansen, J.G.: ‘Reduced power dissipation
through truncated multiplication’. Proc. IEEE Workshop Low-Power
Design, 1999, pp. 61–69
21 Kidambi, S.S., El-Guibaly, F., Antoniou, A.: ‘Area-efﬁcient multipliers
for digital signal processing applications’, IEEE Trans. Circuits Syst. II,
1996, 43, (2), pp. 90–95
22 Jou, J.M., Kuang, S.R., Chen, R.D.: ‘Design of low-error ﬁxed-width
multipliers for DSP applications’, IEEE Trans. Circuits Syst. II, 1999,
46, (6), pp. 836–842
23 Van, L.-D., Wang, S.S., Feng, W.-S.: ‘Design of the lower error
ﬁxed-width multiplier and its application’, IEEE Trans. Circuits Syst.
II, 2000, 47, (10), pp. 1112–1118
24 Jaberipur, G., Parhami, B.: ‘Efﬁcient realisation of arithmetic algorithms
with weighted collections of posibits and negabits’, IET Comput. Digit.
Tech., 2012, 6, (5), pp. 259–268
25 Schulte, M.J., Swartzlander, E.E.: ‘Truncated multiplication with
correction constant’. VLSI Signal Processing VI, 1993, pp. 388–396
26 Wires, K.E., Schulte, M.J., Stine, J.E.: ‘Variable-correction truncated
ﬂoating point multipliers’. Proc. 34th Asilomar Conf. Signals,
Systems, and Computers, 2000, vol. 2, pp. 1344–1348
27 Strollo, A.G.M., Petra, N., De Caro, D.: ‘Dual-tree error compensation
for high performance ﬁxed-width multipliers’, IEEE Trans. Circuits
Syst. II, 2005, 52, (8), pp. 501–507
28 Van, L.-D., Yang, C.-C.: ‘Generalized low-error area-efﬁcient
ﬁxed-width multiplies’, IEEE Trans. Circuits Syst. I, 2005, 52, (8),
pp. 1608–1619
29 Kuang, S.R., Wang, J.P.: ‘Low-error conﬁgurable truncated multipliers
for multiply-accumulate applications’, Electron. Lett., 2006, 42, (16),
pp. 904–905
30 Petra, N., De Caro, D., Garofalo, V., Napoli, E., Strollo, A.G.M.:
‘Truncated binary multipliers with variable correction and minimum
mean square error’, IEEE Trans. Circuits Syst. I, 2010, 57, (6),
pp. 1312–1325
31 Petra, N., De Caro, D., Garofalo, V., Napoli, E., Strollo, A.G.M.:
‘Design of ﬁxed-width multipliers with linear compensation function’,
IEEE Trans. Circuits Syst. I, 2011, 58, (5), pp. 947–960
32 De Caro, D., Petra, N., Strollo, A.G.M., Tessitore, F., Napoli, E.:
‘Fixed-width multipliers and multipliers-accumulators with min-max
approximation error’, IEEE Trans. Circuits Syst. I, 2013, 60, (9),
pp. 2375–2388
33 Srikanthan, T., Lam, S.K., Suman, M.: ‘Area-time efﬁcient sign
detection technique for binary signed-digit number system’, IEEE
Trans. Comput., 2004, 53, (1), pp. 69–72
34 Acharyya, A., Maharatna, K., Al-Hashimi, B.: ‘Algorithm and
architecture for N-D vector cross product computation’, IEEE Trans.
Signal Process., 2011, 59, (2), pp. 812–826

105

& The Institution of Engineering and Technology 2015

2/14/26, 10:03 PM

Ternary ALU

Go back to the list of projects

Working
ternary ALU
02/12/2019
This article is part of my series of
projects around Ternary
Computing and Processor Design.
Click here to see the list of
projects of this series.

CMOS
Implementation
and Analysis of
Ternary
https://louis-dr.github.io/ternalu3.html

1/32

2/14/26, 10:03 PM

Ternary ALU

Arithmetic
Logic Unit
Louis Duret-Robert, Graduate Student
in Electrical and Computer
Engineering at Gerogia Institue of
Technology
Abstract – Ternary logic is an alternative
to binary logic used in every modern
processor. As a base-3 numerical system
can represent numbers using fewer digits
than in base-2, ternary logic circuits are
theorized to be more compact than
equivalent binary circuits. This increase in
density could lead to a gain in
performance measured in transistor cost,
maximal frequency and energy
consumption. In this project, the details of
balanced ternary algebra are reviewed and
a ternary Arithmetic Logic Unit (ALU) is
designed and built using CMOS chips to
prove the feasibility of large ternary CMOS
circuits. Finally, a theoretical analysis of
the benefits of balanced ternary logic is
presented. The conservative conclusion of
this analysis is that balanced ternary can
be cheaper and faster than equivalent
basic binary logic, however, binary logic
has decades of optimization tricks making
it way cheaper and faster.
https://louis-dr.github.io/ternalu3.html

2/32

2/14/26, 10:03 PM

Ternary ALU

Keywords – ternary computing, processor
architecture, ALU design, many-valued
logic

Introduction
Motivation
Every modern computer uses binary logic,
1s and 0s, for computations. Theoretically,
any numerical base can be used for
computation [1]. The numerical base (or
radix) defines how many digits will be
necessary to represent a certain number,
this is the radix economy and is written as

E(b, N ) for base b and number N and
calculated with the following formula.

E(b, N ) = b⌊1 + logb N ⌋
​

The lowest average radix economy is
reached for base e ≈ 2.72 [2]. The closest
integer base is 3, not 2 ; ternary not
binary, and leads on average to the
smallest radix economy.
Therefore, a computer using ternary logic
could be more efficient by requiring less
digits and less circuitry for a similarly
powerful processor. The most famous
ternary computer was the Setun made by
the soviets in the 1970s and was more
efficient [3]. However, binary processors
are easier to develop and binary won. As
https://louis-dr.github.io/ternalu3.html

3/32

2/14/26, 10:03 PM

Ternary ALU

Moore's law slows down, it might be time
to bring ternary computing back to gain
performance.
Switching to ternary logic requires
redefining a whole new algebra, and a
more complex one as the number of
possible states and thus gates is larger.

Ternary algebra
Ternary values
As the binary set of values is written

B = {0, 1}, the symbol T will be used for
the set of ternary values. There exist
multiple ternary sets of values and thus
multiple algebras : perhaps the most
obvious is unbalanced ternary with

T = {0, 1, 2} ; unknown-state ternary
with T = {F , ?, T } similar to an
epistemological set of truth values and an
extension of the Boolean True-False
interpretation of binary logic ; and
balanced ternary T = {−, 0, +} [4].
Balanced ternary logic will be used in this
report. It allows operations on negative
and positive numbers by default with-out
having to use the ternary equivalent of
two’s complement. Consequently, if we
only use the positive numbers, the range
of possible values is halved. This choice
https://louis-dr.github.io/ternalu3.html

4/32

2/14/26, 10:03 PM

Ternary ALU

benefits unsigned operations over signed
operations.
In practice on an electrical computer,
balanced ternary would be represented by
positive, negative and zero voltage. Exotic
ternary computers could use micro-fluid
direction or light polarization. The use of
ternary logic for quantum computation
will not be discussed in this report.
Analogous to the binary 8-bit byte and 4bit nibble, a 3-trit word can be called a
tribble and a 9-trit word a tryte. The word
tryte has also been used for a smaller 6-trit
word, but does not follow powers of 3. A
byte is two nibbles. A tryte is three tribbles.

One-input gates
In binary, a gate with one input and one
output can be represented as a two by one
matrix.
Input Output
0

1

1

0

Can be written with the matrix

1
[ ]
0
​

Therefore there are 22 = 4 possible oneinput one-output matrices in binary :
Matrix Schematic

https://louis-dr.github.io/ternalu3.html

Description

Name

5/32

2/14/26, 10:03 PM

Ternary ALU

0
[ ]
0

Clear

CLR

1
[ ]
1

Mark

MRK

0
[ ]
1

Identity, buffer or pass

BUF

1
[ ]
0

Inverter

NOT

​

​

​

​

Table 1 : binary one-input gates

Only the last two are useful.
In ternary logic, one-input one-output
gates can be represented with a three by
one matrix. There are 33 = 27 possible
such gates. Here are the meaningful ones
[5].
Matrix Schematic

⎡−⎤
0
⎣+⎦
​

​

⎡+⎤
0
⎣−⎦
​

​

⎡+⎤
+
⎣−⎦
​

​

⎡+⎤
−
⎣−⎦
​

​

⎡+⎤
0
⎣+⎦
​

⎡ 0 ⎤
0
⎣+⎦
​

https://louis-dr.github.io/ternalu3.html

​

​

Description

Identity,
​

​

buffer or pass

Inverter

Name Symbol

BUF

A

NOT

A

PNOT

A^

NNOT

Ǎ

ABS

∣A∣

CLU

⌈A⌉

Positively
​

biased
inverter

Negatively
​

biased
inverter

Absolute
​

​

value

Clamp up

6/32

2/14/26, 10:03 PM

⎡−⎤
0
⎣ 0 ⎦
​

​

⎡ 0 ⎤
+
⎣+⎦
​

​

⎡−⎤
−
⎣ 0 ⎦
​

​

⎡ 0 ⎤
+
⎣−⎦
​

​

⎡+⎤
−
⎣ 0 ⎦
​

​

⎡ 0 ⎤
0
⎣+⎦
​

​

⎡ 0 ⎤
+
⎣ 0 ⎦
​

​

⎡+⎤
0
⎣ 0 ⎦
​

​

Ternary ALU

​

​

​

​

​

​

​

​

Clamp down

CLD

⌊A⌋

Increment

INC

A+

Decrement

DEC

A−

Rotate up

RTU

A╯

Rotate down

RTD

A

Is positive

ISP

A =+

Is zero

ISZ

A =0

Is negative

ISN

A =−

╮

Table 2 : ternary one-input gates

Most of them are only useful in rare
situations when building a processor. We
can also note that ISZ is the same gate as
NNOT. The ones to remember are the
buffer and the three inverter gates.

Two-inputs gates
As with one-input gates, two-inputs gates
can also be represented with a matrix. For
a simple binary OR gate :
https://louis-dr.github.io/ternalu3.html

7/32

2/14/26, 10:03 PM

Ternary ALU
A
B

01
0 01
1 1 1

Can be represented with the matrix

[
There are 22

2

0 1
]
1 1
​

​

= 16 possible binary two-

inputs gates. The three useful ones with
their inverted versions are :
Matrix

[

0
0

[

1
1

[

0
1

[

1
0

[

0
1

[

1
0

​

​

​

​

​

​

Schematic Description Name Symbol

0
]
1

And

1
]
0

Inverted

1
]
1

AND

A×B

NAND

A×B

Or

OR

A+B

0
]
0

Inverted or

NOR

A+B

1
]
0

Exclusive or

XOR

A⊕B

XNOR

A⊕B

​

​

and

​

​

​

0
]
1

Inverted

​

exclusive or

​

​

​

Table 3 : useful binary two-inputs gates

In ternary logic, two-inputs gates are
represented with a three by three matrix.
Thus there are 33

3

= 19683 possible such

gates. Only six useful gates and their
inverted versions will be de-scribed,
however some other gates can be useful
such as some asymmetrical gates (as in

https://louis-dr.github.io/ternalu3.html

8/32

2/14/26, 10:03 PM

Ternary ALU

switching the inputs produces differ-ent
results and the matrix is asymmetrical).

⎡−
−
⎣−
​

⎡+
+
⎣+
​

⎡−
0
⎣+
​

⎡+
0
⎣−
​

⎡−
0
⎣ 0
​

⎡+
0
⎣ 0
​

⎡−
−
⎣ 0
​

⎡+
+
⎣ 0
​

⎡+
0
⎣−
​

⎡−
0
⎣+
​

⎡+
−
⎣ 0
​

https://louis-dr.github.io/ternalu3.html

Matrix

​

​

​

​

​

​

​

​

​

​

​

−
0
0
+
0
0
0
0
+
0
0
−
0
0
0
0
0
0

​

​

​

+⎤
0
−⎦
​

+⎤
+
+⎦
​

−⎤
−
−⎦
​

​

0 ⎤
0
−⎦
​

​

​

​

​

​

​

AND

A×B

AND

A×B

OR

A+B

NOR

A+B

CONS

A⊠B

NCONS

A⊠B

Any

ANY

A⊞B

Inverted any

NANY

A⊞B

Multiplication

MUL

A⊗B

NMUL

A⊗B

SUM

A⊕B

minimum

Inverted and
/ minimum

Or /
​

maximum

Inverted or /
​

maximum

Consensus

consensus

​

​

​

Inverted
​

0 ⎤
+
−⎦
​

Symbol

Inverted

0 ⎤
−
−⎦

+⎤
0
−⎦

Name

​

​

​

​

Description

And /
​

​

0 ⎤
+
+⎦

−⎤
0
+⎦

​

−
0
+

−⎤
0
+⎦

0 ⎤
0
+⎦

​

+
0
−

0
0
0

​

​

−
0
+

0
0
0

​

Schematic

multiplication

​

Addition

​

​

​

9/32

2/14/26, 10:03 PM

⎡−
+
⎣ 0
​

​

+
0
−

​

0 ⎤
−
+⎦
​

Ternary ALU

Inverted
​

addition

NSUM

A⊕B

​

Table 4 : useful ternary two-inputs gates

AND and OR ternary gates are sometimes
called MIN and MAX for obvious reasons.
The MUL gate is also sometimes called
XOR.
The gate symbols used here are similar to
the US binary gate symbols with
modifications for the more complex
operations. In addition, as with the US
symbols, a dot on the output signifies an
inverted output. The small triangle
indicates that it's a ternary gate, to
differentiate between equivalent binary
and ternary gates. The symbols are based
on the binary AND and OR gates : if we
only look at the 2×2 submatrix for zero
and positive inputs of the ternary gates,
some look like binary AND and other like
binary OR, so this is the base used for their
symbols, then alterations are added.

Formulae
Some gates are easy to implement with
few transistors and resistors, while others
require combining other simpler gates.
This increases the cost but also the
transmission time of the signal through
the gate and thus the length of the
https://louis-dr.github.io/ternalu3.html

10/32

2/14/26, 10:03 PM

Ternary ALU

transient before reaching the static phase
with the correct output of the circuit. This
can be a bottleneck for the frequency of a
logic circuit such as a processor.
Therefore, finding the best
implementation of a gate is critical.
To find the formulas of logic gates from
simple ones, I Python script is used to test
every possible combinations of basic logic
gates with simple operation prototypes.
For instance, every combination with the
pattern A★B with ★ a two-inputs gate.
The script searches all the combinations
for the simplest solutions with the smallest
transistor and resistor cost.
As will be explained when looking at the
CMOS implementation of those gates, the
simple one-input gates are BUF, NOT,
NNOT, PNOT as well as CLU and CLD if we
allow the use of diodes. The simple twoinputs gates are NAND, NOR, NCONS and
NANY.
As with binary algebra, many formulae
help implementing the more complex
gates. Some of the formulae are only
useful be-cause they correspond to the
CMOS implementations covered later.

A =A
A =− = Ǎ
https://louis-dr.github.io/ternalu3.html

∣A∣ = A × A
⌈A⌉ = A + (0)
​

11/32

2/14/26, 10:03 PM

Ternary ALU

A =+ = A^

⌊A⌋ = A × (0)

╯

A×B = A + B

A╯ = A

╮

​

╮

╮
A+B = A × B
A = A╯
A + = A ⊞ (+) A ⊠ B = A ⊠ B
​

A − = A ⊞ (−) A ⊞ B = A ⊞ B
A╯= A ⊕ (+) A ⊗ B = A ⊗ B
╮

A = A ⊕ (−) A ⊕ B = A ⊕ B
​

A⊗B = A ⊗B =A⊗ B
​

A╯

╮

╮╯

╮╮

╮

╯╯

= A = A = A╯ = A

A ⊗ B = (A + B ) × ( A + B)
A⊗B = A×B ×A+B
​

​

A⊗B = A+B +A×B
A ⊕ B = (A ⊞ B ⊞ A ⊠ B ) ⊞ A ⊠ B
​

​

​

A⊕B = A⊞B⊞ A⊠B ⊞A⊠B
(A × B) ⊠ (A + B) = A ⊠ B

Basic CMOS
implementations

CMOS chip selection
In order to assess the feasibility of ternary
processors, implementations of the basic
ternary logic gates will be first be
described. Current processors use
Complementary Metal Oxide
Semiconductor (CMOS) logic with both
PMOS and MNOS. Without access to
expensive micro-fabrication, CMOS
circuits will be built using the CD4007
chip. This chip contains three CMOS pairs
https://louis-dr.github.io/ternalu3.html

12/32

2/14/26, 10:03 PM

Ternary ALU

but only one is usable as they are not
independent. This chip comes in a DIP14
package, very useful for tests on
breadboard and for custom PCB with DIP
sockets to change the chip if it breaks
down.
This chip works with voltages up to 15V
so an adjustable dual-rail power supply is
used to test different configurations.

Fundamental gates
The ternary inverter actually comes in
three versions, the neutral NOT and the
positive and negatively biased NNOT and
PNOT, but they don't require more
circuitry : just a single CMOS pair. The
other basic gates have two inputs, thus
two CMOS pairs. For the two-input gates,
the two corresponding transistors of the
two CMOS pairs can either be setup in
parallel or in series. Two configurations for
the NMOS and the PMOS, so four
configurations in total for the two pairs.
Those are the four basic gates : NAND,
NOR, NCONS, NANY [6][7].
Note that the non-inverted two-inputs
gates requires an additional regular
inverter on the output of the simpler
inverted versions.
https://louis-dr.github.io/ternalu3.html

13/32

2/14/26, 10:03 PM

Ternary ALU

Figure 1 : Zener-CMOS implementation of ternary inverters,
ternary NAND, ternary NOR, ternary NCONS and ternary NANY

The CD4007 CMOS pair has a small
negative voltage bias so the power supply
is set to −5V +5.7V . Two 1kΩ resistors
are used between the PMOS and NMOS to
stabilize the output. Additionally, a voltage
shifter using a small 2.2V Zener diode and
a 100kΩ pull-down resistor to ground are
used to create a flat and neutral zero state.
Without the voltage shifter, the neutral
state corresponding to a 0 is on a slope,
making it unstable when using the output
to drive another gate, as can be seen on
figure 2.

Figure 2 : CMOS ternary inverter input/output characteristics

Multiplication gate

https://louis-dr.github.io/ternalu3.html

14/32

2/14/26, 10:03 PM

Ternary ALU

The more complex multiplication gate
requires the combination of the
fundamental gates described above,
following the formula listed previously.

A⊗B =A×B×A+B
​

​

Figure 3 : multiplication gate equivalent circuit

This equivalent circuit uses 7 CMOS pairs
when implementing each gate separately.
Some transistors can be factorized to
reduce the cost of this gate ; however, this
requires transistor-level control of the
circuit which is not possible using the
CD4007 chip. Therefore, this will not be
explored in this paper.
The inverted multiplication gate can be
built using the same number of transistors,
which can be useful in certain circuits.

Addition gate
The addition gate is a critical component
for ALU circuits so a working cheap
implementation is a major issue. As with
the multiplication gate, the sum gate can
be implemented using the fundamental
gates.

A ⊕ B = (A ⊞ B ⊞ A ⊠ B) ⊞ A ⊠ B

https://louis-dr.github.io/ternalu3.html

15/32

2/14/26, 10:03 PM

Ternary ALU

Figure 4 : sum gate equivalent circuit

This equivalent circuit uses 11 CMOS
pairs. However, the inverted version of the
sum gate is cheaper as it uses one less
inverter, thus one less CMOS pair. Again,
some transistors can be factorized to
reduce the cost of this gate.

Ternary ALU design
Basic design
The main operation of the Arithmetic
Logic Unit is the addition. This operation,
as in any numerical base requires a carry
system, a way to propagate the carry from
the addition from one digit to the next. For
the sake of simplicity, a ripple-carry
system will be used in this design and not
a carry-lookahead. That means adding the
two trits of one digit of the words requires
the carry of the previous pair of digits,
therefore we have to wait for the previous
sum to be completed. Consequently, as
the word length increases, so does the
time required for the operation to
complete in a linear way. In a full
processor, this reduces the maximum
frequency, or requires complex timing and
scheduling.
As with binary, we start by creating a halfadder, which add two trits and outputs the
https://louis-dr.github.io/ternalu3.html

16/32

2/14/26, 10:03 PM

Ternary ALU

sum as well as the carry of this operation.
The matrices of the sum and carry of two
trits are given in figure 5. We recognize
the sum of A and B to be the SUM gate and
the carry is the CONS gate.

⎡+ − 0 ⎤ ⎡− 0 0 ⎤
− 0 +
0 0 0
⎣ 0 + −⎦ ⎣ 0 0 +⎦
​

​

​

​

​

​

​

​

​

​

Figure 5 : sum of two trits (left) and carry of two trits (right)

Thus, a ternary half-adder can easily be
built.

Figure 6 : ternary half-adder

Then two half-adders are combined to
create a full-adder to add two trits as well
as the previous carry. The carries of the
two additions also have to be combined
with an ANY gate.

Figure 7 : ternary full-adder

This is the heart of the ALU. The first and
last additions of the chain of digits are
special as they respectively don’t have a
previous carry and don’t have to output a
carry. Therefore, the first digit only
requires one half-adder, and the last one
requires two SUM gates.

https://louis-dr.github.io/ternalu3.html

17/32

2/14/26, 10:03 PM

Ternary ALU

Figure 8 : ternary ALU chain

Some ALU also include a flag signal for the
overflow (when the operation results in a
number outside the range of the
architecture). It can be achieved by
replacing the circuitry of the last digit with
a usual full-adder. This of course increases
the cost.

Subtraction
As explained earlier, balanced ternary logic
allows easy operations using positive and
negative numbers. To negate a ternary
number, the only process is to inverter
every trit. This, an ALU that does only
addition can do subtraction by negating
one of the inputs.

Figure 9 : ALU with negating circuit

A simple circuit to negate a ternary word
uses multiplication gates. Each trit of the
word is fed in a multiplication gate and a
https://louis-dr.github.io/ternalu3.html

18/32

2/14/26, 10:03 PM

Ternary ALU

common signal is used to control the sign
of the output word.

Figure 10 : negating circuit

Optimization
The number of CMOS pairs used for the
ALU circuit can be reduced. Only the
addition circuit will be considered here.
First, the fundamental gate of the ALU is
the SUM gate. The SUM gate costs 11
CMOS pairs. Then to build a half-adder, a
SUM gate and a CONS gate are needed for
a total of 14 CMOS pairs. Then the fulladder requires two half-adders and an
ANY gate, 31 CMOS pairs. The first digit of
the ALU is a single half adder (because
there is no incoming carry trit), 14 CMOS
pairs, and the last digits is two SUM gates
(no output carry trit, even though it is
often the case that the last carry bit in a
binary ALU is stored in a flag for branching
instructions and the ability to do
calculations with multiple words), 22
CMOS pairs ; the rest are full-adders. For a
n-trit ALU (n ≥ 2), the total cost of the
ALU (not including the sign controller
required for subtraction) is 31n − 26
https://louis-dr.github.io/ternalu3.html

19/32

2/14/26, 10:03 PM

Ternary ALU

CMOS pairs. For a 3-trit ALU, that amounts
to 67 CMOS pairs.
We can spare one CONS gate per halfadder by using the NCONS gate in the
SUM gate and adding a NOT gate. That
saves 2 CMOS pairs per half-adder. The
new total cost is 27n − 20 CMOS pairs, 61
CMOS pairs for a 3-trit ALU.

Figure 11 : ternary full-adder

Another economy comes from the
formulae listed previously. If we invert
both inputs of a SUM gate, the output is
unchanged.

A⊠B =A⊠B
A⊞B =A⊞B
A⊗B =A⊗B
A⊕B =A⊕B
The trick is to use inverted gates before
the input, and since those inverted gates
are usually cheaper, we can save
transistors. This is simpler to understand
with diagrams.

Figure 12 : N-half-adder

Here is an alternative half-adder. Two
symbols are used and here is why. The
https://louis-dr.github.io/ternalu3.html

20/32

2/14/26, 10:03 PM

Ternary ALU

circle on the output still means that the
output is inverted compared to the default
gate (here the half-adder). The round cup
on the input is supposed to indicate an
inverter should be present on the input ;
that is, to get the behaviour of the default
gate, we have to invert this input. Here,
the two symbols, taken with the labels, are
the same : to get the behaviour of the
default half-adder, we can either invert
both output or both inputs. This is a direct
consequence of the formulae listed above.
Using this N-half-adder, we can create a
N-full-adder.

Figure 13 : N-full-adder

Again, both N-half-adders on this diagram
correspond to the same internal circuitry
described above. However, on the bottom
one, we feed the original A and B signals,
so we get the inverted sum and inverted
carry of A and B. While on the top one, we
feed in the inverted incoming carry and
the inverted sum from the first N-halfadder, so we get the un-inverted final sum
and the uninverted carry. So, one carry is
inverted and the other is not. To combine
the two carries, we have to invert one and
thus add a NOT gate. Then, to get the
https://louis-dr.github.io/ternalu3.html

21/32

2/14/26, 10:03 PM

Ternary ALU

inverted total carry, a NANY is used, which
is more expensive than the ANY gate.
Finally, the full ALU can be built again. As
expected, the first and last digits are also
different.

Figure 14 : new adder chain

With those modifications, the N-halfadder costs 10 CMOS pairs, the N-fulladder 24 CMOS pairs, the first digit 11
CMOS pairs and the last digit 21 CMOS
pairs. The total and final cost after
optimization is 24n − 16 CMOS pairs, 56
for the 3-trit ALU.
Beside an economy of transistors, the
optimizations also reduce the number of
CMOS pairs the signal has to propagate
through, and thus increases the maximum
frequency of the processor. Calculating
the critical path that will be explained
later, a n-trit ternary ALU has a
propagation delay of 9n − 7 CMOS
propagation delays.

https://louis-dr.github.io/ternalu3.html

22/32

2/14/26, 10:03 PM

Ternary ALU

Further economy could be possible at the
transistor level instead of pairs of
transistors using the CD4007 chips as a
reference.

Physical build of the
ALU
Sourcing materials
The CD4007 chips were bought on iconline.com. The custom PCBs were
designed on EasyEDA and manufactured
by JLCPCB. All other electrical
components were bought from various
suppliers on Aliexpress and eBay.

Ternary 2-trit ALU
In order to verify the feasibility of ternary
logic circuits using CMOS pairs, a 2-trit
ALU with subtraction ability has been built.
It uses almost all the gates described
above including the SUM and MUL gates.

Figure 15 : PCB of the ternary SUM gate using CD4007 chips

https://louis-dr.github.io/ternalu3.html

23/32

2/14/26, 10:03 PM

Ternary ALU

Figure 16 : full circuit of the working 2-trit ALU

A more in-depth description of the design
and testing process as well as a
demonstration of the circuit in action can
be found in the other articles on this
website.

Comparison with binary
Metrics
Performance of processors can be
measured on power consumption,
maximal frequency and cost. Only the
latter two will be compared here.
Maximal frequency is determined by the
longest path of the electric signal in the
circuit, the critical path. The time the
signal takes to propagate through the
circuit can depend on multiple factors, but
only the propagation time of the CMOS
transistors will be considered. The
comparison will be measured using the
number of propagation delays of the
critical path of the circuit. One CMOS
propagation delay will refer to one
propagation delay of the CMOS pair (about
https://louis-dr.github.io/ternalu3.html

24/32

2/14/26, 10:03 PM

Ternary ALU

20ns for the CD4007 for example). Simple
gates such as NOT, NAND, NOR, NCONS
and NANY only require a single CMOS
propagation delay, but the more complex
MUL, SUM and NSUM gates require
respectively 3, 6 and 5 CMOS propagation
delays.
Cost itself can be broken down on
multiple factors. Processor fabrication
costs are increased by the technology
used, area of the die, number of
fabrication steps, etc. In the case of
ternary circuits, the technology is not
explored in this report as it would require
extensive experimenting using microfabrication. The number of transistors
affect directly the area of semiconductor
necessary. The number of fabrication
steps depends in part on the technology
used, and the density of interconnections
between transistors requiring more or less
layers on top of the semiconductor. For
the sake of simplicity and to get a first idea
of a comparison, the cost will be modelled
by the number of CMOS pairs necessary.

Binary ALU design
The ternary ALU described above will be
compared to a binary ALU using a similar
design, that is a n-bit ALU with a ripple
carry system.
https://louis-dr.github.io/ternalu3.html

25/32

2/14/26, 10:03 PM

Ternary ALU

Using similar CMOS architecture, the
binary inverter (NOT) costs a single CMOS
pair, and the binary NAND and NOR twoinputs gates cost two CMOS pairs each. All
three of those gates require a single CMOS
propagation delay
The equivalent of the SUM gate of the
ternary ALU in binary is the XOR gate. If
we were to implement this gate as a
combination of simpler gates (binary
NAND and NOR) as we did for the ternary
SUM gate, we can use the following
formula.

A ⊕ B = A + B × (A × B)
​

​

Figure 17 : binary XOR gate

This brings the cost of this gate to 8 CMOS
pairs. Using binary algebra formulae, we
can deduce that the cost for the XNOR
gate is the same. The propagation delay is
of 3 CMOS propagation delays.
The binary half-adder is built with a XOR
gate for the sum and a AND gate for the
carry. The AND gate inside the COR gate
can be used to spare some transistors.
Two half-adders are used to build the fulladder and an OR gate combines the two
carries.
https://louis-dr.github.io/ternalu3.html

26/32

2/14/26, 10:03 PM

Ternary ALU

Figure 18 : binary full-adder

This full-adder costs 19 CMOS pairs and
has a propagation delay of 6 and 7 CMOS
propagation delays for the sum and the
carry respectively. The first bit of the ALU
only requires a single half-adder and the
last one only two XOR gates using a
similar architecture to the ternary ALU.
However, some processors use a different
implementation of the XOR gate using
Pass Transistor Logic [8], where the
transistors are not connected to the power
supply or ground, but to other gate
outputs. This other logic family allows
substantial cost reductions but also
require more testing as the output of a
PTL gate is not directly connected to the
power supply but has to be able to drive
other gates in the circuit. This can require
additional circuitry. There exist many
different PTL-like technologies such as
Double-Pass Transistor Logic, Swing
Restored Pass Transistor Logic and
Complementary Pass Transistor Logic.
They will not be compared in this report.
However, a common PTL CMOS XOR gate
can be built using only 6 transistors.

https://louis-dr.github.io/ternalu3.html

27/32

2/14/26, 10:03 PM

Ternary ALU

Figure 19 : PTL CMOS binary XOR gate

Thus, the cost of this XOR gate is only 3
CMOS pairs, and the delay is 2 CMOS
propagation delays. As this XOR doesn’t
contain a AND gate, we have to add it.
However, we can use cheaper and faster
NAND gates.

Figure 20 : alternative binary full-adder for the PTL XOR

This full-adder costs 12 CMOS pairs and
has a propagation delay of 4 CMOS
propagation delays for both the sum and
the carry.
Both implementations will be considered
in the comparison. Without PTL logic, a nbit binary ALU (without the subtraction
circuit) costs 19n − 14 CMOS pairs and
has a propagation delay of 7n − 6 CMOS
propagation delays. With PTL logic, a n-bit
binary ALU costs 12n − 13 CMOS pairs
and has a propagation delay of 4n − 3
CMOS propagation delays.

Results

https://louis-dr.github.io/ternalu3.html

28/32

2/14/26, 10:03 PM

Ternary ALU

Plotting the expected cost and
propagation delay for different number of
digits in the three different architectures
as a function of the maximum range of
values, we get the following results.

Figure 21 : cost comparison

Figure 22 : propagation delay comparison

As we can see, while the proposed ternary
ALU is substantially cheaper and faster
than a similar binary ALU for equal
maximum range of values, using Pass
Transistor Logic brings a considerable
advantage to binary over balanced
ternary.

Critical analysis
This comparison hints that ternary logic is
not a worthwhile alternative to binary.
However, binary logic has decades of
advance in research, including PTL
https://louis-dr.github.io/ternalu3.html

29/32

2/14/26, 10:03 PM

Ternary ALU

optimization. Using similar CMOS design,
balanced ternary still presents an
advantage over binary. Therefore, it can
be expected that transistor-level design
optimization applied to ternary logic can
rival current binary processors.
Many assumptions have been made in this
analysis. A more thorough analysis would
require experimenting at the
semiconductor level and take into account
power consumption as well.
Moreover, this project only explores
balanced ternary ALU. Unbalanced ternary
logic might require less complex circuitry
for some components of the processor
such as look-ahead carry systems [9].

Conclusion
Balanced ternary logic can be computed
on CMOS circuitry, as shown with the
realization of the ternary ALU proposed in
this report. It is overall cheaper and faster
than similar basic binary logic, however,
decades of research on transistor-level
optimization allow binary to surpass the
ternary logic presented.
More experimenting with other logic
families such as Transistor Pass Logic
should be carried out to try to match the
https://louis-dr.github.io/ternalu3.html

30/32

2/14/26, 10:03 PM

Ternary ALU

performance of optimized binary circuits.
Research on the realization of ternary
circuits in integrated circuits is required to
conclude more accurately on the potential
gains of ternary logic and its uses.
Unbalanced ternary logic should be
explored and compared to balanced
ternary logic.

References
[1] Stanley L. Hurst. 1984. Multiple-Valued
Logic – its Status and its Future. IEEE
Transactions on Computers. Vol. c-33, No.
12, December 1984.
[2] C.B. Tompkins, J.H. Wakelin,
Engineering Research Associ-ates Inc.
1950. High-speed computing devices.
McGraw-Hill Book Company Inc.
[3] N. Brusentsov, J.R. Alvarez. 2006.
Ternary Computers : The Setun and the
Setun 70. Soviet and Russian Computing.
July 2006.
[4] W. Alexander. 1964. The Ternary
Computer. Electronics and Power. Vol. 10,
Issue 2, February 1964.
[5] Douglas W. Jones. 2012. Standard
Ternary Logic. The Ter-nary Manifesto.
www.cs.uiowa.edu/~jones/ternary.
https://louis-dr.github.io/ternalu3.html

31/32

2/14/26, 10:03 PM

Ternary ALU

[6] H.T. Mouftah. 1976. A Study on the
Implementation of Three-Valued Logic.
Proceedings of the sixth international
sym-posium on multiple-valued logic, May
1976, 123-126.
[7] H.T. Mouftah. 1978. Ternary Logic
Circuits with CMOS Integrated Circuits. US
patent 4,107,549, Aug. 15, 1978.
[8] R.P. MeenaakshiSundari, R. Anita, M.K.
Anandkumar. 2013. Implementation of
Low Power CMOS Full Adders Using Pass
Transistor Logic. IOSR Journal of VLSI and
Signal Processing. Vol. 2, Issue 5 (May. –
Jun. 2013).
[9] Douglas W. Jones. 2012. Fast Ternary
Addition. The Ternary Manifesto.
www.cs.uiowa.edu/~jones/ternary.

This article is part of my series of
projects around Ternary
Computing and Processor Design.
Click here to see the list of
projects of this series.

Go back to the list of projects

https://louis-dr.github.io/ternalu3.html

32/32


