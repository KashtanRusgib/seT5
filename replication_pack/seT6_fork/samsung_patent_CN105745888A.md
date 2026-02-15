2/13/26, 2:02 PM
CN105745888A - Method and system using ternary sequences for simultaneous transmission to coherent and non-coherent...
Patents
Patent CN105745888A
Method and system using ternary sequences for simultaneous transmission to coherent and non-coherent receivers
Abstract
A method and system for simultaneous transmission of data to coherent and non-coherent
receivers is described. The method at a transmitter comprises: retrieving a base ternary sequence
CN105745888A
China
having a predefined length; acquiring one or more ternary sequences corresponding to data to be
transmitted; the acquired one or more ternary sequences are transmitted by the transmitter. The
Download PDF
Find Prior Art
Similar
method steps at the receiver include: receiving one or more ternary sequences corresponding to the
transmitted data; demodulating, by the receiver, each ternary sequence received by correlating all
cyclic shifts of the base ternary sequence if the receiver is a coherent receiver; if the receiver is a
non-coherent receiver, demodulating each ternary sequence received by the receiver by correlating
all cyclic shifts of the absolute value of the base ternary sequence; the transmitted data is detected
Other languages: Chinese
Inventor: 苏吉特·卓斯, 钱德拉西卡·德贾斯威·皮斯, 金然·拜纳姆,
洪永骏, 朴昌淳, 曼奥吉·乔德哈瑞
based on the cyclic shift corresponding to the maximum correlation value.Current Assignee : Samsung Electronics Co Ltd
ClassificationsWorldwide applications
H04L25/03834 Arrangements for spectral shaping; Arrangements for providing signals with
2014 KR WO KR CN CN EP EP US CN CN US EP KR WO JP
2018 US US US 2019 US JP
specified spectral properties using pulse shaping
H04L25/4923 Transmitting circuits; Receiving circuits using code conversion at the
transmitter; using predistortion; using insertion of idle bits for obtaining a desired frequency
spectrum; using three or more amplitude levels ; Baseband coding techniques specific to data
transmission systems using multilevel codes using ternary codes
Application CN201480059814.0A events
2014-10-21Application filed by Samsung Electronics Co Ltd
2014-10-21Priority to CN201911130921.9A
H04B1/709 Correlator structure2016-07-06Publication of CN105745888A
H04L25/03312 Arrangements specific to the provision of output signals2019-11-26Application granted
H04L27/04 Modulator circuits; Transmitter circuits2019-11-26Publication of CN105745888B
StatusActive
2034-10-21Anticipated expiration
H04L27/2278 Demodulator circuits; Receiver circuits using coherent demodulation wherein
the carrier recovery circuit uses the received modulated signals using correlation techniques, e.g.
for spread spectrum signals
H04L27/2678 Blind, i.e. without using known symbols using cyclostationarities, e.g. cyclic
prefix or postfix
Info: Patent citations (80), Non-patent citations (3) , Cited by (9),
Legal events, Similar documents, Priority and Related
Applications
H04B1/71637 Receiver aspects
H04W28/18 Negotiating wireless communication parameters
External links: Espacenet, Global Dossier, Discuss
Y02D30/70 Reducing energy consumption in communication networks in wireless
communication networks
Hide more classifications
Landscapes
Engineering & Computer Science
Computer Networks & Wireless Communication
Show more
Claims (28)
Hide Dependent
translated from Chinese
1. A method of sending data, comprising: Retrieves a base ternary sequence with a predefined length; obtaining one or more ternary sequences corresponding to the data to be
transmitted from the base ternary sequence; One or more ternary sequences acquired by the sender. 2. The method of claim 1, wherein the data is in binary form. 3. The method of
claim 1 , wherein the step of deriving from the base ternary sequence one or more ternary sequences corresponding to the data to be transmitted comprises: dividing the data to be
transmitted into one or more data symbols with a predefined length; Each data symbol is mapped to a ternary sequence obtained by providing a cyclic shift to the base ternary
sequence, wherein the amount of the cyclic shift is determined based on a one-to-one mapping. 4. The method of claim 1, further comprising: Generate a base ternary sequence
with a predefined length; Store the base ternary sequence in memory. 5. The method of claim 4, wherein the step of generating the base ternary sequence comprises: Selecting a
seed sequence of a predefined length, wherein the seed sequence is one of the m-sequence and the complement of the m-sequence; If the weights of the seed sequence are
perfect square numbers, a perfect ternary sequence is generated from the seed sequence; produces a near-perfect ternary sequence from the seed sequence if the weight of the
seed sequence differs from a perfect square number; Inserts a predefined value at a predefined position in one of a perfect ternary sequence and a near-perfect ternary sequence to
produce a base ternary sequence. 6. The method of claim 5, wherein, if the weight of the seed sequence is a perfect square number, then the step of generating a perfect ternary
sequence from the seed sequence comprises: Obtain the preferred pair of m sequences from the seed sequence; obtaining a correlation sequence of a preferred pair, wherein the
https://patents.google.com/patent/CN105745888A/en?oq=Patent+CN105745888A
1/132/13/26, 2:02 PM
CN105745888A - Method and system using ternary sequences for simultaneous transmission to coherent and non-coherent...
correlation sequence is obtained as a cross-correlation function between said two sequences of the preferred pair; Obtain offset correlation sequences from corresponding
correlation sequences; Offset-based correlation sequences yield perfect ternary sequences. 7. The method according to claim 6, wherein the step of obtaining the preferred pair of
m sequences from the seed sequence comprises: Selecting the seed sequence as the first m sequence of the preferred pair; Obtain the second m sequence of the preferred pair,
where the second sequence is the decimal form of the predefined first sequence. 8. The method of claim 5, wherein, if the weight of the seed sequence is different from a perfect
square number, the step of generating a near-perfect ternary sequence from the seed sequence comprises: Obtain one or more candidate sequences by inverting the value of one
or more non-zero positions in the seed sequence for a predefined ratio; Sequences are selected from candidate sequences as near-perfect ternary sequences based on the
minimum value of the mean squared autocorrelation coefficient (MSAC). 9. The method of claim 5, wherein the predefined positions for inserting predefined values into one of a
perfect ternary sequence and a near-perfect ternary sequence to generate a base ternary sequence are all possible The position corresponding to the minimum MSAC value among
the positions of . 10. The method of claim 5, wherein, if the seed sequence is an m-sequence, the predefined value inserted into one of the perfect ternary sequence and the near-
perfect ternary sequence is the value "0"; If the seed sequence is the complement of the m-sequence, the predefined value for inserting one of the perfect ternary sequence and the
near-perfect ternary sequence is the value "1". 11. A method of receiving data sent from one or more transmitters, comprising: receiving, by a receiver, one or more ternary
sequences transmitted from said one or more transmitters; demodulating the received one or more ternary sequences using a base ternary sequence; Data transmitted from the
one or more transmitters is detected. 12. The method of claim 11, wherein the one or more ternary sequences correspond to one or more data symbols having a predefined length.
13. The method of claim 12, wherein one or more data symbols constitute data sent from one or more transmitters. 14. The method of claim 11 , wherein demodulating the
received one or more ternary sequences using a base ternary sequence comprises: If the receiver is a coherent receiver, each received ternary sequence is demodulated by the
receiver by associating the received ternary sequence with the full cyclic shift of the base ternary sequence; If the receiver is a non-coherent receiver, each ternary sequence
received is demodulated by the receiver by associating the received ternary sequence with the full cyclic shift of the absolute value of the base ternary sequence. 15. The method of
claim 11 , wherein detecting data transmitted from the one or more transmitters comprises: identifying a single cyclic shift corresponding to a maximum correlation value among
all cyclic shifts; Each data symbol is retrieved from the single cyclic shift by mapping the single cyclic shift back to a data symbol using an inverse of the one-to-one mapping. 16.
The method of claim 11, further comprising: Generate a base ternary sequence with a predefined length; Store the base ternary sequence in memory. 17. The method of claim 16,
wherein the step of generating a base ternary sequence comprises: Selecting a seed sequence of a predefined length, wherein the seed sequence is one of the m-sequence and the
complement of the m-sequence; If the weights of the seed sequence are perfect square numbers, a perfect ternary sequence is generated from the seed sequence; produces a
near-perfect ternary sequence from the seed sequence if the weight of the seed sequence differs from a perfect square number; Inserts a predefined value at a predefined position
in one of a perfect ternary sequence and a near-perfect ternary sequence to produce a base ternary sequence. 18. The method of claim 17, wherein, if the weight of the seed
sequence is a perfect square number, the step of generating a perfect ternary sequence from the seed sequence comprises: Obtain the preferred pair of m sequences from the
seed sequence; obtaining a correlation sequence of a preferred pair, wherein the correlation sequence is obtained as a cross-correlation function between said two sequences of
the preferred pair; Obtain offset correlation sequences from corresponding correlation sequences; Offset-based correlation sequences yield perfect ternary sequences. 19. The
method of claim 17, wherein the step of using the seed sequence to obtain the preferred pair of m-sequences comprises: Selecting the seed sequence as the first m sequence of
the preferred pair; Obtain the second m sequence of the preferred pair, where the second sequence is the decimal form of the predefined first sequence. 20. The method of claim
17, wherein, if the weight of the seed sequence is different from a perfect square number, the step of generating a near-perfect ternary sequence from the seed sequence
comprises: Obtain one or more candidate sequences by inverting the value of one or more non-zero positions in the seed sequence for a predefined ratio; At least one sequence is
selected from the candidate sequences as a near-perfect ternary sequence based on the minimum value of the mean square autocorrelation coefficient (MSAC). 21. The method of
claim 17, wherein the predefined positions for inserting predefined values into one of a perfect ternary sequence and a near-perfect ternary sequence to generate a base ternary
sequence are all possible The position corresponding to the minimum MSAC value among the positions of . 22. The method of claim 17, wherein, if the seed sequence is an m-
sequence, the predefined value inserted into one of a perfect ternary sequence and a near-perfect ternary sequence is the value "0"; If the seed sequence is the complement of the
m-sequence, the predefined value inserted into one of the perfect ternary sequence and the near-perfect ternary sequence is the value "1". 23. A transmitter comprising: data entry
module; sending module; a symbol generation module, in combination with the data input module, adapted to generate one or more symbols based on the input data; The ternary
sequence generation module is combined with the symbol generation module; base ternary sequence retrieval module; a cyclic shift generation module, wherein the base ternary
sequence retrieval module retrieves one or more base ternary sequences corresponding to the generated symbols; The cyclic shift generation module is adapted to generate a
cyclic shift in the base ternary sequence based on the generated symbols. 24. A base ternary sequence generation module, comprising: The seed sequence selection module is
adapted to: select the seed sequence as the first sequence of the preferred pair, and select the second sequence of the preferred pair, wherein the second sequence is the decimal
form of the predefined first sequence; Predefined values are inserted into the module. 25. The base ternary sequence generation module of claim 24, wherein, if the seed sequence
is an m sequence, the perfect ternary sequence generation module is adapted to generate a perfect ternary sequence from the seed sequence, wherein the perfect ternary
sequence The generation of base sequences includes: Obtain the preferred pair of m sequences from the seed sequence; obtaining a correlation sequence of a preferred pair,
wherein the correlation sequence is obtained as a cross-correlation function between said two sequences of the preferred pair; Obtain offset correlation sequences from
corresponding correlation sequences; Offset-based correlation sequences yield perfect ternary sequences. 26. The base ternary sequence generation module of claim 24, wherein
if the seed sequence is the complement of the m-sequence, the near-perfect ternary sequence generation module is adapted to generate a near-perfect ternary sequence from the
seed sequence , where the generation of a perfect ternary sequence consists of: Obtaining one or more candidate sequences by inverting the value of one or more positions with
unit weight in the seed sequence for a predefined ratio; At least one sequence is selected from the candidate sequences as a near-perfect ternary sequence based on the minimum
value of the mean square autocorrelation coefficient (MSAC). 27. The base ternary sequence generation module of claim 26, wherein the predefined value insertion module is
adapted to insert the predefined value into one of a perfect ternary sequence and a near-perfect ternary sequence to generate base ternary sequence. 28. A receiver comprising: a
signal receiving module, configured to receive a signal sent from the transmitter; a demodulation module in combination with the sample sequence input module and the signal
reception module, wherein the demodulation module performs a process on the received signal correlating one or more ternary sequences input from the ternary sequence input
module with the received signal demodulation; A symbol detection module adapted to detect one or more transmitted data symbols based on a sequence of maximum correlation
corresponding to the demodulated ternary sequence.
Description
Method and system for using ternary sequences for simultaneous transmission to coherent and non-coherent receivers
Technical Field
The present invention relates to communication systems, and more particularly, to methods and systems for coherent and non-coherent data transmission.
Background
Low power wireless networks, such as sensor networks, PANs (personal access networks), BANs (body area networks), etc., have received increasing interest in
industrial automation, personalized entertainment and personal healthcare. Typically, the devices in these networks are small in size and need to conserve their battery
life. Thus, although these devices have a relatively low symbol rate, it is desirable that these devices operate at low power. The selection of efficient transmit and receive
protocols that trade off energy versus symbol rate becomes an important aspect in the design of low power wireless networks.
The form of the signal processing algorithm used at the receiver is crucial to the design of the power-saving transmission protocol. It is well known that receivers are
broadly divided into coherent and non-coherent receivers. Coherent receivers utilize phase information in the demodulation of symbols (symbols), whereas non-coherent
receivers are based primarily on envelope detection without phase information. Generally, coherent receivers achieve better performance than non-coherent receivers in
terms of power cost and complexity. Coherent communication supports a bipolar modulation alphabet (alphabets) due to the ability to utilize phase information, while
https://patents.google.com/patent/CN105745888A/en?oq=Patent+CN105745888A
2/132/13/26, 2:02 PM
CN105745888A - Method and system using ternary sequences for simultaneous transmission to coherent and non-coherent...
non-coherent communication supports a unipolar alphabet. Therefore, in general, communication networks are designed to exclusively support coherent receivers or
non-coherent receivers. However, many communication networks that include low power constraints may need to support both coherent and non-coherent reception.
This stems from the fact that some receivers use non-coherent reception due to system processing and power constraints. Therefore, in such networks, the transmission
scheme needs to be designed to ensure suitability for both types of receivers. Furthermore, in many cases, due to practical concerns, the design task is made more
challenging given that the sender does not know the type of target receiver.
Disclosure of Invention
Solution of the problem
The object of the invention is to transmit data in low power devices.
Yet another object of the present invention is to simultaneously transmit data to both coherent and non-coherent receivers.
Embodiments of the present invention describe a method of transmitting data. The method comprises the following steps: retrieving a base ternary sequence having a
predefined length; acquiring one or more ternary sequences corresponding to data to be transmitted from the base ternary sequence; the acquired ternary sequence is
transmitted by the transmitter. According to one embodiment of the present invention, the step of acquiring one or more ternary sequences corresponding to data to be
transmitted from the base ternary sequence includes: dividing data to be transmitted into one or more symbols having a predefined length; mapping one or more
symbols in binary form to one or more ternary sequences obtained as one or more cyclic shifts of a base ternary sequence, wherein the number of cyclic shifts is
determined based on a one-to-one mapping from symbols to ternary sequences obtained as the cyclic shifts.
One aspect of the invention discloses the generation of a base ternary sequence having a predefined length. The method for generating the base ternary sequence
comprises the following steps: selecting a seed sequence of a predefined length, wherein the seed sequence is one of an m-sequence and a complement of the m-
sequence; generating a perfect ternary sequence from the seed sequence if the weight of the seed sequence is a perfect square, wherein the weight of the sequence is
the number of non-zero elements in the sequence; generating a near-perfect ternary sequence from the seed sequence if the weight of the seed sequence is different
from the perfect square number; a predefined binary value is inserted into a predefined position of the perfect ternary sequence or close to the perfect ternary sequence
for generating a base ternary sequence.
Another aspect of the invention discloses a method of receiving data transmitted from one or more transmitters. According to one embodiment of the invention, the
method comprises: receiving, by a receiver from the one or more transmitters, one or more data symbols transmitted as one or more ternary sequences; in case the
receiver is a coherent receiver, the ternary sequence is aligned by correlating the received signal with all cyclic shifts of the base ternary sequenceCarrying out
demodulation; in case the receiver is a non-coherent receiver, demodulating by correlating the received signal with all cyclic shifts of the absolute value of the base
ternary sequence; each data symbol transmitted is detected based on a cyclic shift corresponding to the maximum correlation. In this regard, the cyclic shift of the base
ternary sequence is a ternary sequence obtained by cyclically shifting the base ternary sequence to the left or right. For example, if x is a base ternary sequence of length
N, its elements are given as x0,x1,......,xN. Then the cyclic shift of two bits of the base ternary sequence is x2......xN,x0,x1Or xN-1,xN,......,x0,x1. There are N
different cyclic shifts of the base ternary sequence and the above cyclic shifts of the base ternary sequence can be obtained by cyclically shifting in either direction, as
long as the direction of each cyclic shift remains unchanged.
Another aspect of the invention discloses a transmitter. The transmitter includes: a data input module; a sending module; a symbol generation module, in combination
with the data input module, adapted to generate one or more data symbols based on the input data; a ternary sequence generation module combined with the symbol
generation module; a base ternary sequence retrieval module; and a cyclic shift generation module. The base ternary sequence retrieval module retrieves a base ternary
sequence. Likewise, the cyclic shift generation module is adapted to generate a cyclic shift of the base ternary sequence based on the generated data symbols.
In addition, the invention discloses a basic ternary sequence generation module. The base ternary sequence generation module comprises: a seed sequence selection
module; a perfect ternary sequence generation module; a near perfect ternary sequence generating module; and a predefined value insertion module. The seed sequence
selection module is adapted to select a seed sequence as an m-sequence or a complement of an m-sequence. If the length of the base ternary sequence is N, the weight
of the seed sequence is N/2 if the seed sequence selected is an m-sequence. Likewise, if the selected seed sequence is the complement of the m-sequence, the weight
of the seed sequence is equal to (N-2)/2.
Furthermore, the invention discloses a receiver. A receiver according to one embodiment of the present invention includes: a signal receiving module; the demodulation
module is combined with the ternary sequence input module and the signal receiving module; and a symbol detection module. If the receiver is a coherent receiver, the
ternary sequence input module retrieves all N cyclic shifts of the base ternary sequence. If the receiver is a non-coherent receiver, the ternary sequence input module
retrieves all N cyclic shifts of the absolute value of the base ternary sequence. In this regard, N is the length of the base ternary sequence and will be referred to in many
places herein. The signal receiving module is adapted to receive a signal transmitted from a transmitter.
The demodulation module demodulates the received signal by correlating the received signal with the sequence from the ternary sequence input module.
The symbol detection module is adapted to detect each data symbol transmitted by identifying a cyclic shift of the base ternary sequence corresponding to a maximum
correlation value among all N correlation values obtained by the demodulation module corresponding to the N sequences from the ternary sequence input module and
then mapping the identified cyclic shift to the data symbol using an inverse of the one-to-one mapping used at the transmitter.
Drawings
The above aspects and other features of the present invention will be explained by the following description in conjunction with the accompanying drawings, in which:
FIG. 1 is a block diagram of an exemplary communication system in accordance with one embodiment of the present invention;
FIG. 2 is a block diagram depicting data processing operations in an exemplary communication system, in accordance with one embodiment of the present invention;
FIG. 3 is a flow diagram illustrating a method of transmitting data according to one embodiment of the invention;
fig. 4 is a flowchart illustrating a method of acquiring one or more ternary sequences (ternary sequences) corresponding to data to be transmitted;
FIG. 5 is a flow diagram illustrating a method of generating a base ternary sequence (base ternary sequence), according to one embodiment of the present invention;
FIG. 6 is a flow diagram illustrating a method of generating a perfect (best) ternary sequence from a seed sequence, according to one embodiment of the present
invention;
FIG. 7 is a flow diagram illustrating a method of generating a near perfect ternary sequence, according to one embodiment of the present invention;
FIG. 8 is a block diagram of a transmitter in accordance with one embodiment of the present invention;
https://patents.google.com/patent/CN105745888A/en?oq=Patent+CN105745888A
3/132/13/26, 2:02 PM
CN105745888A - Method and system using ternary sequences for simultaneous transmission to coherent and non-coherent...
FIG. 9 is a block diagram of a base ternary sequence generation module according to one embodiment of the present invention;
FIG. 10 is a block diagram of a receiver according to one embodiment of the invention;
FIG. 11 is a block diagram illustrating an exemplary communications device for implementing various components of an embodiment of the invention.
Best mode for carrying out the invention
Embodiments of the present invention will now be described in detail with reference to the accompanying drawings. However, the present invention is not limited to these
examples. The present invention may be modified in various forms. Accordingly, the embodiments of the present invention are provided only to explain the present
invention more clearly to those skilled in the art of the present invention. In the drawings, like reference numerals are used to designate like components.
This specification may refer to "an" or "some" embodiment in various places. This does not necessarily mean that each such embodiment is the same embodiment or
that the described features only apply to a single embodiment. Individual features of different embodiments may also be combined to provide further embodiments.
As used herein, the singular forms "a", "an" and "the" are intended to include the plural forms as well, unless expressly stated otherwise. It will be further understood that
the terms "comprises," "comprising," "... ...," "includes" and/or "including ... ...," when used in this specification, specify the presence of stated features, integers, steps,
operations, elements, and/or components, but do not preclude the presence or addition of one or more other features, integers, steps, operations, elements, components,
and/or groups thereof. As used herein, the term "and/or" includes any and all combinations of one or more of the associated listed items.
Unless otherwise defined, all terms (including technical and scientific terms) used herein have the same meaning as commonly understood by one of ordinary skill in the
art to which this disclosure belongs. It will be further understood that terms, such as those defined in commonly used dictionaries, should be interpreted as having a
meaning that is consistent with their meaning in the context of the relevant art and will not be interpreted in an idealized or overly formal sense unless expressly so
defined herein.
Fig. 1 is a block diagram of an exemplary communication system in accordance with one embodiment of the present invention. According to one embodiment of the
invention, a communication system includes a sender 101 and one or more receivers. The receiver according to one embodiment of the invention is one of a coherent
receiver (such as 102A, 102B ... ... 102N) and a non-coherent receiver (such as 103A, 103B ... ... 103N). The transmitter 101 and the receiver are connected by a wireless
channel.
Data transmitted from the sender 101 is received and processed simultaneously by coherent receivers 102A, 102B ... ... 102N and non-coherent receivers 103A, 103B ... ...
103N. The transmitter 101 transmits data over a ternary (ternary) alphabet {0, -1, +1 }. Coherent receivers 102A, 102B ... ... 102N demodulate the received signal through a
ternary (ternary) alphabet {0, -1, +1}, whereas noncoherent receivers demodulate the received signal through a binary alphabet {0, 1 }.
Throughout this specification, for convenience, coherent and non-coherent receivers are interchangeably denoted by reference numerals 102 and 103 or coherent
receivers 102A, 102B ... ... 102N and non-coherent receivers 103A, 103B ... ... 103N, respectively.
Fig. 2 is a block diagram depicting data processing operations in an exemplary communication network, in accordance with one embodiment of the present invention.
In block 201 of fig. 2, data to be transmitted in digital form is presented. At the transmitter 101, the data is divided into data blocks of length k (called data symbols).
Thus, N is 2kThe data symbols are encoded as N different ternary sequences (ternary sequences). The coding requires the number of different ternary sequences to be
equal to N. For example, when the symbol size k is 3, each of N-8 symbols is uniquely encoded as one of N-8 ternary sequences.
The transmitter obtains data symbols from a symbol set S, wherein
S={s0,s1,......,sN-1},N=2k
These data symbols are mapped to symbols from the codeset C ═ C0,......,cN-1One of N possible ternary sequences. The mapping is represented as follows:
sm &Element; S &DoubleRightArrow; cg &Element; C - - - ( 1 )
we define a set of intervals ZN(0, 1, 2, ... ..., N-1.) note m, g ∈ ZN. The corresponding ternary sequence is sent to both the non-coherent receiver 103A and the coherent
receiver 102A.
When the transmitter 101 transmits the ternary sequence, the coherent receiver 102A receives the ternary sequence unchanged. The non-coherent receiver 103A receives
the absolute value of the ternary sequence transmitted from the transmitter 101, that is, the transmitted ternary sequence having "-1" is received as a ternary sequence
having "+ 1". Therefore, in order to efficiently transmit the same ternary sequence to the coherent receiver 102A and the non-coherent receiver 103A, the ternary sequence
should belong to a ternary code set (ternary code set) C satisfying the following properties.
a. The sequences in the ternary code set C should be maximally separated.
b. The sequences in the corresponding binary code set | C | which are composed of sequences obtained as absolute values of the corresponding sequences in the
ternary code set C should be maximally separated.
The design of the ternary code set C is achieved by designing a single sequence with good autocorrelation properties on the binary alphabet {0, 1} and the ternary
alphabet {0, -1, +1 }.
This sequence is hereinafter referred to as "base ternary sequence (base ternary sequence)" throughout the specification.
The ternary code set C is obtained as a set of all cyclic shifts of the base ternary sequence described above. Let the base ternary sequence appear as tbThen the codeset
C is given by:
g
C = { cg : cg = L { tb } , &ForAll; g &Element; ZN } - - - ( 2 )
here, Lg{tbIs the "g cyclic shift" operator that cyclically shifts the base ternary sequence by "g" elements. It may be noted that cyclic shifts may be applied in any direction,
meaning that all cyclic shifts are along the same direction whenever more than one cyclic shift is considered.
The mapping in equation (1) may be rewritten as:
we can now look from the symbol set s to ZNThe one-to-one mapping of (a) is defined as:
https://patents.google.com/patent/CN105745888A/en?oq=Patent+CN105745888A
4/132/13/26, 2:02 PM
CN105745888A - Method and system using ternary sequences for simultaneous transmission to coherent and non-coherent...
g=f(sm)(3)
where f (x) is the symbol sm∈ S to cyclic shift g ∈ ZNAny one-to-one mapping of. For example, g ═ f(s)m) May be equivalent to a binary symbol smDecimal system of (d).
Similarly, g ═ f(s)m) May be identical to the symbol smGolay mapping (garymappaping) of or data symbols sm∈ S to cyclic shift ∈ ZNAny other one-to-one mapping of.
Thus, each data symbol is mapped to a unique cyclic shift of the base ternary sequence.
Inverse mapping f-1(x) Is defined as:
sm=f-1(g)(4)
in all of the following discussions, we consider the mapping in equation (3) as a one-to-one mapping and the mapping described by equation (4) as the inverse of the
one-to-one mapping.
Fig. 3 is a flow diagram illustrating a method of transmitting data according to one embodiment of the invention. In step 301, the base ternary sequence is retrieved and
stored in all transmitters and receivers. In step 302, one or more ternary sequences corresponding to data symbols to be transmitted are obtained from a base ternary
sequence. This step is explained in detail in fig. 4. In step 303, the ternary sequence is transmitted to the receiver.
In step 304 of fig. 3, if the receiver is a coherent receiver 102A, 102B, ... ..., 102N, the receiver correlates the received signal with all cyclic shifts of the base ternary
sequence. Likewise, the non-coherent receivers 103A, 103B, ... ..., 103N demodulate the received signal by correlating it with all cyclic shifts of the absolute value of the
base ternary sequence.
In step 305, each data symbol transmitted is detected by mapping the above-mentioned cyclic shift back to the data symbol using the inverse of the one-to-one mapping
based on the cyclic shift corresponding to the largest correlation value among all N correlation values corresponding to all N cyclic shifts.
In one embodiment, the sending and receiving may be explained as follows. And symbol sm∈ S (equivalently, c)g∈ C) is represented as:
cg ( t ) = &Sigma;
N-1
n = 0
cg &lsqb; n &rsqb; p ( t - nTc ) - - - ( 5 )
here, p (t) is a pulsePunching to form wave shape and cg[0],cg[1],......,cg[N-1]Refers to the ternary sequence cgOf (2) is used. Chip duration time TcAnd (4) showing.
And ternary sequence c interfered by Additive White Gaussian Noise (AWGN) and other channel impairmentsg∈ C (equivalently, symbol s)m∈ S) is received by the
receiver.
For example, let yc g(t) and ync g(t) signals c to be transmittedg(t) the baseband equivalents of the corresponding signals received at the coherent receiver 102 and the
non-coherent receiver 103. It can be noted that ync g(t)=|yc g(t) |. For clarity, in the following discussion, signal yc g(t) and ync g(t) ternary sequence c referred to as AND-
Sendg∈ C corresponding "received ternary sequence" if the receiver is a coherent receiver, then y is determined by the ternary sequence to be receivedc g(t) correlating all
cyclic shifts of the base ternary sequence to yc g(t) demodulating. Likewise, by converting the received ternary sequence ync g(t) correlating all cyclic shifts of the
absolute value of the base ternary sequence to ync g(t) demodulating. This will be described below.
g∈ZNSuch as:
Corrg = &Integral;
T
0
y
c
( t ) cg ( t ) dt, &ForAll; g &Element; ZN - - - ( 6 )
g
similarly, for non-coherent receivers, we have
Corrg = &Integral;
T
0
y
nc
g
( t ) | c ( t ) | dt, &ForAll; g &Element; Z - - - ( 7 )
g
N
Wherein,
|c
g
( t ) | = &Sigma;
N-1
n = 0
| c
g
&lsqb; n &rsqb; | p ( t - nTc ) - - - ( 8 )
the data symbols are detected based on a single cyclic shift corresponding to a maximum correlation value among all N correlation values corresponding to the N cyclic
shifts. If we make cyclic shift with g ═ gEstimatingCorresponding maximum correlation value is CorrmaxThen the data symbol is detected as:
fig. 4 is a flowchart illustrating a method of acquiring one or more ternary sequences corresponding to data symbols to be transmitted from a base ternary sequence. In
step 401, the transmitter divides data to be transmitted into one or more data symbols having a predefined length. In step 402, each symbol from the set of data symbols
S is mapped onto one of N possible ternary sequences from the set of codes C obtained as a cyclic shift of the base ternary sequence. The process of the mapping and
inverse mapping is explained in detail in equations 3 and 4.
FIG. 5 is a flow diagram illustrating a method of generating a base ternary sequence, according to one embodiment of the present invention. In step 501, a seed sequence
of a predefined length is selected. The seed sequence may be an m-sequence or the complement of an m-sequence. The seed sequence is N-1 in length, where N-2nIs
the desired length of the base ternary sequence. If the seed sequence is an m-sequence, the weight of the sequence is N/2, and if the seed sequence is the complement
of the m-sequence, the weight is (N-2)/2.
At step 502, it is determined whether the weight of the selected seed sequence is a perfect square (perfect square). In the present invention, the weight of a sequence is
the number of non-zero elements in the sequence. According to one embodiment of the invention, if the weight of the selected seed sequence is a perfect square, a
perfect ternary sequence is generated from the seed sequence as shown in step 503. The method of generating a perfect ternary sequence from a seed sequence is
explained in detail in fig. 6. If the weight of the selected seed sequence is not a perfect square, then a near perfect ternary sequence is generated from the seed sequence
as shown in step 504. The method of generating a near-perfect ternary sequence from a seed sequence according to step 504 is explained in detail in fig. 7.
In step 505, predefined values are inserted in predefined positions of the perfect ternary sequence or near the perfect ternary sequence for generating a base ternary
sequence. The predefined value is determined based on a seed sequence selected for the generation of a perfect ternary sequence. The position for inserting the
predefined value is the position, among all possible positions, at which the MSAC of the resulting base ternary sequence and the MSAC of the absolute value of the base
ternary sequence are minimal. There are two cases, in one case, if the selected seed sequence used to produce a perfect ternary sequence is an m-sequence, then a
value of "1" is inserted in the perfect ternary sequence or in a near-perfect ternary sequence. In another case, if the selected seed sequence is the complement of the m-
sequence, the predefined value inserted close to a perfect ternary sequence is the value "1".
https://patents.google.com/patent/CN105745888A/en?oq=Patent+CN105745888A
5/132/13/26, 2:02 PM
CN105745888A - Method and system using ternary sequences for simultaneous transmission to coherent and non-coherent...
Fig. 6 is a flow diagram illustrating a method of generating a perfect ternary sequence from a seed sequence, according to one embodiment of the present invention. At
step 601, a pair of preferred m-sequences is obtained using a seed sequence. The first m-sequence in this preferred pair is itself a seed sequence. The second seed
sequence in the preferred pair is a predefined decimated m-sequence that is obtained as a seed sequence. It is a known technique to obtain said predefined decimation
of another m-sequence from a given m-sequence. In this context, it is assumed that the values are from the setThen the preferred pair of m-sequences of period P ═ N-1
(where N ═ 2)n) Is a cross-correlation sequence having a cross-correlation sequence of theta: (x, y) of the sequence x and y. K of the sequence theta (x, y)thThe (kth)
element is given by:
&theta; ( x, y ) &lsqb; k &rsqb; = &Sigma;
P-1
i = 0
( -1 )
( xi &CirclePlus; y
( i + k ) modP
)
, 0 &le; k &le; P - 1 - - - ( 10 )
at step 602, a correlation sequence θ (x, y) for the preferred pair is obtained using equation (10).
At step 603, the shifted correlation sequence Ψ from the corresponding correlation sequence θ (x, y) is obtained(x , y). The offset correlation sequence is obtained by
adding a value of "1" to each element in the correlation sequence. I.e. Ψ(x,y)1+ θ (x, y). Let Ψ(x,y)The elements of (a) are the following values:
&Psi;
( x, y )
n+1
&Element; { 0, &PlusMinus; 2
2
}
at step 604, a perfect ternary sequence is generated based on the shifted correlation sequence. To generate a perfect ternary sequence, the shifted correlation sequence
Ψ(x , y)1+ θ (x, y) divided bySequence Λ (x, y) with elements {0, ± 1} is obtained.
The method steps described in step 602, step 603 and step 604 are shown using the following example for obtaining a perfect ternary sequence of length 7.
This is demonstrated in the following example using an m-sequence with a period (period) of 7. The m-sequence x is selected as the seed sequence and the m-sequence
y forms a preferred pair with the m-sequence x.
Let x be {0111010}
And, y ═ {0101110}
Then, let the cross-correlation θ (x, y) be given by:
θ(x,y)={-1-1-533-13}
Ψ(x,y)=1+θ(x,y)={00-44404}
the sequence Λ (x, y) is thus obtained as:
1 + &theta; ( x, y )
4
=
0
0
-1
1
1
0
1
the sequence Λ (x, y) is a perfect ternary sequence with θ (x, y) ═ 4000000 }. Note also that the sequence Λ (x, y) is also a cyclic shift of the absolute value of the seed m-
sequence x.
FIG. 7 is a flow diagram illustrating a method of generating a near perfect ternary sequence, according to one embodiment of the present invention. If the weight of the
seed sequence is different from the perfect square number, a near perfect ternary sequence is generated from the seed sequence. In step 701, one or more candidate
sequences are obtained by inverting the values of one or more positions in the seed sequence corresponding to "1" for a predefined ratio. In this context, inversion
changes a "1" to "-1". According to one embodiment of the present invention, candidate sequences are obtained by inverting all possible combinations of "1" s in the
sequence such that the ratio of the number of-1 s to the number of 1 s in the resulting sequence is within a predefined ratio range. The above-mentioned predefined ratio
ranges refer to all ratios between 1/3 and 2/3.
At step 702, at least one sequence is selected from the candidate sequences as a near-perfect ternary sequence based on a minimum value of a Mean Square
Autocorrelation Coefficient (MSAC). MSAC is calculated as the average of N-1 of the phase side autocorrelation coefficients (phasesquarerautocorrelationcoefficients).
Therefore, a near perfect ternary sequence is obtained by performing a computer search on these scales. A sequence is selected having a minimum value of a Mean
Square Autocorrelation Coefficient (MSAC).
The mean square autocorrelation of a sequence of length P is defined as:
&mu;
MSAC
=
1
( N-1 )
&Sigma;
P-1
&tau; - 1
R ( &tau; )
2
- - - ( 11 )
here, P ═ N-1 is the length of the seed sequence, and R (τ) is the period of the sequence delayed by τ, given by:
R ( &tau; ) = &Sigma;
P-1
i = 0
xi y
i + &tau;
- - - ( 12 )
when the seed sequence is an m-sequence, base ternary sequences of lengths 8, 16 and 32 are shown in table 1.
TABLE 1
Base ternary sequences of lengths 8, 16 and 32 when the seed sequence is the complement of the m-sequence are shown in table 2. Note that multiple base ternary
sequences with similar MSACs are obtained and are all given in tables 1 and 2.
TABLE 2
The sequence in table 2 has a smaller number of consecutive non-zero elements, which may be desirable in receiver design. A sequence with a uniform distribution of
zero and non-zero elements is selected from all the sequences listed in table 2 to obtain a comprehensive list of base ternary sequences shown in table 3.
TABLE 3
In an exemplary embodiment of the present invention, the cyclic shifts of the base ternary sequences of lengths 8, 16 and 32 are presented in table 3. These are used to
encode data symbols of size k 3, k 4 and k 5, respectively, prior to transmission. These base ternary sequences in Table 3 are referred to as 3/8-OOK, 4/16-OOK, and 5/32-
OOK, respectively. Here, "OOK" represents ON-off keying (ON-OFFKeying). Table 4 shows the base ternary sequences in table 3 with respective terms (nomenclature).
TABLE 4
https://patents.google.com/patent/CN105745888A/en?oq=Patent+CN105745888A
6/132/13/26, 2:02 PM
CN105745888A - Method and system using ternary sequences for simultaneous transmission to coherent and non-coherent...
According to embodiments of the present disclosure, alternative term families, such as 3/8 ternary OOK (3/8-too), 4/16 ternary OOK (4/16-too), and 5/32 ternary OOK
(5/32-too), and 3/8 ternary ASK (3/8-TASK), 4/16 ternary ASK (4/16-TASK), and 5/32 ternary ASK (5/32-TASK), may also be provided to the terms 3/8-OOK, 4/16-OOK,
and 5/32-OOK, respectively, of the sequences as referenced in table 4. Here, "ASK" means amplitude shift keying (amplitude shift keying).
Table 5 shows an example of mapping a data symbol with k-3 onto a cyclic shift of a base ternary sequence of length 8, wherein each cyclic shift of the base ternary
sequence is obtained as the decimal equivalent of the respective binary representation of the data symbol. As previously described, any other one-to-one mapping
described by equation (3) as mentioned in fig. 2 may be used to map the data symbols onto different cyclic shifts of the base ternary sequence.
TABLE 5
The autocorrelation function of the base ternary sequence for an arbitrary delay k can be expressed as follows:
R(k)=xp+qx+Ra(N-k+1)+Ra(k)(13)
in the above expression, when the base ternary sequence is derived from a perfect ternary sequence, if the binary value "x" is equal to "0".
Likewise, "x" equals "1" when the base ternary sequence is derived from a near-perfect ternary sequence.
The elements "p" and "q" represent those elements that match (align with) element x at an arbitrary delay k. Term Ra(k) Is an aperiodic autocorrelation coefficient defined
as:
R
a
( k ) = &Sigma;
N-k-1
i = 0
ci ci + k - - - ( 14 )
here, c ═ { c ═ c0,c1,c2,......,cN-1Is the sequence for which the aperiodic autocorrelation coefficients are calculated.
An example of generating a perfect ternary sequence 00-11101 is explained below using an example.
Consider "x" inserted before the third bit, resulting in the sequence shown below.
{00x-11101}
For any shift k-5, then the relative positioning of the elements of the sequence and its shifted copy are:
00x-11101
-1110100x
the autocorrelation of the delay k 5 is given below:
R(k)=x1+1x+Ra(3)+Ra(5)
in the above calculation, exactly p ═ q ═ 1.
When the base ternary sequence is derived from a perfect ternary sequence, we make x 0. Thus, r (k) is modified to:
R(k)=Ra(N-k+1)+Ra(k)(15)
to limitBy selecting a suitable phase of the seed sequence sufficient to reduce the phase of (k) of (a)The value of (c) is minimized. However, in the literature, there are no
known results for the phases of the seed sequence for minimizing aperiodic autocorrelation in both binary and ternary alphabets. However, if only the binary alphabet is
considered, the autocorrelation properties of the sequence are determined by the aperiodic autocorrelation properties of the binary sequence. This fact is used to
compute the autocorrelation of the binary sequence obtained by the spreading of a known sequence, such as the spread m-sequence.
Inserting x ═ 0 at a position corresponding to the minimum value of MSAC of the obtained base ternary sequence and the absolute value of the base ternary sequence
ensures that equation (15) is the minimum value of different values for delay k.
Fig. 8 is a block diagram of a transmitter according to an embodiment of the present invention. According to one embodiment of the invention, the transmitter includes a
data input module 801, a symbol generation module 802, a ternary sequence generation module 803, a base ternary sequence retrieval module 804, a cyclic shift
generation module 805, and a transmission module 806.
In one embodiment of the invention, data to be transmitted is provided to data input module 801. The data input module 801 is operatively connected to a symbol
generation module 802. The binary format data is divided into predefined lengths to produce data symbols. The symbol generation module 802 performs the above-
mentioned operations.
According to one embodiment of the invention, the base ternary sequence is stored in the transmitter 101. The base ternary sequence retrieval module 804 retrieves the
base ternary sequence and provides the base ternary sequence into the ternary sequence generation module 803. The ternary sequence generation module 803 is
connected to the base ternary sequence retrieval module 804 and the symbol generation module 802. The ternary sequence generation module 803 generates one or
more ternary sequences from the base ternary sequence by mapping each symbol to a corresponding ternary sequence obtained as a cyclic shift of the base ternary
sequence based on the one-to-one mapping described in equation (3) in the description of fig. 2.
The transmission module 806 according to an embodiment of the present invention transmits the generated ternary sequence to the coherent receiver 102A and the non-
coherent receiver 103A.
FIG. 9 is a block diagram of a base ternary sequence generation module according to one embodiment of the present invention. Generation of the base ternary sequence
includes selection of a seed sequence, generation of a perfect ternary sequence, generation of a near perfect ternary sequence, and the like.
In an exemplary embodiment of the present invention, the base ternary sequence generating module 900 includes a seed sequence selecting module 901, a perfect
ternary sequence generating module 902, a near-perfect ternary sequence generating module 903, and a predefined value inserting module 904.
The seed sequence selection module 901 selects a seed sequence for generating a base ternary sequence. The seed sequence may be an m-sequence or the
complement of an m-sequence. The length of the selected seed sequence is N-1, where N is the expected length of the base ternary sequence to be generated.
https://patents.google.com/patent/CN105745888A/en?oq=Patent+CN105745888A
7/132/13/26, 2:02 PM
CN105745888A - Method and system using ternary sequences for simultaneous transmission to coherent and non-coherent...
If the weight of the sequence is a perfect square, then the seed sequence is fed into a perfect ternary sequence generation module 902. If the weight of the seed
sequence is not a perfect square, the selected seed sequence is fed into a near perfect ternary sequence generation module 903.
The step of generating a perfect ternary sequence using perfect ternary sequence generation module 902 includes obtaining a preferred pair of m-sequences using a
seed sequence. In addition, the perfect ternary sequence generation module 902 obtains the correlation sequence of the preferred pair. The correlation sequence is
obtained as a cross-correlation function between the two sequences of the preferred pair. Then, the shifted correlation sequences are obtained from the corresponding
correlation sequences, and a perfect ternary sequence is generated based on the shifted correlation sequences.
The operation of generating a near-perfect ternary sequence by the near-perfect ternary sequence generation module 903 includes the case when the weight of the seed
sequence is different from the perfect square number. The generation of a near perfect ternary sequence includes: obtaining one or candidate sequences by inverting all
possible combinations of "1" in the seed sequence such that the ratio of the number of-1 s to the number of +1 s in the resulting sequence is within a predefined ratio
range; and selecting at least one sequence from the candidate sequences as a near perfect ternary sequence based on a minimum value of a Mean Square
Autocorrelation Coefficient (MSAC).
The predefined value insertion module 905 inserts a predefined value into a predefined position of one of the perfect ternary sequence and the near-perfect ternary
sequence for generating a base ternary sequence. The predefined position for inserting the predefined value is the position among all possible positions that minimizes
the resulting base ternary sequence and the MSAC of the absolute value of the base ternary sequence. If the seed sequence is an m-sequence, the inserted predefined
value is "0". The predefined value inserted is "1" if the seed sequence is the complement of the m-sequence.
Fig. 10 is a block diagram of a receiver 102 according to one embodiment of the invention. The receiver may be coherent or non-coherent. A typical receiver includes a
signal receiving module 1001, a demodulation module 1002, a cyclic shift sequence input module 1003, and a symbol detection module 1004.
The signal receiving module 1001 receives a signal transmitted from the transmitter 101. The received signal is demodulated using a demodulation module 1002. If the
receiver is a coherent receiver, demodulation is performed by correlating the received signal with all cyclic shifts of the base ternary sequence. If the receiver is a non-
coherent receiver, demodulation is performed by correlating the received signal with all cyclic shifts of the absolute value of the base ternary sequence. The cyclic shift of
the base ternary sequence and the cyclic shift of the absolute value of the base ternary sequence are provided by the ternary sequence input module 1003. The
associated values are fed to a symbol detection module 1004. The symbol detection module 1004 identifies the data symbol from the cyclic shift corresponding to the
maximum value of correlation by mapping the cyclic shift back to the data symbol using the inverse of the one-to-one mapping.
FIG. 11 is a block diagram illustrating an exemplary communications device for implementing various components of an embodiment of the invention. The
communication device 1100 may be a transmitter or a receiver. In fig. 11, a communication device 1100 includes a processor 1101, a memory 1104, a Read Only Memory
(ROM)1102, a transceiver 1106, and a bus 1103.
Processor 1102, as used herein, means any type of computational circuit (such as, but not limited to, a microprocessor, a microcontroller, a complex instruction set
computing microprocessor, a reduced instruction set computing microprocessor, a very long instruction word microprocessor, an explicit parallel instruction computing
microprocessor, a graphics processor, a digital signal processor), or any other type of processing circuit. The processor 1102 may also include embedded controllers
(such as general purpose or programmable logic devices or arrays, application specific integrated circuits, single-chip microprocessors, smart cards, etc.).
The memory 1104 and the ROM1102 may be volatile memory and non-volatile memory. The memory 1104 includes a base ternary sequence generation module 1105
that generates a base ternary sequence according to one or more embodiments described in fig. 5. Various computer-readable storage media may be stored in or
accessible from the memory element. The memory elements may include any suitable memory device for storing data and machine-readable instructions (such as read-
only memory, random access memory, erasable programmable read-only memory, electrically erasable programmable read-only memory, hard disk drives, removable
media drives for handling compact disks, digital video disks, floppy disks, tape cassettes, memory cards, and the like).
Embodiments of the present subject matter may be implemented in conjunction with modules (including functions, procedures, data structures, and applications) for
performing tasks or defining abstract data types or low-level hardware environments. The base ternary sequence generating module 1105 may be stored in the form of
machine-readable instructions on any of the storage media described above and executable by the processor 1102. In one embodiment, the program may be included on
a compact disk read only memory (CD-ROM) and loaded from the CD-ROM to a hard drive in a non-volatile memory. The transceiver 1106 is capable of transmitting and
receiving data. The bus 1103 serves as an interconnection between various components of the communication device 104.
The present embodiments have been described with reference to specific exemplary embodiments. It will be evident that various modifications and changes may be
made to these embodiments without departing from the broader spirit and scope of the various embodiments. Further, the various devices, modules, etc. described
herein may be enabled and operated using hardware circuitry, firmware, and/or software embodied in a machine-readable medium. While the embodiments herein have
been described in terms of various specific embodiments, it will be apparent to those skilled in the art that the invention may be practiced with modification. However, all
such modifications are considered to be within the scope of the claims. It is also to be understood that the following claims are intended to cover all of the generic and
specific features of the embodiments described herein, and all statements of the scope of the embodiments that, as a matter of language, might be said to fall
therebetween.
Patent Citations (80)
Publication numberPriority datePublication dateAssigneeTitle
CN1516349A *1998-12-142004-07-28�����ּ�����˾Detection of preamble in random access channel
CN1639965A *2002-02-222005-07-13鲁道夫·施瓦脱Method and device for detecting and processing electrical and
optical signals
US7401131B2 *2000-05-222008-07-15Verizon Business Global LlcMethod and system for implementing improved containers in a
global ecosystem of interrelated services
US20100008243A1 *2008-07-112010-01-14Qualcomm IncorporatedFlash position signaling: multiplexing and interference
management
US8856087B2 *2000-05-222014-10-07Verizon Patent And Licensing Inc.Method and system for realizing a rendezvous service in a
management operations center implemented in a global
ecosystem of interrelated services
Family To Family Citations
https://patents.google.com/patent/CN105745888A/en?oq=Patent+CN105745888A
8/132/13/26, 2:02 PM
CN105745888A - Method and system using ternary sequences for simultaneous transmission to coherent and non-coherent...
JPS5242017A1975-09-291977-04-01Fuji Xerox Co LtdRun length code processing method for facsimile signal
US5363144A *1992-04-161994-11-08Goldstar Co., Ltd.Television ghost canceling device
US5550865A1993-05-051996-08-27National Semiconductor CorporationFrequency modulator for data transceiver
FR2719175B11994-04-201996-05-31Cit AlcatelOptical transmission method having reduced sensitivity to
dispersion, and transmission system for implementing this
method.
US5633631A *1994-06-271997-05-27Intel CorporationBinary-to-ternary encoder
US5621580A *1994-08-261997-04-15Cruz; Joao R.Ternary code magnetic recording system
GB9614561D0 *1996-07-111996-09-044Links LtdCommunication system with improved code
KR100233390B1 *1997-02-211999-12-01구자홍Color distortion correcting method and apparatus of tv receiver
US6061818A *1997-05-082000-05-09The Board Of Trustees Of The Leland
Stanford Junior UniversityAltering bit sequences to contain predetermined patterns
US6411799B11997-12-042002-06-25Qualcomm IncorporatedMethod and apparatus for providing ternary power control in a
communication system
KR20000060755A1999-03-192000-10-16정명식3B2T Transceiver System for Widening transfering bandwidth
US6735734B1 *2000-04-282004-05-11John M. LiebetreuMultipoint TDM data distribution system
CN1142636C *2000-06-262004-03-17连宇通信有限公司Method for constructing quadrature spread spectrum code blocks
KR20020046118A2000-12-122002-06-20정용주Apparatus and method of pulse shaping for a minimum bandwidth
transmission using unipolar pulse
US6683915B1 *2000-12-212004-01-27Arraycomm, Inc.Multi-bit per symbol rate quadrature amplitude encoding
JP3582650B2 *2001-08-162004-10-27日本電気株式会社Phase modulation apparatus, phase modulation method thereof,
and phase modulation program
US7167110B2 *2002-01-082007-01-23Nec CorporationMulti-level communication system and method with error
correction
US7248659B2 *2002-02-202007-07-24Freescale Semiconductor, Inc.Method for adjusting acquisition speed in a wireless network
JP2006518155A2003-02-142006-08-03フォーカス エンハンスメンツ インコ
ーポレイテッドFrequency division multiplexing method and apparatus therefor
EP1455498A1 *2003-03-062004-09-08STMicroelectronics N.V.Method and apparatus for the generation of ultra-wideband pulses
WO2004114596A1 *2003-06-252004-12-29Koninklijke Philips Electronics N.V.Frame format decoder and training sequence generator for
wireless lan networks
US7930331B2 *2005-09-262011-04-19Temarylogic LlcEncipherment of digital sequences by reversible transposition
methods
KR100557142B1 *2003-10-142006-03-03삼성전자주식회사RGB-AMI Optical Transmitter Module
KR100656339B12003-12-262006-12-11한국전자통신연구원Pulse signal generator for ultra-wide band radio transceiving and
radio transceiver having the same
WO2005067160A1 *2004-01-062005-07-21Agency For Science, Technology And
ResearchMethod of generating uwb pulses
JP4005974B2 *2004-01-092007-11-14株式会社東芝COMMUNICATION DEVICE, COMMUNICATION METHOD, AND
COMMUNICATION SYSTEM
KR100608991B12004-04-082006-08-03곽경섭Low Interference Ultra-Wideband Wireless Communication
System Using Spreading Code with Low Correlation or Zero
Correlation, and Its Communication Processing Method
US6956510B1 *2004-05-142005-10-18Marvell International Ltd.Methods, software, circuits and systems for coding information
US7649956B2 *2004-10-272010-01-19Nec CorporationModulation and demodulation system, modulator, demodulator
and phase modulation method and phase demodulation method
used therefor
KR100657008B12004-12-072006-12-14한국전자통신연구원FIR filter device and control method in DS-CDMAA modem
transmitter
GB0426965D02004-12-092005-01-12Tang BobMethods to increase number of symbols in a transmission bit and
to increase channel capacity in modulated transmissions, without
needing to reduce signal
https://patents.google.com/patent/CN105745888A/en?oq=Patent+CN105745888A
9/132/13/26, 2:02 PM
CN105745888A - Method and system using ternary sequences for simultaneous transmission to coherent and non-coherent...
US7388927B2 *2005-03-072008-06-17Mitsubishi Electric Research
Laboratories, Inc.M-ary modulation of signals for coherent and differentially
coherent receivers
SG160389A1 *2005-03-162010-04-29Agency Science Tech & ResMethod and system for detecting code sequences in ultra-
wideband systems
US7609773B2 *2005-04-182009-10-27Qualcomm IncorporatedMethod of determining the location of the FFT window and the
delay spread for the platinum broadcast channel estimator
US8005171B2 *2005-06-222011-08-23Qualcomm IncorporatedSystems and method for generating a common preamble for use
in a wireless communication system
WO2007011345A22005-07-182007-01-25Mitsubishi Electric Research
LaboratoriesMethod, apparatus and system for modulating and demodulating
signals compatible with multiple receiver types and designed for
improved receiver performance
US20070183386A1 *2005-08-032007-08-09Texas Instruments IncorporatedReference Signal Sequences and Multi-User Reference Signal
Sequence Allocation
JP4814324B2 *2005-08-092011-11-16ミツビシ・エレクトリック・リサー
チ・ラボラトリーズ・インコーポレイ
テッドDevice, method and protocol for concealed UWB ranging
US7428948B2 *2005-08-112008-09-30Rpg Diffusor Systems, Inc.Hybrid amplitude-phase grating diffusers
US7920077B2 *2006-05-032011-04-05Agency For Science, Technology And
ResearchMethod and system for decompressing at least two two-valued
symbol sequences into a three-valued communication sequence
JP4805016B2 *2006-05-192011-11-02京セラ株式会社COMMUNICATION SYSTEM, COMMUNICATION DEVICE, AND
COMMUNICATION RATE CHANGE METHOD
US7801107B2 *2006-05-252010-09-21Mitsubishi Electric Research
Laboratories, Inc.Method for transmitting a communications packet in a wireless
communications network
WO2008004984A12006-07-032008-01-10Agency For Science, Technology And
ResearchMethod and system for detecting a first symbol sequence in a
data signal, method and system for generating a sub-sequence of
a transmission symbol sequence, and computer program
products
US20080279307A1 *2007-05-072008-11-13Decawave LimitedVery High Data Rate Communications System
JP4407724B2 *2007-06-182010-02-03ソニー株式会社Recording / reproducing apparatus, recording / reproducing
method, reproducing apparatus, and reproducing method
KR100922857B12007-12-102009-10-22한국전자통신연구원Ultra wideband wireless system receiving apparatus and method
for receiving same
US8121205B1 *2008-03-202012-02-21Force10 Networks, Inc.Extended non-return-to-zero serial channel signaling
DE102008017644A1 *2008-04-042009-10-15Adva Ag Optical NetworkingApparatus and method for transmitting an optical data signal
US20090304094A1 *2008-06-042009-12-10The University Of Reading WhiteknightsDual Carrier Modulation Soft Demapper
US8825480B2 *2008-06-052014-09-02Qualcomm IncorporatedApparatus and method of obtaining non-speech data embedded in
vocoder packet
WO2010005775A1 *2008-07-082010-01-14Marvell World Trade Ltd.Physical layer frame format design for wideband wireless
communications systems
EP2251999B1 *2009-05-132013-08-28ADVA Optical Networking SEData transmission method and network for transmitting a digital
optical signal over optical transmission links and networks
US8526816B2 *2009-10-292013-09-03Hewlett-Packard Development
Company, L.P.Optical data bus and method
US8243859B2 *2009-12-042012-08-14Viasat, Inc.Joint frequency and unique word detection
US20130201895A1 *2010-01-262013-08-08Joseph SmallcombMethod for Automatic Reconfiguration in a Hierarchical
Modulation System
US9294316B2 *2010-06-242016-03-22Texas Instruments IncorporatedScrambling sequences for wireless networks
EP2413524B1 *2010-07-282013-01-16Telefonaktiebolaget L M Ericsson
(PUBL)Method and apparatus for determining signal path properties
US8767848B2 *2010-12-232014-07-01Texas Instruments IncorporatedChannel estimation based on long training symbol with doubled
cyclic prefix
US9130679B1 *2011-05-272015-09-08Nec Laboratories America, Inc.Polarization-switched differential ternary phase-shift keying
CN102368758B *2011-09-012015-08-12南京航空航天大学About a kind of new improvement project of GMSK modulation
technology
https://patents.google.com/patent/CN105745888A/en?oq=Patent+CN105745888A
10/132/13/26, 2:02 PM
CN105745888A - Method and system using ternary sequences for simultaneous transmission to coherent and non-coherent...
US9246725B2 *2011-09-062016-01-26Electronics And Telecommunications
Research InstituteMethod of generating and receiving packets in low energy critical
infrastructure monitoring system
CN102413086B *2011-11-082013-11-20哈尔滨工程大学Ternary notation frequency modulation key modulation method
KR20130104289A *2012-03-132013-09-25삼성전자주식회사Apparatus and method for estimating offset value, receiving
apparatus, and method for processing signal in the same
US9232505B2 *2012-07-102016-01-05Electronics And Telecommunications
Research InstituteMethod of generating packet, method of transmitting packet, and
method of ranging of physical layer transmitter of wireless
personal area network system
US9077442B2 *2012-07-162015-07-07Texas Instruments IncorporatedDSSS inverted spreading for smart utility networks
US9629114B2 *2012-09-192017-04-18Siemens AktiengesellschaftMethod and apparatus for wireless transmission of data packets
JP2014220613A *2013-05-072014-11-20ソニー株式会社Transmission circuit, transmission method and transmission
system
CN103248458A *2013-05-112013-08-14哈尔滨工业大学深圳研究生院Physical layer network coding system and method based on
FQPSK modulation
US20150094082A1 *2013-09-302015-04-02Qualcomm IncorporatedChannel estimation using cyclic correlation
KR102349122B1 *2013-10-292022-01-10삼성전자주식회사A method and system using ternary sequences for simultaneous
transmission to coherent and non-coherent recievers
US10256933B2 *2013-10-302019-04-09Samsung Electronics Co., Ltd.Method and device for transmitting preamble sequence
US9819444B2 *2014-05-092017-11-14Avago Technologies General Ip
(Singapore) Pte. Ltd.Robust line coding scheme for communication under severe
external noises
WO2016007118A1 *2014-07-072016-01-14Hewlett-Packard Development
Company, L.P.Portable speaker
US9842020B2 *2014-11-262017-12-12Qualcomm IncorporatedMulti-wire symbol transition clocking symbol error correction
US9935681B2 *2016-03-162018-04-03Texas Instruments IncorporatedPreamble sequence detection of direct sequence spread
spectrum (DSSS) signals
* Cited by examiner, † Cited by third party
Non-Patent Citations (3)
Title
JIAN XING LEE, FRANCOIS CHIN, YUEN SAM KWOK, SAI HO WONG, LI: ""UWB Piconet Interference Suppression Using Clustered Ternary Orthogonal Signaling Scheme"", 《ICUWB
2009》 *
SUJIT JOS,JINESH P. NAIR,DEBARATI SEN,ARUN NANIYAT: ""Method of Generating Multiple Sets of Orthogonal Codes with Wide Choice of Spreading Factors"", 《IEEE
WIRELESS COMMUNICATIONS LETTERS》 *
XIAOMING PENG, FRANCOIS CHIN, SAI HO WONG, KWOK YUEN SAM, LEI ZH: ""A RAKE Combining Scheme for an Energy Detection Based Noncoherent OOK Receiver in UWB
Impulse Radio Systems"", 《THE 2006 IEEE 2006 INTERNATIONAL CONFERENCE ON IEEE》 *
* Cited by examiner, † Cited by third party
Cited By (9)
Publication numberPriority datePublication dateAssigneeTitle
CN112803967A *2020-12-302021-05-14湖南艾科诺维科技有
限公司Detection and parameter estimation method and device for uncoordinated spread
spectrum signal
KR102349122B1 *2013-10-292022-01-10삼성전자주식회사A method and system using ternary sequences for simultaneous transmission to
coherent and non-coherent recievers
US20160278013A1 *2015-03-202016-09-22Qualcomm
IncorporatedPhy for ultra-low power wireless receiver
EP3157217B1 *2015-10-132019-07-03Samsung
Electronics Co., Ltd.Method and system of transmitting independent data from transmitters to receivers
KR102509820B1 *2015-10-132023-03-14삼성전자주식회사Method and system of transmitting independent data by at least two transmitters to
receivers
Family To Family Citations
https://patents.google.com/patent/CN105745888A/en?oq=Patent+CN105745888A
11/132/13/26, 2:02 PM
CN105745888A - Method and system using ternary sequences for simultaneous transmission to coherent and non-coherent...
KR101701421B1 *2015-10-162017-02-13고려대학교 산학협
력단Method and apparatus for multi-sequence spreading-based random access and
multi-user detection
US10757732B2 *2016-05-232020-08-25Lg Electronics Inc.Method and apparatus for competition-based transmitting of uplink data in wireless
communication system to which non-orthogonal multiple access scheme is applied
US10212009B2 *2017-03-062019-02-19Blackberry LimitedModulation for a data bit stream
CN120074751A *2022-12-072025-05-30华为技术有限公司Signal transmission method and device based on ultra-wideband
* Cited by examiner, † Cited by third party, ‡ Family to family citation
Similar Documents
PublicationPublication DateTitle
CN105745888B2019-11-26Method and system using ternary sequences for simultaneous transmission to coherent and non-coherent receivers
CN105874761B2019-10-08For sending the method and device of leader sequence
JP2016538775A52017-09-28JP2017503368A52017-12-14KR101568714B12015-11-12Apparatus and method for transmitting and receiving information using a fast feedback channel in a broadband wireless
communication system
KR102283137B12021-07-29Method and apparatus for transmitting preamble sequence
CN101647206A2010-02-10Correlation device
KR20170043446A2017-04-21Method and system of transmitting independent data by at least two transmitters to receivers
CN106571898B2021-10-01Method and system for transmitting independent data to a receiver by at least two transmitters
KR101269849B12013-06-07Apparatus and method for generating the sequence family to spread the channel of communication system
CN106899532A2017-06-27A kind of signal processing method and device
Priority And Related Applications
Child Applications (1)
ApplicationPriority dateFiling dateRelationTitle
CN201911130921.9A2013-10-292014-10-21DivisionMethod and apparatus for data symbol to chip mapping
Priority Applications (1)
ApplicationPriority dateFiling dateTitle
CN201911130921.9A2013-10-292014-10-21Method and apparatus for data symbol to chip mapping
Applications Claiming Priority (3)
ApplicationFiling date
Title
IN4875CH20132013-10-29IN4875/CHE/20132013-10-29PCT/KR2014/0098732014-10-21A method and system using ternary sequences for simultaneous transmission to coherent and non-coherent recievers
DateCodeTitle
2016-07-06C06Publication
2016-07-06PB01Publication
2017-03-08C10Entry into substantive examination
Legal Events
https://patents.google.com/patent/CN105745888A/en?oq=Patent+CN105745888A
Description
12/132/13/26, 2:02 PM
CN105745888A - Method and system using ternary sequences for simultaneous transmission to coherent and non-coherent...
2017-03-08SE01Entry into force of request for substantive examination
2019-11-26GR01Patent grant
2019-11-26GR01Patent grant
About
Send Feedback
Public Datasets
Terms
https://patents.google.com/patent/CN105745888A/en?oq=Patent+CN105745888A
Privacy Policy
Help
13/13
 G06F7/5443 Sum of products
 G06F7/496 Multiplying; Dividing
 G06F9/30018 Bit or string instructions
 G06F9/30029 Logical and Boolean instructions, e.g. XOR, NOT
 G06N3/04 Architecture, e.g. interconnection topology
 G06N3/0495 Quantised networks; Sparse networks; Compressed networks
 G06N3/0499 Feedforward networks
 G06N3/063 Physical realisation, i.e. hardware implementation of neural networks, neurons or parts of neurons using electronic means
 G06N3/09 Supervised learning
 G11C11/34 Digital stores characterised by the use of particular electric or magnetic storage elements; Storage elements therefor using electric elements using semiconductor devices
 G11C11/54 Digital stores characterised by the use of particular electric or magnetic storage elements; Storage elements therefor using elements simulating biological cells, e.g. neuron
 G11C16/26 Sensing or reading circuits; Data output circuits
 G06F2207/4824 Neural networks
 G06N3/08 Learning methods
 G11C16/0483 Erasable programmable read-only memories electrically programmable using variable threshold transistors, e.g. FAMOS comprising cells having several storage transistors connected in series
