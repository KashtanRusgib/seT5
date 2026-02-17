# Dynamic Epistemic Logic (DEL) Extensions

## Comprehensive Research Compilation

**Date:** February 16, 2026  
**Sources:** Internet Encyclopedia of Philosophy (IEP), Stanford Encyclopedia of Philosophy (SEP), Wikipedia, arXiv, HAL Inria  
**Authors Surveyed:** Baltag, Moss, Solecki, van Ditmarsch, van der Hoek, Kooi, van Benthem, Renne, Plaza, Gerbrandy, Aucher, Segerberg

---

## 1. Overview and Foundations

Dynamic Epistemic Logic (DEL) is the study of modal logics of model change—a highly active area of applied logic that intersects Formal and Social Epistemology, Doxastic Logic, Belief Revision, multi-agent and distributed systems, Artificial Intelligence, Defeasible and Non-monotonic Reasoning, and Epistemic Game Theory (Baltag & Renne 2016, SEP).

The central insight of DEL is the shift from a **static** semantics of truth evaluated within a single Kripke model to a **dynamic** semantics of truth evaluated across modality-specified Kripke model transformations. If `[A]` is a dynamic modality describing an action A, then a formula `[A]φ` expresses that φ holds **after** the occurrence of action A. Formally:

> To determine whether `[A]φ` is true at a pointed Kripke model `(M, w)`, we transform M according to the prescription of action A to obtain a new pointed model `(M', w')`, and then check whether φ holds at `(M', w')`.

This dynamic perspective enables analysis of the epistemic and doxastic consequences of communicative acts—public announcements, private messages, observations—without hard-wiring outcomes into the initial model.

### 1.1 Epistemic Logic Foundations

DEL builds upon classical epistemic logic (Hintikka 1962). A **Kripke model** M = (W, R, V) consists of:

- **W**: a non-empty set of possible worlds (states)
- **R**: a family of accessibility relations {R_a}_{a ∈ A} for each agent a in agent set A
- **V**: a valuation function V: P → 2^W mapping propositions to sets of worlds

The basic modal language ML is:

$$\varphi ::= p \mid \varphi \wedge \varphi \mid \neg \varphi \mid [a]\varphi$$

where p ∈ P (propositional letters) and a ∈ A (agents). The formula `[a]φ` is read as "agent a knows (or believes) that φ". Semantically:

$$M, w \models [a]\varphi \iff \text{for all } v \text{ such that } wR_av, \; M, v \models \varphi$$

Properties of the accessibility relations determine the strength of the epistemic operator:
- **Reflexivity** (T axiom): `[a]φ → φ` — knowledge is truthful
- **Transitivity** (4 axiom): `[a]φ → [a][a]φ` — positive introspection
- **Euclideanness** (5 axiom): `¬[a]φ → [a]¬[a]φ` — negative introspection
- **Seriality** (D axiom): `[a]φ → ⟨a⟩φ` — consistency of beliefs

The system S5 (reflexive, transitive, Euclidean) is typically used for knowledge; KD45 for belief.

---

## 2. Public Announcement Logic (PAL)

### 2.1 Syntax and Semantics

Public Announcement Logic (PAL) is the most basic dynamic epistemic logic, extending the epistemic language with operators for truthful, fully trustworthy public announcements (Plaza 1989/2007). The language of PAL extends ML:

$$\varphi ::= p \mid \varphi \wedge \varphi \mid \neg \varphi \mid [a]\varphi \mid [!\varphi]\varphi$$

The formula `[!φ]ψ` reads: **"after the public announcement of φ, ψ is true."**

**Semantics of public announcement:**

$$M, w \models [!\varphi]\psi \iff (M, w \models \varphi) \implies (M|\varphi, w \models \psi)$$

where the **restricted model** M|φ = (W', R', V') is defined by:

- $W' = \{v \in W \mid M, v \models \varphi\}$ — retain only φ-worlds
- $R'_a = R_a \cap (W' \times W')$ — restrict accessibility to remaining worlds
- $V'(p) = V(p) \cap W'$ — restrict valuation to remaining worlds

The dual operator `⟨!φ⟩ψ ≡ ¬[!φ]¬ψ` means "φ is true and after announcing φ, ψ holds."

### 2.2 Reduction Axioms

A key metatheoretic property of PAL is that every PAL formula can be reduced to an equivalent formula in the base epistemic language (without announcement operators). This is achieved through the following **reduction axioms**:

1. **Atomic reduction:** `[!φ]p ↔ (φ → p)`
2. **Negation:** `[!φ]¬ψ ↔ (φ → ¬[!φ]ψ)`
3. **Conjunction:** `[!φ](ψ ∧ χ) ↔ ([!φ]ψ ∧ [!φ]χ)`
4. **Knowledge:** `[!φ][a]ψ ↔ (φ → [a][!φ]ψ)`
5. **Composition:** `[!φ][!ψ]χ ↔ [!(φ ∧ [!φ]ψ)]χ`

These axioms provide a complete axiomatization and establish that PAL is **equally expressive** as basic epistemic logic EL (without common knowledge). With common knowledge, however, the situation is more complex.

### 2.3 Closure Properties

**Public Announcement Closure Theorem** (SEP): Let M = (W, R, V) be a Kripke model and φ a formula true at at least one world in W. If R_a is reflexive (resp. transitive, Euclidean), then R[!φ]_a is also reflexive (resp. transitive, Euclidean). However, seriality is **not** preserved — announcing φ may eliminate all successors of a remaining world, violating seriality.

### 2.4 Moore Sentences and Unsuccessful Updates

A **Moore sentence** has the form `p ∧ ¬K_a p` ("p is true but agent a doesn't know it"). This sentence can be true but its public announcement makes it false: after announcing `p ∧ ¬K_a p`, the agent learns p, so `K_a p` becomes true, making `p ∧ ¬K_a p` false. This phenomenon is called an **unsuccessful update** (Gerbrandy 1998). The announcement is self-refuting, demonstrating that `[!(p ∧ ¬K_a p)](p ∧ ¬K_a p)` is unsatisfiable.

This has deep connections to the **Fitch paradox**: the principle that all truths are knowable (`∀p(p → ◇K p)`) is inconsistent with the existence of unknown truths. Van Benthem (2004) proposed interpreting "knowable" as "known after an announcement," yielding the dynamic operator `◇K_a p` as "there exists an announcement after which a knows p."

### 2.5 Group Knowledge Operators

PAL naturally extends with group knowledge operators:

- **Common knowledge** among group G ⊆ A: $C_G \varphi$ means "everyone in G knows φ, everyone knows that everyone knows φ, ad infinitum." Semantically, $M, w \models C_G \varphi$ iff φ holds at every world reachable via the reflexive transitive closure of $\bigcup_{a \in G} R_a$.

- **Distributed knowledge** among G: $D_G \varphi$ means "if the agents in G pooled their information, they would know φ." Semantically, $M, w \models D_G \varphi$ iff φ holds at every world reachable via $\bigcap_{a \in G} R_a$.

The inclusion of common knowledge in PAL introduces technical difficulties—adding common knowledge to PAL increases expressivity beyond basic epistemic logic with common knowledge.

---

## 3. Event Models and Action Models

### 3.1 The BMS Framework (Baltag, Moss, Solecki)

The dominant approach in DEL, introduced by Baltag, Moss, and Solecki (1998), generalizes PAL to handle **complex informative events** where different agents may have different perspectives on what occurs. Their key insight: **informational events can be modeled using the same Kripke-style structures used for informational situations**.

An **event model** (also called **action model**) is a triple:

$$\mathcal{E} = (E, Q, \text{pre})$$

where:
- **E** is a finite non-empty set of **events** (possible actions)
- **Q** = {Q_a}_{a ∈ A} is a family of accessibility relations Q_a ⊆ E × E for each agent (epistemic indistinguishability of events)
- **pre**: E → L is a **precondition function** assigning to each event a formula from the epistemic language that must hold for the event to occur

**Intuition:** Given a scenario (e.g., Ann possibly peeking at Bob's card), one enumerates the possible events—Ann sees the card is red, Ann sees it is white, Ann does not look—and specifies which agents can distinguish which events. Ann knows which event occurs; Bob cannot distinguish any of them.

### 3.2 Pointed Event Models

A **pointed event model** (E, e) designates a specific actual event e ∈ E. In the DEL language, these appear as modalities `[E, e]`:

$$\varphi ::= p \mid \varphi \wedge \varphi \mid \neg \varphi \mid [a]\varphi \mid C_G \varphi \mid [\mathcal{E}, e]\varphi$$

The formula `[E, e]φ` reads: "after event e occurs (within event model E), φ holds."

### 3.3 Multi-Pointed Event Models

A **multi-pointed event model** (E, E₀) designates a set E₀ ⊆ E of designated (actual) events. This generalizes single-pointed models and is useful for modeling non-deterministic actions or situations where the actual event is uncertain even to an omniscient observer. Multi-pointed event models also arise naturally in modeling **non-deterministic choice** and **sequential composition** of actions:

- **Non-deterministic choice** `E ∪ F`: the event is either from E or from F.
- **Sequential composition** `E ; F`: first an event from E occurs, then an event from F.

---

## 4. Product Update Mechanism

### 4.1 Definition

The **product update** is the central semantic operation of DEL, constructing a new Kripke model from an existing epistemic model and an event model. Given:

- Epistemic model M = (W, R, V)
- Event model E = (E, Q, pre)

The **product update** M ⊗ E = (W', R', V') is defined:

- **States:** $W' = \{(w, e) \in W \times E \mid M, w \models \text{pre}(e)\}$ — pairs of worlds and events whose precondition is satisfied
- **Accessibility:** $(w, e) R'_a (v, f) \iff wR_av \text{ and } eQ_af$ — an agent considers (v,f) possible from (w,e) iff she cannot distinguish w from v **and** cannot distinguish event e from event f
- **Valuation:** $(w, e) \in V'(p) \iff w \in V(p)$ — propositional facts are unchanged by merely communicative events

### 4.2 Semantic Clause

$$M, w \models [\mathcal{E}, e]\varphi \iff (M, w \models \text{pre}(e)) \implies (M \otimes \mathcal{E}, (w, e) \models \varphi)$$

If the precondition is not satisfied, the formula is vacuously true.

### 4.3 Properties of Product Update

Van Benthem (2001) characterizes product update as satisfying three key properties:

1. **Perfect recall**: the agents remember what they knew before the action
2. **No miracles**: the agents only learn what is warranted by the action structure
3. **Uniformity**: the update applies the same transformation regardless of the actual state

Product update subsumes public announcement as a special case: a public announcement of φ corresponds to a single-event action model with precondition φ and reflexive accessibility for all agents (everyone knows the event is occurring).

### 4.4 Separation of Static and Dynamic Information

A crucial advantage of the BMS framework is that **static information** (what agents know about the world) and **dynamic information** (the structure of the communicative event) can be cleanly separated. The same event model can be applied to different epistemic models, correctly computing the outcomes in each case. This modularity is a major source of the framework's power and generality.

---

## 5. Private and Semi-Private Announcements

### 5.1 Fully Private Announcements

A **private announcement** of φ to a subgroup G ⊆ A is modeled by an event model with two events:

- Event e₁: precondition φ (the announcement occurs), observed by agents in G
- Event e₂: precondition ⊤ (nothing happens), the "null" event

Agents in G can distinguish e₁ from e₂; agents not in G cannot distinguish them (they consider both events possible). After the update, agents in G learn φ while outsiders remain ignorant:

$$[\text{private}_{G}(\varphi)]\psi$$

### 5.2 Semi-Private (Suspicious) Announcements

In a **semi-private** announcement, outsiders may be aware that *something* happened but are uncertain about what. This is modeled by modifying the event model so that outsiders can distinguish between different possible events but not pin down the actual one. The BMS framework handles this naturally through the structure of the accessibility relations Q_a on events.

### 5.3 Examples

**Card games** are canonical examples: when Ann peeks at Bob's card:
- Ann observes the card's value (she distinguishes events by card value)
- Bob knows that Ann might have looked (he cannot distinguish "Ann saw red" from "Ann saw white" from "Ann didn't look")
- An observer watching both might see that Ann looked but not what she saw

Such scenarios produce rich higher-order epistemic structures impossible to model with simple public announcements.

---

## 6. Action Model Logic (AML)

### 6.1 Language and Expressivity

**Action Model Logic** (AML) is the name for the full DEL language with event model modalities. AML formulas include:

$$\varphi ::= p \mid \neg\varphi \mid \varphi \wedge \varphi \mid [a]\varphi \mid [\mathcal{E}, e]\varphi$$

where (E, e) ranges over pointed event models. AML is strictly more expressive than PAL when common knowledge is included. Without common knowledge, AML and PAL have the same expressivity as basic epistemic logic (van Benthem, van Eijck & Kooi 2006).

### 6.2 Reduction Axioms for AML

Like PAL, AML admits **reduction axioms** that eliminate action model operators in favor of static epistemic formulas:

1. **Atoms:** `[E, e]p ↔ (pre(e) → p)`
2. **Negation:** `[E, e]¬φ ↔ (pre(e) → ¬[E, e]φ)`
3. **Conjunction:** `[E, e](φ ∧ ψ) ↔ ([E, e]φ ∧ [E, e]ψ)`
4. **Knowledge:** $[\mathcal{E}, e][a]\varphi \leftrightarrow (\text{pre}(e) \to \bigwedge_{eQ_af} [a][\mathcal{E}, f]\varphi)$

The critical axiom (4) wraps the product update: after event e, agent a knows φ iff for every event f indistinguishable from e for a, agent a already knew that [E, f]φ.

### 6.3 Completeness

Completeness is proved through reduction: every AML formula reduces to an equivalent formula in the base epistemic language, so completeness follows from completeness of the underlying epistemic logic. The reduction terminates because the complexity metric strictly decreases at each step.

---

## 7. Bisimulation and Expressivity Results

### 7.1 Bisimulation

Two pointed Kripke models (M, w) and (N, v) are **bisimilar** if there exists a relation Z ⊆ W_M × W_N satisfying:
- **Atoms:** if wZv then w and v agree on all propositional variables
- **Forth:** if wZv and wR_au, then ∃u' with vR_au' and uZu'
- **Back:** if wZv and vR_au', then ∃u with wR_au and uZu'

Bisimilar pointed models satisfy exactly the same modal formulas. This extends to DEL: bisimulation-invariant properties of pointed models are exactly those expressible in the modal language.

### 7.2 Action Emulation

Two pointed event models (E, e) and (F, f) are **action-emulation equivalent** if they produce bisimilar results on all input models. Action emulation is the dynamic analogue of bisimulation for event models.

### 7.3 Expressivity Hierarchy

The expressivity landscape of DEL variants:

- **PAL** (without common knowledge) = **EL** (basic epistemic logic)
- **AML** (without common knowledge) = **EL**
- **PAL + C_G** (with common knowledge) ⊂ **AML + C_G** — AML is strictly more expressive
- **AML + C_G** ⊂ **Epistemic Temporal Logic** (ETL)

Complexity results (Lutz 2006, Aucher & Schwarzentruber 2013):
- PAL model checking: PSPACE-complete
- AML model checking: PSPACE-complete
- PAL satisfiability: NEXPTIME-complete (with common knowledge)

---

## 8. Belief Revision via DEL

### 8.1 From Knowledge to Belief

Standard DEL with knowledge operators satisfies **monotonicity**: once K_a φ holds, it persists through all updates. This is because knowledge is factive (K_a φ → φ) and updates only eliminate worlds. But belief (B_a φ) need not be monotone—agents can **change their minds**.

In the AGM tradition (Alchourrón, Gärdenfors, Makinson 1985), belief revision involves three operations:
- **Expansion**: adding a belief
- **Revision**: incorporating possibly contradictory information
- **Contraction**: removing a belief

DEL integrates these into a single logical framework.

### 8.2 Plausibility Models

The standard approach (van Benthem 2007, Baltag & Smets 2008) extends Kripke models with **plausibility orderings**:

$$M = (W, \{\sim_a\}_{a \in A}, \{\leq_a\}_{a \in A}, V)$$

where:
- $\sim_a$ is the epistemic accessibility relation (what agent a considers possible)
- $\leq_a$ is a **plausibility ordering** on the worlds (where w ≤_a v means "w is at least as plausible as v for agent a")
- The most plausible worlds determine the agent's beliefs

**Belief** is defined as truth in the most plausible worlds:

$$M, w \models B_a \varphi \iff \text{for all } v \in \text{Min}_{\leq_a}(\sim_a(w)), \; M, v \models \varphi$$

**Conditional belief**: $B_a^\psi \varphi$ means "a believes φ given ψ":

$$M, w \models B_a^\psi \varphi \iff \text{for all } v \in \text{Min}_{\leq_a}(\{u \mid u \sim_a w \text{ and } M, u \models \psi\}), \; M, v \models \varphi$$

### 8.3 Qualitative vs. Quantitative Approaches

- **Qualitative** (van Benthem 2007, Baltag & Smets 2008): comparative plausibility relations. Better suited for logical analysis. Supports conditional belief, safe belief, defeasible knowledge.
- **Quantitative** (Aucher 2005, van Ditmarsch 2005): degrees of belief and plausibility, weighted structures. More fine-grained but harder to axiomatize.

### 8.4 Soft and Hard Information

DEL distinguishes:
- **Hard information** (public announcement): irrevocable, eliminates worlds
- **Soft information** (belief revision): revocable, reorders plausibility

The `[*φ]` operator for belief revision with φ transforms the plausibility ordering to make φ-worlds most plausible, modeling what AGM calls *revision*:

$$\neg p \wedge B_a p \wedge [*\neg p] B_a \neg p$$

reads: "p is false, a believes p, but after revising with ¬p, a believes ¬p."

### 8.5 The AGM Success Postulate and Higher-Order Beliefs

In standard AGM, the **success postulate** states that after revision with φ, the agent believes φ. In DEL, this fails for Moore sentences: after revising with `p ∧ ¬B_a p`, the agent cannot coherently believe the conjunction. This is expected—higher-order belief change in DEL is richer than propositional AGM.

---

## 9. Asynchronous Updates in Multi-Agent Scenarios

### 9.1 Asynchronous Communication

In realistic multi-agent systems, agents may receive information at different times. **Asynchronous DEL** extends the standard framework to handle:

- Messages received with delays
- Agents acting on partial or outdated information
- Non-simultaneous observations

### 9.2 Concurrent Actions

Van Ditmarsch, van der Hoek, and Kooi (2003) extended DEL to model **concurrent** actions—when two or more events occur simultaneously. The interaction between concurrent events creates complications not present in sequential models, as the combined effect may differ from any sequential ordering.

### 9.3 Protocols and Strategies

DEL provides formal tools for reasoning about **epistemic protocols**:
- Which sequences of communicative acts achieve a desired epistemic goal?
- What is the minimal number of announcements to reach common knowledge?
- How do private and public announcements interact in repeated communication?

---

## 10. DEL for Epistemic Planning

### 10.1 Epistemic Planning Problem

The **epistemic planning problem** asks: given an initial epistemic model, a set of available actions (event models), and a goal formula φ, does there exist a sequence of actions leading to a state satisfying φ?

This is significantly harder than classical planning because:
- The state space is exponentially larger (Kripke models vs. propositional states)
- Negative introspection goals (e.g., "a does not know that b knows p") are expressible
- Higher-order knowledge goals interact with action observability

### 10.2 Tractable Compilation

Several approaches aim to make epistemic planning **tractable**:

- **Propositional compilation**: translating epistemic models into propositional representations (Kominis & Geffner 2015)
- **Uniform strategies**: restricting to classes of event models with bounded complexity
- **Symbolic methods**: BDD-based representations of Kripke models

### 10.3 First-Order DEL for Planning

Recent work (arXiv) develops a **first-order version of DEL** combining higher-order reasoning with first-order expressiveness. In this framework:

$$\exists x \, K_x \exists y \, \text{blocks\_door}(y)$$

is a well-formed formula. First-order action models and **product updates** enable epistemic action schemas in the spirit of PDDL, providing compact problem-independent domain descriptions. The metatheory includes axiomatic normal term-modal logics with completeness via reduction axioms (Dynamic Term-Modal Logics for First-Order Epistemic Planning).

---

## 11. Connections to Temporal Logic (DTML)

### 11.1 Dynamic-Temporal Epistemic Logic

DEL has deep connections to **Epistemic Temporal Logic** (ETL). While DEL focuses on the *effects* of specific actions, ETL tracks how knowledge evolves over *time*. The combination yields **Dynamic-Temporal Modal Logic** (DTML):

- **Past operators**: `[Past]φ` means "φ was true before the last action"
- **Since operators**: temporal operators tracking the history of epistemic changes
- **Branching time**: different possible futures arising from different action sequences

Sack (2007) and Aucher & Herzig (2007) developed formal systems adding temporal operators to DEL, enabling reasoning about what agents knew *before* an event—the "converse" direction.

### 11.2 Merging Frameworks

Van Benthem, Gerbrandy, Hoshi, and Pacuit (2009) systematically studied the relationship between DEL and ETL, showing that:
- DEL can be embedded into ETL (every DEL model generates a temporal tree)
- ETL is strictly more expressive than DEL (ETL can express temporal patterns not capturable by finite action sequences)
- The two frameworks provide complementary perspectives: DEL for *local* analysis of action effects; ETL for *global* analysis of temporal patterns

---

## 12. Formal Syntax Summary

### 12.1 PAL Syntax

$$\varphi ::= p \mid \neg\varphi \mid \varphi \wedge \varphi \mid [a]\varphi \mid C_G\varphi \mid [!\varphi]\varphi$$

### 12.2 AML (Full DEL) Syntax

$$\varphi ::= p \mid \neg\varphi \mid \varphi \wedge \varphi \mid [a]\varphi \mid C_G\varphi \mid [\mathcal{E}, e]\varphi$$

### 12.3 DEL with Belief Revision

$$\varphi ::= p \mid \neg\varphi \mid \varphi \wedge \varphi \mid [a]\varphi \mid B_a\varphi \mid B_a^\psi\varphi \mid [*\varphi]\varphi \mid [\mathcal{E}, e]\varphi$$

### 12.4 Key Semantic Definitions

| Operator | Meaning | Semantics |
|----------|---------|-----------|
| `[a]φ` | a knows/believes φ | ∀v: wR_av ⟹ M,v ⊨ φ |
| `C_G φ` | common knowledge in G | φ holds along all (∪R_a)* paths |
| `D_G φ` | distributed knowledge in G | ∀v: w(∩R_a)v ⟹ M,v ⊨ φ |
| `[!φ]ψ` | after announcing φ, ψ holds | M⊨φ ⟹ M\|φ ⊨ ψ |
| `[E,e]φ` | after event e, φ holds | M⊨pre(e) ⟹ M⊗E,(w,e) ⊨ φ |
| `B_a φ` | a believes φ | Min_{≤a}(~a(w)) ⊆ ⟦φ⟧ |
| `[*φ]ψ` | after revising with φ, ψ | plausibility reorder then check ψ |

---

## 13. Applications

### 13.1 Security Protocols

DEL provides formal verification tools for cryptographic and security protocols (Wang, Kuppusamy & van Eijck 2009). Key applications:

- **Protocol verification under common knowledge**: ensuring all parties achieve the required epistemic states after protocol execution
- **Privacy analysis**: modeling which agents learn what information during protocol runs
- **Attack detection**: identifying protocol steps where an adversary gains unintended knowledge

### 13.2 Game Theory

DEL has extensive applications in game theory (van Benthem 2013):

- **Extensive-form games**: modeling information sets and information updates as players observe moves
- **Mechanism design**: designing communication protocols that achieve desired strategic outcomes
- **Epistemic game theory**: characterizing solution concepts (Nash equilibrium, backward induction) in terms of epistemic conditions expressible in DEL

Baltag (2002) developed a logic for "suspicious players" combining epistemic actions with belief updates in game-theoretic settings.

### 13.3 Social Epistemology

DEL analyzes social knowledge phenomena:

- **Gossip protocols**: what is the minimum number of phone calls for everyone to know everyone's secret?
- **Voting and judgment aggregation**: how do public and private signals affect group beliefs?
- **Network epistemology**: how does information flow through social networks?
- **Persuasion and influence**: modeling belief change under social pressure

### 13.4 Speech Act Theory

DEL connects naturally to speech act theory (Austin 1962, Searle 1969). Public announcements model **assertive** speech acts. DEL refines Searle's success conditions:

- The speaker's *knowledge* is a precondition: announcing K_a φ rather than bare φ
- The informativity condition ("H doesn't already know p") should be "p is not common knowledge"—since DEL tracks higher-order knowledge, an announcement can be informative at higher epistemic levels even when first-order knowledge is already shared

DEL also analyzes **questions** as epistemic requests: the question "Do you know φ?" can itself convey information, leading to scenarios where the answer is only knowable *after* the question is posed (van Benthem 2006).

---

## 14. Alternatives, Extensions, and Criticisms

### 14.1 Syntactic Concerns

A common criticism of DEL is that action models appear as **syntactic objects** in the language—they are essentially finite Kripke structures embedded in formulas. Baltag and Moss proposed alternative languages maintaining event-model semantics without directly embedding models (Baltag & Moss 2004). Alternatives using **hybrid logic** (ten Cate 2002) and **algebraic logic** (Baltag, Coecke & Sadrzadeh 2005, 2007) have also been developed.

### 14.2 Factual Change

Standard DEL handles only **epistemic change** (changes in what agents know) with propositional facts remaining constant. Extensions to **ontic change** (factual change, assignment operators) have been developed by van Ditmarsch, van der Hoek & Kooi (2005) and van Benthem, van Eijck & Kooi (2006), allowing actions that change the truth values of propositions (e.g., opening a door, flipping a switch) alongside epistemic effects.

### 14.3 Probability and DEL

Van Benthem, Gerbrandy & Kooi (2009) combined DEL with **probabilistic reasoning**, extending product update to probabilistic Kripke models where each world carries a probability weight. This enables modeling of:

- Bayesian updating after announcements
- Probabilistic beliefs and degrees of confidence
- Stochastic events in multi-agent settings

### 14.4 Justification Logic and DEL

Connections between DEL and **justification logic** (Renne 2008) allow tracking not just *what* agents know but *why* they know it—the evidential basis for beliefs. This is important for modeling argumentation, evidence-based reasoning, and justified belief change.

### 14.5 Evidential Dynamics

Baltag and Renne (SEP, §4.5) discuss **evidential dynamics**—tracking how an agent's body of evidence evolves through actions. Combined with plausibility models, this yields accounts of **justified belief** that respond appropriately to both hard evidence (announcements) and soft evidence (suggestions, defeasible testimony).

---

## 15. Key Formal Results

### 15.1 Completeness Results

| Logic | Axiomatization | Method |
|-------|---------------|--------|
| PAL (no C_G) | EL axioms + reduction axioms | Reduction to EL |
| PAL + C_G | EL+C axioms + PAL reductions | Non-trivial; see Baltag et al. |
| AML (no C_G) | EL axioms + AML reductions | Reduction to EL |
| AML + C_G | EL+C axioms + AML reductions | Reduction; requires care with C_G |
| DEL + belief revision | Plausibility-based axioms | Canonical model + reduction |

### 15.2 Decidability

All standard DEL systems are decidable. The finite model property holds for the base logics, and reduction axioms transfer decidability from the static to the dynamic language.

### 15.3 Complexity

- PAL model checking: **P** (polynomial, same as modal logic)
- PAL satisfiability (no C_G): **PSPACE-complete**
- PAL satisfiability (with C_G): **EXPTIME-complete**
- AML model checking: **PSPACE-complete**
- DEL epistemic planning (general): **undecidable** for sufficiently rich languages; decidable with restrictions

---

## 16. The BMS Framework in Detail

### 16.1 Historical Development

The BMS framework (Baltag, Moss & Solecki 1998) arose from the need to model complex multi-agent informational events. Prior approaches:

- **Plaza (1989)**: Public announcement logic—single-event public communications
- **Gerbrandy & Groeneveld (1997)**: Non-wellfounded set theory for multi-perspective updates
- **Van Ditmarsch (2000)**: Knowledge games with equivalence-preserving transformations

BMS unified and generalized these into a single framework using action models and product update, becoming the **dominant approach** in the field.

### 16.2 Epistemic Programs

Baltag & Moss (2004) introduced **Logics for Epistemic Programs**, extending the BMS framework with:
- **Program composition**: sequential execution of actions `E ; F`
- **Program choice**: non-deterministic choice `E ∪ F`
- **Program iteration**: `E*` (repeat E any finite number of times)

This connects DEL to **Propositional Dynamic Logic** (PDL), creating a framework where epistemic actions are first-class programs composable via standard programming constructs.

### 16.3 Relation to Situation Calculus

Van Ditmarsch, Herzig & De Lima (2011) established formal connections between DEL and the **situation calculus**, showing that DEL's product update can be encoded as situation calculus successor state axioms, and conversely. This bridges the multi-agent epistemic perspective of DEL with the classical AI planning perspective of situation calculus.

---

## 17. Open Problems and Directions

Several open problems and research directions have been identified in the surveyed literature:

1. **Completeness proofs** for concurrent DEL (van Ditmarsch et al. 2003) remain elusive
2. **Infinite event models**: extending DEL beyond finite action models
3. **Continuous dynamics**: combining DEL with continuous-time processes
4. **Learning theory**: DEL models of inductive learning and iterated belief revision
5. **Social network epistemology**: scaling DEL to large-scale social networks
6. **Computational tractability**: practical algorithms for epistemic planning in realistic domains
7. **The relation between DEL and temporal approaches** to belief revision remains "incompletely understood" (IEP survey)
8. **Quantified DEL**: first-order dynamic epistemic logic is in early stages

---

## References

- Baltag, A., Moss, L.S., & Solecki, S. (1998). "The logic of public announcements, common knowledge, and private suspicions." *Proc. TARK 98*, 43–56.
- Baltag, A. & Moss, L.S. (2004). "Logics for epistemic programs." *Synthese*, 139, 165–224.
- Baltag, A. & Renne, B. (2016). "Dynamic Epistemic Logic." *Stanford Encyclopedia of Philosophy*.
- Baltag, A. & Smets, S. (2008). "A qualitative theory of dynamic interactive belief revision." *Proc. 7th LOFT*, 13–60.
- Gerbrandy, J. & Groeneveld, W. (1997). "Reasoning about information change." *J. Logic, Lang., Inform.*, 6, 147–169.
- Hintikka, J. (1962). *Knowledge and Belief.* Cornell University Press.
- Lutz, C. (2006). "Complexity and succinctness of public announcement logic." *Proc. AAMAS 06*.
- Plaza, J. (1989/2007). "Logics of public communications." *Synthese*, 158(2), 165–179.
- van Benthem, J. (2007). "Dynamic logic of belief revision." *J. Applied Non-Classical Logics*, 17(2), 129–155.
- van Benthem, J. (2011). *Logical Dynamics of Information and Interaction.* Cambridge University Press.
- van Benthem, J., van Eijck, J., & Kooi, B. (2006). "Logics of communication and change." *Inf. and Computation*, 204(11), 1620–1662.
- van Ditmarsch, H.P., van der Hoek, W., & Kooi, B. (2007). *Dynamic Epistemic Logic.* Springer.
- van Ditmarsch, H., Herzig, A., & De Lima, T. (2011). "From situation calculus to dynamic epistemic logic." *J. Logic and Computation*, 21(2), 179–204.
- Wang, Y., Kuppusamy, L., & van Eijck, J. (2009). "Verifying epistemic protocols under common knowledge." *Proc. 12th TARK*, 257–266.

---

*This document was compiled from peer-reviewed encyclopedic sources (IEP, SEP), foundational papers, and current research indexed on arXiv. All formal notation follows the conventions of the DEL community as established by Baltag, Moss, Solecki, van Ditmarsch, van der Hoek, Kooi, and van Benthem.*
