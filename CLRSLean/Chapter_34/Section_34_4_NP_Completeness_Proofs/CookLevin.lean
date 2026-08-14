import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.ReachableAlphabet
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Configuration
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.CircuitBuilder
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.CircuitBuilder.ConstantPool
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.CircuitBuilder.FiniteFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BundleCombinators
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StackPrimitives
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StackSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.FiniteLookup
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StackCircuits
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.ControlCircuits
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.PrimitiveRowSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.Validity
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.ValidityBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.Workspace
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StatementCircuits
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BoundaryCircuits
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.Finishing
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization

/-!
# Cook--Levin infrastructure

The first layer extracts a finite program-support over-approximation of the
alphabet used by any fixed bundled TM2 machine and proves that the invariant is
preserved by finite execution. The configuration layer gives finite bounded
row codes, exact two-way codecs, stuttering execution semantics, and a uniform
height bound. The circuit-builder layer supplies proved fresh-wire allocation,
a reusable exact two-gate Boolean constant pool, Boolean combinators, and
exact-cost finite-family mux/equality kernels.  The
pure tableau layer fixes exact row coordinates and adds typed stack views,
zero-gate stack replacement, exact-cost whole-row mux/equality, one-hot codecs,
and fresh external-input layouts.  It also gives pure fixed-width push, peek,
and pop operations on raw Boolean stack bundles, with supported-head codecs,
coordinate laws, and raw one-hot preservation under explicit capacity
premises.  The canonical semantics bridge proves exact list-level push, peek,
and pop behavior and projects successful whole-row evaluation to every decoded
machine stack.  The wire layer lifts these operations to circuit builders:
push and peek allocate no gates, positive-width pop allocates one OR, and
capacity allocates one NOT, all with row-frame and list-semantic contracts.
The generic finite-lookup layer adds exact-cost one-hot maps, pair maps, and
Boolean predicate queries using only static finite preimages.
The finite-control layer adds pool-backed state/status encodings, whole-row
control replacement, canonical decoding inversion, and exact state/status
update semantics. The primitive-row bridge proves that wire-level push and pop
decode as complete dependent-stack updates and exposes pop's old head as an
exact canonical one-hot family. The recursive statement compiler now covers
all seven bundled statement constructors through finite state/symbol truth
tables, proves exact {lit}`stepAux` semantics under explicit prefix capacity, and
publishes exact and affine emitted-gate bounds. The local transition layer now
widens the current public row, serially compiles every finite program label
from that same workspace source, selects a complete row, narrows with an
explicit fit bit, and compares the entire result to the next public row.  Its
final theorem accepts exactly {lit}`stutterStep`, with an exact structural gate
delta and a fixed-machine affine emitted-gate bound.  Canonical row validity,
finite-label dispatch, and the complete local transition all expose such
height-independent coefficients; the principal predicate builders also close
to well-formed general circuits without changing evaluation.  The fresh-layout
layer allocates two consecutive nonaliasing rows at
an arbitrary external-input offset, preserves a caller-supplied assignment
outside them, and proves local completeness; its canonical wrapper exports the
same finite assignment shape used by general-circuit satisfiability.  Exact
boundary constraints compare complete initial/accepting rows through one
shared static pool, reject unencodable concrete targets by an actual false
wire, and provide a symbolic-input-stack initial form.  The normalized verifier
sublayer packages an NP verifier with its concrete TM2 and polynomial
certificate bound, then derives polynomial input, stuttering-horizon, and
uniform stack-height envelopes without changing the underlying bounded run.
Whole-tableau circuitization allocates every row, constrains row validity and
adjacent transitions, recovers the bounded certificate shape, fixes exact
initial and accepting boundaries, and closes their conjunction as a
well-formed general circuit.  Its satisfiability is equivalent to language
membership, and its gate count has an explicit fixed-verifier polynomial
bound. The validity layer builds canonical row
validation with exact semantics and gate cost, while the workspace layer gives
verified constant-cost widen/narrow bridges for one bundled transition.
-/
