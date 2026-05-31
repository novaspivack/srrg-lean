import Mathlib
import SrrgLean.Core.TheorySpace
import SrrgLean.Core.RepresentationCapacity
import SrrgLean.Core.ConstraintFunctional
import SrrgLean.Core.ViabilityFunctional

/-!
# Core — CMCA encoding language and Kolmogorov complexity

The **Chiral Minkowski Cellular Automaton (CMCA)** is the Level-1 algebraic
certificate: update rule `p(L,C,R) = C + R - CR - LCR` over `GF(7)`.

This module formalizes:
1. The CMCA local rule as a `ZMod 7` polynomial.
2. An abstract **CMCA encoding language** — programs that describe SRRG theories.
3. The **CMCA Kolmogorov complexity** functional, decomposed into self-description
   and conditional components matching the SRRG MDL structure in `Bridges/ToMDL.lean`.
4. Interfaces for Turing universality and Kolmogorov–MDL identification.

Reference universality certificate: `phimdl_turing_universal` (ugp-lean-exp, CatAL).
Reference scalar bridge: `SRRGCABridge.kCMCA` (ugp-lean-exp, CatAL).
-/

namespace SrrgLean.Core.CMCALanguage

variable {α : Type*}

/-! ## §1 — CMCA local rule over GF(7) -/

/-- CMCA neighbourhood triple over `GF(7)`. -/
abbrev CMCACell := ZMod 7

/-- **CMCA update rule** (Level-1 algebraic certificate):
    `p(L,C,R) = C + R - C·R - L·C·R` over `GF(7)`. -/
def cmcaUpdate (L C R : CMCACell) : CMCACell :=
  C + R - C * R - L * C * R

@[simp] theorem cmcaUpdate_def (L C R : CMCACell) :
    cmcaUpdate L C R = C + R - C * R - L * C * R := rfl

/-- Diagonal self-referential evaluation: `p(x,x,x)` over `GF(7)`. -/
def cmcaDiagonal (x : CMCACell) : CMCACell :=
  cmcaUpdate x x x

/-! ## §2 — MDL components (aligned with `Bridges/ToMDL.lean`) -/

/-- SRRG MDL description length: `K[S] = B - F[S]`. -/
noncomputable def mdlDescLen
    (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α) (s : α) : ℝ :=
  B - Viability P C s

/-- Self-description component: `L[S] = B - R[S]`. -/
noncomputable def mdlSelfDescLen
    (P : RepCapacityProfile α) (B : ℝ) (s : α) : ℝ :=
  B - P.R s

/-- Conditional component: `L[data|S] = C_Λ[S]`. -/
noncomputable def mdlConditionalLen
    (C : ConstraintProfile α) (s : α) : ℝ :=
  C.functional s

/-- **mdl_decomp** (zero sorry): MDL description length decomposes. -/
theorem mdl_decomp
    (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α) (s : α) :
    mdlDescLen P B C s = mdlSelfDescLen P B s + mdlConditionalLen C s := by
  simp [mdlDescLen, mdlSelfDescLen, mdlConditionalLen, Viability, RepCapacity]
  ring

/-- **mdl_self_desc_eq** (zero sorry): `L[S] = B - R[S]`. -/
theorem mdl_self_desc_eq
    (P : RepCapacityProfile α) (B : ℝ) (s : α) :
    mdlSelfDescLen P B s = B - P.R s := rfl

/-- **mdl_conditional_eq** (zero sorry): `L[data|S] = C_Λ[S]`. -/
theorem mdl_conditional_eq
    (C : ConstraintProfile α) (s : α) :
    mdlConditionalLen C s = C.functional s := rfl

/-- **cmca_k_eq_barrier_minus_viability** (zero sorry):
    CMCA-language MDL cost = `B - F[S]`. -/
theorem cmca_k_eq_barrier_minus_viability
    (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α) (s : α) :
    mdlDescLen P B C s = B - Viability P C s := rfl

/-! ## §3 — Abstract CMCA program and encoding language -/

/-- An abstract CMCA **program**. -/
structure CMCAProgram where
  descLength : ℕ
  descLength_pos : 0 < descLength

/-- A **CMCA encoding language** for theories of type `α`. -/
structure CMCAEncodingLanguage (α : Type*) where
  Program : Type*
  length : Program → ℕ
  length_nonneg : ∀ p, 0 ≤ (length p : ℤ)
  encode : α → Program
  decode : Program → Option α
  encode_decode : ∀ s, decode (encode s) = some s

/-! ## §4 — CMCA Kolmogorov profile -/

/-- Real-valued CMCA Kolmogorov complexity (= SRRG MDL description length). -/
noncomputable def cmcaK_real
    (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α) (s : α) : ℝ :=
  mdlDescLen P B C s

/-- Self-description component in CMCA language. -/
noncomputable def cmcaK_self
    (P : RepCapacityProfile α) (B : ℝ) (s : α) : ℝ :=
  mdlSelfDescLen P B s

/-- Conditional component in CMCA language. -/
noncomputable def cmcaK_cond
    (C : ConstraintProfile α) (s : α) : ℝ :=
  mdlConditionalLen C s

/-- **cmca_k_decomp** (zero sorry): CMCA Kolmogorov decomposes as self + conditional. -/
theorem cmca_k_decomp
    (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α) (s : α) :
    cmcaK_real P B C s = cmcaK_self P B s + cmcaK_cond C s :=
  mdl_decomp P B C s

/-! ## §5 — Turing universality interface -/

/-- **CMCA Turing universality** (interface).

    Certified: `phimdl_turing_universal` in ugp-lean-exp (CatAL, zero sorry). -/
structure CMCATuringUniversal (α : Type*) (L : CMCAEncodingLanguage α) : Prop where
  universal : True  -- placeholder pending ugp-lean-exp import bridge

/-- **Kolmogorov invariance** (up to additive constant) between two CMCA languages. -/
def KolmogorovInvariance {α : Type*} (L₁ L₂ : CMCAEncodingLanguage α) : Prop :=
  ∃ c : ℕ, ∀ s,
    |((L₁.length (L₁.encode s)) : ℤ) - ((L₂.length (L₂.encode s)) : ℤ)| ≤ c

/-- **cmca_universality_invariance** (zero sorry for reflexivity; nontrivial case open).

    For the same language, invariance constant is 0. The cross-language case
    (CMCA ↔ other universal language) requires the full universality chain. -/
theorem cmca_universality_invariance
    {α : Type*} (L : CMCAEncodingLanguage α)
    (_h_univ : CMCATuringUniversal α L) :
    KolmogorovInvariance L L := by
  use 0
  intro s
  simp

/-! ## §6 — Algebraic description length (K_alg route)

### O(1) invariance and argmax/argmin preservation

Classical Kolmogorov invariance: for universal reference languages `U, U'`,
`K_U(x) = K_{U'}(x) + c` where `c` depends only on the compilers `(U, U')`, not on `x`.

Therefore:
- `argmin_x K_U(x) = argmin_x (K_alg(x) + c) = argmin_x K_alg(x)`
- Since `K[S] = B - F[S]` with constant `B`, `argmin K = argmax F` for `K_alg` iff it
  holds for `K_CMCA`; the biconditional OP9 argmax/argmin equivalence is preserved
  under any fixed additive shift.

Exact equality `K_CMCA(S) = K_alg(S)` is **not** required for OP9 argmin closure —
only that the O(1) constant is independent of `S`. CMCA Turing universality
(`phimdl_turing_universal`, ugp-lean-exp) bounds the GTE→CMCA compiler overhead. -/

/-- Default **GTE algebraic atoms** (Lean-certified exact rationals). -/
structure GTEAtoms where
  g1sq : ℚ
  g2sq : ℚ
  N_gen : ℕ
  N_fam : ℕ
  c_H : ℕ

/-- Golden ratio φ = (√5 − 1)/2 from the GTE atom profile. -/
noncomputable def gtePhi : ℝ := (Real.sqrt 5 - 1) / 2

/-- Default GTE atom profile used in the algebraic route. -/
def defaultGTEAtoms : GTEAtoms where
  g1sq := 16 / 125
  g2sq := 2329 / 5400
  N_gen := 3
  N_fam := 5
  c_H := 13

/-- **Algebraic description length** `K_alg`: the SRRG MDL profile expressed over
    GTE atoms. Under the G01 proportionalities this equals `B - F[S]` without Turing
    machine semantics; the `atoms` parameter anchors the GTE interpretation. -/
noncomputable def K_alg
    (_atoms : GTEAtoms) (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α)
    (s : α) : ℝ :=
  cmcaK_real P B C s

/-- Canonical CMCA program length for theory `s` in language `L`. -/
noncomputable def cmcaProgramLen
    {α : Type*} (L : CMCAEncodingLanguage α) (s : α) : ℝ :=
  L.length (L.encode s)

/-- **k_alg_eq_barrier_minus_viability** (zero sorry):

    `K_alg(S) = B - F[S]` from the G01 MDL decomposition
    (`L[S] = B - R[S]`, `L[data|S] = C_Λ[S]`, hence `K = B - F`). -/
theorem k_alg_eq_barrier_minus_viability
    (atoms : GTEAtoms) (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α)
    (s : α) :
    K_alg atoms P B C s = B - Viability P C s :=
  cmca_k_eq_barrier_minus_viability P B C s

/-- **K_alg decomposition** (zero sorry): `K_alg = K_self + K_cond`. -/
theorem k_alg_decomp
    (atoms : GTEAtoms) (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α)
    (s : α) :
    K_alg atoms P B C s =
      cmcaK_self P B s + cmcaK_cond C s := by
  simp [K_alg, cmca_k_decomp]

/-! ### Kolmogorov invariance — argmin preserved under constant shift -/

/-- If `K = K' + c` with `c` independent of `s`, then any minimizer of `K'` minimizes `K`. -/
theorem kolmogorov_invariance_minimizer
    {α : Type*} (K K' : α → ℝ) (c : ℝ) (s₀ : α)
    (h : ∀ s, K s = K' s + c) (hmin : ∀ s, K' s₀ ≤ K' s) :
    ∀ s, K s₀ ≤ K s := by
  intro s
  rw [h s₀, h s]
  linarith [hmin s]

/-- Converse: any minimizer of `K` minimizes `K'`. -/
theorem kolmogorov_invariance_minimizer_reverse
    {α : Type*} (K K' : α → ℝ) (c : ℝ) (s₀ : α)
    (h : ∀ s, K s = K' s + c) (hmin : ∀ s, K s₀ ≤ K s) :
    ∀ s, K' s₀ ≤ K' s := by
  intro s
  have h' : ∀ t, K' t = K t - c := by
    intro t; rw [h t]; ring
  rw [h' s₀, h' s]
  linarith [hmin s]

/-- **kolmogorov_invariance_argmin** (zero sorry):

    A common minimizer exists for `K` and `K'` whenever `K = K' + c` and `s₀`
    minimizes `K'`. Same minimizer minimizes both (OP9 argmin invariance). -/
theorem kolmogorov_invariance_argmin
    {α : Type*} (K K' : α → ℝ) (c : ℝ) (s₀ : α)
    (h : ∀ s, K s = K' s + c) (hmin : ∀ s, K' s₀ ≤ K' s) :
    (∀ s, K s₀ ≤ K s) ∧ (∀ s, K' s₀ ≤ K' s) := by
  have hK := kolmogorov_invariance_minimizer K K' c s₀ h hmin
  exact ⟨hK, kolmogorov_invariance_minimizer_reverse K K' c s₀ h hK⟩

/-- **Argmin equivalence** under a uniform additive shift (zero sorry). -/
theorem argmin_preserved_under_constant_shift
    {α : Type*} (K K' : α → ℝ) (c : ℝ) (s₀ : α)
    (h : ∀ s, K s = K' s + c) :
    (∀ s, K' s₀ ≤ K' s) ↔ (∀ s, K s₀ ≤ K s) := by
  constructor
  · intro hmin s
    exact kolmogorov_invariance_minimizer K K' c s₀ h hmin s
  · intro hmin s
    exact kolmogorov_invariance_minimizer_reverse K K' c s₀ h hmin s

/-! ### GF(7) GTE atom encoding (finite verification) -/

/-- Maximum GF(7) digits per GTE atom field in the compiler (`7³ = 343` states). -/
def gteAtomZ7DigitBound : ℕ := 3

/-- Embed an integer into `GF(7)`. -/
def zmod7OfInt (z : ℤ) : CMCACell := (z : CMCACell)

/-- Encode a rational as two GF(7) digits (numerator, denominator mod 7). -/
def encodeRationalZ7 (q : ℚ) : List CMCACell :=
  [zmod7OfInt q.num, zmod7OfInt q.den]

/-- Encode a natural as one GF(7) digit. -/
def encodeNatZ7 (n : ℕ) : List CMCACell :=
  [zmod7OfInt (n : ℤ)]

theorem encodeRationalZ7_length (q : ℚ) :
    (encodeRationalZ7 q).length ≤ gteAtomZ7DigitBound := by
  simp [encodeRationalZ7, gteAtomZ7DigitBound]

theorem encodeNatZ7_length (n : ℕ) :
    (encodeNatZ7 n).length ≤ gteAtomZ7DigitBound := by
  simp [encodeNatZ7, gteAtomZ7DigitBound]

/-- Per-field GF(7) encodings for a `GTEAtoms` profile. -/
def encodeGTEAtomFields (a : GTEAtoms) : List (List CMCACell) :=
  [encodeRationalZ7 a.g1sq, encodeRationalZ7 a.g2sq,
   encodeNatZ7 a.N_gen, encodeNatZ7 a.N_fam, encodeNatZ7 a.c_H]

theorem encodeGTEAtomFields_length (a : GTEAtoms) :
    ∀ l ∈ encodeGTEAtomFields a, l.length ≤ gteAtomZ7DigitBound := by
  intro l hl
  simp only [encodeGTEAtomFields, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl
  · exact encodeRationalZ7_length a.g1sq
  · exact encodeRationalZ7_length a.g2sq
  · exact encodeNatZ7_length a.N_gen
  · exact encodeNatZ7_length a.N_fam
  · exact encodeNatZ7_length a.c_H

/-! ### CMCA compilation bound (named remaining hypothesis) -/

/-- **CMCA compilation constant**: bounded overhead for compiling one GTE atom
    into CMCA (`log₂(7³)` — three GF(7) digits per atom in the compiler). -/
noncomputable def CMCACompilationConstant : ℝ :=
  Real.log 343 / Real.log 2

theorem CMCACompilationConstant_pos : 0 < CMCACompilationConstant := by
  unfold CMCACompilationConstant
  apply div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 343))
  exact Real.log_pos (by norm_num : (1 : ℝ) < 2)

/-- Three GF(7) digits carry exactly `log₂(343)` bits. -/
theorem gteAtomZ7DigitBound_bits :
    (gteAtomZ7DigitBound : ℝ) * (Real.log 7 / Real.log 2) = CMCACompilationConstant := by
  unfold CMCACompilationConstant gteAtomZ7DigitBound
  field_simp
  rw [show (343 : ℝ) = (7 : ℝ) ^ 3 by norm_num, Real.log_pow 7 3]

/-- **Default GTE atom encodings** (finite verification, zero sorry).

    For each field of `defaultGTEAtoms`, the GF(7) encoding has length ≤ 3.
    Decidable over the five certified atom values (g₁² = 16/125, g₂² = 2329/5400,
    N_gen = 3, N_fam = 5, c_H = 13). -/
theorem defaultGTEAtom_encodings_bounded :
    ∀ l ∈ encodeGTEAtomFields defaultGTEAtoms, l.length ≤ gteAtomZ7DigitBound :=
  encodeGTEAtomFields_length defaultGTEAtoms

/-- **CMCA compiler bound** (named physical obligation — L5 compilation route).

    Every GTE algebraic description compiles to a CMCA program whose length is at
    most `K_alg(S) + CMCACompilationConstant`. The per-atom GF(7) digit bound
    (`defaultGTEAtom_encodings_bounded`, length ≤ 3) gives the constant
    `log₂(343)` per atom; discharging this hypothesis requires linking abstract
    `CMCAEncodingLanguage.encode` to the GTE atom compiler and Kolmogorov
    invariance from `phimdl_turing_universal` (ugp-lean-exp). -/
def CMCACompilerBound
    {α : Type*} (L : CMCAEncodingLanguage α) (atoms : GTEAtoms)
    (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α) : Prop :=
  ∀ s, cmcaProgramLen L s ≤ K_alg atoms P B C s + CMCACompilationConstant

/-- **CMCA compiles algebraic** (zero sorry, conditional on `CMCACompilerBound`). -/
theorem cmca_compiles_algebraic
    {α : Type*} (L : CMCAEncodingLanguage α) (atoms : GTEAtoms)
    (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α) (s : α)
    (h : CMCACompilerBound L atoms P B C) :
    cmcaProgramLen L s ≤ K_alg atoms P B C s + CMCACompilationConstant :=
  h s

/-! ## §7 — Kolmogorov = MDL profile (L4 — algebraic + reference language) -/

/-- Shortest-program Kolmogorov equals the SRRG MDL profile (exact equality, L4). -/
def KolmogorovEqMDLProfile
    {α : Type*} (L : CMCAEncodingLanguage α)
    (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α) : Prop :=
  ∀ s, cmcaProgramLen L s = cmcaK_real P B C s

/-- **CMCA reference language** (named hypothesis for exact L4 equality).

    Physical content: CMCA is the reference language, not merely universal; the
    invariance constant vanishes so canonical program length equals the MDL profile.
    OP9 argmin closure does **not** require this — only `kolmogorov_invariance_argmin`. -/
def CMCAReferenceLanguage
    {α : Type*} (L : CMCAEncodingLanguage α)
    (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α) : Prop :=
  KolmogorovEqMDLProfile L P B C

/-- **kolmogorov_eq_mdl_profile** (conditional on `CMCAReferenceLanguage`).

    Exact L4 equality; discharged when CMCA is proved to be the reference language.
    Argmin-preservation is already proved without this hypothesis. -/
theorem kolmogorov_eq_mdl_profile
    {α : Type*} (L : CMCAEncodingLanguage α)
    (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α)
    (h_ref : CMCAReferenceLanguage L P B C) :
    KolmogorovEqMDLProfile L P B C :=
  h_ref

/-- **Argmin route for L4** (zero sorry): if `s₀` minimizes `K_alg`, it minimizes
    CMCA program length up to the compilation constant (via invariance). -/
theorem argmin_k_alg_iff_argmin_cmca_program
    {α : Type*} (L : CMCAEncodingLanguage α) (atoms : GTEAtoms)
    (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α) (s₀ : α)
    (h_shift : ∀ s, cmcaProgramLen L s = K_alg atoms P B C s + CMCACompilationConstant) :
    (∀ s, K_alg atoms P B C s₀ ≤ K_alg atoms P B C s) ↔
      ∀ s, cmcaProgramLen L s₀ ≤ cmcaProgramLen L s :=
  argmin_preserved_under_constant_shift
    (cmcaProgramLen L) (K_alg atoms P B C) CMCACompilationConstant s₀ h_shift

/-! ## §8 — Theory-space K identification (L6 — algebraic route) -/

/-- Abstract `T.K` equals CMCA Kolmogorov MDL profile (cast to ℝ). -/
def TheoryKEqCMCAK
    {α : Type*} (T : SrrgTheorySpaceFull α)
    (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α) : Prop :=
  ∀ s, (T.K s : ℝ) = cmcaK_real P B C s

/-- Abstract `T.K` equals algebraic description length `K_alg`. -/
def TheoryKEqKAlg
    {α : Type*} (atoms : GTEAtoms) (T : SrrgTheorySpaceFull α)
    (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α) : Prop :=
  ∀ s, (T.K s : ℝ) = K_alg atoms P B C s

/-- `TheoryKEqKAlg` implies `TheoryKEqCMCAK` (zero sorry). -/
theorem theory_k_eq_k_alg_imp_cmca
    {α : Type*} (atoms : GTEAtoms) (T : SrrgTheorySpaceFull α)
    (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α)
    (h : TheoryKEqKAlg atoms T P B C) :
    TheoryKEqCMCAK T P B C := by
  intro s
  rw [h s, K_alg]

/-! ## §9 — Scalar coupling projection -/

/-- Scalar CMCA Kolmogorov: `K_CMCA(g) = -log₂(g² + g)`.

    Matches `SRRGCABridge.kCMCA` (ugp-lean-exp, CatAL). -/
noncomputable def kCMCA_scalar (g : ℝ) : ℝ :=
  -Real.logb 2 (g ^ 2 + g)

end SrrgLean.Core.CMCALanguage
