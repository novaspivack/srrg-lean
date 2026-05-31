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

/-- Flatten per-field GF(7) encodings into one CMCA cell list. -/
def flattenGTEEncoding (a : GTEAtoms) : List CMCACell :=
  (encodeGTEAtomFields a).flatten

theorem flattenGTEEncoding_length (a : GTEAtoms) :
    (flattenGTEEncoding a).length ≤ 5 * gteAtomZ7DigitBound := by
  unfold flattenGTEEncoding encodeGTEAtomFields
  simp only [List.length_flatten]
  have h := encodeGTEAtomFields_length a
  have hsum : (encodeRationalZ7 a.g1sq).length + (encodeRationalZ7 a.g2sq).length +
      (encodeNatZ7 a.N_gen).length + (encodeNatZ7 a.N_fam).length +
      (encodeNatZ7 a.c_H).length ≤ 5 * gteAtomZ7DigitBound := by
    have h1 := h (encodeRationalZ7 a.g1sq) (by simp [encodeGTEAtomFields])
    have h2 := h (encodeRationalZ7 a.g2sq) (by simp [encodeGTEAtomFields])
    have h3 := h (encodeNatZ7 a.N_gen) (by simp [encodeGTEAtomFields])
    have h4 := h (encodeNatZ7 a.N_fam) (by simp [encodeGTEAtomFields])
    have h5 := h (encodeNatZ7 a.c_H) (by simp [encodeGTEAtomFields])
    omega
  exact hsum

/-- CMCA program length in bits (three GF(7) digits per field ⇒ `log₂(343)` per field). -/
noncomputable def cmcaProgramBitLen
    {α : Type*} (L : CMCAEncodingLanguage α) (s : α) : ℝ :=
  cmcaProgramLen L s * (Real.log 7 / Real.log 2)

/-- Five GTE atom fields ⇒ at most `5 · log₂(343)` bits in the concrete compiler. -/
theorem cmcaProgramBitLen_le_five_fields
    {α : Type*} (L : CMCAEncodingLanguage α) (s : α)
    (h_len : (L.length (L.encode s) : ℝ) ≤ (5 * gteAtomZ7DigitBound : ℝ)) :
    cmcaProgramBitLen L s ≤ (5 : ℝ) * CMCACompilationConstant := by
  unfold cmcaProgramBitLen cmcaProgramLen
  have hbits :
      (L.length (L.encode s) : ℝ) * (Real.log 7 / Real.log 2) ≤
        (5 * gteAtomZ7DigitBound : ℝ) * (Real.log 7 / Real.log 2) :=
    mul_le_mul_of_nonneg_right h_len (by
      apply div_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 7))
        (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)))
  calc
    cmcaProgramLen L s * (Real.log 7 / Real.log 2) =
        (L.length (L.encode s) : ℝ) * (Real.log 7 / Real.log 2) := rfl
    _ ≤ (5 * gteAtomZ7DigitBound : ℝ) * (Real.log 7 / Real.log 2) := hbits
    _ = (5 : ℝ) * ((gteAtomZ7DigitBound : ℝ) * (Real.log 7 / Real.log 2)) := by ring
    _ = (5 : ℝ) * CMCACompilationConstant := by
      rw [gteAtomZ7DigitBound_bits]

/-- **Concrete GTE→CMCA encoding language** on `GTEAtoms`.

    Programs are theories; `length` is the flattened GF(7) digit count of the atom
    profile. `encode` / `decode` are identity (the program carries the atom data). -/
def gteEncodingLanguage : CMCAEncodingLanguage GTEAtoms where
  Program := GTEAtoms
  length p := (flattenGTEEncoding p).length
  length_nonneg _ := Int.natCast_nonneg _
  encode := id
  decode p := some p
  encode_decode _ := rfl

theorem gteEncodingLanguage_program_len (a : GTEAtoms) :
    cmcaProgramLen gteEncodingLanguage a = (flattenGTEEncoding a).length := by
  simp [cmcaProgramLen, gteEncodingLanguage]

theorem gteEncodingLanguage_bitlen_bound (a : GTEAtoms) :
    cmcaProgramBitLen gteEncodingLanguage a ≤ (5 : ℝ) * CMCACompilationConstant := by
  have hlen :
      (gteEncodingLanguage.length (gteEncodingLanguage.encode a) : ℝ) ≤
        (5 * gteAtomZ7DigitBound : ℝ) := by
    simp only [gteEncodingLanguage, id, flattenGTEEncoding]
    exact_mod_cast flattenGTEEncoding_length a
  exact cmcaProgramBitLen_le_five_fields gteEncodingLanguage a hlen

/-- **CMCA compiler bound** (L5′ compilation route).

    Every theory compiles to a CMCA program whose **bit length** is at most
    `K_alg(S) + 5 · CMCACompilationConstant` (five atom fields, each ≤ 3 GF(7) digits).
    The universal `∀ L` form is false for arbitrary languages; use
    `CMCACompilerBoundExists` for the existential witness `gteEncodingLanguage`. -/
def CMCACompilerBound
    {α : Type*} (L : CMCAEncodingLanguage α) (atoms : GTEAtoms)
    (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α) : Prop :=
  ∀ s, cmcaProgramBitLen L s ≤ K_alg atoms P B C s + (5 : ℝ) * CMCACompilationConstant

/-- Some CMCA encoding language satisfies the compiler bound (existential form).

    For `α = GTEAtoms`, the witness is `gteEncodingLanguage` (see
    `cmca_compiler_bound_exists_gte_atoms`). -/
def CMCACompilerBoundExists
    (atoms : GTEAtoms) (P : RepCapacityProfile GTEAtoms) (B : ℝ)
    (C : ConstraintProfile GTEAtoms) : Prop :=
  CMCACompilerBound gteEncodingLanguage atoms P B C

/-- **CMCA compiles algebraic** (zero sorry, conditional on `CMCACompilerBound`). -/
theorem cmca_compiles_algebraic
    {α : Type*} (L : CMCAEncodingLanguage α) (atoms : GTEAtoms)
    (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α) (s : α)
    (h : CMCACompilerBound L atoms P B C) :
    cmcaProgramBitLen L s ≤ K_alg atoms P B C s + (5 : ℝ) * CMCACompilationConstant :=
  h s

/-- **Compiler bound for the concrete GTE encoder** (zero sorry).

    Requires `K_alg ≥ 0` (MDL length nonnegative on the profile). -/
theorem cmca_compiler_bound_gte_atoms
    (atoms : GTEAtoms) (P : RepCapacityProfile GTEAtoms) (B : ℝ)
    (C : ConstraintProfile GTEAtoms)
    (hK : ∀ s : GTEAtoms, 0 ≤ K_alg atoms P B C s) :
    CMCACompilerBound gteEncodingLanguage atoms P B C := by
  intro s
  have hleft := gteEncodingLanguage_bitlen_bound s
  have hright :
      (5 : ℝ) * CMCACompilationConstant ≤
        K_alg atoms P B C s + (5 : ℝ) * CMCACompilationConstant := by
    simpa using add_le_add_left (hK s) ((5 : ℝ) * CMCACompilationConstant)
  exact hleft.trans hright

/-- **Existential compiler bound** (zero sorry): witness `gteEncodingLanguage`. -/
theorem cmca_compiler_bound_exists_gte_atoms
    (atoms : GTEAtoms) (P : RepCapacityProfile GTEAtoms) (B : ℝ)
    (C : ConstraintProfile GTEAtoms)
    (hK : ∀ s : GTEAtoms, 0 ≤ K_alg atoms P B C s) :
    CMCACompilerBoundExists atoms P B C :=
  cmca_compiler_bound_gte_atoms atoms P B C hK

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

/-- Choose the natural representative when `x : ℝ` is exactly a natural cast. -/
noncomputable def natOfReal (x : ℝ) (h : ∃ n : ℕ, (n : ℝ) = x) : ℕ :=
  Classical.choose h

/-- **natOfReal_cast** (zero sorry): `(natOfReal x h : ℝ) = x`. -/
theorem natOfReal_cast (x : ℝ) (h : ∃ n : ℕ, (n : ℝ) = x) :
    (natOfReal x h : ℝ) = x :=
  Classical.choose_spec h

/-- Extend a base `SrrgTheorySpaceFull` so `T.K` matches `K_alg` pointwise (cast to ℝ).

    Requires `hNat`: at every theory `s`, `K_alg s` is exactly a natural number cast to ℝ.
    When `K_alg` is not ℕ-valued (e.g. general scalar `-log₂(g²+g)`), use
    `srrg_op9_k_alg_biconditional` in `Bridges/ToMDL.lean` instead. -/
noncomputable def srrgTheorySpaceWithKAlg
    {α : Type u} (atoms : GTEAtoms) (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α)
    (T : SrrgTheorySpaceFull α)
    (hNat : ∀ s, ∃ n : ℕ, (n : ℝ) = K_alg atoms P B C s) : SrrgTheorySpaceFull α :=
  { T with
    K := fun s => natOfReal (K_alg atoms P B C s) (hNat s)
    K_nonneg := fun _ => Int.natCast_nonneg _ }

/-- **TheoryKEqKAlg** for `srrgTheorySpaceWithKAlg` (zero sorry). -/
theorem theory_k_eq_k_alg_for_k_alg_instance
    {α : Type u} (atoms : GTEAtoms) (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α)
    (T : SrrgTheorySpaceFull α)
    (hNat : ∀ s, ∃ n : ℕ, (n : ℝ) = K_alg atoms P B C s) :
    TheoryKEqKAlg atoms (srrgTheorySpaceWithKAlg atoms P B C T hNat) P B C := by
  intro s
  simp [srrgTheorySpaceWithKAlg]
  exact natOfReal_cast (K_alg atoms P B C s) (hNat s)

/-- Extend a base `SrrgTheorySpace` with `K ≡ 0` (ℕ-valued placeholder). -/
def srrgTheorySpaceWithZeroK {α : Type u} (T : SrrgTheorySpace α) : SrrgTheorySpaceFull α where
  toSrrgTheorySpace := T
  K := fun _ => 0
  RecordEquivalent := Eq
  K_nonneg := fun _ => by simp

/-- **TheoryKEqKAlg at the viability barrier** (zero sorry).

    When `Viability[S] = B` for all `S`, `K_alg(S) = 0` and any theory space with
    `T.K ≡ 0` satisfies `TheoryKEqKAlg`. -/
theorem theory_k_eq_k_alg_at_barrier
    {α : Type u} (atoms : GTEAtoms) (T : SrrgTheorySpaceFull α)
    (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α)
    (hK : ∀ s, T.K s = 0) (hV : ∀ s, Viability P C s = B) :
    TheoryKEqKAlg atoms T P B C := by
  intro s
  have h_lhs : (T.K s : ℝ) = 0 := by simpa using congrArg Nat.cast (hK s)
  have h_rhs : K_alg atoms P B C s = 0 := by
    simp [K_alg, cmcaK_real, mdlDescLen, hV s, sub_self]
  rw [h_lhs, h_rhs]

/-- **TheoryKEqKAlg** for `srrgTheorySpaceWithZeroK` when viability equals the barrier. -/
theorem theory_k_eq_k_alg_zero_k_at_barrier
    {α : Type u} (atoms : GTEAtoms) (T : SrrgTheorySpace α)
    (P : RepCapacityProfile α) (B : ℝ) (C : ConstraintProfile α)
    (hV : ∀ s, Viability P C s = B) :
    TheoryKEqKAlg atoms (srrgTheorySpaceWithZeroK T) P B C :=
  theory_k_eq_k_alg_at_barrier atoms (srrgTheorySpaceWithZeroK T) P B C
    (fun _ => rfl) hV

/-! ## §9 — Scalar coupling projection -/

/-- Scalar CMCA Kolmogorov: `K_CMCA(g) = -log₂(g² + g)`.

    Matches `SRRGCABridge.kCMCA` (ugp-lean-exp, CatAL). -/
noncomputable def kCMCA_scalar (g : ℝ) : ℝ :=
  -Real.logb 2 (g ^ 2 + g)

end SrrgLean.Core.CMCALanguage
