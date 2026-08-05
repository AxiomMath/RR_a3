import Mathlib
import QSeriesLib

set_option backward.isDefEq.respectTransparency false

open scoped QTheory PowerSeries.DiscreteTopology Classical
open HJO PowerSeries NumericalSemigroup Finset

/-!
# HJO `a = 3`: formal challenge

The opaque objects below encode the external supernomial machinery.  The proof
obligations are the paper-step declarations and listed supporting lemmas,
culminating in `ProblemHJOa3.thm_main`.
-/

namespace SupernomialInv

open LaurentPolynomial

/-- The Laurent-polynomial variable `q`. -/
noncomputable def q : LaurentPolynomial ℤ := T 1

/-- Substitution `q ↦ q⁻¹` on Laurent polynomials. -/
noncomputable def invSub : LaurentPolynomial ℤ →ₐ[ℤ] LaurentPolynomial ℤ :=
  AddMonoidAlgebra.mapDomainAlgHom ℤ ℤ (-AddMonoidHom.id ℤ)

/-- The Gaussian polynomial `[N;j]q`. -/
noncomputable def gauss (N j : ℕ) : LaurentPolynomial ℤ := qChoose q N j

/-- A one-row semistandard `{1,2}`-tableau. -/
structure Row where
  len : ℕ
  ones : ℕ
  ones_le : ones ≤ len
deriving DecidableEq

instance : Inhabited Row := ⟨⟨0, 0, le_refl 0⟩⟩

def cellIsOne (p : Row) (c : ℕ) : Bool := decide (1 ≤ c ∧ c ≤ p.ones)

def cellIsTwo (p : Row) (c : ℕ) : Bool := decide (p.ones < c ∧ c ≤ p.len)

/-- A multitableau with its two row blocks retained separately. -/
structure MultiTab where
  betaRows : List Row
  sRows : List Row
  order : Bool
deriving DecidableEq

def MultiTab.flatten (T : MultiTab) : List Row :=
  if T.order then T.betaRows ++ T.sRows else T.sRows ++ T.betaRows

/-- Schilling crossings between an earlier and a later row. -/
def crossings (p p' : Row) : ℕ :=
  let N := max p.len p'.len
  (∑ c ∈ Finset.Icc 1 N, (if cellIsTwo p c ∧ cellIsOne p' c then 1 else 0))
    + (∑ c ∈ Finset.Icc 1 N,
        (if cellIsOne p (c + 1) ∧ cellIsTwo p' c then 1 else 0))

/-- Schilling's inversion statistic in the one-row specialization. -/
def invMT (T : MultiTab) : ℕ :=
  let rows := T.flatten
  ∑ i ∈ Finset.range rows.length, ∑ j ∈ Finset.Ioo i rows.length,
    crossings rows[i]! rows[j]!

def intraSum (rows : List Row) (lo hi : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico lo hi, ∑ j ∈ Finset.Ioo i hi, crossings rows[i]! rows[j]!

def crossSum (rows : List Row) (nb n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range nb, ∑ j ∈ Finset.Ico nb n, crossings rows[i]! rows[j]!

def countLevel (rows : List Row) (i : ℕ) : ℕ :=
  (rows.filter (fun p => i ≤ p.ones)).length

def aOf {ℓ : ℕ} (T : MultiTab) (i : Fin ℓ) : ℕ := countLevel T.sRows (i + 1)

def zOf {ℓ : ℕ} (T : MultiTab) (i : Fin ℓ) : ℕ := countLevel T.betaRows (i + 1)

def invWord (w : List Bool) : ℕ :=
  ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
    (if w[i]! = true ∧ w[j]! = false then 1 else 0)

def wordA (sRows : List Row) (i : ℕ) : List Bool :=
  (sRows.filter (fun p => i - 1 ≤ p.ones)).map (fun p => decide (i ≤ p.ones))

def wordZ (betaRows : List Row) (i : ℕ) : List Bool :=
  (betaRows.filter (fun p => i ≤ p.len ∧ p.ones < i + 1)).map
    (fun p => decide (p.ones = i))

def Ja (ℓ : ℕ) (T : MultiTab) : ℤ :=
  ∑ i ∈ Finset.Icc 1 ℓ, (invWord (wordA T.sRows i) : ℤ)

def Jz (ℓ : ℕ) (T : MultiTab) : ℤ :=
  ∑ i ∈ Finset.Icc 1 ℓ, (invWord (wordZ T.betaRows i) : ℤ)

def shiftPrev {ℓ : ℕ} (bd : ℕ) (t : Fin ℓ → ℕ) (j : Fin ℓ) : ℕ :=
  if (j : ℕ) = 0 then bd else t ⟨(j : ℕ) - 1, by omega⟩

def shiftNext {ℓ : ℕ} (t : Fin ℓ → ℕ) (j : Fin ℓ) : ℕ :=
  if h : (j : ℕ) + 1 = ℓ then 0
  else t ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩

/-- The beta-block row lengths whose conjugate is `r`. -/
def betaParts {ℓ : ℕ} (r : Fin ℓ → ℕ) : List ℕ :=
  let R := if 0 < ℓ then Finset.univ.sup r else 0
  (List.range R).map (fun c => (Finset.univ.filter (fun i => c + 1 ≤ r i)).card)

def sBlockLens (ℓ s : ℕ) : List ℕ := List.replicate s ℓ

def rowsOfLen (L : ℕ) : Finset Row :=
  (Finset.range (L + 1)).image
    (fun u => (⟨L, min u L, min_le_right _ _⟩ : Row))

def fillings : List ℕ → Finset (List Row)
  | [] => {[]}
  | L :: Ls =>
      ((rowsOfLen L) ×ˢ (fillings Ls)).image (fun p => p.1 :: p.2)

def levelSum {ℓ : ℕ} (T : MultiTab) : ℕ :=
  ∑ i, (aOf (ℓ := ℓ) T i + zOf (ℓ := ℓ) T i)

def azDomain {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ) (a z : Fin ℓ → ℕ) : Prop :=
  (∀ j, a j ≤ shiftPrev s a j) ∧
    (∀ j, z j ≤ r j) ∧
    (∀ j, shiftNext z j ≤ z j)

instance {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ) (a z : Fin ℓ → ℕ) :
    Decidable (azDomain r s a z) := by
  unfold azDomain
  infer_instance

noncomputable def azFinset {ℓ : ℕ} (r : Fin ℓ → ℕ) (s M : ℕ) :
    Finset ((Fin ℓ → ℕ) × (Fin ℓ → ℕ)) :=
  ((Fintype.piFinset (fun _ => Finset.range (s + 1))) ×ˢ
      (Fintype.piFinset (fun i => Finset.range (r i + 1)))).filter
    (fun p => azDomain r s p.1 p.2 ∧ ∑ i, (p.1 i + p.2 i) = M)

def Eminus {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ) (a z : Fin ℓ → ℕ) : ℤ :=
  ∑ j, ((a j : ℤ) ^ 2 + (z j : ℤ) ^ 2 + (a j : ℤ) * (z j : ℤ)
    + (z j : ℤ) * (shiftPrev s a j : ℤ)
    - (r j : ℤ) * ((a j : ℤ) + (z j : ℤ)))

def Eplus {ℓ : ℕ} (r : Fin ℓ → ℕ) (a z : Fin ℓ → ℕ) : ℤ :=
  ∑ j, ((a j : ℤ) ^ 2 + (z j : ℤ) ^ 2 + (a j : ℤ) * (z j : ℤ)
    + (shiftNext a j : ℤ) * (z j : ℤ)
    - (r j : ℤ) * ((shiftNext a j : ℤ) + (z j : ℤ)))

noncomputable def Bweight {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ)
    (a z : Fin ℓ → ℕ) : LaurentPolynomial ℤ :=
  ∏ j, gauss (shiftPrev s a j) (a j) *
    gauss (r j - shiftNext z j) (z j - shiftNext z j)

/-- Concrete multitableaux in one of the two block orders. -/
noncomputable def TsetOrder {ℓ : ℕ} (r : Fin ℓ → ℕ) (s M : ℕ)
    (betaFirst : Bool) : Finset MultiTab :=
  (((fillings (betaParts r)) ×ˢ (fillings (sBlockLens ℓ s))).image
      (fun p => (⟨p.1, p.2, betaFirst⟩ : MultiTab))).filter
    (fun T => levelSum (ℓ := ℓ) T = M)

noncomputable def TsetMinus {ℓ : ℕ} (r : Fin ℓ → ℕ) (s M : ℕ) :
    Finset MultiTab :=
  TsetOrder r s M true

noncomputable def TsetPlus {ℓ : ℕ} (r : Fin ℓ → ℕ) (s M : ℕ) :
    Finset MultiTab :=
  TsetOrder r s M false

section Mu

variable {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ)

/-- The conjugate partition `μ' = (r₁+s,…,rℓ+s)`. -/
def muPrime : List ℕ := (List.finRange ℓ).map (fun j => r j + s)

def muSize : ℕ := ∑ j, (r j + s)

end Mu

/-- Binary-word interpretation of the Gaussian polynomial. -/
def BinaryWordGauss : Prop :=
  ∀ N k : ℕ,
    gauss N k =
      ∑ v ∈ (Finset.univ.filter
          (fun v : Fin N → Bool =>
            (Finset.univ.filter (fun i => v i = true)).card = k)),
        q ^ (invWord (List.ofFn v))

section PaperSteps

variable {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ)
  (Stil : LaurentPolynomial ℤ → List ℤ → List ℕ → LaurentPolynomial ℤ)

/-- Internal s-block inversion count (`eq:internal-a`). -/
theorem internal_a
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (M : ℕ) (T : MultiTab) (hT : T ∈ TsetMinus r s M) :
    (intraSum T.flatten T.betaRows.length T.flatten.length : ℤ) + Ja ℓ T
      = ∑ i, (aOf (ℓ := ℓ) T i : ℤ) * ((s : ℤ) - (aOf (ℓ := ℓ) T i : ℤ)) := by
  sorry

/-- Internal beta-block inversion count (`eq:internal-z`). -/
theorem internal_z
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (M : ℕ) (T : MultiTab) (hT : T ∈ TsetMinus r s M) :
    (intraSum T.flatten 0 T.betaRows.length : ℤ) + Jz ℓ T
      = ∑ i, (zOf (ℓ := ℓ) T i : ℤ) * ((r i : ℤ) - (zOf (ℓ := ℓ) T i : ℤ)) := by
  sorry

/-- Cross-block inversion count in beta-first order. -/
theorem cross_minus
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (M : ℕ) (T : MultiTab) (hT : T ∈ TsetMinus r s M) :
    (crossSum T.flatten T.betaRows.length T.flatten.length : ℤ)
      = (s : ℤ) * (∑ i, (zOf (ℓ := ℓ) T i : ℤ))
        - (∑ i, (aOf (ℓ := ℓ) T i : ℤ) * (zOf (ℓ := ℓ) T i : ℤ))
        - (∑ i, (zOf (ℓ := ℓ) T i : ℤ) * (shiftPrev s (aOf (ℓ := ℓ) T) i : ℤ))
        + (∑ i, (r i : ℤ) * (aOf (ℓ := ℓ) T i : ℤ)) := by
  sorry

/-- Inversion decomposition (`eq:inv-Eminus`). -/
theorem inv_decomposition_minus
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (hbw : BinaryWordGauss)
    (M : ℕ) (T : MultiTab) (hT : T ∈ TsetMinus r s M) :
    (s : ℤ) * (∑ i, (aOf (ℓ := ℓ) T i + zOf (ℓ := ℓ) T i) : ℕ) - (invMT T : ℤ)
      = Ja ℓ T + Jz ℓ T + Eminus r s (aOf (ℓ := ℓ) T) (zOf (ℓ := ℓ) T) := by
  sorry

/-- Cross-block inversion count in s-first order. -/
theorem cross_plus
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (M : ℕ) (T : MultiTab) (hT : T ∈ TsetPlus r s M) :
    (crossSum T.flatten T.sRows.length T.flatten.length : ℤ)
      = (s : ℤ) * (∑ i, (zOf (ℓ := ℓ) T i : ℤ))
        - (∑ i, (aOf (ℓ := ℓ) T i : ℤ) * (zOf (ℓ := ℓ) T i : ℤ))
        + (∑ i, (r i : ℤ) * (shiftNext (aOf (ℓ := ℓ) T) i : ℤ))
        - (∑ i, (zOf (ℓ := ℓ) T i : ℤ) * (shiftNext (aOf (ℓ := ℓ) T) i : ℤ)) := by
  sorry

/-- Inversion decomposition (`eq:inv-Eplus`). -/
theorem inv_decomposition_plus
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (hbw : BinaryWordGauss)
    (M : ℕ) (T : MultiTab) (hT : T ∈ TsetPlus r s M) :
    (s : ℤ) * (∑ i, (aOf (ℓ := ℓ) T i + zOf (ℓ := ℓ) T i) : ℕ) - (invMT T : ℤ)
      = Ja ℓ T + Jz ℓ T + Eplus r (aOf (ℓ := ℓ) T) (zOf (ℓ := ℓ) T) := by
  sorry

/-- Summed, `Eminus`-weighted consequence of `eq:Jgf` in beta-first order. -/
theorem fiber_minus
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (hbw : BinaryWordGauss) (M : ℕ) :
    ∑ p ∈ azFinset r s M, LaurentPolynomial.T (Eminus r s p.1 p.2)
        * Bweight r s p.1 p.2
      = ∑ T ∈ TsetMinus r s M,
          LaurentPolynomial.T
            (Eminus r s (aOf (ℓ := ℓ) T) (zOf (ℓ := ℓ) T) + Ja ℓ T + Jz ℓ T) := by
  sorry

/-- Summed, `Eplus`-weighted consequence of `eq:Jgf` in s-first order. -/
theorem fiber_plus
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (hbw : BinaryWordGauss) (M : ℕ) :
    ∑ p ∈ azFinset r s M, LaurentPolynomial.T (Eplus r p.1 p.2)
        * Bweight r s p.1 p.2
      = ∑ T ∈ TsetPlus r s M,
          LaurentPolynomial.T
            (Eplus r (aOf (ℓ := ℓ) T) (zOf (ℓ := ℓ) T) + Ja ℓ T + Jz ℓ T) := by
  sorry

/-- Left-supernomial identity, minus sign. -/
theorem left_supernomial_minus
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (hbw : BinaryWordGauss)
    (fact2 : ∀ M : ℕ,
        Stil q [(M : ℤ), (muSize r s : ℤ) - M] (muPrime r s)
          = ∑ T ∈ TsetMinus r s M, q ^ (invMT T))
    (fact2_perm : ∀ M : ℕ,
        ∑ T ∈ TsetMinus r s M, q ^ (invMT T)
          = ∑ T ∈ TsetPlus r s M, q ^ (invMT T))
    (fact3 : ∀ (A B : ℤ),
        Stil q [A, B] (muPrime r s) = Stil q [B, A] (muPrime r s))
    (M : ℕ) :
    ∑ p ∈ azFinset r s M, LaurentPolynomial.T (Eminus r s p.1 p.2)
        * Bweight r s p.1 p.2
      = LaurentPolynomial.T ((s : ℤ) * M) *
          invSub (Stil q [(M : ℤ), (muSize r s : ℤ) - M] (muPrime r s)) := by
  sorry

/-- Left-supernomial identity, plus sign. -/
theorem left_supernomial_plus
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (hbw : BinaryWordGauss)
    (fact2 : ∀ M : ℕ,
        Stil q [(M : ℤ), (muSize r s : ℤ) - M] (muPrime r s)
          = ∑ T ∈ TsetMinus r s M, q ^ (invMT T))
    (fact2_perm : ∀ M : ℕ,
        ∑ T ∈ TsetMinus r s M, q ^ (invMT T)
          = ∑ T ∈ TsetPlus r s M, q ^ (invMT T))
    (fact3 : ∀ (A B : ℤ),
        Stil q [A, B] (muPrime r s) = Stil q [B, A] (muPrime r s))
    (M : ℕ) :
    ∑ p ∈ azFinset r s M, LaurentPolynomial.T (Eplus r p.1 p.2)
        * Bweight r s p.1 p.2
      = LaurentPolynomial.T ((s : ℤ) * M) *
          invSub (Stil q [(M : ℤ), (muSize r s : ℤ) - M] (muPrime r s)) := by
  sorry

end PaperSteps

end SupernomialInv

namespace ProblemHJOa3

open LaurentPolynomial

noncomputable abbrev qX : ℤ⟦X⟧ := X

/-- One-indexed access to a finite tuple, extended by zero. -/
def acc {n : ℕ} (t : Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : 1 ≤ i ∧ i ≤ n then t ⟨i - 1, by omega⟩ else 0

abbrev DomP (k : ℕ) : Type :=
  {rm : (Fin k → ℕ) × (Fin k → ℕ) // Antitone rm.1}

abbrev DomM (k : ℕ) : Type :=
  {rm : (Fin k → ℕ) × (Fin (k - 1) → ℕ) // Antitone rm.1}

/-- Fact 7: Sylvester's gap facts. -/
def Fact7 (a b : ℕ) : Prop :=
  Nat.Coprime a b ∧ 1 < a ∧ 1 < b ∧
    ((finspan {a, b}).gaps.card = (a - 1) * (b - 1) / 2) ∧
    ((a * b - a - b) ∈ (finspan {a, b}).gaps ∧
      (∀ g ∈ (finspan {a, b}).gaps, g ≤ a * b - a - b)) ∧
    (∀ s : ℕ, s ≤ a * b - a - b →
      (s ∈ (finspan {a, b}).gaps ↔
        (a * b - a - b - s) ∉ (finspan {a, b}).gaps))

/-- Fact 8: Huang positivity and coefficientwise finiteness. -/
def Fact8 (a b : ℕ) : Prop :=
  Nat.Coprime a b ∧ 1 < a ∧ 1 < b ∧
    (HJO.Q a b).PosDefOn (HJO.cone a b) ∧
    (∀ n ∈ HJO.cone a b, ∀ i,
      (n i) ^ 2 ≤ ((finspan {a, b}).gaps.card : ℤ) * (HJO.Q a b) n) ∧
    (∀ d : ℤ,
      {n : (finspan {a, b}).gaps → ℤ |
        n ∈ HJO.cone a b ∧ (HJO.Q a b) n = d}.Finite)

/-- Fact 6: elementary Gaussian and Pochhammer identities. -/
def Fact6 : Prop :=
  (∀ N j : ℕ, 1 ≤ j → j ≤ N →
      qChoose qX N j =
        qChoose qX (N - 1) (j - 1) + qX ^ j * qChoose qX (N - 1) j) ∧
  (∀ N j : ℕ, 1 ≤ j → j ≤ N →
      qChoose qX N j =
        qX ^ (N - j) * qChoose qX (N - 1) (j - 1) + qChoose qX (N - 1) j) ∧
  (∀ N j : ℕ, j ≤ N →
      qPochhammer qX qX j * qPochhammer qX qX (N - j) * qChoose qX N j =
        qPochhammer qX qX N) ∧
  (∀ N j : ℕ, N < j → qChoose qX N j = 0) ∧
  (∀ (k : ℕ) (r : Fin k → ℕ), Antitone r →
      invOfUnit (qPochhammer qX qX (acc r 1)) 1 *
          ∏ i ∈ Icc 1 (k - 1), qChoose qX (acc r i) (acc r (i + 1))
        = invOfUnit
            (qPochhammer qX qX (acc r k) *
              ∏ i ∈ Icc 1 (k - 1),
                qPochhammer qX qX (acc r i - acc r (i + 1))) 1)

noncomputable def bTheta (u L : ℕ) : ℤ⟦X⟧ :=
  (X ^ u; (X : ℤ⟦X⟧) ^ L)_∞ *
    (X ^ (L - u); (X : ℤ⟦X⟧) ^ L)_∞

noncomputable def warnaarRHSminus (k : ℕ) : ℤ⟦X⟧ :=
  ((X ^ (3 * k + 2); (X : ℤ⟦X⟧) ^ (3 * k + 2))_∞) ^ 2 *
    invOfUnit (((X; (X : ℤ⟦X⟧))_∞) ^ 2) 1 *
    (bTheta k (3 * k + 2) * bTheta (k + 1) (3 * k + 2) *
      bTheta (k + 1) (3 * k + 2))

noncomputable def warnaarRHSplus (k : ℕ) : ℤ⟦X⟧ :=
  ((X ^ (3 * k + 4); (X : ℤ⟦X⟧) ^ (3 * k + 4))_∞) ^ 2 *
    invOfUnit (((X; (X : ℤ⟦X⟧))_∞) ^ 2) 1 *
    (bTheta (k + 1) (3 * k + 4) * bTheta (k + 1) (3 * k + 4) *
      bTheta (k + 2) (3 * k + 4))

noncomputable def fermPlus (k : ℕ) : ℤ⟦X⟧ :=
  ∑' d : DomP k,
    let r := acc d.1.1
    let m := acc d.1.2
    X ^ (∑ i ∈ Icc 1 k, (r i ^ 2 + m i ^ 2 - r i * m i)) *
      invOfUnit (qPochhammer qX qX (r 1)) 1 *
      (∏ i ∈ Icc 1 (k - 1), qChoose qX (r i) (r (i + 1))) *
      qChoose qX (2 * r k) (m k) *
      ∏ i ∈ Icc 1 (k - 1),
        qChoose qX (r i - r (i + 1) + m (i + 1)) (m i)

noncomputable def fermMinus (k : ℕ) : ℤ⟦X⟧ :=
  ∑' d : DomM k,
    let r := acc d.1.1
    let m := acc d.1.2
    X ^ (r k ^ 2 +
        ∑ i ∈ Icc 1 (k - 1), (r i ^ 2 + m i ^ 2 - r i * m i)) *
      invOfUnit (qPochhammer qX qX (r 1)) 1 *
      (∏ i ∈ Icc 1 (k - 1), qChoose qX (r i) (r (i + 1))) *
      qChoose qX (r (k - 1) + r k) (m (k - 1)) *
      ∏ i ∈ Icc 1 (k - 2),
        qChoose qX (r i - r (i + 1) + m (i + 1)) (m i)

/-- The unexpanded fixed-boundary sum for `b = 3k+1`. -/
noncomputable def SbPlus (k : ℕ) (r : Fin k → ℕ) : ℤ⟦X⟧ :=
  (Polynomial.map (Nat.castRingHom ℤ)
    (∑ᶠ n : (finspan {3, 3 * k + 1}).gaps → ℕ,
      HJO.SumToSum.ThreeOne.lhsTerm k r (finspan {3, 3 * k + 1}).gaps n)).toPowerSeries

/-- The unexpanded fixed-boundary sum for `b = 3k-1`. -/
noncomputable def SbMinus (k : ℕ) (r : Fin k → ℕ) : ℤ⟦X⟧ :=
  ∑ᶠ n : (finspan {3, 3 * k - 1}).gaps → ℕ,
    (if ∀ j : Fin k, HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) = r j then
      X ^ (HJO.Q' (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1)
        (fun i => (n i : ℤ))).toNat *
        ∏ j ∈ Icc 1 (k - 1),
          (qChoose (X : ℤ⟦X⟧) (HJO.extendNat n (3 * j + 1))
              (HJO.extendNat n (3 * j - 2)) *
            HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧)
              ((acc r (k - j) : ℤ) - (HJO.extendNat n (3 * j - 4) : ℤ))
              ((HJO.extendNat n (3 * j - 1) : ℤ) -
                (HJO.extendNat n (3 * j - 4) : ℤ)))
    else 0)

/-- The per-`(r,m)` fermionic body in the plus case. -/
noncomputable def fermBodyP (k : ℕ) (r m : Fin k → ℕ) : ℤ⟦X⟧ :=
  X ^ (∑ i ∈ Icc 1 k,
      (acc r i ^ 2 + acc m i ^ 2 - acc r i * acc m i)) *
    qChoose qX (2 * acc r k) (acc m k) *
    ∏ i ∈ Icc 1 (k - 1),
      qChoose qX (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i)

/-- The per-`(r,m)` fermionic body in the minus case. -/
noncomputable def fermBodyM (k : ℕ) (r : Fin k → ℕ)
    (m : Fin (k - 1) → ℕ) : ℤ⟦X⟧ :=
  X ^ (acc r k ^ 2 + ∑ i ∈ Icc 1 (k - 1),
      (acc r i ^ 2 + acc m i ^ 2 - acc r i * acc m i)) *
    qChoose qX (acc r (k - 1) + acc r k) (acc m (k - 1)) *
    ∏ i ∈ Icc 1 (k - 2),
      qChoose qX (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i)

/-- Genuine charge products for the two residue cases. -/
noncomputable def Pminus (k : ℕ) : ℤ⟦X⟧ :=
  ∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ HJO.negR 3 (3 * k - 1) n

noncomputable def Pplus (k : ℕ) : ℤ⟦X⟧ :=
  ∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ HJO.negR 3 (3 * k + 1) n

/-- Fact 4: Warnaar's two `A₂` Andrews–Gordon identities. -/
def Fact4 : Prop :=
  (∀ k : ℕ, 2 ≤ k → fermMinus k = warnaarRHSminus k) ∧
  (∀ k : ℕ, 1 ≤ k → fermPlus k = warnaarRHSplus k)

noncomputable abbrev qL : LaurentPolynomial ℤ := T 1

def aacc {ℓ : ℕ} (s : ℕ) (a : Fin ℓ → ℕ) (i : ℕ) : ℕ :=
  if i = 0 then s else acc a i

def Eplus {ℓ : ℕ} (r : Fin ℓ → ℕ) (a z : Fin ℓ → ℕ) : ℤ :=
  ∑ i ∈ Icc 1 ℓ,
    ((acc a i : ℤ) ^ 2 + (acc z i : ℤ) ^ 2 +
      (acc a i : ℤ) * (acc z i : ℤ) +
      (acc a (i + 1) : ℤ) * (acc z i : ℤ) -
      (acc r i : ℤ) * ((acc a (i + 1) : ℤ) + (acc z i : ℤ)))

def Eminus {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ) (a z : Fin ℓ → ℕ) : ℤ :=
  ∑ i ∈ Icc 1 ℓ,
    ((acc a i : ℤ) ^ 2 + (acc z i : ℤ) ^ 2 +
      (acc a i : ℤ) * (acc z i : ℤ) +
      (acc z i : ℤ) * (aacc s a (i - 1) : ℤ) -
      (acc r i : ℤ) * ((acc a i : ℤ) + (acc z i : ℤ)))

noncomputable def Brs {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ)
    (a z : Fin ℓ → ℕ) : LaurentPolynomial ℤ :=
  ∏ i ∈ Icc 1 ℓ,
    qChoose qL (aacc s a (i - 1)) (acc a i) *
      qChoose qL (acc r i - acc z (i + 1)) (acc z i - acc z (i + 1))

def domAZ {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ) (a z : Fin ℓ → ℕ) : Prop :=
  Antitone a ∧ acc a 1 ≤ s ∧ Antitone z ∧
    (∀ i ∈ Icc 1 ℓ, acc z i ≤ acc r i)

noncomputable def azFinset {ℓ : ℕ} (r : Fin ℓ → ℕ) (s M : ℕ) :
    Finset ((Fin ℓ → ℕ) × (Fin ℓ → ℕ)) :=
  ((Finset.Nat.antidiagonalTuple (ℓ + ℓ) M).image
      (fun w =>
        (fun i => w (Fin.castAdd ℓ i), fun i => w (Fin.natAdd ℓ i)))).filter
    (fun az => domAZ r s az.1 az.2)

variable
  {Tab : Type}
  (Stil : LaurentPolynomial ℤ → List ℤ → List ℕ → LaurentPolynomial ℤ)
  (Tset : List ℤ → List ℕ → Finset Tab)
  (invStat : Tab → ℕ)
  (tabOf : (ℓ : ℕ) → (Fin ℓ → ℕ) → (Fin ℓ → ℕ) →
    (Fin ℓ → ℕ) → ℕ → Bool → Tab)
  (Ja Jz : (ℓ : ℕ) → (Fin ℓ → ℕ) → (Fin ℓ → ℕ) →
    (Fin ℓ → ℕ) → ℕ → ℤ)

/-- Fact 2: the opaque multitableau/inversion expansion. -/
def Fact2 : Prop :=
  (∀ (q : LaurentPolynomial ℤ) (lam : List ℤ) (mu : List ℕ),
      lam.sum = (mu.sum : ℤ) →
        Stil q lam mu = ∑ T ∈ Tset lam mu, q ^ invStat T) ∧
  (∀ (q : LaurentPolynomial ℤ) (lam : List ℤ) (mu mu' : List ℕ),
      mu.Perm mu' → Stil q lam mu = Stil q lam mu')

/-- Fact 3: content symmetry. -/
def Fact3 : Prop :=
  (∀ (q : LaurentPolynomial ℤ) (lam lam' : List ℤ) (mu : List ℕ),
      lam.Perm lam' → Stil q lam mu = Stil q lam' mu) ∧
  (∀ (q : LaurentPolynomial ℤ) (A B : ℤ) (mu : List ℕ),
      Stil q [A, B] mu = Stil q [B, A] mu)

/-- Fact 1: Schilling's `A₁` rigged-configuration expansion. -/
def Fact1 : Prop :=
  ∀ (l : ℕ) (c : Fin l → ℕ), Antitone c → ∀ M : ℤ, 0 ≤ M →
    Stil qL [((∑ i, c i : ℕ) : ℤ) - M, M] (List.ofFn fun i => c i) =
      ∑ m ∈ Finset.Nat.antidiagonalTuple l M.toNat,
        (∏ i ∈ Icc 1 (l - 1),
          T (((acc c (i + 1) : ℤ) - (acc m (i + 1) : ℤ)) * (acc m i : ℤ))) *
        (∏ i ∈ Icc 1 (l - 1),
          qChoose qL (acc c i - acc c (i + 1) + acc m (i + 1)) (acc m i)) *
        qChoose qL (acc c l) (acc m l)

/-- Fact 5: Gaussian-binomial reciprocity. -/
def Fact5 : Prop :=
  ∀ N j : ℕ, j ≤ N →
    qChoose (T (-1) : LaurentPolynomial ℤ) N j =
      T (-(j * (N - j) : ℤ)) * qChoose qL N j

/-- The Section 3.4 interface derived from the concrete tableau development. -/
def Fact9 : Prop :=
  let _keepInvStat := invStat
  let _keepTabOf := tabOf
  let _keepJa := Ja
  let _keepJz := Jz
  (∀ (ℓ : ℕ), 0 < ℓ → ∀ (r : Fin ℓ → ℕ), Antitone r → ∀ (s M : ℕ),
      (∑ az ∈ azFinset r s M,
          T (Eplus r az.1 az.2) * Brs r s az.1 az.2)
        = T (↑s * ↑M : ℤ) *
            Stil (T (-1))
              [(M : ℤ), (∑ i, ((r i + s : ℕ) : ℤ)) - (M : ℤ)]
              (List.ofFn fun i => r i + s)) ∧
  (∀ (ℓ : ℕ), 0 < ℓ → ∀ (r : Fin ℓ → ℕ), Antitone r → ∀ (s M : ℕ),
      (∑ az ∈ azFinset r s M,
          T (Eminus r s az.1 az.2) * Brs r s az.1 az.2)
        = T (↑s * ↑M : ℤ) *
            Stil (T (-1))
              [(M : ℤ), (∑ i, ((r i + s : ℕ) : ℤ)) - (M : ℤ)]
              (List.ofFn fun i => r i + s))

/-- Fact 2 specialized to the two concrete component orders used in the proof. -/
def Fact2Bundle : Prop :=
  Fact2 Stil Tset invStat ∧
  (∀ (ℓ : ℕ) (r : Fin ℓ → ℕ) (s M : ℕ),
    Stil SupernomialInv.q
        [(M : ℤ), (SupernomialInv.muSize r s : ℤ) - M]
        (SupernomialInv.muPrime r s)
      = ∑ T ∈ SupernomialInv.TsetMinus r s M,
          SupernomialInv.q ^ SupernomialInv.invMT T) ∧
  (∀ (ℓ : ℕ) (r : Fin ℓ → ℕ) (s M : ℕ),
    (∑ T ∈ SupernomialInv.TsetMinus r s M,
        SupernomialInv.q ^ SupernomialInv.invMT T)
      = ∑ T ∈ SupernomialInv.TsetPlus r s M,
          SupernomialInv.q ^ SupernomialInv.invMT T)

/-- Standard binary-word Gaussian identity used in `eq:Jgf`. -/
theorem binaryWordGauss_holds : SupernomialInv.BinaryWordGauss := by
  sorry

/-- Gap-set formula `eq:gaps+`. -/
theorem stmt1_gaps_plus (k : ℕ) (hk : 1 ≤ k)
    (hSylv : Fact7 3 (3 * k + 1)) :
    (finspan {3, 3 * k + 1}).gaps =
      (image (fun t => 3 * t + 1) (range k)) ∪
        (image (fun t => 3 * t + 2) (range (2 * k))) := by
  sorry

/-- Gap-set formula `eq:gaps-`. -/
theorem stmt1_gaps_minus (k : ℕ) (hk : 2 ≤ k)
    (hSylv : Fact7 3 (3 * k - 1)) :
    (finspan {3, 3 * k - 1}).gaps =
      (image (fun t => 3 * t + 1) (range (2 * k - 1))) ∪
        (image (fun t => 3 * t + 2) (range (k - 1))) := by
  sorry

/-- Support of the `U`-kernel in the plus case. -/
theorem stmt2_reindex_plus (k : ℕ) (hk : 1 ≤ k)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) :
    {p : (finspan {3, 3 * k + 1}).gaps ×
        (finspan {3, 3 * k + 1}).gaps |
      HJO.U 3 (3 * k + 1) ((p.2 : ℤ) - (p.1 : ℤ)) ≠ 0} =
    {p | (0 ≤ (p.2 : ℤ) - (p.1 : ℤ) ∧
            (p.2 : ℤ) - (p.1 : ℤ) ≤ 2) ∨
          ((3 * k + 1 : ℤ) ≤ (p.2 : ℤ) - (p.1 : ℤ) ∧
            (p.2 : ℤ) - (p.1 : ℤ) ≤ 3 * k + 3)} := by
  sorry

/-- Support of the `U`-kernel in the minus case. -/
theorem stmt2_reindex_minus (k : ℕ) (hk : 2 ≤ k)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) :
    {p : (finspan {3, 3 * k - 1}).gaps ×
        (finspan {3, 3 * k - 1}).gaps |
      HJO.U 3 (3 * k - 1) ((p.2 : ℤ) - (p.1 : ℤ)) ≠ 0} =
    {p | (0 ≤ (p.2 : ℤ) - (p.1 : ℤ) ∧
            (p.2 : ℤ) - (p.1 : ℤ) ≤ 2) ∨
          ((3 * k - 1 : ℤ) ≤ (p.2 : ℤ) - (p.1 : ℤ) ∧
            (p.2 : ℤ) - (p.1 : ℤ) ≤ 3 * k + 1)} := by
  sorry

/-- Core reindexing identity `eq:Qplus`. -/
theorem stmt_reindexEq_plus (k : ℕ) (hk : 1 ≤ k)
    (n : (finspan {3, 3 * k + 1}).gaps → ℤ) (r a z : Fin k → ℕ)
    (hz : ∀ j : Fin k,
      ∀ h : 3 * (k - 1 - (j : ℕ)) + 1 ∈ (finspan {3, 3 * k + 1}).gaps,
        n ⟨_, h⟩ = (z j : ℤ))
    (ha : ∀ j : Fin k,
      ∀ h : 3 * (k - 1 - (j : ℕ)) + 2 ∈ (finspan {3, 3 * k + 1}).gaps,
        n ⟨_, h⟩ = (a j : ℤ))
    (hr : ∀ j : Fin k,
      ∀ h : 6 * k - 1 - 3 * (j : ℕ) ∈ (finspan {3, 3 * k + 1}).gaps,
        n ⟨_, h⟩ = (r j : ℤ))
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) :
    (HJO.Q 3 (3 * k + 1)) n =
      (∑ j : Fin k, (r j : ℤ) ^ 2) + Eplus r a z := by
  sorry

/-- Core reindexing identity `eq:Qminus`. -/
theorem stmt_reindexEq_minus (k : ℕ) (hk : 2 ≤ k)
    (n : (finspan {3, 3 * k - 1}).gaps → ℤ)
    (r : Fin k → ℕ) (a z : Fin (k - 1) → ℕ)
    (hz : ∀ j : Fin (k - 1),
      ∀ h : 3 * (k - 1 - (j : ℕ)) - 1 ∈ (finspan {3, 3 * k - 1}).gaps,
        n ⟨_, h⟩ = (z j : ℤ))
    (ha : ∀ j : Fin (k - 1),
      ∀ h : 3 * (k - 1 - (j : ℕ)) - 2 ∈ (finspan {3, 3 * k - 1}).gaps,
        n ⟨_, h⟩ = (a j : ℤ))
    (hr : ∀ j : Fin k,
      ∀ h : 6 * k - 5 - 3 * (j : ℕ) ∈ (finspan {3, 3 * k - 1}).gaps,
        n ⟨_, h⟩ = (r j : ℤ))
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) :
    (HJO.Q 3 (3 * k - 1)) n =
      (acc r k : ℤ) ^ 2 +
        (∑ j ∈ Icc 1 (k - 1), (acc r j : ℤ) ^ 2) +
        Eminus (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i))
          (acc r k) a z := by
  sorry

/-- The master transformation, at fixed content `M`. -/
theorem stmt4_master_aux (ell : ℕ) (hell : 1 ≤ ell) (s M : ℕ)
    (r : Fin ell → ℕ) (hr : Antitone r)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat)
    (hSym : Fact3 Stil) (hRecip : Fact5)
    (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    ((∑ az ∈ azFinset r s M,
        T (Eplus r az.1 az.2) * Brs r s az.1 az.2) =
      ∑ m ∈ Finset.Nat.antidiagonalTuple ell M,
        T (∑ i ∈ Icc 1 ell,
            ((acc m i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ))) *
          qChoose qL (acc r ell + s) (acc m ell) *
          ∏ i ∈ Icc 1 (ell - 1),
            qChoose qL
              (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i)) ∧
    ((∑ az ∈ azFinset r s M,
        T (Eminus r s az.1 az.2) * Brs r s az.1 az.2) =
      ∑ m ∈ Finset.Nat.antidiagonalTuple ell M,
        T (∑ i ∈ Icc 1 ell,
            ((acc m i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ))) *
          qChoose qL (acc r ell + s) (acc m ell) *
          ∏ i ∈ Icc 1 (ell - 1),
            qChoose qL
              (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i)) := by
  sorry

/-- Fixed-boundary identity in the plus case, at fixed content `M`. -/
theorem stmt5_fixedBoundary_plus_aux (k : ℕ) (hk : 1 ≤ k)
    (r : Fin k → ℕ) (hr : Antitone r) (M : ℕ)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat)
    (hSym : Fact3 Stil) (hRecip : Fact5)
    (hQbin : Fact6) (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    T (∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2) *
        (∑ az ∈ azFinset r (acc r k) M,
          T (Eplus r az.1 az.2) * Brs r (acc r k) az.1 az.2) =
      ∑ m ∈ Finset.Nat.antidiagonalTuple k M,
        T (∑ i ∈ Icc 1 k,
            ((acc r i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ) +
              (acc m i : ℤ) ^ 2)) *
          qChoose qL (2 * acc r k) (acc m k) *
          ∏ i ∈ Icc 1 (k - 1),
            qChoose qL
              (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i) := by
  sorry

/-- Fixed-boundary identity in the minus case, at fixed content `M`. -/
theorem stmt5_fixedBoundary_minus_aux (k : ℕ) (hk : 2 ≤ k)
    (r : Fin k → ℕ) (hr : Antitone r) (M : ℕ)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat)
    (hSym : Fact3 Stil) (hRecip : Fact5)
    (hQbin : Fact6) (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    T ((acc r k : ℤ) ^ 2 +
        ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2) *
        (∑ az ∈ azFinset
            (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i))
            (acc r k) M,
          T (Eminus
              (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i))
              (acc r k) az.1 az.2) *
            Brs (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i))
              (acc r k) az.1 az.2) =
      ∑ m ∈ Finset.Nat.antidiagonalTuple (k - 1) M,
        T ((acc r k : ℤ) ^ 2 +
            ∑ i ∈ Icc 1 (k - 1),
              ((acc r i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ) +
                (acc m i : ℤ) ^ 2)) *
          qChoose qL (acc r (k - 1) + acc r k) (acc m (k - 1)) *
          ∏ i ∈ Icc 1 (k - 2),
            qChoose qL
              (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i) := by
  sorry

/-- Charge product identification in the minus case. -/
theorem charge_minus_eq_invOfUnit (k : ℕ) (hk : 2 ≤ k) :
    HJO.charge 3 (3 * k - 1) = PowerSeries.invOfUnit (Pminus k) 1 := by
  sorry

/-- Charge product identification in the plus case. -/
theorem charge_plus_eq_invOfUnit (k : ℕ) (hk : 1 ≤ k) :
    HJO.charge 3 (3 * k + 1) = PowerSeries.invOfUnit (Pplus k) 1 := by
  sorry

/-- Final residue computation in the plus case. -/
theorem stmt7_residue_plus (k : ℕ) (hk : 1 ≤ k) (hWarnaar : Fact4) :
    fermPlus k = HJO.charge 3 (3 * k + 1) := by
  sorry

/-- Final residue computation in the minus case. -/
theorem stmt7_residue_minus (k : ℕ) (hk : 2 ≤ k) (hWarnaar : Fact4) :
    fermMinus k = HJO.charge 3 (3 * k - 1) := by
  sorry

/-- Full fixed-boundary identity in the plus case. -/
theorem cor_perR_plus (k : ℕ) (hk : 1 ≤ k)
    (r : Fin k → ℕ) (hr : Antitone r)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat)
    (hSym : Fact3 Stil) (hRecip : Fact5)
    (hQbin : Fact6) (hPD : Fact8 3 (3 * k + 1))
    (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    SbPlus k r = ∑' m : Fin k → ℕ, fermBodyP k r m := by
  sorry

/-- Full fixed-boundary identity in the minus case. -/
theorem cor_perR_minus (k : ℕ) (hk : 2 ≤ k)
    (r : Fin k → ℕ) (hr : Antitone r)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat)
    (hSym : Fact3 Stil) (hRecip : Fact5)
    (hQbin : Fact6) (hPD : Fact8 3 (3 * k - 1))
    (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    SbMinus k r = ∑' m : Fin (k - 1) → ℕ, fermBodyM k r m := by
  sorry

/-- Lemma 3.5 reassembly in the plus case. -/
theorem stmt6_reassembly (k : ℕ) (hk : 1 ≤ k)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat)
    (hSym : Fact3 Stil) (hQbin : Fact6)
    (hPD : Fact8 3 (3 * k + 1))
    (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    HJO.zNat 3 (3 * k + 1) =
      ∑' r : {r : Fin k → ℕ // Antitone r},
        invOfUnit (qPochhammer qX qX (acc r.1 1)) 1 *
          (∏ i ∈ Icc 1 (k - 1),
            qChoose qX (acc r.1 i) (acc r.1 (i + 1))) *
          SbPlus k r.1 := by
  sorry

/-- Lemma 3.5 reassembly in the minus case. -/
theorem stmt6_reassembly_minus (k : ℕ) (hk : 2 ≤ k)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat)
    (hSym : Fact3 Stil) (hQbin : Fact6)
    (hPD : Fact8 3 (3 * k - 1))
    (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    HJO.zNat 3 (3 * k - 1) =
      ∑' r : {r : Fin k → ℕ // Antitone r},
        invOfUnit (qPochhammer qX qX (acc r.1 1)) 1 *
          (∏ i ∈ Icc 1 (k - 1),
            qChoose qX (acc r.1 i) (acc r.1 (i + 1))) *
          SbMinus k r.1 := by
  sorry

include tabOf Ja Jz

/-- Corollary 1.2(2), `b = 3k+1`. -/
theorem cor_closedForm_plus (k : ℕ) (hk : 1 ≤ k)
    (h1 : Fact1 Stil) (h2 : Fact2Bundle Stil Tset invStat)
    (h3 : Fact3 Stil) (h5 : Fact5) (h6 : Fact6)
    (h8 : Fact8 3 (3 * k + 1)) :
    HJO.zNat 3 (3 * k + 1) = fermPlus k := by
  sorry

/-- Corollary 1.2(3), `b = 3k-1`. -/
theorem cor_closedForm_minus (k : ℕ) (hk : 2 ≤ k)
    (h1 : Fact1 Stil) (h2 : Fact2Bundle Stil Tset invStat)
    (h3 : Fact3 Stil) (h5 : Fact5) (h6 : Fact6)
    (h8 : Fact8 3 (3 * k - 1)) :
    HJO.zNat 3 (3 * k - 1) = fermMinus k := by
  sorry

/-- Theorem 1.1, the formal-power-series identity, from Facts 1–8. -/
theorem thm_main (b : ℕ) (hb : 3 < b) (hcop : Nat.Coprime 3 b)
    (h1 : Fact1 Stil) (h2 : Fact2Bundle Stil Tset invStat)
    (h3 : Fact3 Stil) (h4 : Fact4) (h5 : Fact5) (h6 : Fact6)
    (h7 : Fact7 3 b) (h8 : Fact8 3 b) :
    HJO.Conjecture' 3 b := by
  sorry

end ProblemHJOa3
