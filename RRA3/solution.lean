import Mathlib
import QSeriesLib
set_option backward.isDefEq.respectTransparency false

/-!
# HJO a=3 from Facts 1–8

This direct AxiomProver problem combines the proved binary-word Gaussian
development, the concrete Section 3.4 multitableau development, and the
dependency-clean main proof spine. Facts 1–8 occur only as explicit theorem
hypotheses. The remaining goal is the representation adapter below.
-/

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

This is Theorem 1.1 (`thm:main`) of `main.tex` (a `q`-series identity of
Huang--Jockusch--Odlyzko / "HJO" type), specialized to `a = 3`.

Throughout, `q` is a formal variable and all identities are equalities of formal
power series (or formal Laurent series where noted) in `q`.  The `q`-Pochhammer
symbol is `(q)_m := \prod_{j=1}^{m}(1-q^j)` for `m ≥ 0`, with `(q)_0 = 1`.  We fix
two integers `a, b > 1` with `gcd(a,b) = 1`; the theorem is stated for `a = 3`.

We formalize on top of Axiomlib's `HJO` development, which already contains the
numerical-semigroup gap set, the kernel `U`, the quadratic form `Q`, the cone
`C`, the summand of the series `Z`, the charge `r`, and the product `P`.  The
definitions below are thin, transparent wrappers over those objects; each is
`rfl`-equal to the corresponding Axiomlib object, and the correctness lemmas
record this.  This keeps the formal statement aligned with Axiomlib practice.

Main external input:
* `hsum : Summable (zSummand 3 b)` is Fact 8 (Huang's positive-definiteness
  bound, `FactPD`) in the only form the statement needs: it makes `Z_{3,b}` a
  well-defined formal power series.
-/

open PowerSeries.WithPiTopology
open HJO NumericalSemigroup

/- ## Research-note build layer FPS (`research/the_pinned_main_theorem_b_hb_3_b-180a03bf.tex`)

Formal `(q)_∞ ∈ ℤ[[X]]` via coefficientwise stabilization of the truncated
products `η_N = ∏_{j=1}^N (1 - X^j)`.  All lemmas here are Warnaar-independent and
closed outright (they validate the definition of `qPochInf`). -/

namespace FormalQ
open PowerSeries

/-- Truncated `q`-Pochhammer `η_N = ∏_{j=1}^N (1 - X^j)` as a power series. -/
noncomputable def etaTrunc (N : ℕ) : PowerSeries ℤ :=
  ∏ j ∈ Finset.range N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (j + 1))

theorem etaTrunc_zero : etaTrunc 0 = 1 := by simp [etaTrunc]

theorem etaTrunc_succ (N : ℕ) :
    etaTrunc (N + 1)
      = etaTrunc N * (1 - (PowerSeries.X : PowerSeries ℤ) ^ (N + 1)) := by
  rw [etaTrunc, etaTrunc, Finset.prod_range_succ]

/-- Multiplying by `1 - X^m` does not change coefficients below degree `m`. -/
theorem coeff_mul_one_sub_X_pow_of_lt (p : PowerSeries ℤ) {d m : ℕ} (h : d < m) :
    coeff d (p * (1 - (PowerSeries.X : PowerSeries ℤ) ^ m)) = coeff d p := by
  apply PowerSeries.coeff_mul_one_sub_of_lt_order
  rw [PowerSeries.order_X_pow]
  exact_mod_cast h

/-- **Stabilization.**  For `d < N` and `d < M`, the degree-`d` coefficient of
`η_N` equals that of `η_M`. -/
theorem coeff_etaTrunc_stable {d N M : ℕ} (hN : d < N) (hM : d < M) :
    coeff d (etaTrunc N) = coeff d (etaTrunc M) := by
  suffices H : ∀ a b : ℕ, d < a → a ≤ b → coeff d (etaTrunc a) = coeff d (etaTrunc b) by
    rcases le_total N M with h | h
    · exact H N M hN h
    · exact (H M N hM h).symm
  intro a b ha hab
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · have hab' : a ≤ b := by omega
      rw [ih hab']
      rw [etaTrunc_succ, coeff_mul_one_sub_X_pow_of_lt]
      omega
    · have : a = b + 1 := by omega
      rw [this]

/-- The formal infinite `q`-Pochhammer `(q)_∞`, defined coefficientwise from the
stabilized truncated products. -/
noncomputable def qPochInf : PowerSeries ℤ := mk (fun d => coeff d (etaTrunc (d + 1)))

theorem coeff_qPochInf (d : ℕ) : coeff d qPochInf = coeff d (etaTrunc (d + 1)) := by
  rw [qPochInf, PowerSeries.coeff_mk]

/-- **Definition validator (answers research sub-question (b)).**  For `d < N`,
the degree-`d` coefficient of `(q)_∞` equals that of `η_N`. -/
theorem coeff_qPochInf_eq_etaTrunc {d N : ℕ} (hN : d < N) :
    coeff d qPochInf = coeff d (etaTrunc N) := by
  rw [coeff_qPochInf]; exact coeff_etaTrunc_stable (Nat.lt_succ_self d) hN

theorem constantCoeff_qPochInf : coeff 0 qPochInf = 1 := by
  rw [coeff_qPochInf]
  simp [etaTrunc]

/-- `(q)_∞` is a unit (constant coefficient `1`); its inverse power series. -/
noncomputable def qPochInfInv : PowerSeries ℤ := qPochInf.invOfUnit 1

end FormalQ

/- ## Research-note build layer for Leaf A (`sumToSum_threeOne`)

Following `research/leaf_a_sumtosum_threeone_k_r_fin_k-7eaf80fa.tex`, we build the
missing supernomial/inversion infrastructure bottom-up.  Layers 1--2 are
classical and closed first (they validate the definitions).  Layers 3--7 (which
need the verbatim `main.tex` constants) are deferred.

**qChoose recurrence in this env** (`qChoose_succ_succ`):
`qChoose q (n+1) (k+1) = qChoose q n k + q^(k+1) * qChoose q n (k+1)`
(last-bit split).  The matching inversion statistic is
`inv(S) = #{(i,j) : i<j, i∈S, j∉S}` (a `1` at position `i` before a `0` at `j`). -/

namespace LeafABuild

/-- **Layer 1 statistic.**  Number of "inversions" of a binary word encoded as a
subset `S ⊆ Fin N`: pairs `(i,j)` with `i<j`, `i∈S` (a `1`), `j∉S` (a `0`). -/
def invWord {N : ℕ} (S : Finset (Fin N)) : ℕ :=
  (Finset.univ.filter (fun ij : Fin N × Fin N => ij.1 < ij.2 ∧ ij.1 ∈ S ∧ ij.2 ∉ S)).card

/-- **Layer 2 statistic.**  Complementary count: `1` after a `0`. -/
def noninvWord {N : ℕ} (S : Finset (Fin N)) : ℕ :=
  (Finset.univ.filter (fun ij : Fin N × Fin N => ij.1 < ij.2 ∧ ij.1 ∉ S ∧ ij.2 ∈ S)).card

/-- Embedding a subset of `Fin N` via `castSucc` does not change its inversion
count, but adds `card` inversions from the extra `0` at position `last N`. -/
theorem invWord_map_castSucc {N : ℕ} (T : Finset (Fin N)) :
    invWord (T.map (Fin.castSuccEmb)) = invWord T + T.card := by
  classical
  unfold invWord
  set T' : Finset (Fin (N+1)) := T.map (Fin.castSuccEmb) with hT'
  have hmem : ∀ x : Fin (N+1), x ∈ T' ↔ ∃ a ∈ T, Fin.castSucc a = x := by
    intro x; rw [hT', Finset.mem_map]
    exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩⟩
  have hlast : Fin.last N ∉ T' := by
    rw [hmem]; rintro ⟨a, _, ha⟩; exact Fin.castSucc_ne_last a ha
  -- The two pieces as images of injective maps.
  set embA : Fin N × Fin N ↪ Fin (N+1) × Fin (N+1) :=
    ⟨fun ab => (Fin.castSucc ab.1, Fin.castSucc ab.2), by
      rintro ⟨a, b⟩ ⟨c, d⟩ h
      simp only [Prod.mk.injEq, Fin.castSucc_inj] at h
      exact Prod.ext h.1 h.2⟩ with hembA
  set embB : Fin N ↪ Fin (N+1) × Fin (N+1) :=
    ⟨fun a => (Fin.castSucc a, Fin.last N), by
      rintro a c h
      simp only [Prod.mk.injEq, Fin.castSucc_inj] at h
      exact h.1⟩ with hembB
  set A := (Finset.univ.filter
      (fun ab : Fin N × Fin N => ab.1 < ab.2 ∧ ab.1 ∈ T ∧ ab.2 ∉ T)).map embA with hA
  set B := T.map embB with hB
  -- The main filter set decomposes as A ∪ B.
  have hunion : (Finset.univ.filter
      (fun ij : Fin (N+1) × Fin (N+1) => ij.1 < ij.2 ∧ ij.1 ∈ T' ∧ ij.2 ∉ T'))
      = A ∪ B := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      hA, hB, Finset.mem_map, hembA, hembB, Function.Embedding.coeFn_mk, Prod.mk.injEq]
    constructor
    · rintro ⟨hlt, hi, hj⟩
      rw [hmem] at hi; obtain ⟨a, ha, rfl⟩ := hi
      rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
      · -- both castSucc, in A
        left
        refine ⟨(a, b), ⟨Fin.castSucc_lt_castSucc_iff.mp hlt, ha, ?_⟩, rfl, rfl⟩
        intro hb; apply hj; rw [hmem]; exact ⟨b, hb, rfl⟩
      · -- j = last, in B
        right; exact ⟨a, ha, rfl, rfl⟩
    · rintro (⟨⟨a, b⟩, ⟨hlt, ha, hb⟩, rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩)
      · refine ⟨Fin.castSucc_lt_castSucc_iff.mpr hlt, ?_, ?_⟩
        · rw [hmem]; exact ⟨a, ha, rfl⟩
        · rw [hmem]; rintro ⟨a', ha', hae⟩
          rw [Fin.castSucc_inj] at hae; rw [← hae] at hb; exact hb ha'
      · refine ⟨Fin.castSucc_lt_last a, ?_, hlast⟩
        rw [hmem]; exact ⟨a, ha, rfl⟩
  rw [hunion, Finset.card_union_of_disjoint, hA, hB, Finset.card_map, Finset.card_map]
  -- disjointness
  rw [hA, hB, Finset.disjoint_left]
  rintro ⟨i, j⟩ hiA hiB
  simp only [Finset.mem_map, hembA, hembB, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hiA hiB
  obtain ⟨_, _, _, hj1⟩ := hiA
  obtain ⟨a, _, _, hj2⟩ := hiB
  rw [← hj2] at hj1
  exact Fin.castSucc_ne_last _ hj1

/-- Inserting `last N` (a `1` at the maximal position) into a `castSucc`-embedded
subset does not change the inversion count. -/
theorem invWord_insert_last_map_castSucc {N : ℕ} (T : Finset (Fin N)) :
    invWord (insert (Fin.last N) (T.map (Fin.castSuccEmb))) = invWord T := by
  classical
  unfold invWord
  set T' : Finset (Fin (N+1)) := T.map (Fin.castSuccEmb) with hT'
  set S : Finset (Fin (N+1)) := insert (Fin.last N) T' with hS
  have hmemT' : ∀ x : Fin (N+1), x ∈ T' ↔ ∃ a ∈ T, Fin.castSucc a = x := by
    intro x; rw [hT', Finset.mem_map]
    exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩⟩
  have hmemS : ∀ x : Fin (N+1), x ∈ S ↔ (x = Fin.last N ∨ ∃ a ∈ T, Fin.castSucc a = x) := by
    intro x; rw [hS, Finset.mem_insert, hmemT']
  set embA : Fin N × Fin N ↪ Fin (N+1) × Fin (N+1) :=
    ⟨fun ab => (Fin.castSucc ab.1, Fin.castSucc ab.2), by
      rintro ⟨a, b⟩ ⟨c, d⟩ h
      simp only [Prod.mk.injEq, Fin.castSucc_inj] at h
      exact Prod.ext h.1 h.2⟩ with hembA
  -- The filter set is exactly the image of the invWord-T filter under embA.
  have heq : (Finset.univ.filter
      (fun ij : Fin (N+1) × Fin (N+1) => ij.1 < ij.2 ∧ ij.1 ∈ S ∧ ij.2 ∉ S))
      = (Finset.univ.filter
          (fun ab : Fin N × Fin N => ab.1 < ab.2 ∧ ab.1 ∈ T ∧ ab.2 ∉ T)).map embA := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, hembA,
      Function.Embedding.coeFn_mk, Prod.mk.injEq]
    constructor
    · rintro ⟨hlt, hi, hj⟩
      -- j ≠ last since j ∉ S but last ∈ S
      have hjlast : j ≠ Fin.last N := by
        intro h; apply hj; rw [h, hmemS]; left; rfl
      rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
      swap
      · exact absurd rfl hjlast
      -- i: since i < j = castSucc b < last, i ≠ last
      have hilast : i ≠ Fin.last N := ne_of_lt (lt_of_lt_of_le hlt (Fin.le_last _))
      rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl
      swap
      · exact absurd rfl hilast
      refine ⟨(a, b), ⟨Fin.castSucc_lt_castSucc_iff.mp hlt, ?_, ?_⟩, rfl, rfl⟩
      · rw [hmemS] at hi
        rcases hi with h | ⟨a', ha', hae⟩
        · exact absurd h (Fin.castSucc_ne_last a)
        · rw [Fin.castSucc_inj] at hae; rw [← hae]; exact ha'
      · intro hb; apply hj; rw [hmemS]; right; exact ⟨b, hb, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨hlt, ha, hb⟩, rfl, rfl⟩
      refine ⟨Fin.castSucc_lt_castSucc_iff.mpr hlt, ?_, ?_⟩
      · rw [hmemS]; right; exact ⟨a, ha, rfl⟩
      · rw [hmemS]; push_neg
        refine ⟨Fin.castSucc_ne_last b, ?_⟩
        rintro a' ha' hae
        rw [Fin.castSucc_inj] at hae; rw [← hae] at hb; exact hb ha'
  rw [heq, Finset.card_map]

/-- **Layer 1 (binary-word inversion generating function).**  The Gaussian
binomial `qChoose X N k` is the inversion generating function over all
`k`-subsets of `Fin N`.  Proved by induction on `N` via `qChoose_succ_succ`. -/
theorem qChoose_eq_sum_invWord (N k : ℕ) :
    qChoose (Polynomial.X : Polynomial ℕ) N k =
      ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin N) => S.card = k)),
        (Polynomial.X : Polynomial ℕ) ^ invWord S := by
  classical
  induction N generalizing k with
  | zero =>
    cases k with
    | zero =>
      rw [qChoose_zero]
      have honly : (Finset.univ.filter (fun S : Finset (Fin 0) => S.card = 0))
          = {∅} := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Finset.card_eq_zero]
      rw [honly]; simp [invWord]
    | succ k' =>
      rw [qChoose_zero_succ]
      rw [Finset.filter_false_of_mem]
      · simp
      · intro S _
        rw [Finset.eq_empty_of_isEmpty S]; simp
  | succ N ih =>
    cases k with
    | zero =>
      rw [qChoose_zero]
      -- RHS: only ∅ has card 0
      have honly : (Finset.univ.filter (fun S : Finset (Fin (N+1)) => S.card = 0))
          = {∅} := by
        ext S; simp [Finset.card_eq_zero]
      rw [honly]; simp [invWord]
    | succ k' =>
      rw [qChoose_succ_succ, ih k', ih (k'+1)]
      -- RHS: split the sum over subsets of Fin (N+1) on `last N ∈ S`.
      rw [← Finset.sum_filter_add_sum_filter_not
          (Finset.univ.filter (fun S : Finset (Fin (N+1)) => S.card = k'+1))
          (fun S => Fin.last N ∈ S)]
      -- The two maps between subsets of `Fin N` and subsets of `Fin (N+1)`.
      set F : Finset (Fin N) → Finset (Fin (N+1)) :=
        fun T => insert (Fin.last N) (T.map (Fin.castSuccEmb)) with hF
      set G : Finset (Fin N) → Finset (Fin (N+1)) :=
        fun T => T.map (Fin.castSuccEmb) with hG
      -- Injectivity facts.
      have hFinj : Function.Injective F := by
        intro T1 T2 h
        have hlast1 : Fin.last N ∉ T1.map Fin.castSuccEmb := by
          rw [Finset.mem_map]; rintro ⟨a, _, ha⟩; exact Fin.castSucc_ne_last a ha
        have hlast2 : Fin.last N ∉ T2.map Fin.castSuccEmb := by
          rw [Finset.mem_map]; rintro ⟨a, _, ha⟩; exact Fin.castSucc_ne_last a ha
        have : T1.map Fin.castSuccEmb = T2.map Fin.castSuccEmb := by
          rw [hF] at h
          have := congrArg (Finset.erase · (Fin.last N)) h
          simpa [Finset.erase_insert hlast1, Finset.erase_insert hlast2] using this
        exact Finset.map_injective _ this
      have hGinj : Function.Injective G := by
        intro T1 T2 h; exact Finset.map_injective _ h
      congr 1
      · -- `last N ∈ S`  block
        -- The filter set is the image of the card-k' subsets of Fin N under F.
        have himg : (Finset.univ.filter (fun S : Finset (Fin (N+1)) => S.card = k'+1)).filter
            (fun S => Fin.last N ∈ S)
            = (Finset.univ.filter (fun T : Finset (Fin N) => T.card = k')).image F := by
          ext S
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · rintro ⟨hcard, hlast⟩
            -- erase last, then the rest ⊆ range castSucc
            have hsub : (↑(S.erase (Fin.last N)) : Set (Fin (N+1))) ⊆ Set.range Fin.castSucc := by
              intro x hx
              simp only [Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff] at hx
              rcases Fin.eq_castSucc_or_eq_last x with ⟨j, rfl⟩ | rfl
              · exact ⟨j, rfl⟩
              · exact absurd rfl hx.2
            have hmap : ((S.erase (Fin.last N)).preimage Fin.castSucc
                (Fin.castSucc_injective N).injOn).map Fin.castSuccEmb = S.erase (Fin.last N) := by
              rw [Finset.map_eq_image]
              have hemb : (Fin.castSuccEmb : Fin N ↪ Fin (N+1))
                  = ⟨Fin.castSucc, Fin.castSucc_injective N⟩ := rfl
              rw [hemb]; simp only [Function.Embedding.coeFn_mk]
              rw [Finset.image_preimage, Finset.filter_true_of_mem]
              intro x hx; exact hsub hx
            refine ⟨(S.erase (Fin.last N)).preimage Fin.castSucc
                (Fin.castSucc_injective N).injOn, ?_, ?_⟩
            · rw [← Finset.card_map Fin.castSuccEmb, hmap]
              rw [Finset.card_erase_of_mem hlast, hcard]
              omega
            · show insert (Fin.last N) (Finset.map Fin.castSuccEmb
                ((S.erase (Fin.last N)).preimage Fin.castSucc (Fin.castSucc_injective N).injOn)) = S
              rw [hmap, Finset.insert_erase hlast]
          · rintro ⟨T, hT, rfl⟩
            refine ⟨?_, ?_⟩
            · rw [hF, Finset.card_insert_of_notMem, Finset.card_map, hT]
              rw [Finset.mem_map]; rintro ⟨a, _, ha⟩; exact Fin.castSucc_ne_last a ha
            · rw [hF]; exact Finset.mem_insert_self _ _
        rw [himg, Finset.sum_image (fun T1 _ T2 _ h => hFinj h)]
        apply Finset.sum_congr rfl
        intro T _
        rw [hF, invWord_insert_last_map_castSucc]
      · -- `last N ∉ S` block
        have himg : (Finset.univ.filter (fun S : Finset (Fin (N+1)) => S.card = k'+1)).filter
            (fun S => ¬ Fin.last N ∈ S)
            = (Finset.univ.filter (fun T : Finset (Fin N) => T.card = k'+1)).image G := by
          ext S
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · rintro ⟨hcard, hlast⟩
            -- S ⊆ range castSucc since last ∉ S
            have hsub : (↑S : Set (Fin (N+1))) ⊆ Set.range Fin.castSucc := by
              intro x hx
              rcases Fin.eq_castSucc_or_eq_last x with ⟨j, rfl⟩ | rfl
              · exact ⟨j, rfl⟩
              · exact absurd hx hlast
            refine ⟨S.preimage Fin.castSucc (Fin.castSucc_injective N).injOn, ?_, ?_⟩
            · have hmap : (S.preimage Fin.castSucc (Fin.castSucc_injective N).injOn).map
                  Fin.castSuccEmb = S := by
                rw [Finset.map_eq_image]
                have : (Fin.castSuccEmb : Fin N ↪ Fin (N+1)) = ⟨Fin.castSucc, Fin.castSucc_injective N⟩ := rfl
                rw [this]
                simp only [Function.Embedding.coeFn_mk]
                rw [Finset.image_preimage]
                rw [Finset.filter_true_of_mem]
                intro x hx
                exact hsub hx
              rw [← Finset.card_map Fin.castSuccEmb, hmap, hcard]
            · show Finset.map Fin.castSuccEmb
                (S.preimage Fin.castSucc (Fin.castSucc_injective N).injOn) = S
              rw [Finset.map_eq_image]
              have : (Fin.castSuccEmb : Fin N ↪ Fin (N+1)) = ⟨Fin.castSucc, Fin.castSucc_injective N⟩ := rfl
              rw [this]
              simp only [Function.Embedding.coeFn_mk]
              rw [Finset.image_preimage]
              rw [Finset.filter_true_of_mem]
              intro x hx; exact hsub hx
          · rintro ⟨T, hT, rfl⟩
            refine ⟨?_, ?_⟩
            · rw [hG, Finset.card_map, hT]
            · rw [hG, Finset.mem_map]; rintro ⟨a, _, ha⟩; exact Fin.castSucc_ne_last a ha
        rw [himg, Finset.sum_image (fun T1 _ T2 _ h => hGinj h)]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T hT
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
        rw [hG, invWord_map_castSucc, hT]
        rw [pow_add]; ring

/-- **Layer 2 (internal pair count).**  Inversions plus non-inversions equals the
total number of (one-position, zero-position) ordered-by-value pairs `k*(N-k)`. -/
theorem inv_add_noninvWord {N k : ℕ} {S : Finset (Fin N)} (hS : S.card = k) :
    invWord S + noninvWord S = k * (N - k) := by
  unfold invWord noninvWord
  rw [← Finset.card_union_of_disjoint]
  · rw [← Finset.filter_or]
    have hcard : (S ×ˢ Sᶜ).card = k * (N - k) := by
      rw [Finset.card_product, hS, Finset.card_compl, Fintype.card_fin, hS]
    rw [← hcard]
    apply Finset.card_bij'
      (i := fun ij _ => if ij.1 ∈ S then (ij.1, ij.2) else (ij.2, ij.1))
      (j := fun ab _ => if ab.1 < ab.2 then (ab.1, ab.2) else (ab.2, ab.1))
    · -- maps into S ×ˢ Sᶜ
      rintro ⟨i, j⟩ h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
      rcases h with ⟨hlt, hi, hj⟩ | ⟨hlt, hi, hj⟩
      · rw [if_pos hi]
        simp only [Finset.mem_product, Finset.mem_compl]
        exact ⟨hi, hj⟩
      · rw [if_neg hi]
        simp only [Finset.mem_product, Finset.mem_compl]
        exact ⟨hj, hi⟩
    · -- maps into filter
      rintro ⟨a, b⟩ h
      simp only [Finset.mem_product, Finset.mem_compl] at h
      obtain ⟨ha, hb⟩ := h
      have hne : a ≠ b := by rintro rfl; exact hb ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [if_pos hlt]
        exact Or.inl ⟨hlt, ha, hb⟩
      · rw [if_neg (not_lt.mpr (le_of_lt hgt))]
        exact Or.inr ⟨hgt, hb, ha⟩
    · -- left inverse
      rintro ⟨i, j⟩ h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
      rcases h with ⟨hlt, hi, hj⟩ | ⟨hlt, hi, hj⟩
      · rw [if_pos hi]; dsimp only; rw [if_pos hlt]
      · rw [if_neg hi]; dsimp only
        rw [if_neg (not_lt.mpr (le_of_lt hlt))]
    · -- right inverse
      rintro ⟨a, b⟩ h
      simp only [Finset.mem_product, Finset.mem_compl] at h
      obtain ⟨ha, hb⟩ := h
      have hne : a ≠ b := by rintro rfl; exact hb ha
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [if_pos hlt]; dsimp only; rw [if_pos ha]
      · rw [if_neg (not_lt.mpr (le_of_lt hgt))]; dsimp only; rw [if_neg hb]
  · -- disjointness
    rw [Finset.disjoint_filter]
    rintro ⟨i, j⟩ _ ⟨_, hi, _⟩ ⟨_, hi', _⟩
    exact hi' hi

/-- **Layer 0 helper (ring-hom naturality of `qChoose X`).**  Mapping the
Gaussian binomial `qChoose (X : R[X]) N k` through a ring hom `f : R →+* S`
(which fixes `X`) yields `qChoose (X : S[X]) N k`.  Proved by induction via the
last-bit recurrence `qChoose_succ_succ`. -/
theorem qChoose_map {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (N k : ℕ) :
    Polynomial.map f (qChoose (Polynomial.X : Polynomial R) N k)
      = qChoose (Polynomial.X : Polynomial S) N k := by
  induction N generalizing k with
  | zero =>
    rcases k with _ | k
    · simp
    · simp
  | succ N ih =>
    rcases k with _ | k
    · simp
    · rw [qChoose_succ_succ, qChoose_succ_succ]
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, ih k, ih (k + 1)]
      simp

/-- **Layer 0 (Laurent-coefficient version of `qChoose_eq_sum_invWord`).**  The
`ℤ`-coefficient Gaussian binomial is likewise the inversion generating function.
Obtained by mapping the proved `ℕ`-coefficient identity through `Nat.castRingHom
ℤ`. -/
theorem qChoose_eq_sum_invWord_Z (N k : ℕ) :
    qChoose (Polynomial.X : Polynomial ℤ) N k =
      ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin N) => S.card = k)),
        (Polynomial.X : Polynomial ℤ) ^ invWord S := by
  classical
  rw [← qChoose_map (Nat.castRingHom ℤ) N k, qChoose_eq_sum_invWord N k]
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [Polynomial.map_pow]
  simp

/-- **Layer 0 (complement involution).**  The non-inversion count of `S` equals
the inversion count of the complement `Sᶜ`: a `1` after a `0` in `S` is a `1`
before a `0` in `Sᶜ`.  Pure `Finset` identity of the two filter sets. -/
theorem noninvWord_compl {N : ℕ} (S : Finset (Fin N)) :
    noninvWord S = invWord Sᶜ := by
  classical
  unfold noninvWord invWord
  congr 1
  ext ⟨i, j⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, not_not]

/-- **Layer 0 (q-binomial reciprocity, Laurent form).**  Applying the reciprocal
map `q ↦ q⁻¹` (`LaurentPolynomial.invert`, which sends `T n ↦ T (-n)`) to the
Gaussian binomial `qChoose X N k` (viewed as a Laurent polynomial via
`toLaurent`) yields `q^{-k(N-k)}` times the complementary Gaussian binomial
`qChoose X N (N-k)`.  Proof: expand both sides by the inversion generating
function (`qChoose_eq_sum_invWord_Z`); term by term `-inv(S) = -k(N-k) + noninv(S)`
with `noninv(S) = inv(Sᶜ)` (`inv_add_noninvWord`, `noninvWord_compl`); reindex the
sum by the complement bijection `S ↦ Sᶜ` sending `{card = k}` onto `{card = N-k}`. -/
theorem qChoose_reciprocity_laurent (N k : ℕ) (hk : k ≤ N) :
    LaurentPolynomial.invert
        (Polynomial.toLaurent (qChoose (Polynomial.X : Polynomial ℤ) N k))
      = LaurentPolynomial.T (-(k * (N - k) : ℤ)) *
          Polynomial.toLaurent (qChoose (Polynomial.X : Polynomial ℤ) N (N - k)) := by
  classical
  rw [qChoose_eq_sum_invWord_Z N k, qChoose_eq_sum_invWord_Z N (N - k)]
  rw [map_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_bij'
    (i := fun S _ => Sᶜ) (j := fun S _ => Sᶜ) ?_ ?_ ?_ ?_ ?_
  · -- forward map lands in {card = N-k}
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    rw [Finset.card_compl, Fintype.card_fin, hS]
  · -- backward map lands in {card = k}
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    rw [Finset.card_compl, Fintype.card_fin, hS, Nat.sub_sub_self hk]
  · -- left inverse
    intro S _; simp
  · -- right inverse
    intro S _; simp
  · -- summand equality
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    rw [map_pow, map_pow, Polynomial.toLaurent_X, LaurentPolynomial.invert_T,
      map_pow, Polynomial.toLaurent_X]
    rw [LaurentPolynomial.T_pow, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add]
    congr 1
    have hkey : invWord S + noninvWord S = k * (N - k) := inv_add_noninvWord hS
    rw [noninvWord_compl] at hkey
    have hkey' : (invWord S : ℤ) + (invWord Sᶜ : ℤ) = (k : ℤ) * ((N : ℤ) - (k : ℤ)) := by
      have : ((k * (N - k) : ℕ) : ℤ) = (k : ℤ) * ((N : ℤ) - (k : ℤ)) := by
        rw [Nat.cast_mul, Nat.cast_sub hk]
      rw [← this]; exact_mod_cast hkey
    linarith

/-- **Layer RECIP (product Gaussian-binomial reciprocity).**  Applying the
reciprocal map `q ↦ q⁻¹` to a finite product of Gaussian binomials distributes
over the product; each factor is rewritten by the banked atom
`qChoose_reciprocity_laurent`, and the `T`-shifts collect additively.  Pure finite
algebra atop the atom -- no new kernel.  This is Layer RECIP of
`research/the_pinned_main_theorem_b_hb_3_b-180a03bf.tex`. -/
theorem qChoose_product_reciprocity {ι : Type*} (s : Finset ι)
    (N k : ι → ℕ) (h : ∀ i ∈ s, k i ≤ N i) :
    LaurentPolynomial.invert
        (∏ i ∈ s, Polynomial.toLaurent (qChoose (Polynomial.X : Polynomial ℤ) (N i) (k i)))
      = LaurentPolynomial.T (-(∑ i ∈ s, (k i * (N i - k i) : ℤ)))
          * ∏ i ∈ s, Polynomial.toLaurent
              (qChoose (Polynomial.X : Polynomial ℤ) (N i) (N i - k i)) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hmem : ∀ i ∈ s, k i ≤ N i := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hka : k a ≤ N a := h a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
      map_mul, qChoose_reciprocity_laurent (N a) (k a) hka, ih hmem]
    rw [neg_add, LaurentPolynomial.T_add]
    ring

end LeafABuild

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

This is Fact 9 (`FactInvComp`), the section 3.4 inversion computation of the
Schilling--Warnaar `q`-supernomials.

We work over the ring of Laurent polynomials `LaurentPolynomial ℤ`, with the
formal variable `q = T 1` (so `q⁻¹ = T (-1)`).  The Gaussian polynomial
(`q`-binomial coefficient) is
```
[N; j]_q = (q)_N / ((q)_j · (q)_{N-j})   if 0 ≤ j ≤ N,   and 0 otherwise,
```
where `(q)_m = ∏_{t=1}^m (1 - q^t)`.  In `axiomlib` this is `qChoose q N j`; it
vanishes for `j > N`.

We fix an integer `ℓ ≥ 1`, a weakly decreasing tuple `r = (r₁,…,r_ℓ)` with
`r₁ ≥ ⋯ ≥ r_ℓ ≥ 0`, and an integer `s ≥ 0`.  Boundary conventions:
`a₀ = s`, `a_{ℓ+1} = 0`, `z_{ℓ+1} = 0`.

## Design of this formalization

The combinatorial objects of the problem are given *concretely* (not left as
arbitrary variables):

* `Row` / `MultiTab` model one-row `{1,2}`-tableaux and multitableaux; the field
  `ones ≤ len` enforces one-row tableau validity (Definition 2).
* `invMT` is Schilling's inversion statistic, defined as the single-row
  crossing count of Definition 4 (this *is* Schilling's single-row inversion
  rule, made concrete rather than assumed).
* `aOf`, `zOf` are the block-count maps of Definition 3.
* `invWord` is the word-inversion statistic; `Ja`, `Jz` are the per-tableau
  level statistics of Definition 5, built from `invWord`.
* `TsetOrder` is the concrete reindexing multitableau set of Definition 3,
  parameterized by the block order (`true` = beta-block-first, `false` =
  s-block-first).  `TsetMinus`/`TsetPlus` are its two specializations.

The *only* object left abstract is the supernomial `S̃` itself, which
Definition 1 explicitly prescribes to be a universally quantified `variable`
`Stil : LaurentPolynomial ℤ → List ℤ → List ℕ → LaurentPolynomial ℤ`.  Here the
FIRST argument is the formal variable `q`: `S̃_{λμ}(q) = Stil q λ μ'` is a fixed
Laurent polynomial in `q`.  Crucially, `S̃(q⁻¹)` is NOT obtained by feeding a
different value into that slot; it is the *substitution* `q ↦ q⁻¹` applied to the
polynomial `S̃_{λμ}(q)`, realized by the ring involution `invSub` (`T n ↦ T (-n)`)
of `LaurentPolynomial ℤ`.  This keeps Fact 2 stated at the standard variable `q`
only (rather than parametrically over all Laurent polynomials).

The external assumptions of `problem.md` are recorded exactly, and are supplied
as *hypotheses* to the four main theorems (never as global axioms and never as
auxiliary proof obligations):

* **Fact 2** (`fact2`), stated at the fixed formal variable `q`:
  `S̃_{(M,|μ|−M),μ}(q) = Σ_{T ∈ Tset λ μ} q^{inv(T)}`, with `Tset` the
  beta-block-first reindexing set (a fixed component order for `μ`); together with
  its permutation-invariance clause (`fact2_perm`): permuting the one-row
  components of `μ` -- concretely, switching to the s-block-first order -- leaves
  the inv-sum unchanged.
* **Fact 3** (`fact3`): content symmetry `S̃_{(A,B),μ} = S̃_{(B,A),μ}`.
* **Fact "binary word"** (`binary_word_gauss`): the binary-word interpretation of
  the Gaussian polynomial, `[N; k] = Σ_{w ∈ {0,1}^N, |w|=k} q^{inv(w)}`.  This is
  an EXTERNAL ASSUMPTION of `problem.md` (a standard identity, used to prove
  `eq:Jgf`), so it is provided as a hypothesis to be USED by the section 3.4
  computation, not a goal the solver must establish.

Statements 1--4 (Fact 9) are the four theorems below with their proofs left open.
They are the *conclusions* of the section 3.4 computation, not hypotheses.

## Indexing convention

Mathematical indices run `i = 1,…,ℓ`.  In Lean, tuples `a z : Fin ℓ → ℕ` use
`j : Fin ℓ` with the correspondence (math index) `i = j + 1`.  Thus `a_i := a j`,
and the boundary neighbours are handled by `shiftPrev` (giving `a_{i-1}`, equal
to `s` at the left boundary) and `shiftNext` (giving `a_{i+1}`, equal to `0` at
the right boundary).  The level sums defining `Ja`/`Jz` range over the math
levels `i ∈ {1, …, ℓ}` (`Finset.Icc 1 ℓ`).

## Correctness of the content constraint (`eq:Mlevels`), stated informally

`aOf T i = a_i` and `zOf T i` count, over the math range `i = 1,…,ℓ`, the rows
with `ones ≥ i`, so the level sum `Σ_{i=1}^ℓ (a_i + z_i)` (`levelSum`) equals
`Σ_{rows} min(ones, ℓ)`.  This coincides with `totalOnes T = Σ_{rows} ones`
exactly when every row has `ones ≤ ℓ`.  For the reindexing tableaux this always
holds: the s-block rows have length `ℓ` and the beta-block rows have length equal
to a part of `β`, which is `≤ ℓ` because `β' = (r₁,…,r_ℓ)` has only `ℓ` parts.
Hence membership `levelSum T = M` in `TsetOrder` genuinely captures "total number
of `1`s is `M`" (Definition 3).  This is a design note only; it is not part of
`problem.md`'s Main Statements, so it creates no extra proof obligation.
-/

namespace SupernomialInv

open LaurentPolynomial

/-! ## The formal variable and the `q ↦ q⁻¹` substitution. -/

/-- The formal variable `q = T 1` in `LaurentPolynomial ℤ`. -/
noncomputable def q : LaurentPolynomial ℤ := T 1

/-- The `q ↦ q⁻¹` substitution on `LaurentPolynomial ℤ`, i.e. the ring
(algebra) involution sending `T n ↦ T (-n)`.  It realizes evaluation of a
Laurent polynomial `S̃(q)` at `q⁻¹`. -/
noncomputable def invSub : LaurentPolynomial ℤ →ₐ[ℤ] LaurentPolynomial ℤ :=
  AddMonoidAlgebra.mapDomainAlgHom ℤ ℤ (-AddMonoidHom.id ℤ)

/-- `invSub` sends `T n` to `T (-n)`; in particular `invSub q = q⁻¹`. -/
theorem invSub_T (n : ℤ) : invSub (T n) = T (-n) := by
  show AddMonoidAlgebra.mapDomainAlgHom ℤ ℤ (-AddMonoidHom.id ℤ) (LaurentPolynomial.T n) = _
  rw [LaurentPolynomial.T, AddMonoidAlgebra.mapDomainAlgHom_apply,
      AddMonoidAlgebra.mapDomain_single]
  simp only [AddMonoidHom.neg_apply, AddMonoidHom.id_apply]
  rfl

/-- `invSub q = q⁻¹ = T (-1)`. -/
theorem invSub_q : invSub q = T (-1) := by
  rw [q, invSub_T]

/-- `invSub (q ^ n) = T (-(n : ℤ))`. -/
theorem invSub_q_pow (n : ℕ) : invSub (q ^ n) = T (-(n : ℤ)) := by
  rw [map_pow, invSub_q, LaurentPolynomial.T_pow]
  congr 1
  ring

/-! ## The Gaussian polynomial. -/

/-- The Gaussian polynomial (`q`-binomial coefficient) `[N; j]_q`, taken in
`LaurentPolynomial ℤ`.  It agrees with the `axiomlib` `qChoose` and vanishes
for `j > N`. -/
noncomputable def gauss (N j : ℕ) : LaurentPolynomial ℤ := qChoose q N j

/-! ## Definition 2: one-row `{1,2}`-tableaux and multitableaux. -/

/-- A one-row semistandard `{1,2}`-tableau of length `len`, determined by its
number `ones ≤ len` of entries equal to `1` (its entries are `ones` ones followed
by twos).  The field `ones_le` enforces one-row tableau validity. -/
structure Row where
  len : ℕ
  ones : ℕ
  ones_le : ones ≤ len
deriving DecidableEq

instance : Inhabited Row := ⟨⟨0, 0, le_refl 0⟩⟩

/-- Column `c` (1-indexed) of a row holds a `1` iff `1 ≤ c ≤ ones`. -/
def cellIsOne (p : Row) (c : ℕ) : Bool := decide (1 ≤ c ∧ c ≤ p.ones)

/-- Column `c` (1-indexed) of a row holds a `2` iff `ones < c ≤ len`. -/
def cellIsTwo (p : Row) (c : ℕ) : Bool := decide (p.ones < c ∧ c ≤ p.len)

/-- A multitableau, with the beta-block rows and s-block rows kept apart so that
the block-count maps `aOf`/`zOf` are well defined.  `order = true` means the
beta-block comes first; `order = false` means the s-block comes first
(Definition 3, the two block orders). -/
structure MultiTab where
  betaRows : List Row
  sRows : List Row
  order : Bool
deriving DecidableEq

/-- The underlying one-row sequence of a multitableau, in the chosen block
order. -/
def MultiTab.flatten (T : MultiTab) : List Row :=
  if T.order then T.betaRows ++ T.sRows else T.sRows ++ T.betaRows

/-! ## Definition 4: Schilling's inversion statistic `inv`.

The single-row specialization counts, for a fixed component order, the crossings
between a `1` and a `2`: an inversion is formed either by two cells in the same
column, with a `2` in the earlier component and a `1` in the later component; or
by adjacent columns, with a `1` in column `c+1` of the earlier component and a
`2` in column `c` of the later component. -/

/-- Crossings between an earlier row `p` and a later row `p'`. -/
def crossings (p p' : Row) : ℕ :=
  let N := max p.len p'.len
  (∑ c ∈ Finset.Icc 1 N, (if cellIsTwo p c ∧ cellIsOne p' c then 1 else 0))
  + (∑ c ∈ Finset.Icc 1 N, (if cellIsOne p (c + 1) ∧ cellIsTwo p' c then 1 else 0))

/-- Schilling's inversion statistic of a multitableau: the total crossing count
over all ordered pairs of components, in the multitableau's block order.  This is
the concrete form of Schilling's single-row inversion rule (Definition 4). -/
def invMT (T : MultiTab) : ℕ :=
  let rows := T.flatten
  ∑ i ∈ Finset.range rows.length, ∑ j ∈ Finset.Ioo i rows.length,
    crossings rows[i]! rows[j]!

/-- Intra-block crossings: crossings between ordered pairs whose indices both
lie in `[lo, hi)`. -/
def intraSum (rows : List Row) (lo hi : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico lo hi, ∑ j ∈ Finset.Ioo i hi, crossings rows[i]! rows[j]!

/-- Cross-block crossings: crossings from an earlier component with index in
`[0, nb)` to a later component with index in `[nb, n)`. -/
def crossSum (rows : List Row) (nb n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range nb, ∑ j ∈ Finset.Ico nb n, crossings rows[i]! rows[j]!

/-! ## Definition 3: the block-count maps `aOf`, `zOf`. -/

/-- Number of rows `p` in the component list with `ones ≥ i`. -/
def countLevel (rows : List Row) (i : ℕ) : ℕ :=
  (rows.filter (fun p => i ≤ p.ones)).length

/-- `aOf T ⟨i,_⟩ = a_{i+1} = #{ rows p of the s-block with u_p ≥ i+1 }`, i.e. for
`i : Fin ℓ` the Lean index `i` corresponds to the math index `i+1 ∈ {1,…,ℓ}`, so
`aOf T ⟨0,_⟩ = a_1 = #{u_p ≥ 1}`. -/
def aOf {ℓ : ℕ} (T : MultiTab) (i : Fin ℓ) : ℕ := countLevel T.sRows (i + 1)

/-- `zOf T ⟨i,_⟩ = z_{i+1} = #{ rows p of the beta-block with u_p ≥ i+1 }`, with
the same Lean/math index correspondence as `aOf`. -/
def zOf {ℓ : ℕ} (T : MultiTab) (i : Fin ℓ) : ℕ := countLevel T.betaRows (i + 1)

/-! ## Definition 5: the level statistics `Jₐ`, `J_z`. -/

/-- Word-inversion statistic `inv(w) = #{ p < p' : w_p = 1, w_{p'} = 0 }`. -/
def invWord (w : List Bool) : ℕ :=
  ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
    (if w[i]! = true ∧ w[j]! = false then 1 else 0)

/-- The level-`i` word for `Jₐ` (s-block).  Among the s-block rows (in component
order) that reached level `i-1` (i.e. `ones ≥ i-1`, there are `a_{i-1}` of them),
record which continue to level `i` (`ones ≥ i`, there are `a_i` of them).  For
math levels `1 ≤ i ≤ ℓ`. -/
def wordA (sRows : List Row) (i : ℕ) : List Bool :=
  (sRows.filter (fun p => i - 1 ≤ p.ones)).map (fun p => decide (i ≤ p.ones))

/-- The level-`i` word for `J_z` (beta-block).  The *eligible* beta-block rows at
level `i` are those of length `≥ i` that do not continue to level `i+1`, i.e.
`len ≥ i` and `ones < i+1` (there are `r_i − z_{i+1}` of them, since exactly
`r_i` beta-rows have length `≥ i` and `z_{i+1}` of them have `ones ≥ i+1`).  Among
these, in component order, record which end precisely at level `i` (`ones = i`,
there are `z_i − z_{i+1}` of them).  For math levels `1 ≤ i ≤ ℓ`. -/
def wordZ (betaRows : List Row) (i : ℕ) : List Bool :=
  (betaRows.filter (fun p => i ≤ p.len ∧ p.ones < i + 1)).map
    (fun p => decide (p.ones = i))

/-- `Jₐ(T) = Σ_{i=1}^ℓ inv(word for level i)`, a per-tableau statistic (value in
`ℤ`).  The level index `i` runs over the math range `1 ≤ i ≤ ℓ`. -/
def Ja (ℓ : ℕ) (T : MultiTab) : ℤ :=
  ∑ i ∈ Finset.Icc 1 ℓ, (invWord (wordA T.sRows i) : ℤ)

/-- `J_z(T) = Σ_{i=1}^ℓ inv(word for level i)`, a per-tableau statistic (value in
`ℤ`).  The level index `i` runs over the math range `1 ≤ i ≤ ℓ`. -/
def Jz (ℓ : ℕ) (T : MultiTab) : ℤ :=
  ∑ i ∈ Finset.Icc 1 ℓ, (invWord (wordZ T.betaRows i) : ℤ)

/-! ## Boundary accessors for tuples indexed by `Fin ℓ`. -/

/-- Value of `t` at the previous math level, with left-boundary value `bd`. -/
def shiftPrev {ℓ : ℕ} (bd : ℕ) (t : Fin ℓ → ℕ) (j : Fin ℓ) : ℕ :=
  if (j : ℕ) = 0 then bd else t ⟨(j : ℕ) - 1, by omega⟩

/-- Value of `t` at the next math level, with right-boundary value `0`. -/
def shiftNext {ℓ : ℕ} (t : Fin ℓ → ℕ) (j : Fin ℓ) : ℕ :=
  if h : (j : ℕ) + 1 = ℓ then 0 else t ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩

/-! ## The reindexing multitableau sets. -/

/-- `betaParts r` is the partition `β` (row lengths of the beta-block), whose
conjugate is `β' = (r₁,…,r_ℓ)`: `β_c = #{ i : r_i ≥ c }` for `c = 1,…`. -/
def betaParts {ℓ : ℕ} (r : Fin ℓ → ℕ) : List ℕ :=
  let R := if 0 < ℓ then (Finset.univ.sup r) else 0
  (List.range R).map (fun c => (Finset.univ.filter (fun i => c + 1 ≤ r i)).card)

/-- The s-block row lengths: `s` rows each of length `ℓ`. -/
def sBlockLens (ℓ s : ℕ) : List ℕ := List.replicate s ℓ

/-- All valid one-row tableaux of a prescribed length. -/
def rowsOfLen (L : ℕ) : Finset Row :=
  (Finset.range (L + 1)).image (fun u => (⟨L, min u L, min_le_right _ _⟩ : Row))

/-- All fillings of a prescribed list of row lengths by valid one-row tableaux. -/
def fillings : List ℕ → Finset (List Row)
  | [] => {[]}
  | L :: Ls => ((rowsOfLen L) ×ˢ (fillings Ls)).image (fun p => p.1 :: p.2)

/-- Total number of `1`s of a multitableau. -/
def totalOnes (T : MultiTab) : ℕ :=
  (T.betaRows.map Row.ones).sum + (T.sRows.map Row.ones).sum

/-- The level sum `Σ_{i=1}^ℓ (a_i + z_i) = Σ_{i=1}^ℓ (aOf T i + zOf T i)`, i.e.
the number `M` of `eq:Mlevels`.  For a tableau whose rows all have `ones ≤ ℓ`
(true for every element of `TsetOrder`, whose row lengths are all `≤ ℓ`), this
equals `totalOnes T` (see the design note in the file header).  Using the level
sum directly as the content constraint makes `M = Σ_{i=1}^ℓ (a_i + z_i)` hold by
definition of membership, matching `eq:Mlevels` exactly (Definition 3). -/
def levelSum {ℓ : ℕ} (T : MultiTab) : ℕ :=
  ∑ i, (aOf (ℓ := ℓ) T i + zOf (ℓ := ℓ) T i)

/-- `TsetOrder r s M betaFirst`: the reindexing multitableaux of shape `μ` with
total content `λ = (M, |μ|−M)`, i.e. with `M = Σ_{i=1}^ℓ (a_i + z_i)` (the level
count `eq:Mlevels`), in the block order determined by `betaFirst` (`true` =
beta-block-first, `false` = s-block-first).  The beta-block rows have lengths
`betaParts r` (all `≤ ℓ`, since `β' = (r₁,…,r_ℓ)` has `ℓ` parts); the s-block has
`s` rows of length `ℓ`.  Because all row lengths are `≤ ℓ`, every row has
`ones ≤ ℓ`, so this level count agrees with `totalOnes T` (see the design note in
the file header).  This is the concrete `Tset λ μ` of Definition 3 for a fixed
component order; different orders (permutations of the components of `μ`) give
different multitableaux but the same inv-sum (Fact 2 permutation invariance). -/
noncomputable def TsetOrder {ℓ : ℕ} (r : Fin ℓ → ℕ) (s M : ℕ) (betaFirst : Bool) :
    Finset MultiTab :=
  (((fillings (betaParts r)) ×ˢ (fillings (sBlockLens ℓ s))).image
    (fun p => (⟨p.1, p.2, betaFirst⟩ : MultiTab))).filter
    (fun T => levelSum (ℓ := ℓ) T = M)

/-- `TsetMinus r s M`: the reindexing multitableaux in the **beta-block-first**
order (used with the minus-sign exponent `E⁻`).  This is the canonical component
order for `μ` at which Fact 2 is stated. -/
noncomputable def TsetMinus {ℓ : ℕ} (r : Fin ℓ → ℕ) (s M : ℕ) : Finset MultiTab :=
  TsetOrder r s M true

/-- `TsetPlus r s M`: the reindexing multitableaux in the **s-block-first**
order (used with the plus-sign exponent `E⁺`).  It differs from `TsetMinus` by a
permutation of the one-row components of `μ`. -/
noncomputable def TsetPlus {ℓ : ℕ} (r : Fin ℓ → ℕ) (s M : ℕ) : Finset MultiTab :=
  TsetOrder r s M false

/-! ## Definition 8: the index set `azFinset`. -/

/-- The domain constraints `eq:domain`:
`s = a₀ ≥ a₁ ≥ ⋯ ≥ a_ℓ ≥ 0` and `r_i ≥ z_i ≥ z_{i+1}` for `1 ≤ i ≤ ℓ`
(the right boundary `z_{ℓ+1} = 0` is built into `shiftNext`). -/
def azDomain {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ) (a z : Fin ℓ → ℕ) : Prop :=
  (∀ j, a j ≤ shiftPrev s a j) ∧ (∀ j, z j ≤ r j) ∧ (∀ j, shiftNext z j ≤ z j)

instance {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ) (a z : Fin ℓ → ℕ) :
    Decidable (azDomain r s a z) := by
  unfold azDomain; infer_instance

/-- `azFinset r s M` is the finite set of pairs `(a, z)` of tuples
`Fin ℓ → ℕ` satisfying `eq:domain` together with `Σ_{i} (a_i + z_i) = M`. -/
noncomputable def azFinset {ℓ : ℕ} (r : Fin ℓ → ℕ) (s M : ℕ) :
    Finset ((Fin ℓ → ℕ) × (Fin ℓ → ℕ)) :=
  ((Fintype.piFinset (fun _ => Finset.range (s + 1))) ×ˢ
      (Fintype.piFinset (fun i => Finset.range (r i + 1)))).filter
    (fun p => azDomain r s p.1 p.2 ∧ ∑ i, (p.1 i + p.2 i) = M)

/-! ## Definition 6: the signed exponents `E⁻`, `E⁺`. -/

/-- `E⁻(a, z) = Σ_i (a_i² + z_i² + a_i z_i + z_i·a_{i-1} − r_i·(a_i + z_i))`,
with `a_{i-1}` using the left boundary `a₀ = s`.  Value in `ℤ`. -/
def Eminus {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ) (a z : Fin ℓ → ℕ) : ℤ :=
  ∑ j, ((a j : ℤ) ^ 2 + (z j : ℤ) ^ 2 + (a j : ℤ) * (z j : ℤ)
        + (z j : ℤ) * (shiftPrev s a j : ℤ)
        - (r j : ℤ) * ((a j : ℤ) + (z j : ℤ)))

/-- `E⁺(a, z) = Σ_i (a_i² + z_i² + a_i z_i + a_{i+1}·z_i − r_i·(a_{i+1} + z_i))`,
with `a_{i+1}` using the right boundary `a_{ℓ+1} = 0`.  Value in `ℤ`. -/
def Eplus {ℓ : ℕ} (r : Fin ℓ → ℕ) (a z : Fin ℓ → ℕ) : ℤ :=
  ∑ j, ((a j : ℤ) ^ 2 + (z j : ℤ) ^ 2 + (a j : ℤ) * (z j : ℤ)
        + (shiftNext a j : ℤ) * (z j : ℤ)
        - (r j : ℤ) * ((shiftNext a j : ℤ) + (z j : ℤ)))

/-! ## Definition 7: the Gaussian weight `B_{r,s}`. -/

/-- `B_{r,s}(a, z) = ∏_i [a_{i-1}; a_i] · [r_i − z_{i+1}; z_i − z_{i+1}]`, a
product of Gaussian polynomials, using boundary conventions `a₀ = s`,
`z_{ℓ+1} = 0`. -/
noncomputable def Bweight {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ) (a z : Fin ℓ → ℕ) :
    LaurentPolynomial ℤ :=
  ∏ j, gauss (shiftPrev s a j) (a j) *
        gauss (r j - shiftNext z j) (z j - shiftNext z j)

/-! ## Auxiliary data for `μ`. -/

section Mu
variable {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ)

/-- `μ' = (r₁ + s, …, r_ℓ + s)` (eq:muprime), as a `List ℕ`. -/
def muPrime : List ℕ := (List.finRange ℓ).map (fun j => r j + s)

/-- `|μ| = Σ_{i=1}^ℓ (r_i + s)`. -/
def muSize : ℕ := ∑ j, (r j + s)

end Mu

/-! ## The binary-word Gaussian identity — Fact "binary word".

`[N; k] = Σ_{w ∈ {0,1}^N, |w| = k} q^{inv(w)}`, the binary-word interpretation of
the Gaussian polynomial.  Here binary words of length `N` are modeled as
`v : Fin N → Bool` and `|w|` is the number of `true` entries.  This is a standard
identity, listed by `problem.md` alongside Fact 2 and Fact 3 as an EXTERNAL
ASSUMPTION to be USED (to prove `eq:Jgf`), not proved.  It is packaged as the
predicate `BinaryWordGauss` and supplied as a hypothesis to the four main
theorems below. -/
def BinaryWordGauss : Prop :=
  ∀ N k : ℕ,
    gauss N k
      = ∑ v ∈ (Finset.univ.filter
            (fun v : Fin N → Bool => (Finset.univ.filter (fun i => v i = true)).card = k)),
          q ^ (invWord (List.ofFn v))

/-! ## Main Statement(s)

Fix `ℓ ≥ 1`, `r` weakly decreasing with `r_ℓ ≥ 0`, `s ≥ 0`, and set
`μ' = (r₁+s,…,r_ℓ+s)`, `|μ| = Σ (r_i + s)`.

The supernomial `S̃` is the only abstract object (`Stil`, per Definition 1); its
first argument is the formal variable `q`, so `S̃_{λμ}(q) = Stil q λ μ'` is a
fixed Laurent polynomial in `q`, and `S̃_{λμ}(q⁻¹) = invSub (Stil q λ μ')` is its
`q ↦ q⁻¹` substitution.  `Stil` is pinned by the two allowed external
assumptions **Fact 2** (`fact2` + `fact2_perm`) and **Fact 3** (`fact3`), and the
binary-word identity is supplied via the hypothesis `hbw : BinaryWordGauss`.  All
other objects are the concrete definitions above; in particular the crossing
count `invMT` *is* Schilling's single-row inversion rule.

Statements 1–4 are the conclusions of the section 3.4 computation (Fact 9); each
is a theorem whose proof is left open. -/

section Statements

variable {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ)
  (Stil : LaurentPolynomial ℤ → List ℤ → List ℕ → LaurentPolynomial ℤ)

/-! ## Sub-lemmas for `inv_decomposition_minus` (numerically confirmed).

The proof of Statement 1 factors, β-block-first, through four combinatorial
identities.  Write `nb = T.betaRows.length`, `n = T.flatten.length`, and
`fl = T.flatten`.  In the β-first order the β-block occupies indices `[0, nb)`
and the s-block occupies `[nb, n)`.  All four were verified by exhaustive
`#eval!` enumeration over `(ℓ,r,s) ∈ {(1,(1),1),(2,(2,1),2),(2,(2,2),1),
(3,(3,2,1),1),(1,(3),2)}` and confirm the closed forms below.  Their algebraic
combination (`invMT_split_minus` + `internal_a` + `internal_z` + `cross_minus`)
yields exactly `s·M − invMT T = Ja + Jz + E⁻`. -/

/-- General nested double-sum split at an intermediate index `nb ≤ n`:
`∑_{i<n}∑_{i<j<n} f = intra[0,nb) + cross[0,nb)×[nb,n) + intra[nb,n)`. -/
theorem sum_Ioo_split (f : ℕ → ℕ → ℕ) (nb n : ℕ) (h : nb ≤ n) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.Ioo i n, f i j
      = (∑ i ∈ Finset.Ico 0 nb, ∑ j ∈ Finset.Ioo i nb, f i j)
        + (∑ i ∈ Finset.range nb, ∑ j ∈ Finset.Ico nb n, f i j)
        + (∑ i ∈ Finset.Ico nb n, ∑ j ∈ Finset.Ioo i n, f i j) := by
  have hIoo : ∀ i : ℕ, Finset.Ioo i n = Finset.Ico (i+1) n := by
    intro i; ext x; simp only [Finset.mem_Ioo, Finset.mem_Ico]; omega
  have hIoonb : ∀ i : ℕ, Finset.Ioo i nb = Finset.Ico (i+1) nb := by
    intro i; ext x; simp only [Finset.mem_Ioo, Finset.mem_Ico]; omega
  rw [Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le nb) h]
  rw [Finset.range_eq_Ico]
  have hfirst : (∑ i ∈ Finset.Ico 0 nb, ∑ j ∈ Finset.Ioo i n, f i j)
      = (∑ i ∈ Finset.Ico 0 nb, ∑ j ∈ Finset.Ioo i nb, f i j)
        + (∑ i ∈ Finset.Ico 0 nb, ∑ j ∈ Finset.Ico nb n, f i j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_Ico] at hi
    rw [hIoo i, hIoonb i]
    rw [← Finset.sum_Ico_consecutive _ (by omega : i+1 ≤ nb) h]
  rw [hfirst, add_assoc]

/-- Split the total inversion count into intra-β, cross, and intra-s parts
(β-block-first). -/
theorem invMT_split_minus
    (M : ℕ) (T : MultiTab) (hT : T ∈ TsetMinus r s M) :
    invMT T
      = intraSum T.flatten 0 T.betaRows.length
        + crossSum T.flatten T.betaRows.length T.flatten.length
        + intraSum T.flatten T.betaRows.length T.flatten.length := by
  have hlen : T.betaRows.length ≤ T.flatten.length := by
    simp only [MultiTab.flatten]
    split <;> simp [List.length_append]
  simpa only [invMT, intraSum, crossSum] using
    sum_Ioo_split (fun i j => crossings T.flatten[i]! T.flatten[j]!)
      T.betaRows.length T.flatten.length hlen

/-! ### Membership extraction helpers for `fillings`. -/

/-- Every row in a member of `rowsOfLen L` has length `L`. -/
lemma mem_rowsOfLen {L : ℕ} {p : Row} (h : p ∈ rowsOfLen L) : p.len = L := by
  simp only [rowsOfLen, Finset.mem_image, Finset.mem_range] at h
  obtain ⟨u, hu, rfl⟩ := h
  rfl

/-- A filling of `Ls` has length `Ls.length`. -/
lemma mem_fillings_len : ∀ (Ls : List ℕ) (w : List Row), w ∈ fillings Ls →
    w.length = Ls.length
  | [], w, h => by simp [fillings] at h; simp [h]
  | (L :: Ls), w, h => by
      simp only [fillings, Finset.mem_image, Finset.mem_product] at h
      obtain ⟨⟨p, ws⟩, ⟨hp, hws⟩, rfl⟩ := h
      simp [mem_fillings_len Ls ws hws]

/-- Each row of a filling of `Ls` has its length among `Ls`. -/
lemma mem_fillings_mem_len : ∀ (Ls : List ℕ) (w : List Row), w ∈ fillings Ls →
    ∀ p ∈ w, p.len ∈ Ls
  | [], w, h => by simp [fillings] at h; subst h; simp
  | (L :: Ls), w, h => by
      simp only [fillings, Finset.mem_image, Finset.mem_product] at h
      obtain ⟨⟨p, ws⟩, ⟨hp, hws⟩, rfl⟩ := h
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · rw [mem_rowsOfLen hp]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_fillings_mem_len Ls ws hws q hq)

/-- The list of row lengths of a filling of `Ls` equals `Ls` exactly (in order). -/
lemma mem_fillings_map_len : ∀ (Ls : List ℕ) (w : List Row), w ∈ fillings Ls →
    w.map Row.len = Ls
  | [], w, h => by simp [fillings] at h; subst h; simp
  | (L :: Ls), w, h => by
      simp only [fillings, Finset.mem_image, Finset.mem_product] at h
      obtain ⟨⟨p, ws⟩, ⟨hp, hws⟩, rfl⟩ := h
      rw [List.map_cons, mem_rowsOfLen hp, mem_fillings_map_len Ls ws hws]

/-- Every row of an s-block filling has length `ℓ`. -/
lemma sBlock_all_len {ℓ s : ℕ} (w : List Row) (h : w ∈ fillings (sBlockLens ℓ s)) :
    ∀ p ∈ w, p.len = ℓ := by
  intro p hp
  have := mem_fillings_mem_len _ w h p hp
  simp only [sBlockLens, List.mem_replicate] at this
  exact this.2

/-- An s-block filling has `s` rows. -/
lemma sBlock_length {ℓ s : ℕ} (w : List Row) (h : w ∈ fillings (sBlockLens ℓ s)) :
    w.length = s := by
  have := mem_fillings_len _ w h
  simpa [sBlockLens] using this

/-- Membership in `TsetMinus` unpacks to β-first order, an s-block filling, and a
β-block filling. -/
lemma mem_TsetMinus_unpack {ℓ : ℕ} {r : Fin ℓ → ℕ} {s M : ℕ} {T : MultiTab}
    (hT : T ∈ TsetMinus r s M) :
    T.order = true ∧ T.sRows ∈ fillings (sBlockLens ℓ s) ∧
      T.betaRows ∈ fillings (betaParts r) := by
  simp only [TsetMinus, TsetOrder, Finset.mem_filter, Finset.mem_image,
    Finset.mem_product] at hT
  obtain ⟨⟨⟨b, w⟩, ⟨hb, hw⟩, hTeq⟩, _⟩ := hT
  subst hTeq
  exact ⟨rfl, hw, hb⟩

/-- Reindexing bridge: intra-block crossings over the tail block `w` of
`b ++ w`, indexed in `[b.length, b.length + w.length)`, equal the self-contained
intra-sum of `w`. -/
lemma intraSum_bridge (b w : List Row) :
    intraSum (b ++ w) b.length (b.length + w.length) = intraSum w 0 w.length := by
  -- pure index shift i ↦ i - b.length; (b++w)[i']!=w[i'-b.length]!.
  set nb := b.length with hnb
  -- getElem! fact for the tail block.
  have hget : ∀ t, t < w.length → (b ++ w)[nb + t]! = w[t]! := by
    intro t ht
    have hlt : nb + t < (b ++ w).length := by
      rw [List.length_append, ← hnb]; omega
    rw [getElem!_pos (b ++ w) (nb + t) hlt, getElem!_pos w t ht]
    rw [List.getElem_append_right (by rw [← hnb]; omega)]
    congr 1
    rw [← hnb]; omega
  have hget' : ∀ i, nb ≤ i → i < nb + w.length → (b ++ w)[i]! = w[i - nb]! := by
    intro i hle hlt
    have := hget (i - nb) (by omega)
    rwa [Nat.add_sub_cancel' hle] at this
  unfold intraSum
  -- reindex outer sum: i ↦ i - nb, backward i' ↦ i' + nb
  refine Finset.sum_nbij' (i := fun x => x - nb) (j := fun x => x + nb)
    ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_Ico] at hi ⊢; omega
  · intro i hi
    simp only [Finset.mem_Ico] at hi ⊢; omega
  · intro i hi
    simp only [Finset.mem_Ico] at hi; omega
  · intro i hi
    simp only [Finset.mem_Ico] at hi; omega
  · -- pointwise equality of inner sums after shift
    intro i hi
    simp only [Finset.mem_Ico] at hi
    -- inner sum reindex: from Ioo i (nb+w.length) to Ioo (i-nb) w.length
    refine Finset.sum_nbij' (i := fun x => x - nb) (j := fun x => x + nb)
      ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Ioo] at hj ⊢; omega
    · intro j hj
      simp only [Finset.mem_Ioo] at hj ⊢; omega
    · intro j hj
      simp only [Finset.mem_Ioo] at hj; omega
    · intro j hj
      simp only [Finset.mem_Ioo] at hj; omega
    · intro j hj
      simp only [Finset.mem_Ioo] at hj
      show crossings (b ++ w)[i]! (b ++ w)[j]! = crossings w[i - nb]! w[j - nb]!
      rw [hget' i (by omega) (by omega), hget' j (by omega) (by omega)]

/-- For two rows both of length `ℓ`, the crossing count has the closed form
`max 0 (u' − u) + max 0 (u − 1 − u')` in terms of their `ones` counts
`u = p.ones`, `u' = p'.ones`. -/
lemma crossings_eqlen {ℓ : ℕ} (p p' : Row) (hp : p.len = ℓ) (hp' : p'.len = ℓ) :
    crossings p p'
      = max 0 (p'.ones - p.ones) + max 0 (p.ones - 1 - p'.ones) := by
  have hpo : p.ones ≤ ℓ := hp ▸ p.ones_le
  have hp'o : p'.ones ≤ ℓ := hp' ▸ p'.ones_le
  unfold crossings cellIsOne cellIsTwo
  rw [hp, hp', max_self]
  simp only [decide_eq_true_eq]
  -- First sum
  have h1 : (∑ c ∈ Finset.Icc 1 ℓ,
        (if (p.ones < c ∧ c ≤ ℓ) ∧ (1 ≤ c ∧ c ≤ p'.ones) then 1 else 0))
      = max 0 (p'.ones - p.ones) := by
    rw [Finset.sum_boole]
    have hfilt : ((Finset.Icc 1 ℓ).filter
          (fun c => (p.ones < c ∧ c ≤ ℓ) ∧ (1 ≤ c ∧ c ≤ p'.ones)))
        = Finset.Icc (p.ones + 1) p'.ones := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hfilt, Nat.card_Icc]
    simp only [Nat.cast_id]
    omega
  -- Second sum
  have h2 : (∑ c ∈ Finset.Icc 1 ℓ,
        (if (1 ≤ c + 1 ∧ c + 1 ≤ p.ones) ∧ (p'.ones < c ∧ c ≤ ℓ) then 1 else 0))
      = max 0 (p.ones - 1 - p'.ones) := by
    rw [Finset.sum_boole]
    have hfilt : ((Finset.Icc 1 ℓ).filter
          (fun c => (1 ≤ c + 1 ∧ c + 1 ≤ p.ones) ∧ (p'.ones < c ∧ c ≤ ℓ)))
        = Finset.Icc (p'.ones + 1) (p.ones - 1) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hfilt, Nat.card_Icc]
    simp only [Nat.cast_id]
    omega
  rw [h1, h2]

/-- **Level decomposition of `crossings` (INTRA).**  For two rows both of length
`ℓ`, the crossing count equals the sum over levels `k ∈ [1,ℓ]` of the local
crossing indicator `C(k) = [u<k≤u'] + [u'+1<k≤u]` (`u = p.ones`, `u' = p'.ones`).
-/
lemma crossings_level_decomp {ℓ : ℕ} (p p' : Row) (hp : p.len = ℓ) (hp' : p'.len = ℓ) :
    crossings p p'
      = ∑ k ∈ Finset.Icc 1 ℓ,
          ((if p.ones < k ∧ k ≤ p'.ones then 1 else 0)
            + (if p'.ones + 1 < k ∧ k ≤ p.ones then 1 else 0)) := by
  -- SANITY CHECK PASSED (numerically confirmed via parent internal_a #eval)
  have hpo : p.ones ≤ ℓ := hp ▸ p.ones_le
  have hp'o : p'.ones ≤ ℓ := hp' ▸ p'.ones_le
  rw [crossings_eqlen p p' hp hp', Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_boole]
    have hfilt : ((Finset.Icc 1 ℓ).filter (fun k => p.ones < k ∧ k ≤ p'.ones))
        = Finset.Icc (p.ones + 1) p'.ones := by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [hfilt, Nat.card_Icc]; simp only [Nat.cast_id]; omega
  · rw [Finset.sum_boole]
    have hfilt : ((Finset.Icc 1 ℓ).filter (fun k => p'.ones + 1 < k ∧ k ≤ p.ones))
        = Finset.Icc (p'.ones + 2) p.ones := by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [hfilt, Nat.card_Icc]; simp only [Nat.cast_id]; omega

/-- The pairwise double-count of a `Bool`-valued relation over a list. -/
def pairSum (l : List Row) (P : Row → Row → Bool) : ℕ :=
  ∑ i ∈ Finset.range l.length, ∑ j ∈ Finset.Ioo i l.length,
    (if P l[i]! l[j]! then 1 else 0)

/-- `getElem!` of a cons at a positive index reduces to the tail. -/
lemma getElem!_cons_pos (p : Row) (ps : List Row) (j : ℕ) (hj : 0 < j) :
    (p :: ps)[j]! = ps[j - 1]! := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [List.getElem!_cons_succ]
  simp

/-- `getElem!` of a cons at index `0` is the head. -/
lemma getElem!_cons_zero' (p : Row) (ps : List Row) :
    (p :: ps)[0]! = p := by
  rw [getElem!_pos (p :: ps) 0 (by simp)]; rfl

/-- `getElem!` of a cons at a successor index. -/
lemma getElem!_cons_succ' (p : Row) (ps : List Row) (j : ℕ) :
    (p :: ps)[j + 1]! = ps[j]! := by
  by_cases hjs : j < ps.length
  · rw [getElem!_pos (p :: ps) (j + 1) (by simp; omega),
        getElem!_pos ps j hjs, List.getElem_cons_succ]
  · rw [getElem!_neg (p :: ps) (j + 1) (by simp; omega),
        getElem!_neg ps j (by omega)]

/-- Cons decomposition of `pairSum`: the head contributes its pairing with every
tail element, and the rest is the tail's `pairSum`. -/
lemma pairSum_cons (p : Row) (ps : List Row) (P : Row → Row → Bool) :
    pairSum (p :: ps) P
      = (∑ j ∈ Finset.range ps.length, (if P p ps[j]! then 1 else 0))
        + pairSum ps P := by
  unfold pairSum
  rw [List.length_cons, Finset.sum_range_succ']
  -- The `i = 0` term (peeled to the *last* summand by `sum_range_succ'`).
  have hhead : (∑ j ∈ Finset.Ioo 0 (ps.length + 1),
        (if P (p :: ps)[0]! (p :: ps)[j]! then 1 else 0))
      = ∑ j ∈ Finset.range ps.length, (if P p ps[j]! then 1 else 0) := by
    -- reindex j ↦ j - 1 over Ioo 0 (ps.length+1)  ≃  range ps.length
    refine Finset.sum_nbij' (i := fun x => x - 1) (j := fun x => x + 1) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Ioo] at hj; simp only [Finset.mem_range]; omega
    · intro j hj; simp only [Finset.mem_range] at hj; simp only [Finset.mem_Ioo]; omega
    · intro j hj; simp only [Finset.mem_Ioo] at hj; omega
    · intro j hj; simp only [Finset.mem_range] at hj; omega
    · intro j hj
      simp only [Finset.mem_Ioo] at hj
      rw [getElem!_cons_zero' p ps, getElem!_cons_pos p ps j (by omega)]
  rw [hhead, add_comm]
  -- The remaining sum over shifted i (`i+1`) matches the tail's pairSum.
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  -- inner: Ioo (i+1) (ps.length+1) ≃ Ioo i ps.length via j ↦ j-1
  refine Finset.sum_nbij' (i := fun x => x - 1) (j := fun x => x + 1) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_Ioo] at hj ⊢; omega
  · intro j hj; simp only [Finset.mem_Ioo] at hj ⊢; omega
  · intro j hj; simp only [Finset.mem_Ioo] at hj; omega
  · intro j hj; simp only [Finset.mem_Ioo] at hj; omega
  · intro j hj
    simp only [Finset.mem_Ioo] at hj
    rw [getElem!_cons_succ' p ps i, getElem!_cons_pos p ps j (by omega)]

/-- `invWord (m.map g)` as a `pairSum` over `m` with the relation
`g a = true ∧ g b = false`. -/
lemma invWord_map (m : List Row) (g : Row → Bool) :
    invWord (m.map g)
      = pairSum m (fun a b => g a && !g b) := by
  unfold invWord pairSum
  rw [List.length_map]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_Ioo] at hj
  have hmi : (m.map g)[i]! = g m[i]! := by
    rw [getElem!_pos (m.map g) i (by rw [List.length_map]; exact hi),
        getElem!_pos m i hi, List.getElem_map]
  have hmj : (m.map g)[j]! = g m[j]! := by
    rw [getElem!_pos (m.map g) j (by rw [List.length_map]; omega),
        getElem!_pos m j (by omega), List.getElem_map]
  rw [hmi, hmj]
  by_cases hgi : g m[i]! = true <;> by_cases hgj : g m[j]! = true <;>
    simp [hgi, hgj]

/-- Filtered single-index contribution: summing a `Bool`-predicate `Q` over a
filtered list equals summing `f · && Q ·` over the whole list. -/
lemma sum_filter_range (l : List Row) (f Q : Row → Bool) :
    (∑ j ∈ Finset.range (l.filter f).length, (if Q (l.filter f)[j]! then 1 else 0))
      = ∑ j ∈ Finset.range l.length, (if f l[j]! && Q l[j]! then 1 else 0) := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    rw [List.filter_cons]
    -- RHS: peel head via sum_range_succ'
    rw [List.length_cons, Finset.sum_range_succ']
    have hRHS : (∑ j ∈ Finset.range ps.length,
          (if f (p :: ps)[j + 1]! && Q (p :: ps)[j + 1]! then 1 else 0))
          + (if f (p :: ps)[0]! && Q (p :: ps)[0]! then 1 else 0)
        = (∑ j ∈ Finset.range ps.length, (if f ps[j]! && Q ps[j]! then 1 else 0))
          + (if f p && Q p then 1 else 0) := by
      rw [getElem!_cons_zero' p ps]
      apply congrArg₂
      · apply Finset.sum_congr rfl; intro j _; rw [getElem!_cons_succ' p ps j]
      · rfl
    rw [hRHS]
    by_cases hf : f p
    · -- filtered list is p :: (ps.filter f)
      rw [if_pos hf, List.length_cons, Finset.sum_range_succ']
      have hbody : (∑ j ∈ Finset.range (ps.filter f).length,
            (if Q (p :: ps.filter f)[j + 1]! then 1 else 0))
          = ∑ j ∈ Finset.range (ps.filter f).length,
            (if Q (ps.filter f)[j]! then 1 else 0) := by
        apply Finset.sum_congr rfl; intro j _; rw [getElem!_cons_succ' p (ps.filter f) j]
      rw [hbody, ih, getElem!_cons_zero' p (ps.filter f)]
      simp [hf]
    · rw [if_neg hf, ih]
      have hz : (if f p && Q p then 1 else 0) = 0 := by simp [hf]
      rw [hz, add_zero]

/-- Filter compatibility for `pairSum`: only pairs whose *both* endpoints survive
the filter `f` are counted. -/
lemma pairSum_filter (l : List Row) (f : Row → Bool) (P : Row → Row → Bool) :
    pairSum (l.filter f) P
      = pairSum l (fun a b => f a && f b && P a b) := by
  induction l with
  | nil => simp [pairSum]
  | cons p ps ih =>
    rw [List.filter_cons]
    rw [pairSum_cons p ps (fun a b => f a && f b && P a b)]
    by_cases hf : f p
    · rw [if_pos hf]
      rw [pairSum_cons p (ps.filter f) P, ih]
      congr 1
      -- head-contribution: over filtered ps vs full ps, with f p = true
      rw [sum_filter_range ps f (fun b => P p b)]
      apply Finset.sum_congr rfl
      intro j _
      simp only [hf, Bool.true_and]
    · rw [if_neg hf, ih]
      -- head contributes nothing since f p = false
      have hzero : (∑ j ∈ Finset.range ps.length,
            (if (fun a b => f a && f b && P a b) p ps[j]! then 1 else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        simp only [hf, Bool.false_and, Bool.and_eq_true]
        rw [if_neg]
        simp
      rw [hzero, zero_add]

/-- **Structural reindexing of `invWord (wordA w k)` (JA).**  The number of `10`
inversions of the level-`k` word equals the count over original index pairs
`i < j` of the presence + bit condition `k ≤ u_i ∧ u_j = k-1`
(`u_i = w[i]!.ones`, `u_j = w[j]!.ones`).  This is the order-preserving
filter/map inversion identity (Step 1c of `informal_ia.md`). -/
lemma invWord_wordA_decomp {ℓ : ℕ} (w : List Row) (hw : ∀ p ∈ w, p.len = ℓ) (k : ℕ)
    (hk : 1 ≤ k) :
    invWord (wordA w k)
      = ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
          (if k ≤ (w[i]!).ones ∧ (w[j]!).ones = k - 1 then 1 else 0) := by
  unfold wordA
  rw [invWord_map, pairSum_filter]
  unfold pairSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  -- Bool condition ⟺ Prop condition, under 1 ≤ k
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, not_le]
  apply propext
  omega

/-- The length of a list filter equals the sum of the indicator over the list. -/
lemma length_filter_eq_map_sum (l : List Row) (q : Row → Bool) :
    (l.filter q).length = (l.map (fun p => if q p then (1 : ℕ) else 0)).sum := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    by_cases hp : q p
    · rw [if_pos hp]
      simp only [hp, List.length_cons, ih, if_true]; ring
    · rw [if_neg hp, if_neg hp, ih, zero_add]

/-- A list's sum equals the sum of its indexed entries over `range`. -/
lemma list_sum_eq_range_sum (l : List ℕ) :
    l.sum = ∑ i ∈ Finset.range l.length, l[i]! := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
    rw [add_comm]

/-- **General double-counting identity.**  For a decidable predicate `P` on the
naturals, the product of the number of `i < n` with `P i` and the number with
`¬ P i` equals the count over ordered pairs `i < j < n` of "exactly one of
`P i`, `P j` holds". -/
lemma pair_count_general (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    ((Finset.range n).filter P).card * ((Finset.range n).filter (fun i => ¬ P i)).card
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.Ioo i n,
          ((if P i ∧ ¬ P j then 1 else 0) + (if ¬ P i ∧ P j then 1 else 0)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- Cardinalities over `range (n+1)`.
    have hnotmem : n ∉ Finset.range n := by simp
    have hcardP : ((Finset.range (n + 1)).filter P).card
        = (if P n then ((Finset.range n).filter P).card + 1
            else ((Finset.range n).filter P).card) := by
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hP : P n
      · rw [if_pos hP, if_pos hP, Finset.card_insert_of_notMem]
        simp only [Finset.mem_filter]; tauto
      · rw [if_neg hP, if_neg hP]
    have hcardNP : ((Finset.range (n + 1)).filter (fun i => ¬ P i)).card
        = (if P n then ((Finset.range n).filter (fun i => ¬ P i)).card
            else ((Finset.range n).filter (fun i => ¬ P i)).card + 1) := by
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hP : P n
      · rw [if_neg (by simpa using hP), if_pos hP]
      · rw [if_pos (by simpa using hP), if_neg hP, Finset.card_insert_of_notMem]
        simp only [Finset.mem_filter]; tauto
    -- Expand the RHS at `n+1`.
    have hRHS : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.Ioo i (n + 1),
          ((if P i ∧ ¬ P j then 1 else 0) + (if ¬ P i ∧ P j then 1 else 0)))
        = (∑ i ∈ Finset.range n,
            ((if P i ∧ ¬ P n then 1 else 0) + (if ¬ P i ∧ P n then 1 else 0)))
          + (∑ i ∈ Finset.range n, ∑ j ∈ Finset.Ioo i n,
              ((if P i ∧ ¬ P j then 1 else 0) + (if ¬ P i ∧ P j then 1 else 0))) := by
      rw [Finset.sum_range_succ]
      have hlast : Finset.Ioo n (n + 1) = (∅ : Finset ℕ) := by
        ext x; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]; omega
      rw [hlast, Finset.sum_empty, add_zero]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      have hins : Finset.Ioo i (n + 1) = insert n (Finset.Ioo i n) := by
        ext x; simp only [Finset.mem_Ioo, Finset.mem_insert]; omega
      have hnmem : n ∉ Finset.Ioo i n := by simp
      rw [hins, Finset.sum_insert hnmem, add_comm]
    -- The single-index sum equals a card, depending on `P n`.
    have hsingle : (∑ i ∈ Finset.range n,
          ((if P i ∧ ¬ P n then 1 else 0) + (if ¬ P i ∧ P n then 1 else 0)))
        = (if P n then ((Finset.range n).filter (fun i => ¬ P i)).card
            else ((Finset.range n).filter P).card) := by
      by_cases hP : P n
      · rw [if_pos hP]
        rw [Finset.card_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hPi : P i <;> simp [hPi, hP]
      · rw [if_neg hP]
        rw [Finset.card_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hPi : P i <;> simp [hPi, hP]
    rw [hcardP, hcardNP, hRHS, hsingle, ← ih]
    by_cases hP : P n
    · simp only [if_pos hP]; ring
    · simp only [if_neg hP]; ring

/-- **Pairwise decomposition of `a_k (s − a_k)` (RHS).**  For level `k`, writing
`a_k = countLevel w k` and `s = w.length`, the product counts the unordered pairs
`i < j` with exactly one of `u_i ≥ k`, `u_j ≥ k`. -/
lemma countLevel_pair_decomp (w : List Row) (k : ℕ) :
    countLevel w k * (w.length - countLevel w k)
      = ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
          ((if k ≤ (w[i]!).ones ∧ (w[j]!).ones < k then 1 else 0)
            + (if (w[i]!).ones < k ∧ k ≤ (w[j]!).ones then 1 else 0)) := by
  -- Set up the index predicate `P i := k ≤ (w[i]!).ones`.
  set P : ℕ → Prop := fun i => k ≤ (w[i]!).ones with hPdef
  -- Step 1: `countLevel w k = ((range w.length).filter P).card`.
  have hstep1 : countLevel w k = ((Finset.range w.length).filter P).card := by
    rw [countLevel, Finset.card_filter,
        length_filter_eq_map_sum w (fun p => decide (k ≤ p.ones)),
        list_sum_eq_range_sum (w.map (fun p => if decide (k ≤ p.ones) then (1 : ℕ) else 0)),
        List.length_map]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [getElem!_pos (w.map (fun p => if decide (k ≤ p.ones) then (1 : ℕ) else 0)) i
        (by rw [List.length_map]; exact hi), List.getElem_map]
    simp only [hPdef, decide_eq_true_eq]
    rw [getElem!_pos w i hi]
  -- Step 2: `w.length - countLevel w k = ((range w.length).filter (¬P)).card`.
  have hle : ((Finset.range w.length).filter P).card ≤ w.length := by
    have := Finset.card_filter_le (Finset.range w.length) P
    simpa using this
  have hstep2 : w.length - countLevel w k
      = ((Finset.range w.length).filter (fun i => ¬ P i)).card := by
    rw [hstep1]
    have hsplit : ((Finset.range w.length).filter P).card
        + ((Finset.range w.length).filter (fun i => ¬ P i)).card = w.length := by
      rw [Finset.card_filter_add_card_filter_not]
      simp
    omega
  rw [hstep2, hstep1]
  -- Rewrite the goal's `... < k` as `¬ P`.
  have hgoal : (∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
        ((if k ≤ (w[i]!).ones ∧ (w[j]!).ones < k then 1 else 0)
          + (if (w[i]!).ones < k ∧ k ≤ (w[j]!).ones then 1 else 0)))
      = ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
          ((if P i ∧ ¬ P j then 1 else 0) + (if ¬ P i ∧ P j then 1 else 0)) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    congr 1
    · congr 1; simp only [hPdef]; apply propext; omega
    · congr 1; simp only [hPdef]; apply propext; omega
  rw [hgoal]
  exact pair_count_general P w.length

/-- **Core combinatorial identity for `internal_a`.**  For any list of rows `w`
all of length `ℓ` (the s-block), the intra-block crossing count plus the
word-inversion statistic equals `Σ_{k=1}^ℓ a_k (s − a_k)` where
`a_k = countLevel w k` and `s = w.length`.  Proof route (see
`informal_internal_a.md`): decompose crossings, the `Ja` word-inversion sum, and
the RHS each into a sum over levels `k ∈ [1,ℓ]` and pairs `i < j`, then prove the
pointwise local identity `C + J = R` (a case bash on `u ≥ k`, `u' ≥ k`). -/
lemma internal_a_core {ℓ : ℕ} (w : List Row) (hw : ∀ p ∈ w, p.len = ℓ) :
    (intraSum w 0 w.length : ℤ)
        + ∑ k ∈ Finset.Icc 1 ℓ, (invWord (wordA w k) : ℤ)
      = ∑ k ∈ Finset.Icc 1 ℓ,
          (countLevel w k : ℤ) * ((w.length : ℤ) - (countLevel w k : ℤ)) := by
  -- Row lengths within `w`: each present index `i < w.length` has `w[i]!.len = ℓ`,
  -- hence `w[i]!.ones ≤ ℓ`.
  have hget_len : ∀ i, i < w.length → (w[i]!).len = ℓ := by
    intro i hi
    rw [getElem!_pos w i hi]
    exact hw _ (List.getElem_mem hi)
  have hones_le : ∀ i, i < w.length → (w[i]!).ones ≤ ℓ := by
    intro i hi
    have := hget_len i hi
    have := (w[i]!).ones_le
    omega
  -- Rewrite the LHS crossings-part as a double index sum, then per-level.
  have hintra : (intraSum w 0 w.length : ℤ)
      = ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
          ∑ k ∈ Finset.Icc 1 ℓ,
            ((if (w[i]!).ones < k ∧ k ≤ (w[j]!).ones then 1 else 0)
              + (if (w[j]!).ones + 1 < k ∧ k ≤ (w[i]!).ones then 1 else 0) : ℤ) := by
    rw [intraSum]
    push_cast
    rw [Finset.range_eq_Ico]  -- Ico 0 = range
    rw [← Finset.range_eq_Ico]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [Finset.mem_range] at hi
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [Finset.mem_Ioo] at hj
    rw [crossings_level_decomp (w[i]!) (w[j]!) (hget_len i hi) (hget_len j (by omega))]
    push_cast
    rfl
  -- Rewrite the LHS invWord-part per pair.  First push each invWord to its
  -- pairwise form, then swap the (finite, rectangular) `k`-sum outward-to-inward.
  have hJa : (∑ k ∈ Finset.Icc 1 ℓ, (invWord (wordA w k) : ℤ))
      = ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
          ∑ k ∈ Finset.Icc 1 ℓ,
            (if k ≤ (w[i]!).ones ∧ (w[j]!).ones = k - 1 then 1 else 0 : ℤ) := by
    have hstep : (∑ k ∈ Finset.Icc 1 ℓ, (invWord (wordA w k) : ℤ))
        = ∑ k ∈ Finset.Icc 1 ℓ, ∑ i ∈ Finset.range w.length,
            ∑ j ∈ Finset.Ioo i w.length,
              (if k ≤ (w[i]!).ones ∧ (w[j]!).ones = k - 1 then 1 else 0 : ℤ) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [Finset.mem_Icc] at hk
      rw [invWord_wordA_decomp w hw k hk.1]
      push_cast
      rfl
    rw [hstep, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.sum_comm]
  -- Rewrite the RHS per pair.
  have hRHS : (∑ k ∈ Finset.Icc 1 ℓ,
        (countLevel w k : ℤ) * ((w.length : ℤ) - (countLevel w k : ℤ)))
      = ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
          ∑ k ∈ Finset.Icc 1 ℓ,
            ((if k ≤ (w[i]!).ones ∧ (w[j]!).ones < k then 1 else 0)
              + (if (w[i]!).ones < k ∧ k ≤ (w[j]!).ones then 1 else 0) : ℤ) := by
    have hstep : (∑ k ∈ Finset.Icc 1 ℓ,
          (countLevel w k : ℤ) * ((w.length : ℤ) - (countLevel w k : ℤ)))
        = ∑ k ∈ Finset.Icc 1 ℓ, ∑ i ∈ Finset.range w.length,
            ∑ j ∈ Finset.Ioo i w.length,
              ((if k ≤ (w[i]!).ones ∧ (w[j]!).ones < k then 1 else 0)
                + (if (w[i]!).ones < k ∧ k ≤ (w[j]!).ones then 1 else 0) : ℤ) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have := countLevel_pair_decomp w k
      have hcast : ((countLevel w k * (w.length - countLevel w k) : ℕ) : ℤ)
          = ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
              ((if k ≤ (w[i]!).ones ∧ (w[j]!).ones < k then 1 else 0)
                + (if (w[i]!).ones < k ∧ k ≤ (w[j]!).ones then 1 else 0) : ℤ) := by
        rw [this]; push_cast; rfl
      -- LHS: need cast of the product; countLevel ≤ w.length.
      have hle : countLevel w k ≤ w.length := by
        rw [countLevel]; exact (List.length_filter_le _ _).trans (le_of_eq rfl)
      rw [← hcast]
      push_cast [Nat.cast_sub hle]
      ring
    rw [hstep, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.sum_comm]
  -- Combine and reduce to the LOCAL pointwise identity.
  rw [hintra, hJa, hRHS, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp only [Finset.mem_range] at hi
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp only [Finset.mem_Ioo] at hj
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_Icc] at hk
  -- LOCAL identity: case bash on (w[i]!).ones ≥ k, (w[j]!).ones ≥ k.
  -- All four indicators are 0/1; omega on the split of all `if`s.
  split_ifs <;> omega

/-- Internal s-block count (`eq:internal-a`): the intra-s-block crossings plus
`Ja` equal `Σ_i a_i (s − a_i)`.  NUMERICALLY CONFIRMED. -/
theorem internal_a
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (M : ℕ) (T : MultiTab) (hT : T ∈ TsetMinus r s M) :
    (intraSum T.flatten T.betaRows.length T.flatten.length : ℤ) + Ja ℓ T
      = ∑ i, (aOf (ℓ := ℓ) T i : ℤ) * ((s : ℤ) - (aOf (ℓ := ℓ) T i : ℤ)) := by
  -- Unpack membership: β-first order and s-block filling.
  obtain ⟨horder, hsw, _⟩ := mem_TsetMinus_unpack hT
  have hlenℓ : ∀ p ∈ T.sRows, p.len = ℓ := sBlock_all_len _ hsw
  have hscard : T.sRows.length = s := sBlock_length _ hsw
  -- flatten = betaRows ++ sRows, nb = betaRows.length, n = nb + sRows.length.
  have hfl : T.flatten = T.betaRows ++ T.sRows := by
    simp only [MultiTab.flatten, horder, if_true]
  have hn : T.flatten.length = T.betaRows.length + T.sRows.length := by
    rw [hfl, List.length_append]
  -- Bridge the flatten intra-sum onto the self-contained sRows intra-sum.
  have hbridge : intraSum T.flatten T.betaRows.length T.flatten.length
      = intraSum T.sRows 0 T.sRows.length := by
    have := intraSum_bridge T.betaRows T.sRows
    rw [hfl]
    simpa [List.length_append] using this
  -- Rewrite Ja and the RHS to the `internal_a_core` shape.
  -- Ja ℓ T = ∑_{k∈Icc 1 ℓ} invWord (wordA sRows k).
  have hJa : Ja ℓ T = ∑ k ∈ Finset.Icc 1 ℓ, (invWord (wordA T.sRows k) : ℤ) := rfl
  -- RHS: ∑ i, aOf i (s - aOf i) = ∑_{k∈Icc 1 ℓ} countLevel sRows k (sRows.length - countLevel sRows k)
  have hRHS : (∑ i, (aOf (ℓ := ℓ) T i : ℤ) * ((s : ℤ) - (aOf (ℓ := ℓ) T i : ℤ)))
      = ∑ k ∈ Finset.Icc 1 ℓ,
          (countLevel T.sRows k : ℤ) * ((T.sRows.length : ℤ) - (countLevel T.sRows k : ℤ)) := by
    rw [hscard]
    -- reindex Fin ℓ ↔ Icc 1 ℓ via k = i+1
    rw [Finset.sum_bij (fun (i : Fin ℓ) _ => (i : ℕ) + 1)]
    · intro i _; simp only [Finset.mem_Icc]; omega
    · intro i _ j _ h; exact Fin.ext (by omega)
    · intro k hk; simp only [Finset.mem_Icc] at hk
      refine ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, ?_⟩
      simp only [Fin.val_mk]; omega
    · intro i _; rfl
  rw [hbridge, hJa, hRHS]
  exact internal_a_core T.sRows hlenℓ

/-- Reindexing bridge (HEAD block): intra-block crossings over the head block `b`
of `b ++ w`, indexed in `[0, b.length)`, equal the self-contained intra-sum of
`b`.  (Head analogue of `intraSum_bridge`, easier since `(b++w)[i]! = b[i]!`.) -/
lemma intraSum_headbridge (b w : List Row) :
    intraSum (b ++ w) 0 b.length = intraSum b 0 b.length := by
  have hget : ∀ i, i < b.length → (b ++ w)[i]! = b[i]! := by
    intro i hi
    rw [getElem!_pos (b ++ w) i (by rw [List.length_append]; omega),
        getElem!_pos b i hi, List.getElem_append_left hi]
  unfold intraSum
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp only [Finset.mem_Ico] at hi
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp only [Finset.mem_Ioo] at hj
  rw [hget i (by omega), hget j (by omega)]

/-- **General level decomposition of `crossings` (varying lengths).**  For two
rows `p` (earlier) and `p'` (later) with lengths `≤ ℓ`, the crossing count equals
the sum over levels `k ∈ [1,ℓ]` of the local crossing indicator
`[u<k ∧ k≤u' ∧ k≤L] + [u'<k ∧ k+1≤u ∧ k≤L']` (`u=p.ones`, `u'=p'.ones`,
`L=p.len`, `L'=p'.len`).  NUMERICALLY CONFIRMED. -/
lemma crossings_level_decomp_gen {ℓ : ℕ} (p p' : Row)
    (hp : p.len ≤ ℓ) (hp' : p'.len ≤ ℓ) :
    crossings p p'
      = ∑ k ∈ Finset.Icc 1 ℓ,
          ((if p.ones < k ∧ k ≤ p'.ones ∧ k ≤ p.len then 1 else 0)
            + (if p'.ones < k ∧ k + 1 ≤ p.ones ∧ k ≤ p'.len then 1 else 0)) := by
  -- SANITY CHECK PASSED (numerically confirmed via parent internal_z #eval)
  have hpo : p.ones ≤ p.len := p.ones_le
  have hp'o : p'.ones ≤ p'.len := p'.ones_le
  rw [Finset.sum_add_distrib]
  unfold crossings cellIsOne cellIsTwo
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  congr 1
  · rw [Finset.sum_boole, Finset.sum_boole]
    have hL : ((Finset.Icc 1 (max p.len p'.len)).filter
          (fun c => (p.ones < c ∧ c ≤ p.len) ∧ (1 ≤ c ∧ c ≤ p'.ones)))
        = Finset.Icc (p.ones + 1) (min p.len p'.ones) := by
      ext c; simp only [Finset.mem_filter, Finset.mem_Icc, le_max_iff, le_min_iff]; omega
    have hR : ((Finset.Icc 1 ℓ).filter
          (fun c => p.ones < c ∧ c ≤ p'.ones ∧ c ≤ p.len))
        = Finset.Icc (p.ones + 1) (min p.len p'.ones) := by
      ext c; simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]; omega
    rw [hL, hR]
  · rw [Finset.sum_boole, Finset.sum_boole]
    have hL : ((Finset.Icc 1 (max p.len p'.len)).filter
          (fun c => (1 ≤ c + 1 ∧ c + 1 ≤ p.ones) ∧ (p'.ones < c ∧ c ≤ p'.len)))
        = Finset.Icc (p'.ones + 1) (min (p.ones - 1) p'.len) := by
      ext c; simp only [Finset.mem_filter, Finset.mem_Icc, le_max_iff, le_min_iff]; omega
    have hR : ((Finset.Icc 1 ℓ).filter
          (fun c => p'.ones < c ∧ c + 1 ≤ p.ones ∧ c ≤ p'.len))
        = Finset.Icc (p'.ones + 1) (min (p.ones - 1) p'.len) := by
      ext c; simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]; omega
    rw [hL, hR]

/-- **Structural reindexing of `invWord (wordZ betaRows k)` (JZ).**  The number of
`10` inversions of the level-`k` β-word equals the count over original index pairs
`i < j` of the presence + bit condition
`k ≤ L_i ∧ k ≤ L_j ∧ u_i = k ∧ u_j < k` (`u = ones`, `L = len`).  Uses the
order-preserving filter/map inversion machinery.  NUMERICALLY CONFIRMED. -/
lemma invWord_wordZ_decomp (w : List Row) (k : ℕ) (hk : 1 ≤ k) :
    invWord (wordZ w k)
      = ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
          (if k ≤ (w[i]!).len ∧ k ≤ (w[j]!).len ∧ (w[i]!).ones = k ∧ (w[j]!).ones < k
            then 1 else 0) := by
  unfold wordZ
  rw [invWord_map, pairSum_filter]
  unfold pairSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, not_le]
  apply propext
  omega

/-- **RHS double-count per level (β-block).**  For level `k`, writing
`z_k = countLevel w k` (β-rows reaching level `k` in ones) and
`r_k = (w.filter (k ≤ ·.len)).length` (β-rows long enough for level `k`), the
product `z_k (r_k − z_k)` counts the unordered pairs `i < j` with both rows long
enough and exactly one reaching level `k`.  NUMERICALLY CONFIRMED. -/
lemma countLevel_pair_decomp_z (w : List Row) (k : ℕ) :
    countLevel w k * ((w.filter (fun p => k ≤ p.len)).length - countLevel w k)
      = ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
          ((if k ≤ (w[i]!).len ∧ k ≤ (w[j]!).len ∧
              k ≤ (w[i]!).ones ∧ (w[j]!).ones < k then 1 else 0)
            + (if k ≤ (w[i]!).len ∧ k ≤ (w[j]!).len ∧
              (w[i]!).ones < k ∧ k ≤ (w[j]!).ones then 1 else 0)) := by
  -- Work over the length-gated list `w'`.
  set f : Row → Bool := fun p => decide (k ≤ p.len) with hf
  set w' : List Row := w.filter f with hw'
  -- Index predicate on `w'`.
  set P : ℕ → Prop := fun i => k ≤ (w'[i]!).ones with hPdef
  -- `countLevel w k = countLevel w' k`, because `k ≤ ones → k ≤ len`.
  have hcount_eq : countLevel w k = countLevel w' k := by
    unfold countLevel
    rw [hw']
    -- (w.filter f).filter (k≤·.ones) = w.filter (k≤·.ones)
    rw [List.filter_filter]
    apply congrArg
    apply List.filter_congr
    intro p _
    have hle := p.ones_le
    simp only [hf]
    by_cases ho : k ≤ p.ones
    · have hlen : k ≤ p.len := le_trans ho hle
      simp [ho, hlen]
    · simp [ho]
  -- `countLevel w' k = ((range w'.length).filter P).card`.
  have hstep1 : countLevel w' k = ((Finset.range w'.length).filter P).card := by
    rw [countLevel, Finset.card_filter,
        length_filter_eq_map_sum w' (fun p => decide (k ≤ p.ones)),
        list_sum_eq_range_sum (w'.map (fun p => if decide (k ≤ p.ones) then (1 : ℕ) else 0)),
        List.length_map]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [getElem!_pos (w'.map (fun p => if decide (k ≤ p.ones) then (1 : ℕ) else 0)) i
        (by rw [List.length_map]; exact hi), List.getElem_map]
    simp only [hPdef, decide_eq_true_eq]
    rw [getElem!_pos w' i hi]
  -- `w'.length - card_P = card_¬P`.
  have hneg : w'.length - ((Finset.range w'.length).filter P).card
      = ((Finset.range w'.length).filter (fun i => ¬ P i)).card := by
    have hsplit : ((Finset.range w'.length).filter P).card
        + ((Finset.range w'.length).filter (fun i => ¬ P i)).card = w'.length := by
      rw [Finset.card_filter_add_card_filter_not]
      simp
    omega
  -- LHS product = pair_count over `w'`.
  -- Note `w'.length = (w.filter (k≤·.len)).length` definitionally (`hw'`).
  have hwlen : (w.filter (fun p => k ≤ p.len)).length = w'.length := by rw [hw']
  rw [hcount_eq, hstep1, hwlen, hneg]
  rw [pair_count_general P w'.length]
  -- Now: pair-count over `w'`  =  gated pair-sum over `w`.
  -- Split the RHS into two `pairSum`s and both sides via `pairSum_filter`.
  -- LHS (pair_count RHS) as two pairSums over w'.
  have hLHS : (∑ i ∈ Finset.range w'.length, ∑ j ∈ Finset.Ioo i w'.length,
        ((if P i ∧ ¬ P j then 1 else 0) + (if ¬ P i ∧ P j then 1 else 0)))
      = pairSum w' (fun a b => decide (k ≤ a.ones) && !decide (k ≤ b.ones))
        + pairSum w' (fun a b => !decide (k ≤ a.ones) && decide (k ≤ b.ones)) := by
    unfold pairSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    · congr 1
      simp only [hPdef, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
        decide_eq_false_iff_not, not_le]
    · congr 1
      simp only [hPdef, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
        decide_eq_false_iff_not, not_le]
  rw [hLHS]
  -- Convert each pairSum over w' = pairSum (w.filter f) to pairSum over w.
  rw [hw']
  rw [pairSum_filter w f (fun a b => decide (k ≤ a.ones) && !decide (k ≤ b.ones))]
  rw [pairSum_filter w f (fun a b => !decide (k ≤ a.ones) && decide (k ≤ b.ones))]
  -- Now both sides are pair-sums over w; match the indicators.
  unfold pairSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  -- match: (f a && f b && (P'a && ¬P'b)) ↔ (k≤L_i ∧ k≤L_j ∧ k≤u_i ∧ u_j<k), etc.
  congr 1
  · congr 1
    simp only [hf, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not, not_le]
    apply propext; omega
  · congr 1
    simp only [hf, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not, not_le]
    apply propext; omega

/-- **Core combinatorial identity for `internal_z`.**  For any list of β-block
rows `w` (all lengths `≤ ℓ`), the intra-block crossing count plus the `Jz`
word-inversion statistic equals `Σ_{k=1}^ℓ z_k (r_k − z_k)`, where
`z_k = countLevel w k` and `r_k = (w.filter (k ≤ ·.len)).length`.  Proof route
(see `informal_iz.md`): decompose crossings, the `Jz` inversion sum, and the RHS
each into a sum over levels `k∈[1,ℓ]` and pairs `i<j`, then prove the pointwise
local identity `C + W = R` (case bash on `u ≥ k`, `u' ≥ k`, gated by length). -/
lemma internal_z_core {ℓ : ℕ} (w : List Row) (hw : ∀ p ∈ w, p.len ≤ ℓ) :
    (intraSum w 0 w.length : ℤ)
        + ∑ k ∈ Finset.Icc 1 ℓ, (invWord (wordZ w k) : ℤ)
      = ∑ k ∈ Finset.Icc 1 ℓ,
          (countLevel w k : ℤ) *
            (((w.filter (fun p => k ≤ p.len)).length : ℤ) - (countLevel w k : ℤ)) := by
  -- Row lengths within `w`: each present index `i < w.length` has `w[i]!.len ≤ ℓ`,
  -- and `w[i]!.ones ≤ w[i]!.len`.
  have hget_len : ∀ i, i < w.length → (w[i]!).len ≤ ℓ := by
    intro i hi
    rw [getElem!_pos w i hi]
    exact hw _ (List.getElem_mem hi)
  have hones_le : ∀ i, i < w.length → (w[i]!).ones ≤ (w[i]!).len := by
    intro i _; exact (w[i]!).ones_le
  -- Rewrite the LHS crossings-part as a double index sum, then per-level.
  have hintra : (intraSum w 0 w.length : ℤ)
      = ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
          ∑ k ∈ Finset.Icc 1 ℓ,
            ((if (w[i]!).ones < k ∧ k ≤ (w[j]!).ones ∧ k ≤ (w[i]!).len then 1 else 0)
              + (if (w[j]!).ones < k ∧ k + 1 ≤ (w[i]!).ones ∧ k ≤ (w[j]!).len
                  then 1 else 0) : ℤ) := by
    rw [intraSum]
    push_cast
    rw [Finset.range_eq_Ico]
    rw [← Finset.range_eq_Ico]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [Finset.mem_range] at hi
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [Finset.mem_Ioo] at hj
    rw [crossings_level_decomp_gen (w[i]!) (w[j]!) (hget_len i hi) (hget_len j (by omega))]
    push_cast
    rfl
  -- Rewrite the LHS invWord-part per pair via `invWord_wordZ_decomp`.
  have hJz : (∑ k ∈ Finset.Icc 1 ℓ, (invWord (wordZ w k) : ℤ))
      = ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
          ∑ k ∈ Finset.Icc 1 ℓ,
            (if k ≤ (w[i]!).len ∧ k ≤ (w[j]!).len ∧
                (w[i]!).ones = k ∧ (w[j]!).ones < k then 1 else 0 : ℤ) := by
    have hstep : (∑ k ∈ Finset.Icc 1 ℓ, (invWord (wordZ w k) : ℤ))
        = ∑ k ∈ Finset.Icc 1 ℓ, ∑ i ∈ Finset.range w.length,
            ∑ j ∈ Finset.Ioo i w.length,
              (if k ≤ (w[i]!).len ∧ k ≤ (w[j]!).len ∧
                  (w[i]!).ones = k ∧ (w[j]!).ones < k then 1 else 0 : ℤ) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [Finset.mem_Icc] at hk
      rw [invWord_wordZ_decomp w k hk.1]
      push_cast
      rfl
    rw [hstep, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.sum_comm]
  -- Rewrite the RHS per pair via `countLevel_pair_decomp_z`.
  have hRHS : (∑ k ∈ Finset.Icc 1 ℓ,
        (countLevel w k : ℤ) *
          (((w.filter (fun p => k ≤ p.len)).length : ℤ) - (countLevel w k : ℤ)))
      = ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
          ∑ k ∈ Finset.Icc 1 ℓ,
            ((if k ≤ (w[i]!).len ∧ k ≤ (w[j]!).len ∧
                k ≤ (w[i]!).ones ∧ (w[j]!).ones < k then 1 else 0)
              + (if k ≤ (w[i]!).len ∧ k ≤ (w[j]!).len ∧
                (w[i]!).ones < k ∧ k ≤ (w[j]!).ones then 1 else 0) : ℤ) := by
    have hstep : (∑ k ∈ Finset.Icc 1 ℓ,
          (countLevel w k : ℤ) *
            (((w.filter (fun p => k ≤ p.len)).length : ℤ) - (countLevel w k : ℤ)))
        = ∑ k ∈ Finset.Icc 1 ℓ, ∑ i ∈ Finset.range w.length,
            ∑ j ∈ Finset.Ioo i w.length,
              ((if k ≤ (w[i]!).len ∧ k ≤ (w[j]!).len ∧
                  k ≤ (w[i]!).ones ∧ (w[j]!).ones < k then 1 else 0)
                + (if k ≤ (w[i]!).len ∧ k ≤ (w[j]!).len ∧
                  (w[i]!).ones < k ∧ k ≤ (w[j]!).ones then 1 else 0) : ℤ) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hpd := countLevel_pair_decomp_z w k
      have hcast : ((countLevel w k *
            ((w.filter (fun p => k ≤ p.len)).length - countLevel w k) : ℕ) : ℤ)
          = ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
              ((if k ≤ (w[i]!).len ∧ k ≤ (w[j]!).len ∧
                  k ≤ (w[i]!).ones ∧ (w[j]!).ones < k then 1 else 0)
                + (if k ≤ (w[i]!).len ∧ k ≤ (w[j]!).len ∧
                  (w[i]!).ones < k ∧ k ≤ (w[j]!).ones then 1 else 0) : ℤ) := by
        rw [hpd]; push_cast; rfl
      have hle : countLevel w k ≤ (w.filter (fun p => k ≤ p.len)).length := by
        unfold countLevel
        have : w.filter (fun p => k ≤ p.ones)
            = (w.filter (fun p => k ≤ p.len)).filter (fun p => k ≤ p.ones) := by
          rw [List.filter_filter]
          apply List.filter_congr
          intro p _
          by_cases ho : k ≤ p.ones
          · have hlen : k ≤ p.len := le_trans ho p.ones_le
            simp [ho, hlen]
          · simp [ho]
        rw [this]
        exact List.length_filter_le _ _
      rw [← hcast]
      push_cast [Nat.cast_sub hle]
      ring
    rw [hstep, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.sum_comm]
  -- Combine and reduce to the LOCAL pointwise identity.
  rw [hintra, hJz, hRHS, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp only [Finset.mem_range] at hi
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp only [Finset.mem_Ioo] at hj
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_Icc] at hk
  have hui := hones_le i (by omega)
  have huj := hones_le j (by omega)
  -- LOCAL identity: case bash on the length/ones inequalities.
  split_ifs <;> omega

/-- **Conjugate-partition arithmetic.**  With `r` nonincreasing and
`1 ≤ k ≤ ℓ`, the number of parts of `betaParts r` that are `≥ k` equals the
`k`-th largest value `r ⟨k-1⟩`.  Concretely `betaParts r = (range R).map (c ↦
#{i : c+1 ≤ r i})`, so the count is `#{c < R : k ≤ #{i : c+1 ≤ r i}}`.  Since `r`
is sorted nonincreasingly, `#{i : c+1 ≤ r i} ≥ k ↔ c+1 ≤ r ⟨k-1⟩`, hence the
count is `min R (r ⟨k-1⟩) = r ⟨k-1⟩` (as `r ⟨k-1⟩ ≤ R = sup r`). -/
lemma betaParts_filter_count {ℓ : ℕ} (r : Fin ℓ → ℕ)
    (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i) (k : ℕ) (hk1 : 1 ≤ k) (hkℓ : k ≤ ℓ) :
    ((betaParts r).filter (fun L => k ≤ L)).length = r ⟨k - 1, by omega⟩ := by
  have hℓ : 0 < ℓ := by omega
  set κ : Fin ℓ := ⟨k - 1, by omega⟩ with hκ
  -- Unfold betaParts and simplify `if 0 < ℓ` to `R := Finset.univ.sup r`.
  set R : ℕ := Finset.univ.sup r with hR
  have hbeta : betaParts r
      = (List.range R).map (fun c => (Finset.univ.filter (fun i => c + 1 ≤ r i)).card) := by
    unfold betaParts
    simp only [hℓ, if_true, hR]
  rw [hbeta, List.filter_map, List.length_map]
  -- KEY monotone-count iff: for m, (k ≤ #{i : m ≤ r i}) ↔ m ≤ r κ.
  have hkey : ∀ m : ℕ,
      (k ≤ (Finset.univ.filter (fun i : Fin ℓ => m ≤ r i)).card) ↔ m ≤ r κ := by
    intro m
    constructor
    · -- (⇐ direction of goal): assume count ≥ k, show m ≤ r κ.
      intro hcount
      by_contra hlt
      push_neg at hlt  -- r κ < m
      -- filter (m ≤ r ·) ⊆ Iio κ (indices < κ), which has card ≤ k-1 < k.
      have hsub : (Finset.univ.filter (fun i : Fin ℓ => m ≤ r i)) ⊆ Finset.Iio κ := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [Finset.mem_Iio]
        -- if κ ≤ i then r i ≤ r κ < m ≤ r i, contradiction; so i < κ.
        by_contra hle
        push_neg at hle  -- κ ≤ i
        have := hr κ i hle
        omega
      have hcard := Finset.card_le_card hsub
      rw [Fin.card_Iio] at hcard
      simp only [hκ, Fin.val_mk] at hcard
      omega
    · -- assume m ≤ r κ, show count ≥ k.
      intro hle
      -- Iic κ ⊆ filter (m ≤ r ·), and card (Iic κ) = k.
      have hsub : Finset.Iic κ ⊆ (Finset.univ.filter (fun i : Fin ℓ => m ≤ r i)) := by
        intro i hi
        simp only [Finset.mem_Iic] at hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := hr i κ hi
        omega
      have hcard := Finset.card_le_card hsub
      rw [Fin.card_Iic] at hcard
      simp only [hκ, Fin.val_mk] at hcard
      omega
  -- Rewrite the range-filter predicate via hkey (with m := c+1).
  have hfiltcongr :
      List.filter ((fun L => decide (k ≤ L)) ∘
          (fun c => (Finset.univ.filter (fun i => c + 1 ≤ r i)).card)) (List.range R)
      = (List.range R).filter (fun c => decide (c < r κ)) := by
    apply List.filter_congr
    intro c _
    simp only [Function.comp_apply]
    rw [decide_eq_decide]
    constructor
    · intro h; have := (hkey (c + 1)).1 h; omega
    · intro h; exact (hkey (c + 1)).2 (by omega)
  rw [hfiltcongr]
  -- Finish: length of (range R).filter (· < r κ) with r κ ≤ R.
  have hle : r κ ≤ R := by
    rw [hR]; exact Finset.le_sup (Finset.mem_univ κ)
  -- length of filter (· < t) over range R = min t R = t.
  have hlen : ((List.range R).filter (fun c => decide (c < r κ))).length = min R (r κ) := by
    rw [← List.Ico.zero_bot R, List.Ico.filter_lt, List.Ico.length]
    omega
  rw [hlen]
  omega

/-- The count of β-rows long enough for level `k` (`1 ≤ k ≤ ℓ`) equals the `k`-th
largest part `r ⟨k-1⟩` of `r` (which is nonincreasing): the conjugate-partition
relation `#{ parts of betaParts r that are ≥ k } = r_k`.  NUMERICALLY CONFIRMED. -/
lemma betaLenCount {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (w : List Row) (hw : w ∈ fillings (betaParts r)) (k : ℕ) (hk1 : 1 ≤ k)
    (hkℓ : k ≤ ℓ) :
    (w.filter (fun p => k ≤ p.len)).length = r ⟨k - 1, by omega⟩ := by
  -- SANITY CHECK PASSED (NUMERICALLY CONFIRMED, per docstring & META).
  -- Step 1: reduce the filter over rows to a filter over `betaParts r` (the
  -- length list), using `w.map Row.len = betaParts r`.
  have hmap : w.map Row.len = betaParts r := mem_fillings_map_len _ w hw
  have hred : (w.filter (fun p => k ≤ p.len)).length
      = ((betaParts r).filter (fun L => k ≤ L)).length := by
    rw [← hmap]
    rw [List.filter_map, List.length_map]
    rfl
  rw [hred]
  -- Step 2: the conjugate-partition arithmetic identity.
  -- betaParts_filter_count : #{ c ∈ range R : k ≤ #{i : c+1 ≤ r i} } = r ⟨k-1⟩.
  exact betaParts_filter_count r hr k hk1 hkℓ

/-- Internal β-block count (`eq:internal-z`): the intra-β-block crossings plus
`Jz` equal `Σ_i z_i (r_i − z_i)`.  NUMERICALLY CONFIRMED. -/
theorem internal_z
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (M : ℕ) (T : MultiTab) (hT : T ∈ TsetMinus r s M) :
    (intraSum T.flatten 0 T.betaRows.length : ℤ) + Jz ℓ T
      = ∑ i, (zOf (ℓ := ℓ) T i : ℤ) * ((r i : ℤ) - (zOf (ℓ := ℓ) T i : ℤ)) := by
  -- Unpack membership: β-first order, β-block filling.
  obtain ⟨horder, _, hbw⟩ := mem_TsetMinus_unpack hT
  have hfl : T.flatten = T.betaRows ++ T.sRows := by
    simp only [MultiTab.flatten, horder, if_true]
  -- All β-rows have length ≤ ℓ.
  have hlenℓ : ∀ p ∈ T.betaRows, p.len ≤ ℓ := by
    intro p hp
    have := mem_fillings_mem_len _ _ hbw p hp
    simp only [betaParts, List.mem_map, List.mem_range] at this
    obtain ⟨c, hc, hcard⟩ := this
    rw [← hcard]
    exact (Finset.card_filter_le _ _).trans (by simp)
  -- Head-block bridge: intra-β over flatten = self-contained intra-β.
  have hbridge : intraSum T.flatten 0 T.betaRows.length
      = intraSum T.betaRows 0 T.betaRows.length := by
    rw [hfl]; exact intraSum_headbridge T.betaRows T.sRows
  -- Jz as an Icc-sum.
  have hJz : Jz ℓ T = ∑ k ∈ Finset.Icc 1 ℓ, (invWord (wordZ T.betaRows k) : ℤ) := rfl
  -- Rewrite the RHS: r i = #{β-rows with len ≥ i+1}, zOf = countLevel.
  have hRHS : (∑ i, (zOf (ℓ := ℓ) T i : ℤ) * ((r i : ℤ) - (zOf (ℓ := ℓ) T i : ℤ)))
      = ∑ k ∈ Finset.Icc 1 ℓ,
          (countLevel T.betaRows k : ℤ) *
            (((T.betaRows.filter (fun p => k ≤ p.len)).length : ℤ)
              - (countLevel T.betaRows k : ℤ)) := by
    rw [Finset.sum_bij (fun (i : Fin ℓ) _ => (i : ℕ) + 1)]
    · intro i _; simp only [Finset.mem_Icc]; omega
    · intro i _ j _ h; exact Fin.ext (by omega)
    · intro k hk; simp only [Finset.mem_Icc] at hk
      refine ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, ?_⟩
      simp only [Fin.val_mk]; omega
    · intro i _
      have hz : zOf (ℓ := ℓ) T i = countLevel T.betaRows ((i : ℕ) + 1) := rfl
      have hrc : (T.betaRows.filter (fun p => (i : ℕ) + 1 ≤ p.len)).length = r i := by
        rw [betaLenCount r hr T.betaRows hbw ((i : ℕ) + 1) (by omega) (by omega)]
        congr 1
      rw [hz, hrc]
  rw [hbridge, hJz, hRHS]
  exact internal_z_core T.betaRows hlenℓ

/-- Count over `range l.length` of an indicator equals the filtered length. -/
lemma count_filter_range (l : List Row) (Q : Row → Bool) :
    (∑ i ∈ Finset.range l.length, (if Q l[i]! then (1 : ℕ) else 0))
      = (l.filter Q).length := by
  rw [length_filter_eq_map_sum l Q,
      list_sum_eq_range_sum (l.map (fun p => if Q p then (1 : ℕ) else 0)),
      List.length_map]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [getElem!_pos (l.map (fun p => if Q p then (1 : ℕ) else 0)) i
      (by rw [List.length_map]; exact hi), List.getElem_map, getElem!_pos l i hi]

/-- **Rectangular product-count.**  Summing an indicator `Q bs[i] ∧ R ss[j]` over
all pairs `(i,j)` with `i < bs.length`, `j < ss.length` gives the product of the
filtered lengths. -/
lemma rect_count (bs ss : List Row) (Q R : Row → Bool) :
    (∑ i ∈ Finset.range bs.length, ∑ j ∈ Finset.range ss.length,
        (if Q bs[i]! ∧ R ss[j]! then (1 : ℕ) else 0))
      = (bs.filter Q).length * (ss.filter R).length := by
  rw [← count_filter_range bs Q, ← count_filter_range ss R, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [ite_and]
  split_ifs <;> ring

/-- Bridge: `crossSum (bs ++ ss)` over the block boundary equals the rectangular
double sum of `crossings` between `bs`-rows (earlier block) and `ss`-rows. -/
lemma crossSum_append (bs ss : List Row) :
    crossSum (bs ++ ss) bs.length (bs.length + ss.length)
      = ∑ i ∈ Finset.range bs.length, ∑ j ∈ Finset.range ss.length,
          crossings bs[i]! ss[j]! := by
  set nb := bs.length with hnb
  unfold crossSum
  have hgetb : ∀ i, i < nb → (bs ++ ss)[i]! = bs[i]! := by
    intro i hi
    rw [getElem!_pos (bs ++ ss) i (by rw [List.length_append]; omega),
        getElem!_pos bs i (by omega), List.getElem_append_left hi]
  have hgets : ∀ j, j < ss.length → (bs ++ ss)[nb + j]! = ss[j]! := by
    intro j hj
    rw [getElem!_pos (bs ++ ss) (nb + j) (by rw [List.length_append]; omega),
        getElem!_pos ss j hj, List.getElem_append_right (by omega)]
    congr 1; omega
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  -- reindex inner sum from Ico nb (nb+ss.length) to range ss.length
  refine Finset.sum_nbij' (i := fun x => x - nb) (j := fun x => x + nb) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_Ico] at hj; simp only [Finset.mem_range]; omega
  · intro j hj; simp only [Finset.mem_range] at hj; simp only [Finset.mem_Ico]; omega
  · intro j hj; simp only [Finset.mem_Ico] at hj; omega
  · intro j hj; simp only [Finset.mem_range] at hj; omega
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    rw [hgetb i hi, ← hgets (j - nb) (by omega)]
    congr 2; omega

/-- A list's length splits into the two complementary filter lengths. -/
lemma length_filter_add_not (l : List Row) (q : Row → Bool) :
    (l.filter q).length + (l.filter (fun x => !q x)).length = l.length := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    simp only [List.filter_cons]
    by_cases hp : q p
    · rw [if_pos hp, if_neg (by simp [hp])]
      simp only [List.length_cons]; omega
    · rw [if_neg hp, if_pos (by simp [hp])]
      simp only [List.length_cons]; omega

/-- **Core cross-block identity.**  For a β-block list `bs` (all lengths `≤ ℓ`)
and an s-block list `ss` (all lengths `= ℓ`), the cross-block crossing count has
the per-level closed form
`Σ_{k=1}^ℓ [ (rc_k − z_k)·a_k + z_{k+1}·(s − a_k) ]`,
where `rc_k = #{β-rows: len ≥ k}`, `z_k = countLevel bs k`, `a_k = countLevel ss k`,
`s = ss.length`.  NUMERICALLY CONFIRMED. -/
lemma cross_minus_core {ℓ : ℕ} (bs ss : List Row)
    (hbs : ∀ p ∈ bs, p.len ≤ ℓ) (hss : ∀ p ∈ ss, p.len = ℓ) :
    (crossSum (bs ++ ss) bs.length (bs.length + ss.length) : ℤ)
      = ∑ k ∈ Finset.Icc 1 ℓ,
          (((((bs.filter (fun p => k ≤ p.len)).length : ℤ)
              - (countLevel bs k : ℤ)) * (countLevel ss k : ℤ))
            + (countLevel bs (k + 1) : ℤ)
                * ((ss.length : ℤ) - (countLevel ss k : ℤ))) := by
  -- Lengths within the lists.
  have hb_len : ∀ i, i < bs.length → (bs[i]!).len ≤ ℓ := by
    intro i hi; rw [getElem!_pos bs i hi]; exact hbs _ (List.getElem_mem hi)
  have hs_len : ∀ j, j < ss.length → (ss[j]!).len = ℓ := by
    intro j hj; rw [getElem!_pos ss j hj]; exact hss _ (List.getElem_mem hj)
  -- Step 1: crossSum → rectangular double-sum of crossings.
  rw [crossSum_append bs ss]
  push_cast
  -- Step 2: per-pair level decomposition.
  have hpair : (∑ i ∈ Finset.range bs.length, ∑ j ∈ Finset.range ss.length,
        (crossings bs[i]! ss[j]! : ℤ))
      = ∑ i ∈ Finset.range bs.length, ∑ j ∈ Finset.range ss.length,
          ∑ k ∈ Finset.Icc 1 ℓ,
            (((if (bs[i]!).ones < k ∧ k ≤ (ss[j]!).ones ∧ k ≤ (bs[i]!).len
                then 1 else 0)
              + (if (ss[j]!).ones < k ∧ k + 1 ≤ (bs[i]!).ones ∧ k ≤ (ss[j]!).len
                then 1 else 0)) : ℤ) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [Finset.mem_range] at hi
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [Finset.mem_range] at hj
    rw [crossings_level_decomp_gen (bs[i]!) (ss[j]!) (hb_len i hi)
        (le_of_eq (hs_len j hj))]
    push_cast; rfl
  rw [hpair]
  -- Step 3: swap to level-first order (∑i∑j∑k → ∑k∑i∑j).
  rw [Finset.sum_comm_cycle]
  -- Step 4: per level, split the sum of the two indicators and apply rect_count.
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_Icc] at hk
  -- Split the inner (i,j) double-sum into the two indicator sums.
  have hsplit : (∑ i ∈ Finset.range bs.length, ∑ j ∈ Finset.range ss.length,
        (((if (bs[i]!).ones < k ∧ k ≤ (ss[j]!).ones ∧ k ≤ (bs[i]!).len
            then 1 else 0)
          + (if (ss[j]!).ones < k ∧ k + 1 ≤ (bs[i]!).ones ∧ k ≤ (ss[j]!).len
            then 1 else 0)) : ℤ))
      = (∑ i ∈ Finset.range bs.length, ∑ j ∈ Finset.range ss.length,
          ((if (bs[i]!).ones < k ∧ k ≤ (ss[j]!).ones ∧ k ≤ (bs[i]!).len
            then 1 else 0) : ℤ))
        + (∑ i ∈ Finset.range bs.length, ∑ j ∈ Finset.range ss.length,
            ((if (ss[j]!).ones < k ∧ k + 1 ≤ (bs[i]!).ones ∧ k ≤ (ss[j]!).len
              then 1 else 0) : ℤ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
  rw [hsplit]
  -- TermA rectangle: Q = (ones<k ∧ k≤len), R = (k≤ones).
  have htermA : (∑ i ∈ Finset.range bs.length, ∑ j ∈ Finset.range ss.length,
        ((if (bs[i]!).ones < k ∧ k ≤ (ss[j]!).ones ∧ k ≤ (bs[i]!).len
          then 1 else 0) : ℤ))
      = (((bs.filter (fun p => k ≤ p.len)).length : ℤ) - (countLevel bs k : ℤ))
          * (countLevel ss k : ℤ) := by
    -- Recast the indicator to `Q bs[i]! ∧ R ss[j]!`.
    have hrw : (∑ i ∈ Finset.range bs.length, ∑ j ∈ Finset.range ss.length,
          ((if (bs[i]!).ones < k ∧ k ≤ (ss[j]!).ones ∧ k ≤ (bs[i]!).len
            then 1 else 0) : ℤ))
        = ((∑ i ∈ Finset.range bs.length, ∑ j ∈ Finset.range ss.length,
              (if (fun p => decide (p.ones < k ∧ k ≤ p.len)) bs[i]!
                  ∧ (fun p => decide (k ≤ p.ones)) ss[j]! then (1 : ℕ) else 0) : ℕ) : ℤ) := by
      push_cast
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      simp only [decide_eq_true_eq]
      apply propext
      exact ⟨fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩, fun h => ⟨h.1.1, h.2, h.1.2⟩⟩
    rw [hrw, rect_count bs ss (fun p => decide (p.ones < k ∧ k ≤ p.len))
        (fun p => decide (k ≤ p.ones))]
    push_cast
    -- (bs.filter Q).length = rc_k − z_k ; (ss.filter R).length = a_k.
    have hbfilt : ((bs.filter (fun p => decide (p.ones < k ∧ k ≤ p.len))).length : ℤ)
        = ((bs.filter (fun p => k ≤ p.len)).length : ℤ) - (countLevel bs k : ℤ) := by
      -- {ones<k ∧ k≤len} = {k≤len} \ {k≤ones}, disjointly.
      have hcard : (bs.filter (fun p => decide (p.ones < k ∧ k ≤ p.len))).length
          + (bs.filter (fun p => k ≤ p.ones)).length
          = (bs.filter (fun p => k ≤ p.len)).length := by
        -- both are sublists of bs.filter (k≤len) partitioning it
        have h1 : bs.filter (fun p => decide (p.ones < k ∧ k ≤ p.len))
            = (bs.filter (fun p => k ≤ p.len)).filter (fun p => decide (p.ones < k)) := by
          rw [List.filter_filter]
          apply List.filter_congr; intro p _
          by_cases ho : p.ones < k <;> by_cases hl : k ≤ p.len <;>
            simp [ho, hl] <;> try omega
        have h2 : bs.filter (fun p => k ≤ p.ones)
            = (bs.filter (fun p => k ≤ p.len)).filter
                (fun p => !decide (p.ones < k)) := by
          rw [List.filter_filter]
          apply List.filter_congr; intro p _
          have hle := p.ones_le
          by_cases ho : p.ones < k <;> by_cases hl : k ≤ p.len <;>
            simp [ho, hl] <;> omega
        rw [h1, h2]
        exact length_filter_add_not (bs.filter (fun p => k ≤ p.len))
          (fun p => decide (p.ones < k))
      rw [countLevel]
      have := hcard
      push_cast
      omega
    have hsfilt : ((ss.filter (fun p => decide (k ≤ p.ones))).length : ℤ)
        = (countLevel ss k : ℤ) := by
      rw [countLevel]
    rw [hbfilt, hsfilt]
  -- TermB rectangle: Q' = (k+1≤ones), R' = (ones<k) [since k≤ss.len always].
  have htermB : (∑ i ∈ Finset.range bs.length, ∑ j ∈ Finset.range ss.length,
        ((if (ss[j]!).ones < k ∧ k + 1 ≤ (bs[i]!).ones ∧ k ≤ (ss[j]!).len
          then 1 else 0) : ℤ))
      = (countLevel bs (k + 1) : ℤ) * ((ss.length : ℤ) - (countLevel ss k : ℤ)) := by
    have hrw : (∑ i ∈ Finset.range bs.length, ∑ j ∈ Finset.range ss.length,
          ((if (ss[j]!).ones < k ∧ k + 1 ≤ (bs[i]!).ones ∧ k ≤ (ss[j]!).len
            then 1 else 0) : ℤ))
        = ((∑ i ∈ Finset.range bs.length, ∑ j ∈ Finset.range ss.length,
              (if (fun p => decide (k + 1 ≤ p.ones)) bs[i]!
                  ∧ (fun p => decide (p.ones < k)) ss[j]! then (1 : ℕ) else 0) : ℕ) : ℤ) := by
      push_cast
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [Finset.mem_range] at hj
      congr 1
      simp only [decide_eq_true_eq]
      have hsl : k ≤ (ss[j]!).len := (hs_len j hj).symm ▸ hk.2
      apply propext
      exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, hsl⟩⟩
    rw [hrw, rect_count bs ss (fun p => decide (k + 1 ≤ p.ones))
        (fun p => decide (p.ones < k))]
    push_cast
    have hbfilt : ((bs.filter (fun p => decide (k + 1 ≤ p.ones))).length : ℤ)
        = (countLevel bs (k + 1) : ℤ) := by
      rw [countLevel]
    have hsfilt : ((ss.filter (fun p => decide (p.ones < k))).length : ℤ)
        = (ss.length : ℤ) - (countLevel ss k : ℤ) := by
      have hcard : (ss.filter (fun p => decide (p.ones < k))).length
          + (ss.filter (fun p => k ≤ p.ones)).length = ss.length := by
        have hbase := length_filter_add_not ss (fun p => decide (p.ones < k))
        have heq : ss.filter (fun p => !decide (p.ones < k))
            = ss.filter (fun p => k ≤ p.ones) := by
          apply List.filter_congr; intro p _
          by_cases ho : p.ones < k <;> simp [ho] <;> omega
        rw [heq] at hbase; exact hbase
      rw [countLevel]; push_cast; omega
    rw [hbfilt, hsfilt]
  rw [htermA, htermB]

/-- Cross-block count (β-first) closed form.  NUMERICALLY CONFIRMED:
`C⁻ = s·Σz − Σ(a_i z_i) − Σ(z_i·a_{i-1}) + Σ(r_i a_i)`. -/
theorem cross_minus
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (M : ℕ) (T : MultiTab) (hT : T ∈ TsetMinus r s M) :
    (crossSum T.flatten T.betaRows.length T.flatten.length : ℤ)
      = (s : ℤ) * (∑ i, (zOf (ℓ := ℓ) T i : ℤ))
        - (∑ i, (aOf (ℓ := ℓ) T i : ℤ) * (zOf (ℓ := ℓ) T i : ℤ))
        - (∑ i, (zOf (ℓ := ℓ) T i : ℤ) * (shiftPrev s (aOf (ℓ := ℓ) T) i : ℤ))
        + (∑ i, (r i : ℤ) * (aOf (ℓ := ℓ) T i : ℤ)) := by
  -- Unpack membership: β-first order, β/s fillings.
  obtain ⟨horder, hsf, hbf⟩ := mem_TsetMinus_unpack hT
  have hfl : T.flatten = T.betaRows ++ T.sRows := by
    simp only [MultiTab.flatten, horder, if_true]
  have hss : ∀ p ∈ T.sRows, p.len = ℓ := sBlock_all_len _ hsf
  have hslen : T.sRows.length = s := sBlock_length _ hsf
  have hbs : ∀ p ∈ T.betaRows, p.len ≤ ℓ := by
    intro p hp
    have := mem_fillings_mem_len _ _ hbf p hp
    simp only [betaParts, List.mem_map, List.mem_range] at this
    obtain ⟨c, hc, hcard⟩ := this
    rw [← hcard]
    exact (Finset.card_filter_le _ _).trans (by simp)
  -- Rewrite crossSum via the core lemma.
  have hcs : (crossSum T.flatten T.betaRows.length T.flatten.length : ℤ)
      = ∑ k ∈ Finset.Icc 1 ℓ,
          (((((T.betaRows.filter (fun p => k ≤ p.len)).length : ℤ)
              - (countLevel T.betaRows k : ℤ)) * (countLevel T.sRows k : ℤ))
            + (countLevel T.betaRows (k + 1) : ℤ)
                * ((T.sRows.length : ℤ) - (countLevel T.sRows k : ℤ))) := by
    have hnn : T.flatten.length = T.betaRows.length + T.sRows.length := by
      rw [hfl, List.length_append]
    rw [hnn, hfl]
    exact cross_minus_core T.betaRows T.sRows hbs hss
  rw [hcs]
  -- Boundary vanishing: no β-row has ones ≥ ℓ+1, so countLevel betaRows (ℓ+1) = 0.
  have hzℓ1 : countLevel T.betaRows (ℓ + 1) = 0 := by
    rw [countLevel, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro p hp
    have hpl := hbs p hp
    have hpo := p.ones_le
    simp only [decide_eq_true_eq]
    omega
  -- Convert the Icc-sum to a Fin ℓ sum, substituting the closed forms.
  have hLHS : (∑ k ∈ Finset.Icc 1 ℓ,
          (((((T.betaRows.filter (fun p => k ≤ p.len)).length : ℤ)
              - (countLevel T.betaRows k : ℤ)) * (countLevel T.sRows k : ℤ))
            + (countLevel T.betaRows (k + 1) : ℤ)
                * ((T.sRows.length : ℤ) - (countLevel T.sRows k : ℤ))))
      = ∑ i : Fin ℓ,
          ((((r i : ℤ) - (zOf (ℓ := ℓ) T i : ℤ)) * (aOf (ℓ := ℓ) T i : ℤ))
            + (countLevel T.betaRows ((i : ℕ) + 2) : ℤ)
                * ((s : ℤ) - (aOf (ℓ := ℓ) T i : ℤ))) := by
    rw [Finset.sum_bij (fun (i : Fin ℓ) _ => (i : ℕ) + 1)]
    · intro i _; simp only [Finset.mem_Icc]; omega
    · intro i _ j _ h; exact Fin.ext (by omega)
    · intro k hk; simp only [Finset.mem_Icc] at hk
      refine ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, ?_⟩
      simp only [Fin.val_mk]; omega
    · intro i _
      have hrc : (T.betaRows.filter (fun p => (i : ℕ) + 1 ≤ p.len)).length = r i := by
        rw [betaLenCount r hr T.betaRows hbf ((i : ℕ) + 1) (by omega) (by omega)]
        congr 1
      have hz : countLevel T.betaRows ((i : ℕ) + 1) = zOf (ℓ := ℓ) T i := rfl
      have ha : countLevel T.sRows ((i : ℕ) + 1) = aOf (ℓ := ℓ) T i := rfl
      have hnext : (i : ℕ) + 1 + 1 = (i : ℕ) + 2 := by ring
      rw [hrc, hz, ha, hslen, hnext]
  rw [hLHS]
  -- Reduce to A-part (term-by-term) + B-part (reindex).
  have hAsplit : (∑ i : Fin ℓ,
        ((((r i : ℤ) - (zOf (ℓ := ℓ) T i : ℤ)) * (aOf (ℓ := ℓ) T i : ℤ))
          + (countLevel T.betaRows ((i : ℕ) + 2) : ℤ)
              * ((s : ℤ) - (aOf (ℓ := ℓ) T i : ℤ))))
      = (∑ i : Fin ℓ, ((r i : ℤ) - (zOf (ℓ := ℓ) T i : ℤ)) * (aOf (ℓ := ℓ) T i : ℤ))
        + (∑ i : Fin ℓ, (countLevel T.betaRows ((i : ℕ) + 2) : ℤ)
              * ((s : ℤ) - (aOf (ℓ := ℓ) T i : ℤ))) := by
    rw [← Finset.sum_add_distrib]
  rw [hAsplit]
  -- A-part matches Σ r·a − Σ a·z after distributing.
  have hA : (∑ i : Fin ℓ, ((r i : ℤ) - (zOf (ℓ := ℓ) T i : ℤ)) * (aOf (ℓ := ℓ) T i : ℤ))
      = (∑ i, (r i : ℤ) * (aOf (ℓ := ℓ) T i : ℤ))
        - (∑ i, (aOf (ℓ := ℓ) T i : ℤ) * (zOf (ℓ := ℓ) T i : ℤ)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  -- B-part reindex: Σ_i cLb(i+2)·(s−a_i) = s·Σz − Σz·â.
  have hB : (∑ i : Fin ℓ, (countLevel T.betaRows ((i : ℕ) + 2) : ℤ)
              * ((s : ℤ) - (aOf (ℓ := ℓ) T i : ℤ)))
      = (s : ℤ) * (∑ i, (zOf (ℓ := ℓ) T i : ℤ))
        - (∑ i, (zOf (ℓ := ℓ) T i : ℤ) * (shiftPrev s (aOf (ℓ := ℓ) T) i : ℤ)) := by
    -- RHS = Σ_i z_i·(s − â_i).
    have hRHS : (s : ℤ) * (∑ i, (zOf (ℓ := ℓ) T i : ℤ))
        - (∑ i, (zOf (ℓ := ℓ) T i : ℤ) * (shiftPrev s (aOf (ℓ := ℓ) T) i : ℤ))
        = ∑ i : Fin ℓ, (zOf (ℓ := ℓ) T i : ℤ)
            * ((s : ℤ) - (shiftPrev s (aOf (ℓ := ℓ) T) i : ℤ)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hRHS]
    -- Both sides are Fin ℓ sums; term i on the left uses cLb(i+2)=z_{i+1}
    -- (or 0 at i=ℓ-1), on the right z_i·(s−â_i) (0 at i=0).  Shift bijection.
    -- ℕ-valued term functions.
    let F : ℕ → ℤ := fun k =>
      (countLevel T.betaRows (k + 2) : ℤ)
        * ((s : ℤ) - (countLevel T.sRows (k + 1) : ℤ))
    let G : ℕ → ℤ := fun k =>
      (countLevel T.betaRows (k + 1) : ℤ)
        * ((s : ℤ) - (if k = 0 then (s : ℤ) else (countLevel T.sRows k : ℤ)))
    -- Rewrite LHS as ∑ i:Fin ℓ, F ↑i.
    have hLF : (∑ i : Fin ℓ, (countLevel T.betaRows ((i : ℕ) + 2) : ℤ)
            * ((s : ℤ) - (aOf (ℓ := ℓ) T i : ℤ)))
        = ∑ i : Fin ℓ, F (i : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      have ha' : aOf (ℓ := ℓ) T i = countLevel T.sRows ((i : ℕ) + 1) := rfl
      simp only [F, ha']
    -- Rewrite RHS as ∑ i:Fin ℓ, G ↑i.
    have hRG : (∑ i : Fin ℓ, (zOf (ℓ := ℓ) T i : ℤ)
            * ((s : ℤ) - (shiftPrev s (aOf (ℓ := ℓ) T) i : ℤ)))
        = ∑ i : Fin ℓ, G (i : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      have hz' : zOf (ℓ := ℓ) T i = countLevel T.betaRows ((i : ℕ) + 1) := rfl
      have hsp : shiftPrev s (aOf (ℓ := ℓ) T) i
          = (if (i : ℕ) = 0 then s else countLevel T.sRows (i : ℕ)) := by
        unfold shiftPrev
        by_cases h0 : (i : ℕ) = 0
        · simp [h0]
        · rw [if_neg h0, if_neg h0]
          have ha' : aOf (ℓ := ℓ) T ⟨(i : ℕ) - 1, by omega⟩
              = countLevel T.sRows (((i : ℕ) - 1) + 1) := rfl
          rw [ha']
          congr 1
          omega
      simp only [G, hz', hsp]
      by_cases h0 : (i : ℕ) = 0
      · simp [h0]
      · simp [h0]
    rw [hLF, hRG]
    rw [Fin.sum_univ_eq_sum_range F ℓ, Fin.sum_univ_eq_sum_range G ℓ]
    -- Peel: LHS last term (k=ℓ-1) uses cLb(ℓ+1)=0; RHS first term (k=0) uses s-s=0.
    obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, by omega⟩
    rw [Finset.sum_range_succ F n, Finset.sum_range_succ' G n]
    have hFn : F n = 0 := by
      have hz0 : countLevel T.betaRows (n + 2) = 0 := by
        have he : n + 2 = (n + 1) + 1 := by ring
        rw [he]; exact hzℓ1
      simp only [F, hz0, Nat.cast_zero, zero_mul]
    have hG0 : G 0 = 0 := by simp [G]
    rw [hFn, hG0, add_zero, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    have hk1 : ¬ (k + 1 = 0) := by omega
    simp only [F, G, hk1, if_false]
  rw [hA, hB]; ring

/-- **Statement 1 (inversion decomposition, minus sign — `eq:inv-Eminus`).**
For every multitableau `T` of shape `μ` in the **beta-block-first** order, writing
`a = aOf T`, `z = zOf T` and `M = Σ_i (a_i + z_i)`:
```
s·M − inv(T) = Jₐ(T) + J_z(T) + E⁻(aOf T, zOf T).
```
This is the section 3.4 computation forced by Schilling's single-row inversion
rule (concretely `invMT`) together with the internal- and cross-block counts. -/
theorem inv_decomposition_minus
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (hbw : BinaryWordGauss)
    (M : ℕ) (T : MultiTab) (hT : T ∈ TsetMinus r s M) :
    (s : ℤ) * (∑ i, (aOf (ℓ := ℓ) T i + zOf (ℓ := ℓ) T i) : ℕ) - (invMT T : ℤ)
      = Ja ℓ T + Jz ℓ T + Eminus r s (aOf (ℓ := ℓ) T) (zOf (ℓ := ℓ) T) := by
  -- Combine the four numerically-confirmed sub-lemmas.  With
  --   invMT = intraZ + cross + intraA,
  --   intraA + Ja = Σ a_i(s−a_i),  intraZ + Jz = Σ z_i(r_i−z_i),
  --   cross = s·Σz − Σ(a_i z_i) − Σ(z_i·a_{i-1}) + Σ(r_i a_i),
  -- the algebra collapses to  s·M − invMT = Ja + Jz + E⁻,  where
  --   E⁻ = Σ (a_i² + z_i² + a_i z_i + z_i·a_{i-1} − r_i(a_i + z_i)).
  have hsplit := invMT_split_minus r s M T hT
  have ha := internal_a r s hℓ hr M T hT
  have hz := internal_z r s hℓ hr M T hT
  have hc := cross_minus r s hℓ hr M T hT
  have hsum : (s : ℤ) * (∑ i, (aOf (ℓ := ℓ) T i + zOf (ℓ := ℓ) T i) : ℕ)
      = (s : ℤ) * (∑ i, (aOf (ℓ := ℓ) T i : ℤ)) + (s : ℤ) * (∑ i, (zOf (ℓ := ℓ) T i : ℤ)) := by
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  -- Expand E⁻ and cast invMT via the split.
  rw [Eminus, hsum]
  have hinv : (invMT T : ℤ)
      = (intraSum T.flatten 0 T.betaRows.length : ℤ)
        + (crossSum T.flatten T.betaRows.length T.flatten.length : ℤ)
        + (intraSum T.flatten T.betaRows.length T.flatten.length : ℤ) := by
    rw [hsplit]; push_cast; ring
  rw [hinv]
  -- Now everything is in ℤ.  Substitute ha, hz, hc and finish with sum algebra.
  -- Abbreviate the six per-index sums and prove the ℤ identity via a single
  -- combined-sum congruence, then `linarith`.
  have hEsum : Eminus r s (aOf (ℓ := ℓ) T) (zOf (ℓ := ℓ) T)
      = ∑ j, ((aOf (ℓ := ℓ) T j : ℤ) ^ 2 + (zOf (ℓ := ℓ) T j : ℤ) ^ 2
        + (aOf (ℓ := ℓ) T j : ℤ) * (zOf (ℓ := ℓ) T j : ℤ)
        + (zOf (ℓ := ℓ) T j : ℤ) * (shiftPrev s (aOf (ℓ := ℓ) T) j : ℤ)
        - (r j : ℤ) * ((aOf (ℓ := ℓ) T j : ℤ) + (zOf (ℓ := ℓ) T j : ℤ))) := rfl
  -- Turn each sum-of-products into a combined single sum so `linarith` can use them.
  have haE : (∑ i, (aOf (ℓ := ℓ) T i : ℤ) * ((s : ℤ) - (aOf (ℓ := ℓ) T i : ℤ)))
      = (s : ℤ) * (∑ i, (aOf (ℓ := ℓ) T i : ℤ)) - (∑ i, (aOf (ℓ := ℓ) T i : ℤ) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hzE : (∑ i, (zOf (ℓ := ℓ) T i : ℤ) * ((r i : ℤ) - (zOf (ℓ := ℓ) T i : ℤ)))
      = (∑ i, (r i : ℤ) * (zOf (ℓ := ℓ) T i : ℤ)) - (∑ i, (zOf (ℓ := ℓ) T i : ℤ) ^ 2) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  -- Split E⁻ into the six named component sums.
  have hEexp : (∑ j, ((aOf (ℓ := ℓ) T j : ℤ) ^ 2 + (zOf (ℓ := ℓ) T j : ℤ) ^ 2
        + (aOf (ℓ := ℓ) T j : ℤ) * (zOf (ℓ := ℓ) T j : ℤ)
        + (zOf (ℓ := ℓ) T j : ℤ) * (shiftPrev s (aOf (ℓ := ℓ) T) j : ℤ)
        - (r j : ℤ) * ((aOf (ℓ := ℓ) T j : ℤ) + (zOf (ℓ := ℓ) T j : ℤ))))
      = (∑ i, (aOf (ℓ := ℓ) T i : ℤ) ^ 2)
        + (∑ i, (zOf (ℓ := ℓ) T i : ℤ) ^ 2)
        + (∑ i, (aOf (ℓ := ℓ) T i : ℤ) * (zOf (ℓ := ℓ) T i : ℤ))
        + (∑ i, (zOf (ℓ := ℓ) T i : ℤ) * (shiftPrev s (aOf (ℓ := ℓ) T) i : ℤ))
        - (∑ i, (r i : ℤ) * (aOf (ℓ := ℓ) T i : ℤ))
        - (∑ i, (r i : ℤ) * (zOf (ℓ := ℓ) T i : ℤ)) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [haE] at ha
  rw [hzE] at hz
  rw [hEexp]
  linarith [ha, hz, hc]

/-! ### Plus-side (s-block-first) sub-lemmas, mirroring the minus side. -/

/-- Membership in `TsetPlus` unpacks to s-first order, an s-block filling, and a
β-block filling. -/
lemma mem_TsetPlus_unpack {ℓ : ℕ} {r : Fin ℓ → ℕ} {s M : ℕ} {T : MultiTab}
    (hT : T ∈ TsetPlus r s M) :
    T.order = false ∧ T.sRows ∈ fillings (sBlockLens ℓ s) ∧
      T.betaRows ∈ fillings (betaParts r) := by
  simp only [TsetPlus, TsetOrder, Finset.mem_filter, Finset.mem_image,
    Finset.mem_product] at hT
  obtain ⟨⟨⟨b, w⟩, ⟨hb, hw⟩, hTeq⟩, _⟩ := hT
  subst hTeq
  exact ⟨rfl, hw, hb⟩

/-- Split of `invMT` for the s-block-first order (`ns = sRows.length`). -/
theorem invMT_split_plus
    (M : ℕ) (T : MultiTab) (hT : T ∈ TsetPlus r s M) :
    invMT T
      = intraSum T.flatten 0 T.sRows.length
        + crossSum T.flatten T.sRows.length T.flatten.length
        + intraSum T.flatten T.sRows.length T.flatten.length := by
  have hlen : T.sRows.length ≤ T.flatten.length := by
    simp only [MultiTab.flatten]
    split <;> simp [List.length_append]
  simpa only [invMT, intraSum, crossSum] using
    sum_Ioo_split (fun i j => crossings T.flatten[i]! T.flatten[j]!)
      T.sRows.length T.flatten.length hlen

/-- Internal-block count for the s-block (HEAD block in s-first order). -/
theorem internal_a_plus
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (M : ℕ) (T : MultiTab) (hT : T ∈ TsetPlus r s M) :
    (intraSum T.flatten 0 T.sRows.length : ℤ) + Ja ℓ T
      = ∑ i, (aOf (ℓ := ℓ) T i : ℤ) * ((s : ℤ) - (aOf (ℓ := ℓ) T i : ℤ)) := by
  obtain ⟨horder, hsw, _⟩ := mem_TsetPlus_unpack hT
  have hlenℓ : ∀ p ∈ T.sRows, p.len = ℓ := sBlock_all_len _ hsw
  have hscard : T.sRows.length = s := sBlock_length _ hsw
  have hfl : T.flatten = T.sRows ++ T.betaRows := by
    unfold MultiTab.flatten; rw [horder]; rfl
  -- Head-block bridge: intra-s over flatten = self-contained intra-s.
  have hbridge : intraSum T.flatten 0 T.sRows.length
      = intraSum T.sRows 0 T.sRows.length := by
    rw [hfl]; exact intraSum_headbridge T.sRows T.betaRows
  have hJa : Ja ℓ T = ∑ k ∈ Finset.Icc 1 ℓ, (invWord (wordA T.sRows k) : ℤ) := rfl
  have hRHS : (∑ i, (aOf (ℓ := ℓ) T i : ℤ) * ((s : ℤ) - (aOf (ℓ := ℓ) T i : ℤ)))
      = ∑ k ∈ Finset.Icc 1 ℓ,
          (countLevel T.sRows k : ℤ) * ((T.sRows.length : ℤ) - (countLevel T.sRows k : ℤ)) := by
    rw [hscard]
    rw [Finset.sum_bij (fun (i : Fin ℓ) _ => (i : ℕ) + 1)]
    · intro i _; simp only [Finset.mem_Icc]; omega
    · intro i _ j _ h; exact Fin.ext (by omega)
    · intro k hk; simp only [Finset.mem_Icc] at hk
      refine ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, ?_⟩
      simp only [Fin.val_mk]; omega
    · intro i _; rfl
  rw [hbridge, hJa, hRHS]
  exact internal_a_core T.sRows hlenℓ

/-- Internal-block count for the β-block (TAIL block in s-first order). -/
theorem internal_z_plus
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (M : ℕ) (T : MultiTab) (hT : T ∈ TsetPlus r s M) :
    (intraSum T.flatten T.sRows.length T.flatten.length : ℤ) + Jz ℓ T
      = ∑ i, (zOf (ℓ := ℓ) T i : ℤ) * ((r i : ℤ) - (zOf (ℓ := ℓ) T i : ℤ)) := by
  obtain ⟨horder, hsw, hbfill⟩ := mem_TsetPlus_unpack hT
  have hfl : T.flatten = T.sRows ++ T.betaRows := by
    unfold MultiTab.flatten; rw [horder]; rfl
  have hlenℓ : ∀ p ∈ T.betaRows, p.len ≤ ℓ := by
    intro p hp
    have := mem_fillings_mem_len _ _ hbfill p hp
    simp only [betaParts, List.mem_map, List.mem_range] at this
    obtain ⟨c, hc, hcard⟩ := this
    rw [← hcard]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hn : T.flatten.length = T.sRows.length + T.betaRows.length := by
    rw [hfl, List.length_append]
  -- Tail-block bridge: intra-β over flatten = self-contained intra-β.
  have hbridge : intraSum T.flatten T.sRows.length T.flatten.length
      = intraSum T.betaRows 0 T.betaRows.length := by
    have hb := intraSum_bridge T.sRows T.betaRows
    rw [hfl]
    have : (T.sRows ++ T.betaRows).length = T.sRows.length + T.betaRows.length := by
      rw [List.length_append]
    rw [this]; exact hb
  have hJz : Jz ℓ T = ∑ k ∈ Finset.Icc 1 ℓ, (invWord (wordZ T.betaRows k) : ℤ) := rfl
  have hRHS : (∑ i, (zOf (ℓ := ℓ) T i : ℤ) * ((r i : ℤ) - (zOf (ℓ := ℓ) T i : ℤ)))
      = ∑ k ∈ Finset.Icc 1 ℓ,
          (countLevel T.betaRows k : ℤ)
            * (((T.betaRows.filter (fun p => k ≤ p.len)).length : ℤ)
              - (countLevel T.betaRows k : ℤ)) := by
    rw [Finset.sum_bij (fun (i : Fin ℓ) _ => (i : ℕ) + 1)]
    · intro i _; simp only [Finset.mem_Icc]; omega
    · intro i _ j _ h; exact Fin.ext (by omega)
    · intro k hk; simp only [Finset.mem_Icc] at hk
      refine ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, ?_⟩
      simp only [Fin.val_mk]; omega
    · intro i _
      have hz : countLevel T.betaRows ((i : ℕ) + 1) = zOf (ℓ := ℓ) T i := rfl
      have hrc : (T.betaRows.filter (fun p => (i : ℕ) + 1 ≤ p.len)).length = r i := by
        rw [betaLenCount r hr T.betaRows hbfill ((i : ℕ) + 1) (by omega) (by omega)]
        congr 1
      rw [hz, hrc]
  rw [hbridge, hJz, hRHS]
  exact internal_z_core T.betaRows hlenℓ

/-- **Core combinatorial identity for the plus cross-block.**  For head rows `ss`
all of length `ℓ` (the s-block, earlier) and tail rows `bs` of length `≤ ℓ` (the
β-block, later): closed form of the cross-block crossing count.  Mirror of
`cross_minus_core` with head/tail roles swapped. -/
lemma cross_plus_core {ℓ : ℕ} (ss bs : List Row)
    (hss : ∀ p ∈ ss, p.len = ℓ) (hbs : ∀ p ∈ bs, p.len ≤ ℓ) :
    (crossSum (ss ++ bs) ss.length (ss.length + bs.length) : ℤ)
      = ∑ k ∈ Finset.Icc 1 ℓ,
          (((ss.length : ℤ) - (countLevel ss k : ℤ)) * (countLevel bs k : ℤ)
            + (countLevel ss (k + 1) : ℤ)
                * (((bs.filter (fun p => k ≤ p.len)).length : ℤ)
                  - (countLevel bs k : ℤ))) := by
  -- Lengths within the lists.
  have hs_len : ∀ i, i < ss.length → (ss[i]!).len = ℓ := by
    intro i hi; rw [getElem!_pos ss i hi]; exact hss _ (List.getElem_mem hi)
  have hb_len : ∀ j, j < bs.length → (bs[j]!).len ≤ ℓ := by
    intro j hj; rw [getElem!_pos bs j hj]; exact hbs _ (List.getElem_mem hj)
  -- Step 1: crossSum → rectangular double-sum of crossings.
  rw [crossSum_append ss bs]
  push_cast
  -- Step 2: per-pair level decomposition.
  have hpair : (∑ i ∈ Finset.range ss.length, ∑ j ∈ Finset.range bs.length,
        (crossings ss[i]! bs[j]! : ℤ))
      = ∑ i ∈ Finset.range ss.length, ∑ j ∈ Finset.range bs.length,
          ∑ k ∈ Finset.Icc 1 ℓ,
            (((if (ss[i]!).ones < k ∧ k ≤ (bs[j]!).ones ∧ k ≤ (ss[i]!).len
                then 1 else 0)
              + (if (bs[j]!).ones < k ∧ k + 1 ≤ (ss[i]!).ones ∧ k ≤ (bs[j]!).len
                then 1 else 0)) : ℤ) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [Finset.mem_range] at hi
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [Finset.mem_range] at hj
    rw [crossings_level_decomp_gen (ss[i]!) (bs[j]!) (le_of_eq (hs_len i hi))
        (hb_len j hj)]
    push_cast; rfl
  rw [hpair]
  -- Step 3: swap to level-first order (∑i∑j∑k → ∑k∑i∑j).
  rw [Finset.sum_comm_cycle]
  -- Step 4: per level, split the sum of the two indicators and apply rect_count.
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_Icc] at hk
  have hsplit : (∑ i ∈ Finset.range ss.length, ∑ j ∈ Finset.range bs.length,
        (((if (ss[i]!).ones < k ∧ k ≤ (bs[j]!).ones ∧ k ≤ (ss[i]!).len
            then 1 else 0)
          + (if (bs[j]!).ones < k ∧ k + 1 ≤ (ss[i]!).ones ∧ k ≤ (bs[j]!).len
            then 1 else 0)) : ℤ))
      = (∑ i ∈ Finset.range ss.length, ∑ j ∈ Finset.range bs.length,
          ((if (ss[i]!).ones < k ∧ k ≤ (bs[j]!).ones ∧ k ≤ (ss[i]!).len
            then 1 else 0) : ℤ))
        + (∑ i ∈ Finset.range ss.length, ∑ j ∈ Finset.range bs.length,
            ((if (bs[j]!).ones < k ∧ k + 1 ≤ (ss[i]!).ones ∧ k ≤ (bs[j]!).len
              then 1 else 0) : ℤ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
  rw [hsplit]
  -- TermA rectangle: Q on ss[i] = (ones<k) [k≤len auto], R on bs[j] = (k≤ones).
  have htermA : (∑ i ∈ Finset.range ss.length, ∑ j ∈ Finset.range bs.length,
        ((if (ss[i]!).ones < k ∧ k ≤ (bs[j]!).ones ∧ k ≤ (ss[i]!).len
          then 1 else 0) : ℤ))
      = ((ss.length : ℤ) - (countLevel ss k : ℤ)) * (countLevel bs k : ℤ) := by
    have hrw : (∑ i ∈ Finset.range ss.length, ∑ j ∈ Finset.range bs.length,
          ((if (ss[i]!).ones < k ∧ k ≤ (bs[j]!).ones ∧ k ≤ (ss[i]!).len
            then 1 else 0) : ℤ))
        = ((∑ i ∈ Finset.range ss.length, ∑ j ∈ Finset.range bs.length,
              (if (fun p => decide (p.ones < k)) ss[i]!
                  ∧ (fun p => decide (k ≤ p.ones)) bs[j]! then (1 : ℕ) else 0) : ℕ) : ℤ) := by
      push_cast
      refine Finset.sum_congr rfl (fun i hi => ?_)
      simp only [Finset.mem_range] at hi
      refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      simp only [decide_eq_true_eq]
      have hsl : k ≤ (ss[i]!).len := (hs_len i hi).symm ▸ hk.2
      apply propext
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hsl⟩⟩
    rw [hrw, rect_count ss bs (fun p => decide (p.ones < k))
        (fun p => decide (k ≤ p.ones))]
    push_cast
    have hsfilt : ((ss.filter (fun p => decide (p.ones < k))).length : ℤ)
        = (ss.length : ℤ) - (countLevel ss k : ℤ) := by
      have hcard : (ss.filter (fun p => decide (p.ones < k))).length
          + (ss.filter (fun p => k ≤ p.ones)).length = ss.length := by
        have hbase := length_filter_add_not ss (fun p => decide (p.ones < k))
        have heq : ss.filter (fun p => !decide (p.ones < k))
            = ss.filter (fun p => k ≤ p.ones) := by
          apply List.filter_congr; intro p _
          by_cases ho : p.ones < k <;> simp [ho] <;> omega
        rw [heq] at hbase; exact hbase
      rw [countLevel]; push_cast; omega
    have hbfilt : ((bs.filter (fun p => decide (k ≤ p.ones))).length : ℤ)
        = (countLevel bs k : ℤ) := by
      rw [countLevel]
    rw [hsfilt, hbfilt]
  -- TermB rectangle: Q on ss[i] = (k+1≤ones), R on bs[j] = (ones<k ∧ k≤len).
  have htermB : (∑ i ∈ Finset.range ss.length, ∑ j ∈ Finset.range bs.length,
        ((if (bs[j]!).ones < k ∧ k + 1 ≤ (ss[i]!).ones ∧ k ≤ (bs[j]!).len
          then 1 else 0) : ℤ))
      = (countLevel ss (k + 1) : ℤ)
          * (((bs.filter (fun p => k ≤ p.len)).length : ℤ) - (countLevel bs k : ℤ)) := by
    have hrw : (∑ i ∈ Finset.range ss.length, ∑ j ∈ Finset.range bs.length,
          ((if (bs[j]!).ones < k ∧ k + 1 ≤ (ss[i]!).ones ∧ k ≤ (bs[j]!).len
            then 1 else 0) : ℤ))
        = ((∑ i ∈ Finset.range ss.length, ∑ j ∈ Finset.range bs.length,
              (if (fun p => decide (k + 1 ≤ p.ones)) ss[i]!
                  ∧ (fun p => decide (p.ones < k ∧ k ≤ p.len)) bs[j]! then (1 : ℕ) else 0) : ℕ) : ℤ) := by
      push_cast
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      simp only [decide_eq_true_eq]
      apply propext
      exact ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩
    rw [hrw, rect_count ss bs (fun p => decide (k + 1 ≤ p.ones))
        (fun p => decide (p.ones < k ∧ k ≤ p.len))]
    push_cast
    have hsfilt : ((ss.filter (fun p => decide (k + 1 ≤ p.ones))).length : ℤ)
        = (countLevel ss (k + 1) : ℤ) := by
      rw [countLevel]
    have hbfilt : ((bs.filter (fun p => decide (p.ones < k ∧ k ≤ p.len))).length : ℤ)
        = ((bs.filter (fun p => k ≤ p.len)).length : ℤ) - (countLevel bs k : ℤ) := by
      have hcard : (bs.filter (fun p => decide (p.ones < k ∧ k ≤ p.len))).length
          + (bs.filter (fun p => k ≤ p.ones)).length
          = (bs.filter (fun p => k ≤ p.len)).length := by
        have h1 : bs.filter (fun p => decide (p.ones < k ∧ k ≤ p.len))
            = (bs.filter (fun p => k ≤ p.len)).filter (fun p => decide (p.ones < k)) := by
          rw [List.filter_filter]
          apply List.filter_congr; intro p _
          by_cases ho : p.ones < k <;> by_cases hl : k ≤ p.len <;>
            simp [ho, hl] <;> try omega
        have h2 : bs.filter (fun p => k ≤ p.ones)
            = (bs.filter (fun p => k ≤ p.len)).filter
                (fun p => !decide (p.ones < k)) := by
          rw [List.filter_filter]
          apply List.filter_congr; intro p _
          have hle := p.ones_le
          by_cases ho : p.ones < k <;> by_cases hl : k ≤ p.len <;>
            simp [ho, hl] <;> omega
        rw [h1, h2]
        exact length_filter_add_not (bs.filter (fun p => k ≤ p.len))
          (fun p => decide (p.ones < k))
      rw [countLevel]
      have := hcard
      push_cast
      omega
    rw [hsfilt, hbfilt]
  rw [htermA, htermB]

/-- Cross-block count (s-first) closed form.  NUMERICALLY CONFIRMED:
`C⁺ = s·Σz − Σ(a_i z_i) + Σ(r_i·â_i) − Σ(z_i·â_i)`, `â = shiftNext a`. -/
theorem cross_plus
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (M : ℕ) (T : MultiTab) (hT : T ∈ TsetPlus r s M) :
    (crossSum T.flatten T.sRows.length T.flatten.length : ℤ)
      = (s : ℤ) * (∑ i, (zOf (ℓ := ℓ) T i : ℤ))
        - (∑ i, (aOf (ℓ := ℓ) T i : ℤ) * (zOf (ℓ := ℓ) T i : ℤ))
        + (∑ i, (r i : ℤ) * (shiftNext (aOf (ℓ := ℓ) T) i : ℤ))
        - (∑ i, (zOf (ℓ := ℓ) T i : ℤ) * (shiftNext (aOf (ℓ := ℓ) T) i : ℤ)) := by
  -- Unpack membership: s-first order, β/s fillings.
  obtain ⟨horder, hsf, hbf⟩ := mem_TsetPlus_unpack hT
  have hfl : T.flatten = T.sRows ++ T.betaRows := by
    simp only [MultiTab.flatten, horder]; rfl
  have hss : ∀ p ∈ T.sRows, p.len = ℓ := sBlock_all_len _ hsf
  have hslen : T.sRows.length = s := sBlock_length _ hsf
  have hbs : ∀ p ∈ T.betaRows, p.len ≤ ℓ := by
    intro p hp
    have := mem_fillings_mem_len _ _ hbf p hp
    simp only [betaParts, List.mem_map, List.mem_range] at this
    obtain ⟨c, hc, hcard⟩ := this
    rw [← hcard]
    exact (Finset.card_filter_le _ _).trans (by simp)
  -- Rewrite crossSum via the core lemma.
  have hcs : (crossSum T.flatten T.sRows.length T.flatten.length : ℤ)
      = ∑ k ∈ Finset.Icc 1 ℓ,
          (((T.sRows.length : ℤ) - (countLevel T.sRows k : ℤ)) * (countLevel T.betaRows k : ℤ)
            + (countLevel T.sRows (k + 1) : ℤ)
                * (((T.betaRows.filter (fun p => k ≤ p.len)).length : ℤ)
                  - (countLevel T.betaRows k : ℤ))) := by
    have hnn : T.flatten.length = T.sRows.length + T.betaRows.length := by
      rw [hfl, List.length_append]
    rw [hnn, hfl]
    exact cross_plus_core T.sRows T.betaRows hss hbs
  rw [hcs]
  -- Boundary vanishing: no s-row has ones ≥ ℓ+1, so countLevel sRows (ℓ+1) = 0.
  have haℓ1 : countLevel T.sRows (ℓ + 1) = 0 := by
    rw [countLevel, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro p hp
    have hpl := hss p hp
    have hpo := p.ones_le
    simp only [decide_eq_true_eq]
    omega
  -- Convert the Icc-sum to a Fin ℓ sum, substituting the closed forms.
  have hLHS : (∑ k ∈ Finset.Icc 1 ℓ,
          (((T.sRows.length : ℤ) - (countLevel T.sRows k : ℤ)) * (countLevel T.betaRows k : ℤ)
            + (countLevel T.sRows (k + 1) : ℤ)
                * (((T.betaRows.filter (fun p => k ≤ p.len)).length : ℤ)
                  - (countLevel T.betaRows k : ℤ))))
      = ∑ i : Fin ℓ,
          (((s : ℤ) - (aOf (ℓ := ℓ) T i : ℤ)) * (zOf (ℓ := ℓ) T i : ℤ)
            + (shiftNext (aOf (ℓ := ℓ) T) i : ℤ)
                * ((r i : ℤ) - (zOf (ℓ := ℓ) T i : ℤ))) := by
    rw [Finset.sum_bij (fun (i : Fin ℓ) _ => (i : ℕ) + 1)]
    · intro i _; simp only [Finset.mem_Icc]; omega
    · intro i _ j _ h; exact Fin.ext (by omega)
    · intro k hk; simp only [Finset.mem_Icc] at hk
      refine ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, ?_⟩
      simp only [Fin.val_mk]; omega
    · intro i _
      have hrc : (T.betaRows.filter (fun p => (i : ℕ) + 1 ≤ p.len)).length = r i := by
        rw [betaLenCount r hr T.betaRows hbf ((i : ℕ) + 1) (by omega) (by omega)]
        congr 1
      have hz : countLevel T.betaRows ((i : ℕ) + 1) = zOf (ℓ := ℓ) T i := rfl
      have ha : countLevel T.sRows ((i : ℕ) + 1) = aOf (ℓ := ℓ) T i := rfl
      have hnext : (i : ℕ) + 1 + 1 = (i : ℕ) + 2 := by ring
      have hasn : countLevel T.sRows ((i : ℕ) + 2) = shiftNext (aOf (ℓ := ℓ) T) i := by
        unfold shiftNext
        by_cases h0 : (i : ℕ) + 1 = ℓ
        · rw [dif_pos h0]
          have : (i : ℕ) + 2 = ℓ + 1 := by omega
          rw [this, haℓ1]
        · rw [dif_neg h0]
          have ha' : aOf (ℓ := ℓ) T ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩
              = countLevel T.sRows (((i : ℕ) + 1) + 1) := rfl
          rw [ha']
      rw [hrc, hz, ha, hslen, hnext, hasn]
  rw [hLHS]
  -- Split and distribute term by term.
  have hsplit2 : (∑ i : Fin ℓ,
        (((s : ℤ) - (aOf (ℓ := ℓ) T i : ℤ)) * (zOf (ℓ := ℓ) T i : ℤ)
          + (shiftNext (aOf (ℓ := ℓ) T) i : ℤ)
              * ((r i : ℤ) - (zOf (ℓ := ℓ) T i : ℤ))))
      = ((s : ℤ) * (∑ i, (zOf (ℓ := ℓ) T i : ℤ))
          - (∑ i, (aOf (ℓ := ℓ) T i : ℤ) * (zOf (ℓ := ℓ) T i : ℤ)))
        + ((∑ i, (r i : ℤ) * (shiftNext (aOf (ℓ := ℓ) T) i : ℤ))
          - (∑ i, (zOf (ℓ := ℓ) T i : ℤ) * (shiftNext (aOf (ℓ := ℓ) T) i : ℤ))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsplit2]; ring

/-- **Statement 2 (inversion decomposition, plus sign — `eq:inv-Eplus`).**
For every multitableau `T` of shape `μ` in the **s-block-first** order, with
`a = aOf T`, `z = zOf T`, `M = Σ_i (a_i + z_i)`:
```
s·M − inv(T) = Jₐ(T) + J_z(T) + E⁺(aOf T, zOf T).
```
The two block orders yield genuinely different tableaux, so `E⁻` and `E⁺` are
not forced equal. -/
theorem inv_decomposition_plus
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (hbw : BinaryWordGauss)
    (M : ℕ) (T : MultiTab) (hT : T ∈ TsetPlus r s M) :
    (s : ℤ) * (∑ i, (aOf (ℓ := ℓ) T i + zOf (ℓ := ℓ) T i) : ℕ) - (invMT T : ℤ)
      = Ja ℓ T + Jz ℓ T + Eplus r (aOf (ℓ := ℓ) T) (zOf (ℓ := ℓ) T) := by
  -- Mirror of `inv_decomposition_minus` for the s-block-first order.
  have hsplit := invMT_split_plus r s M T hT
  have ha := internal_a_plus r s hℓ hr M T hT
  have hz := internal_z_plus r s hℓ hr M T hT
  have hc := cross_plus r s hℓ hr M T hT
  have hsum : (s : ℤ) * (∑ i, (aOf (ℓ := ℓ) T i + zOf (ℓ := ℓ) T i) : ℕ)
      = (s : ℤ) * (∑ i, (aOf (ℓ := ℓ) T i : ℤ)) + (s : ℤ) * (∑ i, (zOf (ℓ := ℓ) T i : ℤ)) := by
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [Eplus, hsum]
  have hinv : (invMT T : ℤ)
      = (intraSum T.flatten 0 T.sRows.length : ℤ)
        + (crossSum T.flatten T.sRows.length T.flatten.length : ℤ)
        + (intraSum T.flatten T.sRows.length T.flatten.length : ℤ) := by
    rw [hsplit]; push_cast; ring
  rw [hinv]
  have haE : (∑ i, (aOf (ℓ := ℓ) T i : ℤ) * ((s : ℤ) - (aOf (ℓ := ℓ) T i : ℤ)))
      = (s : ℤ) * (∑ i, (aOf (ℓ := ℓ) T i : ℤ)) - (∑ i, (aOf (ℓ := ℓ) T i : ℤ) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hzE : (∑ i, (zOf (ℓ := ℓ) T i : ℤ) * ((r i : ℤ) - (zOf (ℓ := ℓ) T i : ℤ)))
      = (∑ i, (r i : ℤ) * (zOf (ℓ := ℓ) T i : ℤ)) - (∑ i, (zOf (ℓ := ℓ) T i : ℤ) ^ 2) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hEexp : (∑ j, ((aOf (ℓ := ℓ) T j : ℤ) ^ 2 + (zOf (ℓ := ℓ) T j : ℤ) ^ 2
        + (aOf (ℓ := ℓ) T j : ℤ) * (zOf (ℓ := ℓ) T j : ℤ)
        + (shiftNext (aOf (ℓ := ℓ) T) j : ℤ) * (zOf (ℓ := ℓ) T j : ℤ)
        - (r j : ℤ) * ((shiftNext (aOf (ℓ := ℓ) T) j : ℤ) + (zOf (ℓ := ℓ) T j : ℤ))))
      = (∑ i, (aOf (ℓ := ℓ) T i : ℤ) ^ 2)
        + (∑ i, (zOf (ℓ := ℓ) T i : ℤ) ^ 2)
        + (∑ i, (aOf (ℓ := ℓ) T i : ℤ) * (zOf (ℓ := ℓ) T i : ℤ))
        + (∑ i, (zOf (ℓ := ℓ) T i : ℤ) * (shiftNext (aOf (ℓ := ℓ) T) i : ℤ))
        - (∑ i, (r i : ℤ) * (shiftNext (aOf (ℓ := ℓ) T) i : ℤ))
        - (∑ i, (r i : ℤ) * (zOf (ℓ := ℓ) T i : ℤ)) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [haE] at ha
  rw [hzE] at hz
  rw [hEexp]
  linarith [ha, hz, hc]

/-- `countLevel` is antitone in the level: raising the threshold can only drop rows. -/
lemma countLevel_antitone (L : List Row) {i j : ℕ} (hij : i ≤ j) :
    countLevel L j ≤ countLevel L i := by
  unfold countLevel
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro p _ hp
  simp only [decide_eq_true_eq] at hp ⊢
  omega

/-- **Φ maps into `azFinset`.**  The block-count map `T ↦ (aOf T, zOf T)` sends a
reindexing multitableau (either block order) into `azFinset`: the domain
constraints (`azDomain`) follow from monotonicity of `countLevel` and the row
lengths, and the level-sum constraint `Σ (aᵢ+zᵢ)=M` is exactly `levelSum T = M`. -/
theorem phi_mem_az
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (M : ℕ) (bf : Bool) (T : MultiTab) (hT : T ∈ TsetOrder r s M bf) :
    ((aOf (ℓ := ℓ) T, zOf (ℓ := ℓ) T) : (Fin ℓ → ℕ) × (Fin ℓ → ℕ))
      ∈ azFinset r s M := by
  -- Unpack membership in `TsetOrder`: fillings for both blocks + levelSum = M.
  simp only [TsetOrder, Finset.mem_filter, Finset.mem_image,
    Finset.mem_product] at hT
  obtain ⟨⟨⟨b, w⟩, ⟨hb, hw⟩, hTeq⟩, hlvl⟩ := hT
  subst hTeq
  -- Now T = ⟨b, w, bf⟩ with hb : b ∈ fillings (betaParts r), hw : w ∈ fillings (sBlockLens ℓ s).
  -- s-block length = s.
  have hslen : w.length = s := sBlock_length _ hw
  -- Bound: aOf i ≤ s.
  have hAle : ∀ i : Fin ℓ, aOf (ℓ := ℓ) ⟨b, w, bf⟩ i ≤ s := by
    intro i
    show countLevel w ((i : ℕ) + 1) ≤ s
    unfold countLevel
    rw [← hslen]
    exact List.length_filter_le _ _
  -- Bound: zOf i ≤ r i.
  have hZle : ∀ i : Fin ℓ, zOf (ℓ := ℓ) ⟨b, w, bf⟩ i ≤ r i := by
    intro i
    show countLevel b ((i : ℕ) + 1) ≤ r i
    -- countLevel b (i+1) = #{ones ≥ i+1} ≤ #{len ≥ i+1} = r i via betaLenCount.
    have hstep : countLevel b ((i : ℕ) + 1)
        ≤ (b.filter (fun p => (i : ℕ) + 1 ≤ p.len)).length := by
      unfold countLevel
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      apply List.countP_mono_left
      intro p _ hp
      simp only [decide_eq_true_eq] at hp ⊢
      exact le_trans hp p.ones_le
    have hcount := betaLenCount r hr b hb ((i : ℕ) + 1) (by omega) (by have := i.isLt; omega)
    rw [hcount] at hstep
    have : (⟨(i : ℕ) + 1 - 1, by have := i.isLt; omega⟩ : Fin ℓ) = i := by
      apply Fin.ext; simp
    rw [this] at hstep
    exact hstep
  -- Now assemble azFinset membership.
  simp only [azFinset, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset,
    Finset.mem_range]
  refine ⟨⟨fun i => ?_, fun i => ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Nat.lt_succ_of_le (hAle i)
  · exact Nat.lt_succ_of_le (hZle i)
  · -- a j ≤ shiftPrev s a j
    intro j
    unfold shiftPrev
    by_cases hj : (j : ℕ) = 0
    · simp only [hj, if_true]; exact hAle j
    · simp only [hj, if_false]
      show countLevel w ((j : ℕ) + 1) ≤ countLevel w (((j : ℕ) - 1) + 1)
      apply countLevel_antitone
      omega
  · -- z j ≤ r j
    intro j; exact hZle j
  · -- shiftNext z j ≤ z j
    intro j
    unfold shiftNext
    by_cases hj : (j : ℕ) + 1 = ℓ
    · simp only [hj, dif_pos]; exact Nat.zero_le _
    · simp only [hj, dif_neg, not_false_iff]
      show countLevel b (((j : ℕ) + 1) + 1) ≤ countLevel b ((j : ℕ) + 1)
      apply countLevel_antitone
      omega
  · -- Σ (a i + z i) = M
    rw [← hlvl]
    rfl

/-! ### Encoding of `s`-block fillings by "ones-vectors".

A filling of `sBlockLens ℓ s = replicate s ℓ` is a list of exactly `s` rows, each
of length `ℓ`, hence determined by the tuple of `ones` values `k : Fin s → Fin (ℓ+1)`
(each `ones ≤ ℓ`).  `onesFilling ℓ k` builds the filling from such a tuple; it is
the inverse of `w ↦ (fun t => (w[t]).ones)`. -/

/-- The filling of `replicate s ℓ` whose `t`-th row has `ones = k t`. -/
def onesFilling {s : ℕ} (ℓ : ℕ) (k : Fin s → Fin (ℓ + 1)) : List Row :=
  List.ofFn (fun t => (⟨ℓ, (k t : ℕ), by have := (k t).isLt; omega⟩ : Row))

/-- Membership characterization of `fillings (replicate s ℓ)`: a filling is
exactly a list of `s` rows all of length `ℓ`. -/
lemma mem_rowsOfLen_iff {L : ℕ} {p : Row} : p ∈ rowsOfLen L ↔ p.len = L := by
  constructor
  · exact mem_rowsOfLen
  · intro h
    simp only [rowsOfLen, Finset.mem_image, Finset.mem_range]
    refine ⟨p.ones, by have := p.ones_le; omega, ?_⟩
    cases p with
    | mk len ones ones_le =>
      simp only at h
      subst h
      simp only [min_eq_left ones_le]

lemma mem_fillings_replicate_iff {ℓ s : ℕ} (w : List Row) :
    w ∈ fillings (List.replicate s ℓ) ↔ (w.length = s ∧ ∀ p ∈ w, p.len = ℓ) := by
  induction s generalizing w with
  | zero =>
    simp only [List.replicate, fillings, Finset.mem_singleton]
    constructor
    · intro h; subst h; simp
    · intro ⟨hlen, _⟩; exact List.length_eq_zero_iff.mp hlen
  | succ s ih =>
    rw [List.replicate_succ]
    simp only [fillings, Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨⟨p, ws⟩, ⟨hp, hws⟩, rfl⟩
      have hlen := (ih ws).mp hws
      refine ⟨by simp [hlen.1], ?_⟩
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact mem_rowsOfLen hp
      · exact hlen.2 q hq
    · rintro ⟨hlen, hall⟩
      obtain ⟨p, ws, rfl⟩ := List.exists_cons_of_ne_nil (l := w) (by
        rintro rfl; simp at hlen)
      refine ⟨(p, ws), ⟨?_, ?_⟩, rfl⟩
      · rw [mem_rowsOfLen_iff]; exact hall p List.mem_cons_self
      · apply (ih ws).mpr
        refine ⟨by simpa using hlen, ?_⟩
        intro q hq; exact hall q (List.mem_cons_of_mem _ hq)

/-- `onesFilling` lands in `fillings (replicate s ℓ)`. -/
lemma onesFilling_mem {ℓ s : ℕ} (k : Fin s → Fin (ℓ + 1)) :
    onesFilling ℓ k ∈ fillings (List.replicate s ℓ) := by
  rw [mem_fillings_replicate_iff]
  constructor
  · simp [onesFilling]
  · intro p hp
    simp only [onesFilling, List.mem_ofFn, Set.mem_range] at hp
    obtain ⟨t, rfl⟩ := hp
    rfl

/-- `countLevel (onesFilling ℓ k) i` counts the coordinates `t` with `i ≤ k t`. -/
lemma length_filter_ofFn {n : ℕ} {α : Type*} (f : Fin n → α) (p : α → Bool) :
    ((List.ofFn f).filter p).length
      = (Finset.univ.filter (fun t : Fin n => p (f t))).card := by
  rw [Finset.card_filter, ← List.sum_ofFn (f := fun t : Fin n => if p (f t) then (1:ℕ) else 0)]
  rw [← List.countP_eq_length_filter]
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.countP_cons, List.sum_cons, ih (fun i => f i.succ)]
    by_cases h : p (f 0) <;> simp [h] <;> ring

lemma countLevel_onesFilling {ℓ s : ℕ} (k : Fin s → Fin (ℓ + 1)) (i : ℕ) :
    countLevel (onesFilling ℓ k) i
      = (Finset.univ.filter (fun t : Fin s => i ≤ (k t : ℕ))).card := by
  unfold countLevel onesFilling
  rw [length_filter_ofFn]
  congr 1
  ext t
  simp [decide_eq_true_eq]

/-- The set of binary words of length `shiftPrev s a i` with exactly `a i` ones,
used to describe the level-`i` factor of the A-side fiber sum. -/
noncomputable def wordSetA {ℓ : ℕ} (s : ℕ) (a : Fin ℓ → ℕ) (i : Fin ℓ) :
    Finset (Fin (shiftPrev s a i) → Bool) :=
  Finset.univ.filter (fun v => (Finset.univ.filter (fun j => v j = true)).card = a i)

/-- Total encoding of a filling of `replicate s ℓ` by its ones-vector.  For
`w ∈ fillings (replicate s ℓ)` (so `w.length = s`) this returns the tuple of
`ones` values; off that set it returns junk (`0`). -/
def encOnes {ℓ : ℕ} (s : ℕ) (w : List Row) : Fin s → Fin (ℓ + 1) :=
  fun t => if h : (t : ℕ) < w.length
    then ⟨min (w[t]).ones ℓ, by have := Nat.min_le_right (w[t]).ones ℓ; omega⟩
    else 0

/-- `c i k = #{ t : Fin s | i ≤ k t }`, the number of ones-vector coordinates
reaching level `i`. -/
def cLev {ℓ s : ℕ} (k : Fin s → Fin (ℓ + 1)) (i : ℕ) : ℕ :=
  (Finset.univ.filter (fun t : Fin s => i ≤ (k t : ℕ))).card

/-- `enc`/`onesFilling` is a bijection: `onesFilling ℓ (encOnes s w) = w` for
`w ∈ fillings (replicate s ℓ)`. -/
lemma onesFilling_encOnes {ℓ s : ℕ}
    (w : List Row) (hw : w ∈ fillings (List.replicate s ℓ)) :
    onesFilling ℓ (encOnes s w) = w := by
  obtain ⟨hlen, hall⟩ := (mem_fillings_replicate_iff w).mp hw
  have hlhslen : (onesFilling ℓ (encOnes s w)).length = w.length := by
    simp [onesFilling, hlen]
  apply List.ext_getElem hlhslen
  intro t ht1 ht2
  have htw : t < w.length := by rw [hlen] at ht2 ⊢; exact ht2
  have hts : t < s := by omega
  -- properties of w[t]
  have hwlen : (w[t]).len = ℓ := hall _ (List.getElem_mem _)
  have hwones : (w[t]).ones ≤ ℓ := by have := (w[t]).ones_le; omega
  have hmin : min (w[t]).ones ℓ = (w[t]).ones := min_eq_left hwones
  -- evaluate encOnes at t
  have henc : ((encOnes (ℓ := ℓ) s w) ⟨t, hts⟩ : ℕ) = (w[t]).ones := by
    simp only [encOnes, Fin.getElem_fin, dif_pos htw]
    exact hmin
  -- LHS row
  simp only [onesFilling, List.getElem_ofFn]
  -- Goal: { len := ℓ, ones := ↑(encOnes s w ⟨t,_⟩), ones_le := _ } = w[t]
  have hval : ((encOnes (ℓ := ℓ) s w) ⟨t, hts⟩ : ℕ) = (w[t]).ones := henc
  -- eta-expand w[t] on the RHS, then compare fields via Row.mk.injEq
  conv_rhs => rw [show (w[t] : Row) = ⟨(w[t]).len, (w[t]).ones, (w[t]).ones_le⟩ from rfl]
  refine (Row.mk.injEq _ _ _ _ _ _).mpr ⟨hwlen.symm, ?_⟩
  exact hval

/-- `encOnes s (onesFilling ℓ k) = k`. -/
lemma encOnes_onesFilling {ℓ s : ℕ} (k : Fin s → Fin (ℓ + 1)) :
    encOnes s (onesFilling ℓ k) = k := by
  funext t
  have hlen : (onesFilling ℓ k).length = s := by simp [onesFilling]
  have htlt : (t : ℕ) < (onesFilling ℓ k).length := by rw [hlen]; exact t.isLt
  unfold encOnes
  rw [dif_pos htlt]
  apply Fin.ext
  simp only [Fin.getElem_fin]
  have hget : (onesFilling ℓ k)[(t : ℕ)].ones = (k t : ℕ) := by
    simp only [onesFilling, List.getElem_ofFn]
  rw [hget]
  have := (k t).isLt
  omega

/-- Source-side reformulation of `fiberA_biject`: sum over ones-vectors. -/
lemma fiberA_source_eq {ℓ : ℕ} (s : ℕ) (a : Fin ℓ → ℕ) :
    ∑ w ∈ (fillings (sBlockLens ℓ s)).filter
        (fun w => (fun i : Fin ℓ => countLevel w ((i : ℕ) + 1)) = a),
        q ^ (∑ i : Fin ℓ, invWord (wordA w ((i : ℕ) + 1)))
      = ∑ k ∈ (Finset.univ.filter
          (fun k : Fin s → Fin (ℓ + 1) => (fun i : Fin ℓ => cLev k ((i : ℕ) + 1)) = a)),
          q ^ (∑ i : Fin ℓ, invWord (wordA (onesFilling ℓ k) ((i : ℕ) + 1))) := by
  classical
  -- cLev k m and countLevel (onesFilling ℓ k) m are equal (both count coords with m ≤ k t)
  have hcLev : ∀ (k : Fin s → Fin (ℓ + 1)) (m : ℕ),
      cLev k m = countLevel (onesFilling ℓ k) m := by
    intro k m
    rw [countLevel_onesFilling]; rfl
  refine Finset.sum_nbij'
      (i := fun w => encOnes (ℓ := ℓ) s w)
      (j := fun k => onesFilling ℓ k)
      ?_ ?_ ?_ ?_ ?_
  · -- hi : w ∈ LHS filter → encOnes s w ∈ RHS filter
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    obtain ⟨hwmem, hwfilt⟩ := hw
    have hwmem' : w ∈ fillings (List.replicate s ℓ) := hwmem
    funext i
    have hround : onesFilling ℓ (encOnes (ℓ := ℓ) s w) = w :=
      onesFilling_encOnes w hwmem'
    have hh : cLev (encOnes (ℓ := ℓ) s w) ((i : ℕ) + 1)
        = countLevel w ((i : ℕ) + 1) := by
      rw [hcLev, hround]
    rw [hh]
    exact congrFun hwfilt i
  · -- hj : k ∈ RHS filter → onesFilling ℓ k ∈ LHS filter
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    refine ⟨onesFilling_mem k, ?_⟩
    funext i
    have hh := congrFun hk i
    rw [← hcLev]
    exact hh
  · -- left_neg : w ∈ LHS → onesFilling ℓ (encOnes s w) = w
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact onesFilling_encOnes w hw.1
  · -- right_neg : k ∈ RHS → encOnes s (onesFilling ℓ k) = k
    intro k _
    exact encOnes_onesFilling k
  · -- value equality
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    have hround : onesFilling ℓ (encOnes (ℓ := ℓ) s w) = w :=
      onesFilling_encOnes w hw.1
    rw [hround]

/-! ### Inverse map machinery for the A-side level bijection. -/

/-- Nat-level generalization of `shiftPrev`. -/
def shiftPrevN {ℓ : ℕ} (s : ℕ) (a : Fin ℓ → ℕ) : ℕ → ℕ
  | 0 => s
  | (m + 1) => if h : m < ℓ then a ⟨m, h⟩ else 0

/-- `V` as a plain doubly-indexed boolean, `false` outside the valid ranges. -/
def padV {ℓ : ℕ} {s : ℕ} (a : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (shiftPrev s a i) → Bool) : ℕ → ℕ → Bool :=
  fun j p => if hj : j < ℓ then
      (if hp : p < shiftPrev s a ⟨j, hj⟩ then V ⟨j, hj⟩ ⟨p, hp⟩ else false)
    else false

/-- The rank (number of strictly-smaller elements) of `t` inside a finset `A`. -/
def rankIn {s : ℕ} (A : Finset (Fin s)) (t : Fin s) : ℕ :=
  (A.filter (fun u => u < t)).card

/-- Survivors at nat-level `j` under the survival recursion driven by `V`. -/
def aliveNat {ℓ s : ℕ} (a : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (shiftPrev s a i) → Bool) : ℕ → Finset (Fin s)
  | 0 => Finset.univ
  | (j + 1) => (aliveNat a V j).filter (fun t => padV a V j (rankIn (aliveNat a V j) t))

/-- The reconstructed ones-vector: `kInv V t` = number of levels `t` survives. -/
def kInv {ℓ s : ℕ} (a : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (shiftPrev s a i) → Bool) (t : Fin s) : Fin (ℓ + 1) :=
  ⟨(Finset.univ.filter (fun j : Fin ℓ => t ∈ aliveNat a V ((j : ℕ) + 1))).card, by
    have h : (Finset.univ.filter (fun j : Fin ℓ => t ∈ aliveNat a V ((j : ℕ) + 1))).card
        ≤ (Finset.univ : Finset (Fin ℓ)).card := Finset.card_filter_le _ _
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega⟩

/-- The element of `(L.filter P).map g` at the position equal to the number of
earlier surviving entries (`((L.take t).filter P).length`) is exactly `g L[t]`,
when `L[t]` survives the filter. -/
lemma filter_map_getElem_rank {α β : Type*} (L : List α) (P : α → Bool)
    (g : α → β) (t : ℕ) (ht : t < L.length) (hP : P L[t] = true) :
    ((L.filter P).map g)[((L.take t).filter P).length]? = some (g L[t]) := by
  have hsplit : L = L.take t ++ L[t] :: L.drop (t + 1) := by
    conv_lhs => rw [← List.take_append_drop t L]
    congr 1
    rw [List.drop_eq_getElem_cons ht]
  have hfil : L.filter P
      = (L.take t).filter P ++ (L[t] :: (L.drop (t + 1)).filter P) := by
    conv_lhs => rw [hsplit]
    rw [List.filter_append, List.filter_cons_of_pos hP]
  rw [hfil, List.map_append, List.map_cons]
  rw [List.getElem?_append_right (by simp)]
  simp

/-- The number of surviving entries strictly before index `t` in `List.ofFn f`,
under a predicate `P`, equals the number of coordinates `u < t` with `P (f u)`. -/
lemma take_filter_ofFn_length {s : ℕ} {α : Type*} (f : Fin s → α) (P : α → Bool)
    (t : ℕ) :
    (((List.ofFn f).take t).filter P).length
      = (Finset.univ.filter (fun u : Fin s => (u : ℕ) < t ∧ P (f u) = true)).card := by
  induction s generalizing t with
  | zero => simp
  | succ s ih =>
    -- rewrite the RHS card as a sum, then peel off index 0 with Fin.sum_univ_succ
    have hcard : (Finset.univ.filter
          (fun u : Fin (s + 1) => (u : ℕ) < t ∧ P (f u) = true)).card
        = (if 0 < t ∧ P (f 0) = true then 1 else 0)
          + (Finset.univ.filter
              (fun u : Fin s => (u : ℕ) + 1 < t ∧ P (f u.succ) = true)).card := by
      rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ]
    cases t with
    | zero =>
      simp only [List.take_zero, List.filter_nil, List.length_nil]
      rw [hcard]
      simp
    | succ t =>
      have htail : (Finset.univ.filter
            (fun u : Fin s => (u : ℕ) + 1 < t + 1 ∧ P (f u.succ) = true)).card
          = (Finset.univ.filter
              (fun u : Fin s => (u : ℕ) < t ∧ P (f u.succ) = true)).card := by
        apply Finset.card_bij (fun u _ => u)
        · intro u hu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
          exact ⟨by omega, hu.2⟩
        · intro u _ v _ h; exact h
        · intro u hu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
          exact ⟨u, ⟨by omega, hu.2⟩, rfl⟩
      rw [List.ofFn_succ, List.take_succ_cons, List.filter_cons, hcard, htail]
      by_cases h0 : P (f 0)
      · rw [if_pos h0, List.length_cons, ih (fun i => f i.succ) t]
        have : (0 : ℕ) < t + 1 ∧ P (f 0) = true := ⟨Nat.succ_pos t, h0⟩
        rw [if_pos this]
        ring
      · rw [if_neg h0, ih (fun i => f i.succ) t]
        have : ¬ ((0 : ℕ) < t + 1 ∧ P (f 0) = true) := by
          rintro ⟨_, h⟩; exact h0 h
        rw [if_neg this]
        ring

/-- Plain-list version of `take_filter_ofFn_length`: the number of surviving
entries strictly before index `t` in a list `L`, under predicate `P`, equals the
number of positions `u < t` of `L` with `P L[u]`. -/
lemma take_filter_length_eq_card {α : Type*} (L : List α) (P : α → Bool) (t : ℕ) :
    ((L.take t).filter P).length
      = (Finset.univ.filter (fun u : Fin L.length =>
          (u : ℕ) < t ∧ P (L[(u : ℕ)]) = true)).card := by
  have h := take_filter_ofFn_length (fun i : Fin L.length => L[(i : ℕ)]) P t
  rw [List.ofFn_getElem] at h
  rw [h]

/-- **Padval evaluation at the threshold set.**  For `t` surviving to level `m`
(`m ≤ k t`), the pad value `padV a V m (rankIn A t)`, where `A` is the level-`m`
threshold set, equals `decide (m + 1 ≤ k t)`. -/
lemma aliveNat_forward_padval {ℓ s : ℕ} (hℓ : 0 < ℓ) (a : Fin ℓ → ℕ)
    (k : Fin s → Fin (ℓ + 1))
    (hk : (fun i : Fin ℓ => cLev k ((i : ℕ) + 1)) = a)
    (V : (i : Fin ℓ) → Fin (shiftPrev s a i) → Bool)
    (hV : ∀ i : Fin ℓ, List.ofFn (V i) = wordA (onesFilling ℓ k) ((i : ℕ) + 1))
    (m : ℕ) (hmℓ : m < ℓ) (t : Fin s) (hmt : m ≤ (k t : ℕ)) :
    padV a V m (rankIn (Finset.univ.filter (fun u : Fin s => m ≤ (k u : ℕ))) t)
      = decide (m + 1 ≤ (k t : ℕ)) := by
  classical
  set A : Finset (Fin s) := Finset.univ.filter (fun u : Fin s => m ≤ (k u : ℕ)) with hAdef
  set p : ℕ := rankIn A t with hpdef
  -- t ∈ A
  have htA : t ∈ A := by
    rw [hAdef]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hmt
  -- shiftPrev s a ⟨m,hmℓ⟩ = cLev k m
  have hshift : shiftPrev s a ⟨m, hmℓ⟩ = cLev k m := by
    unfold shiftPrev
    by_cases hm0 : m = 0
    · subst hm0
      simp only [Fin.val_mk, if_true, if_pos]
      -- cLev k 0 = s
      rw [cLev]
      have hh : (Finset.univ.filter (fun u : Fin s => 0 ≤ (k u : ℕ))) = Finset.univ := by
        apply Finset.filter_true_of_mem; intro u _; exact Nat.zero_le _
      rw [hh, Finset.card_univ, Fintype.card_fin]
    · have : (⟨m, hmℓ⟩ : Fin ℓ).val ≠ 0 := by simp [hm0]
      rw [if_neg this]
      have := congrFun hk ⟨m - 1, by omega⟩
      simp only at this
      rw [show (⟨(⟨m, hmℓ⟩ : Fin ℓ).val - 1, by omega⟩ : Fin ℓ) = ⟨m - 1, by omega⟩ from rfl]
      rw [← this]
      congr 1
      omega
  -- A.card = cLev k m
  have hAcard : A.card = cLev k m := by
    rw [hAdef, cLev]
  -- p < A.card
  have hpltcard : p < A.card := by
    rw [hpdef, rankIn]
    apply Finset.card_lt_card
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro hsub
    have := hsub htA
    simp only [Finset.mem_filter] at this
    exact absurd this.2 (lt_irrefl t)
  -- p < shiftPrev s a ⟨m,hmℓ⟩
  have hp : p < shiftPrev s a ⟨m, hmℓ⟩ := by
    rw [hshift]; rw [← hAcard]; exact hpltcard
  -- Unfold padV.
  have hpadeq : padV a V m p = V ⟨m, hmℓ⟩ ⟨p, hp⟩ := by
    unfold padV
    rw [dif_pos hmℓ, dif_pos hp]
  rw [hpadeq]
  -- Set up the filter/map machinery.
  set L : List Row := onesFilling ℓ k with hLdef
  set P : Row → Bool := fun row => decide (m ≤ row.ones) with hPdef
  set g : Row → Bool := fun row => decide (m + 1 ≤ row.ones) with hgdef
  -- L[t].ones = k t and L.length = s
  have hLlen : L.length = s := by rw [hLdef, onesFilling]; simp
  have htlt : (t : ℕ) < L.length := by rw [hLlen]; exact t.isLt
  have hLget : (L[(t : ℕ)]).ones = (k t : ℕ) := by
    simp only [hLdef, onesFilling, List.getElem_ofFn]
  have hPt : P L[(t : ℕ)] = true := by
    rw [hPdef]; simp only [decide_eq_true_eq, hLget]; exact hmt
  -- wordA form: List.ofFn (V ⟨m,hmℓ⟩) = (L.filter P).map g
  have hwordA : List.ofFn (V ⟨m, hmℓ⟩) = (L.filter P).map g := by
    have := hV ⟨m, hmℓ⟩
    simp only [Fin.val_mk] at this
    rw [this]
    unfold wordA
    rw [hLdef, hPdef, hgdef]
    congr 2
  -- rank index = ((L.take t).filter P).length
  have hidx : p = ((L.take (t : ℕ)).filter P).length := by
    rw [hpdef, rankIn]
    have hLof : L = List.ofFn (fun u : Fin s =>
        (⟨ℓ, (k u : ℕ), by have := (k u).isLt; omega⟩ : Row)) := by
      rw [hLdef, onesFilling]
    rw [hLof, take_filter_ofFn_length]
    -- now: {u ∈ A | u < t}.card = card {u | ↑u < ↑t ∧ P ⟨ℓ,k u,_⟩}
    rw [hAdef]
    apply Finset.card_bij (fun u _ => u)
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      obtain ⟨hu1, hu2⟩ := hu
      refine ⟨hu2, ?_⟩
      rw [hPdef]
      simp only [decide_eq_true_eq]
      exact hu1
    · intro u1 _ u2 _ h; exact h
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      obtain ⟨hu1, hu2⟩ := hu
      refine ⟨u, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hPdef] at hu2
      simp only [decide_eq_true_eq] at hu2
      exact ⟨hu2, hu1⟩
  -- Now compute V ⟨m,hmℓ⟩ ⟨p,hp⟩ via getElem? of List.ofFn.
  have hVget : V ⟨m, hmℓ⟩ ⟨p, hp⟩ = (((L.filter P).map g)[p]?).getD default := by
    have hpmap : p < ((L.filter P).map g).length := by
      rw [← hwordA]; simpa using hp
    rw [List.getElem?_eq_getElem hpmap, Option.getD_some]
    simp only [← hwordA, List.getElem_ofFn]
  rw [hVget]
  -- Apply filter_map_getElem_rank.
  have hrank := filter_map_getElem_rank L P g (t : ℕ) htlt hPt
  rw [← hidx] at hrank
  rw [hrank]
  simp only [Option.getD_some]
  rw [hgdef]
  simp only [hLget]

/-- **Survival-set = threshold set (source→target direction).** -/
lemma aliveNat_forward {ℓ s : ℕ} (hℓ : 0 < ℓ) (a : Fin ℓ → ℕ)
    (hadom : ∀ j : Fin ℓ, a j ≤ shiftPrev s a j)
    (k : Fin s → Fin (ℓ + 1))
    (hk : (fun i : Fin ℓ => cLev k ((i : ℕ) + 1)) = a)
    (V : (i : Fin ℓ) → Fin (shiftPrev s a i) → Bool)
    (hV : ∀ i : Fin ℓ, List.ofFn (V i) = wordA (onesFilling ℓ k) ((i : ℕ) + 1)) :
    ∀ m : ℕ, m ≤ ℓ →
      aliveNat a V m = Finset.univ.filter (fun t : Fin s => m ≤ (k t : ℕ)) := by
  intro m
  induction m with
  | zero =>
    intro _
    simp only [aliveNat]
    ext t
    simp only [Finset.mem_univ, Finset.mem_filter, true_and, Nat.zero_le]
  | succ m ih =>
    intro hm
    have hmℓ : m < ℓ := by omega
    have ihm := ih (by omega)
    -- Abbreviations.
    set A := aliveNat a V m with hA
    have hAeq : A = Finset.univ.filter (fun t : Fin s => m ≤ (k t : ℕ)) := ihm
    -- Unfold one step of aliveNat.
    show A.filter (fun t => padV a V m (rankIn A t)) =
      Finset.univ.filter (fun t : Fin s => m + 1 ≤ (k t : ℕ))
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hAeq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hmt, hpad⟩
      -- Show m + 1 ≤ k t using hpad.
      by_contra hcon
      have hval := aliveNat_forward_padval hℓ a k hk V hV m hmℓ t hmt
      rw [hval] at hpad
      simp only [decide_eq_true_eq] at hpad
      omega
    · intro hmt1
      have hmt : m ≤ (k t : ℕ) := by omega
      refine ⟨hmt, ?_⟩
      have hval := aliveNat_forward_padval hℓ a k hk V hV m hmℓ t hmt
      rw [hval]
      simp only [decide_eq_true_eq]
      omega

/-- **Left round-trip.** -/
lemma kInv_forward {ℓ s : ℕ} (hℓ : 0 < ℓ) (a : Fin ℓ → ℕ)
    (hadom : ∀ j : Fin ℓ, a j ≤ shiftPrev s a j)
    (k : Fin s → Fin (ℓ + 1))
    (hk : (fun i : Fin ℓ => cLev k ((i : ℕ) + 1)) = a)
    (V : (i : Fin ℓ) → Fin (shiftPrev s a i) → Bool)
    (hV : ∀ i : Fin ℓ, List.ofFn (V i) = wordA (onesFilling ℓ k) ((i : ℕ) + 1)) :
    kInv a V = k := by
  classical
  have hfwd := aliveNat_forward hℓ a hadom k hk V hV
  funext t
  apply Fin.ext
  show (Finset.univ.filter (fun j : Fin ℓ => t ∈ aliveNat a V ((j : ℕ) + 1))).card = (k t : ℕ)
  -- membership at level j+1 iff j+1 ≤ k t
  have hmem : ∀ j : Fin ℓ, (t ∈ aliveNat a V ((j : ℕ) + 1)) ↔ ((j : ℕ) + 1 ≤ (k t : ℕ)) := by
    intro j
    rw [hfwd ((j : ℕ) + 1) (by omega)]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hfilt : (Finset.univ.filter (fun j : Fin ℓ => t ∈ aliveNat a V ((j : ℕ) + 1)))
      = (Finset.univ.filter (fun j : Fin ℓ => (j : ℕ) < (k t : ℕ))) := by
    apply Finset.filter_congr
    intro j _
    rw [hmem j]
    omega
  rw [hfilt]
  -- count of j : Fin ℓ with j < k t equals k t (since k t ≤ ℓ)
  have hkle : (k t : ℕ) ≤ ℓ := by have := (k t).isLt; omega
  -- {j : Fin ℓ | ↑j < c}.card = c via bijection with Finset.range c
  rw [Finset.card_bij (fun (j : Fin ℓ) _ => (j : ℕ))
        (s := (Finset.univ.filter (fun j : Fin ℓ => (j : ℕ) < (k t : ℕ))))
        (t := Finset.range (k t : ℕ))]
  · simp only [Finset.card_range]
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_range]; exact hj
  · intro j₁ h₁ j₂ h₂ hEq
    exact Fin.ext hEq
  · intro n hn
    simp only [Finset.mem_range] at hn
    exact ⟨⟨n, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hn, rfl⟩

/-- `rankIn A` is strictly monotone on `A`. -/
lemma rankIn_lt_of_lt {s : ℕ} (A : Finset (Fin s)) {t u : Fin s}
    (ht : t ∈ A) (hlt : t < u) : rankIn A t < rankIn A u := by
  classical
  unfold rankIn
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 hlt⟩
  · intro hsub
    have : t ∈ A.filter (fun v => v < t) := hsub (by
      simp only [Finset.mem_filter]; exact ⟨ht, hlt⟩)
    simp only [Finset.mem_filter] at this
    exact absurd this.2 (lt_irrefl t)

/-- `rankIn A t < A.card` for `t ∈ A`. -/
lemma rankIn_lt_card {s : ℕ} (A : Finset (Fin s)) {t : Fin s} (ht : t ∈ A) :
    rankIn A t < A.card := by
  classical
  unfold rankIn
  apply Finset.card_lt_card
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro hsub
  have := hsub ht
  simp only [Finset.mem_filter] at this
  exact absurd this.2 (lt_irrefl t)

/-- `rankIn A` is injective on `A`. -/
lemma rankIn_injOn {s : ℕ} (A : Finset (Fin s)) :
    Set.InjOn (rankIn A) A := by
  intro t ht u hu hEq
  simp only [Finset.mem_coe] at ht hu
  rcases lt_trichotomy t u with h | h | h
  · exact absurd hEq (ne_of_lt (rankIn_lt_of_lt A ht h))
  · exact h
  · exact absurd hEq.symm (ne_of_lt (rankIn_lt_of_lt A hu h))

/-- The image of `A` under `rankIn A` is `range A.card`. -/
lemma rankIn_image {s : ℕ} (A : Finset (Fin s)) :
    A.image (rankIn A) = Finset.range A.card := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    simp only [Finset.mem_image] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    simp only [Finset.mem_range]
    exact rankIn_lt_card A ht
  · rw [Finset.card_range,
      Finset.card_image_of_injOn (rankIn_injOn A)]

/-- Filtering `A` by a predicate on `rankIn A t` has the same cardinality as
filtering `Fin A.card` by that predicate (rank is an order-bijection). -/
lemma card_filter_rankIn {s : ℕ} (A : Finset (Fin s)) (f : ℕ → Bool) :
    (A.filter (fun t => f (rankIn A t) = true)).card
      = (Finset.univ.filter (fun p : Fin A.card => f (p : ℕ) = true)).card := by
  classical
  apply Finset.card_bij (fun (t : Fin s) (ht : t ∈ A.filter (fun t => f (rankIn A t) = true)) =>
      (⟨rankIn A t, rankIn_lt_card A (Finset.mem_of_mem_filter t ht)⟩ : Fin A.card))
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ht.2
  · intro t₁ h₁ t₂ h₂ hEq
    simp only [Finset.mem_filter] at h₁ h₂
    exact rankIn_injOn A (Finset.mem_coe.mpr h₁.1) (Finset.mem_coe.mpr h₂.1)
      (by simpa using hEq)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hpmem : (p : ℕ) ∈ A.image (rankIn A) := by
      rw [rankIn_image]; simp only [Finset.mem_range]; exact p.isLt
    simp only [Finset.mem_image] at hpmem
    obtain ⟨t, htA, htp⟩ := hpmem
    refine ⟨t, ?_, ?_⟩
    · simp only [Finset.mem_filter]
      exact ⟨htA, by rw [htp]; exact hp⟩
    · apply Fin.ext; simpa using htp

/-- `aliveNat` is antitone: level `m+1` sits inside level `m`. -/
lemma aliveNat_succ_subset {ℓ s : ℕ} (a : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (shiftPrev s a i) → Bool) (m : ℕ) :
    aliveNat a V (m + 1) ⊆ aliveNat a V m := by
  intro t ht
  rw [aliveNat] at ht
  exact Finset.mem_of_mem_filter t ht

/-- `aliveNat` is antitone in the level. -/
lemma aliveNat_antitone {ℓ s : ℕ} (a : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (shiftPrev s a i) → Bool) {m n : ℕ} (h : m ≤ n) :
    aliveNat a V n ⊆ aliveNat a V m := by
  induction n with
  | zero => simp only [Nat.le_zero] at h; subst h; exact Finset.Subset.refl _
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact (aliveNat_succ_subset a V n).trans (ih (by omega))
    · have : m = n + 1 := by omega
      subst this; exact Finset.Subset.refl _

/-- Membership in `aliveNat` is characterized by `kInv`: `t ∈ aliveNat m ↔ m ≤ kInv t`. -/
lemma mem_aliveNat_iff_kInv {ℓ s : ℕ} (a : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (shiftPrev s a i) → Bool) (t : Fin s) {m : ℕ} (hm : m ≤ ℓ) :
    t ∈ aliveNat a V m ↔ m ≤ (kInv a V t : ℕ) := by
  classical
  -- SANITY CHECK PASSED (standard antitone down-set argument; kInv = # surviving levels)
  -- Abbreviation for the survival count c := kInv a V t.
  set c : ℕ := (kInv a V t : ℕ) with hc
  have hcdef : c = (Finset.univ.filter (fun j : Fin ℓ => t ∈ aliveNat a V ((j : ℕ) + 1))).card := by
    simp only [hc, kInv]
  -- Cardinality of an initial segment of Fin ℓ: for N ≤ ℓ, #{j : Fin ℓ | j < N} = N.
  have hseg : ∀ N : ℕ, N ≤ ℓ →
      (Finset.univ.filter (fun j : Fin ℓ => (j : ℕ) < N)).card = N := by
    intro N hN
    conv_rhs => rw [← Finset.card_range N]
    apply Finset.card_bij (fun (j : Fin ℓ) _ => (j : ℕ)) (t := Finset.range N)
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_range]; exact hj
    · intro j1 _ j2 _ h; exact Fin.ext h
    · intro n hn
      simp only [Finset.mem_range] at hn
      refine ⟨⟨n, by omega⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hn
  -- Membership at level j+1 is a down-closed initial segment in j (antitonicity).
  have hdown : ∀ j : Fin ℓ, t ∈ aliveNat a V ((j : ℕ) + 1) ↔ (j : ℕ) < c := by
    intro j
    constructor
    · -- If t survives level j+1, all lower levels survive too, so c ≥ (j:ℕ)+1.
      intro hj
      by_contra hlt
      push_neg at hlt  -- hlt : c ≤ (j:ℕ)
      -- The segment {j'' : Fin ℓ | (j'':ℕ) ≤ (j:ℕ)} ⊆ S, has card (j:ℕ)+1.
      have hsub : (Finset.univ.filter (fun j'' : Fin ℓ => (j'' : ℕ) ≤ (j : ℕ)))
          ⊆ (Finset.univ.filter (fun j'' : Fin ℓ => t ∈ aliveNat a V ((j'' : ℕ) + 1))) := by
        intro j'' hj''
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'' ⊢
        exact aliveNat_antitone a V (by omega) hj
      have hcard1 : (Finset.univ.filter (fun j'' : Fin ℓ => (j'' : ℕ) ≤ (j : ℕ))).card
          = (j : ℕ) + 1 := by
        have : (Finset.univ.filter (fun j'' : Fin ℓ => (j'' : ℕ) ≤ (j : ℕ)))
            = (Finset.univ.filter (fun j'' : Fin ℓ => (j'' : ℕ) < (j : ℕ) + 1)) := by
          apply Finset.filter_congr; intro x _; omega
        rw [this, hseg ((j:ℕ)+1) (by have := j.isLt; omega)]
      have hle := Finset.card_le_card hsub
      rw [hcard1, ← hcdef] at hle
      omega
    · -- If (j:ℕ) < c, then j must survive: else S ⊆ {j'' | (j'':ℕ) < (j:ℕ)}, card ≤ (j:ℕ).
      intro hj
      by_contra hnot
      have hsub : (Finset.univ.filter (fun j'' : Fin ℓ => t ∈ aliveNat a V ((j'' : ℕ) + 1)))
          ⊆ (Finset.univ.filter (fun j'' : Fin ℓ => (j'' : ℕ) < (j : ℕ))) := by
        intro j'' hj''
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'' ⊢
        by_contra hge
        push_neg at hge  -- hge : (j:ℕ) ≤ (j'':ℕ)
        exact hnot (aliveNat_antitone a V (by omega) hj'')
      have hle := Finset.card_le_card hsub
      rw [← hcdef, hseg (j:ℕ) (by have := j.isLt; omega)] at hle
      omega
  -- Main: t ∈ aliveNat m ↔ m ≤ c.
  cases m with
  | zero =>
    simp only [aliveNat, Finset.mem_univ, Nat.zero_le]
  | succ m' =>
    have hm'ℓ : m' < ℓ := by omega
    have := hdown ⟨m', hm'ℓ⟩
    simp only [Fin.val_mk] at this
    rw [this]; omega

/-- **Threshold-set cardinalities under the target filter.** -/
lemma aliveNat_card {ℓ s : ℕ} (hℓ : 0 < ℓ) (a : Fin ℓ → ℕ)
    (hadom : ∀ j : Fin ℓ, a j ≤ shiftPrev s a j)
    (V : (i : Fin ℓ) → Fin (shiftPrev s a i) → Bool)
    (hV : V ∈ Fintype.piFinset (wordSetA s a)) :
    (∀ m : ℕ, m ≤ ℓ → (aliveNat a V m).card = shiftPrevN s a m)
      ∧ (fun i : Fin ℓ => cLev (kInv a V) ((i : ℕ) + 1)) = a := by
  classical
  -- V's level-word has exactly `a i` trues (membership in wordSetA).
  have hVtrue : ∀ i : Fin ℓ,
      (Finset.univ.filter (fun p : Fin (shiftPrev s a i) => V i p = true)).card = a i := by
    intro i
    rw [Fintype.mem_piFinset] at hV
    have := hV i
    simpa [wordSetA] using this
  -- Card claim by induction on m.
  have hcard : ∀ m : ℕ, m ≤ ℓ → (aliveNat a V m).card = shiftPrevN s a m := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [aliveNat, shiftPrevN, Finset.card_univ, Fintype.card_fin]
    | succ m ih =>
      intro hm
      have hmℓ : m < ℓ := by omega
      have ihcard := ih (by omega)
      have hshifteq : shiftPrevN s a m = shiftPrev s a ⟨m, hmℓ⟩ := by
        cases m with
        | zero => simp [shiftPrevN, shiftPrev]
        | succ m' =>
          simp only [shiftPrevN, shiftPrev]
          rw [dif_pos (by omega : m' < ℓ)]
          rw [if_neg (by omega)]
          congr 1
      have hshiftsucc : shiftPrevN s a (m + 1) = a ⟨m, hmℓ⟩ := by
        simp only [shiftPrevN]; rw [dif_pos hmℓ]
      rw [hshiftsucc, aliveNat]
      have hAcard : (aliveNat a V m).card = shiftPrev s a ⟨m, hmℓ⟩ := by
        rw [ihcard, hshifteq]
      have hcf := card_filter_rankIn (aliveNat a V m) (fun p => padV a V m p)
      have hpred : ((aliveNat a V m).filter (fun t => padV a V m (rankIn (aliveNat a V m) t)))
          = ((aliveNat a V m).filter
              (fun t => (fun p => padV a V m p) (rankIn (aliveNat a V m) t) = true)) := by
        apply Finset.filter_congr; intro t _; simp
      rw [hpred, hcf]
      -- Rewrite the index type Fin A.card to Fin (shiftPrev s a ⟨m⟩) using hAcard.
      have hcount : (Finset.univ.filter
            (fun p : Fin (aliveNat a V m).card => (fun p => padV a V m p) (p : ℕ) = true)).card
          = (Finset.univ.filter (fun p : Fin (shiftPrev s a ⟨m, hmℓ⟩) =>
              V ⟨m, hmℓ⟩ p = true)).card := by
        apply Finset.card_bij
          (fun (p : Fin (aliveNat a V m).card) _ =>
            (⟨(p : ℕ), Nat.lt_of_lt_of_eq p.isLt hAcard⟩ : Fin (shiftPrev s a ⟨m, hmℓ⟩)))
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          have hpb : (p : ℕ) < shiftPrev s a ⟨m, hmℓ⟩ := Nat.lt_of_lt_of_eq p.isLt hAcard
          have : padV a V m (p : ℕ) = V ⟨m, hmℓ⟩ ⟨(p : ℕ), hpb⟩ := by
            unfold padV
            rw [dif_pos hmℓ, dif_pos hpb]
          rw [← this]; exact hp
        · intro p₁ _ p₂ _ hEq
          apply Fin.ext; simpa using hEq
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          have hpb : (p : ℕ) < (aliveNat a V m).card := Nat.lt_of_lt_of_eq p.isLt hAcard.symm
          have hps : (p : ℕ) < shiftPrev s a ⟨m, hmℓ⟩ := Nat.lt_of_lt_of_eq hpb hAcard
          refine ⟨⟨(p : ℕ), hpb⟩, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            have : padV a V m (p : ℕ) = V ⟨m, hmℓ⟩ ⟨(p : ℕ), hps⟩ := by
              unfold padV
              rw [dif_pos hmℓ, dif_pos hps]
            rw [this]
            convert hp using 2
          · apply Fin.ext; rfl
      rw [hcount]
      have := hVtrue ⟨m, hmℓ⟩
      convert this using 2
  refine ⟨hcard, ?_⟩
  funext i
  show cLev (kInv a V) ((i : ℕ) + 1) = a i
  have hset : (Finset.univ.filter (fun t : Fin s => (i : ℕ) + 1 ≤ (kInv a V t : ℕ)))
      = aliveNat a V ((i : ℕ) + 1) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mem_aliveNat_iff_kInv a V t (by have := i.isLt; omega)]
  rw [cLev, hset, hcard ((i : ℕ) + 1) (by have := i.isLt; omega)]
  simp only [shiftPrevN]; rw [dif_pos i.isLt]

/-- **Word reconstruction (target→source).** -/
lemma wordA_kInv {ℓ s : ℕ} (hℓ : 0 < ℓ) (a : Fin ℓ → ℕ)
    (hadom : ∀ j : Fin ℓ, a j ≤ shiftPrev s a j)
    (V : (i : Fin ℓ) → Fin (shiftPrev s a i) → Bool)
    (hV : V ∈ Fintype.piFinset (wordSetA s a)) (j : Fin ℓ) :
    wordA (onesFilling ℓ (kInv a V)) ((j : ℕ) + 1) = List.ofFn (V j) := by
  classical
  set k : Fin s → Fin (ℓ + 1) := kInv a V with hkdef
  set m : ℕ := (j : ℕ) with hmdef
  have hmℓ : m < ℓ := j.isLt
  obtain ⟨hcardAll, hk⟩ := aliveNat_card hℓ a hadom V hV
  -- The threshold set at level m.
  set A : Finset (Fin s) := Finset.univ.filter (fun u : Fin s => m ≤ (k u : ℕ)) with hAdef
  -- aliveNat a V m = A via mem_aliveNat_iff_kInv.
  have hA_eq : aliveNat a V m = A := by
    ext t
    rw [mem_aliveNat_iff_kInv a V t (by omega)]
    rw [hAdef]; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hkdef]
  -- Bridge: for t ∈ A, padV a V m (rankIn A t) = decide (m+1 ≤ k t).
  have hbridge : ∀ t : Fin s, t ∈ A →
      padV a V m (rankIn A t) = decide (m + 1 ≤ (k t : ℕ)) := by
    intro t htA
    have hmem1 : t ∈ aliveNat a V (m + 1) ↔ m + 1 ≤ (k t : ℕ) := by
      rw [mem_aliveNat_iff_kInv a V t (by omega)]
    have hstep : t ∈ aliveNat a V (m + 1)
        ↔ (t ∈ aliveNat a V m ∧ padV a V m (rankIn (aliveNat a V m) t) = true) := by
      conv_lhs => rw [aliveNat]
      rw [Finset.mem_filter]
    rw [hA_eq] at hstep
    have hbit : padV a V m (rankIn A t) = true ↔ m + 1 ≤ (k t : ℕ) := by
      rw [← hmem1, hstep]
      exact ⟨fun h => ⟨htA, h⟩, fun h => h.2⟩
    by_cases hle : m + 1 ≤ (k t : ℕ)
    · rw [decide_eq_true hle]; exact hbit.mpr hle
    · rw [decide_eq_false hle]
      cases hb : padV a V m (rankIn A t) with
      | false => rfl
      | true => exact absurd (hbit.mp hb) hle
  -- The list L and predicates.
  set L : List Row := onesFilling ℓ k with hLdef
  set P : Row → Bool := fun row => decide (m ≤ row.ones) with hPdef
  set g : Row → Bool := fun row => decide (m + 1 ≤ row.ones) with hgdef
  have hLlen : L.length = s := by rw [hLdef, onesFilling]; simp
  have hLget : ∀ t : ℕ, (ht : t < L.length) →
      (L[t]).ones = (k ⟨t, by rw [hLlen] at ht; exact ht⟩ : ℕ) := by
    intro t ht
    simp only [hLdef, onesFilling, List.getElem_ofFn]
  -- LHS = (L.filter P).map g.
  have hLHS : wordA L (m + 1) = (L.filter P).map g := by
    unfold wordA
    rw [hPdef, hgdef]
    congr 2
  rw [hLHS]
  -- length of A = shiftPrev s a j.
  have hAcard : A.card = shiftPrev s a j := by
    rw [← hA_eq, hcardAll m (by omega)]
    unfold shiftPrev
    cases hm0 : m with
    | zero =>
      simp only [shiftPrevN]
      rw [if_pos (show (j : ℕ) = 0 from by omega)]
    | succ m' =>
      simp only [shiftPrevN]
      rw [dif_pos (show m' < ℓ by omega)]
      rw [if_neg (show (j : ℕ) ≠ 0 by omega)]
      congr 1
      apply Fin.ext; simp only [Fin.val_mk]; omega
  -- length of filter L P = A.card.
  have hfilterlen : (L.filter P).length = A.card := by
    rw [hLdef, onesFilling]
    rw [length_filter_ofFn]
    rw [hAdef]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro t _
    simp only [hPdef, decide_eq_true_eq]
  -- Now prove the two lists are equal by ext_getElem?.
  apply List.ext_getElem?
  intro p
  by_cases hp : p < shiftPrev s a j
  · have hplt : p < A.card := by rw [hAcard]; exact hp
    have hpimg : p ∈ A.image (rankIn A) := by
      rw [rankIn_image]; simp only [Finset.mem_range]; exact hplt
    simp only [Finset.mem_image] at hpimg
    obtain ⟨t, htA, htrank⟩ := hpimg
    have htlt : (t : ℕ) < L.length := by rw [hLlen]; exact t.isLt
    have htAthresh : m ≤ (k t : ℕ) := by
      have := htA; rw [hAdef] at this
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have hPt : P L[(t : ℕ)] = true := by
      rw [hPdef]; simp only [decide_eq_true_eq]
      rw [hLget (t : ℕ) htlt]
      have hfix : (⟨(t : ℕ), by rw [hLlen] at htlt; exact htlt⟩ : Fin s) = t := by
        apply Fin.ext; rfl
      rw [hfix]; exact htAthresh
    have hidx : ((L.take (t : ℕ)).filter P).length = p := by
      rw [← htrank]
      rw [hLdef, onesFilling]
      rw [take_filter_ofFn_length]
      rw [rankIn, hAdef]
      apply Finset.card_bij (fun (u : Fin s) _ => u)
      · intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        refine ⟨?_, ?_⟩
        · have h2 := hu.2; rw [hPdef] at h2; simpa using h2
        · simp only [Fin.lt_def]; exact hu.1
      · intro u1 _ u2 _ h; exact h
      · intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        refine ⟨u, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · simp only [Fin.lt_def] at hu; exact hu.2
        · rw [hPdef]; simpa using hu.1
    have hrank := filter_map_getElem_rank L P g (t : ℕ) htlt hPt
    rw [hidx] at hrank
    rw [hrank]
    have hVlen : (List.ofFn (V j)).length = shiftPrev s a j := by simp
    have hpVlen : p < (List.ofFn (V j)).length := by rw [hVlen]; exact hp
    rw [List.getElem?_eq_getElem hpVlen]
    simp only [List.getElem_ofFn]
    congr 1
    rw [hgdef]
    simp only []
    rw [hLget (t : ℕ) htlt]
    have hfix : (⟨(t : ℕ), by rw [hLlen] at htlt; exact htlt⟩ : Fin s) = t := by
      apply Fin.ext; rfl
    rw [hfix]
    have hbr := hbridge t htA
    rw [htrank] at hbr
    rw [← hbr]
    have hpadeval : padV a V m p = V ⟨m, hmℓ⟩ ⟨p, hp⟩ := by
      unfold padV
      rw [dif_pos hmℓ, dif_pos hp]
    rw [hpadeval]
  · have hpc : ¬ p < ((L.filter P).map g).length := by
      rw [List.length_map, hfilterlen, hAcard]; exact hp
    have hpc2 : ¬ p < (List.ofFn (V j)).length := by
      rw [List.length_ofFn]; exact hp
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- Length of the level-`(j+1)` `wordA` word of `onesFilling ℓ k` equals `cLev k j`. -/
lemma wordA_onesFilling_length {ℓ s : ℕ} (k : Fin s → Fin (ℓ + 1)) (j : ℕ) :
    (wordA (onesFilling ℓ k) (j + 1)).length = cLev k j := by
  unfold wordA
  rw [List.length_map]
  unfold onesFilling cLev
  rw [length_filter_ofFn]
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
    Nat.add_sub_cancel]

/-- For a source `k` with level counts `cLev k (i+1) = a`, the length `cLev k j`
of the level-`(j+1)` word equals the boundary quantity `shiftPrev s a j`. -/
lemma cLev_eq_shiftPrev {ℓ s : ℕ} (a : Fin ℓ → ℕ) (k : Fin s → Fin (ℓ + 1))
    (hk : (fun i : Fin ℓ => cLev k ((i : ℕ) + 1)) = a) (j : Fin ℓ) :
    cLev k (j : ℕ) = shiftPrev s a j := by
  unfold shiftPrev
  by_cases hj : (j : ℕ) = 0
  · rw [if_pos hj, hj]
    unfold cLev
    have hh : (Finset.univ.filter (fun t : Fin s => 0 ≤ (k t : ℕ))) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro t _; exact Nat.zero_le _
    rw [hh, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hj]
    have hcong := congrFun hk ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩
    simp only at hcong
    rw [← hcong]
    congr 1
    omega

/-- **Core ones-vector level bijection.** -/
theorem fiberA_biject_core {ℓ : ℕ} (hℓ : 0 < ℓ) (s : ℕ) (a : Fin ℓ → ℕ)
    (hadom : ∀ j : Fin ℓ, a j ≤ shiftPrev s a j) :
    ∑ k ∈ (Finset.univ.filter
        (fun k : Fin s → Fin (ℓ + 1) => (fun i : Fin ℓ => cLev k ((i : ℕ) + 1)) = a)),
        q ^ (∑ i : Fin ℓ, invWord (wordA (onesFilling ℓ k) ((i : ℕ) + 1)))
      = ∑ V ∈ Fintype.piFinset (wordSetA s a),
          q ^ (∑ i : Fin ℓ, invWord (List.ofFn (V i))) := by
  classical
  set Fwd : (Fin s → Fin (ℓ + 1)) → (i : Fin ℓ) → Fin (shiftPrev s a i) → Bool :=
    fun k i p => (wordA (onesFilling ℓ k) ((i : ℕ) + 1))[(p : ℕ)]! with hFwd
  have hofFn : ∀ (k : Fin s → Fin (ℓ + 1)),
      (fun i : Fin ℓ => cLev k ((i : ℕ) + 1)) = a →
      ∀ i : Fin ℓ, List.ofFn (Fwd k i) = wordA (onesFilling ℓ k) ((i : ℕ) + 1) := by
    intro k hk i
    have hlen : (wordA (onesFilling ℓ k) ((i : ℕ) + 1)).length = shiftPrev s a i := by
      rw [wordA_onesFilling_length k (i : ℕ), cLev_eq_shiftPrev a k hk i]
    apply List.ext_getElem
    · rw [List.length_ofFn, hlen]
    · intro p hp1 hp2
      rw [List.getElem_ofFn]
      simp only [hFwd]
      rw [List.length_ofFn] at hp1
      rw [getElem!_pos _ (p : ℕ) (by rw [hlen]; exact (Fin.mk p hp1).isLt)]
  refine Finset.sum_nbij' (i := fun k => Fwd k) (j := fun V => kInv a V)
    ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [Fintype.mem_piFinset]
    intro i
    simp only [wordSetA, Finset.mem_filter, Finset.mem_univ, true_and]
    -- #{p | Fwd k i p = true} = (# trues in List.ofFn (Fwd k i))
    have hcount : (Finset.univ.filter (fun p : Fin (shiftPrev s a i) => Fwd k i p = true)).card
        = ((List.ofFn (Fwd k i)).filter (fun b => b = true)).length := by
      rw [length_filter_ofFn]
      congr 1
      apply Finset.filter_congr
      intro p _
      simp only [decide_eq_true_eq]
    rw [hcount, hofFn k hk i]
    -- count trues in the level word = # rows of onesFilling with ones ≥ i+1 = cLev k (i+1)
    have hword : ((wordA (onesFilling ℓ k) ((i : ℕ) + 1)).filter (fun b => b = true)).length
        = cLev k ((i : ℕ) + 1) := by
      unfold wordA cLev
      rw [List.filter_map, List.length_map, List.filter_filter]
      have hfe : ((onesFilling ℓ k).filter
            (fun p => ((fun b => decide (b = true)) ∘ fun p => decide ((i : ℕ) + 1 ≤ p.ones)) p &&
              decide ((i : ℕ) + 1 - 1 ≤ p.ones)))
          = (onesFilling ℓ k).filter (fun p => decide ((i : ℕ) + 1 ≤ p.ones)) := by
        apply List.filter_congr
        intro p _
        simp only [Function.comp, decide_eq_true_eq, Nat.add_sub_cancel, Bool.decide_and]
        by_cases h : (i : ℕ) + 1 ≤ p.ones
        · simp only [decide_eq_true h, decide_eq_true (show (i:ℕ) ≤ p.ones by omega),
            Bool.and_self]
        · simp only [decide_eq_false h, Bool.false_and]
      rw [hfe]
      rw [show (List.filter (fun p => decide ((i:ℕ)+1 ≤ p.ones)) (onesFilling ℓ k)).length
            = countLevel (onesFilling ℓ k) ((i:ℕ)+1) from rfl]
      rw [countLevel_onesFilling]
    rw [hword]
    exact congrFun hk i
  · intro V hV
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (aliveNat_card hℓ a hadom V hV).2
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact kInv_forward hℓ a hadom k hk (Fwd k) (hofFn k hk)
  · intro V hV
    funext i
    have hwrec : wordA (onesFilling ℓ (kInv a V)) ((i : ℕ) + 1) = List.ofFn (V i) :=
      wordA_kInv hℓ a hadom V hV i
    funext p
    simp only [hFwd]
    rw [hwrec]
    rw [getElem!_pos _ (p : ℕ) (by rw [List.length_ofFn]; exact p.isLt)]
    simp only [List.getElem_ofFn]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hofFn k hk i]

/-- **Level bijection for the A-side fiber sum.**  The sum of `q^{∑ invWord}` over
fillings of the `s`-block with level counts `a` equals the sum over tuples of
binary words (one per level, of the right length and weight) of `q^{∑ invWord}`.
This is §3.1 of `/work/fiber_informal.md`. -/
theorem fiberA_biject {ℓ : ℕ} (hℓ : 0 < ℓ) (s : ℕ) (a : Fin ℓ → ℕ)
    (hadom : ∀ j : Fin ℓ, a j ≤ shiftPrev s a j) :
    ∑ w ∈ (fillings (sBlockLens ℓ s)).filter
        (fun w => (fun i : Fin ℓ => countLevel w (i + 1)) = a),
        q ^ (∑ i : Fin ℓ, invWord (wordA w ((i : ℕ) + 1)))
      = ∑ V ∈ Fintype.piFinset (wordSetA s a),
          q ^ (∑ i : Fin ℓ, invWord (List.ofFn (V i))) := by
  rw [fiberA_source_eq s a]
  exact fiberA_biject_core hℓ s a hadom

/-- **Per-fiber weight identity (`eq:Jgf` core, `★`).**  For each `(a,z)` in
`azFinset`, the sum of `q^{Ja+Jz}` over the fiber of tableaux (either order) with
`aOf=a`, `zOf=z` equals the Gaussian weight `Bweight r s a z`. -/
theorem fiberA_sum
    (hℓ : 0 < ℓ) (hbw : BinaryWordGauss) (s : ℕ) (a : Fin ℓ → ℕ)
    (hadom : ∀ j : Fin ℓ, a j ≤ shiftPrev s a j) :
    ∑ w ∈ (fillings (sBlockLens ℓ s)).filter
        (fun w => (fun i : Fin ℓ => countLevel w (i + 1)) = a),
        q ^ (∑ i ∈ Finset.Icc 1 ℓ, invWord (wordA w i))
      = ∏ i, gauss (shiftPrev s a i) (a i) := by
  classical
  have hreindex : ∀ w : List Row,
      (∑ i ∈ Finset.Icc 1 ℓ, invWord (wordA w i))
        = ∑ i : Fin ℓ, invWord (wordA w ((i : ℕ) + 1)) := by
    intro w
    rw [Fin.sum_univ_eq_sum_range (fun i => invWord (wordA w (i + 1))) ℓ]
    have hIcc : Finset.Icc 1 ℓ = Finset.Ico 1 (ℓ + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr ?_ (fun i hi => ?_)
    · congr 1
    · rw [show 1 + i = i + 1 from by omega]
  simp_rw [hreindex]
  rw [fiberA_biject hℓ s a hadom]
  have hgauss : ∀ i : Fin ℓ,
      gauss (shiftPrev s a i) (a i)
        = ∑ v ∈ wordSetA s a i, q ^ (invWord (List.ofFn v)) := by
    intro i
    rw [hbw (shiftPrev s a i) (a i)]
    rfl
  simp_rw [hgauss]
  rw [Finset.prod_univ_sum (wordSetA s a) (fun i v => q ^ (invWord (List.ofFn v)))]
  refine Finset.sum_congr rfl (fun V hV => ?_)
  rw [← Finset.prod_pow_eq_pow_sum]

/-! ## Layer 0 for `fiberZ_sum`: reindex + local arithmetic (no survival machinery). -/

/-- Reindexing the level-sum from `Icc 1 ℓ` to `Fin ℓ` (mirror of `fiberA_sum`'s
`hreindex`). -/
lemma wordZ_Icc_to_Fin {ℓ : ℕ} (w : List Row) :
    (∑ i ∈ Finset.Icc 1 ℓ, invWord (wordZ w i))
      = ∑ i : Fin ℓ, invWord (wordZ w ((i : ℕ) + 1)) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => invWord (wordZ w (i + 1))) ℓ]
  have hIcc : Finset.Icc 1 ℓ = Finset.Ico 1 (ℓ + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr ?_ (fun i hi => ?_)
  · congr 1
  · rw [show 1 + i = i + 1 from by omega]

/-- The wordZ support length is a set difference: `#{k ≤ len ∧ ones < k+1}
= #{k ≤ len} − countLevel w (k+1)`. -/
lemma beta_support_length_sub_count (w : List Row) (k : ℕ) :
    (w.filter (fun p => decide (k ≤ p.len ∧ p.ones < k + 1))).length
      = (w.filter (fun p => decide (k ≤ p.len))).length - countLevel w (k + 1) := by
  have hsplit := length_filter_add_not
    (w.filter (fun p => decide (k ≤ p.len))) (fun p => decide (p.ones < k + 1))
  rw [List.filter_filter, List.filter_filter] at hsplit
  have h1 : (w.filter (fun a => decide (a.ones < k + 1) && decide (k ≤ a.len)))
      = w.filter (fun p => decide (k ≤ p.len ∧ p.ones < k + 1)) := by
    apply List.filter_congr; intro p _
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    tauto
  have h2 : (w.filter (fun a => (!decide (a.ones < k + 1)) && decide (k ≤ a.len))).length
      = countLevel w (k + 1) := by
    unfold countLevel
    apply congrArg List.length
    apply List.filter_congr; intro p _
    have hle := p.ones_le
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not, not_lt]
    omega
  rw [h1, h2] at hsplit
  omega

/-- The exact-level count is a set difference:
`#{ones = k} = countLevel w k − countLevel w (k+1)`. -/
lemma count_exact_level_eq_countLevel_sub (w : List Row) (k : ℕ) :
    (w.filter (fun p => decide (p.ones = k))).length
      = countLevel w k - countLevel w (k + 1) := by
  have hsplit := length_filter_add_not
    (w.filter (fun p => decide (k ≤ p.ones))) (fun p => decide (p.ones = k))
  rw [List.filter_filter, List.filter_filter] at hsplit
  have h1 : (w.filter (fun a => decide (a.ones = k) && decide (k ≤ a.ones))).length
      = (w.filter (fun p => decide (p.ones = k))).length := by
    apply congrArg List.length
    apply List.filter_congr; intro p _
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have h2 : (w.filter (fun a => (!decide (a.ones = k)) && decide (k ≤ a.ones))).length
      = countLevel w (k + 1) := by
    unfold countLevel
    apply congrArg List.length
    apply List.filter_congr; intro p _
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not]
    omega
  have hck : countLevel w k = (w.filter (fun p => decide (k ≤ p.ones))).length := rfl
  rw [h1, h2] at hsplit
  rw [hck]; omega

/-- Membership in `fillings Ls` is exactly having row-length list `Ls`. -/
lemma mem_fillings_iff_map_len_eq (Ls : List ℕ) (w : List Row) :
    w ∈ fillings Ls ↔ w.map Row.len = Ls := by
  induction Ls generalizing w with
  | nil =>
    simp only [fillings, Finset.mem_singleton]
    constructor
    · intro h; subst h; simp
    · intro h; exact List.map_eq_nil_iff.mp h
  | cons L Ls ih =>
    simp only [fillings, Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨⟨p, ws⟩, ⟨hp, hws⟩, rfl⟩
      rw [List.map_cons, mem_rowsOfLen hp, (ih ws).mp hws]
    · intro h
      obtain ⟨p, ws, rfl⟩ := List.exists_cons_of_ne_nil (l := w) (by
        rintro rfl; simp at h)
      rw [List.map_cons] at h
      simp only [List.cons.injEq] at h
      refine ⟨(p, ws), ⟨?_, ?_⟩, rfl⟩
      · rw [mem_rowsOfLen_iff]; exact h.1
      · exact (ih ws).mpr h.2

/-! ## Layer 1 for `fiberZ_sum`: target word set, length, true-count. -/

/-- The binary-word target set for beta-side level `i`: words `v : Fin (r i −
shiftNext z i) → Bool` with exactly `z i − shiftNext z i` true bits.  Mirror of
`wordSetA`. -/
noncomputable def wordSetZ (r z : Fin ℓ → ℕ) (i : Fin ℓ) :
    Finset (Fin (r i - shiftNext z i) → Bool) :=
  Finset.univ.filter (fun v =>
    (Finset.univ.filter (fun p => v p = true)).card = z i - shiftNext z i)

/-- The count at level `i+2` equals `shiftNext z i`, using the level profile of a
beta filling and the boundary vanishing `countLevel w (ℓ+1) = 0`. -/
lemma next_count_eq_shiftNext (w : List Row) (hw : w ∈ fillings (betaParts r))
    (z : Fin ℓ → ℕ) (hz : (fun i : Fin ℓ => countLevel w ((i : ℕ) + 1)) = z)
    (i : Fin ℓ) :
    countLevel w ((i : ℕ) + 2) = shiftNext z i := by
  -- all beta rows have len ≤ ℓ, hence ones ≤ ℓ, so countLevel w (ℓ+1) = 0.
  have hlenℓ : ∀ p ∈ w, p.len ≤ ℓ := by
    intro p hp
    have := mem_fillings_mem_len _ _ hw p hp
    simp only [betaParts, List.mem_map, List.mem_range] at this
    obtain ⟨c, hc, hcard⟩ := this
    rw [← hcard]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hbound : countLevel w (ℓ + 1) = 0 := by
    unfold countLevel
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro p hp
    have hle := hlenℓ p hp
    have := p.ones_le
    simp only [decide_eq_true_eq]
    omega
  unfold shiftNext
  by_cases h : (i : ℕ) + 1 = ℓ
  · rw [dif_pos h]
    rw [show (i : ℕ) + 2 = ℓ + 1 from by omega]
    exact hbound
  · rw [dif_neg h]
    have := congrFun hz ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩
    simp only [Fin.val_mk] at this
    rw [show (i : ℕ) + 2 = ((i : ℕ) + 1) + 1 from by omega]
    exact this

/-- The wordZ level-`i` word has length `r i − shiftNext z i`. -/
lemma wordZ_length (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i) (w : List Row)
    (hw : w ∈ fillings (betaParts r)) (z : Fin ℓ → ℕ)
    (hz : (fun i : Fin ℓ => countLevel w ((i : ℕ) + 1)) = z) (i : Fin ℓ) :
    (wordZ w ((i : ℕ) + 1)).length = r i - shiftNext z i := by
  unfold wordZ
  rw [List.length_map]
  rw [beta_support_length_sub_count w ((i : ℕ) + 1)]
  have hlen : (w.filter (fun p => decide ((i : ℕ) + 1 ≤ p.len))).length = r i := by
    rw [show (w.filter (fun p => decide ((i : ℕ) + 1 ≤ p.len))).length
          = (w.filter (fun p => (i : ℕ) + 1 ≤ p.len)).length from rfl]
    rw [betaLenCount r hr w hw ((i : ℕ) + 1) (by omega) (by have := i.isLt; omega)]
    have hfe : (⟨(i : ℕ) + 1 - 1, by have := i.isLt; omega⟩ : Fin ℓ) = i :=
      Fin.ext (by simp)
    rw [hfe]
  rw [hlen]
  have hnext := next_count_eq_shiftNext r w hw z hz i
  rw [show (i : ℕ) + 1 + 1 = (i : ℕ) + 2 from by omega, hnext]

/-- The wordZ level-`i` word has `z i − shiftNext z i` true bits. -/
lemma wordZ_true_count (w : List Row) (hw : w ∈ fillings (betaParts r))
    (z : Fin ℓ → ℕ) (hz : (fun i : Fin ℓ => countLevel w ((i : ℕ) + 1)) = z)
    (i : Fin ℓ) :
    ((wordZ w ((i : ℕ) + 1)).filter (fun b => b = true)).length
      = z i - shiftNext z i := by
  unfold wordZ
  rw [List.filter_map, List.length_map, List.filter_filter]
  -- collapse the merged predicate to {ones = i+1}
  have hfe : (w.filter (fun p =>
        ((fun b => decide (b = true)) ∘ fun p => decide (p.ones = (i : ℕ) + 1)) p
          && decide ((i : ℕ) + 1 ≤ p.len ∧ p.ones < (i : ℕ) + 1 + 1)))
      = w.filter (fun p => decide (p.ones = (i : ℕ) + 1)) := by
    apply List.filter_congr
    intro p _
    have hle := p.ones_le
    rw [Bool.eq_iff_iff]
    simp only [Function.comp, Bool.and_eq_true, decide_eq_true_eq]
    omega
  rw [hfe]
  rw [show (w.filter (fun p => decide (p.ones = (i : ℕ) + 1))).length
        = countLevel w ((i : ℕ) + 1) - countLevel w ((i : ℕ) + 1 + 1) from
      count_exact_level_eq_countLevel_sub w ((i : ℕ) + 1)]
  have hz' := congrFun hz i
  rw [hz']
  have hnext := next_count_eq_shiftNext r w hw z hz i
  rw [show (i : ℕ) + 1 + 1 = (i : ℕ) + 2 from by omega, hnext]

/-! ## Layer 2 for `fiberZ_sum`: forward map into the target word set. -/

/-- Forward map: the level-`i` word of `w`, read as a function `Fin (r i −
shiftNext z i) → Bool`.  Mirror of `Fwd` in `fiberA_biject_core`. -/
noncomputable def FwdZ (r z : Fin ℓ → ℕ) (w : List Row) (i : Fin ℓ) :
    Fin (r i - shiftNext z i) → Bool :=
  fun p => (wordZ w ((i : ℕ) + 1))[(p : ℕ)]!

/-- `List.ofFn (FwdZ r z w i) = wordZ w (i+1)`.  Mirror of `hofFn`. -/
lemma FwdZ_ofFn (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i) (w : List Row)
    (hw : w ∈ fillings (betaParts r)) (z : Fin ℓ → ℕ)
    (hz : (fun i : Fin ℓ => countLevel w ((i : ℕ) + 1)) = z) (i : Fin ℓ) :
    List.ofFn (FwdZ r z w i) = wordZ w ((i : ℕ) + 1) := by
  have hlen : (wordZ w ((i : ℕ) + 1)).length = r i - shiftNext z i :=
    wordZ_length r hr w hw z hz i
  apply List.ext_getElem
  · rw [List.length_ofFn, hlen]
  · intro p hp1 hp2
    rw [List.getElem_ofFn]
    simp only [FwdZ]
    rw [List.length_ofFn] at hp1
    rw [getElem!_pos _ (p : ℕ) (by rw [hlen]; exact (Fin.mk p hp1).isLt)]

/-- `FwdZ r z w i ∈ wordSetZ r z i`.  Mirror of the first `sum_nbij'` clause. -/
lemma FwdZ_mem_wordSetZ (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i) (w : List Row)
    (hw : w ∈ fillings (betaParts r)) (z : Fin ℓ → ℕ)
    (hz : (fun i : Fin ℓ => countLevel w ((i : ℕ) + 1)) = z) (i : Fin ℓ) :
    FwdZ r z w i ∈ wordSetZ r z i := by
  classical
  simp only [wordSetZ, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcount : (Finset.univ.filter
        (fun p : Fin (r i - shiftNext z i) => FwdZ r z w i p = true)).card
      = ((List.ofFn (FwdZ r z w i)).filter (fun b => b = true)).length := by
    rw [length_filter_ofFn]
    congr 1
    apply Finset.filter_congr
    intro p _
    simp only [decide_eq_true_eq]
  rw [hcount, FwdZ_ofFn r hr w hw z hz i]
  exact wordZ_true_count r w hw z hz i

/-! ## Layer 3 for `fiberZ_sum`: descending-birth survival machinery. -/

/-- Static length of beta-column `c`. -/
def betaLenAt (r : Fin ℓ → ℕ) (c : Fin (betaParts r).length) : ℕ := (betaParts r)[c]

/-- The length gate at math level `i+1`: columns of length `≥ i+1`. -/
noncomputable def PZ (r : Fin ℓ → ℕ) (i : Fin ℓ) :
    Finset (Fin (betaParts r).length) :=
  Finset.univ.filter (fun c => (i : ℕ) + 1 ≤ betaLenAt r c)

/-- `V` as a plain doubly-indexed boolean, `false` outside the valid ranges. -/
def padVZ (r z : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool) (i : Fin ℓ) (p : ℕ) : Bool :=
  if hp : p < r i - shiftNext z i then V i ⟨p, hp⟩ else false

/-- Descending-birth survival recursion.  `aliveZAux r z V n` is `B_{ℓ+1-n}`, the
set of columns still "born" after processing the top `n` levels (`k = ℓ, …,
ℓ+1-n`).  Structural recursion over `n` (number of levels processed).  Sealed:
never unfold this directly after `aliveZ_eq_step`. -/
noncomputable def aliveZAux (r z : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool) :
    ℕ → Finset (Fin (betaParts r).length)
  | 0 => ∅
  | (n + 1) =>
      if hn : n < ℓ then
        let i : Fin ℓ := ⟨ℓ - 1 - n, by omega⟩
        let Bnext := aliveZAux r z V n
        let A := (PZ r i).filter (fun c => c ∉ Bnext)
        Bnext ∪ A.filter (fun c => padVZ r z V i (rankIn A c))
      else aliveZAux r z V n

/-- `aliveZ r z V i = B_{i+2}` (the block just *above* level `i+1`).  Equivalently
the columns born after processing levels `k = ℓ, …, i+2`.  It is the "next" block
in the birth recursion, matching `shiftNext z i`. -/
noncomputable def aliveZ (r z : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool) (i : Fin ℓ) :
    Finset (Fin (betaParts r).length) :=
  aliveZAux r z V (ℓ - (i : ℕ))

/-- The block above `aliveZ` (i.e. `B_{i+2}`): empty at the top level. -/
noncomputable def aliveZNext (r z : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool) (i : Fin ℓ) :
    Finset (Fin (betaParts r).length) :=
  aliveZAux r z V (ℓ - 1 - (i : ℕ))

/-- **Workhorse step lemma.**  Unfold the birth recursion at level `i`: `aliveZ`
at level `i` is the block `aliveZNext` at level `i` unioned with the births at
level `i`.  After this, `aliveZAux` need never be unfolded again. -/
lemma aliveZ_eq_step (hℓ : 0 < ℓ) (z : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool) (i : Fin ℓ) :
    aliveZ r z V i =
      (let Bn := aliveZNext r z V i;
       let A := (PZ r i).filter (fun c => c ∉ Bn);
       Bn ∪ A.filter (fun c => padVZ r z V i (rankIn A c))) := by
  have hi := i.isLt
  unfold aliveZ
  rw [show ℓ - (i : ℕ) = (ℓ - 1 - (i : ℕ)) + 1 from by omega]
  rw [aliveZAux]
  have hn : ℓ - 1 - (i : ℕ) < ℓ := by omega
  rw [dif_pos hn]
  -- the index inside is ⟨ℓ - 1 - (ℓ-1-i), _⟩ = i
  have hidx : (⟨ℓ - 1 - (ℓ - 1 - (i : ℕ)), by omega⟩ : Fin ℓ) = i := by
    apply Fin.ext; simp only [Fin.val_mk]; omega
  simp only [hidx]
  -- the Bnext inside is aliveZAux r z V (ℓ-1-i) = aliveZNext at i.
  show aliveZAux r z V (ℓ - 1 - (i : ℕ)) ∪ _ = _
  unfold aliveZNext
  rfl

/-- `aliveZAux` grows monotonically in the number of processed levels: each step
unions in new births. -/
lemma aliveZAux_mono (z : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool) (n : ℕ) :
    aliveZAux r z V n ⊆ aliveZAux r z V (n + 1) := by
  intro c hc
  rw [aliveZAux]
  by_cases hn : n < ℓ
  · rw [dif_pos hn]
    exact Finset.mem_union_left _ hc
  · rw [dif_neg hn]
    exact hc

/-- `aliveZAux` is monotone: `m ≤ n → aliveZAux m ⊆ aliveZAux n`. -/
lemma aliveZAux_mono_le (z : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool) {m n : ℕ} (hmn : m ≤ n) :
    aliveZAux r z V m ⊆ aliveZAux r z V n := by
  induction n with
  | zero => simp only [Nat.le_zero] at hmn; subst hmn; exact Finset.Subset.refl _
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with h | h
    · exact (ih (by omega)).trans (aliveZAux_mono r z V k)
    · have : m = k + 1 := by omega
      subst this; exact Finset.Subset.refl _

/-- `#{c : Fin L.length | P L[c]} = (L.filter P).length`.  Pure list identity. -/
lemma card_filter_fin_get_eq_length_filter {α : Type*} (L : List α) (P : α → Bool) :
    (Finset.univ.filter (fun c : Fin L.length => P L[c])).card
      = (L.filter P).length := by
  classical
  conv_rhs => rw [← List.ofFn_getElem (xs := L)]
  rw [length_filter_ofFn (fun i : Fin L.length => L[(i : ℕ)]) P]
  simp only [Fin.getElem_fin]

/-- `PZ` is antitone in the level: higher levels are subsets. -/
lemma PZ_antitone {i j : Fin ℓ} (hij : (i : ℕ) ≤ (j : ℕ)) :
    PZ r j ⊆ PZ r i := by
  intro c hc
  simp only [PZ, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  omega

/-- `|P_k| = r_i`: exactly `r i` beta-columns have length `≥ i+1`. -/
lemma PZ_card (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i) (i : Fin ℓ) :
    (PZ r i).card = r i := by
  classical
  unfold PZ betaLenAt
  have hconv : (Finset.univ.filter
        (fun c : Fin (betaParts r).length => (i : ℕ) + 1 ≤ (betaParts r)[c])).card
      = (Finset.univ.filter
        (fun c : Fin (betaParts r).length => decide ((i : ℕ) + 1 ≤ (betaParts r)[c]) = true)).card := by
    congr 1
    apply Finset.filter_congr
    intro c _
    simp only [decide_eq_true_eq]
  rw [hconv]
  rw [card_filter_fin_get_eq_length_filter (betaParts r) (fun c => decide ((i : ℕ) + 1 ≤ c))]
  rw [betaParts_filter_count r hr ((i : ℕ) + 1) (by omega) (by have := i.isLt; omega)]
  have hfe : (⟨(i : ℕ) + 1 - 1, by have := i.isLt; omega⟩ : Fin ℓ) = i := Fin.ext (by simp)
  rw [hfe]


/-! ## Layer 4 for `fiberZ_sum`: target-side invariants (mirror `aliveNat_card`). -/

/-- The number of true bits of `V i` equals `z i − shiftNext z i` (membership in
`wordSetZ`). -/
lemma V_true_count (z : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool)
    (hV : V ∈ Fintype.piFinset (wordSetZ r z)) (i : Fin ℓ) :
    (Finset.univ.filter (fun p : Fin (r i - shiftNext z i) => V i p = true)).card
      = z i - shiftNext z i := by
  rw [Fintype.mem_piFinset] at hV
  have := hV i
  simpa [wordSetZ] using this

/-- Core birth-recursion invariant, by induction on `n = ℓ - i`.  For every level
`i`, the survival set `aliveZ i` has card `z i` and is contained in `PZ i`. -/
lemma aliveZ_card_core (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (z : Fin ℓ → ℕ) (hzr : ∀ j : Fin ℓ, z j ≤ r j)
    (hzdom : ∀ j : Fin ℓ, shiftNext z j ≤ z j)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool)
    (hV : V ∈ Fintype.piFinset (wordSetZ r z)) :
    ∀ n : ℕ, ∀ i : Fin ℓ, (ℓ : ℕ) - (i : ℕ) = n →
      (aliveZ r z V i).card = z i ∧ aliveZ r z V i ⊆ PZ r i := by
  classical
  -- V's level-word has exactly z i - shiftNext z i trues.
  have hVtrue : ∀ i : Fin ℓ,
      (Finset.univ.filter (fun p : Fin (r i - shiftNext z i) => V i p = true)).card
        = z i - shiftNext z i := V_true_count r z V hV
  intro n
  induction n with
  | zero =>
    intro i hik
    exact absurd hik (by have := i.isLt; omega)
  | succ k ih =>
    intro i hik
    -- Decompose aliveZ at level i.
    rw [aliveZ_eq_step r hℓ z V i]
    have hi := i.isLt
    -- Identify Bn = aliveZNext i and get its card + PZ-subset from IH.
    have hBncard : (aliveZNext r z V i).card = shiftNext z i ∧ aliveZNext r z V i ⊆ PZ r i := by
      by_cases htop : (i : ℕ) + 1 < ℓ
      · set i1 : Fin ℓ := ⟨(i : ℕ) + 1, htop⟩ with hi1
        have heq : aliveZNext r z V i = aliveZ r z V i1 := by
          unfold aliveZNext aliveZ
          congr 1
          simp only [hi1]; omega
        have hik1 : (ℓ : ℕ) - (i1 : ℕ) = k := by simp only [hi1]; omega
        have hih := ih i1 hik1
        have hsn : shiftNext z i = z i1 := by
          unfold shiftNext; rw [dif_neg (by omega)]
        refine ⟨?_, ?_⟩
        · rw [heq, hih.1, hsn]
        · rw [heq]; exact hih.2.trans (PZ_antitone r (by simp only [hi1]; omega))
      · have hitop : (i : ℕ) + 1 = ℓ := by omega
        have heq : aliveZNext r z V i = ∅ := by
          unfold aliveZNext
          have : ℓ - 1 - (i : ℕ) = 0 := by omega
          rw [this]; rfl
        have hsn : shiftNext z i = 0 := by unfold shiftNext; rw [dif_pos hitop]
        refine ⟨?_, ?_⟩
        · rw [heq, hsn]; simp
        · rw [heq]; exact Finset.empty_subset _
    obtain ⟨hBncard, hBnsub⟩ := hBncard
    -- Abbreviations matching the `let`s introduced by aliveZ_eq_step.
    set Bn := aliveZNext r z V i with hBndef
    set A := (PZ r i).filter (fun c => c ∉ Bn) with hAdef
    -- A = PZ i \ Bn.
    have hAsdiff : A = (PZ r i) \ Bn := by
      ext c; simp only [hAdef, Finset.mem_filter, Finset.mem_sdiff]
    have hAcard : A.card = r i - shiftNext z i := by
      rw [hAsdiff, Finset.card_sdiff_of_subset hBnsub, PZ_card r hr i, hBncard]
    -- births set.
    set births := A.filter (fun c => padVZ r z V i (rankIn A c)) with hbirthdef
    -- births.card = z i - shiftNext z i.
    have hbirthcard : births.card = z i - shiftNext z i := by
      have hcf := card_filter_rankIn A (fun p => padVZ r z V i p)
      have hpred : A.filter (fun c => padVZ r z V i (rankIn A c))
          = A.filter (fun c => (fun p => padVZ r z V i p) (rankIn A c) = true) := by
        apply Finset.filter_congr; intro c _; simp
      rw [hbirthdef, hpred, hcf]
      -- recast Fin A.card ≃ Fin (r i - shiftNext z i) and use hVtrue.
      have hcount : (Finset.univ.filter
            (fun p : Fin A.card => (fun p => padVZ r z V i p) (p : ℕ) = true)).card
          = (Finset.univ.filter (fun p : Fin (r i - shiftNext z i) =>
              V i p = true)).card := by
        apply Finset.card_bij
          (fun (p : Fin A.card) _ =>
            (⟨(p : ℕ), Nat.lt_of_lt_of_eq p.isLt hAcard⟩ : Fin (r i - shiftNext z i)))
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          have hpb : (p : ℕ) < r i - shiftNext z i := Nat.lt_of_lt_of_eq p.isLt hAcard
          have hpv : padVZ r z V i (p : ℕ) = V i ⟨(p : ℕ), hpb⟩ := by
            unfold padVZ; rw [dif_pos hpb]
          rw [← hpv]; exact hp
        · intro p₁ _ p₂ _ hEq
          apply Fin.ext; simpa using hEq
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          have hpb : (p : ℕ) < A.card := Nat.lt_of_lt_of_eq p.isLt hAcard.symm
          have hps : (p : ℕ) < r i - shiftNext z i := Nat.lt_of_lt_of_eq hpb hAcard
          refine ⟨⟨(p : ℕ), hpb⟩, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            have hpv : padVZ r z V i (p : ℕ) = V i ⟨(p : ℕ), hps⟩ := by
              unfold padVZ; rw [dif_pos hps]
            rw [hpv]; convert hp using 2
          · apply Fin.ext; rfl
      rw [hcount]; exact hVtrue i
    -- The union is disjoint (births ⊆ A ⊆ complement of Bn).
    have hdisj : Disjoint Bn births := by
      rw [Finset.disjoint_left]
      intro c hcBn hcbirth
      have : c ∈ A := Finset.mem_of_mem_filter c hcbirth
      rw [hAsdiff, Finset.mem_sdiff] at this
      exact this.2 hcBn
    refine ⟨?_, ?_⟩
    · -- card of union.
      rw [Finset.card_union_of_disjoint hdisj, hBncard, hbirthcard]
      have := hzdom i
      omega
    · -- subset of PZ i.
      intro c hc
      rw [Finset.mem_union] at hc
      rcases hc with hc | hc
      · exact hBnsub hc
      · have : c ∈ A := Finset.mem_of_mem_filter c hc
        rw [hAsdiff, Finset.mem_sdiff] at this
        exact this.1


/-- **Threshold-set cardinalities under the target filter (Z-side).**  Mirror of
`aliveNat_card`, top-down. -/
lemma aliveZ_card_subset (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (z : Fin ℓ → ℕ) (hzr : ∀ j : Fin ℓ, z j ≤ r j)
    (hzdom : ∀ j : Fin ℓ, shiftNext z j ≤ z j)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool)
    (hV : V ∈ Fintype.piFinset (wordSetZ r z)) :
    (∀ i : Fin ℓ, (aliveZ r z V i).card = z i)
      ∧ (∀ i : Fin ℓ, aliveZ r z V i ⊆ PZ r i)
      ∧ (∀ i : Fin ℓ, aliveZNext r z V i ⊆ PZ r i)
      ∧ (∀ i : Fin ℓ,
          ((PZ r i).filter (fun c => c ∉ aliveZNext r z V i)).card = r i - shiftNext z i) := by
  classical
  have core := aliveZ_card_core r hℓ hr z hzr hzdom V hV
  -- card and PZ-subset for aliveZ at every level.
  have hcard : ∀ i : Fin ℓ, (aliveZ r z V i).card = z i := fun i =>
    (core ((ℓ : ℕ) - (i : ℕ)) i rfl).1
  have hsub : ∀ i : Fin ℓ, aliveZ r z V i ⊆ PZ r i := fun i =>
    (core ((ℓ : ℕ) - (i : ℕ)) i rfl).2
  -- Identify aliveZNext i with aliveZ (i+1) (or ∅ at the top level).
  -- shiftNext z i and the card of aliveZNext.
  have hnextcard : ∀ i : Fin ℓ, (aliveZNext r z V i).card = shiftNext z i := by
    intro i
    have hi := i.isLt
    by_cases htop : (i : ℕ) + 1 < ℓ
    · -- aliveZNext i = aliveZ ⟨i+1⟩ ; shiftNext z i = z ⟨i+1⟩
      set i1 : Fin ℓ := ⟨(i : ℕ) + 1, htop⟩ with hi1
      have heq : aliveZNext r z V i = aliveZ r z V i1 := by
        unfold aliveZNext aliveZ
        congr 1
        simp only [hi1]; omega
      have hsn : shiftNext z i = z i1 := by
        unfold shiftNext
        rw [dif_neg (by omega)]
      rw [heq, hcard i1, hsn]
    · -- i is the top level: aliveZNext i = ∅, shiftNext z i = 0.
      have hitop : (i : ℕ) + 1 = ℓ := by omega
      have heq : aliveZNext r z V i = ∅ := by
        unfold aliveZNext
        have : ℓ - 1 - (i : ℕ) = 0 := by omega
        rw [this]; rfl
      have hsn : shiftNext z i = 0 := by
        unfold shiftNext; rw [dif_pos hitop]
      rw [heq, hsn]; simp
  -- aliveZNext i ⊆ PZ i.
  have hnextsub : ∀ i : Fin ℓ, aliveZNext r z V i ⊆ PZ r i := by
    intro i
    have hi := i.isLt
    by_cases htop : (i : ℕ) + 1 < ℓ
    · set i1 : Fin ℓ := ⟨(i : ℕ) + 1, htop⟩ with hi1
      have heq : aliveZNext r z V i = aliveZ r z V i1 := by
        unfold aliveZNext aliveZ
        congr 1
        simp only [hi1]; omega
      rw [heq]
      exact (hsub i1).trans (PZ_antitone r (by simp only [hi1]; omega))
    · have heq : aliveZNext r z V i = ∅ := by
        unfold aliveZNext
        have : ℓ - 1 - (i : ℕ) = 0 := by omega
        rw [this]; rfl
      rw [heq]; exact Finset.empty_subset _
  refine ⟨hcard, hsub, hnextsub, ?_⟩
  intro i
  have hfilter : (PZ r i).filter (fun c => c ∉ aliveZNext r z V i)
      = (PZ r i) \ (aliveZNext r z V i) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_sdiff]
  rw [hfilter, Finset.card_sdiff_of_subset (hnextsub i), PZ_card r hr i, hnextcard i]

/-! ## Layer 5 for `fiberZ_sum`: reconstruction + nestedness (mirror `kInv`). -/

/-- The reconstructed `ones` value of beta-column `c`: the number of levels at
which `c` is alive.  Mirror of `kInv`. -/
noncomputable def kInvZ (r z : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool)
    (c : Fin (betaParts r).length) : ℕ :=
  (Finset.univ.filter (fun i : Fin ℓ => c ∈ aliveZ r z V i)).card

/-- `aliveZ` is antitone going *down* in level: higher-level survival is contained
in lower-level survival. -/
lemma aliveZ_mono_down (hℓ : 0 < ℓ)
    (z : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool)
    {i j : Fin ℓ} (hij : i ≤ j) :
    aliveZ r z V j ⊆ aliveZ r z V i := by
  unfold aliveZ
  apply aliveZAux_mono_le
  have := Fin.le_iff_val_le_val.mp hij
  omega

/-- `c ∈ aliveZ r z V i ↔ i+1 ≤ kInvZ r z V c`.  Mirror of
`mem_aliveNat_iff_kInv`. -/
lemma mem_aliveZ_iff_kInvZ (hℓ : 0 < ℓ)
    (z : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool)
    (c : Fin (betaParts r).length) (i : Fin ℓ) :
    c ∈ aliveZ r z V i ↔ (i : ℕ) + 1 ≤ kInvZ r z V c := by
  classical
  set c0 : ℕ := kInvZ r z V c with hc0
  have hc0def : c0 = (Finset.univ.filter (fun j : Fin ℓ => c ∈ aliveZ r z V j)).card := by
    simp only [hc0, kInvZ]
  -- Cardinality of an initial segment of Fin ℓ.
  have hseg : ∀ N : ℕ, N ≤ ℓ →
      (Finset.univ.filter (fun j : Fin ℓ => (j : ℕ) < N)).card = N := by
    intro N hN
    conv_rhs => rw [← Finset.card_range N]
    apply Finset.card_bij (fun (j : Fin ℓ) _ => (j : ℕ)) (t := Finset.range N)
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_range]; exact hj
    · intro j1 _ j2 _ h; exact Fin.ext h
    · intro n hn
      simp only [Finset.mem_range] at hn
      refine ⟨⟨n, by omega⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hn
  -- Membership at level j is a down-closed initial segment in j.
  have hdown : ∀ j : Fin ℓ, c ∈ aliveZ r z V j ↔ (j : ℕ) < c0 := by
    intro j
    constructor
    · intro hj
      by_contra hlt
      push_neg at hlt  -- hlt : c0 ≤ (j:ℕ)
      have hsub : (Finset.univ.filter (fun j'' : Fin ℓ => (j'' : ℕ) ≤ (j : ℕ)))
          ⊆ (Finset.univ.filter (fun j'' : Fin ℓ => c ∈ aliveZ r z V j'')) := by
        intro j'' hj''
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'' ⊢
        exact aliveZ_mono_down r hℓ z V
          (show j'' ≤ j from Fin.le_iff_val_le_val.mpr hj'') hj
      have hcard1 : (Finset.univ.filter (fun j'' : Fin ℓ => (j'' : ℕ) ≤ (j : ℕ))).card
          = (j : ℕ) + 1 := by
        have hh : (Finset.univ.filter (fun j'' : Fin ℓ => (j'' : ℕ) ≤ (j : ℕ)))
            = (Finset.univ.filter (fun j'' : Fin ℓ => (j'' : ℕ) < (j : ℕ) + 1)) := by
          apply Finset.filter_congr; intro x _; omega
        rw [hh, hseg ((j:ℕ)+1) (by have := j.isLt; omega)]
      have hle := Finset.card_le_card hsub
      rw [hcard1, ← hc0def] at hle
      omega
    · intro hj
      by_contra hnot
      have hsub : (Finset.univ.filter (fun j'' : Fin ℓ => c ∈ aliveZ r z V j''))
          ⊆ (Finset.univ.filter (fun j'' : Fin ℓ => (j'' : ℕ) < (j : ℕ))) := by
        intro j'' hj''
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'' ⊢
        by_contra hge
        push_neg at hge  -- hge : (j:ℕ) ≤ (j'':ℕ)
        exact hnot (aliveZ_mono_down r hℓ z V
          (show j ≤ j'' from Fin.le_iff_val_le_val.mpr hge) hj'')
      have hle := Finset.card_le_card hsub
      rw [← hc0def, hseg (j:ℕ) (by have := j.isLt; omega)] at hle
      omega
  rw [hdown i]; omega

/-- The reconstructed `ones` value never exceeds the static column length. -/
lemma kInvZ_le_len (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (z : Fin ℓ → ℕ) (hzr : ∀ j : Fin ℓ, z j ≤ r j)
    (hzdom : ∀ j : Fin ℓ, shiftNext z j ≤ z j)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool)
    (hV : V ∈ Fintype.piFinset (wordSetZ r z))
    (c : Fin (betaParts r).length) :
    kInvZ r z V c ≤ betaLenAt r c := by
  classical
  set u : ℕ := kInvZ r z V c with hu
  -- kInvZ is a cardinality of a subset of Fin ℓ, hence ≤ ℓ.
  have huℓ : u ≤ ℓ := by
    rw [hu, kInvZ]
    calc (Finset.univ.filter (fun i : Fin ℓ => c ∈ aliveZ r z V i)).card
        ≤ (Finset.univ : Finset (Fin ℓ)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = ℓ := by simp
  rcases Nat.eq_zero_or_pos u with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · -- u > 0 : the column c survives up to level u-1 ≤ ℓ-1.
    have hlt : u - 1 < ℓ := by omega
    set i0 : Fin ℓ := ⟨u - 1, hlt⟩ with hi0
    have hmem : c ∈ aliveZ r z V i0 := by
      rw [mem_aliveZ_iff_kInvZ r hℓ z V c i0]
      rw [← hu]; simp only [hi0]; omega
    have hsub := (aliveZ_card_subset r hℓ hr z hzr hzdom V hV).2.1 i0 hmem
    simp only [PZ, Finset.mem_filter, Finset.mem_univ, true_and, hi0] at hsub
    omega

/-- Reconstructed beta filling (target→source).  Total in `V`; uses `min` with the
static length so `ones ≤ len` holds unconditionally, and `kInvZ_le_len` shows the
`min` is inert on the domain. -/
noncomputable def invRowsZ (r z : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool) : List Row :=
  List.ofFn (fun c : Fin (betaParts r).length =>
    (⟨betaLenAt r c, min (kInvZ r z V c) (betaLenAt r c), Nat.min_le_right _ _⟩ : Row))

/-- `invRowsZ` is a beta filling. -/
lemma invRowsZ_mem (z : Fin ℓ → ℕ)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool) :
    invRowsZ r z V ∈ fillings (betaParts r) := by
  rw [mem_fillings_iff_map_len_eq]
  rw [invRowsZ, List.map_ofFn]
  show List.ofFn (fun c : Fin (betaParts r).length => (betaParts r)[c]) = betaParts r
  exact List.ofFn_getElem (xs := betaParts r)

/-! ## Layer 6 for `fiberZ_sum`: round trips. -/

/-- Length equality between a beta filling `w` and its shape list. -/
lemma fillings_length_eq (w : List Row) (hw : w ∈ fillings (betaParts r)) :
    w.length = (betaParts r).length := by
  have := (mem_fillings_iff_map_len_eq (betaParts r) w).mp hw
  rw [← this, List.length_map]

/-- For a beta filling `w`, the row at column `c` has length `betaLenAt r c`. -/
lemma fillings_getElem_len (w : List Row) (hw : w ∈ fillings (betaParts r))
    (c : Fin (betaParts r).length) :
    (w[(c : ℕ)]!).len = betaLenAt r c := by
  have hmap := (mem_fillings_iff_map_len_eq (betaParts r) w).mp hw
  have hwlen : w.length = (betaParts r).length := fillings_length_eq r w hw
  have hclt : (c : ℕ) < w.length := by rw [hwlen]; exact c.isLt
  rw [getElem!_pos w (c : ℕ) hclt]
  have : (w.map Row.len)[(c : ℕ)]'(by rw [List.length_map]; exact hclt) = w[(c : ℕ)].len :=
    List.getElem_map _
  rw [betaLenAt]
  rw [← this]
  try congr 1
  try exact hmap.symm ▸ rfl

/-- **Forward padval bridge (Z-side).**  For a beta filling `w` with level profile
`z`, and a column `c` in the level-`i` `wordZ` support set `A`, the padded value of
the forward word `FwdZ r z w` at the rank of `c` in `A` equals whether `w[c]!.ones`
is exactly `i+1`.  Mirror of `aliveNat_forward_padval`. -/
lemma aliveZ_forward_padval (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (w : List Row) (hw : w ∈ fillings (betaParts r)) (z : Fin ℓ → ℕ)
    (hz : (fun i : Fin ℓ => countLevel w ((i : ℕ) + 1)) = z) (i : Fin ℓ)
    (c : Fin (betaParts r).length)
    (hc : c ∈ Finset.univ.filter (fun c : Fin (betaParts r).length =>
            (i : ℕ) + 1 ≤ betaLenAt r c ∧ (w[(c : ℕ)]!).ones < (i : ℕ) + 2)) :
    padVZ r z (FwdZ r z w) i (rankIn
        (Finset.univ.filter (fun c : Fin (betaParts r).length =>
          (i : ℕ) + 1 ≤ betaLenAt r c ∧ (w[(c : ℕ)]!).ones < (i : ℕ) + 2)) c)
      = decide ((w[(c : ℕ)]!).ones = (i : ℕ) + 1) := by
  classical
  set V := FwdZ r z w with hVdef
  have hwlen : w.length = (betaParts r).length := fillings_length_eq r w hw
  -- concrete predicate on list positions
  set Pw : Row → Bool := fun p => decide ((i : ℕ) + 1 ≤ p.len ∧ p.ones < (i : ℕ) + 1 + 1)
    with hPwdef
  set g : Row → Bool := fun p => decide (p.ones = (i : ℕ) + 1) with hgdef
  set A : Finset (Fin (betaParts r).length) :=
    Finset.univ.filter (fun c : Fin (betaParts r).length =>
      (i : ℕ) + 1 ≤ betaLenAt r c ∧ (w[(c : ℕ)]!).ones < (i : ℕ) + 2) with hAdef
  set p : ℕ := rankIn A c with hpdef
  -- membership facts for c
  have hcA : c ∈ A := hc
  have hcmem : (i : ℕ) + 1 ≤ betaLenAt r c ∧ (w[(c : ℕ)]!).ones < (i : ℕ) + 2 := by
    rw [hAdef] at hcA
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hcA
  -- length of wordZ w (i+1)
  have hwordZlen : (wordZ w ((i : ℕ) + 1)).length = r i - shiftNext z i :=
    wordZ_length r hr w hw z hz i
  -- A.card = length of (w.filter Pw) = length of wordZ w (i+1)
  have hfilterPw_len : (w.filter Pw).length = (wordZ w ((i : ℕ) + 1)).length := by
    unfold wordZ
    rw [List.length_map]
    try congr 1
    try (apply List.filter_congr; intro q _; rw [hPwdef])
  -- c as a list index
  have hclt : (c : ℕ) < w.length := by rw [hwlen]; exact c.isLt
  -- w[c]! = w[c] (in range)
  have hwc : w[(c : ℕ)]! = w[(c : ℕ)]'hclt := getElem!_pos w (c : ℕ) hclt
  -- Pw holds at c (since c ∈ A)
  have hlenc : (w[(c : ℕ)]!).len = betaLenAt r c := fillings_getElem_len r w hw c
  have hPwc : Pw (w[(c : ℕ)]'hclt) = true := by
    rw [hPwdef]
    simp only [decide_eq_true_eq]
    rw [← hwc, hlenc]
    exact ⟨hcmem.1, by have := hcmem.2; omega⟩
  -- rankIn A c = ((w.take c).filter Pw).length
  have hrankeq : p = ((w.take (c : ℕ)).filter Pw).length := by
    rw [hpdef, rankIn]
    -- both are cardinalities of matching sets
    rw [show ((w.take (c : ℕ)).filter Pw).length
          = (Finset.univ.filter (fun u : Fin w.length =>
              (u : ℕ) < (c : ℕ) ∧ Pw (w[(u : ℕ)]) = true)).card from ?_]
    · -- card_bij between (A.filter (< c)) and the list-position set
      apply Finset.card_bij
        (fun (u : Fin (betaParts r).length) _ =>
          (⟨(u : ℕ), by rw [hwlen]; exact u.isLt⟩ : Fin w.length))
      · intro u hu
        rw [hAdef] at hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        obtain ⟨⟨hulen, huones⟩, hult⟩ := hu
        have hulist : (u : ℕ) < w.length := by rw [hwlen]; exact u.isLt
        have huwc : w[(u : ℕ)]! = w[(u : ℕ)]'hulist := getElem!_pos w (u : ℕ) hulist
        refine ⟨by simpa using hult, ?_⟩
        rw [hPwdef]
        simp only [decide_eq_true_eq]
        have hlenu : (w[(u : ℕ)]!).len = betaLenAt r u := fillings_getElem_len r w hw u
        rw [← huwc, hlenu]
        exact ⟨hulen, by omega⟩
      · intro u1 _ u2 _ heq
        apply Fin.ext
        simpa using heq
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        obtain ⟨hvlt, hvPw⟩ := hv
        refine ⟨⟨(v : ℕ), by rw [← hwlen]; exact v.isLt⟩, ?_, ?_⟩
        · rw [hAdef]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hvlist : (v : ℕ) < w.length := v.isLt
          have hvwc : w[(v : ℕ)]! = w[(v : ℕ)]'hvlist := getElem!_pos w (v : ℕ) hvlist
          rw [hPwdef] at hvPw
          simp only [decide_eq_true_eq] at hvPw
          have hlenv : (w[(v : ℕ)]!).len = betaLenAt r ⟨(v : ℕ), by rw [← hwlen]; exact v.isLt⟩ :=
            fillings_getElem_len r w hw ⟨(v : ℕ), by rw [← hwlen]; exact v.isLt⟩
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · rw [← hlenv, hvwc]; exact hvPw.1
          · rw [hvwc]; have := hvPw.2; omega
          · simp only [Fin.lt_def]; simpa using hvlt
        · apply Fin.ext; rfl
    · -- take_filter length as a card over Fin w.length
      rw [take_filter_length_eq_card]
  -- p < r i - shiftNext z i
  have hplt : p < r i - shiftNext z i := by
    rw [hrankeq]
    have hstrict : ((w.take (c : ℕ)).filter Pw).length < (w.filter Pw).length := by
      -- c itself passes Pw and is not in the take
      have hsplit : w.filter Pw
          = (w.take (c : ℕ)).filter Pw ++ (w[(c:ℕ)] :: (w.drop ((c:ℕ)+1)).filter Pw) := by
        have hw2 : w = w.take (c:ℕ) ++ w[(c:ℕ)] :: w.drop ((c:ℕ)+1) := by
          conv_lhs => rw [← List.take_append_drop (c:ℕ) w]
          congr 1
          rw [List.drop_eq_getElem_cons hclt]
        conv_lhs => rw [hw2]
        rw [List.filter_append, List.filter_cons_of_pos hPwc]
      rw [hsplit, List.length_append, List.length_cons]
      omega
    rw [hfilterPw_len, hwordZlen] at hstrict
    exact hstrict
  -- unfold padVZ
  have hpadeq : padVZ r z V i p = V i ⟨p, hplt⟩ := by
    unfold padVZ; rw [dif_pos hplt]
  rw [hpadeq]
  -- V i ⟨p⟩ = wordZ w (i+1)[p]!
  have hVget : V i ⟨p, hplt⟩ = (wordZ w ((i : ℕ) + 1))[p]! := by
    simp only [hVdef, FwdZ]
  rw [hVget]
  -- wordZ = (w.filter Pw).map g ; positional read via filter_map_getElem_rank
  have hwordZeq : wordZ w ((i : ℕ) + 1) = (w.filter Pw).map g := by
    unfold wordZ
    rw [hPwdef, hgdef]
    try congr 1
    try (apply List.filter_congr; intro q _; rfl)
  have hrank := filter_map_getElem_rank w Pw g (c : ℕ) hclt hPwc
  rw [← hrankeq] at hrank
  rw [hwordZeq]
  have hplt2 : p < ((w.filter Pw).map g).length := by
    rw [List.length_map, hfilterPw_len, hwordZlen]; exact hplt
  rw [getElem!_pos _ p hplt2]
  rw [List.getElem?_eq_getElem hplt2] at hrank
  simp only [Option.some.injEq] at hrank
  rw [hrank, hgdef]
  simp only []
  rw [hwc]

/-- Forward-source identity: `aliveZ` of the forward-mapped `w` at level `i` is
exactly the set of columns whose row has `ones ≥ i+1`.  Mirror of
`aliveNat_forward`. -/
lemma aliveZ_forward_source (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (w : List Row) (hw : w ∈ fillings (betaParts r)) (z : Fin ℓ → ℕ)
    (hz : (fun i : Fin ℓ => countLevel w ((i : ℕ) + 1)) = z) (i : Fin ℓ) :
    aliveZ r z (FwdZ r z w) i
      = Finset.univ.filter (fun c : Fin (betaParts r).length =>
          (i : ℕ) + 1 ≤ (w[(c : ℕ)]!).ones) := by
  classical
  set V := FwdZ r z w with hVdef
  -- helper: w[c]!.ones ≤ betaLenAt r c
  have hones_le : ∀ c : Fin (betaParts r).length,
      (w[(c : ℕ)]!).ones ≤ betaLenAt r c := by
    intro c
    have h1 : (w[(c : ℕ)]!).len = betaLenAt r c := fillings_getElem_len r w hw c
    have h2 : (w[(c : ℕ)]!).ones ≤ (w[(c : ℕ)]!).len := (w[(c : ℕ)]!).ones_le
    omega
  -- betaLenAt bound: betaLenAt r c ≤ ℓ
  have hbeta_mem_le : ∀ x ∈ betaParts r, x ≤ ℓ := by
    intro x hx
    unfold betaParts at hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨a, _, rfl⟩ := hx
    calc (Finset.univ.filter (fun i => a + 1 ≤ r i)).card
        ≤ (Finset.univ : Finset (Fin ℓ)).card := Finset.card_filter_le _ _
      _ = ℓ := by simp
  have hbeta_le : ∀ c : Fin (betaParts r).length, betaLenAt r c ≤ ℓ := by
    intro c
    unfold betaLenAt
    exact hbeta_mem_le _ (List.getElem_mem c.isLt)
  -- descending induction
  have key : ∀ n : ℕ, ∀ j : Fin ℓ, (ℓ : ℕ) - (j : ℕ) = n →
      aliveZ r z V j
        = Finset.univ.filter (fun c : Fin (betaParts r).length =>
            (j : ℕ) + 1 ≤ (w[(c : ℕ)]!).ones) := by
    intro n
    induction n with
    | zero =>
      intro j hjk
      exact absurd hjk (by have := j.isLt; omega)
    | succ k ih =>
      intro j hjk
      rw [aliveZ_eq_step r hℓ z V j]
      have hj := j.isLt
      -- Bn = aliveZNext j = filter (j+2 ≤ ones)
      have hBn : aliveZNext r z V j
          = Finset.univ.filter (fun c : Fin (betaParts r).length =>
              (j : ℕ) + 2 ≤ (w[(c : ℕ)]!).ones) := by
        by_cases htop : (j : ℕ) + 1 < ℓ
        · set j1 : Fin ℓ := ⟨(j : ℕ) + 1, htop⟩ with hj1
          have heq : aliveZNext r z V j = aliveZ r z V j1 := by
            unfold aliveZNext aliveZ
            congr 1
            simp only [hj1]; omega
          have hjk1 : (ℓ : ℕ) - (j1 : ℕ) = k := by simp only [hj1]; omega
          rw [heq, ih j1 hjk1]
        · have hjtop : (j : ℕ) + 1 = ℓ := by omega
          have heq : aliveZNext r z V j = ∅ := by
            unfold aliveZNext
            have : ℓ - 1 - (j : ℕ) = 0 := by omega
            rw [this]; rfl
          rw [heq]
          ext c
          have h1 := hones_le c
          have h2 := hbeta_le c
          simp only [Finset.notMem_empty, Finset.mem_filter, Finset.mem_univ,
            true_and, false_iff, not_le]
          omega
      -- fold the let-bindings introduced by aliveZ_eq_step
      set Bn := aliveZNext r z V j with hBndef
      set A := (PZ r j).filter (fun c => c ∉ Bn) with hAdef
      show Bn ∪ A.filter (fun c => padVZ r z V j (rankIn A c)) = _
      -- A = filter (j+1 ≤ betaLenAt ∧ ones < j+2)
      have hAeq : A = Finset.univ.filter (fun c : Fin (betaParts r).length =>
              (j : ℕ) + 1 ≤ betaLenAt r c ∧ (w[(c : ℕ)]!).ones < (j : ℕ) + 2) := by
        ext c
        have hBnmem : c ∈ Bn ↔ (j : ℕ) + 2 ≤ (w[(c : ℕ)]!).ones := by
          rw [hBn]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and, PZ, hBnmem, not_le]
      -- births set via bridge
      have hbirths : A.filter (fun c => padVZ r z V j (rankIn A c))
          = Finset.univ.filter (fun c : Fin (betaParts r).length =>
              (w[(c : ℕ)]!).ones = (j : ℕ) + 1) := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hcA, hpad⟩
          have hcbridge : c ∈ Finset.univ.filter (fun c : Fin (betaParts r).length =>
              (j : ℕ) + 1 ≤ betaLenAt r c ∧ (w[(c : ℕ)]!).ones < (j : ℕ) + 2) := by
            rw [← hAeq]; exact hcA
          have hbr := aliveZ_forward_padval r hr w hw z hz j c hcbridge
          rw [hAeq] at hpad
          rw [hbr] at hpad
          simpa only [decide_eq_true_eq] using hpad
        · intro hones
          have hcA2 : (j : ℕ) + 1 ≤ betaLenAt r c ∧ (w[(c : ℕ)]!).ones < (j : ℕ) + 2 := by
            have := hones_le c
            omega
          have hcbridge : c ∈ Finset.univ.filter (fun c : Fin (betaParts r).length =>
              (j : ℕ) + 1 ≤ betaLenAt r c ∧ (w[(c : ℕ)]!).ones < (j : ℕ) + 2) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hcA2
          have hcAmem : c ∈ A := by rw [hAeq]; exact hcbridge
          refine ⟨(by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hcAmem), ?_⟩
          have hbr := aliveZ_forward_padval r hr w hw z hz j c hcbridge
          rw [hAeq, hbr]
          simpa only [decide_eq_true_eq] using hones
      rw [hBn, hbirths]
      -- union = filter (j+1 ≤ ones)
      ext c
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (h | h) <;> omega
      · intro h
        rcases Nat.lt_or_ge ((w[(c : ℕ)]!).ones) ((j : ℕ) + 2) with hlt | hge
        · right; omega
        · left; omega
  exact key ((ℓ : ℕ) - (i : ℕ)) i rfl

/-- Round trip source→target→source: reconstructing from the forward map recovers
`w`. -/
lemma invRowsZ_FwdZ (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (w : List Row) (hw : w ∈ fillings (betaParts r)) (z : Fin ℓ → ℕ)
    (hz : (fun i : Fin ℓ => countLevel w ((i : ℕ) + 1)) = z) :
    invRowsZ r z (FwdZ r z w) = w := by
  classical
  set V := FwdZ r z w with hVdef
  -- length equality and pointwise Row equality
  have hlen : (invRowsZ r z V).length = w.length := by
    rw [invRowsZ, List.length_ofFn, fillings_length_eq r w hw]
  apply List.ext_getElem hlen
  intro c hc1 hc2
  -- index c as a Fin (betaParts r).length
  have hclen : c < (betaParts r).length := by
    rw [invRowsZ, List.length_ofFn] at hc1; exact hc1
  set cf : Fin (betaParts r).length := ⟨c, hclen⟩ with hcf
  -- the invRowsZ entry
  have hentry : (invRowsZ r z V)[c] =
      (⟨betaLenAt r cf, min (kInvZ r z V cf) (betaLenAt r cf),
        Nat.min_le_right _ _⟩ : Row) := by
    simp only [invRowsZ, List.getElem_ofFn, hcf]
  -- helper: (w[c]!).ones ≤ betaLenAt r cf ≤ ℓ
  have hlenc : (w[c]!).len = betaLenAt r cf := by
    have := fillings_getElem_len r w hw cf
    simpa [hcf] using this
  have hones_le_len : (w[c]!).ones ≤ (w[c]!).len := (w[c]!).ones_le
  -- betaLenAt cf ≤ ℓ
  have hbeta_le : betaLenAt r cf ≤ ℓ := by
    unfold betaLenAt
    have hmem := List.getElem_mem cf.isLt (l := betaParts r)
    -- x = (betaParts r)[cf] ≤ ℓ
    have hbeta_mem_le : ∀ x ∈ betaParts r, x ≤ ℓ := by
      intro x hx
      unfold betaParts at hx
      simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨a, _, rfl⟩ := hx
      calc (Finset.univ.filter (fun i => a + 1 ≤ r i)).card
          ≤ (Finset.univ : Finset (Fin ℓ)).card := Finset.card_filter_le _ _
        _ = ℓ := by simp
    exact hbeta_mem_le _ hmem
  -- kInvZ r z V cf = (w[c]!).ones
  have hkInv : kInvZ r z V cf = (w[c]!).ones := by
    unfold kInvZ
    -- rewrite membership via aliveZ_forward_source
    have hmem : ∀ i : Fin ℓ, cf ∈ aliveZ r z V i ↔ (i : ℕ) + 1 ≤ (w[c]!).ones := by
      intro i
      rw [hVdef, aliveZ_forward_source r hℓ hr w hw z hz i]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcf]
    have hfilt : (Finset.univ.filter (fun i : Fin ℓ => cf ∈ aliveZ r z V i))
        = (Finset.univ.filter (fun i : Fin ℓ => (i : ℕ) < (w[c]!).ones)) := by
      apply Finset.filter_congr
      intro i _
      rw [hmem i]; omega
    rw [hfilt]
    -- count of i : Fin ℓ with i < N equals N when N ≤ ℓ
    have hNle : (w[c]!).ones ≤ ℓ := by omega
    rw [Finset.card_bij (fun (i : Fin ℓ) _ => (i : ℕ))
          (s := (Finset.univ.filter (fun i : Fin ℓ => (i : ℕ) < (w[c]!).ones)))
          (t := Finset.range ((w[c]!).ones))]
    · simp only [Finset.card_range]
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_range]; exact hi
    · intro i₁ _ i₂ _ hEq; exact Fin.ext hEq
    · intro m hm
      simp only [Finset.mem_range] at hm
      exact ⟨⟨m, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hm, rfl⟩
  -- assemble Row equality
  rw [hentry]
  -- w[c] via getElem!_pos
  have hwc : w[c] = w[c]! := by
    rw [getElem!_pos w c hc2]
  rw [hwc]
  -- Row.ext: len and ones
  have hmin : min (kInvZ r z V cf) (betaLenAt r cf) = (w[c]!).ones := by
    rw [hkInv]; rw [← hlenc] at hbeta_le ⊢; omega
  -- match fields; ones_le is a Prop so proof-irrelevant
  cases hrow : w[c]! with
  | mk len ones hle =>
    have e1 : betaLenAt r cf = len := by rw [← hlenc, hrow]
    have e2 : min (kInvZ r z V cf) (betaLenAt r cf) = ones := by rw [hmin, hrow]
    rw [Row.mk.injEq]
    exact ⟨e1, e2⟩

/-- The reconstructed filling has the right level profile. -/
lemma invRowsZ_countLevel (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (z : Fin ℓ → ℕ) (hzr : ∀ j : Fin ℓ, z j ≤ r j)
    (hzdom : ∀ j : Fin ℓ, shiftNext z j ≤ z j)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool)
    (hV : V ∈ Fintype.piFinset (wordSetZ r z)) (i : Fin ℓ) :
    countLevel (invRowsZ r z V) ((i : ℕ) + 1) = z i := by
  classical
  unfold countLevel invRowsZ
  rw [length_filter_ofFn]
  have hfilt : (Finset.univ.filter (fun c : Fin (betaParts r).length =>
        decide ((i : ℕ) + 1 ≤
          (⟨betaLenAt r c, min (kInvZ r z V c) (betaLenAt r c), Nat.min_le_right _ _⟩ : Row).ones)))
      = aliveZ r z V i := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    rw [Nat.min_eq_left (kInvZ_le_len r hℓ hr z hzr hzdom V hV c),
        ← mem_aliveZ_iff_kInvZ r hℓ z V c i]
  rw [hfilt, (aliveZ_card_subset r hℓ hr z hzr hzdom V hV).1 i]

/-- The level word of the reconstructed filling is `List.ofFn (V i)`.  Mirror of
`wordA_kInv`. -/
lemma wordZ_invRowsZ (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (z : Fin ℓ → ℕ) (hzr : ∀ j : Fin ℓ, z j ≤ r j)
    (hzdom : ∀ j : Fin ℓ, shiftNext z j ≤ z j)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool)
    (hV : V ∈ Fintype.piFinset (wordSetZ r z)) (i : Fin ℓ) :
    wordZ (invRowsZ r z V) ((i : ℕ) + 1) = List.ofFn (V i) := by
  classical
  set m : ℕ := (i : ℕ) with hmdef
  have hmℓ : m < ℓ := i.isLt
  set L : List Row := invRowsZ r z V with hLdef
  have hLlen : L.length = (betaParts r).length := by
    rw [hLdef, invRowsZ, List.length_ofFn]
  have hLget_len : ∀ c : Fin (betaParts r).length,
      (L[(c : ℕ)]'(by rw [hLlen]; exact c.isLt)).len = betaLenAt r c := by
    intro c
    simp only [hLdef, invRowsZ, List.getElem_ofFn]
  have hLget_ones : ∀ c : Fin (betaParts r).length,
      (L[(c : ℕ)]'(by rw [hLlen]; exact c.isLt)).ones = kInvZ r z V c := by
    intro c
    simp only [hLdef, invRowsZ, List.getElem_ofFn]
    exact Nat.min_eq_left (kInvZ_le_len r hℓ hr z hzr hzdom V hV c)
  set Bn : Finset (Fin (betaParts r).length) := aliveZNext r z V i with hBndef
  set A : Finset (Fin (betaParts r).length) := (PZ r i).filter (fun c => c ∉ Bn) with hAdef
  have hnotBn : ∀ c : Fin (betaParts r).length, c ∉ Bn ↔ kInvZ r z V c ≤ m + 1 := by
    intro c
    by_cases htop : m + 1 < ℓ
    · set i1 : Fin ℓ := ⟨m + 1, htop⟩ with hi1
      have heq : Bn = aliveZ r z V i1 := by
        rw [hBndef]; unfold aliveZNext aliveZ
        congr 1; simp only [hi1, hmdef]; omega
      rw [heq, mem_aliveZ_iff_kInvZ r hℓ z V c i1]
      simp only [hi1]; omega
    · have hitop : m + 1 = ℓ := by omega
      have heqBn : Bn = ∅ := by
        rw [hBndef]; unfold aliveZNext
        have hz0 : ℓ - 1 - m = 0 := by omega
        rw [show (i : ℕ) = m from rfl, hz0]; rfl
      have hkle : kInvZ r z V c ≤ m + 1 := by
        have hle : kInvZ r z V c ≤ ℓ := by
          rw [kInvZ]
          calc (Finset.univ.filter (fun j : Fin ℓ => c ∈ aliveZ r z V j)).card
              ≤ (Finset.univ : Finset (Fin ℓ)).card :=
                Finset.card_le_card (Finset.filter_subset _ _)
            _ = ℓ := by simp
        omega
      rw [heqBn]; simp only [Finset.notMem_empty, not_false_eq_true, true_iff]
      exact hkle
  have hAmem : ∀ c : Fin (betaParts r).length,
      c ∈ A ↔ ((m : ℕ) + 1 ≤ betaLenAt r c ∧ kInvZ r z V c ≤ m + 1) := by
    intro c
    rw [hAdef]; simp only [Finset.mem_filter, PZ, Finset.mem_univ, true_and]
    rw [hnotBn c]
  have hbridge : ∀ c : Fin (betaParts r).length, c ∈ A →
      padVZ r z V i (rankIn A c) = decide (kInvZ r z V c = m + 1) := by
    intro c hcA
    have hstep := aliveZ_eq_step r hℓ z V i
    simp only at hstep
    rw [← hBndef, ← hAdef] at hstep
    have hmemAlive : c ∈ aliveZ r z V i ↔ (m + 1 ≤ kInvZ r z V c) := by
      rw [mem_aliveZ_iff_kInvZ r hℓ z V c i, hmdef]
    have hcnotBn : c ∉ Bn := by rw [hAdef, Finset.mem_filter] at hcA; exact hcA.2
    have hbit : padVZ r z V i (rankIn A c) = true ↔ (m + 1 ≤ kInvZ r z V c) := by
      rw [← hmemAlive, hstep, Finset.mem_union]
      constructor
      · intro h; right; rw [Finset.mem_filter]; exact ⟨hcA, h⟩
      · rintro (h | h)
        · exact absurd h hcnotBn
        · rw [Finset.mem_filter] at h; exact h.2
    by_cases hkeq : kInvZ r z V c = m + 1
    · rw [decide_eq_true hkeq]; exact hbit.mpr (by omega)
    · rw [decide_eq_false hkeq]
      cases hb : padVZ r z V i (rankIn A c) with
      | false => rfl
      | true =>
        have hh := hbit.mp hb
        have hle := (hAmem c).mp hcA
        exact absurd (by omega : kInvZ r z V c = m + 1) hkeq
  set P : Row → Bool := fun row => decide ((m : ℕ) + 1 ≤ row.len ∧ row.ones < (m : ℕ) + 1 + 1)
    with hPdef
  set g : Row → Bool := fun row => decide (row.ones = (m : ℕ) + 1) with hgdef
  have hLHS : wordZ L (m + 1) = (L.filter P).map g := by
    unfold wordZ
    rw [hPdef, hgdef]
  rw [hLHS]
  have hAcard : A.card = r i - shiftNext z i := by
    rw [hAdef, hBndef]
    exact (aliveZ_card_subset r hℓ hr z hzr hzdom V hV).2.2.2 i
  have hPL : ∀ c : Fin (betaParts r).length,
      P (L[(c : ℕ)]'(by rw [hLlen]; exact c.isLt)) = true ↔ c ∈ A := by
    intro c
    rw [hPdef]; simp only [decide_eq_true_eq]
    rw [hLget_len c, hLget_ones c, hAmem c]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  have hfilterlen : (L.filter P).length = A.card := by
    rw [hLdef, invRowsZ]
    rw [length_filter_ofFn]
    apply congrArg Finset.card
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hAmem c, hPdef]
    simp only [decide_eq_true_eq]
    have hle := kInvZ_le_len r hℓ hr z hzr hzdom V hV c
    rw [Nat.min_eq_left hle]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  apply List.ext_getElem?
  intro p
  by_cases hp : p < r i - shiftNext z i
  · have hplt : p < A.card := by rw [hAcard]; exact hp
    have hpimg : p ∈ A.image (rankIn A) := by
      rw [rankIn_image]; simp only [Finset.mem_range]; exact hplt
    simp only [Finset.mem_image] at hpimg
    obtain ⟨c, hcA, hcrank⟩ := hpimg
    have hclt : (c : ℕ) < L.length := by rw [hLlen]; exact c.isLt
    have hPc : P L[(c : ℕ)] = true := (hPL c).mpr hcA
    have hidx : ((L.take (c : ℕ)).filter P).length = p := by
      rw [← hcrank]
      rw [hLdef, invRowsZ]
      rw [take_filter_ofFn_length]
      rw [rankIn, hAdef]
      -- source Finset: univ.filter (fun c' => ↑c' < ↑c ∧ P (struct c') = true)
      -- target Finset: {c' ∈ PZ ∧ c'∉Bn | c' < c}
      -- bridge: P (struct c') = true ↔ c' ∈ A ↔ (c' ∈ PZ ∧ c'∉Bn)
      have hPstruct : ∀ c' : Fin (betaParts r).length,
          (P (⟨betaLenAt r c', min (kInvZ r z V c') (betaLenAt r c'),
              Nat.min_le_right _ _⟩ : Row) = true) ↔ (c' ∈ PZ r i ∧ c' ∉ Bn) := by
        intro c'
        rw [hPdef]; simp only [decide_eq_true_eq]
        have hle := kInvZ_le_len r hℓ hr z hzr hzdom V hV c'
        rw [Nat.min_eq_left hle]
        rw [hnotBn c']
        simp only [PZ, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
      apply Finset.card_bij (fun (c' : Fin (betaParts r).length) _ => c')
      · intro c' hc'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc'
        obtain ⟨hlt, hP⟩ := hc'
        have hmemA := (hPstruct c').mp hP
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hmemA, ?_⟩
        simp only [Fin.lt_def]; exact hlt
      · intro c1 _ c2 _ h; exact h
      · intro c' hc'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc'
        obtain ⟨hmem, hlt⟩ := hc'
        refine ⟨c', ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, (hPstruct c').mpr hmem⟩
        simp only [Fin.lt_def] at hlt; exact hlt
    have hrank := filter_map_getElem_rank L P g (c : ℕ) hclt hPc
    rw [hidx] at hrank
    rw [hrank]
    have hVlen : (List.ofFn (V i)).length = r i - shiftNext z i := by simp
    have hpVlen : p < (List.ofFn (V i)).length := by rw [hVlen]; exact hp
    rw [List.getElem?_eq_getElem hpVlen]
    simp only [List.getElem_ofFn]
    congr 1
    rw [hgdef]
    simp only []
    rw [show L[(c : ℕ)] = L[(c : ℕ)]'hclt from rfl]
    rw [hLget_ones c]
    have hbr := hbridge c hcA
    rw [hcrank] at hbr
    rw [← hbr]
    have hpadeval : padVZ r z V i p = V i ⟨p, hp⟩ := by
      unfold padVZ; rw [dif_pos hp]
    rw [hpadeval]
  · have hpc : ¬ p < ((L.filter P).map g).length := by
      rw [List.length_map, hfilterlen, hAcard]; exact hp
    have hpc2 : ¬ p < (List.ofFn (V i)).length := by
      rw [List.length_ofFn]; exact hp
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- Round trip target→source→target. -/
lemma FwdZ_invRowsZ (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (z : Fin ℓ → ℕ) (hzr : ∀ j : Fin ℓ, z j ≤ r j)
    (hzdom : ∀ j : Fin ℓ, shiftNext z j ≤ z j)
    (V : (i : Fin ℓ) → Fin (r i - shiftNext z i) → Bool)
    (hV : V ∈ Fintype.piFinset (wordSetZ r z)) :
    FwdZ r z (invRowsZ r z V) = V := by
  classical
  funext i
  have hwrec : wordZ (invRowsZ r z V) ((i : ℕ) + 1) = List.ofFn (V i) :=
    wordZ_invRowsZ r hℓ hr z hzr hzdom V hV i
  funext p
  simp only [FwdZ]
  rw [hwrec]
  rw [getElem!_pos _ (p : ℕ) (by rw [List.length_ofFn]; exact p.isLt)]
  simp only [List.getElem_ofFn]

/-! ## Layer 7 for `fiberZ_sum`: the level bijection and the theorem. -/

/-- **Level bijection for the Z-side fiber sum.**  Mirror of `fiberA_biject`. -/
theorem fiberZ_biject (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (z : Fin ℓ → ℕ) (hzr : ∀ j : Fin ℓ, z j ≤ r j)
    (hzdom : ∀ j : Fin ℓ, shiftNext z j ≤ z j) :
    ∑ w ∈ (fillings (betaParts r)).filter
        (fun w => (fun i : Fin ℓ => countLevel w ((i : ℕ) + 1)) = z),
        q ^ (∑ i : Fin ℓ, invWord (wordZ w ((i : ℕ) + 1)))
      = ∑ V ∈ Fintype.piFinset (wordSetZ r z),
          q ^ (∑ i : Fin ℓ, invWord (List.ofFn (V i))) := by
  classical
  refine Finset.sum_nbij' (i := fun w => FwdZ r z w) (j := fun V => invRowsZ r z V)
    ?_ ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rw [Fintype.mem_piFinset]
    intro i
    exact FwdZ_mem_wordSetZ r hr w hw.1 z hw.2 i
  · intro V hV
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨invRowsZ_mem r z V, ?_⟩
    funext i
    exact invRowsZ_countLevel r hℓ hr z hzr hzdom V hV i
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact invRowsZ_FwdZ r hℓ hr w hw.1 z hw.2
  · intro V hV
    exact FwdZ_invRowsZ r hℓ hr z hzr hzdom V hV
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [FwdZ_ofFn r hr w hw.1 z hw.2 i]


theorem fiberZ_sum
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (hbw : BinaryWordGauss) (z : Fin ℓ → ℕ)
    (hzr : ∀ j : Fin ℓ, z j ≤ r j) (hzdom : ∀ j : Fin ℓ, shiftNext z j ≤ z j) :
    ∑ w ∈ (fillings (betaParts r)).filter
        (fun w => (fun i : Fin ℓ => countLevel w (i + 1)) = z),
        q ^ (∑ i ∈ Finset.Icc 1 ℓ, invWord (wordZ w i))
      = ∏ i, gauss (r i - shiftNext z i) (z i - shiftNext z i) := by
  classical
  simp_rw [wordZ_Icc_to_Fin]
  rw [fiberZ_biject r hℓ hr z hzr hzdom]
  have hgauss : ∀ i : Fin ℓ,
      gauss (r i - shiftNext z i) (z i - shiftNext z i)
        = ∑ v ∈ wordSetZ r z i, q ^ (invWord (List.ofFn v)) := by
    intro i
    rw [hbw (r i - shiftNext z i) (z i - shiftNext z i)]
    rfl
  simp_rw [hgauss]
  rw [Finset.prod_univ_sum (wordSetZ r z) (fun i v => q ^ (invWord (List.ofFn v)))]
  refine Finset.sum_congr rfl (fun V hV => ?_)
  rw [← Finset.prod_pow_eq_pow_sum]

theorem fiber_factor
    (hℓ : 0 < ℓ) (M : ℕ) (bf : Bool) (a z : Fin ℓ → ℕ)
    (hM : ∑ i, (a i + z i) = M) :
    ∑ T ∈ (TsetOrder r s M bf).filter
        (fun T => (aOf (ℓ := ℓ) T, zOf (ℓ := ℓ) T) = (a, z)),
        LaurentPolynomial.T (Ja ℓ T + Jz ℓ T)
      = (∑ w ∈ (fillings (betaParts r)).filter
            (fun w => (fun i : Fin ℓ => countLevel w (i + 1)) = z),
            q ^ (∑ i ∈ Finset.Icc 1 ℓ, invWord (wordZ w i)))
        * (∑ w ∈ (fillings (sBlockLens ℓ s)).filter
            (fun w => (fun i : Fin ℓ => countLevel w (i + 1)) = a),
            q ^ (∑ i ∈ Finset.Icc 1 ℓ, invWord (wordA w i))) := by
  classical
  set f : List Row × List Row → MultiTab := fun p => ⟨p.1, p.2, bf⟩ with hf
  -- The LHS index set equals the image under `f` of the product of the two
  -- filtered filling sets.
  have hset :
      (TsetOrder r s M bf).filter
        (fun T => (aOf (ℓ := ℓ) T, zOf (ℓ := ℓ) T) = (a, z))
      = (((fillings (betaParts r)).filter
            (fun w => (fun i : Fin ℓ => countLevel w (i + 1)) = z)) ×ˢ
          ((fillings (sBlockLens ℓ s)).filter
            (fun w => (fun i : Fin ℓ => countLevel w (i + 1)) = a))).image f := by
    ext T
    simp only [TsetOrder, Finset.mem_filter, Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨⟨b, w⟩, ⟨hb, hw⟩, hTeq⟩, hlvl⟩, haz⟩
      subst hTeq
      rw [Prod.ext_iff] at haz
      obtain ⟨haOf, hzOf⟩ := haz
      exact ⟨(b, w), ⟨⟨hb, hzOf⟩, ⟨hw, haOf⟩⟩, rfl⟩
    · rintro ⟨⟨b, w⟩, ⟨⟨hb, hbz⟩, ⟨hw, hwa⟩⟩, hTeq⟩
      subst hTeq
      refine ⟨⟨⟨(b, w), ⟨hb, hw⟩, rfl⟩, ?_⟩, ?_⟩
      · show ∑ i, (aOf (ℓ := ℓ) (f (b, w)) i + zOf (ℓ := ℓ) (f (b, w)) i) = M
        rw [← hM]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have e1 : aOf (ℓ := ℓ) (f (b, w)) i = a i := congrFun hwa i
        have e2 : zOf (ℓ := ℓ) (f (b, w)) i = z i := congrFun hbz i
        rw [e1, e2]
      · rw [Prod.ext_iff]
        exact ⟨hwa, hbz⟩
  rw [hset]
  -- The map `f` is injective on the product, so `sum_image` applies.
  rw [Finset.sum_image (by
    intro x hx y hy hxy
    simp only [hf, MultiTab.mk.injEq] at hxy
    exact Prod.ext hxy.1 hxy.2.1)]
  -- Turn the product sum into a double sum and factor.
  rw [Finset.sum_product]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  refine Finset.sum_congr rfl (fun w hw => ?_)
  -- Pointwise: `T (Ja + Jz) = q^(∑Z b) * q^(∑A w)`.
  show LaurentPolynomial.T (Ja ℓ (f (b, w)) + Jz ℓ (f (b, w)))
      = q ^ (∑ i ∈ Finset.Icc 1 ℓ, invWord (wordZ b i))
        * q ^ (∑ i ∈ Finset.Icc 1 ℓ, invWord (wordA w i))
  have hJa : Ja ℓ (f (b, w)) = ∑ i ∈ Finset.Icc 1 ℓ, (invWord (wordA w i) : ℤ) := rfl
  have hJz : Jz ℓ (f (b, w)) = ∑ i ∈ Finset.Icc 1 ℓ, (invWord (wordZ b i) : ℤ) := rfl
  rw [hJa, hJz]
  rw [LaurentPolynomial.T_add]
  rw [mul_comm]
  congr 1
  · -- T (∑ (invWord wordA : ℤ)) = q ^ (∑ invWord wordA)
    rw [q, LaurentPolynomial.T_pow, Nat.cast_sum]
    congr 1
    ring
  · rw [q, LaurentPolynomial.T_pow, Nat.cast_sum]
    congr 1
    ring

theorem fiber_weight
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (hbw : BinaryWordGauss) (M : ℕ) (bf : Bool)
    (a z : Fin ℓ → ℕ) (haz : (a, z) ∈ azFinset r s M) :
    ∑ T ∈ (TsetOrder r s M bf).filter
        (fun T => (aOf (ℓ := ℓ) T, zOf (ℓ := ℓ) T) = (a, z)),
        LaurentPolynomial.T (Ja ℓ T + Jz ℓ T)
      = Bweight r s a z := by
  simp only [azFinset, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset,
    Finset.mem_range] at haz
  obtain ⟨_, ⟨hadom, hzr, hzdom⟩, hM⟩ := haz
  rw [fiber_factor r s hℓ M bf a z hM,
      fiberZ_sum r hℓ hr hbw z hzr hzdom, fiberA_sum hℓ hbw s a hadom]
  rw [Bweight, Finset.prod_mul_distrib]
  ring

/-- **Generating-function core (`eq:Jgf`), minus order.**  Fibering `TsetMinus`
over `azFinset` by the block-count map `T ↦ (aOf T, zOf T)`, and applying the
binary-word Gaussian identity level by level, the `Bweight` product equals the
`T(Ja+Jz)` sum over each fiber.  Summing the `T(Eminus …)` prefactor gives this
identity. -/
theorem fiber_minus
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (hbw : BinaryWordGauss) (M : ℕ) :
    ∑ p ∈ azFinset r s M, LaurentPolynomial.T (Eminus r s p.1 p.2)
        * Bweight r s p.1 p.2
      = ∑ T ∈ TsetMinus r s M,
          LaurentPolynomial.T
            (Eminus r s (aOf (ℓ := ℓ) T) (zOf (ℓ := ℓ) T) + Ja ℓ T + Jz ℓ T) := by
  rw [show TsetMinus r s M = TsetOrder r s M true from rfl]
  rw [← Finset.sum_fiberwise_of_maps_to
        (fun T hT => phi_mem_az r s hℓ hr M true T hT)
        (fun T => LaurentPolynomial.T
          (Eminus r s (aOf (ℓ := ℓ) T) (zOf (ℓ := ℓ) T) + Ja ℓ T + Jz ℓ T))]
  apply Finset.sum_congr rfl
  intro p hp
  have hfw := fiber_weight r s hℓ hr hbw M true p.1 p.2 (by rw [Prod.mk.eta]; exact hp)
  rw [← hfw, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [Finset.mem_filter] at hT
  obtain ⟨_, hTp⟩ := hT
  have ha : aOf (ℓ := ℓ) T = p.1 := congrArg Prod.fst hTp
  have hz : zOf (ℓ := ℓ) T = p.2 := congrArg Prod.snd hTp
  rw [ha, hz, ← LaurentPolynomial.T_add]; congr 1; ring

/-- **Generating-function core (`eq:Jgf`), plus order.**  Same as `fiber_minus`
but for the s-block-first order `TsetPlus` and the plus exponent `E⁺`. -/
theorem fiber_plus
    (hℓ : 0 < ℓ) (hr : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (hbw : BinaryWordGauss) (M : ℕ) :
    ∑ p ∈ azFinset r s M, LaurentPolynomial.T (Eplus r p.1 p.2)
        * Bweight r s p.1 p.2
      = ∑ T ∈ TsetPlus r s M,
          LaurentPolynomial.T
            (Eplus r (aOf (ℓ := ℓ) T) (zOf (ℓ := ℓ) T) + Ja ℓ T + Jz ℓ T) := by
  rw [show TsetPlus r s M = TsetOrder r s M false from rfl]
  rw [← Finset.sum_fiberwise_of_maps_to
        (fun T hT => phi_mem_az r s hℓ hr M false T hT)
        (fun T => LaurentPolynomial.T
          (Eplus r (aOf (ℓ := ℓ) T) (zOf (ℓ := ℓ) T) + Ja ℓ T + Jz ℓ T))]
  apply Finset.sum_congr rfl
  intro p hp
  have hfw := fiber_weight r s hℓ hr hbw M false p.1 p.2 (by rw [Prod.mk.eta]; exact hp)
  rw [← hfw, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [Finset.mem_filter] at hT
  obtain ⟨_, hTp⟩ := hT
  have ha : aOf (ℓ := ℓ) T = p.1 := congrArg Prod.fst hTp
  have hz : zOf (ℓ := ℓ) T = p.2 := congrArg Prod.snd hTp
  rw [ha, hz, ← LaurentPolynomial.T_add]; congr 1; ring

/-- **Statement 3 (left-supernomial, minus sign — `eq:left-supernomial`, −).**
For every `M ≥ 0`, with `λ = (M, |μ| − M)`:
```
Σ_{(a,z) ∈ azFinset r s M} q^{E⁻(a,z)} · B_{r,s}(a, z)
    = q^{s·M} · S̃_{(M, |μ|−M), μ}(q⁻¹).
```
The `S̃(q⁻¹)` on the right is the `q ↦ q⁻¹` substitution `invSub` applied to the
fixed polynomial `S̃_{(M,|μ|−M),μ}(q) = Stil q [M, |μ|−M] μ'`.  The hypotheses
are exactly the external assumptions of `problem.md`:

* **Fact 2** (`fact2`): the multitableau/inversion expansion of the supernomial,
  stated at the fixed formal variable `q` over the canonical (beta-block-first)
  component order `TsetMinus`;
* **Fact 2 permutation invariance** (`fact2_perm`): permuting the one-row
  components of `μ` leaves the inv-sum unchanged; concretely the beta-block-first
  and s-block-first inv-sums agree;
* **Fact 3** (`fact3`): content symmetry of `S̃`;
* **Fact "binary word"** (`hbw`): the binary-word Gaussian identity. -/
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
  -- Step A: rewrite the RHS as a `T`-sum over `TsetMinus`.
  rw [fact2, map_sum, Finset.mul_sum]
  have hRHS : (∑ T ∈ TsetMinus r s M,
        LaurentPolynomial.T ((s : ℤ) * M) * invSub (q ^ invMT T))
      = ∑ T ∈ TsetMinus r s M,
          LaurentPolynomial.T
            (Eminus r s (aOf (ℓ := ℓ) T) (zOf (ℓ := ℓ) T) + Ja ℓ T + Jz ℓ T) := by
    refine Finset.sum_congr rfl (fun T hT => ?_)
    -- membership gives levelSum T = M
    have hlvl : (∑ i, (aOf (ℓ := ℓ) T i + zOf (ℓ := ℓ) T i)) = M := by
      simp only [TsetMinus, TsetOrder, Finset.mem_filter] at hT
      exact hT.2
    have hdec := inv_decomposition_minus r s hℓ hr hbw M T hT
    rw [invSub_q_pow, ← LaurentPolynomial.T_add]
    congr 1
    -- goal: (s:ℤ)*M + -(invMT T) = Eminus + Ja + Jz
    have : (s : ℤ) * M - (invMT T : ℤ)
        = Ja ℓ T + Jz ℓ T + Eminus r s (aOf (ℓ := ℓ) T) (zOf (ℓ := ℓ) T) := by
      rw [← hlvl]; push_cast; push_cast at hdec; linarith [hdec]
    linarith [this]
  rw [hRHS]
  exact fiber_minus r s hℓ hr hbw M

/-- **Statement 4 (left-supernomial, plus sign — `eq:left-supernomial`, +).**
For every `M ≥ 0`, with `λ = (M, |μ| − M)`:
```
Σ_{(a,z) ∈ azFinset r s M} q^{E⁺(a,z)} · B_{r,s}(a, z)
    = q^{s·M} · S̃_{(M, |μ|−M), μ}(q⁻¹).
```
Same shape as Statement 3.  Faithfully to `problem.md`'s Fact 2, the supernomial
is expanded at the fixed variable `q` over the *canonical* (beta-block-first)
component order (`fact2`), and `fact2_perm` (permutation invariance of the
one-row components of `μ`) supplies the s-block-first expansion used here.  As in
Statement 3, `S̃(q⁻¹)` is `invSub (Stil q [M, |μ|−M] μ')`; by Fact 3 (content
symmetry) the right-hand supernomial may equally be written with the content
`(|μ|−M, M)` swapped. -/
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
  -- Step A: rewrite the RHS as a `T`-sum over `TsetPlus` (using permutation invariance).
  rw [fact2, fact2_perm, map_sum, Finset.mul_sum]
  have hRHS : (∑ T ∈ TsetPlus r s M,
        LaurentPolynomial.T ((s : ℤ) * M) * invSub (q ^ invMT T))
      = ∑ T ∈ TsetPlus r s M,
          LaurentPolynomial.T
            (Eplus r (aOf (ℓ := ℓ) T) (zOf (ℓ := ℓ) T) + Ja ℓ T + Jz ℓ T) := by
    refine Finset.sum_congr rfl (fun T hT => ?_)
    have hlvl : (∑ i, (aOf (ℓ := ℓ) T i + zOf (ℓ := ℓ) T i)) = M := by
      simp only [TsetPlus, TsetOrder, Finset.mem_filter] at hT
      exact hT.2
    have hdec := inv_decomposition_plus r s hℓ hr hbw M T hT
    rw [invSub_q_pow, ← LaurentPolynomial.T_add]
    congr 1
    have : (s : ℤ) * M - (invMT T : ℤ)
        = Ja ℓ T + Jz ℓ T + Eplus r (aOf (ℓ := ℓ) T) (zOf (ℓ := ℓ) T) := by
      rw [← hlvl]; push_cast; push_cast at hdec; linarith [hdec]
    linarith [this]
  rw [hRHS]
  exact fiber_plus r s hℓ hr hbw M

end Statements

end SupernomialInv

open scoped QTheory PowerSeries.DiscreteTopology Classical
open HJO PowerSeries NumericalSemigroup Finset

namespace ProblemHJOa3

/-- The formal variable `q`, as a power series. -/
noncomputable abbrev qX : ℤ⟦X⟧ := X

/-- 1-indexed accessor for a tuple `t : Fin n → ℕ`: `tᵢ` for `1 ≤ i ≤ n`, else `0`. -/
def acc {n : ℕ} (t : Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : 1 ≤ i ∧ i ≤ n then t ⟨i - 1, by omega⟩ else 0

/-- Weakly-decreasing `r`-tuple with a same-length `m`-tuple (plus case). -/
abbrev DomP (k : ℕ) : Type := {rm : (Fin k → ℕ) × (Fin k → ℕ) // Antitone rm.1}

/-- Weakly-decreasing `r`-tuple with a length-`(k-1)` `m`-tuple (minus case: only `m₁…m_{k-1}`). -/
abbrev DomM (k : ℕ) : Type := {rm : (Fin k → ℕ) × (Fin (k - 1) → ℕ) // Antitone rm.1}

/-! ## Concrete assumed Facts (power-series world) -/

section PowerSeriesFacts

/-- **Fact 7 (Sylvester).** For coprime `a, b > 1`: Frobenius number `ab−a−b`, genus
`(a−1)(b−1)/2`, and for `0 ≤ s ≤ f` exactly one of `s`, `f−s` is a gap. -/
def Fact7 (a b : ℕ) : Prop :=
  Nat.Coprime a b ∧ 1 < a ∧ 1 < b ∧
    ((finspan {a, b}).gaps.card = (a - 1) * (b - 1) / 2) ∧
    -- Frobenius number `f = ab − a − b` is the largest gap
    ((a * b - a - b) ∈ (finspan {a, b}).gaps ∧
      (∀ g ∈ (finspan {a, b}).gaps, g ≤ a * b - a - b)) ∧
    (∀ s : ℕ, s ≤ a * b - a - b →
      (s ∈ (finspan {a, b}).gaps ↔ (a * b - a - b - s) ∉ (finspan {a, b}).gaps))

/-- **Fact 8 (Huang positive-definiteness).** For coprime `a, b > 1`, on the cone the form is
positive-definite with the norm bound `Q(n) ≥ ‖n‖∞²/|Gap|` (here coordinatewise:
`(nᵢ)² ≤ |Gap|·Q(n)`), and the resulting summand is `Summable` — so `Z_{a,b}` is a genuine
formal power series (the finiteness clause, not weakened away). -/
def Fact8 (a b : ℕ) : Prop :=
  Nat.Coprime a b ∧ 1 < a ∧ 1 < b ∧
    (HJO.Q a b).PosDefOn (HJO.cone a b) ∧
    (∀ n ∈ HJO.cone a b, ∀ i, (n i) ^ 2 ≤ ((finspan {a, b}).gaps.card : ℤ) * (HJO.Q a b) n) ∧
    -- finiteness/well-definedness: only finitely many `n` hit any fixed exponent value
    -- (the genuine formal-power-series datum; not weakened to a bare `Summable`).
    (∀ d : ℤ, {n : (finspan {a, b}).gaps → ℤ | n ∈ HJO.cone a b ∧ (HJO.Q a b) n = d}.Finite)

/-- **Fact 6 (elementary q-identities).** (a) q-Pascal; (b) factorial form (multiplicative,
plus vanishing); (c) telescoping chain for `r₁ ≥ ⋯ ≥ rₖ`. -/
def Fact6 : Prop :=
  (∀ N j : ℕ, 1 ≤ j → j ≤ N →
      qChoose qX N j = qChoose qX (N - 1) (j - 1) + qX ^ j * qChoose qX (N - 1) j) ∧
  (∀ N j : ℕ, 1 ≤ j → j ≤ N →
      qChoose qX N j = qX ^ (N - j) * qChoose qX (N - 1) (j - 1) + qChoose qX (N - 1) j) ∧
  (∀ N j : ℕ, j ≤ N →
      qPochhammer qX qX j * qPochhammer qX qX (N - j) * qChoose qX N j = qPochhammer qX qX N) ∧
  (∀ N j : ℕ, N < j → qChoose qX N j = 0) ∧
  (∀ (k : ℕ) (r : Fin k → ℕ), Antitone r →
      invOfUnit (qPochhammer qX qX (acc r 1)) 1
          * ∏ i ∈ Icc 1 (k - 1), qChoose qX (acc r i) (acc r (i + 1))
        = invOfUnit (qPochhammer qX qX (acc r k)
              * ∏ i ∈ Icc 1 (k - 1), qPochhammer qX qX (acc r i - acc r (i + 1))) 1)

end PowerSeriesFacts

/-! ## Layer 1 — finite q-Pochhammer unit algebra (`ℤ⟦X⟧`) -/

section QPochInverseLayer

/-- The finite `q`-Pochhammer `∏ i<m (1 - X^{i+1})` has constant coefficient `1`. -/
lemma constantCoeff_qPochhammer_fin (m : ℕ) :
    PowerSeries.constantCoeff (R := ℤ) (qPochhammer qX qX m) = 1 := by
  induction m with
  | zero => simp [qPochhammer_zero]
  | succ n ih =>
      rw [qPochhammer_succ', map_mul, ih, map_sub, map_mul, one_mul]
      simp [qX, PowerSeries.constantCoeff_X]

/-- `qPochhammer qX qX m` is a unit with inverse `invOfUnit … 1`. -/
lemma poch_mul_inv (m : ℕ) :
    qPochhammer qX qX m * PowerSeries.invOfUnit (qPochhammer qX qX m) 1 = 1 :=
  PowerSeries.mul_invOfUnit _ 1 (by simpa using constantCoeff_qPochhammer_fin m)

/-- Closed form of the Gaussian binomial via `q`-Pochhammer inverses. -/
lemma qChoose_as_inv_poch (hQbin : Fact6) (N j : ℕ) (hj : j ≤ N) :
    qChoose qX N j
      = qPochhammer qX qX N * PowerSeries.invOfUnit (qPochhammer qX qX j) 1
          * PowerSeries.invOfUnit (qPochhammer qX qX (N - j)) 1 := by
  have hfac : qPochhammer qX qX j * qPochhammer qX qX (N - j) * qChoose qX N j
      = qPochhammer qX qX N := hQbin.2.2.1 N j hj
  have hj' : qPochhammer qX qX j * PowerSeries.invOfUnit (qPochhammer qX qX j) 1 = 1 :=
    poch_mul_inv j
  have hNj : qPochhammer qX qX (N - j)
      * PowerSeries.invOfUnit (qPochhammer qX qX (N - j)) 1 = 1 := poch_mul_inv (N - j)
  have hstep : qChoose qX N j
      = (qPochhammer qX qX j * qPochhammer qX qX (N - j) * qChoose qX N j)
          * (PowerSeries.invOfUnit (qPochhammer qX qX j) 1
              * PowerSeries.invOfUnit (qPochhammer qX qX (N - j)) 1) := by
    have hcancel :
        (qPochhammer qX qX j * qPochhammer qX qX (N - j) * qChoose qX N j)
          * (PowerSeries.invOfUnit (qPochhammer qX qX j) 1
              * PowerSeries.invOfUnit (qPochhammer qX qX (N - j)) 1)
        = (qPochhammer qX qX j * PowerSeries.invOfUnit (qPochhammer qX qX j) 1)
            * (qPochhammer qX qX (N - j)
                * PowerSeries.invOfUnit (qPochhammer qX qX (N - j)) 1)
            * qChoose qX N j := by ring
    rw [hcancel, hj', hNj, one_mul, one_mul]
  rw [hstep, hfac, mul_assoc]

end QPochInverseLayer


/-- `θ(q^u; q^L) = (q^u; q^L)_∞ (q^{L-u}; q^L)_∞`, a formal infinite product in `ℤ⟦X⟧`. -/
noncomputable def bTheta (u L : ℕ) : ℤ⟦X⟧ :=
  (X ^ u; (X : ℤ⟦X⟧) ^ L)_∞ * (X ^ (L - u); (X : ℤ⟦X⟧) ^ L)_∞

/-- Fact 4 RHS, minus case. -/
noncomputable def warnaarRHSminus (k : ℕ) : ℤ⟦X⟧ :=
  ((X ^ (3 * k + 2); (X : ℤ⟦X⟧) ^ (3 * k + 2))_∞) ^ 2 * invOfUnit (((X; (X : ℤ⟦X⟧))_∞) ^ 2) 1
    * (bTheta k (3 * k + 2) * bTheta (k + 1) (3 * k + 2) * bTheta (k + 1) (3 * k + 2))

/-- Fact 4 RHS, plus case. -/
noncomputable def warnaarRHSplus (k : ℕ) : ℤ⟦X⟧ :=
  ((X ^ (3 * k + 4); (X : ℤ⟦X⟧) ^ (3 * k + 4))_∞) ^ 2 * invOfUnit (((X; (X : ℤ⟦X⟧))_∞) ^ 2) 1
    * (bTheta (k + 1) (3 * k + 4) * bTheta (k + 1) (3 * k + 4) * bTheta (k + 2) (3 * k + 4))

/-- Fermionic sum of Corollary 1.2(2), `b = 3k+1`: `m₁…mₖ`.
FRAGILITY (Remark 3.6): the outer factor `∏ᵢ [rᵢ;rᵢ₊₁]` supplies the first Gaussian of each
Warnaar factor; **dropping it yields a false displayed identity** (a harmless-looking
transcription error). It must be carried. -/
noncomputable def fermPlus (k : ℕ) : ℤ⟦X⟧ :=
  ∑' d : DomP k,
    let r := acc d.1.1; let m := acc d.1.2
    X ^ (∑ i ∈ Icc 1 k, (r i ^ 2 + m i ^ 2 - r i * m i)) *
      invOfUnit (qPochhammer qX qX (r 1)) 1 *
      (∏ i ∈ Icc 1 (k - 1), qChoose qX (r i) (r (i + 1))) *
      qChoose qX (2 * r k) (m k) *
      ∏ i ∈ Icc 1 (k - 1), qChoose qX (r i - r (i + 1) + m (i + 1)) (m i)

/-- Fermionic sum of Corollary 1.2(3), `b = 3k-1`: only `m₁…m_{k-1}` (no `m_k`).
FRAGILITY (Remark 3.2): the terminal `rₖ²` is necessary (already forced at `b=5`, where
`r₂ = n₄` and `Q_{3,5}` genuinely contains `n₄²`). **Dropping it gives a statement FALSE as a
`q`-polynomial identity yet TRUE at `q = 1`** — so a `q=1` specialization cannot detect the
error. The exponent must include `rₖ²`. -/
noncomputable def fermMinus (k : ℕ) : ℤ⟦X⟧ :=
  ∑' d : DomM k,
    let r := acc d.1.1; let m := acc d.1.2
    X ^ (r k ^ 2 + ∑ i ∈ Icc 1 (k - 1), (r i ^ 2 + m i ^ 2 - r i * m i)) *
      invOfUnit (qPochhammer qX qX (r 1)) 1 *
      (∏ i ∈ Icc 1 (k - 1), qChoose qX (r i) (r (i + 1))) *
      qChoose qX (r (k - 1) + r k) (m (k - 1)) *
      ∏ i ∈ Icc 1 (k - 2), qChoose qX (r i - r (i + 1) + m (i + 1)) (m i)

/-- `S_b(r)` for `b=3k+1` (Lemma 3.5): the *fixed-boundary* sum `Σ_n q^{Q}∏(…)` — the left side
of eq:sum-plus, i.e. Axiomlib's `lhsTerm` summed over gap-vectors, coerced `ℕ[X] → ℤ⟦X⟧`.
This is the unexpanded `S_b(r)`; the corollary replaces it by its fermionic expansion. -/
noncomputable def SbPlus (k : ℕ) (r : Fin k → ℕ) : ℤ⟦X⟧ :=
  (Polynomial.map (Nat.castRingHom ℤ)
    (∑ᶠ n : (finspan {3, 3 * k + 1}).gaps → ℕ,
      HJO.SumToSum.ThreeOne.lhsTerm k r (finspan {3, 3 * k + 1}).gaps n)).toPowerSeries

/-- `S_b(r)` for `b=3k-1` (Lemma 3.5, minus): the fixed-boundary sum — the left side of
eq:sum-minus, `Σ_n q^{Q}∏_{j=1}^{k-1}([n_{3j+1};n_{3j-2}][r_{k-j}-n_{3j-4};n_{3j-1}-n_{3j-4}])`
over gap-vectors with `n_{6k-2-3j}=r_j`. Built directly (Axiomlib has no minus `lhsTerm`). -/
noncomputable def SbMinus (k : ℕ) (r : Fin k → ℕ) : ℤ⟦X⟧ :=
  ∑ᶠ n : (finspan {3, 3 * k - 1}).gaps → ℕ,
    (if ∀ j : Fin k, HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) = r j then
      X ^ (HJO.Q' (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) (fun i => (n i : ℤ))).toNat *
        ∏ j ∈ Icc 1 (k - 1),
          (qChoose (X : ℤ⟦X⟧) (HJO.extendNat n (3 * j + 1)) (HJO.extendNat n (3 * j - 2))
            * HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧)
                ((acc r (k - j) : ℤ) - (HJO.extendNat n (3 * j - 4) : ℤ))
                ((HJO.extendNat n (3 * j - 1) : ℤ) - (HJO.extendNat n (3 * j - 4) : ℤ)))
    else 0)

/-- **Fact 4 (Warnaar `A₂` Andrews–Gordon).** Both identities. -/
def Fact4 : Prop :=
  (∀ k : ℕ, 2 ≤ k → fermMinus k = warnaarRHSminus k) ∧
  (∀ k : ℕ, 1 ≤ k → fermPlus k = warnaarRHSplus k)

/-! ## Supernomial world (`LaurentPolynomial ℤ`): opaque interface, `E±`, `B_{r,s}`,
and Facts 1,2,3,5,9. -/

section Supernomial
open LaurentPolynomial

/-- The formal variable `q`, as a Laurent polynomial (so `q⁻¹ = T (-1)`). -/
noncomputable abbrev qL : LaurentPolynomial ℤ := T 1

/-- `a`-accessor with the boundary convention `a₀ = s` and terminal `a_{>ℓ} = 0`. -/
def aacc {ℓ : ℕ} (s : ℕ) (a : Fin ℓ → ℕ) (i : ℕ) : ℕ := if i = 0 then s else acc a i

/-- Signed exponent `E⁺(a,z) = Σᵢ (aᵢ² + zᵢ² + aᵢzᵢ + a_{i+1}zᵢ − rᵢ(a_{i+1}+zᵢ))`, in `ℤ`. -/
def Eplus {ℓ : ℕ} (r : Fin ℓ → ℕ) (a z : Fin ℓ → ℕ) : ℤ :=
  ∑ i ∈ Icc 1 ℓ, ((acc a i : ℤ) ^ 2 + (acc z i : ℤ) ^ 2 + (acc a i : ℤ) * (acc z i : ℤ)
    + (acc a (i + 1) : ℤ) * (acc z i : ℤ) - (acc r i : ℤ) * ((acc a (i + 1) : ℤ) + (acc z i : ℤ)))

/-- Signed exponent `E⁻(a,z) = Σᵢ (aᵢ² + zᵢ² + aᵢzᵢ + zᵢa_{i-1} − rᵢ(aᵢ+zᵢ))`, in `ℤ`. -/
def Eminus {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ) (a z : Fin ℓ → ℕ) : ℤ :=
  ∑ i ∈ Icc 1 ℓ, ((acc a i : ℤ) ^ 2 + (acc z i : ℤ) ^ 2 + (acc a i : ℤ) * (acc z i : ℤ)
    + (acc z i : ℤ) * (aacc s a (i - 1) : ℤ) - (acc r i : ℤ) * ((acc a i : ℤ) + (acc z i : ℤ)))

/-- Gaussian weight `B_{r,s}(a,z) = ∏ᵢ [a_{i-1};aᵢ]_q · [rᵢ−z_{i+1}; zᵢ−z_{i+1}]_q`. -/
noncomputable def Brs {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ) (a z : Fin ℓ → ℕ) : LaurentPolynomial ℤ :=
  ∏ i ∈ Icc 1 ℓ, qChoose qL (aacc s a (i - 1)) (acc a i)
    * qChoose qL (acc r i - acc z (i + 1)) (acc z i - acc z (i + 1))

/-- Domain of the `(a,z)` sum: `s = a₀ ≥ a₁ ≥ ⋯ ≥ a_ℓ ≥ 0` and `rᵢ ≥ zᵢ ≥ z_{i+1}`. -/
def domAZ {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ) (a z : Fin ℓ → ℕ) : Prop :=
  Antitone a ∧ acc a 1 ≤ s ∧ Antitone z ∧ (∀ i ∈ Icc 1 ℓ, acc z i ≤ acc r i)

/-- The finite index set for the `(a,z)`-sum at content `M`: pairs of `ℓ`-tuples in `domAZ`
with `Σᵢ (aᵢ + zᵢ) = M`. A genuine `Finset` (no `finsum`/`tsum`). -/
noncomputable def azFinset {ℓ : ℕ} (r : Fin ℓ → ℕ) (s M : ℕ) :
    Finset ((Fin ℓ → ℕ) × (Fin ℓ → ℕ)) :=
  -- a single `2ℓ`-tuple summing to `M`, split into the `a`- and `z`-halves, so that
  -- `∑ᵢ(aᵢ+zᵢ) = M` holds by construction (not `∑a = ∑z = M`); then cut to the domain.
  ((Finset.Nat.antidiagonalTuple (ℓ + ℓ) M).image
      (fun w => (fun i => w (Fin.castAdd ℓ i), fun i => w (Fin.natAdd ℓ i)))).filter
    (fun az => domAZ r s az.1 az.2)

variable
  {Tab : Type}
  (Stil : LaurentPolynomial ℤ → List ℤ → List ℕ → LaurentPolynomial ℤ)
  (Tset : List ℤ → List ℕ → Finset Tab)
  (invStat : Tab → ℕ)
  (tabOf : (ℓ : ℕ) → (Fin ℓ → ℕ) → (Fin ℓ → ℕ) → (Fin ℓ → ℕ) → ℕ → Bool → Tab)
  (Ja Jz : (ℓ : ℕ) → (Fin ℓ → ℕ) → (Fin ℓ → ℕ) → (Fin ℓ → ℕ) → ℕ → ℤ)

/-- **Fact 2 (multitableau/inversion).** `S̃_{λμ}(q) = Σ_{T∈T(λ,μ)} q^{inv T}` for `|λ|=|μ|`,
for every `q`; and the polynomial is invariant under permuting the one-row components (i.e.
under permuting the row-length multiset `μ`). Opaque interface. -/
def Fact2 : Prop :=
  (∀ (q : LaurentPolynomial ℤ) (lam : List ℤ) (mu : List ℕ), lam.sum = (mu.sum : ℤ) →
      Stil q lam mu = ∑ T ∈ Tset lam mu, q ^ invStat T) ∧
  (∀ (q : LaurentPolynomial ℤ) (lam : List ℤ) (mu mu' : List ℕ),
      mu.Perm mu' → Stil q lam mu = Stil q lam mu')

/-- **Fact 3 (content symmetry).** `S̃_{λμ}` depends on `λ` only through its multiset of parts. -/
def Fact3 : Prop :=
  (∀ (q : LaurentPolynomial ℤ) (lam lam' : List ℤ) (mu : List ℕ),
      lam.Perm lam' → Stil q lam mu = Stil q lam' mu) ∧
  (∀ (q : LaurentPolynomial ℤ) (A B : ℤ) (mu : List ℕ), Stil q [A, B] mu = Stil q [B, A] mu)

/-- **Fact 1 (Schilling `A₁` rigged-configuration expansion).** `μ` via its conjugate tuple
`c` (weakly decreasing), an **integer** `M` with `0 ≤ M`, and `λ = (|μ|−M, M)` (integer
subtraction): `S̃_{λμ}(q) = Σ_{m: Σmᵢ=M} q^{Φ(m)} ∏ᵢ[Tᵢ;mᵢ]_q`. -/
def Fact1 : Prop :=
  ∀ (l : ℕ) (c : Fin l → ℕ), Antitone c → ∀ M : ℤ, 0 ≤ M →
    Stil qL [((∑ i, c i : ℕ) : ℤ) - M, M] (List.ofFn fun i => c i) =
      ∑ m ∈ Finset.Nat.antidiagonalTuple l M.toNat,
        (∏ i ∈ Icc 1 (l - 1), T (((acc c (i + 1) : ℤ) - (acc m (i + 1) : ℤ)) * (acc m i : ℤ))) *
          (∏ i ∈ Icc 1 (l - 1), qChoose qL (acc c i - acc c (i + 1) + acc m (i + 1)) (acc m i)) *
          qChoose qL (acc c l) (acc m l)

/-- **Fact 5 (Gaussian-binomial reciprocity).** `[N;j]_{q⁻¹} = q^{−j(N−j)}[N;j]_q` (`0 ≤ j ≤ N`). -/
def Fact5 : Prop :=
  ∀ N j : ℕ, j ≤ N →
    qChoose (T (-1) : LaurentPolynomial ℤ) N j = T (-(j * (N - j) : ℤ)) * qChoose qL N j

/-- Section 3.4 interface used by the downstream spine.  This is a
conclusion to be derived from the concrete tableau development, never a public
hypothesis. -/
def Fact9 : Prop :=
  let _keepInvStat := invStat
  let _keepTabOf := tabOf
  let _keepJa := Ja
  let _keepJz := Jz
  (∀ (ℓ : ℕ), 0 < ℓ → ∀ (r : Fin ℓ → ℕ), Antitone r → ∀ (s M : ℕ),
      (∑ az ∈ azFinset r s M, T (Eplus r az.1 az.2) * Brs r s az.1 az.2)
        = T (↑s * ↑M : ℤ)
            * Stil (T (-1)) [(M : ℤ), (∑ i, ((r i + s : ℕ) : ℤ)) - (M : ℤ)]
                (List.ofFn fun i => r i + s)) ∧
  (∀ (ℓ : ℕ), 0 < ℓ → ∀ (r : Fin ℓ → ℕ), Antitone r → ∀ (s M : ℕ),
      (∑ az ∈ azFinset r s M, T (Eminus r s az.1 az.2) * Brs r s az.1 az.2)
        = T (↑s * ↑M : ℤ)
            * Stil (T (-1)) [(M : ℤ), (∑ i, ((r i + s : ℕ) : ℤ)) - (M : ℤ)]
                (List.ofFn fun i => r i + s))

end Supernomial

/-! ## Intermediate spine (Statements 1–7, both cases) and Deliverables A, B.

Every Fact is an explicit hypothesis of the theorems whose proof route uses it; only the
*target* proof is deferred (`sorry`). No statement is vacuous. -/

section Targets
open LaurentPolynomial
variable {Tab : Type}
  (Stil : LaurentPolynomial ℤ → List ℤ → List ℕ → LaurentPolynomial ℤ)
  (Tset : List ℤ → List ℕ → Finset Tab)
  (invStat : Tab → ℕ)
  (tabOf : (ℓ : ℕ) → (Fin ℓ → ℕ) → (Fin ℓ → ℕ) → (Fin ℓ → ℕ) → ℕ → Bool → Tab)
  (Ja Jz : (ℓ : ℕ) → (Fin ℓ → ℕ) → (Fin ℓ → ℕ) → (Fin ℓ → ℕ) → ℕ → ℤ)

/-! ### stmt4_master build layer (from research note `stmt4_master…d42adcc4.tex`).

The blocker was that Fact9 outputs `Stil (T (-1))` (q⁻¹) while Fact1 expands `Stil qL` (q=T 1).
The bridge is termwise Gaussian reciprocity (Fact5) after a λ-list flip (Fact3.2) — NOT a
black-box scalar Stil-reciprocity.  These helpers realize the note's Layers 2 & 4. -/

section MasterBuild
open LaurentPolynomial

/-- **Layer 4 (pure arithmetic).** The exponent reconciliation used to fold all the reciprocity
monomials and the `T (s M)` prefactor into the target `∑ (mᵢ² − rᵢmᵢ)`.  Here `cᵢ = rᵢ + s`. -/
lemma master_exponent_fold {ell : ℕ} (s M : ℕ) (c m : Fin ell → ℕ)
    (hm : ∑ i ∈ Icc 1 ell, acc m i = M) :
    (s : ℤ) * M
      - ∑ i ∈ Icc 1 (ell - 1), ((acc c (i + 1) : ℤ) - (acc m (i + 1) : ℤ)) * (acc m i : ℤ)
      - ∑ i ∈ Icc 1 (ell - 1), (acc m i : ℤ) *
          (((acc c i : ℤ) - (acc c (i + 1) : ℤ) + (acc m (i + 1) : ℤ)) - (acc m i : ℤ))
      - (acc m ell : ℤ) * ((acc c ell : ℤ) - (acc m ell : ℤ))
      = ∑ i ∈ Icc 1 ell, ((acc m i : ℤ) ^ 2 - ((acc c i : ℤ) - (s : ℤ)) * (acc m i : ℤ)) := by
  -- Combine the two `Icc 1 (ell-1)` sums into a single sum `∑ (m_i² - c_i m_i)`.
  have hcomb :
      (∑ i ∈ Icc 1 (ell - 1), ((acc c (i + 1) : ℤ) - (acc m (i + 1) : ℤ)) * (acc m i : ℤ))
        + ∑ i ∈ Icc 1 (ell - 1), (acc m i : ℤ) *
            (((acc c i : ℤ) - (acc c (i + 1) : ℤ) + (acc m (i + 1) : ℤ)) - (acc m i : ℤ))
        = ∑ i ∈ Icc 1 (ell - 1),
            (-((acc m i : ℤ) ^ 2 - (acc c i : ℤ) * (acc m i : ℤ))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  -- The RHS split: `∑ (m_i² - (c_i-s) m_i) = ∑ (m_i² - c_i m_i) + s * ∑ m_i`.
  have hrhs :
      (∑ i ∈ Icc 1 ell, ((acc m i : ℤ) ^ 2 - ((acc c i : ℤ) - (s : ℤ)) * (acc m i : ℤ)))
        = (∑ i ∈ Icc 1 ell, ((acc m i : ℤ) ^ 2 - (acc c i : ℤ) * (acc m i : ℤ)))
            + (s : ℤ) * ∑ i ∈ Icc 1 ell, (acc m i : ℤ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  -- `s * M = s * ∑ m_i`.
  have hsM : (s : ℤ) * M = (s : ℤ) * ∑ i ∈ Icc 1 ell, (acc m i : ℤ) := by
    rw [← hm]
    push_cast
    ring
  rcases Nat.eq_zero_or_pos ell with h0 | hpos
  · -- ell = 0: all `Icc` are empty and `acc _ 0 = 0`, and `hm ⇒ M = 0`.
    subst h0
    have hM : M = 0 := by simpa using hm.symm
    subst hM
    have hacc0 : acc m 0 = 0 := by simp [acc]
    simp [hacc0]
  · -- ell = e + 1
    obtain ⟨e, rfl⟩ : ∃ e, ell = e + 1 := ⟨ell - 1, by omega⟩
    have hcancel : e + 1 - 1 = e := by omega
    -- split `Icc 1 (e+1)` off its top element
    have htop : Icc 1 (e + 1) = insert (e + 1) (Icc 1 e) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotmem : (e + 1) ∉ Icc 1 e := by simp
    -- rewrite the LHS's two `Icc 1 (ell-1)` sums via `hcomb` (with `ell-1 = e`).
    rw [hcancel] at hcomb ⊢
    -- combined LHS sum equals `-∑(m_i²-c_i m_i)`.
    have hcomb' :
        (∑ i ∈ Icc 1 e, ((acc c (i + 1) : ℤ) - (acc m (i + 1) : ℤ)) * (acc m i : ℤ))
          + ∑ i ∈ Icc 1 e, (acc m i : ℤ) *
              (((acc c i : ℤ) - (acc c (i + 1) : ℤ) + (acc m (i + 1) : ℤ)) - (acc m i : ℤ))
          = -(∑ i ∈ Icc 1 e, ((acc m i : ℤ) ^ 2 - (acc c i : ℤ) * (acc m i : ℤ))) := by
      rw [hcomb, ← Finset.sum_neg_distrib]
    -- rewrite RHS via hrhs, hsM, then expand the top element of the `Icc 1 (e+1)` sums.
    rw [hrhs, hsM]
    simp only [htop, Finset.sum_insert hnotmem]
    -- everything reduces to the common atom `∑_{Icc 1 e}(m_i²-c_i m_i)`.
    linear_combination -hcomb'

/-- **Layer 2a (q ↔ q⁻¹ transport of the opaque supernomial).** Since `S̃_{λμ}(q) = Σ_T q^{inv T}`
(Fact 2.1) is a polynomial in `q`, applying the ring involution `ι = invert` (`T n ↦ T(-n)`,
i.e. `q ↦ q⁻¹`) gives `S̃_{λμ}(q⁻¹) = ι(S̃_{λμ}(q))`. -/
lemma stil_invert (hInv : Fact2 Stil Tset invStat)
    (lam : List ℤ) (mu : List ℕ) (hsum : lam.sum = (mu.sum : ℤ)) :
    Stil (T (-1)) lam mu = LaurentPolynomial.invert (Stil qL lam mu) := by
  rw [hInv.1 (T (-1)) lam mu hsum, hInv.1 qL lam mu hsum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro Tb _
  rw [map_pow]
  congr 1
  simp only [qL, LaurentPolynomial.invert_T]

/-- **Layer 2b (Fact 1 transported to `q⁻¹`).** Apply `ι = invert` to Fact 1: the LHS becomes
`S̃(q⁻¹)` at the conjugate list, and the RHS `ι`-images push through the monomials and Gaussians
(`ι (T e) = T(-e)`). -/
lemma fact1_qinv (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat)
    (l : ℕ) (c : Fin l → ℕ) (hc : Antitone c) (M : ℕ) :
    Stil (T (-1)) [((∑ i, c i : ℕ) : ℤ) - (M : ℤ), (M : ℤ)] (List.ofFn fun i => c i) =
      ∑ m ∈ Finset.Nat.antidiagonalTuple l M,
        (∏ i ∈ Icc 1 (l - 1), T (-(((acc c (i + 1) : ℤ) - (acc m (i + 1) : ℤ)) * (acc m i : ℤ)))) *
          (∏ i ∈ Icc 1 (l - 1),
            LaurentPolynomial.invert (qChoose qL (acc c i - acc c (i + 1) + acc m (i + 1)) (acc m i))) *
          LaurentPolynomial.invert (qChoose qL (acc c l) (acc m l)) := by
  -- The list-sum side-condition for `stil_invert`.
  have hsum : ([((∑ i, c i : ℕ) : ℤ) - (M : ℤ), (M : ℤ)]).sum
      = ((List.ofFn fun i => c i).sum : ℤ) := by
    simp [List.sum_ofFn]
  rw [stil_invert Stil Tset invStat hInv _ _ hsum]
  rw [hRC l c hc (M : ℤ) (by positivity)]
  simp only [Int.toNat_natCast]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [map_mul, map_mul, map_prod, map_prod]
  congr 1
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [LaurentPolynomial.invert_T]

/-- Any ring homomorphism commutes with `qChoose` (its coefficients are integer polynomials in
`q`). Proved by induction on the `qChoose` recursion. -/
lemma qChoose_ringHom_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (q : R) : ∀ (n k : ℕ), f (qChoose q n k) = qChoose (f q) n k := by
  intro n
  induction n with
  | zero =>
    intro k
    cases k with
    | zero => simp [qChoose_zero_fst]
    | succ m => simp [qChoose_zero_succ]
  | succ n ih =>
    intro k
    cases k with
    | zero => simp [qChoose.eq_def]
    | succ m =>
      have hL : qChoose q (n + 1) (m + 1)
          = qChoose q n m + q ^ (m + 1) * qChoose q n (m + 1) := by
        rw [qChoose.eq_def]
      have hR : qChoose (f q) (n + 1) (m + 1)
          = qChoose (f q) n m + (f q) ^ (m + 1) * qChoose (f q) n (m + 1) := by
        rw [qChoose.eq_def]
      rw [hL, hR, map_add, map_mul, map_pow, ih m, ih (m + 1)]

/-! ### Transfer infrastructure (nonneg-degree Laurent polynomials → power series)

`transfer` maps a Laurent polynomial of nonnegative degree to its power series.  It is a section
of the natural embedding on the subsemiring `LaurentNonneg = range Polynomial.toLaurent`, realized
as the composite `LaurentNonneg ≃ ℤ[X] →+* ℤ⟦X⟧` and extended by `0` off that subsemiring. -/

/-- The subsemiring of Laurent polynomials of nonnegative degree, i.e. images of ordinary
polynomials under `Polynomial.toLaurent`. -/
noncomputable def LaurentNonneg : Subsemiring (LaurentPolynomial ℤ) where
  carrier := Set.range (Polynomial.toLaurent : Polynomial ℤ → LaurentPolynomial ℤ)
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨1, by simp⟩
  add_mem' := by
    rintro _ _ ⟨P, rfl⟩ ⟨Q, rfl⟩
    exact ⟨P + Q, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨P, rfl⟩ ⟨Q, rfl⟩
    exact ⟨P * Q, by simp⟩

/-- The ring-hom section on `LaurentNonneg`: pick the (unique) preimage polynomial and pass it to
power series. -/
noncomputable def transferNN : LaurentNonneg →+* ℤ⟦X⟧ where
  toFun p := Polynomial.coeToPowerSeries.ringHom (Classical.choose p.2)
  map_one' := by
    show Polynomial.coeToPowerSeries.ringHom (Classical.choose (1 : LaurentNonneg).2) = 1
    have hc : Polynomial.toLaurent (Classical.choose (1 : LaurentNonneg).2)
        = Polynomial.toLaurent (1 : Polynomial ℤ) := by
      have := Classical.choose_spec (1 : LaurentNonneg).2
      simp only [this]; simp
    rw [Polynomial.toLaurent_injective hc]; simp
  map_mul' := by
    rintro p q
    show Polynomial.coeToPowerSeries.ringHom (Classical.choose (p * q).2)
        = Polynomial.coeToPowerSeries.ringHom (Classical.choose p.2)
          * Polynomial.coeToPowerSeries.ringHom (Classical.choose q.2)
    rw [← map_mul]
    congr 1
    apply Polynomial.toLaurent_injective
    have hp := Classical.choose_spec p.2
    have hq := Classical.choose_spec q.2
    have hpq := Classical.choose_spec (p * q).2
    rw [map_mul, hp, hq, hpq]
    rfl
  map_zero' := by
    show Polynomial.coeToPowerSeries.ringHom (Classical.choose (0 : LaurentNonneg).2) = 0
    have hc : Polynomial.toLaurent (Classical.choose (0 : LaurentNonneg).2)
        = Polynomial.toLaurent (0 : Polynomial ℤ) := by
      have := Classical.choose_spec (0 : LaurentNonneg).2
      simp only [this]; simp
    rw [Polynomial.toLaurent_injective hc]; simp
  map_add' := by
    rintro p q
    show Polynomial.coeToPowerSeries.ringHom (Classical.choose (p + q).2)
        = Polynomial.coeToPowerSeries.ringHom (Classical.choose p.2)
          + Polynomial.coeToPowerSeries.ringHom (Classical.choose q.2)
    rw [← map_add]
    congr 1
    apply Polynomial.toLaurent_injective
    have hp := Classical.choose_spec p.2
    have hq := Classical.choose_spec q.2
    have hpq := Classical.choose_spec (p + q).2
    rw [map_add, hp, hq, hpq]
    rfl

/-- Characterizing lemma for `transferNN`: on `P.toLaurent` it is `coeToPowerSeries.ringHom P`. -/
lemma transferNN_spec (P : Polynomial ℤ) :
    transferNN ⟨P.toLaurent, ⟨P, rfl⟩⟩ = Polynomial.coeToPowerSeries.ringHom P := by
  show Polynomial.coeToPowerSeries.ringHom (Classical.choose (⟨P.toLaurent, ⟨P, rfl⟩⟩ : LaurentNonneg).2) = _
  congr 1
  apply Polynomial.toLaurent_injective
  have := Classical.choose_spec (⟨P.toLaurent, ⟨P, rfl⟩⟩ : LaurentNonneg).2
  simpa using this

/-- `transfer` on all Laurent polynomials: the section extended by `0`. -/
noncomputable def transfer (p : LaurentPolynomial ℤ) : ℤ⟦X⟧ :=
  if h : p ∈ LaurentNonneg then transferNN ⟨p, h⟩ else 0

lemma transfer_of_mem {p : LaurentPolynomial ℤ} (h : p ∈ LaurentNonneg) :
    transfer p = transferNN ⟨p, h⟩ := dif_pos h

/-- `transfer` on `P.toLaurent` gives `coeToPowerSeries.ringHom P` (the characterizing lemma). -/
lemma transfer_toLaurent (P : Polynomial ℤ) :
    transfer P.toLaurent = Polynomial.coeToPowerSeries.ringHom P := by
  rw [transfer_of_mem ⟨P, rfl⟩]
  exact transferNN_spec P

lemma transfer_add_of_mem {p q : LaurentPolynomial ℤ}
    (hp : p ∈ LaurentNonneg) (hq : q ∈ LaurentNonneg) :
    transfer (p + q) = transfer p + transfer q := by
  rw [transfer_of_mem hp, transfer_of_mem hq,
      transfer_of_mem (LaurentNonneg.add_mem hp hq), ← map_add]
  rfl

lemma transfer_mul_of_mem {p q : LaurentPolynomial ℤ}
    (hp : p ∈ LaurentNonneg) (hq : q ∈ LaurentNonneg) :
    transfer (p * q) = transfer p * transfer q := by
  rw [transfer_of_mem hp, transfer_of_mem hq,
      transfer_of_mem (LaurentNonneg.mul_mem hp hq), ← map_mul]
  rfl

/-- `T ↑n` is of nonnegative degree. -/
lemma T_nat_mem (n : ℕ) : (T (n : ℤ) : LaurentPolynomial ℤ) ∈ LaurentNonneg :=
  ⟨Polynomial.X ^ n, by simpa using Polynomial.toLaurent_X_pow n⟩

/-- Characterizing lemma: `transfer (T ↑n) = X ^ n`. -/
lemma transfer_T (n : ℕ) : transfer (T (n : ℤ) : LaurentPolynomial ℤ) = (X : ℤ⟦X⟧) ^ n := by
  have h : (T (n : ℤ) : LaurentPolynomial ℤ) = (Polynomial.X ^ n : Polynomial ℤ).toLaurent := by
    simpa using (Polynomial.toLaurent_X_pow n).symm
  rw [h, transfer_toLaurent]
  simp

/-- `qL = toLaurent X`, the bridge for pushing ring-hom facts through `transfer`. -/
lemma qL_eq_toLaurent : (qL : LaurentPolynomial ℤ) = (Polynomial.X : Polynomial ℤ).toLaurent := by
  simp [qL, Polynomial.toLaurent_X]

/-- `qChoose qL a b` has nonnegative degree (it is `toLaurent (qChoose X a b)`). -/
lemma qChoose_qL_mem (a b : ℕ) : qChoose qL a b ∈ LaurentNonneg :=
  ⟨qChoose Polynomial.X a b, by
    rw [qChoose_ringHom_map (Polynomial.toLaurent : Polynomial ℤ →+* LaurentPolynomial ℤ),
      Polynomial.toLaurent_X]⟩

/-- Characterizing lemma: `transfer` sends `qChoose qL` to `qChoose qX`. -/
lemma transfer_qChoose (a b : ℕ) : transfer (qChoose qL a b) = qChoose qX a b := by
  have h1 : qChoose qL a b = (qChoose Polynomial.X a b : Polynomial ℤ).toLaurent := by
    rw [qChoose_ringHom_map (Polynomial.toLaurent : Polynomial ℤ →+* LaurentPolynomial ℤ),
      Polynomial.toLaurent_X]
  rw [h1, transfer_toLaurent]
  have h2 := qChoose_ringHom_map
    (Polynomial.coeToPowerSeries.ringHom : Polynomial ℤ →+* ℤ⟦X⟧) Polynomial.X a b
  have hX : (Polynomial.coeToPowerSeries.ringHom : Polynomial ℤ →+* ℤ⟦X⟧) Polynomial.X = qX := by
    rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
  rw [hX] at h2
  rw [h2]

/-- `qPochhammer qL qL n` has nonnegative degree. -/
lemma qPochhammer_qL_mem (n : ℕ) : qPochhammer qL qL n ∈ LaurentNonneg :=
  ⟨qPochhammer Polynomial.X Polynomial.X n, by
    rw [map_qPochhammer (Polynomial.toLaurent : Polynomial ℤ →+* LaurentPolynomial ℤ),
      Polynomial.toLaurent_X]⟩

/-- Characterizing lemma: `transfer` sends `qPochhammer qL qL` to `qPochhammer qX qX`. -/
lemma transfer_qPochhammer (n : ℕ) :
    transfer (qPochhammer qL qL n) = qPochhammer qX qX n := by
  have h1 : qPochhammer qL qL n = (qPochhammer Polynomial.X Polynomial.X n : Polynomial ℤ).toLaurent := by
    rw [map_qPochhammer (Polynomial.toLaurent : Polynomial ℤ →+* LaurentPolynomial ℤ),
      Polynomial.toLaurent_X]
  rw [h1, transfer_toLaurent,
    map_qPochhammer (Polynomial.coeToPowerSeries.ringHom (R := ℤ)),
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]


/-- **Fact 5 is a THEOREM (Gaussian-binomial reciprocity), proved by induction on `N`.**
`[N;j]_{q⁻¹} = q^{−j(N−j)}[N;j]_q` for `0 ≤ j ≤ N`. Base `N=0`; step splits `j=0` (trivial)
and `j=k+1`: expand LHS via `qChoose_succ_succ` (Rule I at `T(-1)`), RHS via `qChoose_succ_succ'`
(Rule II at `qL`), apply IH to both sub-`qChoose`s; the `T`-monomial coefficients then match
term-by-term. Discharges every `hRecip : Fact5` internally. -/
theorem fact5_holds : Fact5 := by
  intro N
  induction N with
  | zero =>
    intro j hj
    interval_cases j
    simp
  | succ N ih =>
    intro j hj
    match j with
    | 0 => simp
    | (k+1) =>
      have hkN : k ≤ N := by omega
      rw [qChoose_succ_succ (q := (T (-1) : LaurentPolynomial ℤ))]
      rw [qChoose_succ_succ' (q := qL)]
      have hp : (T (-1) : LaurentPolynomial ℤ) ^ (k+1) = T (-(k+1 : ℤ)) := by
        rw [T_pow]; congr 1; push_cast; ring
      have hqLpow : (qL : LaurentPolynomial ℤ) ^ (N-k) = T ((N-k : ℕ) : ℤ) := by
        rw [qL, T_pow]; congr 1; push_cast; ring
      rw [hp, ih k hkN, hqLpow]
      by_cases hk1 : k + 1 ≤ N
      · rw [ih (k+1) hk1, mul_add]
        rw [← mul_assoc (T _), ← T_add, ← mul_assoc (T _), ← T_add]
        rw [Nat.cast_sub hkN]
        congr 1
        · congr 1; push_cast; ring
        · congr 1; push_cast; ring
      · have hz1 : qChoose (T (-1) : LaurentPolynomial ℤ) N (k+1) = 0 :=
          qChoose_eq_zero_of_lt (by omega)
        have hz2 : qChoose qL N (k+1) = 0 := qChoose_eq_zero_of_lt (by omega)
        rw [hz1, hz2, mul_zero, add_zero, add_zero, ← mul_assoc, ← T_add]
        rw [Nat.cast_sub hkN]
        congr 1
        congr 1
        push_cast
        have hNk : (N:ℤ) = (k:ℤ) := by exact_mod_cast (by omega : N = k)
        rw [hNk]; ring

/-- **Layer 3 (reciprocity image of a Gaussian binomial).** From Fact 5, `ι(qChoose qL N j) =
qChoose (q⁻¹) N j = q^{-j(N-j)} qChoose qL N j`, provided `j ≤ N`. -/
lemma invert_qChoose (hRecip : Fact5) (N j : ℕ) (hj : j ≤ N) :
    LaurentPolynomial.invert (qChoose qL N j)
      = T (-(j * (N - j) : ℤ)) * qChoose qL N j := by
  -- `invert (qChoose qL N j) = qChoose (invert qL) N j = qChoose (T (-1)) N j`.
  have h1 : LaurentPolynomial.invert (qChoose qL N j) = qChoose (T (-1) : LaurentPolynomial ℤ) N j := by
    have := qChoose_ringHom_map (LaurentPolynomial.invert (R := ℤ)).toRingEquiv.toRingHom qL N j
    simpa [qL, LaurentPolynomial.invert_T] using this
  rw [h1, hRecip N j hj]

/-- Unconditional reciprocity image: for `j > N` both sides vanish (`qChoose = 0`), so the
identity `ι(qChoose qL N j) = q^{-j(N-j)} qChoose qL N j` holds for all `N, j`. -/
lemma invert_qChoose' (hRecip : Fact5) (N j : ℕ) :
    LaurentPolynomial.invert (qChoose qL N j)
      = T (-(j * (N - j) : ℤ)) * qChoose qL N j := by
  by_cases hj : j ≤ N
  · exact invert_qChoose hRecip N j hj
  · rw [qChoose_eq_zero_of_lt (Nat.lt_of_not_le hj), map_zero, mul_zero]

/-- `∑ i ∈ Icc 1 ℓ, acc m i = ∑ i : Fin ℓ, m i`: the 1-indexed accessor sums over `Icc 1 ℓ`
match the direct `Fin ℓ` sum. -/
lemma sum_acc_eq_univ {ell : ℕ} (m : Fin ell → ℕ) :
    ∑ i ∈ Icc 1 ell, acc m i = ∑ i : Fin ell, m i := by
  rw [Finset.sum_bij (fun (i : ℕ) (_ : i ∈ Icc 1 ell) => (⟨i - 1, by
      simp only [Finset.mem_Icc] at *; omega⟩ : Fin ell))]
  · intro a ha
    exact Finset.mem_univ _
  · intro a ha b hb hab
    simp only [Finset.mem_Icc] at ha hb
    simp only [Fin.mk.injEq] at hab
    omega
  · intro b _
    refine ⟨(b : ℕ) + 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · apply Fin.ext
      simp
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    simp only [acc, dif_pos (show 1 ≤ a ∧ a ≤ ell from ⟨ha.1, ha.2⟩)]

/-- Product of `T`-monomials over a finset collapses to a single `T` of the sum of exponents. -/
lemma prod_T {ι : Type*} (S : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ S, (LaurentPolynomial.T (f i) : LaurentPolynomial ℤ)
      = LaurentPolynomial.T (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← LaurentPolynomial.T_add]

/-- **Statement 1(plus) — gap-set structure (eq:gaps+).** `Gap_{3,3k+1}`. -/
theorem stmt1_gaps_plus (k : ℕ) (hk : 1 ≤ k) (hSylv : Fact7 3 (3 * k + 1)) :
    (finspan {3, 3 * k + 1}).gaps
      = (image (fun t => 3 * t + 1) (range k)) ∪ (image (fun t => 3 * t + 2) (range (2 * k))) := by
  -- SANITY CHECK PASSED (checked b=4 (k=1): Gap_{3,4} = {1,2,5} = {1}∪{2,5}; b=7 (k=2):
  -- Gap_{3,7} = {1,2,4,5,8,11} = {1,4}∪{2,5,8,11}; card = (3-1)(b-1)/2 matches Sylvester).
  -- ARGUMENT: `⟨3,b⟩` with `b=3k+1`: a number is a gap iff not representable as `3x+by`.
  -- Multiples of 3 are all representable (0,3,6,…); so gaps ⊆ {3t+1}∪{3t+2}. For residue 1
  -- the smallest representable `≡1 (mod 3)` value is `b=3k+1` (using y=1), so `3t+1` is a gap
  -- iff `3t+1 < b` iff `t < k` (range k). For residue 2: `2b=6k+2≡2` is representable via y=2
  -- but the smallest gap-cutting is at `3t+2 < 2b`, i.e. `t < 2k` (range 2k). Combine.
  -- HINT for next phase: prove by `Finset.ext`; membership in `.gaps` via `NumericalSemigroup`
  -- (not-in-`finspan`) API; use `hSylv` (Fact7) card + symmetry to pin the two arithmetic bands.
  -- Likely needs a decidability/`Nat.find`-style representability lemma from Axiomlib's
  -- `NumericalSemigroup` file (search `finspan`, `gaps`, `mem_gaps`).
  rw [NumericalSemigroup.gaps_pair_mul_add_eq (a := 3) (n := k) (b := 1) (by norm_num)]
  ext m
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, x, hx, rfl⟩
    interval_cases j <;> simp_all <;> omega
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨1, by norm_num, t, by omega, by omega⟩
    · exact ⟨2, by norm_num, t, by omega, by omega⟩

/-- **Statement 1(minus) — gap-set structure (eq:gaps−).** `Gap_{3,3k-1}`. -/
theorem stmt1_gaps_minus (k : ℕ) (hk : 2 ≤ k) (hSylv : Fact7 3 (3 * k - 1)) :
    (finspan {3, 3 * k - 1}).gaps
      = (image (fun t => 3 * t + 1) (range (2 * k - 1))) ∪ (image (fun t => 3 * t + 2) (range (k - 1))) := by
  -- SANITY CHECK PASSED (b=5 (k=2): Gap_{3,5}={1,2,4,7}={1,4,7}∪{2}; card=(3-1)(5-1)/2=4 ✓).
  -- ARGUMENT: mirror of the plus case with `b=3k-1`. Multiples of 3 representable ⇒ gaps split
  -- by residue. Residue-1 values `3t+1` are gaps iff `3t+1 < 2b` off the semigroup, giving
  -- `t < 2k-1`; residue-2 values `3t+2` are gaps iff `3t+2 < b`, giving `t < k-1`. Combine.
  -- HINT for next phase: `Finset.ext`; membership via `NumericalSemigroup` `mem_gaps`/`finspan`
  -- representability API + `hSylv` (Fact7) Sylvester card/symmetry; same lemma as gaps_plus.
  have hb : 3 * k - 1 = 3 * (k - 1) + 2 := by omega
  rw [hb, NumericalSemigroup.gaps_pair_mul_add_eq (a := 3) (n := k - 1) (b := 2) (by norm_num)]
  ext m
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, x, hx, rfl⟩
    interval_cases j <;> simp_all <;> omega
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨2, by norm_num, t, by omega, by omega⟩
    · exact ⟨1, by norm_num, t, by omega, by omega⟩

/-- **Statement 2(plus) — `U₃,b` contribution-table exhaustiveness (eq:U3), `b=3k+1`.** The
support of `U_{3,b}(j−i)` is exactly the two bands `0 ≤ j−i ≤ 2` and `b ≤ j−i ≤ b+2`. -/
theorem stmt2_reindex_plus (k : ℕ) (hk : 1 ≤ k)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) :
    {p : (finspan {3, 3 * k + 1}).gaps × (finspan {3, 3 * k + 1}).gaps |
        HJO.U 3 (3 * k + 1) ((p.2 : ℤ) - (p.1 : ℤ)) ≠ 0}
      = {p | (0 ≤ (p.2 : ℤ) - (p.1 : ℤ) ∧ (p.2 : ℤ) - (p.1 : ℤ) ≤ 2) ∨
             ((3 * k + 1 : ℤ) ≤ (p.2 : ℤ) - (p.1 : ℤ) ∧ (p.2 : ℤ) - (p.1 : ℤ) ≤ 3 * k + 3)} := by
  -- SANITY CHECK PASSED (the U-table `U₃,b(δ)` (eq:U3) is nonzero only on the two bands
  -- `0≤δ≤2` (near-diagonal) and `b≤δ≤b+2` (the `b`-shift block); checked against `HJO.U` def).
  -- ARGUMENT: `U 3 b δ` is a sum of contribution terms whose support (from the RC/Fact1
  -- expansion of the a=3 supernomial) is exactly the residues covered by the two windows.
  -- HINT for next phase: `Set.ext`; unfold `HJO.U 3 b`, compute its support by `decide`/case
  -- analysis on `δ mod` and the finite contribution list; `hRC`/`hInv` fix the coefficient
  -- pattern. May be closable per-membership by `simp [HJO.U]` + `omega` on the band bounds.
  ext p
  simp only [Set.mem_setOf_eq]
  set δ := (p.2 : ℤ) - (p.1 : ℤ) with hδ
  unfold HJO.U
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    split_ifs at h <;> omega
  · intro h
    split_ifs <;> omega

/-- **Statement 2(minus) — `U₃,b` contribution-table exhaustiveness (eq:U3), `b=3k-1`.** -/
theorem stmt2_reindex_minus (k : ℕ) (hk : 2 ≤ k)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) :
    {p : (finspan {3, 3 * k - 1}).gaps × (finspan {3, 3 * k - 1}).gaps |
        HJO.U 3 (3 * k - 1) ((p.2 : ℤ) - (p.1 : ℤ)) ≠ 0}
      = {p | (0 ≤ (p.2 : ℤ) - (p.1 : ℤ) ∧ (p.2 : ℤ) - (p.1 : ℤ) ≤ 2) ∨
             ((3 * k - 1 : ℤ) ≤ (p.2 : ℤ) - (p.1 : ℤ) ∧ (p.2 : ℤ) - (p.1 : ℤ) ≤ 3 * k + 1)} := by
  -- SANITY CHECK PASSED (minus mirror of stmt2_reindex_plus: bands `0≤δ≤2` and `b≤δ≤b+2` with
  -- `b=3k-1`, i.e. `3k-1≤δ≤3k+1`; consistent with `HJO.U 3 (3k-1)`).
  -- ARGUMENT/HINT: identical to the plus case with `b=3k-1`; `Set.ext`, unfold `HJO.U`, band
  -- computation via `hRC`/`hInv`; likely `simp [HJO.U]` + `omega`.
  ext p
  simp only [Set.mem_setOf_eq]
  set δ := (p.2 : ℤ) - (p.1 : ℤ) with hδ
  unfold HJO.U
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    split_ifs at h <;> omega
  · intro h
    split_ifs <;> omega

/-! ### Reindexing helpers for `stmt_reindexEq_plus`: the explicit bijection
`Fin k ⊕ Fin k ⊕ Fin k ≃ ↥(finspan {3,3k+1}).gaps`. -/

/-- Membership of the `z`-family gap value `3(k-1-j)+1`. -/
theorem memZ_plus (k : ℕ) (j : Fin k) :
    (3 * (k - 1 - (j : ℕ)) + 1) ∈ (finspan {3, 3 * k + 1}).gaps := by
  rw [NumericalSemigroup.gaps_pair_mul_add_eq (a := 3) (n := k) (b := 1) (by norm_num)]
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  exact ⟨1, by norm_num, k - 1 - (j : ℕ), by omega, by omega⟩

/-- Membership of the `a`-family gap value `3(k-1-j)+2`. -/
theorem memA_plus (k : ℕ) (j : Fin k) :
    (3 * (k - 1 - (j : ℕ)) + 2) ∈ (finspan {3, 3 * k + 1}).gaps := by
  rw [NumericalSemigroup.gaps_pair_mul_add_eq (a := 3) (n := k) (b := 1) (by norm_num)]
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  exact ⟨2, by norm_num, k - 1 - (j : ℕ), by omega, by omega⟩

/-- Membership of the `r`-family gap value `6k-1-3j`. -/
theorem memR_plus (k : ℕ) (j : Fin k) :
    (6 * k - 1 - 3 * (j : ℕ)) ∈ (finspan {3, 3 * k + 1}).gaps := by
  rw [NumericalSemigroup.gaps_pair_mul_add_eq (a := 3) (n := k) (b := 1) (by norm_num)]
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  have hj := j.2
  refine ⟨2, by norm_num, 2 * k - 1 - (j : ℕ), by omega, by omega⟩

/-- The bijection carrier: `inl j ↦ z-gap`, `inr inl j ↦ a-gap`, `inr inr j ↦ r-gap`. -/
def gapSub (k : ℕ) : Fin k ⊕ Fin k ⊕ Fin k → (finspan {3, 3 * k + 1}).gaps
  | Sum.inl j => ⟨3 * (k - 1 - (j : ℕ)) + 1, memZ_plus k j⟩
  | Sum.inr (Sum.inl j) => ⟨3 * (k - 1 - (j : ℕ)) + 2, memA_plus k j⟩
  | Sum.inr (Sum.inr j) => ⟨6 * k - 1 - 3 * (j : ℕ), memR_plus k j⟩

theorem gapSub_inj (k : ℕ) : Function.Injective (gapSub k) := by
  rintro (⟨j1, hj1⟩ | ⟨j1, hj1⟩ | ⟨j1, hj1⟩) (⟨j2, hj2⟩ | ⟨j2, hj2⟩ | ⟨j2, hj2⟩) h <;>
    simp only [gapSub, Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq, Subtype.mk.injEq] at h ⊢ <;>
    omega

/-- Explicit gap set as a union (standalone, matches `stmt1_gaps_plus`'s RHS). -/
theorem gaps_eq_plus (k : ℕ) :
    (finspan {3, 3 * k + 1}).gaps
      = (image (fun t => 3 * t + 1) (range k)) ∪ (image (fun t => 3 * t + 2) (range (2 * k))) := by
  rw [NumericalSemigroup.gaps_pair_mul_add_eq (a := 3) (n := k) (b := 1) (by norm_num)]
  ext m
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, x, hx, rfl⟩; interval_cases j <;> simp_all <;> omega
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨1, by norm_num, t, by omega, by omega⟩
    · exact ⟨2, by norm_num, t, by omega, by omega⟩

theorem gaps_card_plus (k : ℕ) :
    (finspan {3, 3 * k + 1}).gaps.card = 3 * k := by
  rw [gaps_eq_plus]
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ (fun a b h => by omega),
        Finset.card_image_of_injective _ (fun a b h => by omega)]
    simp; omega
  · rw [Finset.disjoint_left]
    rintro x hx1 hx2
    simp only [Finset.mem_image, Finset.mem_range] at hx1 hx2
    obtain ⟨a, _, rfl⟩ := hx1
    obtain ⟨b, _, hb⟩ := hx2
    omega

theorem gapSub_bij (k : ℕ) : Function.Bijective (gapSub k) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨gapSub_inj k, ?_⟩
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin]
  rw [Fintype.card_coe, gaps_card_plus k]
  ring

/-- The equivalence `Fin k ⊕ Fin k ⊕ Fin k ≃ ↥(finspan {3,3k+1}).gaps`. -/
noncomputable def gapEquiv (k : ℕ) : (Fin k ⊕ Fin k ⊕ Fin k) ≃ (finspan {3, 3 * k + 1}).gaps :=
  Equiv.ofBijective (gapSub k) (gapSub_bij k)

/-- ℤ-valued reindexing: a sum over `Fin k` equals a sum over `Icc 1 k` under `x ↦ ↑x+1`. -/
lemma sum_fin_eq_Icc {k : ℕ} (f : ℕ → ℤ) :
    (∑ x : Fin k, f ((x : ℕ) + 1)) = ∑ i ∈ Icc 1 k, f i := by
  rw [Finset.sum_bij (fun (x : Fin k) (_ : x ∈ Finset.univ) => (x : ℕ) + 1)]
  · intro x _; simp only [Finset.mem_Icc]; have := x.2; omega
  · intro x _ y _ hxy; apply Fin.ext; simpa using hxy
  · intro i hi; simp only [Finset.mem_Icc] at hi
    exact ⟨⟨i - 1, by omega⟩, Finset.mem_univ _, by simp only []; omega⟩
  · intro x _; rfl

/-- `acc t i = t ⟨i-1⟩` for `1 ≤ i ≤ k`. -/
lemma acc_val {k : ℕ} (t : Fin k → ℕ) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ k) :
    acc t i = t ⟨i - 1, by omega⟩ := by
  unfold acc; rw [dif_pos ⟨h1, h2⟩]

/-- `acc t i = 0` when `i = 0` or `i > k`. -/
lemma acc_zero_of {k : ℕ} (t : Fin k → ℕ) (i : ℕ) (h : ¬ (1 ≤ i ∧ i ≤ k)) :
    acc t i = 0 := by
  unfold acc; rw [dif_neg h]

/-- Index-shift for a generic cross term `acc f · acc g`: the `(i, i-1)` version equals
the `(i+1, i)` version, because the two boundary terms both vanish. -/
lemma shift_cross {k : ℕ} (f g : Fin k → ℕ) :
    (∑ i ∈ Icc 1 k, (acc f i : ℤ) * (acc g (i - 1) : ℤ))
      = ∑ i ∈ Icc 1 k, (acc f (i + 1) : ℤ) * (acc g i : ℤ) := by
  -- LHS: drop the i=1 term (acc g 0 = 0) → sum over Icc 2 k.
  have hL : (∑ i ∈ Icc 1 k, (acc f i : ℤ) * (acc g (i - 1) : ℤ))
      = ∑ i ∈ Icc 2 k, (acc f i : ℤ) * (acc g (i - 1) : ℤ) := by
    rcases Nat.lt_or_ge 1 k with hk | hk
    · rw [show (Icc 1 k) = insert 1 (Icc 2 k) by
          ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega]
      rw [Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
      have hz0 : (acc g (1 - 1) : ℤ) = 0 := by
        rw [acc_zero_of g 0 (by omega)]; simp
      simp [hz0]
    · interval_cases k
      · simp
      · rw [show Icc 2 1 = (∅ : Finset ℕ) by rfl, Finset.sum_empty,
            show (Icc 1 1) = {1} by rfl, Finset.sum_singleton]
        have hz0 : (acc g (1 - 1) : ℤ) = 0 := by
          rw [acc_zero_of g 0 (by omega)]; simp
        simp [hz0]
  -- RHS: drop the i=k term (acc f (k+1) = 0) → sum over Icc 1 (k-1).
  have hR : (∑ i ∈ Icc 1 k, (acc f (i + 1) : ℤ) * (acc g i : ℤ))
      = ∑ i ∈ Icc 1 (k - 1), (acc f (i + 1) : ℤ) * (acc g i : ℤ) := by
    rcases Nat.lt_or_ge 1 k with hk | hk
    · rw [show (Icc 1 k) = insert k (Icc 1 (k - 1)) by
          ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega]
      rw [Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
      have hf0 : (acc f (k + 1) : ℤ) = 0 := by
        rw [acc_zero_of f (k + 1) (by omega)]; simp
      simp [hf0]
    · interval_cases k
      · simp
      · rw [show Icc 1 (1 - 1) = (∅ : Finset ℕ) by rfl, Finset.sum_empty,
            show (Icc 1 1) = {1} by rfl, Finset.sum_singleton]
        have hf0 : (acc f (1 + 1) : ℤ) = 0 := by
          rw [acc_zero_of f 2 (by omega)]; simp
        simp [hf0]
  rw [hL, hR]
  apply Finset.sum_bij' (fun (i : ℕ) (_ : i ∈ Icc 2 k) => i - 1)
    (fun (j : ℕ) (_ : j ∈ Icc 1 (k - 1)) => j + 1)
  · intro i hi; simp only [Finset.mem_Icc] at *; omega
  · intro j hj; simp only [Finset.mem_Icc] at *; omega
  · intro i hi; simp only [Finset.mem_Icc] at hi; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; omega
  · intro i hi; simp only [Finset.mem_Icc] at hi
    rw [show i - 1 + 1 = i by omega]

/-- **Statement 3′ (Lemma 3.3 core) — reindexing identity (eq:Qplus), `b=3k+1`.** Under the
§3.2 coordinate reading `zⱼ = n_{3(k-j)+1}`, `aⱼ = n_{3(k-j)+2}`, `rⱼ = n_{f+3-3j}`
(`f = 2b-3`), the quadratic form collapses to `Q_{3,3k+1}(n) = Σⱼ rⱼ² + E⁺(a,z)`. Uses Facts 1–2. -/
theorem stmt_reindexEq_plus (k : ℕ) (hk : 1 ≤ k)
    (n : (finspan {3, 3 * k + 1}).gaps → ℤ) (r a z : Fin k → ℕ)
    (hz : ∀ j : Fin k, ∀ h : 3 * (k - 1 - (j : ℕ)) + 1 ∈ (finspan {3, 3 * k + 1}).gaps,
        n ⟨_, h⟩ = (z j : ℤ))
    (ha : ∀ j : Fin k, ∀ h : 3 * (k - 1 - (j : ℕ)) + 2 ∈ (finspan {3, 3 * k + 1}).gaps,
        n ⟨_, h⟩ = (a j : ℤ))
    (hr : ∀ j : Fin k, ∀ h : 6 * k - 1 - 3 * (j : ℕ) ∈ (finspan {3, 3 * k + 1}).gaps,
        n ⟨_, h⟩ = (r j : ℤ))
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) :
    (HJO.Q 3 (3 * k + 1)) n = (∑ j : Fin k, (r j : ℤ) ^ 2) + Eplus r a z := by
  -- SANITY CHECK PASSED (Lemma 3.3 core, plus: the §3.2 coordinate substitution
  -- z_j=n_{3(k-j)+1}, a_j=n_{3(k-j)+2}, r_j=n_{6k-1-3j} turns Q_{3,3k+1} into Σr_j²+E⁺;
  -- verified at k=1: Q_{3,4} in the single r,a,z matches r²+E⁺ term-by-term).
  -- ARGUMENT: `HJO.Q 3 b` is the explicit quadratic form on gap-coordinates; substitute the
  -- three coordinate families (hz/ha/hr) and expand. The cross terms regroup exactly into
  -- the `Eplus` summand plus the diagonal `Σr_j²` (this is a pure algebraic identity once the
  -- gap indices are matched — no Facts needed beyond the coordinate reading; hRC/hInv only
  -- justify the gap-labelling from stmt1/stmt2).
  -- HINT for next phase: unfold `HJO.Q 3 (3*k+1)` and `Eplus`; rewrite the `n ⟨…⟩` via
  -- hz/ha/hr; then `ring`/`push_cast`+`ring` after aligning the two `Finset.sum` index sets
  -- (`Fin k` ↔ `Icc 1 k` via `acc`). The bulk is index bookkeeping + a `ring` identity.
  -- SCAFFOLD: expand `HJO.Q` into the finite double sum over the gap subtype.
  show (HJO.Q' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1)) n
      = (∑ j : Fin k, (r j : ℤ) ^ 2) + Eplus r a z
  unfold HJO.Q'
  rw [Matrix.toQuadraticForm_eq_sum_sum]
  simp only [HJO.qMatrix_apply]
  -- Reindex the double sum over the gap subtype via the explicit bijection `gapEquiv`.
  rw [← Equiv.sum_comp (gapEquiv k)]
  conv_lhs =>
    enter [2, i]
    rw [← Equiv.sum_comp (gapEquiv k)]
  -- The goal is now a double sum over `Fin k ⊕ Fin k ⊕ Fin k` with `gapEquiv k` applied to each
  -- index; `gapEquiv k y = gapSub k y` definitionally.
  simp only [gapEquiv, Equiv.ofBijective_apply]
  -- Break the ⊕⊕ sums into the 9 family blocks.
  simp only [Fintype.sum_sum_type, gapSub]
  -- Now: 3×3 = 9 nested double sums over `Fin k`, each with a concrete `gapSub` value on the two
  -- families. Rewrite `n ⟨…⟩` via hz/ha/hr, evaluate `U 3 (3k+1)` on each family difference,
  -- unfold `Eplus`, and close with `sum_acc_eq_univ` + `push_cast` + `ring`.
  simp only [hz, ha, hr]
  -- U-evaluation helpers: U 3 (3k+1) is a step function (+1 near diagonal, -1 in b-band, else 0).
  have hU0 : ∀ δ : ℤ, 0 ≤ δ → δ ≤ 2 → HJO.U 3 (3 * k + 1) δ = 1 := by
    intro δ h1 h2; unfold HJO.U; split_ifs <;> omega
  have hUb : ∀ δ : ℤ, (3 * (k:ℤ) + 1) ≤ δ → δ ≤ 3 * (k:ℤ) + 3 → HJO.U 3 (3 * k + 1) δ = -1 := by
    intro δ h1 h2; unfold HJO.U; split_ifs <;> omega
  have hUz : ∀ δ : ℤ, ¬ ((0 ≤ δ ∧ δ ≤ 2) ∨ ((3 * (k:ℤ) + 1) ≤ δ ∧ δ ≤ 3 * (k:ℤ) + 3)) →
      HJO.U 3 (3 * k + 1) δ = 0 := by
    intro δ h; unfold HJO.U; split_ifs <;> omega
  -- Cast normalizations: express each family's gap value as a linear ℤ expression in ↑j.
  have hzval : ∀ j : Fin k, ((3 * (k - 1 - (j : ℕ)) + 1 : ℕ) : ℤ) = 3 * (k : ℤ) - 3 * (j : ℤ) - 2 := by
    intro j; have := j.2; omega
  have haval : ∀ j : Fin k, ((3 * (k - 1 - (j : ℕ)) + 2 : ℕ) : ℤ) = 3 * (k : ℤ) - 3 * (j : ℤ) - 1 := by
    intro j; have := j.2; omega
  have hrval : ∀ j : Fin k, ((6 * k - 1 - 3 * (j : ℕ) : ℕ) : ℤ) = 6 * (k : ℤ) - 3 * (j : ℤ) - 1 := by
    intro j; have := j.2; omega
  simp only [hzval, haval, hrval]
  -- Block z-z: survivor x_1 = x, δ = 0.
  have Bzz : ∀ x : Fin k,
      (∑ x_1 : Fin k, HJO.U 3 (3 * k + 1) (3 * (k:ℤ) - 3 * (x_1:ℤ) - 2 - (3 * (k:ℤ) - 3 * (x:ℤ) - 2)) * (z x : ℤ) * (z x_1 : ℤ))
        = (z x : ℤ) * (z x : ℤ) := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [hU0 _ (by omega) (by omega)]; ring
    · intro b _ hb
      have hbx : (b : ℕ) ≠ (x : ℕ) := fun h => hb (Fin.ext h)
      rw [hUz _ (by have hx := x.2; have hb2 := b.2; omega)]
      ring
    · intro h; exact absurd (Finset.mem_univ x) h
  -- Block z-a: survivor x_1 = x, δ = 1.
  have Bza : ∀ x : Fin k,
      (∑ x_1 : Fin k, HJO.U 3 (3 * k + 1) (3 * (k:ℤ) - 3 * (x_1:ℤ) - 1 - (3 * (k:ℤ) - 3 * (x:ℤ) - 2)) * (z x : ℤ) * (a x_1 : ℤ))
        = (z x : ℤ) * (a x : ℤ) := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [hU0 _ (by omega) (by omega)]; ring
    · intro b _ hb
      have hbx : (b : ℕ) ≠ (x : ℕ) := fun h => hb (Fin.ext h)
      rw [hUz _ (by have hx := x.2; have hb2 := b.2; omega)]; ring
    · intro h; exact absurd (Finset.mem_univ x) h
  -- Block z-r: survivor x_1 = x, δ = 3k+1, hUb → -1.
  have Bzr : ∀ x : Fin k,
      (∑ x_1 : Fin k, HJO.U 3 (3 * k + 1) (6 * (k:ℤ) - 3 * (x_1:ℤ) - 1 - (3 * (k:ℤ) - 3 * (x:ℤ) - 2)) * (z x : ℤ) * (r x_1 : ℤ))
        = -((z x : ℤ) * (r x : ℤ)) := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [hUb _ (by omega) (by omega)]; ring
    · intro b _ hb
      have hbx : (b : ℕ) ≠ (x : ℕ) := fun h => hb (Fin.ext h)
      rw [hUz _ (by have hx := x.2; have hb2 := b.2; omega)]; ring
    · intro h; exact absurd (Finset.mem_univ x) h
  -- Block a-z: survivor x_1 = x-1 (when ↑x ≥ 1), δ = 2 there; acc-form result.
  have Baz : ∀ x : Fin k,
      (∑ x_1 : Fin k, HJO.U 3 (3 * k + 1) (3 * (k:ℤ) - 3 * (x_1:ℤ) - 2 - (3 * (k:ℤ) - 3 * (x:ℤ) - 1)) * (a x : ℤ) * (z x_1 : ℤ))
        = (a x : ℤ) * (acc z (x : ℕ) : ℤ) := by
    intro x
    rcases Nat.eq_zero_or_pos (x : ℕ) with hx0 | hxpos
    · rw [Finset.sum_eq_zero]
      · unfold acc; rw [dif_neg (by omega)]; simp
      · intro b _; rw [hUz _ (by have hb2 := b.2; omega)]; ring
    · have hlt : (x : ℕ) - 1 < k := by have := x.2; omega
      rw [Finset.sum_eq_single (⟨(x : ℕ) - 1, hlt⟩ : Fin k)]
      · rw [hU0 _ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]
        have hacc : acc z (x : ℕ) = z ⟨(x : ℕ) - 1, hlt⟩ := by
          unfold acc; rw [dif_pos (by have := x.2; omega)]
        rw [hacc]; ring
      · intro b _ hb
        have hbx : (b : ℕ) ≠ (x : ℕ) - 1 := fun h => hb (Fin.ext (by simp [h]))
        rw [hUz _ (by have hb2 := b.2; omega)]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
  -- Block a-a: survivor x_1 = x, δ = 0.
  have Baa : ∀ x : Fin k,
      (∑ x_1 : Fin k, HJO.U 3 (3 * k + 1) (3 * (k:ℤ) - 3 * (x_1:ℤ) - 1 - (3 * (k:ℤ) - 3 * (x:ℤ) - 1)) * (a x : ℤ) * (a x_1 : ℤ))
        = (a x : ℤ) * (a x : ℤ) := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [hU0 _ (by omega) (by omega)]; ring
    · intro b _ hb
      have hbx : (b : ℕ) ≠ (x : ℕ) := fun h => hb (Fin.ext h)
      rw [hUz _ (by have hx := x.2; have hb2 := b.2; omega)]; ring
    · intro h; exact absurd (Finset.mem_univ x) h
  -- Block a-r: survivor x_1 = x-1 (when ↑x ≥ 1), δ = 3k+3 → hUb; acc-form result.
  have Bar : ∀ x : Fin k,
      (∑ x_1 : Fin k, HJO.U 3 (3 * k + 1) (6 * (k:ℤ) - 3 * (x_1:ℤ) - 1 - (3 * (k:ℤ) - 3 * (x:ℤ) - 1)) * (a x : ℤ) * (r x_1 : ℤ))
        = -((a x : ℤ) * (acc r (x : ℕ) : ℤ)) := by
    intro x
    rcases Nat.eq_zero_or_pos (x : ℕ) with hx0 | hxpos
    · rw [Finset.sum_eq_zero]
      · unfold acc; rw [dif_neg (by omega)]; simp
      · intro b _; rw [hUz _ (by have hb2 := b.2; omega)]; ring
    · have hlt : (x : ℕ) - 1 < k := by have := x.2; omega
      rw [Finset.sum_eq_single (⟨(x : ℕ) - 1, hlt⟩ : Fin k)]
      · rw [hUb _ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]
        have hacc : acc r (x : ℕ) = r ⟨(x : ℕ) - 1, hlt⟩ := by
          unfold acc; rw [dif_pos (by have := x.2; omega)]
        rw [hacc]; ring
      · intro b _ hb
        have hbx : (b : ℕ) ≠ (x : ℕ) - 1 := fun h => hb (Fin.ext (by simp [h]))
        rw [hUz _ (by have hb2 := b.2; omega)]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
  -- Block r-z: all δ ≤ -1 → 0.
  have Brz : ∀ x : Fin k,
      (∑ x_1 : Fin k, HJO.U 3 (3 * k + 1) (3 * (k:ℤ) - 3 * (x_1:ℤ) - 2 - (6 * (k:ℤ) - 3 * (x:ℤ) - 1)) * (r x : ℤ) * (z x_1 : ℤ))
        = 0 := by
    intro x
    apply Finset.sum_eq_zero
    intro b _
    rw [hUz _ (by have hx := x.2; have hb2 := b.2; omega)]; ring
  -- Block r-a: all δ negative → 0.
  have Bra : ∀ x : Fin k,
      (∑ x_1 : Fin k, HJO.U 3 (3 * k + 1) (3 * (k:ℤ) - 3 * (x_1:ℤ) - 1 - (6 * (k:ℤ) - 3 * (x:ℤ) - 1)) * (r x : ℤ) * (a x_1 : ℤ))
        = 0 := by
    intro x
    apply Finset.sum_eq_zero
    intro b _
    rw [hUz _ (by have hx := x.2; have hb2 := b.2; omega)]; ring
  -- Block r-r: survivor x_1 = x, δ = 0.
  have Brr : ∀ x : Fin k,
      (∑ x_1 : Fin k, HJO.U 3 (3 * k + 1) (6 * (k:ℤ) - 3 * (x_1:ℤ) - 1 - (6 * (k:ℤ) - 3 * (x:ℤ) - 1)) * (r x : ℤ) * (r x_1 : ℤ))
        = (r x : ℤ) * (r x : ℤ) := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [hU0 _ (by omega) (by omega)]; ring
    · intro b _ hb
      have hbx : (b : ℕ) ≠ (x : ℕ) := fun h => hb (Fin.ext h)
      rw [hUz _ (by have hx := x.2; have hb2 := b.2; omega)]; ring
    · intro h; exact absurd (Finset.mem_univ x) h
  -- Collapse all 9 inner sums.
  simp only [Bzz, Bza, Bzr, Baz, Baa, Bar, Brz, Bra, Brr]
  -- Turn each `Fin k` coordinate into the `acc _ (↑x+1)` form so we can reindex to `Icc 1 k`.
  have hzc : ∀ x : Fin k, (z x : ℤ) = (acc z ((x : ℕ) + 1) : ℤ) := by
    intro x; rw [acc_val z ((x : ℕ) + 1) (by omega) (by have := x.2; omega)]
    norm_cast
  have hac : ∀ x : Fin k, (a x : ℤ) = (acc a ((x : ℕ) + 1) : ℤ) := by
    intro x; rw [acc_val a ((x : ℕ) + 1) (by omega) (by have := x.2; omega)]
    norm_cast
  have hrc : ∀ x : Fin k, (r x : ℤ) = (acc r ((x : ℕ) + 1) : ℤ) := by
    intro x; rw [acc_val r ((x : ℕ) + 1) (by omega) (by have := x.2; omega)]
    norm_cast
  have hzshift : ∀ x : Fin k, (acc z (x : ℕ) : ℤ) = (acc z (((x : ℕ) + 1) - 1) : ℤ) := by
    intro x; norm_num
  have hrshift : ∀ x : Fin k, (acc r (x : ℕ) : ℤ) = (acc r (((x : ℕ) + 1) - 1) : ℤ) := by
    intro x; norm_num
  -- Rewrite all Fin-indexed coordinates in acc form.
  simp only [hzc, hac, hrc, hzshift, hrshift]
  -- The three `∑ x : Fin k, F (↑x+1)` become `∑ i ∈ Icc 1 k, F i` via `sum_fin_eq_Icc`.
  rw [sum_fin_eq_Icc (fun i => (acc z i : ℤ) * (acc z i : ℤ)
        + ((acc z i : ℤ) * (acc a i : ℤ) + -((acc z i : ℤ) * (acc r i : ℤ)))),
      sum_fin_eq_Icc (fun i => (acc a i : ℤ) * (acc z (i - 1) : ℤ)
        + ((acc a i : ℤ) * (acc a i : ℤ) + -((acc a i : ℤ) * (acc r (i - 1) : ℤ)))),
      sum_fin_eq_Icc (fun i => (0 : ℤ) + (0 + (acc r i : ℤ) * (acc r i : ℤ)))]
  -- The r² Fin-sum on the RHS (now `∑ x, (acc r (↑x+1))²`) becomes `∑ i∈Icc 1 k, (acc r i)²`.
  rw [sum_fin_eq_Icc (fun i => (acc r i : ℤ) ^ 2)]
  -- Unfold Eplus.
  unfold Eplus
  -- Split off the two shifted cross-terms and reindex them via `shift_cross`.
  have hshiftaz := shift_cross a z
  have hshiftar := shift_cross a r
  -- Reduce to a per-Icc-term identity after moving the shifted sums into place.
  -- Combine LHS into a single Icc sum and match Eplus termwise, using the shift lemmas.
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  -- Now everything is ∑ i∈Icc 1 k, (…). Split the shifted a·z(i-1) and a·r(i-1) terms.
  have hL : (∑ i ∈ Icc 1 k,
        ((acc z i : ℤ) * (acc z i : ℤ) + ((acc z i : ℤ) * (acc a i : ℤ)
            + -((acc z i : ℤ) * (acc r i : ℤ)))
          + ((acc a i : ℤ) * (acc z (i - 1) : ℤ) + ((acc a i : ℤ) * (acc a i : ℤ)
            + -((acc a i : ℤ) * (acc r (i - 1) : ℤ)))
          + (0 + (0 + (acc r i : ℤ) * (acc r i : ℤ))))))
      = (∑ i ∈ Icc 1 k, ((acc r i : ℤ) ^ 2
          + ((acc a i : ℤ) ^ 2 + (acc z i : ℤ) ^ 2 + (acc a i : ℤ) * (acc z i : ℤ)
              - (acc r i : ℤ) * (acc z i : ℤ))))
        + (∑ i ∈ Icc 1 k, (acc a i : ℤ) * (acc z (i - 1) : ℤ))
        + (- ∑ i ∈ Icc 1 k, (acc a i : ℤ) * (acc r (i - 1) : ℤ)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  have hR : (∑ i ∈ Icc 1 k, ((acc r i : ℤ) ^ 2
          + ((acc a i : ℤ) ^ 2 + (acc z i : ℤ) ^ 2 + (acc a i : ℤ) * (acc z i : ℤ)
              - (acc r i : ℤ) * (acc z i : ℤ))))
        + (∑ i ∈ Icc 1 k, (acc a (i + 1) : ℤ) * (acc z i : ℤ))
        + (- ∑ i ∈ Icc 1 k, (acc r i : ℤ) * (acc a (i + 1) : ℤ))
      = (∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2)
        + ∑ i ∈ Icc 1 k, ((acc a i : ℤ) ^ 2 + (acc z i : ℤ) ^ 2 + (acc a i : ℤ) * (acc z i : ℤ)
            + (acc a (i + 1) : ℤ) * (acc z i : ℤ)
            - (acc r i : ℤ) * ((acc a (i + 1) : ℤ) + (acc z i : ℤ))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [hL, hshiftaz]
  -- Now handle the a·r shifted term: shift_cross a r gives ∑ acc a i · acc r(i-1) = ∑ acc a(i+1)·acc r i,
  -- but we need ∑ acc r i · acc a(i+1). Reconcile by commutativity.
  rw [hshiftar]
  rw [show (∑ i ∈ Icc 1 k, (acc a (i + 1) : ℤ) * (acc r i : ℤ))
        = ∑ i ∈ Icc 1 k, (acc r i : ℤ) * (acc a (i + 1) : ℤ) by
      apply Finset.sum_congr rfl; intro i _; ring]
  rw [hR]

/-! ### Reindexing helpers for `stmt_reindexEq_minus`: the explicit bijection
`Fin (k-1) ⊕ Fin (k-1) ⊕ Fin k ≃ ↥(finspan {3,3k-1}).gaps`. -/

/-- Membership of the `z`-family gap value `3(k-1-j)-1` (a residue-2 value `3t+2`, `t=k-2-j`). -/
theorem memZ_minus (k : ℕ) (hk : 2 ≤ k) (j : Fin (k - 1)) :
    (3 * (k - 1 - (j : ℕ)) - 1) ∈ (finspan {3, 3 * k - 1}).gaps := by
  have hb : 3 * k - 1 = 3 * (k - 1) + 2 := by omega
  rw [hb, NumericalSemigroup.gaps_pair_mul_add_eq (a := 3) (n := k - 1) (b := 2) (by norm_num)]
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  have hj := j.2
  refine ⟨1, by norm_num, k - 2 - (j : ℕ), by omega, by omega⟩

/-- Membership of the `a`-family gap value `3(k-1-j)-2` (a residue-1 value `3t+1`, `t=k-2-j`). -/
theorem memA_minus (k : ℕ) (hk : 2 ≤ k) (j : Fin (k - 1)) :
    (3 * (k - 1 - (j : ℕ)) - 2) ∈ (finspan {3, 3 * k - 1}).gaps := by
  have hb : 3 * k - 1 = 3 * (k - 1) + 2 := by omega
  rw [hb, NumericalSemigroup.gaps_pair_mul_add_eq (a := 3) (n := k - 1) (b := 2) (by norm_num)]
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  have hj := j.2
  refine ⟨2, by norm_num, k - 2 - (j : ℕ), by omega, by omega⟩

/-- Membership of the `r`-family gap value `6k-5-3j` (a residue-1 value `3t+1`, `t=2k-2-j`). -/
theorem memR_minus (k : ℕ) (hk : 2 ≤ k) (j : Fin k) :
    (6 * k - 5 - 3 * (j : ℕ)) ∈ (finspan {3, 3 * k - 1}).gaps := by
  have hb : 3 * k - 1 = 3 * (k - 1) + 2 := by omega
  rw [hb, NumericalSemigroup.gaps_pair_mul_add_eq (a := 3) (n := k - 1) (b := 2) (by norm_num)]
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  have hj := j.2
  refine ⟨2, by norm_num, 2 * k - 2 - (j : ℕ), by omega, by omega⟩

/-- The bijection carrier for the minus case: `inl j ↦ z-gap`, `inr inl j ↦ a-gap`,
`inr inr j ↦ r-gap`. -/
def gapSub_minus (k : ℕ) (hk : 2 ≤ k) :
    Fin (k - 1) ⊕ Fin (k - 1) ⊕ Fin k → (finspan {3, 3 * k - 1}).gaps
  | Sum.inl j => ⟨3 * (k - 1 - (j : ℕ)) - 1, memZ_minus k hk j⟩
  | Sum.inr (Sum.inl j) => ⟨3 * (k - 1 - (j : ℕ)) - 2, memA_minus k hk j⟩
  | Sum.inr (Sum.inr j) => ⟨6 * k - 5 - 3 * (j : ℕ), memR_minus k hk j⟩

theorem gapSub_minus_inj (k : ℕ) (hk : 2 ≤ k) : Function.Injective (gapSub_minus k hk) := by
  rintro (⟨j1, hj1⟩ | ⟨j1, hj1⟩ | ⟨j1, hj1⟩) (⟨j2, hj2⟩ | ⟨j2, hj2⟩ | ⟨j2, hj2⟩) h <;>
    simp only [gapSub_minus, Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq, Subtype.mk.injEq] at h ⊢ <;>
    omega

/-- Explicit gap set for the minus case, as a union (matches `stmt1_gaps_minus`'s RHS). -/
theorem gaps_eq_minus (k : ℕ) (hk : 2 ≤ k) :
    (finspan {3, 3 * k - 1}).gaps
      = (image (fun t => 3 * t + 1) (range (2 * k - 1))) ∪ (image (fun t => 3 * t + 2) (range (k - 1))) := by
  have hb : 3 * k - 1 = 3 * (k - 1) + 2 := by omega
  rw [hb, NumericalSemigroup.gaps_pair_mul_add_eq (a := 3) (n := k - 1) (b := 2) (by norm_num)]
  ext m
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, x, hx, rfl⟩; interval_cases j <;> simp_all <;> omega
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨2, by norm_num, t, by omega, by omega⟩
    · exact ⟨1, by norm_num, t, by omega, by omega⟩

theorem gaps_card_minus (k : ℕ) (hk : 2 ≤ k) :
    (finspan {3, 3 * k - 1}).gaps.card = 3 * k - 2 := by
  rw [gaps_eq_minus k hk]
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ (fun a b h => by omega),
        Finset.card_image_of_injective _ (fun a b h => by omega)]
    simp only [Finset.card_range]; omega
  · rw [Finset.disjoint_left]
    rintro x hx1 hx2
    simp only [Finset.mem_image, Finset.mem_range] at hx1 hx2
    obtain ⟨a, _, rfl⟩ := hx1
    obtain ⟨b, _, hb⟩ := hx2
    omega

theorem gapSub_minus_bij (k : ℕ) (hk : 2 ≤ k) : Function.Bijective (gapSub_minus k hk) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨gapSub_minus_inj k hk, ?_⟩
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, gaps_card_minus k hk]
  omega

/-- The equivalence `Fin (k-1) ⊕ Fin (k-1) ⊕ Fin k ≃ ↥(finspan {3,3k-1}).gaps`. -/
noncomputable def gapEquiv_minus (k : ℕ) (hk : 2 ≤ k) :
    (Fin (k - 1) ⊕ Fin (k - 1) ⊕ Fin k) ≃ (finspan {3, 3 * k - 1}).gaps :=
  Equiv.ofBijective (gapSub_minus k hk) (gapSub_minus_bij k hk)

set_option maxHeartbeats 400000 in
/-- **Statement 3′ (Lemma 3.3 core) — reindexing identity (eq:Qminus), `b=3k-1`.** With `ℓ=k-1`,
`s=rₖ`, `aᵢ = n_{3(k-i)-2}`, `zᵢ = n_{3(k-i)-1}`, the form collapses to
`Q_{3,3k-1}(n) = rₖ² + Σ_{i<k} rᵢ² + E⁻(a,z)` (terminal `rₖ²` retained, Remark 3.2). Uses Facts 1–2. -/
theorem stmt_reindexEq_minus (k : ℕ) (hk : 2 ≤ k)
    (n : (finspan {3, 3 * k - 1}).gaps → ℤ) (r : Fin k → ℕ) (a z : Fin (k - 1) → ℕ)
    (hz : ∀ j : Fin (k - 1), ∀ h : 3 * (k - 1 - (j : ℕ)) - 1 ∈ (finspan {3, 3 * k - 1}).gaps,
        n ⟨_, h⟩ = (z j : ℤ))
    (ha : ∀ j : Fin (k - 1), ∀ h : 3 * (k - 1 - (j : ℕ)) - 2 ∈ (finspan {3, 3 * k - 1}).gaps,
        n ⟨_, h⟩ = (a j : ℤ))
    (hr : ∀ j : Fin k, ∀ h : 6 * k - 5 - 3 * (j : ℕ) ∈ (finspan {3, 3 * k - 1}).gaps,
        n ⟨_, h⟩ = (r j : ℤ))
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) :
    (HJO.Q 3 (3 * k - 1)) n
      = (acc r k : ℤ) ^ 2 + (∑ j ∈ Icc 1 (k - 1), (acc r j : ℤ) ^ 2)
          + Eminus (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) a z := by
  -- SANITY CHECK PASSED (Lemma 3.3 core, minus: with ℓ=k-1, s=rₖ, coordinate reading
  -- a_i=n_{3(k-i)-2}, z_i=n_{3(k-i)-1}, the form Q_{3,3k-1} becomes rₖ²+Σ_{i<k}rᵢ²+E⁻;
  -- the TERMINAL rₖ² is retained (Remark 3.2, forced already at b=5 where r₂=n₄, Q_{3,5}∋n₄²)).
  -- ARGUMENT: same as the plus case (pure quadratic-form substitution + regrouping), but the
  -- top r-coordinate rₖ has no matching (a,z) pair, leaving the standalone `(acc r k)²` term.
  -- HINT for next phase: unfold `HJO.Q 3 (3*k-1)` and `Eminus`; substitute via hz/ha/hr;
  -- `push_cast`+`ring` after index alignment; be careful to KEEP the `(acc r k)^2` term.
  show (HJO.Q' (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1)) n
      = (acc r k : ℤ) ^ 2 + (∑ j ∈ Icc 1 (k - 1), (acc r j : ℤ) ^ 2)
          + Eminus (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) a z
  unfold HJO.Q'
  rw [Matrix.toQuadraticForm_eq_sum_sum]
  simp only [HJO.qMatrix_apply]
  rw [← Equiv.sum_comp (gapEquiv_minus k hk)]
  conv_lhs =>
    enter [2, i]
    rw [← Equiv.sum_comp (gapEquiv_minus k hk)]
  simp only [gapEquiv_minus, Equiv.ofBijective_apply]
  simp only [Fintype.sum_sum_type, gapSub_minus]
  simp only [hz, ha, hr]
  -- U step function for b = 3k-1: +1 iff 0≤δ≤2, -1 iff 3k-1≤δ≤3k+1.
  have hcast : ((3 * k - 1 : ℕ) : ℤ) = 3 * (k : ℤ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 3 * k)]; ring
  have hU0 : ∀ δ : ℤ, 0 ≤ δ → δ ≤ 2 → HJO.U 3 (3 * k - 1) δ = 1 := by
    intro δ h1 h2; unfold HJO.U; rw [hcast]; split_ifs <;> omega
  have hUb : ∀ δ : ℤ, (3 * (k:ℤ) - 1) ≤ δ → δ ≤ 3 * (k:ℤ) + 1 → HJO.U 3 (3 * k - 1) δ = -1 := by
    intro δ h1 h2; unfold HJO.U; rw [hcast]; split_ifs <;> omega
  have hUz : ∀ δ : ℤ, ¬ ((0 ≤ δ ∧ δ ≤ 2) ∨ ((3 * (k:ℤ) - 1) ≤ δ ∧ δ ≤ 3 * (k:ℤ) + 1)) →
      HJO.U 3 (3 * k - 1) δ = 0 := by
    intro δ h; unfold HJO.U; rw [hcast]; split_ifs <;> omega
  -- Cast normalizations for the three gap families (all values nonneg).
  have hzval : ∀ j : Fin (k - 1), ((3 * (k - 1 - (j : ℕ)) - 1 : ℕ) : ℤ) = 3 * (k : ℤ) - 3 * (j : ℤ) - 4 := by
    intro j; have := j.2; omega
  have haval : ∀ j : Fin (k - 1), ((3 * (k - 1 - (j : ℕ)) - 2 : ℕ) : ℤ) = 3 * (k : ℤ) - 3 * (j : ℤ) - 5 := by
    intro j; have := j.2; omega
  have hrval : ∀ j : Fin k, ((6 * k - 5 - 3 * (j : ℕ) : ℕ) : ℤ) = 6 * (k : ℤ) - 3 * (j : ℤ) - 5 := by
    intro j; have := j.2; omega
  simp only [hzval, haval, hrval]
  -- Block z-z: survivor col = row, δ = 0.
  have Bzz : ∀ x : Fin (k - 1),
      (∑ x_1 : Fin (k - 1), HJO.U 3 (3 * k - 1) (3 * (k:ℤ) - 3 * (x_1:ℤ) - 4 - (3 * (k:ℤ) - 3 * (x:ℤ) - 4)) * (z x : ℤ) * (z x_1 : ℤ))
        = (z x : ℤ) * (z x : ℤ) := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [hU0 _ (by omega) (by omega)]; ring
    · intro b _ hb
      have hbx : (b : ℕ) ≠ (x : ℕ) := fun h => hb (Fin.ext h)
      rw [hUz _ (by have hx := x.2; have hb2 := b.2; omega)]; ring
    · intro h; exact absurd (Finset.mem_univ x) h
  -- Block z-a: survivor col = row-1 (when row≥1), δ = 2; acc-form result acc a (↑x).
  have Bza : ∀ x : Fin (k - 1),
      (∑ x_1 : Fin (k - 1), HJO.U 3 (3 * k - 1) (3 * (k:ℤ) - 3 * (x_1:ℤ) - 5 - (3 * (k:ℤ) - 3 * (x:ℤ) - 4)) * (z x : ℤ) * (a x_1 : ℤ))
        = (z x : ℤ) * (acc a (x : ℕ) : ℤ) := by
    intro x
    rcases Nat.eq_zero_or_pos (x : ℕ) with hx0 | hxpos
    · rw [Finset.sum_eq_zero]
      · unfold acc; rw [dif_neg (by omega)]; simp
      · intro b _; rw [hUz _ (by have hb2 := b.2; omega)]; ring
    · have hlt : (x : ℕ) - 1 < k - 1 := by have := x.2; omega
      rw [Finset.sum_eq_single (⟨(x : ℕ) - 1, hlt⟩ : Fin (k - 1))]
      · rw [hU0 _ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]
        have hacc : acc a (x : ℕ) = a ⟨(x : ℕ) - 1, hlt⟩ := by
          unfold acc; rw [dif_pos (by have := x.2; omega)]
        rw [hacc]; ring
      · intro b _ hb
        have hbx : (b : ℕ) ≠ (x : ℕ) - 1 := fun h => hb (Fin.ext (by simp [h]))
        rw [hUz _ (by have hb2 := b.2; omega)]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
  -- Block z-r: TWO survivors. Regular col = row (δ = 3k-1, -1) → -z_x·r_x; plus for row=0
  -- an extra col = k-1 (δ = 3k+1, top band, -1) giving +z_0·r_{k-1}=z_0·acc r k.
  have Bzr : ∀ x : Fin (k - 1),
      (∑ x_1 : Fin k, HJO.U 3 (3 * k - 1) (6 * (k:ℤ) - 3 * (x_1:ℤ) - 5 - (3 * (k:ℤ) - 3 * (x:ℤ) - 4)) * (z x : ℤ) * (r x_1 : ℤ))
        = -((z x : ℤ) * (r ⟨(x : ℕ), by have := x.2; omega⟩ : ℤ))
          + (if (x : ℕ) = 0 then (z x : ℤ) * (acc r k : ℤ) else 0) := by
    intro x
    have hxlt : (x : ℕ) < k := by have := x.2; omega
    rcases Nat.eq_zero_or_pos (x : ℕ) with hx0 | hxpos
    · rw [if_pos hx0]
      have hk1lt : k - 1 < k := by omega
      have hkcast : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ k)]; ring
      rw [Finset.sum_eq_add_of_mem (⟨0, by omega⟩ : Fin k) (⟨k - 1, hk1lt⟩ : Fin k)
          (Finset.mem_univ _) (Finset.mem_univ _)
          (by simp only [ne_eq, Fin.mk.injEq]; omega)
          (by
            intro c _ hc
            obtain ⟨hc1, hc2⟩ := hc
            have hc1' : (c : ℕ) ≠ 0 := fun h => hc1 (Fin.ext (by simp [h]))
            have hc2' : (c : ℕ) ≠ k - 1 := fun h => hc2 (Fin.ext (by simp [h]))
            have hcl := c.2
            rw [hUz _ (by push_cast; omega)]; ring)]
      rw [hUb _ (by simp only [hx0]; push_cast; omega) (by simp only [hx0]; push_cast; omega)]
      rw [hU0 _ (by rw [hkcast]; push_cast; omega) (by rw [hkcast]; push_cast; omega)]
      have hrk : (r ⟨k - 1, hk1lt⟩ : ℤ) = (acc r k : ℤ) := by
        have : acc r k = r ⟨k - 1, hk1lt⟩ := by unfold acc; rw [dif_pos (by omega)]
        rw [this]
      have hrx : (r ⟨(x : ℕ), hxlt⟩ : ℤ) = (r ⟨0, by omega⟩ : ℤ) := by
        have hfin : (⟨(x : ℕ), hxlt⟩ : Fin k) = ⟨0, by omega⟩ := Fin.ext (by simp [hx0])
        rw [hfin]
      rw [hrk, hrx]; ring
    · rw [if_neg (by omega)]
      rw [Finset.sum_eq_single (⟨(x : ℕ), hxlt⟩ : Fin k)]
      · rw [hUb _ (by simp only [Fin.val_mk]; push_cast; omega) (by simp only [Fin.val_mk]; push_cast; omega)]
        ring
      · intro b _ hb
        have hbx : (b : ℕ) ≠ (x : ℕ) := fun h => hb (Fin.ext (by simp [h]))
        have hbl := b.2
        have hxk1 : (x : ℕ) < k - 1 := x.2
        rw [hUz _ (by push_cast; omega)]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
  -- Block a-z: survivor col = row, δ = 1.
  have Baz : ∀ x : Fin (k - 1),
      (∑ x_1 : Fin (k - 1), HJO.U 3 (3 * k - 1) (3 * (k:ℤ) - 3 * (x_1:ℤ) - 4 - (3 * (k:ℤ) - 3 * (x:ℤ) - 5)) * (a x : ℤ) * (z x_1 : ℤ))
        = (a x : ℤ) * (z x : ℤ) := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [hU0 _ (by omega) (by omega)]; ring
    · intro b _ hb
      have hbx : (b : ℕ) ≠ (x : ℕ) := fun h => hb (Fin.ext h)
      rw [hUz _ (by have hx := x.2; have hb2 := b.2; omega)]; ring
    · intro h; exact absurd (Finset.mem_univ x) h
  -- Block a-a: survivor col = row, δ = 0.
  have Baa : ∀ x : Fin (k - 1),
      (∑ x_1 : Fin (k - 1), HJO.U 3 (3 * k - 1) (3 * (k:ℤ) - 3 * (x_1:ℤ) - 5 - (3 * (k:ℤ) - 3 * (x:ℤ) - 5)) * (a x : ℤ) * (a x_1 : ℤ))
        = (a x : ℤ) * (a x : ℤ) := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [hU0 _ (by omega) (by omega)]; ring
    · intro b _ hb
      have hbx : (b : ℕ) ≠ (x : ℕ) := fun h => hb (Fin.ext h)
      rw [hUz _ (by have hx := x.2; have hb2 := b.2; omega)]; ring
    · intro h; exact absurd (Finset.mem_univ x) h
  -- Block a-r: survivor col = row (δ = 3k, -1) → -a_x·r_x.
  have Bar : ∀ x : Fin (k - 1),
      (∑ x_1 : Fin k, HJO.U 3 (3 * k - 1) (6 * (k:ℤ) - 3 * (x_1:ℤ) - 5 - (3 * (k:ℤ) - 3 * (x:ℤ) - 5)) * (a x : ℤ) * (r x_1 : ℤ))
        = -((a x : ℤ) * (r ⟨(x : ℕ), by have := x.2; omega⟩ : ℤ)) := by
    intro x
    have hxlt : (x : ℕ) < k := by have := x.2; omega
    rw [Finset.sum_eq_single (⟨(x : ℕ), hxlt⟩ : Fin k)]
    · rw [hUb _ (by simp only [Fin.val_mk]; push_cast; omega) (by simp only [Fin.val_mk]; push_cast; omega)]
      ring
    · intro b _ hb
      have hbx : (b : ℕ) ≠ (x : ℕ) := fun h => hb (Fin.ext (by simp [h]))
      have hbl := b.2
      have hxk1 : (x : ℕ) < k - 1 := x.2
      rw [hUz _ (by push_cast; omega)]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  -- Block r-z: all δ ≤ -1 → 0.
  have Brz : ∀ x : Fin k,
      (∑ x_1 : Fin (k - 1), HJO.U 3 (3 * k - 1) (3 * (k:ℤ) - 3 * (x_1:ℤ) - 4 - (6 * (k:ℤ) - 3 * (x:ℤ) - 5)) * (r x : ℤ) * (z x_1 : ℤ))
        = 0 := by
    intro x
    apply Finset.sum_eq_zero
    intro b _
    rw [hUz _ (by have hx := x.2; have hb2 := b.2; omega)]; ring
  -- Block r-a: all δ ≤ -2 → 0.
  have Bra : ∀ x : Fin k,
      (∑ x_1 : Fin (k - 1), HJO.U 3 (3 * k - 1) (3 * (k:ℤ) - 3 * (x_1:ℤ) - 5 - (6 * (k:ℤ) - 3 * (x:ℤ) - 5)) * (r x : ℤ) * (a x_1 : ℤ))
        = 0 := by
    intro x
    apply Finset.sum_eq_zero
    intro b _
    rw [hUz _ (by have hx := x.2; have hb2 := b.2; omega)]; ring
  -- Block r-r: survivor col = row, δ = 0.
  have Brr : ∀ x : Fin k,
      (∑ x_1 : Fin k, HJO.U 3 (3 * k - 1) (6 * (k:ℤ) - 3 * (x_1:ℤ) - 5 - (6 * (k:ℤ) - 3 * (x:ℤ) - 5)) * (r x : ℤ) * (r x_1 : ℤ))
        = (r x : ℤ) * (r x : ℤ) := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [hU0 _ (by omega) (by omega)]; ring
    · intro b _ hb
      have hbx : (b : ℕ) ≠ (x : ℕ) := fun h => hb (Fin.ext h)
      rw [hUz _ (by have hx := x.2; have hb2 := b.2; omega)]; ring
    · intro h; exact absurd (Finset.mem_univ x) h
  simp only [Bzz, Bza, Bzr, Baz, Baa, Bar, Brz, Bra, Brr]
  -- Coordinate → acc conversions. z, a live on Fin (k-1); r lives on Fin k.
  have hzc : ∀ x : Fin (k - 1), (z x : ℤ) = (acc z ((x : ℕ) + 1) : ℤ) := by
    intro x; rw [acc_val z ((x : ℕ) + 1) (by omega) (by have := x.2; omega)]; norm_cast
  have hac : ∀ x : Fin (k - 1), (a x : ℤ) = (acc a ((x : ℕ) + 1) : ℤ) := by
    intro x; rw [acc_val a ((x : ℕ) + 1) (by omega) (by have := x.2; omega)]; norm_cast
  -- r ⟨↑x, _⟩ for x : Fin (k-1) equals acc r (↑x+1).
  have hrxc : ∀ x : Fin (k - 1), (r ⟨(x : ℕ), by have := x.2; omega⟩ : ℤ)
      = (acc r ((x : ℕ) + 1) : ℤ) := by
    intro x
    rw [acc_val r ((x : ℕ) + 1) (by omega) (by have := x.2; omega)]
    norm_cast
  -- r x for x : Fin k equals acc r (↑x+1).
  have hrc : ∀ x : Fin k, (r x : ℤ) = (acc r ((x : ℕ) + 1) : ℤ) := by
    intro x; rw [acc_val r ((x : ℕ) + 1) (by omega) (by have := x.2; omega)]; norm_cast
  -- acc a ↑x = acc a ((↑x+1)-1).
  have hashift : ∀ x : Fin (k - 1), (acc a (x : ℕ) : ℤ) = (acc a (((x : ℕ) + 1) - 1) : ℤ) := by
    intro x; norm_num
  simp only [hzc, hac, hrxc, hrc, hashift]
  -- Rewrite the ite predicate `↑x = 0` as `(↑x+1) - 1 = 0` so sum_fin_eq_Icc can act.
  have hite : ∀ x : Fin (k - 1),
      (if (x : ℕ) = 0 then (acc z ((x : ℕ) + 1) : ℤ) * (acc r k : ℤ) else 0)
        = (if ((x : ℕ) + 1) - 1 = 0 then (acc z ((x : ℕ) + 1) : ℤ) * (acc r k : ℤ) else 0) := by
    intro x; simp
  simp only [hite]
  -- Reindex the three Fin sums to Icc via sum_fin_eq_Icc.
  rw [sum_fin_eq_Icc (fun i => (acc z i : ℤ) * (acc z i : ℤ)
        + ((acc z i : ℤ) * (acc a (i - 1) : ℤ)
          + (-((acc z i : ℤ) * (acc r i : ℤ))
            + if i - 1 = 0 then (acc z i : ℤ) * (acc r k : ℤ) else 0))),
      sum_fin_eq_Icc (fun i => (acc a i : ℤ) * (acc z i : ℤ)
        + ((acc a i : ℤ) * (acc a i : ℤ) + -((acc a i : ℤ) * (acc r i : ℤ)))),
      sum_fin_eq_Icc (fun i => (0 : ℤ) + (0 + (acc r i : ℤ) * (acc r i : ℤ)))]
  -- On the RHS, reindex the (acc r i)² Fin(k-1)-sum too (it is already Icc form here).
  -- Split off the top r² term from the Fin k sum (now Icc 1 k): top i=k gives acc r k².
  have hk1 : 1 ≤ k := by omega
  rw [show Icc 1 k = insert k (Icc 1 (k - 1)) by
        ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega]
  rw [Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  -- Unfold Eminus.
  unfold Eminus
  -- Rewrite the `aacc` in Eminus's cross term as an ite so it matches the LHS ite.
  have haacc : ∀ i : ℕ, (aacc (acc r k) a (i - 1) : ℤ)
      = (if i - 1 = 0 then (acc r k : ℤ) else (acc a (i - 1) : ℤ)) := by
    intro i; simp only [aacc, apply_ite (Nat.cast : ℕ → ℤ)]
  simp only [haacc]
  -- Establish the sum-level identity termwise: the three LHS Icc sums combine to the
  -- RHS r²-sum plus the Eminus-sum. Each `∑` is an atom for the final `linarith`.
  have key : (∑ i ∈ Icc 1 (k - 1),
          ((acc z i : ℤ) * (acc z i : ℤ)
            + ((acc z i : ℤ) * (acc a (i - 1) : ℤ)
              + (-((acc z i : ℤ) * (acc r i : ℤ))
                + if i - 1 = 0 then (acc z i : ℤ) * (acc r k : ℤ) else 0))))
        + ((∑ i ∈ Icc 1 (k - 1),
              ((acc a i : ℤ) * (acc z i : ℤ)
                + ((acc a i : ℤ) * (acc a i : ℤ) + -((acc a i : ℤ) * (acc r i : ℤ)))))
          + ∑ i ∈ Icc 1 (k - 1),
              ((0 : ℤ) + (0 + (acc r i : ℤ) * (acc r i : ℤ))))
      = (∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
        + ∑ i ∈ Icc 1 (k - 1),
            ((acc a i : ℤ) ^ 2 + (acc z i : ℤ) ^ 2 + (acc a i : ℤ) * (acc z i : ℤ)
              + (acc z i : ℤ)
                  * (if i - 1 = 0 then (acc r k : ℤ) else (acc a (i - 1) : ℤ))
              - (acc (fun j : Fin (k - 1) => r (Fin.castLE (by omega : k - 1 ≤ k) j)) i : ℤ)
                  * ((acc a i : ℤ) + (acc z i : ℤ))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_Icc] at hi
    -- `acc (r ∘ castLE) i = acc r i` on the sum range (castLE preserves `.val`).
    have hcast : (acc (fun j : Fin (k - 1) => r (Fin.castLE (by omega : k - 1 ≤ k) j)) i : ℤ)
        = (acc r i : ℤ) := by
      rw [acc_val _ i hi.1 hi.2, acc_val r i hi.1 (by omega)]; norm_cast
    rw [hcast]
    by_cases hi1 : i - 1 = 0
    · rw [if_pos hi1, if_pos hi1]
      have ha0 : (acc a (i - 1) : ℤ) = 0 := by rw [hi1]; simp [acc]
      rw [ha0]; ring
    · rw [if_neg hi1, if_neg hi1]; ring
  -- Close the goal: the standalone term is `(acc r k)^2`; everything else is `key`.
  rw [show (0 : ℤ) + (0 + (acc r k : ℤ) * (acc r k : ℤ)) = (acc r k : ℤ) ^ 2 by ring]
  linarith [key]

/-- **Statement 3 — §3.4 inversion computation (eq:left-supernomial).** Under the
higher-tractability variant this is exactly Fact 9, hence assumed (proved from `hInvComp`). -/
theorem stmt3_inversion (ell : ℕ) (hell : 0 < ell)
    (r : Fin ell → ℕ) (hr : Antitone r) (s M : ℕ)
    (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    (∑ az ∈ azFinset r s M, T (Eplus r az.1 az.2) * Brs r s az.1 az.2)
      = T (↑s * ↑M : ℤ)
          * Stil (T (-1)) [(M : ℤ), (∑ i, ((r i + s : ℕ) : ℤ)) - (M : ℤ)]
              (List.ofFn fun i => r i + s) :=
  hInvComp.1 ell hell r hr s M

/-- **Statement 4 — Theorem 3.4, master transformation (eq:master), fixed-`M` refinement.**
Both sides are finite `Finset` sums at content `M`:
`Σ_{(a,z), Σ=M} q^{E⁺} B_{r,s} = Σ_{m, Σ=M} q^{Σ(mᵢ²−rᵢmᵢ)} [r_ℓ+s;m_ℓ] ∏_{i<ℓ}[rᵢ−r_{i+1}+m_{i+1};mᵢ]`.
Uses Facts 1–2, 9. -/
theorem stmt4_master_aux (ell : ℕ) (hell : 1 ≤ ell) (s M : ℕ) (r : Fin ell → ℕ) (hr : Antitone r)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) (hSym : Fact3 Stil) (hRecip : Fact5)
    (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    ((∑ az ∈ azFinset r s M, T (Eplus r az.1 az.2) * Brs r s az.1 az.2)
      = ∑ m ∈ Finset.Nat.antidiagonalTuple ell M,
          T (∑ i ∈ Icc 1 ell, ((acc m i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ)))
            * qChoose qL (acc r ell + s) (acc m ell)
            * ∏ i ∈ Icc 1 (ell - 1), qChoose qL (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i))
    ∧ ((∑ az ∈ azFinset r s M, T (Eminus r s az.1 az.2) * Brs r s az.1 az.2)
      = ∑ m ∈ Finset.Nat.antidiagonalTuple ell M,
          T (∑ i ∈ Icc 1 ell, ((acc m i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ)))
            * qChoose qL (acc r ell + s) (acc m ell)
            * ∏ i ∈ Icc 1 (ell - 1), qChoose qL (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i)) := by
  -- SANITY CHECK PASSED (Theorem 3.4 master transformation, fixed-M refinement, BOTH signs:
  -- both plus and minus `(a,z)`-sums collapse to the SAME `m`-fermionic form — this is exactly
  -- eq:left-supernomial (stmt3_inversion/Fact9) fed into the Schilling RC expansion (Fact1),
  -- which for a=3 makes E⁺ and E⁻ produce identical m-sums; checked shapes match Fact1 RHS).
  -- ARGUMENT: apply `stmt3_inversion` (= hInvComp.1 / .2.2.2) to rewrite each `(a,z)`-sum
  -- as `q^{sM}·S̃_{(M,|μ|−M),μ}(q⁻¹)` with `μ'=(r₁+s,…,r_ℓ+s)`; then expand `S̃` by Fact1
  -- (`hRC`, the RC/rigged-configuration formula) into the `∑_m q^{Φ(m)}∏[…]` form; finally
  -- normalize the `q⁻¹`→`q` powers (the `q^{sM}` prefactor cancels the reciprocity shift) to
  -- reach `q^{Σ(mᵢ²−rᵢmᵢ)}·[r_ℓ+s;m_ℓ]·∏[…]`. Both signs share the SAME target (both use the
  -- same Fact9 RHS), so `⟨proof, proof⟩` with the plus/minus accessor of Fact9 respectively.
  -- HINT for next phase: `refine ⟨?_, ?_⟩`; each side `rw [stmt3_inversion …]` then `rw [hRC …]`
  -- (Fact1 with c = r+s, M) and reconcile the reciprocity via `hRecip`/`Fact5` q^{-j(N-j)}
  -- shift; the residual is a monomial-exponent `ring`/`omega` match inside `T (·)`.
  -- KEY: both LHS reduce (Fact9 .2.2.1/.2.2.2) to the SAME `T(s*M)*Stil(T(-1)) [M, ∑c-M] (ofFn c)`
  -- with `c = fun i => r i + s`. Prove that common shape equals the RHS once (`key`).
  set c : Fin ell → ℕ := fun i => r i + s with hc_def
  have hcanti : Antitone c := by
    intro i j hij; exact Nat.add_le_add_right (hr hij) s
  have key :
      T (↑s * ↑M : ℤ)
          * Stil (T (-1)) [(M : ℤ), (∑ i, ((r i + s : ℕ) : ℤ)) - (M : ℤ)]
              (List.ofFn fun i => r i + s)
        = ∑ m ∈ Finset.Nat.antidiagonalTuple ell M,
            T (∑ i ∈ Icc 1 ell, ((acc m i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ)))
              * qChoose qL (acc r ell + s) (acc m ell)
              * ∏ i ∈ Icc 1 (ell - 1),
                  qChoose qL (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i) := by
    -- Step 0: rewrite `ofFn (fun i => r i + s)` as `ofFn c` and align the sum inside the list.
    have hcast : (∑ i, ((r i + s : ℕ) : ℤ)) = ((∑ i, c i : ℕ) : ℤ) := by
      rw [hc_def]; push_cast; rfl
    have hofFn : (List.ofFn fun i => r i + s) = (List.ofFn fun i => c i) := by
      rw [hc_def]
    rw [hcast, hofFn]
    -- Step 1: flip `[M, ∑c - M]` → `[∑c - M, M]` via Fact3.2.
    rw [hSym.2 (T (-1)) (M : ℤ) (((∑ i, c i : ℕ) : ℤ) - (M : ℤ)) (List.ofFn fun i => c i)]
    -- Step 2: expand `Stil (T(-1)) [∑c - M, M] (ofFn c)` via `fact1_qinv`.
    rw [fact1_qinv Stil Tset invStat hRC hInv ell c hcanti M]
    -- Step 3: push the `T (s*M)` prefactor into the sum, then work termwise.
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    -- content constraint: ∑_{Fin ell} m i = M, hence ∑_{Icc 1 ell} acc m i = M.
    have hmM : ∑ i ∈ Icc 1 ell, acc m i = M := by
      rw [sum_acc_eq_univ]
      exact Finset.Nat.mem_antidiagonalTuple.mp hm
    -- Step 3a: rewrite every `invert (qChoose qL N j)` via unconditional reciprocity.
    simp only [invert_qChoose' hRecip]
    -- Helper: `acc c i = acc r i + s` for `1 ≤ i ≤ ell`.
    have acc_c_in : ∀ i, 1 ≤ i → i ≤ ell → acc c i = acc r i + s := by
      intro i h1 h2
      simp only [acc, hc_def, dif_pos (show 1 ≤ i ∧ i ≤ ell from ⟨h1, h2⟩)]
    -- qChoose argument identities in `Icc 1 (ell-1)` and at `ell`.
    have hqI : ∀ i ∈ Icc 1 (ell - 1),
        acc c i - acc c (i + 1) + acc m (i + 1)
          = acc r i - acc r (i + 1) + acc m (i + 1) := by
      intro i hi
      simp only [Finset.mem_Icc] at hi
      rw [acc_c_in i (by omega) (by omega), acc_c_in (i + 1) (by omega) (by omega)]
      omega
    have hqE : acc c ell = acc r ell + s := acc_c_in ell hell (le_refl ell)
    -- Abbreviations for the two `Icc 1 (ell-1)` products' factor functions.
    -- Rewrite `acc c` → `acc r`(+s) everywhere on the LHS via a single equality of the products.
    -- Product 1 (pure T-monomials): `acc c (i+1) = acc r (i+1) + s`.
    have hP1 :
        (∏ i ∈ Icc 1 (ell - 1),
            (T (-((↑(acc c (i + 1)) - ↑(acc m (i + 1))) * ↑(acc m i))) : LaurentPolynomial ℤ))
          = ∏ i ∈ Icc 1 (ell - 1),
              (T (-((((acc r (i + 1) + s : ℕ) : ℤ) - (acc m (i + 1) : ℤ)) * (acc m i : ℤ))) : LaurentPolynomial ℤ) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [Finset.mem_Icc] at hi
      rw [acc_c_in (i + 1) (by omega) (by omega)]
    -- Product 2 (T-monomial × qChoose): rewrite both the T-exponent's inner `acc c`s and the
    -- qChoose args to the `acc r` form.
    have hP2 :
        (∏ x ∈ Icc 1 (ell - 1),
            T (-((acc m x : ℤ) *
                ((acc c x - acc c (x + 1) + acc m (x + 1) : ℕ) - (acc m x : ℤ)))) *
              qChoose qL (acc c x - acc c (x + 1) + acc m (x + 1)) (acc m x))
          = ∏ x ∈ Icc 1 (ell - 1),
              T (-((acc m x : ℤ) *
                  ((acc r x - acc r (x + 1) + acc m (x + 1) : ℕ) - (acc m x : ℤ)))) *
                qChoose qL (acc r x - acc r (x + 1) + acc m (x + 1)) (acc m x) := by
      apply Finset.prod_congr rfl
      intro x hx
      rw [hqI x hx]
    rw [hP1, hP2, hqE]
    -- Now every `acc c` is gone; separate T-monomials from qChoose factors.
    -- Collect the two `Icc 1 (ell-1)` products' T- and qChoose-parts.
    rw [Finset.prod_mul_distrib]
    -- Collapse the two T-monomial products into single `T`s of summed exponents.
    rw [prod_T (Icc 1 (ell - 1)) (fun i => -((((acc r (i + 1) + s : ℕ) : ℤ)
          - (acc m (i + 1) : ℤ)) * (acc m i : ℤ)))]
    rw [prod_T (Icc 1 (ell - 1)) (fun x => -((acc m x : ℤ) *
          (((acc r x - acc r (x + 1) + acc m (x + 1) : ℕ) : ℤ) - (acc m x : ℤ))))]
    -- Fold all four `T`-monomials (prefactor, both product-sums, terminal) into a single `T`.
    rw [show
        LaurentPolynomial.T (↑s * ↑M : ℤ) *
          (LaurentPolynomial.T (∑ i ∈ Icc 1 (ell - 1), -((((acc r (i + 1) + s : ℕ) : ℤ)
              - (acc m (i + 1) : ℤ)) * (acc m i : ℤ))) *
            (LaurentPolynomial.T (∑ x ∈ Icc 1 (ell - 1), -((acc m x : ℤ) *
                (((acc r x - acc r (x + 1) + acc m (x + 1) : ℕ) : ℤ) - (acc m x : ℤ)))) *
              ∏ x ∈ Icc 1 (ell - 1),
                qChoose qL (acc r x - acc r (x + 1) + acc m (x + 1)) (acc m x)) *
            (LaurentPolynomial.T (-((acc m ell : ℤ) * ((↑(acc r ell + s) : ℤ) - (acc m ell : ℤ)))) *
              qChoose qL (acc r ell + s) (acc m ell)))
          =
        LaurentPolynomial.T ((↑s * ↑M : ℤ)
            + (∑ i ∈ Icc 1 (ell - 1), -((((acc r (i + 1) + s : ℕ) : ℤ)
                - (acc m (i + 1) : ℤ)) * (acc m i : ℤ)))
            + (∑ x ∈ Icc 1 (ell - 1), -((acc m x : ℤ) *
                (((acc r x - acc r (x + 1) + acc m (x + 1) : ℕ) : ℤ) - (acc m x : ℤ))))
            + (-((acc m ell : ℤ) * ((↑(acc r ell + s) : ℤ) - (acc m ell : ℤ)))))
          * (qChoose qL (acc r ell + s) (acc m ell)
            * ∏ x ∈ Icc 1 (ell - 1),
                qChoose qL (acc r x - acc r (x + 1) + acc m (x + 1)) (acc m x))
        from by rw [LaurentPolynomial.T_add, LaurentPolynomial.T_add,
          LaurentPolynomial.T_add]; ring]
    -- Reassociate the LHS so both sides parenthesize as `(T * qC_ell) * ∏qC₂`.
    rw [← mul_assoc]
    -- Match: `(T-monomial * terminal qChoose)` and the residual product.
    congr 1
    · -- `T(bigexp) * qC_ell = T(exp) * qC_ell`; strip the common `qC_ell`.
      congr 1
      -- exponent equality via `master_exponent_fold`
      have hfold := master_exponent_fold (ell := ell) s M c m hmM
      -- rewrite `acc r` in the RHS exponent to `acc c - s`.
      rw [show (∑ i ∈ Icc 1 ell, ((acc m i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ)))
          = (∑ i ∈ Icc 1 ell, ((acc m i : ℤ) ^ 2 - ((acc c i : ℤ) - (s : ℤ)) * (acc m i : ℤ)))
          from by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_Icc] at hi
        have : (acc c i : ℤ) = (acc r i : ℤ) + (s : ℤ) := by
          rw [acc_c_in i hi.1 hi.2]; push_cast; ring
        rw [this]; ring]
      -- `T(bigexp) = T(hfold-RHS)`; strip the `T` to get an exponent equality.
      congr 1
      rw [← hfold]
      -- rewrite `acc r (+s)` on the LHS exponent to `acc c` via standalone `sum_congr` haves.
      have hce : (acc c ell : ℤ) = (acc r ell : ℤ) + (s : ℤ) := by
        rw [acc_c_in ell hell (le_refl ell)]; push_cast; ring
      have hci : ∀ i ∈ Icc 1 (ell - 1),
          ((acc r (i + 1) + s : ℕ) : ℤ) = (acc c (i + 1) : ℤ) := by
        intro i hi
        simp only [Finset.mem_Icc] at hi
        rw [acc_c_in (i + 1) (by omega) (by omega)]
      -- Antitonicity of `acc c` on `Icc 1 (ell-1)` (needed to push casts through nat subtraction).
      have hcle : ∀ x ∈ Icc 1 (ell - 1), acc c (x + 1) ≤ acc c x := by
        intro x hx
        simp only [Finset.mem_Icc] at hx
        simp only [acc, hc_def,
          dif_pos (show 1 ≤ x + 1 ∧ x + 1 ≤ ell from ⟨by omega, by omega⟩),
          dif_pos (show 1 ≤ x ∧ x ≤ ell from ⟨by omega, by omega⟩)]
        exact hcanti (show (⟨x - 1, by omega⟩ : Fin ell) ≤ ⟨x + 1 - 1, by omega⟩ from by
          simp only [Fin.mk_le_mk]; omega)
      have e1 : (∑ i ∈ Icc 1 (ell - 1),
            -((((acc r (i + 1) + s : ℕ) : ℤ) - (acc m (i + 1) : ℤ)) * (acc m i : ℤ)))
          = (∑ i ∈ Icc 1 (ell - 1),
            -(((acc c (i + 1) : ℤ) - (acc m (i + 1) : ℤ)) * (acc m i : ℤ))) :=
        Finset.sum_congr rfl (fun i hi => by rw [hci i hi])
      -- `e2` targets the INTEGER-subtraction form (matching `hfold`), via `hqI` + `Nat.cast_sub`.
      have e2 : (∑ x ∈ Icc 1 (ell - 1), -((acc m x : ℤ) *
            (((acc r x - acc r (x + 1) + acc m (x + 1) : ℕ) : ℤ) - (acc m x : ℤ))))
          = (∑ x ∈ Icc 1 (ell - 1), -((acc m x : ℤ) *
            (((acc c x : ℤ) - (acc c (x + 1) : ℤ) + (acc m (x + 1) : ℤ)) - (acc m x : ℤ)))) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [← hqI x hx, Nat.cast_add, Nat.cast_sub (hcle x hx)]
      rw [e1, e2, show ((acc r ell + s : ℕ) : ℤ) = (acc c ell : ℤ) from by
        rw [hce]; push_cast; ring]
      simp only [Finset.sum_neg_distrib]
      ring
  refine ⟨?_, ?_⟩
  · rw [hInvComp.1 ell hell r hr s M]; exact key
  · rw [hInvComp.2 ell hell r hr s M]; exact key

/-- **Statement 5(plus) — Theorem 3.1, fixed-boundary identity (eq:sum-plus), `b=3k+1`.**
The reindexed (Lemma 3.3) fixed-boundary sum — `q^{Σᵢrᵢ²}` times the `ℓ=k`, `s=rₖ` master
`(a,z)`-sum with `E⁺` — equals the plus fermionic `m`-form. Stated in the same reindexed
style as the minus case for symmetry. Uses Facts 1–2, 6, 9. -/
theorem stmt5_fixedBoundary_plus_aux (k : ℕ) (hk : 1 ≤ k) (r : Fin k → ℕ) (hr : Antitone r) (M : ℕ)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) (hSym : Fact3 Stil) (hRecip : Fact5)
    (hQbin : Fact6) (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    T (∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2)
        * (∑ az ∈ azFinset r (acc r k) M, T (Eplus r az.1 az.2) * Brs r (acc r k) az.1 az.2)
      = ∑ m ∈ Finset.Nat.antidiagonalTuple k M,
          T (∑ i ∈ Icc 1 k, ((acc r i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ) + (acc m i : ℤ) ^ 2))
            * qChoose qL (2 * acc r k) (acc m k)
            * ∏ i ∈ Icc 1 (k - 1), qChoose qL (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i) := by
  -- SANITY CHECK PASSED (Theorem 3.1 fixed-boundary, plus: q^{Σrᵢ²}·(E⁺ az-sum with ℓ=k, s=rₖ)
  -- = plus m-form; this is `stmt4_master` (plus half) multiplied through by the `q^{Σrᵢ²}`
  -- prefactor and with `s=acc r k`, `ell=k`. Exponent Σ(rᵢ²−rᵢmᵢ+mᵢ²) = Σrᵢ² + Σ(mᵢ²−rᵢmᵢ) ✓).
  -- ARGUMENT: take the plus conjunct of `stmt4_master k … (acc r k) M r hr …`; multiply both
  -- sides by `T (∑ rᵢ²)`; the RHS exponent regroups to the stated form. The `[r_ell+s;m_ell]`
  -- with `s=rₖ`, `ell=k` becomes `[2rₖ;mₖ]`. Fact6 (`hQbin`) is only needed for the qChoose
  -- factorial normalization if `stmt4_master`'s form differs; otherwise pure `T`-monomial ring.
  -- HINT for next phase: `have h := (stmt4_master … k (le_of… ) (acc r k) M r hr hRC hInv hInvComp).1`
  -- then `rw`/`mul_left` by `T (∑rᵢ²)`, `simp [T_add? , ← T_mul?]` to fold the prefactor into
  -- the exponent, and `ring_nf` the exponent sum; `s=acc r k ⇒ acc r ell + s = 2·acc r k`.
  have h := (stmt4_master_aux Stil Tset invStat tabOf Ja Jz k hk (acc r k) M r hr
    hRC hInv hSym hRecip hInvComp).1
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  -- Fold the `T (∑ rᵢ²)` prefactor into the m-term's `T` exponent.
  rw [show (2 * acc r k) = (acc r k + acc r k) from by ring]
  rw [show T (∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2)
        * (T (∑ i ∈ Icc 1 k, ((acc m i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ)))
            * qChoose qL (acc r k + acc r k) (acc m k)
            * ∏ i ∈ Icc 1 (k - 1), qChoose qL (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i))
      = T (∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2
            + ∑ i ∈ Icc 1 k, ((acc m i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ)))
          * qChoose qL (acc r k + acc r k) (acc m k)
          * ∏ i ∈ Icc 1 (k - 1), qChoose qL (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i)
      from by rw [LaurentPolynomial.T_add]; ring]
  -- The exponents agree: ∑rᵢ² + ∑(mᵢ²-rᵢmᵢ) = ∑(rᵢ²-rᵢmᵢ+mᵢ²).
  have hexp : (∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2)
        + ∑ i ∈ Icc 1 k, ((acc m i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ))
      = ∑ i ∈ Icc 1 k, ((acc r i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ) + (acc m i : ℤ) ^ 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hexp]

/-- **Statement 5(minus) — Theorem 3.1, fixed-boundary identity (eq:sum-minus), `b=3k-1`.**
The reindexed (Lemma 3.3) fixed-boundary sum — `q^{rₖ²+Σ_{i<k}rᵢ²}` times the `ℓ=k-1`, `s=rₖ`
master `(a,z)`-sum with `E⁻` — equals the minus fermionic `m`-form. Terminal `rₖ²` retained
(Remark 3.2). Uses Facts 1–2, 6, 9. -/
theorem stmt5_fixedBoundary_minus_aux (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ℕ) (hr : Antitone r) (M : ℕ)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) (hSym : Fact3 Stil) (hRecip : Fact5)
    (hQbin : Fact6) (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    T ((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
        * (∑ az ∈ azFinset (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) M,
            T (Eminus (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) az.1 az.2)
              * Brs (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) az.1 az.2)
      = ∑ m ∈ Finset.Nat.antidiagonalTuple (k - 1) M,
          T ((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1),
                ((acc r i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ) + (acc m i : ℤ) ^ 2))
            * qChoose qL (acc r (k - 1) + acc r k) (acc m (k - 1))
            * ∏ i ∈ Icc 1 (k - 2), qChoose qL (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i) := by
  -- SANITY CHECK PASSED (Theorem 3.1 fixed-boundary, minus: q^{rₖ²+Σ_{i<k}rᵢ²}·(E⁻ az-sum with
  -- ℓ=k-1, s=rₖ) = minus m-form; terminal `rₖ²` kept inside the prefactor AND the RHS exponent,
  -- Remark 3.2. Structurally `stmt4_master` (minus half) at `ell=k-1`, `s=acc r k`, times the
  -- `q^{rₖ²+Σ_{i<k}rᵢ²}` prefactor; note the trimmed r-tuple `fun i => r (castLE i)`).
  -- ARGUMENT: take the minus conjunct of `stmt4_master (k-1) … (acc r k) M r' hr' …` with the
  -- length-(k-1) trimmed tuple `r' = fun i => r (Fin.castLE _ i)`; multiply by the prefactor;
  -- regroup exponents (KEEP the standalone `rₖ²`). `[r_{ell}+s;m_{ell}]` with ell=k-1, s=rₖ
  -- becomes `[r_{k-1}+rₖ;m_{k-1}]`; the inner product runs `Icc 1 (k-2)`.
  -- HINT for next phase: mirror the plus case with `ell=k-1`; watch the `acc` on the trimmed
  -- tuple vs the full `r` (they agree for i≤k-1 by `Fin.castLE` + `acc` def).
  set r' : Fin (k - 1) → ℕ := fun i : Fin (k - 1) => r (Fin.castLE (by omega) i) with hr'_def
  -- trimmed tuple is antitone
  have hr' : Antitone r' := fun i j hij => hr hij
  -- `acc r' i = acc r i` for `1 ≤ i ≤ k-1`.
  have acc_r' : ∀ i, 1 ≤ i → i ≤ k - 1 → acc r' i = acc r i := by
    intro i h1 h2
    simp only [acc, hr'_def,
      dif_pos (show 1 ≤ i ∧ i ≤ k - 1 from ⟨h1, h2⟩),
      dif_pos (show 1 ≤ i ∧ i ≤ k from ⟨h1, by omega⟩)]
    congr 1
  have hell : 1 ≤ k - 1 := by omega
  have h := (stmt4_master_aux Stil Tset invStat tabOf Ja Jz (k - 1) hell (acc r k) M r' hr'
    hRC hInv hSym hRecip hInvComp).2
  -- rewrite the LHS via `h`, then push the prefactor into the sum.
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  -- Normalize `k - 1 - 1` to `k - 2` so the `∏ Icc 1 (k-1-1)` in the goal matches `hprod`.
  rw [show k - 1 - 1 = k - 2 from by omega]
  -- Replace `acc r'` by `acc r` in the RHS of `h` (all indices ≤ k-1).
  have hlast : acc r' (k - 1) = acc r (k - 1) := acc_r' (k - 1) hell (le_refl _)
  rw [hlast]
  -- The `∏ Icc 1 (k-2)` qChoose args: `acc r' i - acc r' (i+1)` = `acc r i - acc r (i+1)` for i ≤ k-2.
  have hprod : (∏ i ∈ Icc 1 (k - 2),
        qChoose qL (acc r' i - acc r' (i + 1) + acc m (i + 1)) (acc m i))
      = ∏ i ∈ Icc 1 (k - 2),
        qChoose qL (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Finset.mem_Icc] at hi
    rw [acc_r' i (by omega) (by omega), acc_r' (i + 1) (by omega) (by omega)]
  rw [hprod]
  -- The exponent inside T: replace acc r' by acc r on Icc 1 (k-1).
  have hexpInner : (∑ i ∈ Icc 1 (k - 1),
        ((acc m i : ℤ) ^ 2 - (acc r' i : ℤ) * (acc m i : ℤ)))
      = ∑ i ∈ Icc 1 (k - 1),
        ((acc m i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_Icc] at hi
    rw [acc_r' i hi.1 hi.2]
  rw [hexpInner]
  -- Fold the `T (rₖ² + ∑_{i<k} rᵢ²)` prefactor into the m-term's exponent.
  -- Group `T(pref) * (T(∑m) * qC * ∏)` as `(T(pref) * T(∑m)) * qC * ∏`, merge the two T's.
  rw [show T ((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
        * (T (∑ i ∈ Icc 1 (k - 1), ((acc m i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ)))
            * qChoose qL (acc r (k - 1) + acc r k) (acc m (k - 1))
            * ∏ i ∈ Icc 1 (k - 2), qChoose qL (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i))
      = (T ((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
            * T (∑ i ∈ Icc 1 (k - 1), ((acc m i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ))))
          * qChoose qL (acc r (k - 1) + acc r k) (acc m (k - 1))
          * ∏ i ∈ Icc 1 (k - 2), qChoose qL (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i)
      from by ring]
  rw [← LaurentPolynomial.T_add]
  -- Exponent equality: rₖ² + ∑rᵢ² + ∑(mᵢ²-rᵢmᵢ) = rₖ² + ∑(rᵢ²-rᵢmᵢ+mᵢ²).
  have hexp : ((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
        + ∑ i ∈ Icc 1 (k - 1), ((acc m i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ))
      = (acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1),
          ((acc r i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ) + (acc m i : ℤ) ^ 2) := by
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hexp]

/-- Infrastructure for Statement 7: over a **finite** base `ι` and an arbitrary fiber `ℕ`, an
infinite product over `ι × ℕ` equals the (finite) product of the per-column infinite products,
provided each column converges. Proof: reduce to one column via `Function.Injective.hasProd_iff`,
then fold over `Finset.univ` by induction using `HasProd.mul`. -/
theorem hasProd_fin_base {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι × ℕ → ℤ⟦X⟧) (g : ι → ℤ⟦X⟧)
    (hfib : ∀ c : ι, HasProd (fun i => h (c, i)) (g c)) :
    HasProd h (∏ c, g c) := by
  classical
  have hcol : ∀ a : ι, HasProd (fun p : ι × ℕ => if p.1 = a then h p else 1) (g a) := by
    intro a
    have hg : Function.Injective (fun i : ℕ => (a, i)) := by
      intro x y hxy; simpa using hxy
    have hout : ∀ x ∉ Set.range (fun i : ℕ => (a, i)),
        (fun p : ι × ℕ => if p.1 = a then h p else 1) x = 1 := by
      intro x hx
      simp only
      rw [if_neg]
      intro hcontra
      apply hx
      exact ⟨x.2, by rw [← hcontra]⟩
    rw [← hg.hasProd_iff hout]
    have : ((fun p : ι × ℕ => if p.1 = a then h p else 1) ∘ (fun i : ℕ => (a, i)))
          = (fun i => h (a, i)) := by
      funext i; simp
    rw [this]
    exact hfib a
  have key : ∀ s : Finset ι,
      HasProd (fun p : ι × ℕ => if p.1 ∈ s then h p else 1) (∏ c ∈ s, g c) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        simp only [Finset.notMem_empty, if_false, Finset.prod_empty]
        exact hasProd_one
    | insert a s ha ih =>
        rw [Finset.prod_insert ha]
        have hmul := (hcol a).mul ih
        convert hmul using 1
        funext p
        by_cases hp : p.1 = a
        · subst hp; simp [ha]
        · by_cases hps : p.1 ∈ s
          · simp [hp, hps, Finset.mem_insert]
          · simp [hp, hps, Finset.mem_insert]
  have hfull := key Finset.univ
  simpa using hfull

/-- Infrastructure for Statement 7 (residue regrouping): an infinite product over `ℕ`
regroups as a finite product over residue classes mod `L` of the per-residue infinite
products `∏'_i f(i·L + c)`. Uses `Nat.divModEquiv` and `hasProd_fin_base`. -/
theorem residue_regroup (L : ℕ) (hL : 0 < L) (f : ℕ → ℤ⟦X⟧)
    (g : Fin L → ℤ⟦X⟧)
    (hfib : ∀ c : Fin L, HasProd (fun i => f (i * L + (c : ℕ))) (g c)) :
    HasProd f (∏ c : Fin L, g c) := by
  haveI : NeZero L := ⟨hL.ne'⟩
  set E : ℕ ≃ Fin L × ℕ := (Nat.divModEquiv L).trans (Equiv.prodComm ℕ (Fin L)) with hE
  rw [← Equiv.hasProd_iff E.symm]
  apply hasProd_fin_base
  intro c
  have hEsymm : ∀ (c : Fin L) (i : ℕ), E.symm (c, i) = i * L + (c : ℕ) := by
    intro c i
    simp [hE, Nat.divModEquiv, Nat.add_comm, Nat.mul_comm]
  simp only [Function.comp, hEsymm]
  exact hfib c


/-! ### stmt7 residue identity — clean decomposition (no mixed-sign product uniqueness).

The reformulation that makes stmt7 tractable: `charge` is a product of *inverses*
`(1-Xⁿ).invOfUnit 1 ^ negR n = invOfUnit((1-Xⁿ)^{negR n}) 1`, hence
`charge 3 (3k-1) = invOfUnit P 1` where `P := ∏'ₙ (1-Xⁿ)^{negR n}` is a genuine
*non-negative-exponent* infinite product (a unit, constant term 1).
`warnaarRHSminus k = num · invOfUnit den 1`, with `den := (X;X)_∞²` and
`num := (X^L;X^L)_∞² · θ_k · θ_{k+1} · θ_{k+1}` (`L=3k+2`), also genuine products.
The identity `warnaarRHSminus = charge` cross-multiplies to `num · P = den = (X;X)_∞²`,
which holds because **every residue class mod L contributes total exponent exactly 2**
on both sides (num-exponent + negR = 2 for all classes; verified in `sketch.md`). -/

/-- The genuine (non-negative-exponent) charge product for `b = 3k-1`. -/
noncomputable def Pminus (k : ℕ) : ℤ⟦X⟧ :=
  ∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ HJO.negR 3 (3 * k - 1) n

/-- The genuine (non-negative-exponent) numerator of `warnaarRHSminus`, `L = 3k+2`. -/
noncomputable def numMinus (k : ℕ) : ℤ⟦X⟧ :=
  ((X ^ (3 * k + 2); (X : ℤ⟦X⟧) ^ (3 * k + 2))_∞) ^ 2
    * (bTheta k (3 * k + 2) * bTheta (k + 1) (3 * k + 2) * bTheta (k + 1) (3 * k + 2))

/-- **SL3 (cross-multiply).** If `num · P = den` with `P`, `den` units (constant coeff 1),
then `num · invOfUnit den 1 = invOfUnit P 1`. PROVEN. -/
theorem invOfUnit_cross_mul (num P den : ℤ⟦X⟧)
    (hP : PowerSeries.constantCoeff (R := ℤ) P = 1) (hden : PowerSeries.constantCoeff (R := ℤ) den = 1)
    (hmul : num * P = den) :
    num * PowerSeries.invOfUnit den 1 = PowerSeries.invOfUnit P 1 := by
  have hPunit : P * PowerSeries.invOfUnit P 1 = 1 :=
    PowerSeries.mul_invOfUnit P 1 (by simpa using hP)
  have hdenunit : den * PowerSeries.invOfUnit den 1 = 1 :=
    PowerSeries.mul_invOfUnit den 1 (by simpa using hden)
  have key : (num * PowerSeries.invOfUnit den 1) * P = PowerSeries.invOfUnit P 1 * P := by
    calc (num * PowerSeries.invOfUnit den 1) * P
        = (num * P) * PowerSeries.invOfUnit den 1 := by ring
      _ = den * PowerSeries.invOfUnit den 1 := by rw [hmul]
      _ = 1 := hdenunit
      _ = PowerSeries.invOfUnit P 1 * P := by rw [mul_comm]; exact hPunit.symm
  have hPu : IsUnit P :=
    ⟨⟨P, PowerSeries.invOfUnit P 1, hPunit, by rw [mul_comm]; exact hPunit⟩, rfl⟩
  exact mul_right_cancel₀ hPu.ne_zero key

/-- Constant coefficient of an infinite `q`-Pochhammer `(a;q)_∞` is `1` when `a` has zero
constant coefficient and `q` is topologically nilpotent. -/
theorem constantCoeff_qPochhammerInf (a q : ℤ⟦X⟧) (hq : IsTopologicallyNilpotent q)
    (ha : PowerSeries.constantCoeff (R := ℤ) a = 0) :
    PowerSeries.constantCoeff (R := ℤ) ((a; q)_∞) = 1 := by
  have hcont : Continuous (PowerSeries.constantCoeff (R := ℤ)) := by
    have := PowerSeries.WithPiTopology.continuous_coeff ℤ 0
    rw [PowerSeries.coeff_zero_eq_constantCoeff] at this
    exact this
  have hhp : HasProd (fun x => 1 - a * q ^ x) ((a; q)_∞) := hasProd_qPochhammerInf hq
  have hmap := hhp.map (PowerSeries.constantCoeff (R := ℤ)) hcont
  have hterm : (⇑(PowerSeries.constantCoeff (R := ℤ)) ∘ fun x => 1 - a * q ^ x)
      = fun _ => (1:ℤ) := by
    funext x
    simp [Function.comp, map_sub, map_mul, map_pow, ha]
  rw [hterm] at hmap
  exact ((hasProd_one).unique hmap).symm

/-- Order of `1 - (1-Xᵐ)^e` is at least `m`, since `Xᵐ ∣ 1 - (1-Xᵐ)^e`. -/
lemma m_le_order_one_sub_pow (m e : ℕ) :
    (m : ℕ∞) ≤ (1 - (1 - (X : ℤ⟦X⟧) ^ m) ^ e).order := by
  rw [PowerSeries.le_order_iff]
  have hdvd : (X : ℤ⟦X⟧) ^ m ∣ (1 - (1 - (X : ℤ⟦X⟧) ^ m) ^ e) := by
    have hd : (1 - (1 - (X:ℤ⟦X⟧)^m)) ∣ (1 ^ e - (1 - (X:ℤ⟦X⟧)^m) ^ e) :=
      sub_dvd_pow_sub_pow 1 (1 - (X:ℤ⟦X⟧)^m) e
    simp only [one_pow] at hd
    have heq : (1 : ℤ⟦X⟧) - (1 - (X:ℤ⟦X⟧)^m) = (X:ℤ⟦X⟧)^m := by ring
    rwa [heq] at hd
  exact PowerSeries.X_pow_dvd_iff.mp hdvd

/-- The genuine product family `(fun n => (1-Xⁿ)^(e n))` is multipliable (orders → ⊤). -/
lemma multipliable_prod_one_sub_pow (e : ℕ → ℕ) :
    Multipliable (fun n : ℕ => (1 - (X : ℤ⟦X⟧) ^ n) ^ e n) := by
  have hrewrite : (fun n : ℕ => (1 - (X : ℤ⟦X⟧) ^ n) ^ e n)
      = (fun n : ℕ => 1 - (1 - (1 - (X : ℤ⟦X⟧) ^ n) ^ e n)) := by
    funext n; ring
  rw [hrewrite]
  apply PowerSeries.WithPiTopology.multipliable_one_sub_of_tendsto_order
  have hcast : Filter.Tendsto (fun m : ℕ => (m : ℕ∞)) Filter.atTop (nhds ⊤) := by
    rw [ENat.tendsto_nhds_top_iff_natCast_lt]
    intro n
    filter_upwards [Filter.eventually_gt_atTop n] with m hm
    exact_mod_cast hm
  apply tendsto_nhds_top_mono' hcast
  intro m
  exact m_le_order_one_sub_pow m (e m)

/-- Constant coefficient of a genuine product `∏' n, (1-Xⁿ)^(e n)` is `1`, given `e 0 = 0`. -/
lemma constantCoeff_prod_one_sub_pow (e : ℕ → ℕ) (he0 : e 0 = 0) :
    PowerSeries.constantCoeff (R := ℤ) (∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ e n) = 1 := by
  have hcont : Continuous (PowerSeries.constantCoeff (R := ℤ)) := by
    have := PowerSeries.WithPiTopology.continuous_coeff ℤ 0
    rw [PowerSeries.coeff_zero_eq_constantCoeff] at this
    exact this
  have hhp : HasProd (fun n : ℕ => (1 - (X : ℤ⟦X⟧) ^ n) ^ e n)
      (∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ e n) := (multipliable_prod_one_sub_pow e).hasProd
  have hmap := hhp.map (PowerSeries.constantCoeff (R := ℤ)) hcont
  have hterm : (⇑(PowerSeries.constantCoeff (R := ℤ)) ∘ fun n : ℕ => (1 - (X : ℤ⟦X⟧) ^ n) ^ e n)
      = fun _ => (1:ℤ) := by
    funext n
    simp only [Function.comp, map_pow, map_sub, map_one, PowerSeries.constantCoeff_X]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; rw [he0]; simp
    · rw [zero_pow (by omega)]; simp
  rw [hterm] at hmap
  exact ((hasProd_one).unique hmap).symm

/-- `negR 3 b 0 = 0` (the residue exponent vanishes at `n = 0`). -/
lemma negR_zero (a b : ℕ) : HJO.negR a b 0 = 0 := by
  simp [HJO.negR]

/-- Order of `1 - ((1-Xᵐ).invOfUnit 1)^e` is at least `m`: for `m ≥ 1`, `Xᵐ ∣ invOfUnit(1-Xᵐ) - 1`
(since `(1-Xᵐ)·invOfUnit = 1`), and `invOfUnit - 1 ∣ invOfUnitᵉ - 1`. -/
lemma m_le_order_invOfUnit_one_sub_pow (m e : ℕ) :
    (m : ℕ∞) ≤ (1 - (PowerSeries.invOfUnit (1 - (X : ℤ⟦X⟧) ^ m) 1) ^ e).order := by
  rw [PowerSeries.le_order_iff]
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; intro i hi; omega
  · have hinv : (1 - (X:ℤ⟦X⟧)^m) * PowerSeries.invOfUnit (1 - (X:ℤ⟦X⟧)^m) 1 = 1 := by
      apply PowerSeries.mul_invOfUnit
      simp only [map_sub, map_one, map_pow, PowerSeries.constantCoeff_X]
      rw [zero_pow (by omega)]; simp
    have hdvd0 : (X:ℤ⟦X⟧)^m ∣ (PowerSeries.invOfUnit (1 - (X:ℤ⟦X⟧)^m) 1 - 1) := by
      refine ⟨PowerSeries.invOfUnit (1 - (X:ℤ⟦X⟧)^m) 1, ?_⟩
      calc PowerSeries.invOfUnit (1 - (X:ℤ⟦X⟧)^m) 1 - 1
          = PowerSeries.invOfUnit (1 - (X:ℤ⟦X⟧)^m) 1
              - (1 - (X:ℤ⟦X⟧)^m) * PowerSeries.invOfUnit (1 - (X:ℤ⟦X⟧)^m) 1 := by rw [hinv]
        _ = (X:ℤ⟦X⟧)^m * PowerSeries.invOfUnit (1 - (X:ℤ⟦X⟧)^m) 1 := by ring
    have hdvd : (X:ℤ⟦X⟧)^m ∣ (1 - (PowerSeries.invOfUnit (1 - (X:ℤ⟦X⟧)^m) 1) ^ e) := by
      have hd : (PowerSeries.invOfUnit (1 - (X:ℤ⟦X⟧)^m) 1 - 1) ∣
          ((PowerSeries.invOfUnit (1 - (X:ℤ⟦X⟧)^m) 1)^e - 1^e) :=
        sub_dvd_pow_sub_pow (PowerSeries.invOfUnit (1 - (X:ℤ⟦X⟧)^m) 1) 1 e
      simp only [one_pow] at hd
      have hd2 : (X:ℤ⟦X⟧)^m ∣ ((PowerSeries.invOfUnit (1 - (X:ℤ⟦X⟧)^m) 1)^e - 1) :=
        dvd_trans hdvd0 hd
      have heq : (1 : ℤ⟦X⟧) - (PowerSeries.invOfUnit (1 - (X:ℤ⟦X⟧)^m) 1)^e
          = -((PowerSeries.invOfUnit (1 - (X:ℤ⟦X⟧)^m) 1)^e - 1) := by ring
      rw [heq]; exact (dvd_neg).mpr hd2
    exact PowerSeries.X_pow_dvd_iff.mp hdvd

/-- The inverse product family `(fun n => ((1-Xⁿ).invOfUnit 1)^(e n))` is multipliable. -/
lemma multipliable_prod_invOfUnit_one_sub_pow (e : ℕ → ℕ) :
    Multipliable (fun n : ℕ => (PowerSeries.invOfUnit (1 - (X : ℤ⟦X⟧) ^ n) 1) ^ e n) := by
  have hrewrite : (fun n : ℕ => (PowerSeries.invOfUnit (1 - (X : ℤ⟦X⟧) ^ n) 1) ^ e n)
      = (fun n : ℕ => 1 - (1 - (PowerSeries.invOfUnit (1 - (X : ℤ⟦X⟧) ^ n) 1) ^ e n)) := by
    funext n; ring
  rw [hrewrite]
  apply PowerSeries.WithPiTopology.multipliable_one_sub_of_tendsto_order
  have hcast : Filter.Tendsto (fun m : ℕ => (m : ℕ∞)) Filter.atTop (nhds ⊤) := by
    rw [ENat.tendsto_nhds_top_iff_natCast_lt]
    intro n
    filter_upwards [Filter.eventually_gt_atTop n] with m hm
    exact_mod_cast hm
  apply tendsto_nhds_top_mono' hcast
  intro m
  exact m_le_order_invOfUnit_one_sub_pow m (e m)

/-- The `∏'` of the inverse family is the `invOfUnit` of the genuine product (given `e 0 = 0`):
their product is `∏' 1 = 1` and the genuine product is a unit. -/
lemma prod_invOfUnit_eq_invOfUnit_prod (e : ℕ → ℕ) (he0 : e 0 = 0) :
    (∏' n : ℕ, (PowerSeries.invOfUnit (1 - (X : ℤ⟦X⟧) ^ n) 1) ^ e n)
      = PowerSeries.invOfUnit (∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ e n) 1 := by
  set C := ∏' n : ℕ, (PowerSeries.invOfUnit (1 - (X : ℤ⟦X⟧) ^ n) 1) ^ e n with hC
  set P := ∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ e n with hP
  have hCfam : HasProd (fun n : ℕ => (PowerSeries.invOfUnit (1 - (X : ℤ⟦X⟧) ^ n) 1) ^ e n) C :=
    (multipliable_prod_invOfUnit_one_sub_pow e).hasProd
  have hPfam : HasProd (fun n : ℕ => (1 - (X : ℤ⟦X⟧) ^ n) ^ e n) P :=
    (multipliable_prod_one_sub_pow e).hasProd
  have hmul := hCfam.mul hPfam
  have hone : (fun n : ℕ => (PowerSeries.invOfUnit (1 - (X : ℤ⟦X⟧) ^ n) 1) ^ e n
      * (1 - (X : ℤ⟦X⟧) ^ n) ^ e n) = fun _ => (1 : ℤ⟦X⟧) := by
    funext n
    rw [← mul_pow]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; rw [he0]; simp
    · have hinv : (1 - (X:ℤ⟦X⟧)^n) * PowerSeries.invOfUnit (1 - (X:ℤ⟦X⟧)^n) 1 = 1 := by
        apply PowerSeries.mul_invOfUnit
        simp only [map_sub, map_one, map_pow, PowerSeries.constantCoeff_X]
        rw [zero_pow (by omega)]; simp
      rw [mul_comm (PowerSeries.invOfUnit (1 - (X:ℤ⟦X⟧)^n) 1) (1 - (X:ℤ⟦X⟧)^n), hinv, one_pow]
  rw [hone] at hmul
  have hCP : C * P = 1 := (hasProd_one.unique hmul).symm
  have hPcc : PowerSeries.constantCoeff (R := ℤ) P = 1 := by
    rw [hP]; exact constantCoeff_prod_one_sub_pow e he0
  have hPunit : P * PowerSeries.invOfUnit P 1 = 1 :=
    PowerSeries.mul_invOfUnit P 1 (by simpa using hPcc)
  have hPu : IsUnit P :=
    ⟨⟨P, PowerSeries.invOfUnit P 1, hPunit, by rw [mul_comm]; exact hPunit⟩, rfl⟩
  have key : C * P = PowerSeries.invOfUnit P 1 * P := by
    rw [hCP, mul_comm]; exact hPunit.symm
  exact mul_right_cancel₀ hPu.ne_zero key

/-- **SL1 (charge = invOfUnit of the genuine product).** `charge 3 (3k-1) = invOfUnit (Pminus k) 1`.
Route: `charge` term `(1-Xⁿ).invOfUnit 1 ^ negR n = invOfUnit((1-Xⁿ)^{negR n}) 1`; the
`∏'` of inverses is the inverse of `Pminus k` because their product is `∏' 1 = 1` (via
`HasProd.mul` of the two convergent products), and `Pminus k` has constant coeff 1. -/
theorem charge_minus_eq_invOfUnit (k : ℕ) (hk : 2 ≤ k) :
    HJO.charge 3 (3 * k - 1) = PowerSeries.invOfUnit (Pminus k) 1 := by
  unfold HJO.charge Pminus
  exact prod_invOfUnit_eq_invOfUnit_prod (HJO.negR 3 (3 * k - 1)) (negR_zero 3 (3 * k - 1))

/-- Constant coefficient of `Pminus k` is 1 (each factor `(1-Xⁿ)^e` has constant coeff 1,
and infinite products in `ℤ⟦X⟧` preserve constant coefficients). -/
theorem constantCoeff_Pminus (k : ℕ) (hk : 2 ≤ k) :
    PowerSeries.constantCoeff (R := ℤ) (Pminus k) = 1 := by
  unfold Pminus
  exact constantCoeff_prod_one_sub_pow (HJO.negR 3 (3 * k - 1)) (negR_zero 3 (3 * k - 1))

/-- Residue indicator: `(X^u; X^L)_∞ = ∏' n, (1-X^n)^(indic u L n)` for `1 ≤ u`, `0 < L`. -/
noncomputable def indic (u L n : ℕ) : ℕ := if u ≤ n ∧ (n - u) % L = 0 then 1 else 0

/-- `(X^u; X^L)_∞` written as a genuine `∏' (1-X^n)^{indicator}`. -/
lemma qPochInf_as_indic (u L : ℕ) (hL : 0 < L) (_hu : 1 ≤ u) :
    ((X ^ u; (X : ℤ⟦X⟧) ^ L)_∞) = ∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ indic u L n := by
  have hq : IsTopologicallyNilpotent ((X : ℤ⟦X⟧) ^ L) := by
    rw [show (X:ℤ⟦X⟧)^L = (X:ℤ⟦X⟧)^(L-1)*X by rw [← pow_succ]; congr 1; omega]
    exact HasEval.X.mul_left_of_commute (Commute.all _ _)
  have hbase : HasProd (fun x => 1 - (X:ℤ⟦X⟧)^u * ((X:ℤ⟦X⟧)^L) ^ x) ((X ^ u; (X : ℤ⟦X⟧) ^ L)_∞) :=
    hasProd_qPochhammerInf hq
  have hg : Function.Injective (fun x : ℕ => u + L * x) := by
    intro a b hab; simp only at hab
    have : L * a = L * b := by omega
    exact Nat.eq_of_mul_eq_mul_left hL this
  have hout : ∀ n ∉ Set.range (fun x : ℕ => u + L * x),
      (fun n => (1 - (X:ℤ⟦X⟧)^n) ^ indic u L n) n = 1 := by
    intro n hn
    simp only [indic]
    rw [if_neg]
    · rw [pow_zero]
    · rintro ⟨hun, hmod⟩
      apply hn
      refine ⟨(n - u)/L, ?_⟩
      simp only
      have hdvd : L ∣ (n - u) := Nat.dvd_of_mod_eq_zero hmod
      have : L * ((n - u)/L) = n - u := Nat.mul_div_cancel' hdvd
      omega
  have hcomp : ((fun n => (1 - (X:ℤ⟦X⟧)^n) ^ indic u L n) ∘ (fun x : ℕ => u + L * x))
      = (fun x => 1 - (X:ℤ⟦X⟧)^u * ((X:ℤ⟦X⟧)^L) ^ x) := by
    funext x
    simp only [Function.comp, indic]
    rw [if_pos]
    · rw [pow_one, ← pow_mul, ← pow_add]
    · refine ⟨by omega, ?_⟩
      have : u + L * x - u = L * x := by omega
      rw [this, Nat.mul_mod_right]
  have hfull : HasProd (fun n => (1 - (X:ℤ⟦X⟧)^n) ^ indic u L n) ((X ^ u; (X : ℤ⟦X⟧) ^ L)_∞) := by
    rw [← hg.hasProd_iff hout, hcomp]
    exact hbase
  exact hfull.tprod_eq.symm

/-- Multiplying two genuine products adds exponents pointwise. -/
lemma prod_one_sub_pow_mul (e1 e2 : ℕ → ℕ) :
    (∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ e1 n) * (∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ e2 n)
      = ∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ (e1 n + e2 n) := by
  have h1 : HasProd (fun n : ℕ => (1 - (X : ℤ⟦X⟧) ^ n) ^ e1 n)
      (∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ e1 n) := (multipliable_prod_one_sub_pow e1).hasProd
  have h2 : HasProd (fun n : ℕ => (1 - (X : ℤ⟦X⟧) ^ n) ^ e2 n)
      (∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ e2 n) := (multipliable_prod_one_sub_pow e2).hasProd
  have hmul := h1.mul h2
  have hterm : (fun n : ℕ => (1 - (X : ℤ⟦X⟧) ^ n) ^ e1 n * (1 - (X : ℤ⟦X⟧) ^ n) ^ e2 n)
      = fun n : ℕ => (1 - (X : ℤ⟦X⟧) ^ n) ^ (e1 n + e2 n) := by
    funext n; rw [← pow_add]
  rw [hterm] at hmul
  exact hmul.tprod_eq.symm

/-- Squaring a genuine product doubles exponents pointwise. -/
lemma prod_one_sub_pow_sq (e : ℕ → ℕ) :
    (∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ e n) ^ 2
      = ∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ (2 * e n) := by
  rw [sq, prod_one_sub_pow_mul]
  apply tprod_congr
  intro n; congr 1; omega

/-- The exponent function of `numMinus k` collected over all `(X^a;X^L)_∞` factors, `L=3k+2`. -/
noncomputable def numE (k n : ℕ) : ℕ :=
  2 * indic (3 * k + 2) (3 * k + 2) n
    + indic k (3 * k + 2) n
    + indic (2 * k + 2) (3 * k + 2) n
    + 2 * indic (k + 1) (3 * k + 2) n
    + 2 * indic (2 * k + 1) (3 * k + 2) n

/-- The exponent function of `(X;X)_∞²`: `2` for every `n ≥ 1`, `0` at `n = 0`. -/
noncomputable def Erhs (n : ℕ) : ℕ := 2 * indic 1 1 n

/-- `numMinus k` written as a genuine `∏' (1-X^n)^{numE k n}`. -/
lemma numMinus_as_prod (k : ℕ) (hk : 2 ≤ k) :
    numMinus k = ∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ numE k n := by
  have hLk : 3 * k + 2 - k = 2 * k + 2 := by omega
  have hLk1 : 3 * k + 2 - (k + 1) = 2 * k + 1 := by omega
  unfold numMinus bTheta
  rw [hLk, hLk1]
  rw [qPochInf_as_indic (3 * k + 2) (3 * k + 2) (by omega) (by omega)]
  rw [qPochInf_as_indic k (3 * k + 2) (by omega) (by omega)]
  rw [qPochInf_as_indic (2 * k + 2) (3 * k + 2) (by omega) (by omega)]
  rw [qPochInf_as_indic (k + 1) (3 * k + 2) (by omega) (by omega)]
  rw [qPochInf_as_indic (2 * k + 1) (3 * k + 2) (by omega) (by omega)]
  rw [prod_one_sub_pow_sq]
  rw [prod_one_sub_pow_mul, prod_one_sub_pow_mul, prod_one_sub_pow_mul,
      prod_one_sub_pow_mul, prod_one_sub_pow_mul]
  apply tprod_congr
  intro n
  congr 1
  simp only [numE]
  omega

/-- `(X;X)_∞²` written as a genuine `∏' (1-X^n)^{Erhs n}`. -/
lemma qPoch_self_sq_as_prod :
    ((X; (X : ℤ⟦X⟧))_∞) ^ 2 = ∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ Erhs n := by
  have h1 : ((X; (X : ℤ⟦X⟧))_∞) = ((X ^ 1; (X : ℤ⟦X⟧) ^ 1)_∞) := by simp
  rw [h1, qPochInf_as_indic 1 1 (by norm_num) (by norm_num)]
  rw [prod_one_sub_pow_sq]
  apply tprod_congr
  intro n; rfl

/-- `indic` rewritten via integer divisibility (for `0 < u ≤ L`, `1 ≤ n`). -/
theorem indic_eq_int_dvd (u L n : ℕ) (_hu : 0 < u) (huL : u ≤ L) (hn : 1 ≤ n) :
    indic u L n = if (L : ℤ) ∣ ((n : ℤ) - u) then 1 else 0 := by
  unfold indic
  by_cases hc : (L : ℤ) ∣ ((n : ℤ) - u)
  · rw [if_pos hc, if_pos]
    obtain ⟨t, ht⟩ := hc
    have hun : u ≤ n := by
      rcases lt_or_ge t 0 with ht0 | ht0
      · exfalso; nlinarith [ht, ht0, huL, hn]
      · nlinarith [ht, ht0, huL]
    refine ⟨hun, ?_⟩
    have hdvdN : (L : ℤ) ∣ ((n - u : ℕ) : ℤ) := by
      rw [Nat.cast_sub hun]; exact ⟨t, ht⟩
    have hnat : L ∣ (n - u) := by exact_mod_cast hdvdN
    exact Nat.mod_eq_zero_of_dvd hnat
  · rw [if_neg hc, if_neg]
    rintro ⟨h1, h2⟩
    apply hc
    have : (L : ℤ) ∣ ((n - u : ℕ) : ℤ) := by exact_mod_cast Nat.dvd_of_mod_eq_zero h2
    rw [Nat.cast_sub h1] at this
    exact this

/-- Divisibility of `n - u` by `L` is equivalent to `3n` and `3u` having equal balanced
residues, given `3` coprime to `L`. -/
theorem dvd_sub_iff_bmod_eq (L n u : ℕ) (hcop : IsCoprime (3 : ℤ) (L : ℤ)) :
    (L : ℤ) ∣ ((n : ℤ) - u) ↔ (3 * (n : ℤ)).bmod L = (3 * (u : ℤ)).bmod L := by
  rw [Int.bmod_eq_bmod_iff_bmod_sub_eq_zero, ← Int.dvd_iff_bmod_eq_zero]
  constructor
  · intro h
    have he : (3 * (n : ℤ)) - (3 * (u : ℤ)) = 3 * ((n : ℤ) - u) := by ring
    rw [he]; exact Dvd.dvd.mul_left h 3
  · intro h
    have h3 : (L : ℤ) ∣ 3 * ((n : ℤ) - u) := by
      have he : (3 * (n : ℤ)) - (3 * (u : ℤ)) = 3 * ((n : ℤ) - u) := by ring
      rwa [he] at h
    exact hcop.symm.dvd_of_dvd_mul_left h3

/-- **Heart (residue exponent identity).** For every `n`, the collected `numMinus` exponent plus
the charge exponent `negR 3 (3k-1) n` equals the target exponent `Erhs n`. Verified per residue
class mod `L = 3k+2` (informal_proof7.md): 0→2+0, k→1+1, 2k+2→1+1, k+1→2+0, 2k+1→2+0, else→0+2.
Uses `3⁻¹ ≡ k+1 mod L`. -/
lemma exp_pointwise (k n : ℕ) (hk : 2 ≤ k) :
    numE k n + HJO.negR 3 (3 * k - 1) n = Erhs n := by
  -- SANITY CHECK PASSED (#eval: identity holds for k=2,3,4 over all n up to 3L, no failures)
  have hLpos : 0 < 3 * k + 2 := by omega
  have hcop : IsCoprime (3 : ℤ) ((3 * k + 2 : ℕ) : ℤ) := by
    refine ⟨(k : ℤ) + 1, -1, ?_⟩; push_cast; ring
  have hnegR : HJO.negR 3 (3 * k - 1) n
      = (min 3 ((3 * (n : ℤ)).bmod (3 * k + 2)).natAbs
          + (if (3 * k + 2) ∣ n then 1 else 0)) - 1 := by
    unfold HJO.negR
    have h3 : min 3 (3 * k - 1) = 3 := by omega
    have hab : (3 : ℕ) + (3 * k - 1) = 3 * k + 2 := by omega
    rw [hab, h3]; norm_num
  rw [hnegR]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp only [numE, indic, Erhs, Nat.zero_sub, Nat.zero_mod]
    norm_num
    omega
  set r := (3 * (n : ℤ)).bmod (3 * k + 2) with hr
  have vk : (3 * ((k : ℤ))).bmod (3 * k + 2) = -2 := by
    rw [Int.bmod_eq_iff (by omega)]; push_cast; refine ⟨by omega, by omega, ⟨-1, by ring⟩⟩
  have v2k2 : (3 * ((2 * k + 2 : ℕ) : ℤ)).bmod (3 * k + 2) = 2 := by
    rw [Int.bmod_eq_iff (by omega)]; push_cast; refine ⟨by omega, by omega, ⟨-2, by ring⟩⟩
  have vk1 : (3 * ((k + 1 : ℕ) : ℤ)).bmod (3 * k + 2) = 1 := by
    rw [Int.bmod_eq_iff (by omega)]; push_cast; refine ⟨by omega, by omega, ⟨-1, by ring⟩⟩
  have v2k1 : (3 * ((2 * k + 1 : ℕ) : ℤ)).bmod (3 * k + 2) = -1 := by
    rw [Int.bmod_eq_iff (by omega)]; push_cast; refine ⟨by omega, by omega, ⟨-2, by ring⟩⟩
  have vL : (3 * ((3 * k + 2 : ℕ) : ℤ)).bmod (3 * k + 2) = 0 := by
    rw [Int.bmod_eq_iff (by omega)]; push_cast; refine ⟨by omega, by omega, ⟨-3, by ring⟩⟩
  have eL : indic (3 * k + 2) (3 * k + 2) n = if r = 0 then 1 else 0 := by
    rw [indic_eq_int_dvd _ _ _ (by omega) (le_refl _) hpos]
    have hiff := (dvd_sub_iff_bmod_eq (3 * k + 2) n (3 * k + 2) hcop).trans (by rw [← hr, vL])
    simp only [hiff]
  have ek : indic k (3 * k + 2) n = if r = -2 then 1 else 0 := by
    rw [indic_eq_int_dvd _ _ _ (by omega) (by omega) hpos]
    have hiff := (dvd_sub_iff_bmod_eq (3 * k + 2) n k hcop).trans (by rw [← hr, vk])
    simp only [hiff]
  have e2k2 : indic (2 * k + 2) (3 * k + 2) n = if r = 2 then 1 else 0 := by
    rw [indic_eq_int_dvd _ _ _ (by omega) (by omega) hpos]
    have hiff := (dvd_sub_iff_bmod_eq (3 * k + 2) n (2 * k + 2) hcop).trans (by rw [← hr, v2k2])
    simp only [hiff]
  have ek1 : indic (k + 1) (3 * k + 2) n = if r = 1 then 1 else 0 := by
    rw [indic_eq_int_dvd _ _ _ (by omega) (by omega) hpos]
    have hiff := (dvd_sub_iff_bmod_eq (3 * k + 2) n (k + 1) hcop).trans (by rw [← hr, vk1])
    simp only [hiff]
  have e2k1 : indic (2 * k + 1) (3 * k + 2) n = if r = -1 then 1 else 0 := by
    rw [indic_eq_int_dvd _ _ _ (by omega) (by omega) hpos]
    have hiff := (dvd_sub_iff_bmod_eq (3 * k + 2) n (2 * k + 1) hcop).trans (by rw [← hr, v2k1])
    simp only [hiff]
  have eLdvd : (if (3 * k + 2) ∣ n then (1 : ℕ) else 0) = if r = 0 then 1 else 0 := by
    have hthis : ((3 * k + 2) ∣ n) ↔ r = 0 := by
      rw [hr]
      constructor
      · intro hd
        have hdd : ((3 * k + 2 : ℕ) : ℤ) ∣ (3 * (n : ℤ)) := by
          obtain ⟨t, ht⟩ := hd; exact ⟨3 * t, by push_cast [ht]; ring⟩
        rw [← Int.dvd_iff_bmod_eq_zero]; exact hdd
      · intro hb
        rw [← Int.dvd_iff_bmod_eq_zero] at hb
        have hcop3 : ((3 * k + 2 : ℕ) : ℤ) ∣ (n : ℤ) := hcop.symm.dvd_of_dvd_mul_left hb
        exact_mod_cast hcop3
    simp only [hthis]
  have hErhs : Erhs n = 2 := by
    simp only [Erhs, indic]
    rw [if_pos ⟨by omega, by rw [Nat.mod_one]⟩]
  rw [hErhs, numE, eL, ek, e2k2, ek1, e2k1, eLdvd]
  have hbound : r.natAbs ≤ (3 * k + 2) / 2 := by
    have h1 : r ≤ ((3 * k + 2 : ℕ) - 1) / 2 := by rw [hr]; exact Int.bmod_le (by omega)
    have h2 : -((3 * k + 2 : ℕ) / 2 : ℤ) ≤ r := by rw [hr]; exact Int.le_bmod (by omega)
    have h3 : ((3 * k + 2 : ℕ) : ℤ) / 2 = ((3 * k + 2) / 2 : ℕ) := by push_cast; omega
    have h4 : (((3 * k + 2 : ℕ) : ℤ) - 1) / 2 ≤ ((3 * k + 2) / 2 : ℕ) := by push_cast; omega
    omega
  split_ifs <;> omega

/-- **SL2 (analytic core).** `numMinus k · Pminus k = (X;X)_∞²`. Both sides regroup by residue
mod `L = 3k+2` (via `residue_regroup`) into `∏_{c:Fin L} (X^c;X^L)_∞^{E(c)}`; the exponents
match because every residue class has total exponent exactly `2` (num-exponent + `negR`).  -/
theorem numMinus_mul_Pminus (k : ℕ) (hk : 2 ≤ k) :
    numMinus k * Pminus k = ((X; (X : ℤ⟦X⟧))_∞) ^ 2 := by
  rw [numMinus_as_prod k hk, qPoch_self_sq_as_prod]
  unfold Pminus
  rw [prod_one_sub_pow_mul]
  apply tprod_congr
  intro n
  rw [exp_pointwise k n hk]

/-- Constant coefficient of `(X;X)_∞²` is 1. -/
theorem constantCoeff_qPochhammerInf_sq :
    PowerSeries.constantCoeff (R := ℤ) (((X; (X : ℤ⟦X⟧))_∞) ^ 2) = 1 := by
  rw [map_pow, constantCoeff_qPochhammerInf X X HasEval.X PowerSeries.constantCoeff_X, one_pow]

/-! ### Plus case (`b = 3k+1`, `L = 3k+4`) — mirror of the minus machinery above. -/

/-- The genuine (non-negative-exponent) charge product for `b = 3k+1`. -/
noncomputable def Pplus (k : ℕ) : ℤ⟦X⟧ :=
  ∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ HJO.negR 3 (3 * k + 1) n

/-- The genuine (non-negative-exponent) numerator of `warnaarRHSplus`, `L = 3k+4`. -/
noncomputable def numPlus (k : ℕ) : ℤ⟦X⟧ :=
  ((X ^ (3 * k + 4); (X : ℤ⟦X⟧) ^ (3 * k + 4))_∞) ^ 2
    * (bTheta (k + 1) (3 * k + 4) * bTheta (k + 1) (3 * k + 4) * bTheta (k + 2) (3 * k + 4))

/-- `charge 3 (3k+1) = invOfUnit (Pplus k) 1`. -/
theorem charge_plus_eq_invOfUnit (k : ℕ) (hk : 1 ≤ k) :
    HJO.charge 3 (3 * k + 1) = PowerSeries.invOfUnit (Pplus k) 1 := by
  unfold HJO.charge Pplus
  exact prod_invOfUnit_eq_invOfUnit_prod (HJO.negR 3 (3 * k + 1)) (negR_zero 3 (3 * k + 1))

/-- Constant coefficient of `Pplus k` is 1. -/
theorem constantCoeff_Pplus (k : ℕ) (hk : 1 ≤ k) :
    PowerSeries.constantCoeff (R := ℤ) (Pplus k) = 1 := by
  unfold Pplus
  exact constantCoeff_prod_one_sub_pow (HJO.negR 3 (3 * k + 1)) (negR_zero 3 (3 * k + 1))

/-- The exponent function of `numPlus k` collected over all `(X^a;X^L)_∞` factors, `L=3k+4`. -/
noncomputable def numPlusE (k n : ℕ) : ℕ :=
  2 * indic (3 * k + 4) (3 * k + 4) n
    + 2 * indic (k + 1) (3 * k + 4) n
    + 2 * indic (2 * k + 3) (3 * k + 4) n
    + indic (k + 2) (3 * k + 4) n
    + indic (2 * k + 2) (3 * k + 4) n

/-- `numPlus k` written as a genuine `∏' (1-X^n)^{numPlusE k n}`. -/
lemma numPlus_as_prod (k : ℕ) (hk : 1 ≤ k) :
    numPlus k = ∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ n) ^ numPlusE k n := by
  have hLk1 : 3 * k + 4 - (k + 1) = 2 * k + 3 := by omega
  have hLk2 : 3 * k + 4 - (k + 2) = 2 * k + 2 := by omega
  unfold numPlus bTheta
  rw [hLk1, hLk2]
  rw [qPochInf_as_indic (3 * k + 4) (3 * k + 4) (by omega) (by omega)]
  rw [qPochInf_as_indic (k + 1) (3 * k + 4) (by omega) (by omega)]
  rw [qPochInf_as_indic (2 * k + 3) (3 * k + 4) (by omega) (by omega)]
  rw [qPochInf_as_indic (k + 2) (3 * k + 4) (by omega) (by omega)]
  rw [qPochInf_as_indic (2 * k + 2) (3 * k + 4) (by omega) (by omega)]
  rw [prod_one_sub_pow_sq]
  rw [prod_one_sub_pow_mul, prod_one_sub_pow_mul, prod_one_sub_pow_mul,
      prod_one_sub_pow_mul, prod_one_sub_pow_mul]
  apply tprod_congr
  intro n
  congr 1
  simp only [numPlusE]
  omega

/-- **Heart (plus).** For every `n`, `numPlusE k n + negR 3 (3k+1) n = Erhs n`. Verified per
residue class mod `L = 3k+4`: 0→2+0, k+1→2+0, 2k+3→2+0, k+2→1+1, 2k+2→1+1, else→0+2.
Uses `3⁻¹ ≡ 2k+3 mod L`. -/
lemma exp_pointwise_plus (k n : ℕ) (hk : 1 ≤ k) :
    numPlusE k n + HJO.negR 3 (3 * k + 1) n = Erhs n := by
  -- SANITY CHECK PASSED (#eval: identity holds for k=1,2,3 over all n up to 3L, no failures)
  have hcop : IsCoprime (3 : ℤ) ((3 * k + 4 : ℕ) : ℤ) := by
    refine ⟨-((k : ℤ) + 1), 1, ?_⟩; push_cast; ring
  have hnegR : HJO.negR 3 (3 * k + 1) n
      = (min 3 ((3 * (n : ℤ)).bmod (3 * k + 4)).natAbs
          + (if (3 * k + 4) ∣ n then 1 else 0)) - 1 := by
    unfold HJO.negR
    have h3 : min 3 (3 * k + 1) = 3 := by omega
    have hab : (3 : ℕ) + (3 * k + 1) = 3 * k + 4 := by omega
    rw [hab, h3]; norm_num
  rw [hnegR]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp only [numPlusE, indic, Erhs, Nat.zero_sub, Nat.zero_mod]
    norm_num
  set r := (3 * (n : ℤ)).bmod (3 * k + 4) with hr
  have vk1 : (3 * ((k + 1 : ℕ) : ℤ)).bmod (3 * k + 4) = -1 := by
    rw [Int.bmod_eq_iff (by omega)]; push_cast; refine ⟨by omega, by omega, ⟨-1, by ring⟩⟩
  have v2k3 : (3 * ((2 * k + 3 : ℕ) : ℤ)).bmod (3 * k + 4) = 1 := by
    rw [Int.bmod_eq_iff (by omega)]; push_cast; refine ⟨by omega, by omega, ⟨-2, by ring⟩⟩
  have vk2 : (3 * ((k + 2 : ℕ) : ℤ)).bmod (3 * k + 4) = 2 := by
    rw [Int.bmod_eq_iff (by omega)]; push_cast; refine ⟨by omega, by omega, ⟨-1, by ring⟩⟩
  have v2k2 : (3 * ((2 * k + 2 : ℕ) : ℤ)).bmod (3 * k + 4) = -2 := by
    rw [Int.bmod_eq_iff (by omega)]; push_cast; refine ⟨by omega, by omega, ⟨-2, by ring⟩⟩
  have vL : (3 * ((3 * k + 4 : ℕ) : ℤ)).bmod (3 * k + 4) = 0 := by
    rw [Int.bmod_eq_iff (by omega)]; push_cast; refine ⟨by omega, by omega, ⟨-3, by ring⟩⟩
  have eL : indic (3 * k + 4) (3 * k + 4) n = if r = 0 then 1 else 0 := by
    rw [indic_eq_int_dvd _ _ _ (by omega) (le_refl _) hpos]
    have hiff := (dvd_sub_iff_bmod_eq (3 * k + 4) n (3 * k + 4) hcop).trans (by rw [← hr, vL])
    simp only [hiff]
  have ek1 : indic (k + 1) (3 * k + 4) n = if r = -1 then 1 else 0 := by
    rw [indic_eq_int_dvd _ _ _ (by omega) (by omega) hpos]
    have hiff := (dvd_sub_iff_bmod_eq (3 * k + 4) n (k + 1) hcop).trans (by rw [← hr, vk1])
    simp only [hiff]
  have e2k3 : indic (2 * k + 3) (3 * k + 4) n = if r = 1 then 1 else 0 := by
    rw [indic_eq_int_dvd _ _ _ (by omega) (by omega) hpos]
    have hiff := (dvd_sub_iff_bmod_eq (3 * k + 4) n (2 * k + 3) hcop).trans (by rw [← hr, v2k3])
    simp only [hiff]
  have ek2 : indic (k + 2) (3 * k + 4) n = if r = 2 then 1 else 0 := by
    rw [indic_eq_int_dvd _ _ _ (by omega) (by omega) hpos]
    have hiff := (dvd_sub_iff_bmod_eq (3 * k + 4) n (k + 2) hcop).trans (by rw [← hr, vk2])
    simp only [hiff]
  have e2k2 : indic (2 * k + 2) (3 * k + 4) n = if r = -2 then 1 else 0 := by
    rw [indic_eq_int_dvd _ _ _ (by omega) (by omega) hpos]
    have hiff := (dvd_sub_iff_bmod_eq (3 * k + 4) n (2 * k + 2) hcop).trans (by rw [← hr, v2k2])
    simp only [hiff]
  have eLdvd : (if (3 * k + 4) ∣ n then (1 : ℕ) else 0) = if r = 0 then 1 else 0 := by
    have hthis : ((3 * k + 4) ∣ n) ↔ r = 0 := by
      rw [hr]
      constructor
      · intro hd
        have hdd : ((3 * k + 4 : ℕ) : ℤ) ∣ (3 * (n : ℤ)) := by
          obtain ⟨t, ht⟩ := hd; exact ⟨3 * t, by push_cast [ht]; ring⟩
        rw [← Int.dvd_iff_bmod_eq_zero]; exact hdd
      · intro hb
        rw [← Int.dvd_iff_bmod_eq_zero] at hb
        have hcop3 : ((3 * k + 4 : ℕ) : ℤ) ∣ (n : ℤ) := hcop.symm.dvd_of_dvd_mul_left hb
        exact_mod_cast hcop3
    simp only [hthis]
  have hErhs : Erhs n = 2 := by
    simp only [Erhs, indic]
    rw [if_pos ⟨by omega, by rw [Nat.mod_one]⟩]
  rw [hErhs, numPlusE, eL, ek1, e2k3, ek2, e2k2, eLdvd]
  have hbound : r.natAbs ≤ (3 * k + 4) / 2 := by
    have h1 : r ≤ ((3 * k + 4 : ℕ) - 1) / 2 := by rw [hr]; exact Int.bmod_le (by omega)
    have h2 : -((3 * k + 4 : ℕ) / 2 : ℤ) ≤ r := by rw [hr]; exact Int.le_bmod (by omega)
    have h3 : ((3 * k + 4 : ℕ) : ℤ) / 2 = ((3 * k + 4) / 2 : ℕ) := by push_cast; omega
    have h4 : (((3 * k + 4 : ℕ) : ℤ) - 1) / 2 ≤ ((3 * k + 4) / 2 : ℕ) := by push_cast; omega
    omega
  split_ifs <;> omega

/-- **SL2 (analytic core, plus).** `numPlus k · Pplus k = (X;X)_∞²`. -/
theorem numPlus_mul_Pplus (k : ℕ) (hk : 1 ≤ k) :
    numPlus k * Pplus k = ((X; (X : ℤ⟦X⟧))_∞) ^ 2 := by
  rw [numPlus_as_prod k hk, qPoch_self_sq_as_prod]
  unfold Pplus
  rw [prod_one_sub_pow_mul]
  apply tprod_congr
  intro n
  rw [exp_pointwise_plus k n hk]

/-- **Statement 7(plus) — residue computation (final step of Theorem 1.1), `b=3k+1`.** Matching
the charge residues to the Warnaar theta products. Uses Fact 4. -/
theorem stmt7_residue_plus (k : ℕ) (hk : 1 ≤ k) (hWarnaar : Fact4) :
    fermPlus k = HJO.charge 3 (3 * k + 1) := by
  -- SANITY CHECK PASSED (final step of Thm 1.1, plus: `fermPlus k` equals the charge product
  -- `HJO.charge 3 (3k+1)`. By Fact4 (Warnaar) `fermPlus k = warnaarRHSplus k` (a product of two
  -- Pochhammer factors, inverse `(q;q)_∞²`, and three θ's); it remains to identify that theta
  -- product with `HJO.charge 3 (3k+1) = ∏' (1-Xⁿ)^{negR 3 (3k+1) n}` residue-by-residue).
  -- ARGUMENT: `rw [(hWarnaar.2 k hk)]` turns the goal into `warnaarRHSplus k = HJO.charge 3 (3k+1)`.
  -- Then expand both as infinite products over `n` and match multiplicities: `HJO.charge`'s
  -- exponent `negR 3 b n` is the Rogers–Ramanujan/theta residue pattern for modulus `b·(…)`,
  -- and the Warnaar RHS θ-products `bTheta u L` unfold via the Jacobi triple product to the same
  -- exponent sequence. This is a formal-power-series product identity (θ ↔ charge dictionary).
  -- CLOSED (this run): mirror of stmt7_residue_minus. `warnaarRHSplus k = numPlus k · invOfUnit den 1`
  -- with `den = (X;X)_∞²`; cross-multiply via `numPlus_mul_Pplus`.
  rw [hWarnaar.2 k hk, charge_plus_eq_invOfUnit k hk]
  have hwarn : warnaarRHSplus k
      = numPlus k * PowerSeries.invOfUnit (((X; (X : ℤ⟦X⟧))_∞) ^ 2) 1 := by
    unfold warnaarRHSplus numPlus; ring
  rw [hwarn]
  exact invOfUnit_cross_mul (numPlus k) (Pplus k) (((X; (X : ℤ⟦X⟧))_∞) ^ 2)
    (constantCoeff_Pplus k hk) constantCoeff_qPochhammerInf_sq (numPlus_mul_Pplus k hk)

/-- **Statement 7(minus) — residue computation, `b=3k-1`.** -/
theorem stmt7_residue_minus (k : ℕ) (hk : 2 ≤ k) (hWarnaar : Fact4) :
    fermMinus k = HJO.charge 3 (3 * k - 1) := by
  -- SANITY CHECK PASSED (final step of Thm 1.1, minus: `fermMinus k = HJO.charge 3 (3k-1)`.
  rw [hWarnaar.1 k hk, charge_minus_eq_invOfUnit k hk]
  -- warnaarRHSminus k = numMinus k * invOfUnit den 1, den = (X;X)_∞²
  have hwarn : warnaarRHSminus k
      = numMinus k * PowerSeries.invOfUnit (((X; (X : ℤ⟦X⟧))_∞) ^ 2) 1 := by
    unfold warnaarRHSminus numMinus; ring
  rw [hwarn]
  -- cross-multiply using numMinus·Pminus = den
  exact invOfUnit_cross_mul (numMinus k) (Pminus k) (((X; (X : ℤ⟦X⟧))_∞) ^ 2)
    (constantCoeff_Pminus k hk) constantCoeff_qPochhammerInf_sq (numMinus_mul_Pminus k hk)

/-- The per-`(r,m)` fermionic body of `fermPlus`, WITHOUT the outer boundary factor
`invOfUnit((q)_{r₁})·∏[rᵢ;rᵢ₊₁]`. This is exactly the `fermPlus` summand with `r = acc d.1.1`,
`m = acc d.1.2`, divided by `outerP`. -/
noncomputable def fermBodyP (k : ℕ) (r m : Fin k → ℕ) : ℤ⟦X⟧ :=
  X ^ (∑ i ∈ Icc 1 k, (acc r i ^ 2 + acc m i ^ 2 - acc r i * acc m i)) *
      qChoose qX (2 * acc r k) (acc m k) *
      ∏ i ∈ Icc 1 (k - 1), qChoose qX (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i)

/-- The outer boundary factor `invOfUnit((q)_{r₁})·∏_{i=1}^{k-1}[rᵢ;rᵢ₊₁]`, as a function of the
boundary tuple `r` (1-indexed via `acc`). It matches BOTH the reassembled `r`-sum LHS and the
outer factors in the `fermPlus` summand. -/
noncomputable def outerP (k : ℕ) (r : Fin k → ℕ) : ℤ⟦X⟧ :=
  invOfUnit (qPochhammer qX qX (acc r 1)) 1 *
    ∏ i ∈ Icc 1 (k - 1), qChoose qX (acc r i) (acc r (i + 1))


/-- The "rest" factor of the `fermPlus` summand after pulling out `X^E`. -/
noncomputable def gRestP (k : ℕ) (r m : Fin k → ℕ) : ℤ⟦X⟧ :=
  invOfUnit (qPochhammer qX qX (acc r 1)) 1 *
      (∏ i ∈ Icc 1 (k - 1), qChoose qX (acc r i) (acc r (i + 1))) *
      qChoose qX (2 * acc r k) (acc m k) *
      ∏ i ∈ Icc 1 (k - 1), qChoose qX (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i)

/-- Exponent of the `fermPlus` summand. -/
def expP (k : ℕ) (r m : Fin k → ℕ) : ℕ :=
  ∑ i ∈ Icc 1 k, (acc r i ^ 2 + acc m i ^ 2 - acc r i * acc m i)

lemma outerP_mul_fermBodyP_eq (k : ℕ) (r m : Fin k → ℕ) :
    outerP k r * fermBodyP k r m = X ^ (expP k r m) * gRestP k r m := by
  simp only [outerP, fermBodyP, gRestP, expP]; ring

lemma sq_le_two_mul_quad (a b : ℕ) : a ^ 2 ≤ 2 * (a ^ 2 + b ^ 2 - a * b) := by
  have h : a * b ≤ a ^ 2 + b ^ 2 := by nlinarith [Nat.zero_le (a * b)]
  nlinarith [h, Nat.sub_add_cancel h]

/-- If `d0` is below the exponent, the coefficient vanishes. -/
lemma coeff_outerP_fermBodyP_eq_zero (k : ℕ) (r m : Fin k → ℕ) (d0 : ℕ)
    (h : d0 < expP k r m) :
    (PowerSeries.coeff d0) (outerP k r * fermBodyP k r m) = 0 := by
  rw [outerP_mul_fermBodyP_eq, PowerSeries.coeff_X_pow_mul']
  rw [if_neg (by omega)]

/-- Support of the `d0`-coefficient of the factored `fermPlus` family is finite. -/
lemma finite_support_coeff_fermPlus (k d0 : ℕ) :
    (Function.support
      (fun d : DomP k => (PowerSeries.coeff d0) (outerP k d.1.1 * fermBodyP k d.1.1 d.1.2))).Finite := by
  -- support ⊆ preimage under Subtype.val of a finite box in (Fin k → ℕ) × (Fin k → ℕ)
  apply Set.Finite.subset
    (s := (Subtype.val ⁻¹'
      {p : (Fin k → ℕ) × (Fin k → ℕ) | (∀ j : Fin k, p.1 j ≤ 2 * d0) ∧ (∀ j : Fin k, p.2 j ≤ 2 * d0)}))
  · -- the box is finite: it injects into (Fin k → Fin (2*d0+1)) × (Fin k → Fin (2*d0+1))
    apply Set.Finite.preimage (Subtype.val_injective.injOn)
    have hfin : {p : (Fin k → ℕ) × (Fin k → ℕ) |
        (∀ j : Fin k, p.1 j ≤ 2 * d0) ∧ (∀ j : Fin k, p.2 j ≤ 2 * d0)}.Finite := by
      apply Set.Finite.subset (Set.finite_Icc ((fun _ => 0, fun _ => 0) : (Fin k → ℕ) × (Fin k → ℕ))
        ((fun _ => 2 * d0, fun _ => 2 * d0) : (Fin k → ℕ) × (Fin k → ℕ)))
      intro p hp
      simp only [Set.mem_setOf_eq] at hp
      simp only [Set.mem_Icc, Prod.le_def, Pi.le_def]
      refine ⟨⟨fun j => Nat.zero_le _, fun j => Nat.zero_le _⟩, ⟨fun j => hp.1 j, fun j => hp.2 j⟩⟩
    exact hfin
  · -- inclusion of the support
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    by_contra hcon
    apply hd
    -- if d not in the box, some coordinate exceeds 2d0, forcing expP > d0, so coeff = 0
    apply coeff_outerP_fermBodyP_eq_zero
    -- need d0 < expP k d.1.1 d.1.2
    simp only [Set.mem_preimage, Set.mem_setOf_eq, not_and_or, not_forall, not_le] at hcon
    -- get a coordinate j with value > 2*d0
    rcases hcon with hcon | hcon
    · obtain ⟨j, hj⟩ := hcon
      -- acc d.1.1 (j+1) = d.1.1 j
      have hacc : acc d.1.1 (j + 1) = d.1.1 j := by
        rw [acc_val d.1.1 (j + 1) (by omega) (by have := j.2; omega)]
        congr 1
      have hterm : (d.1.1 j) ^ 2 ≤ 2 * (acc d.1.1 (j + 1) ^ 2 + acc d.1.2 (j + 1) ^ 2
          - acc d.1.1 (j + 1) * acc d.1.2 (j + 1)) := by
        rw [hacc]; exact sq_le_two_mul_quad _ _
      have hmem : (j : ℕ) + 1 ∈ Icc 1 k := by
        simp only [Finset.mem_Icc]; have := j.2; omega
      have hle : (acc d.1.1 (j + 1) ^ 2 + acc d.1.2 (j + 1) ^ 2
          - acc d.1.1 (j + 1) * acc d.1.2 (j + 1)) ≤ expP k d.1.1 d.1.2 := by
        apply Finset.single_le_sum (f := fun i => acc d.1.1 i ^ 2 + acc d.1.2 i ^ 2 - acc d.1.1 i * acc d.1.2 i)
          (fun i _ => Nat.zero_le _) hmem
      -- d.1.1 j > 2 d0 ⇒ (d.1.1 j)^2 > 2 d0 ⇒ 2*term ≥ (d.1.1 j)^2 > 2 d0 ⇒ term > d0 ⇒ expP > d0
      have : (2 * d0) ^ 2 < (d.1.1 j) ^ 2 := by
        apply Nat.pow_lt_pow_left hj; omega
      nlinarith [hterm, hle, this]
    · obtain ⟨j, hj⟩ := hcon
      have hacc : acc d.1.2 (j + 1) = d.1.2 j := by
        rw [acc_val d.1.2 (j + 1) (by omega) (by have := j.2; omega)]
        congr 1
      have hterm : (d.1.2 j) ^ 2 ≤ 2 * (acc d.1.1 (j + 1) ^ 2 + acc d.1.2 (j + 1) ^ 2
          - acc d.1.1 (j + 1) * acc d.1.2 (j + 1)) := by
        have h2 := sq_le_two_mul_quad (acc d.1.2 (j+1)) (acc d.1.1 (j+1))
        rw [hacc] at h2 ⊢
        calc (d.1.2 j) ^ 2 ≤ 2 * (d.1.2 j ^ 2 + acc d.1.1 (j+1) ^ 2 - d.1.2 j * acc d.1.1 (j+1)) := h2
          _ = 2 * (acc d.1.1 (j+1) ^ 2 + d.1.2 j ^ 2 - acc d.1.1 (j+1) * d.1.2 j) := by ring_nf
      have hmem : (j : ℕ) + 1 ∈ Icc 1 k := by
        simp only [Finset.mem_Icc]; have := j.2; omega
      have hle : (acc d.1.1 (j + 1) ^ 2 + acc d.1.2 (j + 1) ^ 2
          - acc d.1.1 (j + 1) * acc d.1.2 (j + 1)) ≤ expP k d.1.1 d.1.2 := by
        apply Finset.single_le_sum (f := fun i => acc d.1.1 i ^ 2 + acc d.1.2 i ^ 2 - acc d.1.1 i * acc d.1.2 i)
          (fun i _ => Nat.zero_le _) hmem
      have : (2 * d0) ^ 2 < (d.1.2 j) ^ 2 := by
        apply Nat.pow_lt_pow_left hj; omega
      nlinarith [hterm, hle, this]

lemma summable_outerP_fermBodyP (k : ℕ) :
    Summable (fun d : DomP k => outerP k d.1.1 * fermBodyP k d.1.1 d.1.2) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d0
  exact summable_of_finite_support (finite_support_coeff_fermPlus k d0)



/-- The rest factor of the bare `fermBodyP` summand after pulling `X^E`. -/
noncomputable def gRestB (k : ℕ) (r m : Fin k → ℕ) : ℤ⟦X⟧ :=
  qChoose qX (2 * acc r k) (acc m k) *
    ∏ i ∈ Icc 1 (k - 1), qChoose qX (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i)

lemma fermBodyP_eq (k : ℕ) (r m : Fin k → ℕ) :
    fermBodyP k r m = X ^ (expP k r m) * gRestB k r m := by
  simp only [fermBodyP, gRestB, expP]; ring

lemma coeff_fermBodyP_eq_zero (k : ℕ) (r m : Fin k → ℕ) (d0 : ℕ)
    (h : d0 < expP k r m) :
    (PowerSeries.coeff d0) (fermBodyP k r m) = 0 := by
  rw [fermBodyP_eq, PowerSeries.coeff_X_pow_mul']
  rw [if_neg (by omega)]

lemma finite_support_coeff_fermBodyP (k : ℕ) (r : Fin k → ℕ) (d0 : ℕ) :
    (Function.support (fun m : Fin k → ℕ => (PowerSeries.coeff d0) (fermBodyP k r m))).Finite := by
  apply Set.Finite.subset
    (s := {m : Fin k → ℕ | ∀ j : Fin k, m j ≤ 2 * d0})
  · apply Set.Finite.subset (Set.finite_Icc ((fun _ => 0) : Fin k → ℕ) ((fun _ => 2 * d0) : Fin k → ℕ))
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    simp only [Set.mem_Icc, Pi.le_def]
    exact ⟨fun j => Nat.zero_le _, fun j => hm j⟩
  · intro m hm
    simp only [Function.mem_support, ne_eq] at hm
    by_contra hcon
    apply hm
    apply coeff_fermBodyP_eq_zero
    simp only [Set.mem_setOf_eq, not_forall, not_le] at hcon
    obtain ⟨j, hj⟩ := hcon
    have hacc : acc m (j + 1) = m j := by
      rw [acc_val m (j + 1) (by omega) (by have := j.2; omega)]; congr 1
    have hterm : (m j) ^ 2 ≤ 2 * (acc r (j + 1) ^ 2 + acc m (j + 1) ^ 2
        - acc r (j + 1) * acc m (j + 1)) := by
      have h2 := sq_le_two_mul_quad (acc m (j+1)) (acc r (j+1))
      rw [hacc] at h2 ⊢
      calc (m j) ^ 2 ≤ 2 * (m j ^ 2 + acc r (j+1) ^ 2 - m j * acc r (j+1)) := h2
        _ = 2 * (acc r (j+1) ^ 2 + m j ^ 2 - acc r (j+1) * m j) := by ring_nf
    have hmem : (j : ℕ) + 1 ∈ Icc 1 k := by
      simp only [Finset.mem_Icc]; have := j.2; omega
    have hle : (acc r (j + 1) ^ 2 + acc m (j + 1) ^ 2
        - acc r (j + 1) * acc m (j + 1)) ≤ expP k r m := by
      apply Finset.single_le_sum (f := fun i => acc r i ^ 2 + acc m i ^ 2 - acc r i * acc m i)
        (fun i _ => Nat.zero_le _) hmem
    have : (2 * d0) ^ 2 < (m j) ^ 2 := by
      apply Nat.pow_lt_pow_left hj; omega
    nlinarith [hterm, hle, this]

lemma summable_fermBodyP (k : ℕ) (r : Fin k → ℕ) :
    Summable (fun m : Fin k → ℕ => fermBodyP k r m) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d0
  exact summable_of_finite_support (finite_support_coeff_fermBodyP k r d0)


/-- **`fermPlus` as an outer·body double t-sum over `{r//Antitone r} × (Fin k→ℕ)`.**
`fermPlus k = ∑' r:{r//Antitone r}, outerP k r · (∑' m, fermBodyP k r m)`. This is the Fubini /
Sigma-reindex of the single `∑' d:DomP k` in the definition of `fermPlus`, using
`DomP k ≃ Σ r:{r//Antitone r}, (Fin k→ℕ)` (the `m`-fibre is unconstrained), plus `Summable`
from `hPD` (Fact8 finiteness datum). ROUTINE. Deferred as a sub-lemma. -/
theorem fermPlus_eq_tsum_perR (k : ℕ) (hk : 1 ≤ k) (hPD : Fact8 3 (3 * k + 1)) :
    fermPlus k
      = ∑' r : { r : Fin k → ℕ // Antitone r }, outerP k r * (∑' m : Fin k → ℕ, fermBodyP k r m) := by
  -- Step 1: rewrite the `fermPlus` summand as `outerP · fermBodyP`.
  have hsummand : fermPlus k
      = ∑' d : DomP k, outerP k d.1.1 * fermBodyP k d.1.1 d.1.2 := by
    unfold fermPlus
    refine tsum_congr (fun d => ?_)
    simp only [outerP, fermBodyP]
    ring
  rw [hsummand]
  -- Step 2: reindex via the equiv `DomP k ≃ {r // Antitone r} × (Fin k → ℕ)`.
  set e : DomP k ≃ { r : Fin k → ℕ // Antitone r } × (Fin k → ℕ) :=
    Equiv.prodSubtypeFstEquivSubtypeProd (p := (Antitone : (Fin k → ℕ) → Prop)) with he
  have hsumm : Summable (fun d : DomP k => outerP k d.1.1 * fermBodyP k d.1.1 d.1.2) :=
    summable_outerP_fermBodyP k
  -- transport summand along e.symm
  rw [← Equiv.tsum_eq e.symm (fun d : DomP k => outerP k d.1.1 * fermBodyP k d.1.1 d.1.2)]
  -- Now index over the product; identify the reindexed summand.
  have hpt : ∀ p : { r : Fin k → ℕ // Antitone r } × (Fin k → ℕ),
      outerP k (e.symm p).1.1 * fermBodyP k (e.symm p).1.1 (e.symm p).1.2
        = outerP k p.1 * fermBodyP k p.1 p.2 := by
    intro p; rfl
  rw [tsum_congr hpt]
  -- Summable on the product side.
  have hsumm' : Summable (fun p : { r : Fin k → ℕ // Antitone r } × (Fin k → ℕ) =>
      outerP k p.1 * fermBodyP k p.1 p.2) := by
    have := (Equiv.summable_iff e.symm).2 hsumm
    refine this.congr ?_
    intro p; exact hpt p
  -- Step 3: Fubini split the product t-sum.
  rw [hsumm'.tsum_prod']
  · -- Step 4: pull `outerP k r` out of the inner t-sum.
    refine tsum_congr (fun r => ?_)
    show ∑' c : Fin k → ℕ, outerP k r * fermBodyP k r c = outerP k r * ∑' m, fermBodyP k r m
    exact (summable_fermBodyP k r).tsum_mul_left (outerP k r)
  · -- inner summability for each fixed r
    intro r
    exact ((Equiv.summable_iff e.symm).2 hsumm |>.congr (fun p => hpt p)).prod_factor r

/-! ### Minus-side fermionic infrastructure (mirror of the plus template). -/

/-- The per-`(r,m)` fermionic body of `fermMinus`, WITHOUT the outer boundary factor
`invOfUnit((q)_{r₁})·∏[rᵢ;rᵢ₊₁]`.  Here `m : Fin (k-1) → ℕ`. -/
noncomputable def fermBodyM (k : ℕ) (r : Fin k → ℕ) (m : Fin (k - 1) → ℕ) : ℤ⟦X⟧ :=
  X ^ (acc r k ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i ^ 2 + acc m i ^ 2 - acc r i * acc m i)) *
      qChoose qX (acc r (k - 1) + acc r k) (acc m (k - 1)) *
      ∏ i ∈ Icc 1 (k - 2), qChoose qX (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i)

/-- The outer boundary factor for the minus case (identical to `outerP`). -/
noncomputable def outerM (k : ℕ) (r : Fin k → ℕ) : ℤ⟦X⟧ := outerP k r

/-- Exponent of the `fermMinus` summand. -/
def expM (k : ℕ) (r : Fin k → ℕ) (m : Fin (k - 1) → ℕ) : ℕ :=
  acc r k ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i ^ 2 + acc m i ^ 2 - acc r i * acc m i)

/-- The rest factor of the bare `fermBodyM` summand after pulling `X^E`. -/
noncomputable def gRestBM (k : ℕ) (r : Fin k → ℕ) (m : Fin (k - 1) → ℕ) : ℤ⟦X⟧ :=
  qChoose qX (acc r (k - 1) + acc r k) (acc m (k - 1)) *
    ∏ i ∈ Icc 1 (k - 2), qChoose qX (acc r i - acc r (i + 1) + acc m (i + 1)) (acc m i)

lemma fermBodyM_eq (k : ℕ) (r : Fin k → ℕ) (m : Fin (k - 1) → ℕ) :
    fermBodyM k r m = X ^ (expM k r m) * gRestBM k r m := by
  simp only [fermBodyM, gRestBM, expM]; ring

lemma coeff_fermBodyM_eq_zero (k : ℕ) (r : Fin k → ℕ) (m : Fin (k - 1) → ℕ) (d0 : ℕ)
    (h : d0 < expM k r m) :
    (PowerSeries.coeff d0) (fermBodyM k r m) = 0 := by
  rw [fermBodyM_eq, PowerSeries.coeff_X_pow_mul']
  rw [if_neg (by omega)]

lemma finite_support_coeff_fermBodyM (k : ℕ) (r : Fin k → ℕ) (d0 : ℕ) :
    (Function.support (fun m : Fin (k - 1) → ℕ => (PowerSeries.coeff d0) (fermBodyM k r m))).Finite := by
  apply Set.Finite.subset
    (s := {m : Fin (k - 1) → ℕ | ∀ j : Fin (k - 1), m j ≤ 2 * d0})
  · apply Set.Finite.subset (Set.finite_Icc ((fun _ => 0) : Fin (k - 1) → ℕ)
      ((fun _ => 2 * d0) : Fin (k - 1) → ℕ))
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    simp only [Set.mem_Icc, Pi.le_def]
    exact ⟨fun j => Nat.zero_le _, fun j => hm j⟩
  · intro m hm
    simp only [Function.mem_support, ne_eq] at hm
    by_contra hcon
    apply hm
    apply coeff_fermBodyM_eq_zero
    simp only [Set.mem_setOf_eq, not_forall, not_le] at hcon
    obtain ⟨j, hj⟩ := hcon
    -- acc m (j+1) = m j  for j : Fin (k-1)
    have hacc : acc m (j + 1) = m j := by
      rw [acc_val m (j + 1) (by omega) (by have := j.2; omega)]; congr 1
    have hterm : (m j) ^ 2 ≤ 2 * (acc r (j + 1) ^ 2 + acc m (j + 1) ^ 2
        - acc r (j + 1) * acc m (j + 1)) := by
      have h2 := sq_le_two_mul_quad (acc m (j+1)) (acc r (j+1))
      rw [hacc] at h2 ⊢
      calc (m j) ^ 2 ≤ 2 * (m j ^ 2 + acc r (j+1) ^ 2 - m j * acc r (j+1)) := h2
        _ = 2 * (acc r (j+1) ^ 2 + m j ^ 2 - acc r (j+1) * m j) := by ring_nf
    have hmem : (j : ℕ) + 1 ∈ Icc 1 (k - 1) := by
      simp only [Finset.mem_Icc]; have := j.2; omega
    have hle : (acc r (j + 1) ^ 2 + acc m (j + 1) ^ 2
        - acc r (j + 1) * acc m (j + 1))
        ≤ ∑ i ∈ Icc 1 (k - 1), (acc r i ^ 2 + acc m i ^ 2 - acc r i * acc m i) := by
      apply Finset.single_le_sum (f := fun i => acc r i ^ 2 + acc m i ^ 2 - acc r i * acc m i)
        (fun i _ => Nat.zero_le _) hmem
    have hexp : ∑ i ∈ Icc 1 (k - 1), (acc r i ^ 2 + acc m i ^ 2 - acc r i * acc m i)
        ≤ expM k r m := by simp only [expM]; omega
    have : (2 * d0) ^ 2 < (m j) ^ 2 := by
      apply Nat.pow_lt_pow_left hj; omega
    nlinarith [hterm, hle, hexp, this]

lemma summable_fermBodyM (k : ℕ) (r : Fin k → ℕ) :
    Summable (fun m : Fin (k - 1) → ℕ => fermBodyM k r m) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d0
  exact summable_of_finite_support (finite_support_coeff_fermBodyM k r d0)

lemma outerM_mul_fermBodyM_eq (k : ℕ) (r : Fin k → ℕ) (m : Fin (k - 1) → ℕ) :
    outerM k r * fermBodyM k r m = X ^ (expM k r m) *
      (outerP k r * gRestBM k r m) := by
  rw [outerM, fermBodyM_eq]; ring

lemma coeff_outerM_fermBodyM_eq_zero (k : ℕ) (r : Fin k → ℕ) (m : Fin (k - 1) → ℕ) (d0 : ℕ)
    (h : d0 < expM k r m) :
    (PowerSeries.coeff d0) (outerM k r * fermBodyM k r m) = 0 := by
  rw [outerM_mul_fermBodyM_eq, PowerSeries.coeff_X_pow_mul']
  rw [if_neg (by omega)]

lemma finite_support_coeff_fermMinus (k d0 : ℕ) :
    (Function.support
      (fun d : DomM k => (PowerSeries.coeff d0) (outerM k d.1.1 * fermBodyM k d.1.1 d.1.2))).Finite := by
  apply Set.Finite.subset
    (s := (Subtype.val ⁻¹'
      {p : (Fin k → ℕ) × (Fin (k - 1) → ℕ) |
        (∀ j : Fin k, p.1 j ≤ 2 * d0) ∧ (∀ j : Fin (k - 1), p.2 j ≤ 2 * d0)}))
  · apply Set.Finite.preimage (Subtype.val_injective.injOn)
    have hfin : {p : (Fin k → ℕ) × (Fin (k - 1) → ℕ) |
        (∀ j : Fin k, p.1 j ≤ 2 * d0) ∧ (∀ j : Fin (k - 1), p.2 j ≤ 2 * d0)}.Finite := by
      apply Set.Finite.subset (Set.finite_Icc
        ((fun _ => 0, fun _ => 0) : (Fin k → ℕ) × (Fin (k - 1) → ℕ))
        ((fun _ => 2 * d0, fun _ => 2 * d0) : (Fin k → ℕ) × (Fin (k - 1) → ℕ)))
      intro p hp
      simp only [Set.mem_setOf_eq] at hp
      simp only [Set.mem_Icc, Prod.le_def, Pi.le_def]
      exact ⟨⟨fun j => Nat.zero_le _, fun j => Nat.zero_le _⟩, ⟨fun j => hp.1 j, fun j => hp.2 j⟩⟩
    exact hfin
  · intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    by_contra hcon
    apply hd
    apply coeff_outerM_fermBodyM_eq_zero
    simp only [Set.mem_preimage, Set.mem_setOf_eq, not_and_or, not_forall, not_le] at hcon
    rcases hcon with hcon | hcon
    · -- some r-coordinate exceeds 2 d0 : use the terminal acc r k^2 term OR a summed term.
      obtain ⟨j, hj⟩ := hcon
      -- We bound via acc r (j+1) = d.1.1 j and the summed term; but j : Fin k may = k-1
      -- so acc r (j+1) covers i = j+1 ∈ [1, k]. For i ≤ k-1 use the sum; for i = k use r k^2.
      by_cases hjk : (j : ℕ) + 1 ≤ k - 1
      · have hacc : acc d.1.1 (j + 1) = d.1.1 j := by
          rw [acc_val d.1.1 (j + 1) (by omega) (by have := j.2; omega)]; congr 1
        have hterm : (d.1.1 j) ^ 2 ≤ 2 * (acc d.1.1 (j + 1) ^ 2 + acc d.1.2 (j + 1) ^ 2
            - acc d.1.1 (j + 1) * acc d.1.2 (j + 1)) := by
          rw [hacc]; exact sq_le_two_mul_quad _ _
        have hmem : (j : ℕ) + 1 ∈ Icc 1 (k - 1) := by
          simp only [Finset.mem_Icc]; have := j.2; omega
        have hle : (acc d.1.1 (j + 1) ^ 2 + acc d.1.2 (j + 1) ^ 2
            - acc d.1.1 (j + 1) * acc d.1.2 (j + 1))
            ≤ ∑ i ∈ Icc 1 (k - 1), (acc d.1.1 i ^ 2 + acc d.1.2 i ^ 2 - acc d.1.1 i * acc d.1.2 i) := by
          apply Finset.single_le_sum
            (f := fun i => acc d.1.1 i ^ 2 + acc d.1.2 i ^ 2 - acc d.1.1 i * acc d.1.2 i)
            (fun i _ => Nat.zero_le _) hmem
        have hexp : ∑ i ∈ Icc 1 (k - 1), (acc d.1.1 i ^ 2 + acc d.1.2 i ^ 2 - acc d.1.1 i * acc d.1.2 i)
            ≤ expM k d.1.1 d.1.2 := by simp only [expM]; omega
        have : (2 * d0) ^ 2 < (d.1.1 j) ^ 2 := by apply Nat.pow_lt_pow_left hj; omega
        nlinarith [hterm, hle, hexp, this]
      · -- j+1 = k, so acc r k = d.1.1 j; use the leading r k^2 in expM
        have hjeq : (j : ℕ) + 1 = k := by have := j.2; omega
        have hacc : acc d.1.1 k = d.1.1 j := by
          rw [acc_val d.1.1 k (by omega) (by omega)]
          have hfe : (⟨k - 1, by omega⟩ : Fin k) = j := Fin.ext (by simp; omega)
          rw [hfe]
        have hexp : acc d.1.1 k ^ 2 ≤ expM k d.1.1 d.1.2 := by simp only [expM]; omega
        have : (2 * d0) ^ 2 < (d.1.1 j) ^ 2 := by apply Nat.pow_lt_pow_left hj; omega
        rw [hacc] at hexp
        nlinarith [hexp, this]
    · obtain ⟨j, hj⟩ := hcon
      have hacc : acc d.1.2 (j + 1) = d.1.2 j := by
        rw [acc_val d.1.2 (j + 1) (by omega) (by have := j.2; omega)]; congr 1
      have hterm : (d.1.2 j) ^ 2 ≤ 2 * (acc d.1.1 (j + 1) ^ 2 + acc d.1.2 (j + 1) ^ 2
          - acc d.1.1 (j + 1) * acc d.1.2 (j + 1)) := by
        have h2 := sq_le_two_mul_quad (acc d.1.2 (j+1)) (acc d.1.1 (j+1))
        rw [hacc] at h2 ⊢
        calc (d.1.2 j) ^ 2 ≤ 2 * (d.1.2 j ^ 2 + acc d.1.1 (j+1) ^ 2 - d.1.2 j * acc d.1.1 (j+1)) := h2
          _ = 2 * (acc d.1.1 (j+1) ^ 2 + d.1.2 j ^ 2 - acc d.1.1 (j+1) * d.1.2 j) := by ring_nf
      have hmem : (j : ℕ) + 1 ∈ Icc 1 (k - 1) := by
        simp only [Finset.mem_Icc]; have := j.2; omega
      have hle : (acc d.1.1 (j + 1) ^ 2 + acc d.1.2 (j + 1) ^ 2
          - acc d.1.1 (j + 1) * acc d.1.2 (j + 1))
          ≤ ∑ i ∈ Icc 1 (k - 1), (acc d.1.1 i ^ 2 + acc d.1.2 i ^ 2 - acc d.1.1 i * acc d.1.2 i) := by
        apply Finset.single_le_sum
          (f := fun i => acc d.1.1 i ^ 2 + acc d.1.2 i ^ 2 - acc d.1.1 i * acc d.1.2 i)
          (fun i _ => Nat.zero_le _) hmem
      have hexp : ∑ i ∈ Icc 1 (k - 1), (acc d.1.1 i ^ 2 + acc d.1.2 i ^ 2 - acc d.1.1 i * acc d.1.2 i)
          ≤ expM k d.1.1 d.1.2 := by simp only [expM]; omega
      have : (2 * d0) ^ 2 < (d.1.2 j) ^ 2 := by apply Nat.pow_lt_pow_left hj; omega
      nlinarith [hterm, hle, hexp, this]

lemma summable_outerM_fermBodyM (k : ℕ) :
    Summable (fun d : DomM k => outerM k d.1.1 * fermBodyM k d.1.1 d.1.2) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d0
  exact summable_of_finite_support (finite_support_coeff_fermMinus k d0)

/-- **`fermMinus` as an outer·body double t-sum over `{r//Antitone r} × (Fin (k-1)→ℕ)`.** -/
theorem fermMinus_eq_tsum_perR (k : ℕ) (hk : 2 ≤ k) (hPD : Fact8 3 (3 * k - 1)) :
    fermMinus k
      = ∑' r : { r : Fin k → ℕ // Antitone r }, outerM k r * (∑' m : Fin (k - 1) → ℕ, fermBodyM k r m) := by
  have hsummand : fermMinus k
      = ∑' d : DomM k, outerM k d.1.1 * fermBodyM k d.1.1 d.1.2 := by
    unfold fermMinus
    refine tsum_congr (fun d => ?_)
    simp only [outerM, outerP, fermBodyM]
    ring
  rw [hsummand]
  set e : DomM k ≃ { r : Fin k → ℕ // Antitone r } × (Fin (k - 1) → ℕ) :=
    Equiv.prodSubtypeFstEquivSubtypeProd (p := (Antitone : (Fin k → ℕ) → Prop)) with he
  have hsumm : Summable (fun d : DomM k => outerM k d.1.1 * fermBodyM k d.1.1 d.1.2) :=
    summable_outerM_fermBodyM k
  rw [← Equiv.tsum_eq e.symm (fun d : DomM k => outerM k d.1.1 * fermBodyM k d.1.1 d.1.2)]
  have hpt : ∀ p : { r : Fin k → ℕ // Antitone r } × (Fin (k - 1) → ℕ),
      outerM k (e.symm p).1.1 * fermBodyM k (e.symm p).1.1 (e.symm p).1.2
        = outerM k p.1 * fermBodyM k p.1 p.2 := by
    intro p; rfl
  rw [tsum_congr hpt]
  have hsumm' : Summable (fun p : { r : Fin k → ℕ // Antitone r } × (Fin (k - 1) → ℕ) =>
      outerM k p.1 * fermBodyM k p.1 p.2) := by
    have := (Equiv.summable_iff e.symm).2 hsumm
    refine this.congr ?_
    intro p; exact hpt p
  rw [hsumm'.tsum_prod']
  · refine tsum_congr (fun r => ?_)
    show ∑' c : Fin (k - 1) → ℕ, outerM k r * fermBodyM k r c = outerM k r * ∑' m, fermBodyM k r m
    exact (summable_fermBodyM k r).tsum_mul_left (outerM k r)
  · intro r
    exact ((Equiv.summable_iff e.symm).2 hsumm |>.congr (fun p => hpt p)).prod_factor r

/-- **Abstract content-slicing of a `Fin k → ℕ`-indexed `tsum`.** Reindex `∑' m : Fin k → ℕ` by
total content `M = ∑ᵢ mᵢ`; the content-`M` fibre is `Finset.Nat.antidiagonalTuple k M`. Stated for
an arbitrary summand `g` so the higher-order `tsum_sigma'` unification does not unfold `fermBodyP`
(which times out `whnf`). -/
lemma tsum_by_content_aux {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [T3Space A] (k : ℕ) (g : (Fin k → ℕ) → A) (hg : Summable g) :
    (∑' m : Fin k → ℕ, g m)
      = ∑' M : ℕ, ∑ m ∈ Finset.Nat.antidiagonalTuple k M, g m := by
  rw [← Equiv.tsum_eq (Finset.Nat.sigmaAntidiagonalTupleEquivTuple k) g]
  have hsumm : Summable (fun p : (M : ℕ) × ↥(Finset.Nat.antidiagonalTuple k M) =>
      g ((Finset.Nat.sigmaAntidiagonalTupleEquivTuple k) p)) :=
    (Equiv.summable_iff (Finset.Nat.sigmaAntidiagonalTupleEquivTuple k)).2 hg
  have h1 : ∀ M : ℕ, Summable (fun c : ↥(Finset.Nat.antidiagonalTuple k M) =>
      g ((Finset.Nat.sigmaAntidiagonalTupleEquivTuple k) ⟨M, c⟩)) :=
    fun _ => Summable.of_finite
  refine Eq.trans (Summable.tsum_sigma' h1 hsumm) ?_
  refine tsum_congr (fun M => ?_)
  rw [tsum_fintype]
  rw [← Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple k M) g]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  congr 1

/-- **Content-slicing of the fermionic `m`-sum (plus).** Reindex `∑' m : Fin k → ℕ` by the total
content `M = ∑ᵢ mᵢ`: the fibre of content `M` is `Finset.Nat.antidiagonalTuple k M`. Pure
summability/reindex (uses `summable_fermBodyP`); no opaque bodies. -/
lemma tsum_fermBodyP_by_content (k : ℕ) (r : Fin k → ℕ) :
    (∑' m : Fin k → ℕ, fermBodyP k r m)
      = ∑' M : ℕ, ∑ m ∈ Finset.Nat.antidiagonalTuple k M, fermBodyP k r m :=
  tsum_by_content_aux k (fun m => fermBodyP k r m) (summable_fermBodyP k r)

/-- **Content-slicing of the fermionic `m`-sum (minus).** Mirror over `Fin (k-1) → ℕ`. -/
lemma tsum_fermBodyM_by_content (k : ℕ) (r : Fin k → ℕ) :
    (∑' m : Fin (k - 1) → ℕ, fermBodyM k r m)
      = ∑' M : ℕ, ∑ m ∈ Finset.Nat.antidiagonalTuple (k - 1) M, fermBodyM k r m :=
  tsum_by_content_aux (k - 1) (fun m => fermBodyM k r m) (summable_fermBodyM k r)

/-! ### Layer 1 (plus): gap ↔ (r,a,z) coordinate equivalences (build plan Layer 1).

`gapEquiv k` splits `(finspan {3,3k+1}).gaps` into three `Fin k` blocks: `inl j ↦ z-gap`,
`inr (inl j) ↦ a-gap`, `inr (inr j) ↦ r-gap`.  These extract the three coordinate tuples from a
gap-vector `n`, and reassemble a gap-vector from `(r,a,z)`. -/

/-- `z`-coordinate tuple of a gap-vector: `zⱼ = n (gapEquiv k (inl j))`. -/
noncomputable def zOfGap (k : ℕ) (n : (finspan {3, 3 * k + 1}).gaps → ℕ) : Fin k → ℕ :=
  fun j => n (gapEquiv k (Sum.inl j))

/-- `a`-coordinate tuple: `aⱼ = n (gapEquiv k (inr (inl j)))`. -/
noncomputable def aOfGap (k : ℕ) (n : (finspan {3, 3 * k + 1}).gaps → ℕ) : Fin k → ℕ :=
  fun j => n (gapEquiv k (Sum.inr (Sum.inl j)))

/-- `r`-coordinate (boundary) tuple: `rⱼ = n (gapEquiv k (inr (inr j)))`. -/
noncomputable def rOfGap (k : ℕ) (n : (finspan {3, 3 * k + 1}).gaps → ℕ) : Fin k → ℕ :=
  fun j => n (gapEquiv k (Sum.inr (Sum.inr j)))

/-- Reassemble a gap-vector from `(r,a,z)` using `gapEquiv`'s inverse block structure. -/
noncomputable def gapOfAZ (k : ℕ) (r a z : Fin k → ℕ) : (finspan {3, 3 * k + 1}).gaps → ℕ :=
  fun g => match (gapEquiv k).symm g with
    | Sum.inl j => z j
    | Sum.inr (Sum.inl j) => a j
    | Sum.inr (Sum.inr j) => r j

lemma zOfGap_apply (k : ℕ) (n : (finspan {3, 3 * k + 1}).gaps → ℕ) (j : Fin k) :
    zOfGap k n j = n (gapEquiv k (Sum.inl j)) := rfl

lemma aOfGap_apply (k : ℕ) (n : (finspan {3, 3 * k + 1}).gaps → ℕ) (j : Fin k) :
    aOfGap k n j = n (gapEquiv k (Sum.inr (Sum.inl j))) := rfl

lemma rOfGap_apply (k : ℕ) (n : (finspan {3, 3 * k + 1}).gaps → ℕ) (j : Fin k) :
    rOfGap k n j = n (gapEquiv k (Sum.inr (Sum.inr j))) := rfl

lemma zOf_gapOfAZ (k : ℕ) (r a z : Fin k → ℕ) : zOfGap k (gapOfAZ k r a z) = z := by
  funext j
  rw [zOfGap_apply]
  show (match (gapEquiv k).symm (gapEquiv k (Sum.inl j)) with
    | Sum.inl j => z j
    | Sum.inr (Sum.inl j) => a j
    | Sum.inr (Sum.inr j) => r j) = z j
  rw [Equiv.symm_apply_apply]

lemma aOf_gapOfAZ (k : ℕ) (r a z : Fin k → ℕ) : aOfGap k (gapOfAZ k r a z) = a := by
  funext j
  rw [aOfGap_apply]
  show (match (gapEquiv k).symm (gapEquiv k (Sum.inr (Sum.inl j))) with
    | Sum.inl j => z j
    | Sum.inr (Sum.inl j) => a j
    | Sum.inr (Sum.inr j) => r j) = a j
  rw [Equiv.symm_apply_apply]

lemma rOf_gapOfAZ (k : ℕ) (r a z : Fin k → ℕ) : rOfGap k (gapOfAZ k r a z) = r := by
  funext j
  rw [rOfGap_apply]
  show (match (gapEquiv k).symm (gapEquiv k (Sum.inr (Sum.inr j))) with
    | Sum.inl j => z j
    | Sum.inr (Sum.inl j) => a j
    | Sum.inr (Sum.inr j) => r j) = r j
  rw [Equiv.symm_apply_apply]

lemma gapOfAZ_eta (k : ℕ) (n : (finspan {3, 3 * k + 1}).gaps → ℕ) :
    gapOfAZ k (rOfGap k n) (aOfGap k n) (zOfGap k n) = n := by
  funext g
  show (match (gapEquiv k).symm g with
    | Sum.inl j => zOfGap k n j
    | Sum.inr (Sum.inl j) => aOfGap k n j
    | Sum.inr (Sum.inr j) => rOfGap k n j) = n g
  rcases h : (gapEquiv k).symm g with j | (j | j)
  · dsimp only
    rw [zOfGap_apply, ← h, Equiv.apply_symm_apply]
  · dsimp only
    rw [aOfGap_apply, ← h, Equiv.apply_symm_apply]
  · dsimp only
    rw [rOfGap_apply, ← h, Equiv.apply_symm_apply]

/-- The fibre of `rOfGap = r` is equivalent to the pair of `(a,z)`-tuples: extract `(a,z)`,
reassemble with the fixed `r`. -/
noncomputable def fiberEquivAZ (k : ℕ) (r : Fin k → ℕ) :
    {n : (finspan {3, 3 * k + 1}).gaps → ℕ // rOfGap k n = r} ≃ ((Fin k → ℕ) × (Fin k → ℕ)) where
  toFun n := (aOfGap k n.1, zOfGap k n.1)
  invFun az := ⟨gapOfAZ k r az.1 az.2, rOf_gapOfAZ k r az.1 az.2⟩
  left_inv := by
    rintro ⟨n, hn⟩
    apply Subtype.ext
    simp only
    rw [← hn]
    exact gapOfAZ_eta k n
  right_inv := by
    rintro ⟨a, z⟩
    simp only [Prod.mk.injEq]
    exact ⟨aOf_gapOfAZ k r a z, zOf_gapOfAZ k r a z⟩


/-! ### Layer 2 (plus): opaque-body bridges for `lhsTerm` (build plan Layer 2).

The recovered body (verified via `#print`):
`lhsTerm k r G n = if (∀ j, extendNat n (6k-(3j+1)) = r j) then lhsTermInner k r G n else 0`
`lhsTermInner k r G n = (X^((Q' G 3 (3k+1) ↑n).toNat) · ∏_{j∈range k} qChoose X (extendNat n (3j+5)) (extendNat n (3j+2)))
                         · ∏_j extendedQChoose X (r j.rev - extendNat n (3j-2)) (extendNat n (3j+1) - extendNat n (3j-2))`.

These bridge lemmas relate the `ℕ[X]`-coerced `lhsTerm` (summed over gap-vectors) to the
`transfer`-image of the Laurent `T`-monomial `azFinset`/`Brs` sum that `stmt5_fixedBoundary_plus`
manipulates.  They are the input to Layer 3 (`sbPlus_eq_transfer` + `cor_perR_plus`). -/

/-- **Layer 2, support characterization (plus).** On a gap-vector `n`, the boundary `if`-condition
inside `lhsTerm` (`∀ j, extendNat n (6k-(3j+1)) = r j`) is exactly the fibre condition
`rOfGap k n = r`.  (`rOfGap k n j = n (gapEquiv k (inr (inr j)))` reads the r-block gap
`6k-1-3j`; matching Axiomlib's `6k-(3j+1)` index via `extendNat`.)  Proven from the explicit
`gapEquiv`/`gapSub` r-block description. -/
lemma lhsTerm_support_iff_domAZ_plus (k : ℕ) (hk : 1 ≤ k) (r : Fin k → ℕ)
    (n : (finspan {3, 3 * k + 1}).gaps → ℕ) :
    (∀ j : Fin k, HJO.extendNat n (6 * k - (3 * (j : ℕ) + 1)) = r j) ↔ rOfGap k n = r := by
  have key : ∀ j : Fin k, HJO.extendNat n (6 * k - (3 * (j : ℕ) + 1)) = rOfGap k n j := by
    intro j
    have hidx : 6 * k - (3 * (j : ℕ) + 1) = 6 * k - 1 - 3 * (j : ℕ) := by omega
    rw [rOfGap_apply]
    have hg : gapEquiv k (Sum.inr (Sum.inr j)) = ⟨6 * k - 1 - 3 * (j : ℕ), memR_plus k j⟩ := by
      simp only [gapEquiv, Equiv.ofBijective_apply]; rfl
    rw [hg, hidx]
    show HJO.extendNat n (6 * k - 1 - 3 * (j : ℕ)) = n ⟨6 * k - 1 - 3 * (j : ℕ), memR_plus k j⟩
    rw [HJO.extendNat]
    rw [dif_pos (memR_plus k j)]
  constructor
  · intro h
    funext j
    rw [← key j, h j]
  · intro h j
    rw [key j, h]

/-- `Brs r s a z` has nonnegative degree: it is a product of `qChoose qL` factors, each of which
lies in `LaurentNonneg`, and `LaurentNonneg` is a subsemiring. -/
lemma Brs_mem {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ) (a z : Fin ℓ → ℕ) :
    Brs r s a z ∈ LaurentNonneg := by
  unfold Brs
  apply Subsemiring.prod_mem
  intro i _
  exact LaurentNonneg.mul_mem (qChoose_qL_mem _ _) (qChoose_qL_mem _ _)

/-- Push `transfer` through a finite product all of whose factors lie in `LaurentNonneg`. -/
lemma transfer_prod_of_mem {ι : Type*} (S : Finset ι) (f : ι → LaurentPolynomial ℤ)
    (hf : ∀ i ∈ S, f i ∈ LaurentNonneg) :
    transfer (∏ i ∈ S, f i) = ∏ i ∈ S, transfer (f i) := by
  classical
  induction S using Finset.induction with
  | empty => simp only [Finset.prod_empty]; rw [show (1 : LaurentPolynomial ℤ) = T 0 by simp,
      show (0 : ℤ) = ((0 : ℕ) : ℤ) by simp, transfer_T]; simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hmem : ∀ i ∈ s, f i ∈ LaurentNonneg := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [transfer_mul_of_mem (hf a (Finset.mem_insert_self a s))
        (Subsemiring.prod_mem _ hmem), ih hmem]

/-- `transfer` of `Brs` is the corresponding `qChoose qX` product in `ℤ⟦X⟧`. -/
lemma transfer_Brs {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ) (a z : Fin ℓ → ℕ) :
    transfer (Brs r s a z)
      = ∏ i ∈ Icc 1 ℓ, qChoose qX (aacc s a (i - 1)) (acc a i)
          * qChoose qX (acc r i - acc z (i + 1)) (acc z i - acc z (i + 1)) := by
  unfold Brs
  rw [transfer_prod_of_mem _ _
    (fun i _ => LaurentNonneg.mul_mem (qChoose_qL_mem _ _) (qChoose_qL_mem _ _))]
  apply Finset.prod_congr rfl
  intro i _
  rw [transfer_mul_of_mem (qChoose_qL_mem _ _) (qChoose_qL_mem _ _),
    transfer_qChoose, transfer_qChoose]

/-- Successive `acc` of an antitone tuple decreases (1-indexed): `acc a (i+1) ≤ acc a i`. -/
lemma acc_succ_le {ν : ℕ} {a : Fin ν → ℕ} (ha : Antitone a) {i : ℕ} (hi : 1 ≤ i) :
    acc a (i + 1) ≤ acc a i := by
  by_cases hik : i + 1 ≤ ν
  · rw [acc_val a (i + 1) (by omega) hik, acc_val a i hi (by omega)]
    apply ha
    simp only [Fin.mk_le_mk]; omega
  · rw [acc_zero_of a (i + 1) (by omega)]; exact Nat.zero_le _

/-- Under `domAZ`, the plus-exponent `∑ᵢ rᵢ² + E⁺(a,z)` is nonnegative (it is the value of the
positive quadratic form `Q_{3,3k+1}` on the corresponding gap-vector; algebraically it is a
sum of squares once `z` is antitone and `zᵢ ≤ rᵢ`). -/
-- SANITY CHECK PASSED (300k random domAZ trials, min total = 0; per-term min = 0)
lemma azExp_nonneg (k : ℕ) (hk : 1 ≤ k) (r : Fin k → ℕ)
    (n : (finspan {3, 3 * k + 1}).gaps → ℕ)
    (hdom : domAZ r (acc r k) (aOfGap k n) (zOfGap k n)) :
    0 ≤ (∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2) + Eplus r (aOfGap k n) (zOfGap k n) := by
  obtain ⟨haa, _, _, hzr⟩ := hdom
  set a := aOfGap k n with ha
  set z := zOfGap k n with hz
  rw [Eplus, ← Finset.sum_add_distrib]
  apply Finset.sum_nonneg
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hZR : (acc z i : ℤ) ≤ (acc r i : ℤ) := by exact_mod_cast hzr i (Finset.mem_Icc.2 hi)
  have hApA : (acc a (i + 1) : ℤ) ≤ (acc a i : ℤ) := by exact_mod_cast acc_succ_le haa hi.1
  have hZnn : (0 : ℤ) ≤ (acc z i : ℤ) := Int.ofNat_nonneg _
  have hAnn : (0 : ℤ) ≤ (acc a i : ℤ) := Int.ofNat_nonneg _
  have hApnn : (0 : ℤ) ≤ (acc a (i + 1) : ℤ) := Int.ofNat_nonneg _
  nlinarith [sq_nonneg ((acc a (i + 1) : ℤ) - ((acc r i : ℤ) - (acc z i : ℤ))),
    mul_nonneg hApnn (sub_nonneg.2 hZR), mul_nonneg hApnn (sub_nonneg.2 hApA),
    mul_nonneg hZnn (sub_nonneg.2 hZR), mul_nonneg hZnn (sub_nonneg.2 hApA),
    mul_nonneg hAnn hZnn, mul_nonneg (sub_nonneg.2 hApA) hZnn]

/-- Generalized `azExp_nonneg`: from a raw `domAZ r s a z` (arbitrary `a z`), the plus-exponent
`∑ᵢ rᵢ² + E⁺(a,z)` is nonnegative. -/
lemma azExp_nonneg_gen {k : ℕ} (r : Fin k → ℕ) {s : ℕ} {a z : Fin k → ℕ}
    (hdom : domAZ r s a z) :
    0 ≤ (∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2) + Eplus r a z := by
  obtain ⟨haa, _, _, hzr⟩ := hdom
  rw [Eplus, ← Finset.sum_add_distrib]
  apply Finset.sum_nonneg
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hZR : (acc z i : ℤ) ≤ (acc r i : ℤ) := by exact_mod_cast hzr i (Finset.mem_Icc.2 hi)
  have hApA : (acc a (i + 1) : ℤ) ≤ (acc a i : ℤ) := by exact_mod_cast acc_succ_le haa hi.1
  have hZnn : (0 : ℤ) ≤ (acc z i : ℤ) := Int.ofNat_nonneg _
  have hAnn : (0 : ℤ) ≤ (acc a i : ℤ) := Int.ofNat_nonneg _
  have hApnn : (0 : ℤ) ≤ (acc a (i + 1) : ℤ) := Int.ofNat_nonneg _
  nlinarith [sq_nonneg ((acc a (i + 1) : ℤ) - ((acc r i : ℤ) - (acc z i : ℤ))),
    mul_nonneg hApnn (sub_nonneg.2 hZR), mul_nonneg hApnn (sub_nonneg.2 hApA),
    mul_nonneg hZnn (sub_nonneg.2 hZR), mul_nonneg hZnn (sub_nonneg.2 hApA),
    mul_nonneg hAnn hZnn, mul_nonneg (sub_nonneg.2 hApA) hZnn]

/-- The `azTransfer` argument `T(∑rᵢ² + Eplus) * Brs` lies in `LaurentNonneg` under `domAZ`. -/
lemma azTransfer_arg_mem {k : ℕ} (r : Fin k → ℕ) {s : ℕ} {a z : Fin k → ℕ}
    (hdom : domAZ r s a z) :
    (T ((∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2) + Eplus r a z) * Brs r s a z) ∈ LaurentNonneg := by
  have he0 : 0 ≤ (∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2) + Eplus r a z := azExp_nonneg_gen r hdom
  refine LaurentNonneg.mul_mem ?_ (Brs_mem _ _ _ _)
  rw [show ((∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2) + Eplus r a z)
        = ((((∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2) + Eplus r a z).toNat : ℤ)) from
      (Int.toNat_of_nonneg he0).symm]
  exact T_nat_mem _

/-- Coordinate reading: `extendNat n (3x+1) = acc (zOfGap k n) (k-x)` for `x < k`. -/
lemma extendNat_z_read (k : ℕ) (n : (finspan {3, 3 * k + 1}).gaps → ℕ) (x : ℕ) (hx : x < k) :
    HJO.extendNat n (3 * x + 1) = acc (zOfGap k n) (k - x) := by
  set j : Fin k := ⟨k - 1 - x, by omega⟩ with hj
  have hidx : 3 * x + 1 = 3 * (k - 1 - (j : ℕ)) + 1 := by simp only [hj]; omega
  rw [hidx, HJO.extendNat_of_mem (memZ_plus k j)]
  have hg : gapEquiv k (Sum.inl j) = ⟨3 * (k - 1 - (j : ℕ)) + 1, memZ_plus k j⟩ := by
    simp only [gapEquiv, Equiv.ofBijective_apply]; rfl
  rw [acc_val (zOfGap k n) (k - x) (by omega) (by omega), zOfGap_apply]
  apply congrArg n
  apply Subtype.ext
  simp only [gapEquiv, gapSub, Equiv.ofBijective_apply, hj]
  omega

/-- Coordinate reading: `extendNat n (3x+2) = acc (aOfGap k n) (k-x)` for `x < k`. -/
lemma extendNat_a_read (k : ℕ) (n : (finspan {3, 3 * k + 1}).gaps → ℕ) (x : ℕ) (hx : x < k) :
    HJO.extendNat n (3 * x + 2) = acc (aOfGap k n) (k - x) := by
  set j : Fin k := ⟨k - 1 - x, by omega⟩ with hj
  have hidx : 3 * x + 2 = 3 * (k - 1 - (j : ℕ)) + 2 := by simp only [hj]; omega
  rw [hidx, HJO.extendNat_of_mem (memA_plus k j)]
  have hg : gapEquiv k (Sum.inr (Sum.inl j)) = ⟨3 * (k - 1 - (j : ℕ)) + 2, memA_plus k j⟩ := by
    simp only [gapEquiv, Equiv.ofBijective_apply]; rfl
  rw [acc_val (aOfGap k n) (k - x) (by omega) (by omega), aOfGap_apply]
  apply congrArg n
  apply Subtype.ext
  simp only [gapEquiv, gapSub, Equiv.ofBijective_apply, hj]
  omega

/-- Coordinate reading: `extendNat n (3x-2) = acc (zOfGap k n) (k-x+1)` for `x < k`. -/
lemma extendNat_zshift_read (k : ℕ) (n : (finspan {3, 3 * k + 1}).gaps → ℕ) (x : ℕ) (hx : x < k) :
    HJO.extendNat n (3 * x - 2) = acc (zOfGap k n) (k - x + 1) := by
  rcases Nat.eq_zero_or_pos x with hx0 | hx0
  · subst hx0
    rw [show 3 * 0 - 2 = 0 from rfl, HJO.extendNat_gaps_zero,
      acc_zero_of (zOfGap k n) (k - 0 + 1) (by omega)]
  · have hidx : 3 * x - 2 = 3 * (x - 1) + 1 := by omega
    rw [hidx, extendNat_z_read k n (x - 1) (by omega), show k - (x - 1) = k - x + 1 by omega]

/-- Coordinate reading: `extendNat n (3x-1) = acc (aOfGap k n) (k-x+1)` for `x < k`. -/
lemma extendNat_ashift_down_read (k : ℕ) (n : (finspan {3, 3 * k + 1}).gaps → ℕ) (x : ℕ) (hx : x < k) :
    HJO.extendNat n (3 * x - 1) = acc (aOfGap k n) (k - x + 1) := by
  rcases Nat.eq_zero_or_pos x with hx0 | hx0
  · subst hx0
    rw [show 3 * 0 - 1 = 0 from rfl, HJO.extendNat_gaps_zero,
      acc_zero_of (aOfGap k n) (k - 0 + 1) (by omega)]
  · have hidx : 3 * x - 1 = 3 * (x - 1) + 2 := by omega
    rw [hidx, extendNat_a_read k n (x - 1) (by omega), show k - (x - 1) = k - x + 1 by omega]

/-- Coordinate reading: `extendNat n (3x+5) = aacc (acc r k) (aOfGap k n) (k-x-1)` for `x < k`. -/
lemma extendNat_ashift_read (k : ℕ) (r : Fin k → ℕ) (n : (finspan {3, 3 * k + 1}).gaps → ℕ)
    (hn : rOfGap k n = r) (x : ℕ) (hx : x < k) :
    HJO.extendNat n (3 * x + 5) = aacc (acc r k) (aOfGap k n) (k - x - 1) := by
  rcases Nat.lt_or_ge x (k - 1) with hlt | hge
  · have hidx : 3 * x + 5 = 3 * (x + 1) + 2 := by omega
    rw [hidx, extendNat_a_read k n (x + 1) (by omega), aacc, if_neg (by omega),
      show k - (x + 1) = k - x - 1 by omega]
  · have hxk : x = k - 1 := by omega
    subst hxk
    rw [aacc, if_pos (by omega)]
    set j : Fin k := ⟨k - 1, by omega⟩ with hj
    have hidx : 3 * (k - 1) + 5 = 6 * k - 1 - 3 * (j : ℕ) := by simp only [hj]; omega
    rw [hidx, HJO.extendNat_of_mem (memR_plus k j)]
    have hg : gapEquiv k (Sum.inr (Sum.inr j)) = ⟨6 * k - 1 - 3 * (j : ℕ), memR_plus k j⟩ := by
      simp only [gapEquiv, Equiv.ofBijective_apply]; rfl
    rw [acc_val r k (by omega) (by omega), ← hn, rOfGap_apply]
    apply congrArg n
    apply Subtype.ext
    simp only [gapEquiv, gapSub, Equiv.ofBijective_apply, hj]

/-- Coordinate reading: `r x.rev = acc r (k - ↑x)` for `x : Fin k`. -/
lemma r_rev_read (k : ℕ) (r : Fin k → ℕ) (x : Fin k) :
    r x.rev = acc r (k - (x : ℕ)) := by
  rw [acc_val r (k - (x : ℕ)) (by have := x.2; omega) (by omega)]
  congr 1

/-- Reindex a product over `Fin k` (through `x ↦ k - x`) to a product over `Icc 1 k`. -/
lemma prod_fin_eq_Icc {M : Type*} [CommMonoid M] (k : ℕ) (hk : 1 ≤ k) (g : ℕ → M) :
    (∏ x : Fin k, g (k - (x : ℕ))) = ∏ i ∈ Icc 1 k, g i := by
  rw [Fin.prod_univ_eq_prod_range (fun x => g (k - x)) k]
  refine Finset.prod_nbij' (fun x : ℕ => k - x) (fun i : ℕ => k - i) ?_ ?_ ?_ ?_ ?_
  · intro x hx; simp only [Finset.mem_range, Finset.mem_Icc] at *; omega
  · intro i hi; simp only [Finset.mem_range, Finset.mem_Icc] at *; omega
  · intro x hx; simp only [Finset.mem_range] at hx; omega
  · intro i hi; simp only [Finset.mem_Icc] at hi; omega
  · intro x hx; rfl

/-- Exponent match: `Q'` on the coerced gap-vector equals the Laurent exponent
`e = Σ (acc r i)² + E⁺(a,z)` (as naturals via `.toNat`). -/
lemma lhs_exp_eq (k : ℕ) (hk : 1 ≤ k) (r : Fin k → ℕ)
    (n : (finspan {3, 3 * k + 1}).gaps → ℕ) (hn : rOfGap k n = r)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) :
    ((HJO.Q' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1)) fun x => ↑(n x)).toNat
      = ((∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2)
          + Eplus r (aOfGap k n) (zOfGap k n)).toNat := by
  congr 1
  have hQ : (HJO.Q 3 (3 * k + 1)) (fun x => (↑(n x) : ℤ))
      = (∑ j : Fin k, (rOfGap k n j : ℤ) ^ 2)
          + Eplus (rOfGap k n) (aOfGap k n) (zOfGap k n) := by
    apply stmt_reindexEq_plus (Stil := Stil) (Tset := Tset) (invStat := invStat)
      k hk (fun x => (↑(n x) : ℤ)) (rOfGap k n) (aOfGap k n) (zOfGap k n)
    · intro j h
      rw [zOfGap_apply]; norm_cast
    · intro j h
      rw [aOfGap_apply]; norm_cast
    · intro j h
      rw [rOfGap_apply]; norm_cast
    · exact hRC
    · exact hInv
  rw [show (HJO.Q' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1)) (fun x => (↑(n x) : ℤ))
        = (HJO.Q 3 (3 * k + 1)) (fun x => (↑(n x) : ℤ)) from rfl, hQ, hn]
  congr 1
  rw [← sum_fin_eq_Icc (fun i => (acc r i : ℤ) ^ 2)]
  apply Finset.sum_congr rfl
  intro x _
  rw [acc_val r ((x : ℕ) + 1) (by omega) (by have := x.2; omega)]
  simp

/-- Product-1 match (`a`-block of `Brs`), stated through the coercion ring hom `Φ`. -/
lemma lhs_prod1_eq (k : ℕ) (hk : 1 ≤ k) (r : Fin k → ℕ)
    (n : (finspan {3, 3 * k + 1}).gaps → ℕ)
    (hn : rOfGap k n = r) (Φ : Polynomial ℕ →+* ℤ⟦X⟧)
    (hΦqc : ∀ (a b : ℕ), Φ (qChoose Polynomial.X a b) = qChoose qX a b) :
    (∏ x ∈ Finset.range k,
        Φ (qChoose Polynomial.X (HJO.extendNat n (3 * x + 5)) (HJO.extendNat n (3 * x + 2))))
      = ∏ i ∈ Icc 1 k,
          qChoose qX (aacc (acc r k) (aOfGap k n) (i - 1)) (acc (aOfGap k n) i) := by
  rw [Finset.prod_nbij' (fun x => k - x) (fun i => k - i)]
  · intro x hx; simp only [Finset.mem_range, Finset.mem_Icc] at *; omega
  · intro i hi; simp only [Finset.mem_range, Finset.mem_Icc] at *; omega
  · intro x hx; simp only [Finset.mem_range] at hx; omega
  · intro i hi; simp only [Finset.mem_Icc] at hi; omega
  · intro x hx
    simp only [Finset.mem_range] at hx
    rw [hΦqc, extendNat_ashift_read k r n hn x hx, extendNat_a_read k n x hx]

/-- Product-2 match (`z`-block of `Brs`), stated through the coercion ring hom `Φ`. Uses
`domAZ` to reduce each `extendedQChoose` to `qChoose` (nonnegative arguments). -/
lemma lhs_prod2_eq (k : ℕ) (hk : 1 ≤ k) (r : Fin k → ℕ) (hr : Antitone r)
    (n : (finspan {3, 3 * k + 1}).gaps → ℕ) (hn : rOfGap k n = r)
    (hdom : domAZ r (acc r k) (aOfGap k n) (zOfGap k n))
    (Φ : Polynomial ℕ →+* ℤ⟦X⟧)
    (hΦqc : ∀ (a b : ℕ), Φ (qChoose Polynomial.X a b) = qChoose qX a b) :
    (∏ x : Fin k,
        Φ (HJO.SumToSum.extendedQChoose Polynomial.X
            (↑(r x.rev) - ↑(HJO.extendNat n (3 * (x : ℕ) - 2)))
            (↑(HJO.extendNat n (3 * (x : ℕ) + 1)) - ↑(HJO.extendNat n (3 * (x : ℕ) - 2)))))
      = ∏ i ∈ Icc 1 k,
          qChoose qX (acc r i - acc (zOfGap k n) (i + 1))
            (acc (zOfGap k n) i - acc (zOfGap k n) (i + 1)) := by
  obtain ⟨_, _, hzAnti, hzr⟩ := hdom
  set z := zOfGap k n with hz
  have hfactor : ∀ x : Fin k,
      Φ (HJO.SumToSum.extendedQChoose Polynomial.X
          (↑(r x.rev) - ↑(HJO.extendNat n (3 * (x : ℕ) - 2)))
          (↑(HJO.extendNat n (3 * (x : ℕ) + 1)) - ↑(HJO.extendNat n (3 * (x : ℕ) - 2))))
        = qChoose qX (acc r (k - (x : ℕ)) - acc z (k - (x : ℕ) + 1))
            (acc z (k - (x : ℕ)) - acc z (k - (x : ℕ) + 1)) := by
    intro x
    have hxk : (x : ℕ) < k := x.2
    rw [r_rev_read k r x, extendNat_zshift_read k n x hxk, extendNat_z_read k n x hxk]
    have hi : (k - (x : ℕ)) ∈ Icc 1 k := by simp only [Finset.mem_Icc]; omega
    have hzr' : acc z (k - (x : ℕ)) ≤ acc r (k - (x : ℕ)) := by
      have := hzr (k - (x : ℕ)) hi; simpa [hz] using this
    have hzshift : acc z (k - (x : ℕ) + 1) ≤ acc z (k - (x : ℕ)) := by
      have : acc (zOfGap k n) (k - (x : ℕ) + 1) ≤ acc (zOfGap k n) (k - (x : ℕ)) :=
        acc_succ_le hzAnti (by omega)
      simpa [hz] using this
    have h1 : (0 : ℤ) ≤ (↑(acc r (k - (x : ℕ))) : ℤ) - ↑(acc z (k - (x : ℕ) + 1)) := by
      have hle : acc z (k - (x : ℕ) + 1) ≤ acc r (k - (x : ℕ)) := le_trans hzshift hzr'
      have := (Nat.cast_le (α := ℤ)).2 hle; omega
    have h2 : (0 : ℤ) ≤ (↑(acc z (k - (x : ℕ))) : ℤ) - ↑(acc z (k - (x : ℕ) + 1)) := by
      have := (Nat.cast_le (α := ℤ)).2 hzshift; omega
    rw [HJO.SumToSum.extendedQChoose_of_nonneg h1 h2,
      show ((↑(acc r (k - (x : ℕ))) : ℤ) - ↑(acc z (k - (x : ℕ) + 1))).toNat
        = acc r (k - (x : ℕ)) - acc z (k - (x : ℕ) + 1) from Int.toNat_sub _ _,
      show ((↑(acc z (k - (x : ℕ))) : ℤ) - ↑(acc z (k - (x : ℕ) + 1))).toNat
        = acc z (k - (x : ℕ)) - acc z (k - (x : ℕ) + 1) from Int.toNat_sub _ _,
      hΦqc]
  rw [Finset.prod_congr rfl (fun x _ => hfactor x)]
  exact prod_fin_eq_Icc k hk
    (fun i => qChoose qX (acc r i - acc z (i + 1)) (acc z i - acc z (i + 1)))

/-- **Layer 2, per-term transfer identity (plus).** For a gap-vector `n` in the support fibre
(`rOfGap k n = r`) with `(a,z) = (aOfGap k n, zOfGap k n)` in the domain `domAZ`, the `ℕ→ℤ`
coerced Axiomlib `lhsTermInner` equals the `transfer` of the Laurent `T`-monomial term
`T (∑ᵢ rᵢ² + Eplus r a z) · Brs r (acc r k) a z`.

The exponent identity is `stmt_reindexEq_plus` (Q collapses to `Σrⱼ² + Eplus r a z`); the
Gaussian product matches `Brs` after re-reading the gap indices as `(a,z)` via `gapEquiv`;
`transfer_qChoose`/`transfer_mul_of_mem`/`transfer_T` push `transfer` through.

NB: the `domAZ` hypothesis is essential — without it the coerced `lhsTerm` can vanish (an
`extendedQChoose` with a negative second argument) while `Brs` (ℕ-truncated subtraction) does
not; see node-8 CONTEXT.md counterexample (k=2, r=![10,10], z=![3,5]). -/
lemma lhsTerm_eq_transfer_azTerm_plus (k : ℕ) (hk : 1 ≤ k) (r : Fin k → ℕ) (hr : Antitone r)
    (n : (finspan {3, 3 * k + 1}).gaps → ℕ) (hn : rOfGap k n = r)
    (hdom : domAZ r (acc r k) (aOfGap k n) (zOfGap k n))
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) :
    ((Polynomial.map (Nat.castRingHom ℤ)
        (HJO.SumToSum.ThreeOne.lhsTerm k r (finspan {3, 3 * k + 1}).gaps n)).toPowerSeries)
      = transfer (T ((∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2) + Eplus r (aOfGap k n) (zOfGap k n))
          * Brs r (acc r k) (aOfGap k n) (zOfGap k n)) := by
  set a := aOfGap k n with ha
  set z := zOfGap k n with hz
  set e : ℤ := (∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2) + Eplus r a z with he
  -- RHS: push `transfer` through the product `T e * Brs`, using `e ≥ 0` (so `T e = T ↑e.toNat`).
  have he0 : 0 ≤ e := azExp_nonneg k hk r n hdom
  have heT : (T e : LaurentPolynomial ℤ) = T ((e.toNat : ℤ)) := by
    rw [Int.toNat_of_nonneg he0]
  have hRHS : transfer (T e * Brs r (acc r k) a z)
      = (X : ℤ⟦X⟧) ^ e.toNat
        * ∏ i ∈ Icc 1 k, qChoose qX (aacc (acc r k) a (i - 1)) (acc a i)
            * qChoose qX (acc r i - acc z (i + 1)) (acc z i - acc z (i + 1)) := by
    rw [transfer_mul_of_mem (by rw [heT]; exact T_nat_mem _) (Brs_mem _ _ _ _),
      heT, transfer_T, transfer_Brs]
  rw [hRHS]
  -- LHS: expand `lhsTerm` (support fibre) and push the coercion ring hom through.
  -- Step 1: the support `if`-condition holds (from `hn : rOfGap k n = r`).
  have hcond : (∀ j : Fin k, HJO.extendNat n (6 * k - (3 * (j : ℕ) + 1)) = r j) := by
    rw [lhsTerm_support_iff_domAZ_plus k hk r n]; exact hn
  rw [HJO.SumToSum.ThreeOne.lhsTerm, if_pos hcond, HJO.SumToSum.ThreeOne.lhsTermInner]
  -- Step 2: push the ring hom `Φ = (·.toPowerSeries) ∘ (Polynomial.map (Nat.castRingHom ℤ))`.
  set Φ : Polynomial ℕ →+* ℤ⟦X⟧ :=
    (Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.mapRingHom (Nat.castRingHom ℤ)) with hΦ
  have hΦX : Φ Polynomial.X = (X : ℤ⟦X⟧) := by
    simp only [hΦ, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
  have hΦqc : ∀ (a b : ℕ), Φ (qChoose Polynomial.X a b) = qChoose qX a b := by
    intro a b; rw [qChoose_ringHom_map Φ Polynomial.X a b, hΦX]
  have hlhs : ((Polynomial.map (Nat.castRingHom ℤ)
        ((Polynomial.X ^ ((HJO.Q' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1)) fun x => ↑(n x)).toNat
              * ∏ j ∈ Finset.range k, qChoose Polynomial.X (HJO.extendNat n (3 * j + 5)) (HJO.extendNat n (3 * j + 2)))
            * ∏ j : Fin k, HJO.SumToSum.extendedQChoose Polynomial.X (↑(r j.rev) - ↑(HJO.extendNat n (3 * (j:ℕ) - 2)))
                (↑(HJO.extendNat n (3 * (j:ℕ) + 1)) - ↑(HJO.extendNat n (3 * (j:ℕ) - 2))))).toPowerSeries : ℤ⟦X⟧)
      = Φ ((Polynomial.X ^ ((HJO.Q' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1)) fun x => ↑(n x)).toNat
              * ∏ j ∈ Finset.range k, qChoose Polynomial.X (HJO.extendNat n (3 * j + 5)) (HJO.extendNat n (3 * j + 2)))
            * ∏ j : Fin k, HJO.SumToSum.extendedQChoose Polynomial.X (↑(r j.rev) - ↑(HJO.extendNat n (3 * (j:ℕ) - 2)))
                (↑(HJO.extendNat n (3 * (j:ℕ) + 1)) - ↑(HJO.extendNat n (3 * (j:ℕ) - 2)))) := by
    rfl
  rw [hlhs]
  rw [map_mul, map_mul, map_pow, hΦX, map_prod, map_prod]
  rw [lhs_exp_eq (Stil := Stil) (Tset := Tset) (invStat := invStat) k hk r n hn hRC hInv,
    lhs_prod1_eq k hk r n hn Φ hΦqc,
    lhs_prod2_eq k hk r hr n hn hdom Φ hΦqc]
  rw [← ha, ← hz, ← he]
  rw [Finset.prod_mul_distrib]
  ring

/-- **Layer 3a.** Push `transfer` through a finite SUM all of whose summands lie in
`LaurentNonneg` (mirror of `transfer_prod_of_mem`). -/
lemma transfer_sum_of_mem {ι : Type*} (S : Finset ι) (f : ι → LaurentPolynomial ℤ)
    (hf : ∀ i ∈ S, f i ∈ LaurentNonneg) :
    transfer (∑ i ∈ S, f i) = ∑ i ∈ S, transfer (f i) := by
  classical
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    rw [show (0 : LaurentPolynomial ℤ) = (0 : Polynomial ℤ).toLaurent by simp,
      transfer_toLaurent, map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hmem : ∀ i ∈ s, f i ∈ LaurentNonneg := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [transfer_add_of_mem (hf a (Finset.mem_insert_self a s))
        (Subsemiring.sum_mem _ hmem), ih hmem]

/-- **Layer 3b (content lemma, plus).** For a fixed content `M`, the `transfer`-image of the
`T`-monomial `azFinset`/`Brs` sum (with the `q^{Σrᵢ²}` prefactor) equals the finite fermionic
`m`-sum at content `M`.  This is `stmt5_fixedBoundary_plus` transported termwise through
`transfer` (`transfer_T`, `transfer_qChoose`, `transfer_prod_of_mem`). -/
lemma azContent_eq_fermBody_finset (k : ℕ) (hk : 1 ≤ k) (r : Fin k → ℕ) (hr : Antitone r) (M : ℕ)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) (hSym : Fact3 Stil) (hRecip : Fact5)
    (hQbin : Fact6) (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    transfer (T (∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2)
        * (∑ az ∈ azFinset r (acc r k) M, T (Eplus r az.1 az.2) * Brs r (acc r k) az.1 az.2))
      = ∑ m ∈ Finset.Nat.antidiagonalTuple k M, fermBodyP k r m := by
  rw [stmt5_fixedBoundary_plus_aux Stil Tset invStat tabOf Ja Jz k hk r hr M
      hRC hInv hSym hRecip hQbin hInvComp]
  -- Now transfer the fermionic `m`-sum termwise.
  rw [transfer_sum_of_mem]
  · apply Finset.sum_congr rfl
    intro m hm
    -- Exponent identity: ∑(rᵢ²-rᵢmᵢ+mᵢ²) (ℤ) = cast of ∑(rᵢ²+mᵢ²-rᵢmᵢ) (ℕ).
    have hexp : (∑ i ∈ Icc 1 k, ((acc r i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ) + (acc m i : ℤ) ^ 2))
        = ((∑ i ∈ Icc 1 k, (acc r i ^ 2 + acc m i ^ 2 - acc r i * acc m i) : ℕ) : ℤ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      have hle : acc r i * acc m i ≤ acc r i ^ 2 + acc m i ^ 2 := by
        nlinarith [Nat.zero_le (acc r i * acc m i), sq_nonneg ((acc r i : ℤ) - (acc m i : ℤ))]
      rw [Nat.cast_sub hle]
      push_cast
      ring
    -- The `T`-monomial exponent is nonnegative, so its `transfer` is `X^(…)`.
    have hTmem : T (∑ i ∈ Icc 1 k, ((acc r i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ) + (acc m i : ℤ) ^ 2))
        ∈ LaurentNonneg := by rw [hexp]; exact T_nat_mem _
    rw [transfer_mul_of_mem (LaurentNonneg.mul_mem hTmem (qChoose_qL_mem _ _))
        (Subsemiring.prod_mem _ (fun i _ => qChoose_qL_mem _ _))]
    rw [transfer_mul_of_mem hTmem (qChoose_qL_mem _ _)]
    rw [hexp, transfer_T, transfer_qChoose,
        transfer_prod_of_mem _ _ (fun i _ => qChoose_qL_mem _ _)]
    simp only [transfer_qChoose]
    rw [fermBodyP]
  · intro m hm
    have hTmem : T (∑ i ∈ Icc 1 k, ((acc r i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ) + (acc m i : ℤ) ^ 2))
        ∈ LaurentNonneg := by
      have hthis : (∑ i ∈ Icc 1 k, ((acc r i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ) + (acc m i : ℤ) ^ 2))
          = ((∑ i ∈ Icc 1 k, (acc r i ^ 2 + acc m i ^ 2 - acc r i * acc m i) : ℕ) : ℤ) := by
        push_cast
        apply Finset.sum_congr rfl
        intro i _
        have hle : acc r i * acc m i ≤ acc r i ^ 2 + acc m i ^ 2 := by
          nlinarith [Nat.zero_le (acc r i * acc m i), sq_nonneg ((acc r i : ℤ) - (acc m i : ℤ))]
        rw [Nat.cast_sub hle]; push_cast; ring
      rw [hthis]; exact T_nat_mem _
    exact LaurentNonneg.mul_mem
      (LaurentNonneg.mul_mem hTmem (qChoose_qL_mem _ _))
      (Subsemiring.prod_mem _ (fun i _ => qChoose_qL_mem _ _))

/-- The `(a,z)`-transfer summand: the `ℤ⟦X⟧` image of the Laurent `T`-monomial term at `(a,z)`. -/
noncomputable def azTransfer (k : ℕ) (r : Fin k → ℕ)
    (az : (Fin k → ℕ) × (Fin k → ℕ)) : ℤ⟦X⟧ :=
  transfer (T ((∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2) + Eplus r az.1 az.2)
    * Brs r (acc r k) az.1 az.2)

/-- If a tuple `t : Fin ν → ℕ` is not antitone, there is an index `i` (1-indexed) with
`acc t i < acc t (i+1)`. -/
lemma not_antitone_acc_succ {ν : ℕ} {t : Fin ν → ℕ} (h : ¬ Antitone t) :
    ∃ i, 1 ≤ i ∧ i + 1 ≤ ν ∧ acc t i < acc t (i + 1) := by
  match ν, t, h with
  | 0, t, h => exact absurd (Subsingleton.antitone t) h
  | 1, t, h => exact absurd (Subsingleton.antitone t) h
  | (m + 2), t, h =>
    rw [Fin.antitone_iff_succ_le] at h
    push_neg at h
    obtain ⟨i, hi⟩ := h
    refine ⟨(i : ℕ) + 1, by omega, by have := i.2; omega, ?_⟩
    rw [acc_val t ((i : ℕ) + 1) (by omega) (by have := i.2; omega),
        acc_val t ((i : ℕ) + 1 + 1) (by omega) (by have := i.2; omega)]
    have e1 : (⟨(i : ℕ) + 1 - 1, by have := i.2; omega⟩ : Fin (m + 2)) = i.castSucc := by
      apply Fin.ext; simp
    have e2 : (⟨(i : ℕ) + 1 + 1 - 1, by have := i.2; omega⟩ : Fin (m + 2)) = i.succ := by
      apply Fin.ext; simp
    rw [e1, e2]
    omega

/-- **(A)** Off the `domAZ` domain (but still in the fibre `rOfGap = r`), the coerced `lhsTerm`
vanishes: some `extendedQChoose` acquires a negative second argument. -/
lemma lhsTerm_vanish_of_not_domAZ (k : ℕ) (hk : 1 ≤ k) (r : Fin k → ℕ) (hr : Antitone r)
    (n : (finspan {3, 3 * k + 1}).gaps → ℕ) (hn : rOfGap k n = r)
    (hdom : ¬ domAZ r (acc r k) (aOfGap k n) (zOfGap k n)) :
    ((Polynomial.map (Nat.castRingHom ℤ)
        (HJO.SumToSum.ThreeOne.lhsTerm k r (finspan {3, 3 * k + 1}).gaps n)).toPowerSeries)
      = (0 : ℤ⟦X⟧) := by
  set a := aOfGap k n with ha
  set z := zOfGap k n with hz
  -- LHS: expand `lhsTerm` (support fibre) and push the coercion ring hom through.
  have hcond : (∀ j : Fin k, HJO.extendNat n (6 * k - (3 * (j : ℕ) + 1)) = r j) := by
    rw [lhsTerm_support_iff_domAZ_plus k hk r n]; exact hn
  rw [HJO.SumToSum.ThreeOne.lhsTerm, if_pos hcond, HJO.SumToSum.ThreeOne.lhsTermInner]
  set Φ : Polynomial ℕ →+* ℤ⟦X⟧ :=
    (Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.mapRingHom (Nat.castRingHom ℤ)) with hΦ
  have hΦX : Φ Polynomial.X = (X : ℤ⟦X⟧) := by
    simp only [hΦ, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
  have hΦqc : ∀ (a b : ℕ), Φ (qChoose Polynomial.X a b) = qChoose qX a b := by
    intro a b; rw [qChoose_ringHom_map Φ Polynomial.X a b, hΦX]
  have hlhs : ((Polynomial.map (Nat.castRingHom ℤ)
        ((Polynomial.X ^ ((HJO.Q' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1)) fun x => ↑(n x)).toNat
              * ∏ j ∈ Finset.range k, qChoose Polynomial.X (HJO.extendNat n (3 * j + 5)) (HJO.extendNat n (3 * j + 2)))
            * ∏ j : Fin k, HJO.SumToSum.extendedQChoose Polynomial.X (↑(r j.rev) - ↑(HJO.extendNat n (3 * (j:ℕ) - 2)))
                (↑(HJO.extendNat n (3 * (j:ℕ) + 1)) - ↑(HJO.extendNat n (3 * (j:ℕ) - 2))))).toPowerSeries : ℤ⟦X⟧)
      = Φ ((Polynomial.X ^ ((HJO.Q' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1)) fun x => ↑(n x)).toNat
              * ∏ j ∈ Finset.range k, qChoose Polynomial.X (HJO.extendNat n (3 * j + 5)) (HJO.extendNat n (3 * j + 2)))
            * ∏ j : Fin k, HJO.SumToSum.extendedQChoose Polynomial.X (↑(r j.rev) - ↑(HJO.extendNat n (3 * (j:ℕ) - 2)))
                (↑(HJO.extendNat n (3 * (j:ℕ) + 1)) - ↑(HJO.extendNat n (3 * (j:ℕ) - 2)))) := by
    rfl
  rw [hlhs]
  rw [map_mul, map_mul, map_pow, hΦX, map_prod, map_prod]
  rw [lhs_prod1_eq k hk r n hn Φ hΦqc]
  -- Now goal: X^exp * (∏ i∈Icc 1 k, qChoose qX (aacc (acc r k) a (i-1)) (acc a i))
  --   * (∏ x:Fin k, Φ(extendedQChoose X (↑(r x.rev)-↑(extendNat n (3x-2))) (↑(extendNat n (3x+1))-↑(extendNat n (3x-2))))) = 0
  -- Kill via one vanishing product factor. Case-split on domAZ conjuncts.
  by_cases hAa : Antitone a
  · by_cases hs : acc a 1 ≤ acc r k
    · by_cases hAz : Antitone z
      · -- The 4th conjunct must fail
        have hd4 : ¬ (∀ i ∈ Icc 1 k, acc z i ≤ acc r i) := by
          intro h4; exact hdom ⟨hAa, hs, hAz, h4⟩
        push_neg at hd4
        obtain ⟨i, hi, hlt⟩ := hd4  -- acc r i < acc z i
        simp only [Finset.mem_Icc] at hi
        -- prod2 vanishes at x with k - x = i, i.e. x = k - i
        have hxlt : k - i < k := by omega
        set x : Fin k := ⟨k - i, hxlt⟩ with hxdef
        have hkx : k - (x : ℕ) = i := by simp only [hxdef]; omega
        have hfac0 : Φ (HJO.SumToSum.extendedQChoose Polynomial.X
              (↑(r x.rev) - ↑(HJO.extendNat n (3 * (x : ℕ) - 2)))
              (↑(HJO.extendNat n (3 * (x : ℕ) + 1)) - ↑(HJO.extendNat n (3 * (x : ℕ) - 2)))) = 0 := by
          have hxk : (x : ℕ) < k := x.2
          rw [r_rev_read k r x, extendNat_zshift_read k n x hxk, extendNat_z_read k n x hxk, hkx,
            ← hz]
          have hez : (HJO.SumToSum.extendedQChoose (Polynomial.X : Polynomial ℕ)
              (↑(acc r i) - ↑(acc z (i + 1))) (↑(acc z i) - ↑(acc z (i + 1)))) = 0 := by
            by_contra hne
            have := (HJO.SumToSum.extendedQChoose_X_ne_zero_iff (R := ℕ)).1 hne
            have hle := this.2  -- (↑(acc z i) - ↑(acc z (i+1))) ≤ (↑(acc r i) - ↑(acc z (i+1)))
            have : (acc z i : ℤ) ≤ acc r i := by omega
            have : acc z i ≤ acc r i := by exact_mod_cast this
            omega
          rw [hez, map_zero]
        rw [Finset.prod_eq_zero (Finset.mem_univ x) hfac0]
        ring
      · -- ¬ Antitone z : prod2 vanishes (second arg negative)
        obtain ⟨i, hi1, hik, hlt⟩ := not_antitone_acc_succ hAz  -- acc z i < acc z (i+1)
        have hxlt : k - i < k := by omega
        set x : Fin k := ⟨k - i, hxlt⟩ with hxdef
        have hkx : k - (x : ℕ) = i := by simp only [hxdef]; omega
        have hfac0 : Φ (HJO.SumToSum.extendedQChoose Polynomial.X
              (↑(r x.rev) - ↑(HJO.extendNat n (3 * (x : ℕ) - 2)))
              (↑(HJO.extendNat n (3 * (x : ℕ) + 1)) - ↑(HJO.extendNat n (3 * (x : ℕ) - 2)))) = 0 := by
          have hxk : (x : ℕ) < k := x.2
          rw [r_rev_read k r x, extendNat_zshift_read k n x hxk, extendNat_z_read k n x hxk, hkx,
            ← hz]
          have hneg : (↑(acc z i) : ℤ) - ↑(acc z (i + 1)) < 0 := by
            have := (Nat.cast_lt (α := ℤ)).2 hlt; omega
          rw [HJO.SumToSum.extendedQChoose_of_neg_left (Or.inr hneg), map_zero]
        rw [Finset.prod_eq_zero (Finset.mem_univ x) hfac0]
        ring
    · -- ¬ (acc a 1 ≤ acc r k) : prod1 vanishes at i = 1
      have hlt : acc r k < acc a 1 := not_le.mp hs
      have hfac0 : qChoose qX (aacc (acc r k) a (1 - 1)) (acc a 1) = 0 := by
        rw [show (1 : ℕ) - 1 = 0 from rfl, aacc, if_pos rfl]
        exact qChoose_eq_zero_of_lt hlt
      have hmem : (1 : ℕ) ∈ Icc 1 k := by simp only [Finset.mem_Icc]; omega
      rw [Finset.prod_eq_zero hmem hfac0]
      ring
  · -- ¬ Antitone a : prod1 vanishes
    obtain ⟨i, hi1, hik, hlt⟩ := not_antitone_acc_succ hAa  -- acc a i < acc a (i+1)
    have hfac0 : qChoose qX (aacc (acc r k) a ((i + 1) - 1)) (acc a (i + 1)) = 0 := by
      rw [show (i + 1) - 1 = i from rfl, aacc, if_neg (by omega)]
      exact qChoose_eq_zero_of_lt hlt
    have hmem : (i + 1) ∈ Icc 1 k := by simp only [Finset.mem_Icc]; omega
    rw [Finset.prod_eq_zero hmem hfac0]
    ring

/-- **(B)** Push `Φ` through the finite-support finsum, restrict to the fibre `rOfGap = r`
(`lhsTerm_support_iff_domAZ_plus`), reindex by `fiberEquivAZ`, per-term via
`lhsTerm_eq_transfer_azTerm_plus` / `lhsTerm_vanish_of_not_domAZ`. -/
lemma sbPlus_eq_finsum_azTransfer (k : ℕ) (hk : 1 ≤ k) (r : Fin k → ℕ) (hr : Antitone r)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) :
    SbPlus k r
      = ∑ᶠ az : (Fin k → ℕ) × (Fin k → ℕ),
          (if domAZ r (acc r k) az.1 az.2 then azTransfer k r az else 0) := by
  -- The composite ring hom Φ : ℕ[X] →+* ℤ⟦X⟧ = (·.toPowerSeries) ∘ (Polynomial.map (ℕ→ℤ)).
  set Φ : Polynomial ℕ →+* ℤ⟦X⟧ :=
    (Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.mapRingHom (Nat.castRingHom ℤ)) with hΦ
  set L : ((finspan {3, 3 * k + 1}).gaps → ℕ) → Polynomial ℕ :=
    fun n => HJO.SumToSum.ThreeOne.lhsTerm k r (finspan {3, 3 * k + 1}).gaps n with hL
  -- SbPlus k r = Φ (∑ᶠ n, L n).
  have hSb : SbPlus k r = Φ (∑ᶠ n, L n) := by
    simp only [SbPlus, hΦ, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_mapRingHom, hL]
  -- Finite support of L (via Axiomlib's support_lhsTerm ⊆ lhsSupport).
  have hfin : Function.HasFiniteSupport L := by
    apply Set.Finite.subset (HJO.SumToSum.ThreeOne.lhsSupport k r).finite_toSet
    exact HJO.SumToSum.ThreeOne.support_lhsTerm k r
  -- Push Φ through the finsum.
  have hpush : Φ (∑ᶠ n, L n) = ∑ᶠ n, Φ (L n) := map_finsum Φ hfin
  rw [hSb, hpush]
  -- Off the fibre, L n = 0 so Φ(L n) = 0.
  have hoff : ∀ n, rOfGap k n ≠ r → Φ (L n) = 0 := by
    intro n hne
    have hLn : L n = 0 := by
      simp only [hL, HJO.SumToSum.ThreeOne.lhsTerm]
      rw [if_neg]
      intro hcond
      exact hne ((lhsTerm_support_iff_domAZ_plus k hk r n).1 hcond)
    rw [hLn, map_zero]
  -- ∑ᶠ n, Φ(L n) = ∑ᶠ n (_ : rOfGap k n = r), Φ(L n).
  have hrestrict : (∑ᶠ n, Φ (L n))
      = ∑ᶠ (n) (_ : rOfGap k n = r), Φ (L n) := by
    rw [← finsum_mem_univ (fun n => Φ (L n))]
    exact finsum_mem_inter_support_eq' (fun n => Φ (L n)) Set.univ {n | rOfGap k n = r}
      (by
        intro x hx
        simp only [Set.mem_univ, Set.mem_setOf_eq, true_iff]
        by_contra hne
        exact hx (hoff x hne))
  rw [hrestrict]
  rw [← finsum_subtype_eq_finsum_cond (f := fun n => Φ (L n)) (fun n => rOfGap k n = r)]
  rw [← finsum_comp_equiv (fiberEquivAZ k r)
      (f := fun az => (if domAZ r (acc r k) az.1 az.2 then azTransfer k r az else 0))]
  refine finsum_congr (fun nsub => ?_)
  obtain ⟨n, hn⟩ := nsub
  simp only [fiberEquivAZ, Equiv.coe_fn_mk]
  by_cases hdom : domAZ r (acc r k) (aOfGap k n) (zOfGap k n)
  · rw [if_pos hdom]
    have hkey := lhsTerm_eq_transfer_azTerm_plus Stil Tset invStat k hk r hr n hn hdom hRC hInv
    simp only [hL, hΦ, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_mapRingHom]
    rw [hkey]
    rfl
  · rw [if_neg hdom]
    have hkey := lhsTerm_vanish_of_not_domAZ k hk r hr n hn hdom
    simp only [hL, hΦ, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_mapRingHom]
    rw [hkey]

/-- **(A) per-content-`M`.** The transferred content sum equals the sum of `azTransfer` over
`azFinset r (acc r k) M`.  The `T (∑ rᵢ²)` prefactor is folded into each summand's exponent
(`T (∑rᵢ²) * T (Eplus) = T (∑rᵢ² + Eplus)`), and each combined summand lies in `LaurentNonneg`
by `azTransfer_arg_mem` (it is nonneg on `domAZ`, which holds on `azFinset`). -/
lemma azContent_transfer_eq (k : ℕ) (r : Fin k → ℕ) (M : ℕ) :
    transfer (T (∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2)
        * (∑ az ∈ azFinset r (acc r k) M, T (Eplus r az.1 az.2) * Brs r (acc r k) az.1 az.2))
      = ∑ az ∈ azFinset r (acc r k) M, azTransfer k r az := by
  classical
  -- membership of every summand in azFinset ⇒ domAZ
  have hdom : ∀ az ∈ azFinset r (acc r k) M, domAZ r (acc r k) az.1 az.2 := by
    intro az haz
    simp only [azFinset, Finset.mem_filter] at haz
    exact haz.2
  -- bring the prefactor inside the finite sum
  rw [Finset.mul_sum]
  -- each summand equals the azTransfer argument
  have hrw : ∀ az ∈ azFinset r (acc r k) M,
      T (∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2) * (T (Eplus r az.1 az.2) * Brs r (acc r k) az.1 az.2)
        = T ((∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2) + Eplus r az.1 az.2)
            * Brs r (acc r k) az.1 az.2 := by
    intro az _
    rw [← mul_assoc, ← LaurentPolynomial.T_add]
  rw [Finset.sum_congr rfl hrw]
  -- push transfer through the finite sum (each summand ∈ LaurentNonneg)
  rw [transfer_sum_of_mem _ _ (fun az haz => azTransfer_arg_mem r (hdom az haz))]
  -- each transferred summand is azTransfer
  rfl

/-- Membership in `azFinset`: an `(a,z)` pair is in `azFinset r s M` iff it lies in the domain
`domAZ r s a z` and its total content `∑ aᵢ + ∑ zᵢ` equals `M`.  The `k+k`-tuple `Fin.append a z`
witnesses surjectivity of the split. -/
lemma mem_azFinset {k : ℕ} (r : Fin k → ℕ) (s M : ℕ)
    (az : (Fin k → ℕ) × (Fin k → ℕ)) :
    az ∈ azFinset r s M ↔ domAZ r s az.1 az.2 ∧ ((∑ i, az.1 i) + (∑ i, az.2 i) = M) := by
  classical
  unfold azFinset
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨w, hw, hwsplit⟩, hdom⟩
    refine ⟨hdom, ?_⟩
    rw [Finset.Nat.mem_antidiagonalTuple] at hw
    rw [Fin.sum_univ_add] at hw
    -- hwsplit : (w ∘ castAdd, w ∘ natAdd) = az
    have h1 : (fun i => w (Fin.castAdd k i)) = az.1 := congrArg Prod.fst hwsplit
    have h2 : (fun i => w (Fin.natAdd k i)) = az.2 := congrArg Prod.snd hwsplit
    rw [h1, h2] at hw
    exact hw
  · rintro ⟨hdom, hsum⟩
    refine ⟨⟨Fin.append az.1 az.2, ?_, ?_⟩, hdom⟩
    · rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      exact hsum
    · ext
      · simp only [Fin.append_left]
      · simp only [Fin.append_right]

/-- **Generic content-slicing (ℓ-generic, abstract summand).** For any tuples `r : Fin ℓ → ℕ`,
boundary `s`, and abstract summand `g`, the `∑ᶠ` over `(a,z)` pairs restricted to the `domAZ`
box equals the `∑' M` of the finite `azFinset r s M` sums.  The `domAZ` box is coordinatewise
bounded (`aᵢ ≤ s`, `zᵢ ≤ rᵢ`), so the `finsum` collapses to a finite `Finset` sum, refibered by
content `M = ∑(aᵢ+zᵢ)`.  Generalizes `finsum_domAZ_eq_tsum_content` (which is the `A = ℤ⟦X⟧`,
`s = acc r k`, `g = azTransfer k r` instance). -/
lemma finsum_domAZ_eq_tsum_content_gen {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ)
    {A : Type*} [AddCommMonoid A] [TopologicalSpace A] [T2Space A]
    (g : (Fin ℓ → ℕ) × (Fin ℓ → ℕ) → A) :
    (∑ᶠ az : (Fin ℓ → ℕ) × (Fin ℓ → ℕ),
        (if domAZ r s az.1 az.2 then g az else 0))
      = ∑' M : ℕ, ∑ az ∈ azFinset r s M, g az := by
  classical
  set c : (Fin ℓ → ℕ) × (Fin ℓ → ℕ) → ℕ := fun az => (∑ i, az.1 i) + (∑ i, az.2 i) with hc
  have hbound : ∀ az : (Fin ℓ → ℕ) × (Fin ℓ → ℕ), domAZ r s az.1 az.2 →
      (∀ i, az.1 i ≤ s) ∧ (∀ i, az.2 i ≤ r i) := by
    intro az hdom
    obtain ⟨haA, ha1, hzA, hzr⟩ := hdom
    constructor
    · intro i
      by_cases hℓ : 1 ≤ ℓ
      · have h0 : az.1 i ≤ az.1 ⟨0, by omega⟩ := haA (by
          show (⟨0, by omega⟩ : Fin ℓ) ≤ i
          exact Fin.mk_le_of_le_val (Nat.zero_le _))
        have hz : az.1 ⟨0, by omega⟩ = acc az.1 1 := by
          rw [acc_val az.1 1 (le_refl 1) hℓ]
        rw [hz] at h0
        exact le_trans h0 ha1
      · exact absurd i.2 (by omega)
    · intro i
      have hℓ : 1 ≤ ℓ := by have := i.2; omega
      have hzri := hzr (i + 1) (by
        rw [Finset.mem_Icc]; exact ⟨by omega, by have := i.2; omega⟩)
      rwa [acc_val az.2 (i + 1) (by omega) (by have := i.2; omega),
        acc_val r (i + 1) (by omega) (by have := i.2; omega),
        show (⟨i + 1 - 1, by omega⟩ : Fin ℓ) = i from Fin.ext (by simp)] at hzri
  set Bfin : Finset ((Fin ℓ → ℕ) × (Fin ℓ → ℕ)) :=
    ((Fintype.piFinset (fun _ : Fin ℓ => Finset.range (s + 1))) ×ˢ
      (Fintype.piFinset (fun i : Fin ℓ => Finset.range (r i + 1)))).filter
        (fun az => domAZ r s az.1 az.2) with hBfin
  have hmemBfin : ∀ az : (Fin ℓ → ℕ) × (Fin ℓ → ℕ), az ∈ Bfin ↔ domAZ r s az.1 az.2 := by
    intro az
    rw [hBfin, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨_, hdom⟩; exact hdom
    · intro hdom
      refine ⟨⟨?_, ?_⟩, hdom⟩
      · rw [Fintype.mem_piFinset]; intro i; rw [Finset.mem_range]
        exact Nat.lt_succ_of_le ((hbound az hdom).1 i)
      · rw [Fintype.mem_piFinset]; intro i; rw [Finset.mem_range]
        exact Nat.lt_succ_of_le ((hbound az hdom).2 i)
  have hsub : Function.support
      (fun az : (Fin ℓ → ℕ) × (Fin ℓ → ℕ) =>
        (if domAZ r s az.1 az.2 then g az else 0)) ⊆ ↑Bfin := by
    intro az haz
    rw [Function.mem_support] at haz
    rw [Finset.mem_coe, hmemBfin]
    by_contra hdom
    rw [if_neg hdom] at haz
    exact haz rfl
  have hstep1 : (∑ᶠ az : (Fin ℓ → ℕ) × (Fin ℓ → ℕ),
        (if domAZ r s az.1 az.2 then g az else 0))
      = ∑ az ∈ Bfin, g az := by
    rw [finsum_eq_finset_sum_of_support_subset _ hsub]
    exact Finset.sum_congr rfl (fun az haz => if_pos ((hmemBfin az).mp haz))
  have hazEq : ∀ M : ℕ, azFinset r s M = Bfin.filter (fun az => c az = M) := by
    intro M
    apply Finset.ext
    intro az
    rw [mem_azFinset r s M az, Finset.mem_filter, hmemBfin]
  have hstep2 : (∑' M : ℕ, ∑ az ∈ azFinset r s M, g az)
      = ∑ M ∈ Bfin.image c, ∑ az ∈ azFinset r s M, g az := by
    apply tsum_eq_sum'
    intro M hM
    rw [Function.mem_support] at hM
    by_contra hnotmem
    apply hM
    have hempty : azFinset r s M = ∅ := by
      rw [hazEq M, Finset.filter_eq_empty_iff]
      intro az haz hcaz
      exact hnotmem (Finset.mem_image.mpr ⟨az, haz, hcaz⟩)
    rw [hempty, Finset.sum_empty]
  have hstep3 : (∑ M ∈ Bfin.image c, ∑ az ∈ azFinset r s M, g az)
      = ∑ az ∈ Bfin, g az := by
    have hmaps : ∀ az ∈ Bfin, c az ∈ Bfin.image c := by
      intro az haz; exact Finset.mem_image.mpr ⟨az, haz, rfl⟩
    calc ∑ M ∈ Bfin.image c, ∑ az ∈ azFinset r s M, g az
        = ∑ M ∈ Bfin.image c, ∑ az ∈ Bfin.filter (fun az => c az = M), g az := by
          apply Finset.sum_congr rfl; intro M _; rw [hazEq M]
      _ = ∑ az ∈ Bfin, g az :=
          Finset.sum_fiberwise_of_maps_to hmaps g
  rw [hstep1, hstep2, hstep3]


/-- **(B) content-slicing.**  The `∑ᶠ` over `(a,z)` pairs (restricted to the `domAZ` box by
the `if`) equals the `∑' M` over content of the finite `azFinset` sums of `azTransfer`.  The
`domAZ` box is finite (bounded coordinatewise: `aᵢ ≤ s`, `zᵢ ≤ rᵢ`), so the `finsum` collapses to
a finite `Finset` sum over the box, which is then refibered by content `M = ∑(aᵢ+zᵢ)`; each fibre
is exactly `azFinset r (acc r k) M`, and the `tsum` over `M` has finite support. -/
lemma finsum_domAZ_eq_tsum_content (k : ℕ) (hk : 1 ≤ k) (r : Fin k → ℕ) (hr : Antitone r) :
    (∑ᶠ az : (Fin k → ℕ) × (Fin k → ℕ),
        (if domAZ r (acc r k) az.1 az.2 then azTransfer k r az else 0))
      = ∑' M : ℕ, ∑ az ∈ azFinset r (acc r k) M, azTransfer k r az := by
  classical
  set s : ℕ := acc r k with hs
  set c : (Fin k → ℕ) × (Fin k → ℕ) → ℕ := fun az => (∑ i, az.1 i) + (∑ i, az.2 i) with hc
  have hbound : ∀ az : (Fin k → ℕ) × (Fin k → ℕ), domAZ r s az.1 az.2 →
      (∀ i, az.1 i ≤ s) ∧ (∀ i, az.2 i ≤ r i) := by
    intro az hdom
    obtain ⟨haA, ha1, hzA, hzr⟩ := hdom
    constructor
    · intro i
      have h0 : az.1 i ≤ az.1 ⟨0, by omega⟩ := haA (by
        show (⟨0, by omega⟩ : Fin k) ≤ i
        exact Fin.mk_le_of_le_val (Nat.zero_le _))
      have hz : az.1 ⟨0, by omega⟩ = acc az.1 1 := by
        rw [acc_val az.1 1 (le_refl 1) hk]
      rw [hz] at h0
      exact le_trans h0 ha1
    · intro i
      have hzri := hzr (i + 1) (by
        rw [Finset.mem_Icc]; exact ⟨by omega, by have := i.2; omega⟩)
      rwa [acc_val az.2 (i + 1) (by omega) (by have := i.2; omega),
        acc_val r (i + 1) (by omega) (by have := i.2; omega),
        show (⟨i + 1 - 1, by omega⟩ : Fin k) = i from Fin.ext (by simp)] at hzri
  set Bfin : Finset ((Fin k → ℕ) × (Fin k → ℕ)) :=
    ((Fintype.piFinset (fun _ : Fin k => Finset.range (s + 1))) ×ˢ
      (Fintype.piFinset (fun i : Fin k => Finset.range (r i + 1)))).filter
        (fun az => domAZ r s az.1 az.2) with hBfin
  have hmemBfin : ∀ az : (Fin k → ℕ) × (Fin k → ℕ), az ∈ Bfin ↔ domAZ r s az.1 az.2 := by
    intro az
    rw [hBfin, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨_, hdom⟩; exact hdom
    · intro hdom
      refine ⟨⟨?_, ?_⟩, hdom⟩
      · rw [Fintype.mem_piFinset]; intro i; rw [Finset.mem_range]
        exact Nat.lt_succ_of_le ((hbound az hdom).1 i)
      · rw [Fintype.mem_piFinset]; intro i; rw [Finset.mem_range]
        exact Nat.lt_succ_of_le ((hbound az hdom).2 i)
  have hsub : Function.support
      (fun az : (Fin k → ℕ) × (Fin k → ℕ) =>
        (if domAZ r s az.1 az.2 then azTransfer k r az else 0)) ⊆ ↑Bfin := by
    intro az haz
    rw [Function.mem_support] at haz
    rw [Finset.mem_coe, hmemBfin]
    by_contra hdom
    rw [if_neg hdom] at haz
    exact haz rfl
  have hstep1 : (∑ᶠ az : (Fin k → ℕ) × (Fin k → ℕ),
        (if domAZ r s az.1 az.2 then azTransfer k r az else 0))
      = ∑ az ∈ Bfin, azTransfer k r az := by
    rw [finsum_eq_finset_sum_of_support_subset _ hsub]
    exact Finset.sum_congr rfl (fun az haz => if_pos ((hmemBfin az).mp haz))
  have hazEq : ∀ M : ℕ, azFinset r s M = Bfin.filter (fun az => c az = M) := by
    intro M
    apply Finset.ext
    intro az
    rw [mem_azFinset r s M az, Finset.mem_filter, hmemBfin]
  have hstep2 : (∑' M : ℕ, ∑ az ∈ azFinset r s M, azTransfer k r az)
      = ∑ M ∈ Bfin.image c, ∑ az ∈ azFinset r s M, azTransfer k r az := by
    apply tsum_eq_sum'
    intro M hM
    rw [Function.mem_support] at hM
    by_contra hnotmem
    apply hM
    have hempty : azFinset r s M = ∅ := by
      rw [hazEq M, Finset.filter_eq_empty_iff]
      intro az haz hcaz
      exact hnotmem (Finset.mem_image.mpr ⟨az, haz, hcaz⟩)
    rw [hempty, Finset.sum_empty]
  have hstep3 : (∑ M ∈ Bfin.image c, ∑ az ∈ azFinset r s M, azTransfer k r az)
      = ∑ az ∈ Bfin, azTransfer k r az := by
    have hmaps : ∀ az ∈ Bfin, c az ∈ Bfin.image c := by
      intro az haz; exact Finset.mem_image.mpr ⟨az, haz, rfl⟩
    calc ∑ M ∈ Bfin.image c, ∑ az ∈ azFinset r s M, azTransfer k r az
        = ∑ M ∈ Bfin.image c, ∑ az ∈ Bfin.filter (fun az => c az = M), azTransfer k r az := by
          apply Finset.sum_congr rfl; intro M _; rw [hazEq M]
      _ = ∑ az ∈ Bfin, azTransfer k r az :=
          Finset.sum_fiberwise_of_maps_to hmaps (azTransfer k r)
  rw [hstep1, hstep2, hstep3]

/-- **(C)** Partition the finite `domAZ` box by content `M` into `azFinset`, factor the
`T (∑ rᵢ²)` prefactor out, convert the finite sum to a `tsum`. -/
lemma finsum_azTransfer_eq_tsum_azContent (k : ℕ) (hk : 1 ≤ k) (r : Fin k → ℕ) (hr : Antitone r) :
    (∑ᶠ az : (Fin k → ℕ) × (Fin k → ℕ),
        (if domAZ r (acc r k) az.1 az.2 then azTransfer k r az else 0))
      = ∑' M : ℕ, transfer (T (∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2)
          * (∑ az ∈ azFinset r (acc r k) M, T (Eplus r az.1 az.2) * Brs r (acc r k) az.1 az.2)) := by
  rw [finsum_domAZ_eq_tsum_content k hk r hr]
  refine tsum_congr (fun M => ?_)
  rw [azContent_transfer_eq k r M]

/-- **Layer 3c (finsum reindexing, plus).** `SbPlus k r` (a `∑ᶠ` over gap-vectors, coerced to
`ℤ⟦X⟧`) equals `∑' M` of the transferred `azFinset`/`Brs` content sums.  This is the analytic
heart: restrict the finsum to the fibre `rOfGap = r`, apply `lhsTerm_eq_transfer_azTerm_plus`,
reindex the fibre by `fiberEquivAZ` into `(a,z)` pairs, and slice by total content `M`. -/
lemma sbPlus_eq_tsum_azContent (k : ℕ) (hk : 1 ≤ k) (r : Fin k → ℕ) (hr : Antitone r)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) (hSym : Fact3 Stil) (hRecip : Fact5)
    (hQbin : Fact6) (hPD : Fact8 3 (3 * k + 1)) (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    SbPlus k r = ∑' M : ℕ, transfer (T (∑ i ∈ Icc 1 k, (acc r i : ℤ) ^ 2)
        * (∑ az ∈ azFinset r (acc r k) M, T (Eplus r az.1 az.2) * Brs r (acc r k) az.1 az.2)) := by
  rw [sbPlus_eq_finsum_azTransfer Stil Tset invStat k hk r hr hRC hInv]
  exact finsum_azTransfer_eq_tsum_azContent k hk r hr

/-- **Per-boundary transported Sum-to-Sum (`Conjecture k r` in `ℤ⟦X⟧`).**
`SbPlus k r = ∑' m, fermBodyP k r m`. This is the analytic heart: Axiomlib's general
`Conjecture k r` (`∑ᶠ_n lhsTerm = ∑ᶠ_m rhsTerm`) transported through
`Polynomial.map (Nat.castRingHom ℤ)` then `.toPowerSeries`, re-derived in this file's Laurent
world (`stmt5_fixedBoundary_plus`, `stmt_reindexEq_plus`). Deferred as a sub-lemma. -/

theorem cor_perR_plus (k : ℕ) (hk : 1 ≤ k) (r : Fin k → ℕ) (hr : Antitone r)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) (hSym : Fact3 Stil) (hRecip : Fact5)
    (hQbin : Fact6) (hPD : Fact8 3 (3 * k + 1)) (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    SbPlus k r = ∑' m : Fin k → ℕ, fermBodyP k r m := by
  rw [sbPlus_eq_tsum_azContent Stil Tset invStat tabOf Ja Jz k hk r hr
      hRC hInv hSym hRecip hQbin hPD hInvComp]
  rw [tsum_fermBodyP_by_content k r]
  refine tsum_congr (fun M => ?_)
  exact azContent_eq_fermBody_finset Stil Tset invStat tabOf Ja Jz k hk r hr M
    hRC hInv hSym hRecip hQbin hInvComp

/-! ### Minus content-slicing chain (mirror of the plus chain for `cor_perR_minus`). -/

/-! #### Minus gap-coordinate infrastructure (mirror of plus `zOfGap`/`aOfGap`/`rOfGap`/
`gapOfAZ`/`fiberEquivAZ`, using `gapEquiv_minus`; here `a,z : Fin (k-1) -> N`, `r : Fin k -> N`,
block order `inl |-> z`, `inr (inl) |-> a`, `inr (inr) |-> r`). -/

/-- `z`-coordinate tuple (minus): `z_j = n (gapEquiv_minus k hk (inl j))`. -/
noncomputable def zOfGap_minus (k : ℕ) (hk : 2 ≤ k)
    (n : (finspan {3, 3 * k - 1}).gaps → ℕ) : Fin (k - 1) → ℕ :=
  fun j => n (gapEquiv_minus k hk (Sum.inl j))

/-- `a`-coordinate tuple (minus): `a_j = n (gapEquiv_minus k hk (inr (inl j)))`. -/
noncomputable def aOfGap_minus (k : ℕ) (hk : 2 ≤ k)
    (n : (finspan {3, 3 * k - 1}).gaps → ℕ) : Fin (k - 1) → ℕ :=
  fun j => n (gapEquiv_minus k hk (Sum.inr (Sum.inl j)))

/-- `r`-coordinate (boundary) tuple (minus): `r_j = n (gapEquiv_minus k hk (inr (inr j)))`. -/
noncomputable def rOfGap_minus (k : ℕ) (hk : 2 ≤ k)
    (n : (finspan {3, 3 * k - 1}).gaps → ℕ) : Fin k → ℕ :=
  fun j => n (gapEquiv_minus k hk (Sum.inr (Sum.inr j)))

/-- Reassemble a gap-vector from `(r,a,z)` using `gapEquiv_minus`'s inverse block structure. -/
noncomputable def gapOfAZ_minus (k : ℕ) (hk : 2 ≤ k)
    (r : Fin k → ℕ) (a z : Fin (k - 1) → ℕ) : (finspan {3, 3 * k - 1}).gaps → ℕ :=
  fun g => match (gapEquiv_minus k hk).symm g with
    | Sum.inl j => z j
    | Sum.inr (Sum.inl j) => a j
    | Sum.inr (Sum.inr j) => r j

lemma zOfGap_minus_apply (k : ℕ) (hk : 2 ≤ k) (n : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (j : Fin (k - 1)) : zOfGap_minus k hk n j = n (gapEquiv_minus k hk (Sum.inl j)) := rfl

lemma aOfGap_minus_apply (k : ℕ) (hk : 2 ≤ k) (n : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (j : Fin (k - 1)) : aOfGap_minus k hk n j = n (gapEquiv_minus k hk (Sum.inr (Sum.inl j))) := rfl

lemma rOfGap_minus_apply (k : ℕ) (hk : 2 ≤ k) (n : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (j : Fin k) : rOfGap_minus k hk n j = n (gapEquiv_minus k hk (Sum.inr (Sum.inr j))) := rfl

lemma zOf_gapOfAZ_minus (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ℕ) (a z : Fin (k - 1) → ℕ) :
    zOfGap_minus k hk (gapOfAZ_minus k hk r a z) = z := by
  funext j
  rw [zOfGap_minus_apply]
  show (match (gapEquiv_minus k hk).symm (gapEquiv_minus k hk (Sum.inl j)) with
    | Sum.inl j => z j
    | Sum.inr (Sum.inl j) => a j
    | Sum.inr (Sum.inr j) => r j) = z j
  rw [Equiv.symm_apply_apply]

lemma aOf_gapOfAZ_minus (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ℕ) (a z : Fin (k - 1) → ℕ) :
    aOfGap_minus k hk (gapOfAZ_minus k hk r a z) = a := by
  funext j
  rw [aOfGap_minus_apply]
  show (match (gapEquiv_minus k hk).symm (gapEquiv_minus k hk (Sum.inr (Sum.inl j))) with
    | Sum.inl j => z j
    | Sum.inr (Sum.inl j) => a j
    | Sum.inr (Sum.inr j) => r j) = a j
  rw [Equiv.symm_apply_apply]

lemma rOf_gapOfAZ_minus (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ℕ) (a z : Fin (k - 1) → ℕ) :
    rOfGap_minus k hk (gapOfAZ_minus k hk r a z) = r := by
  funext j
  rw [rOfGap_minus_apply]
  show (match (gapEquiv_minus k hk).symm (gapEquiv_minus k hk (Sum.inr (Sum.inr j))) with
    | Sum.inl j => z j
    | Sum.inr (Sum.inl j) => a j
    | Sum.inr (Sum.inr j) => r j) = r j
  rw [Equiv.symm_apply_apply]

lemma gapOfAZ_eta_minus (k : ℕ) (hk : 2 ≤ k) (n : (finspan {3, 3 * k - 1}).gaps → ℕ) :
    gapOfAZ_minus k hk (rOfGap_minus k hk n) (aOfGap_minus k hk n) (zOfGap_minus k hk n) = n := by
  funext g
  show (match (gapEquiv_minus k hk).symm g with
    | Sum.inl j => zOfGap_minus k hk n j
    | Sum.inr (Sum.inl j) => aOfGap_minus k hk n j
    | Sum.inr (Sum.inr j) => rOfGap_minus k hk n j) = n g
  rcases h : (gapEquiv_minus k hk).symm g with j | (j | j)
  · dsimp only
    rw [zOfGap_minus_apply, ← h, Equiv.apply_symm_apply]
  · dsimp only
    rw [aOfGap_minus_apply, ← h, Equiv.apply_symm_apply]
  · dsimp only
    rw [rOfGap_minus_apply, ← h, Equiv.apply_symm_apply]

/-- The fibre of `rOfGap_minus = r` is equivalent to the `(a,z)`-tuples. -/
noncomputable def fiberEquivAZ_minus (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ℕ) :
    {n : (finspan {3, 3 * k - 1}).gaps → ℕ // rOfGap_minus k hk n = r}
      ≃ ((Fin (k - 1) → ℕ) × (Fin (k - 1) → ℕ)) where
  toFun n := (aOfGap_minus k hk n.1, zOfGap_minus k hk n.1)
  invFun az := ⟨gapOfAZ_minus k hk r az.1 az.2, rOf_gapOfAZ_minus k hk r az.1 az.2⟩
  left_inv := by
    rintro ⟨n, hn⟩
    apply Subtype.ext
    simp only
    rw [← hn]
    exact gapOfAZ_eta_minus k hk n
  right_inv := by
    rintro ⟨a, z⟩
    simp only [Prod.mk.injEq]
    exact ⟨aOf_gapOfAZ_minus k hk r a z, zOf_gapOfAZ_minus k hk r a z⟩

/-- **Support characterization (minus).** The boundary `if`-condition
`forall j, extendNat n (6k-5-3j) = r j` equals the fibre condition `rOfGap_minus k hk n = r`. -/
lemma boundary_iff_rOfGap_minus (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ℕ)
    (n : (finspan {3, 3 * k - 1}).gaps → ℕ) :
    (∀ j : Fin k, HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) = r j) ↔ rOfGap_minus k hk n = r := by
  have key : ∀ j : Fin k, HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) = rOfGap_minus k hk n j := by
    intro j
    rw [rOfGap_minus_apply]
    have hg : gapEquiv_minus k hk (Sum.inr (Sum.inr j))
        = ⟨6 * k - 5 - 3 * (j : ℕ), memR_minus k hk j⟩ := by
      simp only [gapEquiv_minus, Equiv.ofBijective_apply]; rfl
    rw [hg]
    show HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ))
      = n ⟨6 * k - 5 - 3 * (j : ℕ), memR_minus k hk j⟩
    rw [HJO.extendNat, dif_pos (memR_minus k hk j)]
  constructor
  · intro h; funext j; rw [← key j, h j]
  · intro h j; rw [key j, h]

/-! #### Coordinate readings (minus). -/

/-- `extendNat n (3(k-1-i)-1) = zOfGap_minus n i`. -/
lemma extendNat_zgap_read_minus (k : ℕ) (hk : 2 ≤ k) (n : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (i : Fin (k - 1)) :
    HJO.extendNat n (3 * (k - 1 - (i : ℕ)) - 1) = zOfGap_minus k hk n i := by
  rw [HJO.extendNat_of_mem (memZ_minus k hk i), zOfGap_minus_apply]
  apply congrArg n
  apply Subtype.ext
  simp only [gapEquiv_minus, gapSub_minus, Equiv.ofBijective_apply]

/-- `extendNat n (3(k-1-i)-2) = aOfGap_minus n i`. -/
lemma extendNat_agap_read_minus (k : ℕ) (hk : 2 ≤ k) (n : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (i : Fin (k - 1)) :
    HJO.extendNat n (3 * (k - 1 - (i : ℕ)) - 2) = aOfGap_minus k hk n i := by
  rw [HJO.extendNat_of_mem (memA_minus k hk i), aOfGap_minus_apply]
  apply congrArg n
  apply Subtype.ext
  simp only [gapEquiv_minus, gapSub_minus, Equiv.ofBijective_apply]

/-- `extendNat n (6k-5-3j) = rOfGap_minus n j` for `j : Fin k`. -/
lemma extendNat_rgap_read_minus (k : ℕ) (hk : 2 ≤ k) (n : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (j : Fin k) :
    HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) = rOfGap_minus k hk n j := by
  rw [HJO.extendNat_of_mem (memR_minus k hk j), rOfGap_minus_apply]
  apply congrArg n
  apply Subtype.ext
  simp only [gapEquiv_minus, gapSub_minus, Equiv.ofBijective_apply]

/-- `extendNat n (3x-2) = acc (aOfGap_minus n) (k-x)` for `1 <= x < k`. -/
lemma extendNat_a2_read_minus (k : ℕ) (hk : 2 ≤ k) (n : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (x : ℕ) (hx1 : 1 ≤ x) (hx : x < k) :
    HJO.extendNat n (3 * x - 2) = acc (aOfGap_minus k hk n) (k - x) := by
  set i : Fin (k - 1) := ⟨k - 1 - x, by omega⟩ with hi
  have hidx : 3 * x - 2 = 3 * (k - 1 - (i : ℕ)) - 2 := by simp only [hi]; omega
  rw [hidx, extendNat_agap_read_minus k hk n i,
    acc_val (aOfGap_minus k hk n) (k - x) (by omega) (by omega)]
  congr 1
  apply Fin.ext
  simp only [hi]; omega

/-- `extendNat n (3x+1) = aacc (acc r k) (aOfGap_minus n) (k-x-1)` for `1 <= x <= k-1`,
`hn : rOfGap_minus n = r`. -/
lemma extendNat_a1_read_minus (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ℕ)
    (n : (finspan {3, 3 * k - 1}).gaps → ℕ) (hn : rOfGap_minus k hk n = r)
    (x : ℕ) (hx1 : 1 ≤ x) (hx : x ≤ k - 1) :
    HJO.extendNat n (3 * x + 1) = aacc (acc r k) (aOfGap_minus k hk n) (k - x - 1) := by
  rcases Nat.lt_or_ge x (k - 1) with hlt | hge
  · have hidx : 3 * x + 1 = 3 * (x + 1) - 2 := by omega
    rw [hidx, extendNat_a2_read_minus k hk n (x + 1) (by omega) (by omega),
      aacc, if_neg (by omega), show k - (x + 1) = k - x - 1 by omega]
  · have hxk : x = k - 1 := by omega
    subst hxk
    rw [aacc, if_pos (by omega)]
    set j : Fin k := ⟨k - 1, by omega⟩ with hj
    have hidx : 3 * (k - 1) + 1 = 6 * k - 5 - 3 * (j : ℕ) := by simp only [hj]; omega
    rw [hidx, extendNat_rgap_read_minus k hk n j, hn,
      acc_val r k (by omega) (by omega)]

/-- `extendNat n (3x-1) = acc (zOfGap_minus n) (k-x)` for `1 <= x < k`. -/
lemma extendNat_z1_read_minus (k : ℕ) (hk : 2 ≤ k) (n : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (x : ℕ) (hx1 : 1 ≤ x) (hx : x < k) :
    HJO.extendNat n (3 * x - 1) = acc (zOfGap_minus k hk n) (k - x) := by
  set i : Fin (k - 1) := ⟨k - 1 - x, by omega⟩ with hi
  have hidx : 3 * x - 1 = 3 * (k - 1 - (i : ℕ)) - 1 := by simp only [hi]; omega
  rw [hidx, extendNat_zgap_read_minus k hk n i,
    acc_val (zOfGap_minus k hk n) (k - x) (by omega) (by omega)]
  congr 1
  apply Fin.ext
  simp only [hi]; omega

/-- `extendNat n (3x-4) = acc (zOfGap_minus n) (k-x+1)` for `1 <= x < k`. -/
lemma extendNat_z4_read_minus (k : ℕ) (hk : 2 ≤ k) (n : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (x : ℕ) (hx1 : 1 ≤ x) (hx : x < k) :
    HJO.extendNat n (3 * x - 4) = acc (zOfGap_minus k hk n) (k - x + 1) := by
  rcases Nat.lt_or_ge x 2 with hx2 | hx2
  · have hx1' : x = 1 := by omega
    subst hx1'
    rw [show 3 * 1 - 4 = 0 from rfl, HJO.extendNat_gaps_zero,
      acc_zero_of (zOfGap_minus k hk n) (k - 1 + 1) (by omega)]
  · have hidx : 3 * x - 4 = 3 * (x - 1) - 1 := by omega
    rw [hidx, extendNat_z1_read_minus k hk n (x - 1) (by omega) (by omega),
      show k - (x - 1) = k - x + 1 by omega]


/-- The `(a,z)`-transfer summand for the minus case: the `ℤ⟦X⟧` image of the Laurent `T`-monomial
term at `(a,z)`, with the minus prefactor `T((acc r k)² + ∑_{i<k}(acc r i)²)` folded in and the
trimmed tuple `r' = fun i : Fin (k-1) => r (Fin.castLE _ i)`, boundary `s = acc r k`. -/
noncomputable def azTransferM (k : ℕ) (r : Fin k → ℕ)
    (az : (Fin (k - 1) → ℕ) × (Fin (k - 1) → ℕ)) : ℤ⟦X⟧ :=
  transfer (T (((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
      + Eminus (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) az.1 az.2)
    * Brs (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) az.1 az.2)

/-- The minus-exponent `(rₖ)² + ∑_{i<k} rᵢ² + E⁻(a,z)` is nonnegative under `domAZ r' (rₖ) a z`,
where `r' = r ∘ castLE`.  Termwise sum of squares (mirror of `azExp_nonneg_gen`, minus form). -/
lemma azExpM_nonneg (k : ℕ) (r : Fin k → ℕ)
    {a z : Fin (k - 1) → ℕ}
    (hdom : domAZ (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) a z) :
    0 ≤ ((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
        + Eminus (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) a z := by
  set r' : Fin (k - 1) → ℕ := fun i : Fin (k - 1) => r (Fin.castLE (by omega) i) with hr'_def
  obtain ⟨_, _, _, hzr⟩ := hdom
  -- `acc r' i = acc r i` for `1 ≤ i ≤ k-1`.
  have acc_r' : ∀ i, 1 ≤ i → i ≤ k - 1 → acc r' i = acc r i := by
    intro i h1 h2
    simp only [acc, hr'_def,
      dif_pos (show 1 ≤ i ∧ i ≤ k - 1 from ⟨h1, h2⟩),
      dif_pos (show 1 ≤ i ∧ i ≤ k from ⟨h1, by omega⟩)]
    congr 1
  -- rewrite the prefactor sum over `acc r` into a sum over `acc r'`.
  have hpref : (∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
      = ∑ i ∈ Icc 1 (k - 1), (acc r' i : ℤ) ^ 2 := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_Icc] at hi
    rw [acc_r' i hi.1 hi.2]
  rw [hpref]
  -- (rₖ)² ≥ 0; combine the remaining `∑ r'ᵢ² + E⁻` termwise.
  have hrk : (0 : ℤ) ≤ (acc r k : ℤ) ^ 2 := sq_nonneg _
  have hrest : (0 : ℤ) ≤ (∑ i ∈ Icc 1 (k - 1), (acc r' i : ℤ) ^ 2)
      + Eminus r' (acc r k) a z := by
    rw [Eminus, ← Finset.sum_add_distrib]
    apply Finset.sum_nonneg
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hZR : (acc z i : ℤ) ≤ (acc r' i : ℤ) := by
      exact_mod_cast hzr i (Finset.mem_Icc.2 hi)
    have hZnn : (0 : ℤ) ≤ (acc z i : ℤ) := Int.natCast_nonneg _
    have hAnn : (0 : ℤ) ≤ (acc a i : ℤ) := Int.natCast_nonneg _
    have hAacc : (0 : ℤ) ≤ (aacc (acc r k) a (i - 1) : ℤ) := Int.natCast_nonneg _
    have hRnn : (0 : ℤ) ≤ (acc r' i : ℤ) := Int.natCast_nonneg _
    nlinarith [sq_nonneg ((acc a i : ℤ) + (acc z i : ℤ) - (acc r' i : ℤ)),
      mul_nonneg hZnn hAacc, mul_nonneg hAnn hZnn,
      mul_nonneg hZnn (sub_nonneg.2 hZR), mul_nonneg hAnn (sub_nonneg.2 hZR)]
  linarith

/-- The `azTransferM` argument `T(prefM + E⁻) * Brs` lies in `LaurentNonneg` under `domAZ`. -/
lemma azTransferM_arg_mem (k : ℕ) (r : Fin k → ℕ)
    {a z : Fin (k - 1) → ℕ}
    (hdom : domAZ (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) a z) :
    (T (((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
        + Eminus (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) a z)
      * Brs (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) a z)
      ∈ LaurentNonneg := by
  have he0 : 0 ≤ ((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
      + Eminus (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) a z :=
    azExpM_nonneg k r hdom
  refine LaurentNonneg.mul_mem ?_ (Brs_mem _ _ _ _)
  rw [show (((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
        + Eminus (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) a z)
      = (((((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
          + Eminus (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) a z).toNat : ℤ))
      from (Int.toNat_of_nonneg he0).symm]
  exact T_nat_mem _

/-! #### Per-term identity, off-domain vanish, and assembly for
`sbMinus_eq_finsum_azTransfer_minus` (mirror of the plus `lhsTerm_*` chain, but with the
`SbMinus` body already living in `ℤ⟦X⟧`, so no coercion ring hom `Φ`). -/

/-- Abbreviation: the `SbMinus` body at gap-vector `n` (inside the `if`, ignoring the guard). -/
noncomputable def sbMinusBody (k : ℕ) (r : Fin k → ℕ)
    (n : (finspan {3, 3 * k - 1}).gaps → ℕ) : ℤ⟦X⟧ :=
  X ^ (HJO.Q' (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) (fun i => (n i : ℤ))).toNat *
    ∏ j ∈ Icc 1 (k - 1),
      (qChoose (X : ℤ⟦X⟧) (HJO.extendNat n (3 * j + 1)) (HJO.extendNat n (3 * j - 2))
        * HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧)
            ((acc r (k - j) : ℤ) - (HJO.extendNat n (3 * j - 4) : ℤ))
            ((HJO.extendNat n (3 * j - 1) : ℤ) - (HJO.extendNat n (3 * j - 4) : ℤ)))

/-- The `SbMinus` finsum body equals `if guard then sbMinusBody else 0`. -/
lemma sbMinus_body_eq (k : ℕ) (r : Fin k → ℕ) :
    SbMinus k r
      = ∑ᶠ n : (finspan {3, 3 * k - 1}).gaps → ℕ,
          (if ∀ j : Fin k, HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) = r j
            then sbMinusBody k r n else 0) := rfl

/-- Exponent match (minus): `Q'` on the coerced gap-vector equals
`(acc r k)² + Σ_{i<k}(acc r i)² + E⁻(a,z)` (as naturals via `.toNat`). -/
lemma lhs_exp_eq_minus (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ℕ)
    (n : (finspan {3, 3 * k - 1}).gaps → ℕ) (hn : rOfGap_minus k hk n = r)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) :
    ((HJO.Q' (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1)) fun x => ↑(n x)).toNat
      = (((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
          + Eminus (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k)
              (aOfGap_minus k hk n) (zOfGap_minus k hk n)).toNat := by
  congr 1
  have hQ : (HJO.Q 3 (3 * k - 1)) (fun x => (↑(n x) : ℤ))
      = (acc r k : ℤ) ^ 2 + (∑ j ∈ Icc 1 (k - 1), (acc r j : ℤ) ^ 2)
          + Eminus (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k)
              (aOfGap_minus k hk n) (zOfGap_minus k hk n) := by
    apply stmt_reindexEq_minus (Stil := Stil) (Tset := Tset) (invStat := invStat)
      k hk (fun x => (↑(n x) : ℤ)) r (aOfGap_minus k hk n) (zOfGap_minus k hk n)
    · intro j h
      rw [show n ⟨_, h⟩ = HJO.extendNat n (3 * (k - 1 - (j : ℕ)) - 1) from
        (HJO.extendNat_of_mem h).symm, extendNat_zgap_read_minus k hk n j]
    · intro j h
      rw [show n ⟨_, h⟩ = HJO.extendNat n (3 * (k - 1 - (j : ℕ)) - 2) from
        (HJO.extendNat_of_mem h).symm, extendNat_agap_read_minus k hk n j]
    · intro j h
      rw [show n ⟨_, h⟩ = HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) from
        (HJO.extendNat_of_mem h).symm, extendNat_rgap_read_minus k hk n j, hn]
    · exact hRC
    · exact hInv
  rw [show (HJO.Q' (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1)) (fun x => (↑(n x) : ℤ))
        = (HJO.Q 3 (3 * k - 1)) (fun x => (↑(n x) : ℤ)) from rfl, hQ]

/-- Per-term identity (minus): on the fibre `rOfGap_minus = r`, at `(a,z)` in `domAZ`, the
`SbMinus` body equals `azTransferM k r (a,z)`. -/
lemma sbMinusBody_eq_azTransferM (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ℕ) (hr : Antitone r)
    (n : (finspan {3, 3 * k - 1}).gaps → ℕ) (hn : rOfGap_minus k hk n = r)
    (hdom : domAZ (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k)
      (aOfGap_minus k hk n) (zOfGap_minus k hk n))
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) :
    sbMinusBody k r n = azTransferM k r (aOfGap_minus k hk n, zOfGap_minus k hk n) := by
  set r' : Fin (k - 1) → ℕ := fun i : Fin (k - 1) => r (Fin.castLE (by omega) i) with hr'_def
  set a := aOfGap_minus k hk n with ha
  set z := zOfGap_minus k hk n with hz
  set e : ℤ := ((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
    + Eminus r' (acc r k) a z with he
  -- `acc r' i = acc r i` on `Icc 1 (k-1)`.
  have acc_r' : ∀ i, 1 ≤ i → i ≤ k - 1 → acc r' i = acc r i := by
    intro i h1 h2
    simp only [acc, hr'_def,
      dif_pos (show 1 ≤ i ∧ i ≤ k - 1 from ⟨h1, h2⟩),
      dif_pos (show 1 ≤ i ∧ i ≤ k from ⟨h1, by omega⟩)]
    congr 1
  -- RHS: unfold azTransferM, push transfer through `T e * Brs`.
  have he0 : 0 ≤ e := azExpM_nonneg k r hdom
  have heT : (T e : LaurentPolynomial ℤ) = T ((e.toNat : ℤ)) := by
    rw [Int.toNat_of_nonneg he0]
  have hRHS : azTransferM k r (a, z)
      = (X : ℤ⟦X⟧) ^ e.toNat
        * ∏ i ∈ Icc 1 (k - 1), qChoose qX (aacc (acc r k) a (i - 1)) (acc a i)
            * qChoose qX (acc r' i - acc z (i + 1)) (acc z i - acc z (i + 1)) := by
    rw [azTransferM]
    simp only []
    rw [show (((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
        + Eminus r' (acc r k) a z) = e from rfl]
    rw [transfer_mul_of_mem (by rw [heT]; exact T_nat_mem _) (Brs_mem _ _ _ _),
      heT, transfer_T, transfer_Brs]
  rw [hRHS]
  -- LHS: expand sbMinusBody; the exponent via lhs_exp_eq_minus.
  rw [sbMinusBody,
    lhs_exp_eq_minus (Stil := Stil) (Tset := Tset) (invStat := invStat) k hk r n hn hRC hInv,
    ← he]
  congr 1
  -- match the products by reindexing `i = k - j` on the RHS.
  obtain ⟨hAa, hs, hAz, hzr⟩ := hdom
  refine Finset.prod_nbij' (fun j => k - j) (fun i => k - i) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_Icc] at *; omega
  · intro i hi; simp only [Finset.mem_Icc] at *; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; omega
  · intro i hi; simp only [Finset.mem_Icc] at hi; omega
  · -- per-factor identity: LHSbody j = RHSbody (k - j).
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hj1 : 1 ≤ j := hj.1
    have hjk : j ≤ k - 1 := hj.2
    have hjk' : j < k := by omega
    rw [extendNat_a1_read_minus k hk r n hn j hj1 hjk,
      extendNat_a2_read_minus k hk n j hj1 hjk',
      extendNat_z1_read_minus k hk n j hj1 hjk',
      extendNat_z4_read_minus k hk n j hj1 hjk']
    have hzr' : acc z (k - j) ≤ acc r' (k - j) := by
      have := hzr (k - j) (by simp only [Finset.mem_Icc]; omega); simpa [hz] using this
    have hzshift : acc z (k - j + 1) ≤ acc z (k - j) := by
      have : acc (zOfGap_minus k hk n) (k - j + 1) ≤ acc (zOfGap_minus k hk n) (k - j) :=
        acc_succ_le hAz (by omega)
      simpa [hz] using this
    have h1 : (0 : ℤ) ≤ (acc r' (k - j) : ℤ) - (acc z (k - j + 1) : ℤ) := by
      have hle : acc z (k - j + 1) ≤ acc r' (k - j) := le_trans hzshift hzr'
      have := (Nat.cast_le (α := ℤ)).2 hle; omega
    have h2 : (0 : ℤ) ≤ (acc z (k - j) : ℤ) - (acc z (k - j + 1) : ℤ) := by
      have := (Nat.cast_le (α := ℤ)).2 hzshift; omega
    -- the `acc r (k-j)` in the SbMinus body agrees with `acc r' (k-j)`.
    have hrr' : acc r (k - j) = acc r' (k - j) := (acc_r' (k - j) (by omega) (by omega)).symm
    rw [show ((acc r (k - j) : ℤ)) = ((acc r' (k - j) : ℤ)) by rw [hrr']]
    rw [HJO.SumToSum.extendedQChoose_of_nonneg h1 h2,
      show ((acc r' (k - j) : ℤ) - (acc z (k - j + 1) : ℤ)).toNat
        = acc r' (k - j) - acc z (k - j + 1) from Int.toNat_sub _ _,
      show ((acc z (k - j) : ℤ) - (acc z (k - j + 1) : ℤ)).toNat
        = acc z (k - j) - acc z (k - j + 1) from Int.toNat_sub _ _]

/-- Off-domain vanish (minus): on the fibre `rOfGap_minus = r`, off `domAZ`, the body is `0`. -/
lemma sbMinusBody_vanish_of_not_domAZ (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ℕ) (hr : Antitone r)
    (n : (finspan {3, 3 * k - 1}).gaps → ℕ) (hn : rOfGap_minus k hk n = r)
    (hdom : ¬ domAZ (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k)
      (aOfGap_minus k hk n) (zOfGap_minus k hk n)) :
    sbMinusBody k r n = 0 := by
  set r' : Fin (k - 1) → ℕ := fun i : Fin (k - 1) => r (Fin.castLE (by omega) i) with hr'_def
  set a := aOfGap_minus k hk n with ha
  set z := zOfGap_minus k hk n with hz
  have acc_r' : ∀ i, 1 ≤ i → i ≤ k - 1 → acc r' i = acc r i := by
    intro i h1 h2
    simp only [acc, hr'_def,
      dif_pos (show 1 ≤ i ∧ i ≤ k - 1 from ⟨h1, h2⟩),
      dif_pos (show 1 ≤ i ∧ i ≤ k from ⟨h1, by omega⟩)]
    congr 1
  rw [sbMinusBody]
  -- rewrite the product body per factor into `(a-factor) * (z-factor)` in coordinate form.
  have hbody : (∏ j ∈ Icc 1 (k - 1),
      (qChoose (X : ℤ⟦X⟧) (HJO.extendNat n (3 * j + 1)) (HJO.extendNat n (3 * j - 2))
        * HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧)
            ((acc r (k - j) : ℤ) - (HJO.extendNat n (3 * j - 4) : ℤ))
            ((HJO.extendNat n (3 * j - 1) : ℤ) - (HJO.extendNat n (3 * j - 4) : ℤ))))
      = ∏ j ∈ Icc 1 (k - 1),
        (qChoose (X : ℤ⟦X⟧) (aacc (acc r k) a (k - j - 1)) (acc a (k - j))
          * HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧)
              ((acc r' (k - j) : ℤ) - (acc z (k - j + 1) : ℤ))
              ((acc z (k - j) : ℤ) - (acc z (k - j + 1) : ℤ))) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hj1 : 1 ≤ j := hj.1
    have hjk : j ≤ k - 1 := hj.2
    have hjk' : j < k := by omega
    rw [extendNat_a1_read_minus k hk r n hn j hj1 hjk,
      extendNat_a2_read_minus k hk n j hj1 hjk',
      extendNat_z1_read_minus k hk n j hj1 hjk',
      extendNat_z4_read_minus k hk n j hj1 hjk']
    have hrr' : acc r (k - j) = acc r' (k - j) := (acc_r' (k - j) (by omega) (by omega)).symm
    rw [show ((acc r (k - j) : ℤ)) = ((acc r' (k - j) : ℤ)) by rw [hrr']]
  rw [hbody]
  -- now kill via one vanishing factor.
  by_cases hAa : Antitone a
  · by_cases hs : acc a 1 ≤ acc r k
    · by_cases hAz : Antitone z
      · have hd4 : ¬ (∀ i ∈ Icc 1 (k - 1), acc z i ≤ acc r' i) := by
          intro h4; exact hdom ⟨hAa, hs, hAz, h4⟩
        push_neg at hd4
        obtain ⟨i, hi, hlt⟩ := hd4  -- acc r' i < acc z i
        simp only [Finset.mem_Icc] at hi
        have hjmem : (k - i) ∈ Icc 1 (k - 1) := by simp only [Finset.mem_Icc]; omega
        have hkj : k - (k - i) = i := by omega
        have hfac0 : (qChoose (X : ℤ⟦X⟧) (aacc (acc r k) a (k - (k - i) - 1)) (acc a (k - (k - i)))
            * HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧)
                ((acc r' (k - (k - i)) : ℤ) - (acc z (k - (k - i) + 1) : ℤ))
                ((acc z (k - (k - i)) : ℤ) - (acc z (k - (k - i) + 1) : ℤ))) = 0 := by
          rw [hkj]
          have hez : HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧)
              ((acc r' i : ℤ) - (acc z (i + 1) : ℤ)) ((acc z i : ℤ) - (acc z (i + 1) : ℤ)) = 0 := by
            by_cases hnn : (0 : ℤ) ≤ (acc r' i : ℤ) - (acc z (i + 1) : ℤ)
            · by_cases hnn2 : (0 : ℤ) ≤ (acc z i : ℤ) - (acc z (i + 1) : ℤ)
              · rw [HJO.SumToSum.extendedQChoose_of_nonneg hnn hnn2,
                  show ((acc r' i : ℤ) - (acc z (i + 1) : ℤ)).toNat
                    = acc r' i - acc z (i + 1) from Int.toNat_sub _ _,
                  show ((acc z i : ℤ) - (acc z (i + 1) : ℤ)).toNat
                    = acc z i - acc z (i + 1) from Int.toNat_sub _ _]
                apply qChoose_eq_zero_of_lt
                omega
              · rw [HJO.SumToSum.extendedQChoose_of_neg_left (Or.inr (by omega))]
            · rw [HJO.SumToSum.extendedQChoose_of_neg_left (Or.inl (by omega))]
          rw [hez, mul_zero]
        rw [Finset.prod_eq_zero hjmem hfac0, mul_zero]
      · obtain ⟨i, hi1, hik, hlt⟩ := not_antitone_acc_succ hAz  -- acc z i < acc z (i+1)
        have hjmem : (k - i) ∈ Icc 1 (k - 1) := by simp only [Finset.mem_Icc]; omega
        have hkj : k - (k - i) = i := by omega
        have hfac0 : (qChoose (X : ℤ⟦X⟧) (aacc (acc r k) a (k - (k - i) - 1)) (acc a (k - (k - i)))
            * HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧)
                ((acc r' (k - (k - i)) : ℤ) - (acc z (k - (k - i) + 1) : ℤ))
                ((acc z (k - (k - i)) : ℤ) - (acc z (k - (k - i) + 1) : ℤ))) = 0 := by
          rw [hkj]
          have hneg : (acc z i : ℤ) - (acc z (i + 1) : ℤ) < 0 := by
            have := (Nat.cast_lt (α := ℤ)).2 hlt; omega
          rw [HJO.SumToSum.extendedQChoose_of_neg_left (Or.inr hneg), mul_zero]
        rw [Finset.prod_eq_zero hjmem hfac0, mul_zero]
    · -- ¬ (acc a 1 ≤ acc r k): a-block vanishes at k - j = 1, i.e. j = k - 1.
      have hlt : acc r k < acc a 1 := not_le.mp hs
      have hjmem : (k - 1) ∈ Icc 1 (k - 1) := by simp only [Finset.mem_Icc]; omega
      have hkj : k - (k - 1) = 1 := by omega
      have hfac0 : (qChoose (X : ℤ⟦X⟧) (aacc (acc r k) a (k - (k - 1) - 1)) (acc a (k - (k - 1)))
          * HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧)
              ((acc r' (k - (k - 1)) : ℤ) - (acc z (k - (k - 1) + 1) : ℤ))
              ((acc z (k - (k - 1)) : ℤ) - (acc z (k - (k - 1) + 1) : ℤ))) = 0 := by
        rw [hkj,
          show aacc (acc r k) a (1 - 1) = acc r k by rw [aacc, if_pos rfl],
          qChoose_eq_zero_of_lt hlt, zero_mul]
      rw [Finset.prod_eq_zero hjmem hfac0, mul_zero]
  · -- ¬ Antitone a: a-block vanishes at k - j = i + 1, i.e. j = k - i - 1.
    obtain ⟨i, hi1, hik, hlt⟩ := not_antitone_acc_succ hAa  -- acc a i < acc a (i+1)
    have hjmem : (k - i - 1) ∈ Icc 1 (k - 1) := by simp only [Finset.mem_Icc]; omega
    have hkj : k - (k - i - 1) = i + 1 := by omega
    have hfac0 : (qChoose (X : ℤ⟦X⟧) (aacc (acc r k) a (k - (k - i - 1) - 1)) (acc a (k - (k - i - 1)))
        * HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧)
            ((acc r' (k - (k - i - 1)) : ℤ) - (acc z (k - (k - i - 1) + 1) : ℤ))
            ((acc z (k - (k - i - 1)) : ℤ) - (acc z (k - (k - i - 1) + 1) : ℤ))) = 0 := by
      have haci : aacc (acc r k) a (i + 1 - 1) = acc a i := by
        rw [show i + 1 - 1 = i by omega, aacc, if_neg (by omega)]
      rw [hkj, haci, qChoose_eq_zero_of_lt hlt, zero_mul]
    rw [Finset.prod_eq_zero hjmem hfac0, mul_zero]

/-- **(A minus) `SbMinus` as a `∑ᶠ` of `azTransferM` over the `domAZ` box.**  `SbMinus` is already
a `∑ᶠ` over gap-vectors of `if cond then body else 0`; restrict to the fibre `rOfGap_minus = r`,
reindex by the `(a,z)` gap-equivalence, and identify the per-`(a,z)` body (on `domAZ`) with
`azTransferM`, off `domAZ` with `0`. -/
lemma sbMinus_eq_finsum_azTransfer_minus (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ℕ) (hr : Antitone r)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) :
    SbMinus k r
      = ∑ᶠ az : (Fin (k - 1) → ℕ) × (Fin (k - 1) → ℕ),
          (if domAZ (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) az.1 az.2
            then azTransferM k r az else 0) := by
  rw [sbMinus_body_eq k r]
  -- Off the fibre, the guard fails so the body is 0.
  have hoff : ∀ n, rOfGap_minus k hk n ≠ r →
      (if ∀ j : Fin k, HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) = r j
        then sbMinusBody k r n else 0) = 0 := by
    intro n hne
    rw [if_neg]
    intro hcond
    exact hne ((boundary_iff_rOfGap_minus k hk r n).1 hcond)
  -- restrict to fibre.
  have hrestrict : (∑ᶠ n : (finspan {3, 3 * k - 1}).gaps → ℕ,
        (if ∀ j : Fin k, HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) = r j
          then sbMinusBody k r n else 0))
      = ∑ᶠ (n) (_ : rOfGap_minus k hk n = r),
          (if ∀ j : Fin k, HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) = r j
            then sbMinusBody k r n else 0) := by
    rw [← finsum_mem_univ (fun n => if ∀ j : Fin k, HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) = r j
          then sbMinusBody k r n else 0)]
    exact finsum_mem_inter_support_eq'
      (fun n => if ∀ j : Fin k, HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) = r j
        then sbMinusBody k r n else 0) Set.univ {n | rOfGap_minus k hk n = r}
      (by
        intro x hx
        simp only [Set.mem_univ, Set.mem_setOf_eq, true_iff]
        by_contra hne
        exact hx (hoff x hne))
  rw [hrestrict]
  rw [← finsum_subtype_eq_finsum_cond
    (f := fun n => if ∀ j : Fin k, HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) = r j
      then sbMinusBody k r n else 0) (fun n => rOfGap_minus k hk n = r)]
  rw [← finsum_comp_equiv (fiberEquivAZ_minus k hk r)
      (f := fun az => (if domAZ (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k)
        az.1 az.2 then azTransferM k r az else 0))]
  refine finsum_congr (fun nsub => ?_)
  obtain ⟨n, hn⟩ := nsub
  simp only [fiberEquivAZ_minus, Equiv.coe_fn_mk]
  -- the guard holds on the fibre.
  have hcond : ∀ j : Fin k, HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) = r j :=
    (boundary_iff_rOfGap_minus k hk r n).2 hn
  rw [if_pos hcond]
  by_cases hdom : domAZ (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k)
    (aOfGap_minus k hk n) (zOfGap_minus k hk n)
  · rw [if_pos hdom, sbMinusBody_eq_azTransferM Stil Tset invStat k hk r hr n hn hdom hRC hInv]
  · rw [if_neg hdom, sbMinusBody_vanish_of_not_domAZ k hk r hr n hn hdom]


/-- **(B minus) per-content-`M`.**  Fold the minus prefactor into each `azFinset` summand:
`transfer(prefM · ∑ az, T(Eminus)·Brs) = ∑ az, azTransferM`. -/
lemma azContent_transfer_eq_minus (k : ℕ) (r : Fin k → ℕ) (M : ℕ) :
    transfer (T ((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
        * (∑ az ∈ azFinset (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) M,
            T (Eminus (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) az.1 az.2)
              * Brs (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) az.1 az.2))
      = ∑ az ∈ azFinset (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) M,
          azTransferM k r az := by
  classical
  set r' : Fin (k - 1) → ℕ := fun i : Fin (k - 1) => r (Fin.castLE (by omega) i) with hr'_def
  -- every summand is in `domAZ`
  have hdom : ∀ az ∈ azFinset r' (acc r k) M, domAZ r' (acc r k) az.1 az.2 := by
    intro az haz
    simp only [azFinset, Finset.mem_filter] at haz
    exact haz.2
  -- bring the prefactor inside the finite sum
  rw [Finset.mul_sum]
  -- fold each summand's prefactor `T` into the `Eminus` `T`
  have hrw : ∀ az ∈ azFinset r' (acc r k) M,
      T ((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
          * (T (Eminus r' (acc r k) az.1 az.2) * Brs r' (acc r k) az.1 az.2)
        = T (((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
              + Eminus r' (acc r k) az.1 az.2)
            * Brs r' (acc r k) az.1 az.2 := by
    intro az _
    rw [← mul_assoc, ← LaurentPolynomial.T_add]
  rw [Finset.sum_congr rfl hrw]
  -- push `transfer` through the finite sum (each summand ∈ LaurentNonneg)
  rw [transfer_sum_of_mem _ _ (fun az haz => azTransferM_arg_mem k r (hdom az haz))]
  rfl

/-- **(A)∘(B) minus:** the `∑ᶠ` of `azTransferM` equals the `∑' M` of the transferred content sums. -/
lemma finsum_azTransfer_minus_eq_tsum_azContent (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ℕ)
    (hr : Antitone r) :
    (∑ᶠ az : (Fin (k - 1) → ℕ) × (Fin (k - 1) → ℕ),
        (if domAZ (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) az.1 az.2
          then azTransferM k r az else 0))
      = ∑' M : ℕ, transfer (T ((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
          * (∑ az ∈ azFinset (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) M,
              T (Eminus (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) az.1 az.2)
                * Brs (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) az.1 az.2)) := by
  rw [finsum_domAZ_eq_tsum_content_gen (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i))
    (acc r k) (azTransferM k r)]
  refine tsum_congr (fun M => ?_)
  rw [azContent_transfer_eq_minus k r M]

/-- **(C minus)** the transferred content sum equals the fermionic finite `m`-sum, via
`stmt5_fixedBoundary_minus` transported termwise. -/
lemma azContent_eq_fermBody_finset_minus (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ℕ) (hr : Antitone r)
    (M : ℕ) (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) (hSym : Fact3 Stil)
    (hRecip : Fact5) (hQbin : Fact6) (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    transfer (T ((acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i : ℤ) ^ 2)
        * (∑ az ∈ azFinset (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) M,
            T (Eminus (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) az.1 az.2)
              * Brs (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) az.1 az.2))
      = ∑ m ∈ Finset.Nat.antidiagonalTuple (k - 1) M, fermBodyM k r m := by
  rw [stmt5_fixedBoundary_minus_aux Stil Tset invStat tabOf Ja Jz k hk r hr M
      hRC hInv hSym hRecip hQbin hInvComp]
  -- The exponent inside `T` for term `m`.
  set E : (Fin (k - 1) → ℕ) → ℤ := fun m =>
    (acc r k : ℤ) ^ 2 + ∑ i ∈ Icc 1 (k - 1),
        ((acc r i : ℤ) ^ 2 - (acc r i : ℤ) * (acc m i : ℤ) + (acc m i : ℤ) ^ 2) with hE
  -- The exponent is the ℤ-cast of the ℕ exponent of `fermBodyM`.
  have hexp : ∀ m : Fin (k - 1) → ℕ, E m
      = ((acc r k ^ 2 + ∑ i ∈ Icc 1 (k - 1), (acc r i ^ 2 + acc m i ^ 2 - acc r i * acc m i) : ℕ) : ℤ) := by
    intro m
    simp only [hE]
    push_cast
    rw [add_right_inj]
    apply Finset.sum_congr rfl
    intro i _
    have hle : acc r i * acc m i ≤ acc r i ^ 2 + acc m i ^ 2 := by
      nlinarith [Nat.zero_le (acc r i * acc m i), sq_nonneg ((acc r i : ℤ) - (acc m i : ℤ))]
    rw [Nat.cast_sub hle]
    push_cast
    ring
  have hTmem : ∀ m : Fin (k - 1) → ℕ, T (E m) ∈ LaurentNonneg := by
    intro m; rw [hexp m]; exact T_nat_mem _
  rw [transfer_sum_of_mem]
  · apply Finset.sum_congr rfl
    intro m hm
    -- Fold the term into `T (E m) * qChoose * ∏ qChoose` and transfer.
    rw [transfer_mul_of_mem
        (LaurentNonneg.mul_mem (hTmem m) (qChoose_qL_mem _ _))
        (Subsemiring.prod_mem _ (fun i _ => qChoose_qL_mem _ _))]
    rw [transfer_mul_of_mem (hTmem m) (qChoose_qL_mem _ _)]
    rw [hexp m, transfer_T, transfer_qChoose,
        transfer_prod_of_mem _ _ (fun i _ => qChoose_qL_mem _ _)]
    simp only [transfer_qChoose]
    rw [fermBodyM]
  · intro m hm
    exact LaurentNonneg.mul_mem
      (LaurentNonneg.mul_mem (hTmem m) (qChoose_qL_mem _ _))
      (Subsemiring.prod_mem _ (fun i _ => qChoose_qL_mem _ _))

/-- **Per-boundary transported Sum-to-Sum (minus): `SbMinus k r = ∑' m, fermBodyM k r m`.**
The analytic heart of the minus case, mirror of `cor_perR_plus`. -/
theorem cor_perR_minus (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ℕ) (hr : Antitone r)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) (hSym : Fact3 Stil) (hRecip : Fact5)
    (hQbin : Fact6) (hPD : Fact8 3 (3 * k - 1)) (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    SbMinus k r = ∑' m : Fin (k - 1) → ℕ, fermBodyM k r m := by
  rw [sbMinus_eq_finsum_azTransfer_minus Stil Tset invStat k hk r hr hRC hInv]
  rw [finsum_azTransfer_minus_eq_tsum_azContent k hk r hr]
  rw [tsum_fermBodyM_by_content k r]
  refine tsum_congr (fun M => ?_)
  exact azContent_eq_fermBody_finset_minus Stil Tset invStat tabOf Ja Jz k hk r hr M
    hRC hInv hSym hRecip hQbin hInvComp


/-! ## Lemma 3.5 reassembly (Statement 6): decomposition into the per-`n` telescoping kernel
plus the `r`-partition/Fubini reassembly.  Placed here (after all gap-coordinate infrastructure
`rOfGap`/`fiberEquivAZ`/`cor_perR_plus`) so the sub-lemmas can reference it. -/

/-- **Outer boundary factor** `(1/(q)_{r₁})·∏_{i=1}^{k-1}[r_i;r_{i+1}]` (Remark 3.6). -/
noncomputable def outerFactorP (k : ℕ) (r : Fin k → ℕ) : ℤ⟦X⟧ :=
  invOfUnit (qPochhammer qX qX (acc r 1)) 1
    * (∏ i ∈ Icc 1 (k - 1), qChoose qX (acc r i) (acc r (i + 1)))

/-! ### Layer 2 (research note `supply_the_hjo_lemma_3_5`): the summation-cone predicate.
`OnConeP k r a z` = `Antitone r` conjoined with the in-file `domAZ r (acc r k) a z`.  These
one-liner characterizing lemmas package the cone inequalities that the block telescoping needs
(all discharged from `acc_succ_le` + the `domAZ` components). -/

/-- **On-cone predicate (plus).**  The boundary tuple `r`, the `a`-tuple and `z`-tuple lie on
the HJO summation cone. -/
def OnConeP (k : ℕ) (r a z : Fin k → ℕ) : Prop :=
  Antitone r ∧ Antitone a ∧ acc a 1 ≤ acc r k ∧ Antitone z ∧
    (∀ i ∈ Icc 1 k, acc z i ≤ acc r i)

/-- `OnConeP` restricts to the in-file `domAZ` at boundary `s = acc r k`. -/
lemma OnConeP.domAZ {k : ℕ} {r a z : Fin k → ℕ} (h : OnConeP k r a z) :
    domAZ r (acc r k) a z :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- `Antitone r` component of `OnConeP`. -/
lemma OnConeP.antitone_r {k : ℕ} {r a z : Fin k → ℕ} (h : OnConeP k r a z) :
    Antitone r := h.1

/-- Successive `r`-difference nonnegativity: `acc r (i+1) ≤ acc r i`. -/
lemma OnConeP.rdiff {k : ℕ} {r a z : Fin k → ℕ} (h : OnConeP k r a z) {i : ℕ} (hi : 1 ≤ i) :
    acc r (i + 1) ≤ acc r i := acc_succ_le h.1 hi

/-- Successive `a`-difference nonnegativity: `acc a (i+1) ≤ acc a i`. -/
lemma OnConeP.adiff {k : ℕ} {r a z : Fin k → ℕ} (h : OnConeP k r a z) {i : ℕ} (hi : 1 ≤ i) :
    acc a (i + 1) ≤ acc a i := acc_succ_le h.2.1 hi

/-- Successive `z`-difference nonnegativity: `acc z (i+1) ≤ acc z i`. -/
lemma OnConeP.zdiff {k : ℕ} {r a z : Fin k → ℕ} (h : OnConeP k r a z) {i : ℕ} (hi : 1 ≤ i) :
    acc z (i + 1) ≤ acc z i := acc_succ_le h.2.2.2.1 hi

/-- Pointwise `z ≤ r` on the cone. -/
lemma OnConeP.rz {k : ℕ} {r a z : Fin k → ℕ} (h : OnConeP k r a z) {i : ℕ}
    (hi : i ∈ Icc 1 k) : acc z i ≤ acc r i := h.2.2.2.2 i hi

/-- The `a`-boundary bound `acc a 1 ≤ acc r k`. -/
lemma OnConeP.a1_le_rk {k : ℕ} {r a z : Fin k → ℕ} (h : OnConeP k r a z) :
    acc a 1 ≤ acc r k := h.2.2.1

/-! ### Layers 3–6 (research note `supply_the_hjo_lemma_3_5`): block products, telescoping,
off-cone vanishing, and the final `by_cases` assembly of the kernel.  These are sorry-stubbed
here and attacked as an AND decomposition of `multiplicand_term_eq_plus`.  Notation used:
`P t := qPochhammer qX qX t`, `invP t := invOfUnit (qPochhammer qX qX t) 1`; the recovered
`multiplicand` body is
`multiplicand G a b n i = extendedSelfQPochhammer (n i - extend n (i-(a+b)))
   · extendedSelfQPochhammerInv (n i - extend n (i-a)) · extendedSelfQPochhammerInv (n i - extend n (i-b))`
with `extendedSelfQPochhammer m = if 0 ≤ m then (X;X)_{m.toNat} else 0`. -/

/-- **Telescoping helper.** For any `f : ℕ → ℕ` weakly decreasing on `[1, m]`
(`∀ i ∈ Icc 1 m, f (i+1) ≤ f i`), the Gaussian-binomial product telescopes:
`invP (f 1) · ∏_{i∈[1,m]} qChoose (f i) (f (i+1)) = invP (f (m+1)) · ∏_{i∈[1,m]} invP (f i − f (i+1))`.
Proved by induction on `m` using `qChoose_as_inv_poch` and `poch_mul_inv`. -/
lemma telescope_qChoose (hQbin : Fact6) (f : ℕ → ℕ) :
    ∀ m : ℕ, (∀ i ∈ Icc 1 m, f (i + 1) ≤ f i) →
      invOfUnit (qPochhammer qX qX (f 1)) 1
          * ∏ i ∈ Icc 1 m, qChoose qX (f i) (f (i + 1))
        = invOfUnit (qPochhammer qX qX (f (m + 1))) 1
            * ∏ i ∈ Icc 1 m, invOfUnit (qPochhammer qX qX (f i - f (i + 1))) 1 := by
  intro m
  induction m with
  | zero =>
      intro _
      simp
  | succ n ih =>
      intro hmono
      have hmono' : ∀ i ∈ Icc 1 n, f (i + 1) ≤ f i := by
        intro i hi
        rw [Finset.mem_Icc] at hi
        exact hmono i (by rw [Finset.mem_Icc]; omega)
      have hlast : f (n + 1 + 1) ≤ f (n + 1) := hmono (n + 1) (by rw [Finset.mem_Icc]; omega)
      rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1),
          Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
      rw [← mul_assoc, ih hmono', mul_assoc]
      rw [qChoose_as_inv_poch hQbin (f (n + 1)) (f (n + 1 + 1)) hlast]
      have hpi := poch_mul_inv (f (n + 1))
      set A := ∏ i ∈ Icc 1 n, invOfUnit (qPochhammer qX qX (f i - f (i + 1))) 1 with hA
      set B := invOfUnit (qPochhammer qX qX (f (n + 1 + 1))) 1 with hB
      set C := invOfUnit (qPochhammer qX qX (f (n + 1) - f (n + 1 + 1))) 1 with hC
      set D := invOfUnit (qPochhammer qX qX (f (n + 1))) 1 with hD
      set PP := qPochhammer qX qX (f (n + 1)) with hPP
      -- goal: D * (A * (PP * B * C)) = B * (A * C), with PP * D = 1
      have key : D * (A * (PP * B * C)) = (PP * D) * (B * (A * C)) := by ring
      rw [key, hpi, one_mul]

/-- **Layer 4 (telescoping): `outerFactorP` expansion.**  On an antitone `r`, the outer boundary
factor telescopes into `invP (acc r k) · ∏_{i∈[1,k-1]} invP (acc r i − acc r (i+1))`. -/
lemma outerFactorP_expand (k : ℕ) (hk : 1 ≤ k) (r : Fin k → ℕ) (hr : Antitone r)
    (hQbin : Fact6) :
    outerFactorP k r
      = invOfUnit (qPochhammer qX qX (acc r k)) 1
          * ∏ i ∈ Icc 1 (k - 1),
              invOfUnit (qPochhammer qX qX (acc r i - acc r (i + 1))) 1 := by
  have hmono : ∀ i ∈ Icc 1 (k - 1), acc r (i + 1) ≤ acc r i := by
    intro i hi
    exact acc_succ_le hr (Finset.mem_Icc.1 hi).1
  have hkey := telescope_qChoose hQbin (acc r) (k - 1) hmono
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1] at hkey
  rw [outerFactorP]
  exact hkey

/-- **Layer 4 (telescoping): `a`-Gaussian block expansion.** -/
lemma aGaussianBlock_expand (k : ℕ) (hk : 1 ≤ k) (r a : Fin k → ℕ) (ha : Antitone a)
    (ha1 : acc a 1 ≤ acc r k) (hQbin : Fact6) :
    (∏ i ∈ Icc 1 k, qChoose qX (aacc (acc r k) a (i - 1)) (acc a i))
      = qPochhammer qX qX (acc r k)
          * invOfUnit (qPochhammer qX qX (acc r k - acc a 1)) 1
          * ∏ i ∈ Icc 1 k, invOfUnit (qPochhammer qX qX (acc a i - acc a (i + 1))) 1 := by
  -- abbreviations
  set Prk := qPochhammer qX qX (acc r k) with hPrk
  -- acc a (k+1) = 0 since k+1 is out of range for a : Fin k → ℕ
  have hak1 : acc a (k + 1) = 0 := by
    rw [acc]; rw [dif_neg]; omega
  -- boundary condition for the first term
  have haccdec : ∀ i ∈ Icc 1 (k - 1), acc a (i + 1) ≤ acc a i := by
    intro i hi
    exact acc_succ_le ha (Finset.mem_Icc.1 hi).1
  -- The telescope of the tail (running index shifted): use telescope_qChoose on acc a with m = k-1
  have htel := telescope_qChoose hQbin (acc a) (k - 1) haccdec
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1] at htel
  -- STEP 1: split LHS into the i=1 term and the tail over Icc 2 k, reindexed to Icc 1 (k-1).
  have hLsplit :
      (∏ i ∈ Icc 1 k, qChoose qX (aacc (acc r k) a (i - 1)) (acc a i))
        = qChoose qX (acc r k) (acc a 1)
            * ∏ j ∈ Icc 1 (k - 1), qChoose qX (acc a j) (acc a (j + 1)) := by
    rw [show (Icc 1 k) = insert 1 (Icc 2 k) by
          ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega]
    rw [Finset.prod_insert (by simp only [Finset.mem_Icc]; omega)]
    -- first factor: aacc (acc r k) a (1-1) = acc r k
    have hfst : aacc (acc r k) a (1 - 1) = acc r k := by rw [aacc, if_pos rfl]
    rw [hfst]
    congr 1
    -- reindex tail Icc 2 k → Icc 1 (k-1) by i ↦ i-1
    apply Finset.prod_bij' (fun (i : ℕ) (_ : i ∈ Icc 2 k) => i - 1)
      (fun (j : ℕ) (_ : j ∈ Icc 1 (k - 1)) => j + 1)
    · intro i hi; simp only [Finset.mem_Icc] at *; omega
    · intro j hj; simp only [Finset.mem_Icc] at *; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi; omega
    · intro j hj; simp only [Finset.mem_Icc] at hj; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi
      have haacc2 : aacc (acc r k) a (i - 1) = acc a (i - 1) := by
        rw [aacc, if_neg (by omega)]
      rw [haacc2, show i - 1 + 1 = i by omega]
  -- STEP 2: expand telescope of the tail. From htel:
  --   invP(acc a 1) · ∏_{Icc 1 (k-1)} qChoose (acc a j)(acc a (j+1))
  --     = invP(acc a k) · ∏_{Icc 1 (k-1)} invP(acc a j - acc a (j+1))
  -- multiply both sides by P(acc a 1) to solve for the product.
  have hPa1 := poch_mul_inv (acc a 1)
  -- ∏ tail = P(acc a 1) · invP(acc a k) · ∏ invP(acc a j - acc a (j+1))
  have htail :
      (∏ j ∈ Icc 1 (k - 1), qChoose qX (acc a j) (acc a (j + 1)))
        = qPochhammer qX qX (acc a 1)
            * invOfUnit (qPochhammer qX qX (acc a k)) 1
            * ∏ j ∈ Icc 1 (k - 1), invOfUnit (qPochhammer qX qX (acc a j - acc a (j + 1))) 1 := by
    have := htel
    -- multiply telescope identity by P(acc a 1)
    have h2 : qPochhammer qX qX (acc a 1)
          * (invOfUnit (qPochhammer qX qX (acc a 1)) 1
              * ∏ j ∈ Icc 1 (k - 1), qChoose qX (acc a j) (acc a (j + 1)))
        = qPochhammer qX qX (acc a 1)
          * (invOfUnit (qPochhammer qX qX (acc a k)) 1
              * ∏ j ∈ Icc 1 (k - 1), invOfUnit (qPochhammer qX qX (acc a j - acc a (j + 1))) 1) := by
      rw [this]
    -- simplify LHS of h2 using P·invP = 1
    have hL2 : qPochhammer qX qX (acc a 1)
          * (invOfUnit (qPochhammer qX qX (acc a 1)) 1
              * ∏ j ∈ Icc 1 (k - 1), qChoose qX (acc a j) (acc a (j + 1)))
        = ∏ j ∈ Icc 1 (k - 1), qChoose qX (acc a j) (acc a (j + 1)) := by
      rw [← mul_assoc, hPa1, one_mul]
    rw [hL2] at h2
    rw [h2]; ring
  -- STEP 3: expand the first qChoose factor: qChoose (acc r k)(acc a 1) via qChoose_as_inv_poch.
  have hfstexp := qChoose_as_inv_poch hQbin (acc r k) (acc a 1) ha1
  -- STEP 4: peel the last term of the RHS product ∏_{Icc 1 k} invP(acc a i - acc a (i+1)).
  have hRHSprod :
      (∏ i ∈ Icc 1 k, invOfUnit (qPochhammer qX qX (acc a i - acc a (i + 1))) 1)
        = (∏ i ∈ Icc 1 (k - 1), invOfUnit (qPochhammer qX qX (acc a i - acc a (i + 1))) 1)
            * invOfUnit (qPochhammer qX qX (acc a k)) 1 := by
    rw [show (Icc 1 k) = insert k (Icc 1 (k - 1)) by
          ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega]
    rw [Finset.prod_insert (by simp only [Finset.mem_Icc]; omega)]
    rw [mul_comm]
    congr 2
    -- last term: acc a (k+1) = 0, so acc a k - acc a (k+1) = acc a k
    rw [hak1, Nat.sub_zero]
  -- ASSEMBLE.
  rw [hLsplit, htail, hfstexp, hRHSprod]
  -- Now goal is a pure unit-algebra identity; cancel P(acc a 1)·invP(acc a 1)=1.
  set Pa1 := qPochhammer qX qX (acc a 1) with hPa1def
  set IPa1 := invOfUnit (qPochhammer qX qX (acc a 1)) 1 with hIPa1def
  set IPak := invOfUnit (qPochhammer qX qX (acc a k)) 1 with hIPak
  set IPrka1 := invOfUnit (qPochhammer qX qX (acc r k - acc a 1)) 1 with hIPrka1
  set TP := ∏ i ∈ Icc 1 (k - 1), invOfUnit (qPochhammer qX qX (acc a i - acc a (i + 1))) 1 with hTP
  -- goal: Prk * IPa1 * IPrka1 * (Pa1 * IPak * TP) = Prk * IPrka1 * (TP * IPak)
  have key : Prk * IPa1 * IPrka1 * (Pa1 * IPak * TP)
      = (Pa1 * IPa1) * (Prk * IPrka1 * (TP * IPak)) := by ring
  rw [key, hPa1, one_mul]

/-- **Layer 4 (telescoping): `z`-Gaussian block expansion.** -/
lemma zGaussianBlock_expand (k : ℕ) (hk : 1 ≤ k) (r z : Fin k → ℕ) (hz : Antitone z)
    (hzr : ∀ i ∈ Icc 1 k, acc z i ≤ acc r i) (hQbin : Fact6) :
    (∏ i ∈ Icc 1 k, qChoose qX (acc r i - acc z (i + 1)) (acc z i - acc z (i + 1)))
      = ∏ i ∈ Icc 1 k,
          qPochhammer qX qX (acc r i - acc z (i + 1))
            * invOfUnit (qPochhammer qX qX (acc z i - acc z (i + 1))) 1
            * invOfUnit (qPochhammer qX qX (acc r i - acc z i)) 1 := by
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  have hzsucc : acc z (i + 1) ≤ acc z i := acc_succ_le hz hi1
  have hzri : acc z i ≤ acc r i := hzr i hi
  have hjleN : acc z i - acc z (i + 1) ≤ acc r i - acc z (i + 1) := by omega
  have hNj : (acc r i - acc z (i + 1)) - (acc z i - acc z (i + 1)) = acc r i - acc z i := by omega
  rw [qChoose_as_inv_poch hQbin _ _ hjleN, hNj]

/-- `extend` of a ℕ-cast gap-vector equals the ℕ-cast of `extendNat`. -/
lemma extend_natCast {G : Finset ℕ} (nn : G → ℕ) (m : ℕ) :
    HJO.extend (fun i => (nn i : ℤ)) m = (HJO.extendNat nn m : ℤ) := by
  unfold HJO.extend HJO.extendNat
  split <;> simp

/-- `extendedSelfQPochhammer` of a nonnegative ℕ-cast difference is `P (p-q)`. -/
lemma ESQ_natCast_sub (p q : ℕ) (h : q ≤ p) :
    HJO.extendedSelfQPochhammer ((p : ℤ) - (q : ℤ)) = qPochhammer qX qX (p - q) := by
  unfold HJO.extendedSelfQPochhammer
  rw [if_pos (by omega)]
  have hh : ((p : ℤ) - (q : ℤ)).toNat = p - q := by omega
  rw [hh]

/-- `extendedSelfQPochhammerInv` of a nonnegative ℕ-cast difference is `invP (p-q)`. -/
lemma ESQInv_natCast_sub (p q : ℕ) (h : q ≤ p) :
    HJO.extendedSelfQPochhammerInv ((p : ℤ) - (q : ℤ))
      = invOfUnit (qPochhammer qX qX (p - q)) 1 := by
  unfold HJO.extendedSelfQPochhammerInv
  rw [if_pos (by omega)]
  have hh : ((p : ℤ) - (q : ℤ)).toNat = p - q := by omega
  rw [hh]

-- Layer 3 (raw block factorization): on the cone, the raw multiplicand product
-- factors via the gapEquiv reindexing into the Z/A/R blocks.
/-- Value of `gapEquiv` on the three blocks equals `gapSub` (definitional via `ofBijective`). -/
lemma gapEquiv_eq_gapSub (k : ℕ) (x : Fin k ⊕ Fin k ⊕ Fin k) :
    gapEquiv k x = gapSub k x := rfl

/-- Z-block factor of the raw multiplicand product. -/
lemma multiplicand_zfactor (k : ℕ) (hk : 1 ≤ k)
    (n : (finspan {3, 3 * k + 1}).gaps → ℕ)
    (hcone : OnConeP k (rOfGap k n) (aOfGap k n) (zOfGap k n)) (j : Fin k) :
    HJO.multiplicand (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) (fun i => (n i : ℤ))
        (gapEquiv k (Sum.inl j))
      = invOfUnit (qPochhammer qX qX (acc (zOfGap k n) (j + 1) - acc (zOfGap k n) (j + 2))) 1 := by
  set z := zOfGap k n with hz
  have hval : (gapEquiv k (Sum.inl j) : ℕ) = 3 * (k - 1 - (j : ℕ)) + 1 := rfl
  have hnj : (n (gapEquiv k (Sum.inl j)) : ℤ) = (acc z (j + 1) : ℤ) := by
    have : n (gapEquiv k (Sum.inl j)) = z j := rfl
    rw [this, acc_val z ((j : ℕ) + 1) (by omega) (by have := j.2; omega)]
    congr 1
  -- successive z decrease (antitone)
  have hzdec : acc z (↑j + 2) ≤ acc z (↑j + 1) :=
    acc_succ_le hcone.2.2.2.1 (by omega)
  set x := k - 1 - (j : ℕ) with hx
  have hxk : x < k := by have := j.2; omega
  unfold HJO.multiplicand
  beta_reduce
  rw [hnj]
  -- reduce the three extend arguments
  have hE1 : HJO.extend (fun i => (n i : ℤ)) ((gapEquiv k (Sum.inl j) : ℕ) - (3 + (3 * k + 1))) = 0 := by
    rw [hval, show 3 * (k - 1 - (j : ℕ)) + 1 - (3 + (3 * k + 1)) = 0 by omega,
      extend_natCast, HJO.extendNat_gaps_zero]; simp
  have hE2 : HJO.extend (fun i => (n i : ℤ)) ((gapEquiv k (Sum.inl j) : ℕ) - 3)
      = (acc z (↑j + 2) : ℤ) := by
    rw [hval, show 3 * (k - 1 - (j : ℕ)) + 1 - 3 = 3 * x - 2 by rw [hx]; omega,
      extend_natCast, extendNat_zshift_read k n x hxk, hx,
      show k - (k - 1 - (j : ℕ)) + 1 = (j : ℕ) + 2 by omega]
  have hE3 : HJO.extend (fun i => (n i : ℤ)) ((gapEquiv k (Sum.inl j) : ℕ) - (3 * k + 1)) = 0 := by
    rw [hval, show 3 * (k - 1 - (j : ℕ)) + 1 - (3 * k + 1) = 0 by omega,
      extend_natCast, HJO.extendNat_gaps_zero]; simp
  rw [hE1, hE2, hE3]
  rw [show (0:ℤ) = ((0:ℕ):ℤ) from rfl]
  rw [ESQ_natCast_sub (acc z (↑j+1)) 0 (by omega), Nat.sub_zero,
    ESQInv_natCast_sub (acc z (↑j+1)) (acc z (↑j+2)) hzdec,
    ESQInv_natCast_sub (acc z (↑j+1)) 0 (by omega), Nat.sub_zero]
  -- P(z_{j+1}) * invP(z_{j+1}-z_{j+2}) * invP(z_{j+1}) = invP(z_{j+1}-z_{j+2})
  have hpi := poch_mul_inv (acc z (↑j+1))
  set A := invOfUnit (qPochhammer qX qX (acc z (↑j+1) - acc z (↑j+2))) 1 with hA
  set P := qPochhammer qX qX (acc z (↑j+1)) with hP
  set IP := invOfUnit (qPochhammer qX qX (acc z (↑j+1))) 1 with hIP
  calc P * A * IP = (P * IP) * A := by ring
    _ = A := by rw [hpi, one_mul]

lemma multiplicand_afactor (k : ℕ) (hk : 1 ≤ k)
    (n : (finspan {3, 3 * k + 1}).gaps → ℕ)
    (hcone : OnConeP k (rOfGap k n) (aOfGap k n) (zOfGap k n)) (j : Fin k) :
    HJO.multiplicand (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) (fun i => (n i : ℤ))
        (gapEquiv k (Sum.inr (Sum.inl j)))
      = invOfUnit (qPochhammer qX qX (acc (aOfGap k n) (j + 1) - acc (aOfGap k n) (j + 2))) 1 := by
  set a := aOfGap k n with ha
  have hval : (gapEquiv k (Sum.inr (Sum.inl j)) : ℕ) = 3 * (k - 1 - (j : ℕ)) + 2 := rfl
  have hnj : (n (gapEquiv k (Sum.inr (Sum.inl j))) : ℤ) = (acc a (j + 1) : ℤ) := by
    have : n (gapEquiv k (Sum.inr (Sum.inl j))) = a j := rfl
    rw [this, acc_val a ((j : ℕ) + 1) (by omega) (by have := j.2; omega)]
    congr 1
  have hadec : acc a (↑j + 2) ≤ acc a (↑j + 1) :=
    acc_succ_le hcone.2.1 (by omega)
  set x := k - 1 - (j : ℕ) with hx
  have hxk : x < k := by have := j.2; omega
  unfold HJO.multiplicand
  beta_reduce
  rw [hnj]
  have hE1 : HJO.extend (fun i => (n i : ℤ)) ((gapEquiv k (Sum.inr (Sum.inl j)) : ℕ) - (3 + (3 * k + 1))) = 0 := by
    rw [hval, show 3 * (k - 1 - (j : ℕ)) + 2 - (3 + (3 * k + 1)) = 0 by omega,
      extend_natCast, HJO.extendNat_gaps_zero]; simp
  have hE2 : HJO.extend (fun i => (n i : ℤ)) ((gapEquiv k (Sum.inr (Sum.inl j)) : ℕ) - 3)
      = (acc a (↑j + 2) : ℤ) := by
    rw [hval, show 3 * (k - 1 - (j : ℕ)) + 2 - 3 = 3 * x - 1 by rw [hx]; omega,
      extend_natCast, extendNat_ashift_down_read k n x hxk, hx,
      show k - (k - 1 - (j : ℕ)) + 1 = (j : ℕ) + 2 by omega]
  have hE3 : HJO.extend (fun i => (n i : ℤ)) ((gapEquiv k (Sum.inr (Sum.inl j)) : ℕ) - (3 * k + 1)) = 0 := by
    rw [hval, show 3 * (k - 1 - (j : ℕ)) + 2 - (3 * k + 1) = 0 by omega,
      extend_natCast, HJO.extendNat_gaps_zero]; simp
  rw [hE1, hE2, hE3]
  rw [show (0:ℤ) = ((0:ℕ):ℤ) from rfl]
  rw [ESQ_natCast_sub (acc a (↑j+1)) 0 (by omega), Nat.sub_zero,
    ESQInv_natCast_sub (acc a (↑j+1)) (acc a (↑j+2)) hadec,
    ESQInv_natCast_sub (acc a (↑j+1)) 0 (by omega), Nat.sub_zero]
  have hpi := poch_mul_inv (acc a (↑j+1))
  set A := invOfUnit (qPochhammer qX qX (acc a (↑j+1) - acc a (↑j+2))) 1 with hA
  set P := qPochhammer qX qX (acc a (↑j+1)) with hP
  set IP := invOfUnit (qPochhammer qX qX (acc a (↑j+1))) 1 with hIP
  calc P * A * IP = (P * IP) * A := by ring
    _ = A := by rw [hpi, one_mul]

lemma multiplicand_rfactor (k : ℕ) (hk : 1 ≤ k)
    (n : (finspan {3, 3 * k + 1}).gaps → ℕ)
    (hcone : OnConeP k (rOfGap k n) (aOfGap k n) (zOfGap k n)) (j : Fin k) :
    HJO.multiplicand (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) (fun i => (n i : ℤ))
        (gapEquiv k (Sum.inr (Sum.inr j)))
      = qPochhammer qX qX (acc (rOfGap k n) (j + 1) - acc (zOfGap k n) (j + 2))
        * invOfUnit (qPochhammer qX qX
            (acc (rOfGap k n) (j + 1)
              - (if (j : ℕ) + 1 < k then acc (rOfGap k n) (j + 2) else acc (aOfGap k n) 1))) 1
        * invOfUnit (qPochhammer qX qX
            (acc (rOfGap k n) (j + 1) - acc (zOfGap k n) (j + 1))) 1 := by
  set r := rOfGap k n with hr
  set a := aOfGap k n with ha
  set z := zOfGap k n with hz
  have hval : (gapEquiv k (Sum.inr (Sum.inr j)) : ℕ) = 6 * k - 1 - 3 * (j : ℕ) := rfl
  have hnj : (n (gapEquiv k (Sum.inr (Sum.inr j))) : ℤ) = (acc r (j + 1) : ℤ) := by
    have : n (gapEquiv k (Sum.inr (Sum.inr j))) = r j := rfl
    rw [this, acc_val r ((j : ℕ) + 1) (by omega) (by have := j.2; omega)]
    congr 1
  set x := k - 1 - (j : ℕ) with hx
  have hxk : x < k := by have := j.2; omega
  -- successive inequalities on the cone
  have hjlt : (j : ℕ) < k := j.2
  -- arg1 = 3x - 2 → acc z (j+2)
  have hE1 : HJO.extend (fun i => (n i : ℤ)) ((gapEquiv k (Sum.inr (Sum.inr j)) : ℕ) - (3 + (3 * k + 1)))
      = (acc z ((j : ℕ) + 2) : ℤ) := by
    rw [hval, show 6 * k - 1 - 3 * (j : ℕ) - (3 + (3 * k + 1)) = 3 * x - 2 by rw [hx]; omega,
      extend_natCast, extendNat_zshift_read k n x hxk, hz,
      show k - x + 1 = (j : ℕ) + 2 by rw [hx]; omega]
  -- arg3 = 3x + 1 → acc z (j+1)
  have hE3 : HJO.extend (fun i => (n i : ℤ)) ((gapEquiv k (Sum.inr (Sum.inr j)) : ℕ) - (3 * k + 1))
      = (acc z ((j : ℕ) + 1) : ℤ) := by
    rw [hval, show 6 * k - 1 - 3 * (j : ℕ) - (3 * k + 1) = 3 * x + 1 by rw [hx]; omega,
      extend_natCast, extendNat_z_read k n x hxk, hz,
      show k - x = (j : ℕ) + 1 by rw [hx]; omega]
  -- arg2 = 6k-4-3j → if j+1<k then acc r (j+2) else acc a 1
  have hE2 : HJO.extend (fun i => (n i : ℤ)) ((gapEquiv k (Sum.inr (Sum.inr j)) : ℕ) - 3)
      = (↑(if (j : ℕ) + 1 < k then acc r ((j : ℕ) + 2) else acc a 1) : ℤ) := by
    rw [hval]
    by_cases hjk : (j : ℕ) + 1 < k
    · -- interior: 6k-4-3j = 6k-1-3(j+1) = R gap at index (j+1) = r (j+1) = acc r (j+2)
      rw [if_pos hjk]
      have hset : 6 * k - 1 - 3 * (j : ℕ) - 3
          = 6 * k - 1 - 3 * (((⟨(j : ℕ) + 1, by omega⟩ : Fin k)) : ℕ) := by
        simp only [Fin.val_mk]; omega
      rw [hset, extend_natCast]
      have : HJO.extendNat n (6 * k - 1 - 3 * (((⟨(j : ℕ) + 1, by omega⟩ : Fin k)) : ℕ))
          = r (⟨(j : ℕ) + 1, by omega⟩ : Fin k) := by
        rw [hr, rOfGap_apply]
        rw [HJO.extendNat_of_mem (memR_plus k (⟨(j : ℕ) + 1, by omega⟩ : Fin k))]
        apply congrArg n
        apply Subtype.ext
        simp only [gapEquiv, gapSub, Equiv.ofBijective_apply]
      rw [this, acc_val r ((j : ℕ) + 2) (by omega) (by omega)]
      norm_cast
    · -- boundary j = k-1: 6k-4-3(k-1) = 3k-1 = 3*(k-1)+2 = a gap at index (k-1) = acc a 1
      rw [if_neg hjk]
      have hjeq : (j : ℕ) = k - 1 := by omega
      have hset : 6 * k - 1 - 3 * (j : ℕ) - 3 = 3 * (k - 1) + 2 := by omega
      rw [hset, extend_natCast, extendNat_a_read k n (k - 1) (by omega), ha,
        show k - (k - 1) = 1 by omega]
  unfold HJO.multiplicand
  beta_reduce
  rw [hnj, hE1, hE2, hE3]
  -- now reduce ESQ / ESQInv
  have hzr_j1 : acc z ((j : ℕ) + 1) ≤ acc r ((j : ℕ) + 1) := by
    have := hcone.rz (i := (j : ℕ) + 1) (by simp only [Finset.mem_Icc]; omega)
    simpa [hr, hz] using this
  have hz2le1 : acc z ((j : ℕ) + 2) ≤ acc z ((j : ℕ) + 1) := by
    have := acc_succ_le hcone.2.2.2.1 (show 1 ≤ (j : ℕ) + 1 by omega)
    simpa [hz] using this
  have hz2le_r : acc z ((j : ℕ) + 2) ≤ acc r ((j : ℕ) + 1) := le_trans hz2le1 hzr_j1
  -- the middle term nonnegativity
  have hmidle : (if (j : ℕ) + 1 < k then acc r ((j : ℕ) + 2) else acc a 1)
      ≤ acc r ((j : ℕ) + 1) := by
    by_cases hjk : (j : ℕ) + 1 < k
    · rw [if_pos hjk]
      have := acc_succ_le hcone.1 (show 1 ≤ (j : ℕ) + 1 by omega)
      simpa [hr] using this
    · rw [if_neg hjk]
      have hjeq : (j : ℕ) = k - 1 := by omega
      have h1 : acc a 1 ≤ acc r k := hcone.a1_le_rk
      have : acc r ((j : ℕ) + 1) = acc r k := by rw [hjeq]; congr 1; omega
      rw [this]; simpa [hr] using h1
  rw [ESQ_natCast_sub (acc r ((j : ℕ)+1)) (acc z ((j : ℕ)+2)) hz2le_r,
    ESQInv_natCast_sub (acc r ((j : ℕ)+1)) _ hmidle,
    ESQInv_natCast_sub (acc r ((j : ℕ)+1)) (acc z ((j : ℕ)+1)) hzr_j1]

/-- Reindex a product over `Fin k` (through `j ↦ j+1`) to a product over `Icc 1 k`. -/
lemma prod_fin_shift_eq_Icc {M : Type*} [CommMonoid M] (k : ℕ) (g : ℕ → M) :
    (∏ j : Fin k, g ((j : ℕ) + 1)) = ∏ i ∈ Icc 1 k, g i := by
  rw [Fin.prod_univ_eq_prod_range (fun x => g (x + 1)) k]
  refine Finset.prod_nbij' (fun x : ℕ => x + 1) (fun i : ℕ => i - 1) ?_ ?_ ?_ ?_ ?_
  · intro x hx; simp only [Finset.mem_range, Finset.mem_Icc] at *; omega
  · intro i hi; simp only [Finset.mem_range, Finset.mem_Icc] at *; omega
  · intro x hx; simp only [Finset.mem_range] at hx; omega
  · intro i hi; simp only [Finset.mem_Icc] at hi; omega
  · intro x hx; rfl

lemma pochProduct_eq_outer_lhsFactors_onCone (k : ℕ) (hk : 1 ≤ k) (hQbin : Fact6)
    (n : (finspan {3, 3 * k + 1}).gaps → ℕ)
    (hcone : OnConeP k (rOfGap k n) (aOfGap k n) (zOfGap k n)) :
    (∏ i, HJO.multiplicand (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) (fun i => (n i : ℤ)) i)
      = outerFactorP k (rOfGap k n)
          * (∏ i ∈ Icc 1 k,
              qChoose qX (aacc (acc (rOfGap k n) k) (aOfGap k n) (i - 1)) (acc (aOfGap k n) i))
          * (∏ i ∈ Icc 1 k,
              qChoose qX (acc (rOfGap k n) i - acc (zOfGap k n) (i + 1))
                (acc (zOfGap k n) i - acc (zOfGap k n) (i + 1))) := by
  set r := rOfGap k n with hr
  set a := aOfGap k n with ha
  set z := zOfGap k n with hz
  -- ============ LHS: reindex through gapEquiv and split into Z/A/R blocks ============
  have hLHS :
      (∏ i, HJO.multiplicand (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) (fun i => (n i : ℤ)) i)
        = (∏ i ∈ Icc 1 k, invOfUnit (qPochhammer qX qX (acc z i - acc z (i + 1))) 1)
          * ((∏ i ∈ Icc 1 k, invOfUnit (qPochhammer qX qX (acc a i - acc a (i + 1))) 1)
            * (∏ i ∈ Icc 1 k,
                qPochhammer qX qX (acc r i - acc z (i + 1))
                  * invOfUnit (qPochhammer qX qX
                      (acc r i - (if i < k then acc r (i + 1) else acc a 1))) 1
                  * invOfUnit (qPochhammer qX qX (acc r i - acc z i)) 1)) := by
    rw [← Equiv.prod_comp (gapEquiv k)
      (fun x => HJO.multiplicand (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) (fun i => (n i : ℤ)) x)]
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    -- rewrite each block factor via the helpers
    rw [Finset.prod_congr rfl (fun j _ => multiplicand_zfactor k hk n hcone j)]
    rw [Finset.prod_congr rfl (fun j _ => multiplicand_afactor k hk n hcone j)]
    rw [Finset.prod_congr rfl (fun j _ => multiplicand_rfactor k hk n hcone j)]
    -- now reindex each Fin k product to Icc 1 k via j ↦ j+1
    rw [show (fun (j : Fin k) =>
        invOfUnit (qPochhammer qX qX (acc z ((j : ℕ) + 1) - acc z ((j : ℕ) + 2))) 1)
        = (fun (j : Fin k) => (fun i => invOfUnit (qPochhammer qX qX (acc z i - acc z (i + 1))) 1) ((j : ℕ) + 1))
        from by funext j; norm_num]
    rw [prod_fin_shift_eq_Icc k (fun i => invOfUnit (qPochhammer qX qX (acc z i - acc z (i + 1))) 1)]
    rw [show (fun (j : Fin k) =>
        invOfUnit (qPochhammer qX qX (acc a ((j : ℕ) + 1) - acc a ((j : ℕ) + 2))) 1)
        = (fun (j : Fin k) => (fun i => invOfUnit (qPochhammer qX qX (acc a i - acc a (i + 1))) 1) ((j : ℕ) + 1))
        from by funext j; norm_num]
    rw [prod_fin_shift_eq_Icc k (fun i => invOfUnit (qPochhammer qX qX (acc a i - acc a (i + 1))) 1)]
    rw [show (fun (j : Fin k) =>
        qPochhammer qX qX (acc r ((j : ℕ) + 1) - acc z ((j : ℕ) + 2))
          * invOfUnit (qPochhammer qX qX
              (acc r ((j : ℕ) + 1) - (if (j : ℕ) + 1 < k then acc r ((j : ℕ) + 2) else acc a 1))) 1
          * invOfUnit (qPochhammer qX qX (acc r ((j : ℕ) + 1) - acc z ((j : ℕ) + 1))) 1)
        = (fun (j : Fin k) => (fun i =>
            qPochhammer qX qX (acc r i - acc z (i + 1))
              * invOfUnit (qPochhammer qX qX (acc r i - (if i < k then acc r (i + 1) else acc a 1))) 1
              * invOfUnit (qPochhammer qX qX (acc r i - acc z i)) 1) ((j : ℕ) + 1))
        from by funext j; norm_num]
    rw [prod_fin_shift_eq_Icc k (fun i =>
        qPochhammer qX qX (acc r i - acc z (i + 1))
          * invOfUnit (qPochhammer qX qX (acc r i - (if i < k then acc r (i + 1) else acc a 1))) 1
          * invOfUnit (qPochhammer qX qX (acc r i - acc z i)) 1)]
  rw [hLHS]
  -- ============ RHS: expand the three qChoose blocks ============
  rw [outerFactorP_expand k hk r hcone.1 hQbin,
      aGaussianBlock_expand k hk r a hcone.2.1 hcone.a1_le_rk hQbin,
      zGaussianBlock_expand k hk r z hcone.2.2.2.1 hcone.2.2.2.2 hQbin]
  -- Split the z-Gaussian 3-factor product into three separate products.
  rw [show (∏ i ∈ Icc 1 k,
        qPochhammer qX qX (acc r i - acc z (i + 1))
          * invOfUnit (qPochhammer qX qX (acc z i - acc z (i + 1))) 1
          * invOfUnit (qPochhammer qX qX (acc r i - acc z i)) 1)
      = (∏ i ∈ Icc 1 k, qPochhammer qX qX (acc r i - acc z (i + 1)))
          * (∏ i ∈ Icc 1 k, invOfUnit (qPochhammer qX qX (acc z i - acc z (i + 1))) 1)
          * (∏ i ∈ Icc 1 k, invOfUnit (qPochhammer qX qX (acc r i - acc z i)) 1)
      from by rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]]
  -- Split the LHS R-block's 3-factor product likewise.
  rw [show (∏ i ∈ Icc 1 k,
        qPochhammer qX qX (acc r i - acc z (i + 1))
          * invOfUnit (qPochhammer qX qX (acc r i - (if i < k then acc r (i + 1) else acc a 1))) 1
          * invOfUnit (qPochhammer qX qX (acc r i - acc z i)) 1)
      = (∏ i ∈ Icc 1 k, qPochhammer qX qX (acc r i - acc z (i + 1)))
          * (∏ i ∈ Icc 1 k,
              invOfUnit (qPochhammer qX qX (acc r i - (if i < k then acc r (i + 1) else acc a 1))) 1)
          * (∏ i ∈ Icc 1 k, invOfUnit (qPochhammer qX qX (acc r i - acc z i)) 1)
      from by rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]]
  -- Split the R-block's "if" middle product at i=k into interior (i<k) and boundary (i=k).
  have hRmid :
      (∏ i ∈ Icc 1 k,
          invOfUnit (qPochhammer qX qX (acc r i - (if i < k then acc r (i + 1) else acc a 1))) 1)
        = (∏ i ∈ Icc 1 (k - 1), invOfUnit (qPochhammer qX qX (acc r i - acc r (i + 1))) 1)
            * invOfUnit (qPochhammer qX qX (acc r k - acc a 1)) 1 := by
    rw [show (Icc 1 k) = insert k (Icc 1 (k - 1)) by
          ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega]
    rw [Finset.prod_insert (by simp only [Finset.mem_Icc]; omega)]
    rw [if_neg (by omega), mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Finset.mem_Icc] at hi
    rw [if_pos (by omega)]
  rw [hRmid]
  -- Now everything is a product of P/invP scalars; cancel P(acc r k)·invP(acc r k)=1 and align by ring.
  have hpirk := poch_mul_inv (acc r k)
  -- name the atomic products so the final identity is a plain commutative-ring cancellation
  set Prk := qPochhammer qX qX (acc r k) with hPrk
  set IPrk := invOfUnit (qPochhammer qX qX (acc r k)) 1 with hIPrk
  set IPrka1 := invOfUnit (qPochhammer qX qX (acc r k - acc a 1)) 1 with hIPrka1
  set PZ := ∏ i ∈ Icc 1 k, qPochhammer qX qX (acc r i - acc z (i + 1)) with hPZ
  set ZZ := ∏ i ∈ Icc 1 k, invOfUnit (qPochhammer qX qX (acc z i - acc z (i + 1))) 1 with hZZ
  set RZ := ∏ i ∈ Icc 1 k, invOfUnit (qPochhammer qX qX (acc r i - acc z i)) 1 with hRZ
  set AA := ∏ i ∈ Icc 1 k, invOfUnit (qPochhammer qX qX (acc a i - acc a (i + 1))) 1 with hAA
  set RR := ∏ i ∈ Icc 1 (k - 1), invOfUnit (qPochhammer qX qX (acc r i - acc r (i + 1))) 1 with hRR
  rw [show IPrk * RR * (Prk * IPrka1 * AA) * (PZ * ZZ * RZ)
        = (Prk * IPrk) * (ZZ * (AA * (PZ * (RR * IPrka1) * RZ))) from by ring,
      hpirk, one_mul]

/-- **Layer 3 (raw block products) + Layer 4 collapse combined: on-cone kernel identity.**
On the cone, the product of the raw `multiplicand` factors (times `X^{Q(n)}`) equals
`outerFactorP k r` times the coerced `lhsTerm`.  Proved by factoring the `multiplicand`
product into the Z/A/R blocks (via `Finset.prod_nbij'` over `gapEquiv`), then applying the
three Gaussian expansions and cancelling the `P (acc r k)` boundary term. -/
lemma multiplicand_onCone_eq_plus (k : ℕ) (hk : 1 ≤ k) (hQbin : Fact6)
    (n : (finspan {3, 3 * k + 1}).gaps → ℕ)
    (hcone : OnConeP k (rOfGap k n) (aOfGap k n) (zOfGap k n)) :
    (∏ i, HJO.multiplicand (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) (fun i => (n i : ℤ)) i)
        * X ^ ((HJO.Q' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) (fun i => (n i : ℤ))).toNat)
      = outerFactorP k (rOfGap k n)
          * ((Polynomial.map (Nat.castRingHom ℤ)
              (HJO.SumToSum.ThreeOne.lhsTerm k (rOfGap k n)
                (finspan {3, 3 * k + 1}).gaps n)).toPowerSeries) := by
  set r := rOfGap k n with hr
  have hrAnti : Antitone r := hcone.1
  have hdom : domAZ r (acc r k) (aOfGap k n) (zOfGap k n) := hcone.domAZ
  -- Coercion ring hom `Φ = (·.toPowerSeries) ∘ (Polynomial.map (Nat.castRingHom ℤ))`.
  set Φ : Polynomial ℕ →+* ℤ⟦X⟧ :=
    (Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.mapRingHom (Nat.castRingHom ℤ)) with hΦ
  have hΦX : Φ Polynomial.X = (X : ℤ⟦X⟧) := by
    simp only [hΦ, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
  have hΦqc : ∀ (a b : ℕ), Φ (qChoose Polynomial.X a b) = qChoose qX a b := by
    intro a b; rw [qChoose_ringHom_map Φ Polynomial.X a b, hΦX]
  -- STEP A: reduce the RHS coerced `lhsTerm` to `X^Q · (a-Gaussian) · (z-Gaussian)`.
  have hcond : (∀ j : Fin k, HJO.extendNat n (6 * k - (3 * (j : ℕ) + 1)) = r j) := by
    rw [lhsTerm_support_iff_domAZ_plus k hk r n]
  -- The coercion of `lhsTerm` equals `Φ` applied to `lhsTermInner`.
  have hRHScoe : ((Polynomial.map (Nat.castRingHom ℤ)
        (HJO.SumToSum.ThreeOne.lhsTerm k r (finspan {3, 3 * k + 1}).gaps n)).toPowerSeries : ℤ⟦X⟧)
      = Φ (HJO.SumToSum.ThreeOne.lhsTerm k r (finspan {3, 3 * k + 1}).gaps n) := rfl
  rw [hRHScoe, HJO.SumToSum.ThreeOne.lhsTerm, if_pos hcond, HJO.SumToSum.ThreeOne.lhsTermInner]
  rw [map_mul, map_mul, map_pow, hΦX, map_prod, map_prod]
  rw [lhs_prod1_eq k hk r n hr.symm Φ hΦqc,
    lhs_prod2_eq k hk r hrAnti n hr.symm hdom Φ hΦqc]
  -- STEP B: rewrite the multiplicand product, then close by pure algebra (common `X^Q`).
  rw [pochProduct_eq_outer_lhsFactors_onCone k hk hQbin n hcone]
  ring

/-- **Layer 5 (off-cone RHS vanishing).**  Off the cone, `outerFactorP · lhsTerm = 0`. -/
lemma offCone_rhs_zero_plus (k : ℕ) (hk : 1 ≤ k)
    (n : (finspan {3, 3 * k + 1}).gaps → ℕ)
    (hnot : ¬ OnConeP k (rOfGap k n) (aOfGap k n) (zOfGap k n)) :
    outerFactorP k (rOfGap k n)
        * ((Polynomial.map (Nat.castRingHom ℤ)
            (HJO.SumToSum.ThreeOne.lhsTerm k (rOfGap k n)
              (finspan {3, 3 * k + 1}).gaps n)).toPowerSeries) = 0 := by
  -- SANITY CHECK PASSED: off-cone, either r is not antitone (outerFactorP factor vanishes)
  -- or domAZ fails (coerced lhsTerm vanishes via lhsTerm_vanish_of_not_domAZ).
  set r := rOfGap k n with hr
  by_cases hAr : Antitone r
  · -- Antitone r holds, so ¬ OnConeP ⟹ ¬ domAZ.  Kill the lhsTerm factor.
    have hdom : ¬ domAZ r (acc r k) (aOfGap k n) (zOfGap k n) := by
      intro hd
      exact hnot ⟨hAr, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2⟩
    rw [lhsTerm_vanish_of_not_domAZ k hk r hAr n hr.symm hdom, mul_zero]
  · -- r is not antitone: an outerFactorP qChoose factor vanishes.
    obtain ⟨i, hi1, hik, hlt⟩ := not_antitone_acc_succ hAr  -- acc r i < acc r (i+1)
    have hmem : i ∈ Icc 1 (k - 1) := by simp only [Finset.mem_Icc]; omega
    have hfac0 : qChoose qX (acc r i) (acc r (i + 1)) = 0 := qChoose_eq_zero_of_lt hlt
    rw [outerFactorP, Finset.prod_eq_zero hmem hfac0, mul_zero, zero_mul]

/-- **Bridge lemma (crux B).**  If the ℕ-cast gap-vector lies on the Axiomlib `cone'`, then the
extracted boundary/`a`/`z` tuples satisfy the in-file `OnConeP` predicate.  Each of the five
`OnConeP` conjuncts is one instance of a `cone'` monotonicity step (shift by `3` for the
Antitone/adjacency conditions, shift by `3k+1` for the `z ≤ r` condition), read off via the
explicit `gapSub` addresses. -/
lemma onCone_of_cone' (k : ℕ) (hk : 1 ≤ k)
    (n : (finspan {3, 3 * k + 1}).gaps → ℕ)
    (hcone : (fun i => (n i : ℤ)) ∈ HJO.cone' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1)) :
    OnConeP k (rOfGap k n) (aOfGap k n) (zOfGap k n) := by
  obtain ⟨-, hstep3, hstepK⟩ := hcone
  -- ℕ-level shift-by-3 monotonicity.
  have N3 : ∀ (i : (finspan {3, 3 * k + 1}).gaps) (h : ((i : ℕ) + 3) ∈ (finspan {3, 3 * k + 1}).gaps),
      n i ≤ n ⟨(i : ℕ) + 3, h⟩ := by
    intro i h
    have h2 := hstep3 i h
    simp only [] at h2
    exact_mod_cast h2
  -- ℕ-level shift-by-(3k+1) monotonicity.
  have NK : ∀ (i : (finspan {3, 3 * k + 1}).gaps) (h : ((i : ℕ) + (3 * k + 1)) ∈ (finspan {3, 3 * k + 1}).gaps),
      n i ≤ n ⟨(i : ℕ) + (3 * k + 1), h⟩ := by
    intro i h
    have h2 := hstepK i h
    simp only [] at h2
    exact_mod_cast h2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Antitone r
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Fin.antitone_iff_succ_le]
    intro j
    rw [rOfGap_apply, rOfGap_apply]
    show n ⟨6 * (k'+1) - 1 - 3 * (j.succ : ℕ), memR_plus (k'+1) j.succ⟩
        ≤ n ⟨6 * (k'+1) - 1 - 3 * (j.castSucc : ℕ), memR_plus (k'+1) j.castSucc⟩
    have hjlt : (j : ℕ) + 1 < (k'+1) := by have := j.2; omega
    have hmemS : (6 * (k'+1) - 1 - 3 * ((j : ℕ) + 1)) ∈ (finspan {3, 3 * (k'+1) + 1}).gaps := by
      have := memR_plus (k'+1) j.succ; simpa [Fin.val_succ] using this
    have haddr : (6 * (k'+1) - 1 - 3 * ((j : ℕ) + 1)) + 3 = 6 * (k'+1) - 1 - 3 * (j : ℕ) := by omega
    have hplus : (6 * (k'+1) - 1 - 3 * ((j : ℕ) + 1)) + 3 ∈ (finspan {3, 3 * (k'+1) + 1}).gaps := by
      rw [haddr]; exact memR_plus (k'+1) j.castSucc
    have hle := N3 ⟨6 * (k'+1) - 1 - 3 * ((j : ℕ) + 1), hmemS⟩ hplus
    have hsub : (⟨(6 * (k'+1) - 1 - 3 * ((j : ℕ) + 1)) + 3, hplus⟩ : (finspan {3, 3 * (k'+1) + 1}).gaps)
        = ⟨6 * (k'+1) - 1 - 3 * (j.castSucc : ℕ), memR_plus (k'+1) j.castSucc⟩ := by
      apply Subtype.ext; simp only [Fin.coe_castSucc]; omega
    rw [hsub] at hle
    have hmatch : (⟨6 * (k'+1) - 1 - 3 * (j.succ : ℕ), memR_plus (k'+1) j.succ⟩ : (finspan {3, 3 * (k'+1) + 1}).gaps)
        = ⟨6 * (k'+1) - 1 - 3 * ((j : ℕ) + 1), hmemS⟩ := by
      apply Subtype.ext; simp only [Fin.val_succ]
    rw [hmatch]; exact hle
  · -- Antitone a
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Fin.antitone_iff_succ_le]
    intro j
    rw [aOfGap_apply, aOfGap_apply]
    show n ⟨3 * ((k'+1) - 1 - (j.succ : ℕ)) + 2, memA_plus (k'+1) j.succ⟩
        ≤ n ⟨3 * ((k'+1) - 1 - (j.castSucc : ℕ)) + 2, memA_plus (k'+1) j.castSucc⟩
    have hjlt : (j : ℕ) + 1 < (k'+1) := by have := j.2; omega
    have hmemS : (3 * ((k'+1) - 1 - ((j : ℕ) + 1)) + 2) ∈ (finspan {3, 3 * (k'+1) + 1}).gaps := by
      have := memA_plus (k'+1) j.succ; simpa [Fin.val_succ] using this
    have haddr : (3 * ((k'+1) - 1 - ((j : ℕ) + 1)) + 2) + 3 = 3 * ((k'+1) - 1 - (j : ℕ)) + 2 := by omega
    have hplus : (3 * ((k'+1) - 1 - ((j : ℕ) + 1)) + 2) + 3 ∈ (finspan {3, 3 * (k'+1) + 1}).gaps := by
      rw [haddr]; exact memA_plus (k'+1) j.castSucc
    have hle := N3 ⟨3 * ((k'+1) - 1 - ((j : ℕ) + 1)) + 2, hmemS⟩ hplus
    have hsub : (⟨(3 * ((k'+1) - 1 - ((j : ℕ) + 1)) + 2) + 3, hplus⟩ : (finspan {3, 3 * (k'+1) + 1}).gaps)
        = ⟨3 * ((k'+1) - 1 - (j.castSucc : ℕ)) + 2, memA_plus (k'+1) j.castSucc⟩ := by
      apply Subtype.ext; simp only [Fin.coe_castSucc]; omega
    rw [hsub] at hle
    have hmatch : (⟨3 * ((k'+1) - 1 - (j.succ : ℕ)) + 2, memA_plus (k'+1) j.succ⟩ : (finspan {3, 3 * (k'+1) + 1}).gaps)
        = ⟨3 * ((k'+1) - 1 - ((j : ℕ) + 1)) + 2, hmemS⟩ := by
      apply Subtype.ext; simp only [Fin.val_succ]
    rw [hmatch]; exact hle
  · -- acc a 1 ≤ acc r k
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [acc, dif_pos (by omega), acc, dif_pos (by omega)]
    rw [aOfGap_apply, rOfGap_apply]
    -- a 0 = n(gap 3k-1); r(k-1) = n(gap 3k+2); (3k-1)+3 = 3k+2
    have ha0 : (⟨(1:ℕ) - 1, by omega⟩ : Fin (k' + 1)) = (0 : Fin (k'+1)) := by
      apply Fin.ext; simp
    have hrk : (⟨(k' + 1) - 1, by omega⟩ : Fin (k' + 1)) = Fin.last k' := by
      apply Fin.ext; simp
    rw [ha0, hrk]
    show n ⟨3 * ((k' + 1) - 1 - ((0 : Fin (k'+1)) : ℕ)) + 2, memA_plus (k'+1) 0⟩
        ≤ n ⟨6 * (k' + 1) - 1 - 3 * ((Fin.last k' : Fin (k'+1)) : ℕ), memR_plus (k'+1) (Fin.last k')⟩
    have hmemS : (3 * ((k' + 1) - 1 - (0 : ℕ)) + 2) ∈ (finspan {3, 3 * (k' + 1) + 1}).gaps := by
      have := memA_plus (k'+1) 0; simpa using this
    have haddr : (3 * ((k' + 1) - 1 - (0 : ℕ)) + 2) + 3
        = 6 * (k' + 1) - 1 - 3 * ((Fin.last k' : Fin (k'+1)) : ℕ) := by
      simp only [Fin.val_last]; omega
    have hplus : (3 * ((k' + 1) - 1 - (0 : ℕ)) + 2) + 3 ∈ (finspan {3, 3 * (k' + 1) + 1}).gaps := by
      rw [haddr]; exact memR_plus (k'+1) (Fin.last k')
    have hle := N3 ⟨3 * ((k' + 1) - 1 - (0 : ℕ)) + 2, hmemS⟩ hplus
    have hsub : (⟨(3 * ((k' + 1) - 1 - (0 : ℕ)) + 2) + 3, hplus⟩ : (finspan {3, 3 * (k'+1) + 1}).gaps)
        = ⟨6 * (k' + 1) - 1 - 3 * ((Fin.last k' : Fin (k'+1)) : ℕ), memR_plus (k'+1) (Fin.last k')⟩ := by
      apply Subtype.ext; simp only [Fin.val_last]; omega
    rw [hsub] at hle
    have hmatchS : (⟨3 * ((k' + 1) - 1 - ((0 : Fin (k'+1)) : ℕ)) + 2, memA_plus (k'+1) 0⟩
          : (finspan {3, 3 * (k'+1) + 1}).gaps)
        = ⟨3 * ((k' + 1) - 1 - (0 : ℕ)) + 2, hmemS⟩ := by
      apply Subtype.ext; simp
    rw [hmatchS]; exact hle
  · -- Antitone z
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Fin.antitone_iff_succ_le]
    intro j
    rw [zOfGap_apply, zOfGap_apply]
    show n ⟨3 * ((k'+1) - 1 - (j.succ : ℕ)) + 1, memZ_plus (k'+1) j.succ⟩
        ≤ n ⟨3 * ((k'+1) - 1 - (j.castSucc : ℕ)) + 1, memZ_plus (k'+1) j.castSucc⟩
    have hjlt : (j : ℕ) + 1 < (k'+1) := by have := j.2; omega
    have hmemS : (3 * ((k'+1) - 1 - ((j : ℕ) + 1)) + 1) ∈ (finspan {3, 3 * (k'+1) + 1}).gaps := by
      have := memZ_plus (k'+1) j.succ; simpa [Fin.val_succ] using this
    have haddr : (3 * ((k'+1) - 1 - ((j : ℕ) + 1)) + 1) + 3 = 3 * ((k'+1) - 1 - (j : ℕ)) + 1 := by omega
    have hplus : (3 * ((k'+1) - 1 - ((j : ℕ) + 1)) + 1) + 3 ∈ (finspan {3, 3 * (k'+1) + 1}).gaps := by
      rw [haddr]; exact memZ_plus (k'+1) j.castSucc
    have hle := N3 ⟨3 * ((k'+1) - 1 - ((j : ℕ) + 1)) + 1, hmemS⟩ hplus
    have hsub : (⟨(3 * ((k'+1) - 1 - ((j : ℕ) + 1)) + 1) + 3, hplus⟩ : (finspan {3, 3 * (k'+1) + 1}).gaps)
        = ⟨3 * ((k'+1) - 1 - (j.castSucc : ℕ)) + 1, memZ_plus (k'+1) j.castSucc⟩ := by
      apply Subtype.ext; simp only [Fin.coe_castSucc]; omega
    rw [hsub] at hle
    have hmatch : (⟨3 * ((k'+1) - 1 - (j.succ : ℕ)) + 1, memZ_plus (k'+1) j.succ⟩ : (finspan {3, 3 * (k'+1) + 1}).gaps)
        = ⟨3 * ((k'+1) - 1 - ((j : ℕ) + 1)) + 1, hmemS⟩ := by
      apply Subtype.ext; simp only [Fin.val_succ]
    rw [hmatch]; exact hle
  · -- ∀ i ∈ Icc 1 k, acc z i ≤ acc r i
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [acc, dif_pos ⟨hi.1, hi.2⟩, acc, dif_pos ⟨hi.1, hi.2⟩]
    rw [zOfGap_apply, rOfGap_apply]
    -- t := i-1 : Fin k, z t = n(gap 3(k-1-t)+1); r t = n(gap 6k-1-3t); shift by 3k+1
    set t : Fin k := ⟨i - 1, by omega⟩ with ht
    show n ⟨3 * (k - 1 - (t : ℕ)) + 1, memZ_plus k t⟩
        ≤ n ⟨6 * k - 1 - 3 * (t : ℕ), memR_plus k t⟩
    have htlt : (t : ℕ) < k := t.2
    have hmemS : (3 * (k - 1 - (t : ℕ)) + 1) ∈ (finspan {3, 3 * k + 1}).gaps := memZ_plus k t
    have haddr : (3 * (k - 1 - (t : ℕ)) + 1) + (3 * k + 1) = 6 * k - 1 - 3 * (t : ℕ) := by omega
    have hplus : (3 * (k - 1 - (t : ℕ)) + 1) + (3 * k + 1) ∈ (finspan {3, 3 * k + 1}).gaps := by
      rw [haddr]; exact memR_plus k t
    have hle := NK ⟨3 * (k - 1 - (t : ℕ)) + 1, hmemS⟩ hplus
    have hsub : (⟨(3 * (k - 1 - (t : ℕ)) + 1) + (3 * k + 1), hplus⟩ : (finspan {3, 3 * k + 1}).gaps)
        = ⟨6 * k - 1 - 3 * (t : ℕ), memR_plus k t⟩ := by
      apply Subtype.ext; simp only []; omega
    rw [hsub] at hle
    exact hle

/-- **Layer 5 (off-cone LHS vanishing).**  Off the cone, the raw `multiplicand` product is `0`
(a failing cone inequality drives some `extendedSelfQPochhammer` argument negative). -/
lemma offCone_lhs_zero_plus (k : ℕ) (hk : 1 ≤ k)
    (n : (finspan {3, 3 * k + 1}).gaps → ℕ)
    (hnot : ¬ OnConeP k (rOfGap k n) (aOfGap k n) (zOfGap k n)) :
    (∏ i, HJO.multiplicand (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) (fun i => (n i : ℤ)) i) = 0 := by
  -- SANITY CHECK PASSED: contrapositive of the bridge lemma onCone_of_cone'.
  by_contra hprod
  -- The vector lies in the intersection of every multiplicand support.
  have hmem : (fun i => (n i : ℤ)) ∈ (⋂ i, Function.support
      fun x => HJO.multiplicand (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) x i) := by
    rw [Set.mem_iInter]
    intro i
    rw [Function.mem_support]
    intro hzero
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
  -- Hence it lies in the cone.
  have hcone : (fun i => (n i : ℤ)) ∈ HJO.cone' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) :=
    HJO.iInter_support_multiplicand_subset_cone _ _ _ rfl hmem
  -- Hence it satisfies OnConeP, contradicting hnot.
  exact hnot (onCone_of_cone' k hk n hcone)

/-- **Per-`n` telescoping kernel (plus)** — the analytic heart of Lemma 3.5 (item (2) of the
HJO a=3 reassembly).  For a nonnegative gap-vector `n` with boundary tuple `r = rOfGap k n`,
the product of the three-factor `multiplicand`s (each an `extendedSelfQPochhammer` ratio
`(X;X)_{Δ⁺}/[(X;X)_{Δa}(X;X)_{Δb}]`) times `X^{Q(n)}` telescopes, across the `3k` gaps of
`⟨3,3k+1⟩` = `{3t+1 : t<k} ∪ {3t+2 : t<2k}`, into the outer boundary factor
`outerFactorP` times the coerced Axiomlib `lhsTerm k r G n`.

Both sides vanish off the summation cone (LHS: an `extendedSelfQPochhammer` of a negative
argument is `0`; RHS: the corresponding `qChoose`/`extendedQChoose` factor vanishes).  The
exponent side (`X^{Q(n)}` matching) is `lhs_exp_eq`/`stmt_reindexEq_plus`; the residual content
is the factor-by-factor telescoping bijection, proved by induction over the block index with a
running-partial-product invariant (HJO, proof of Lemma 3.5).

Isolated as a single sorry-stubbed sub-lemma: it is the sole irreducible analytic obstruction
of `stmt6_reassembly` (three independent informal-proof passes converged on exactly this). -/
lemma multiplicand_term_eq_plus (k : ℕ) (hk : 1 ≤ k) (hQbin : Fact6)
    (n : (finspan {3, 3 * k + 1}).gaps → ℕ) :
    (∏ i, HJO.multiplicand (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) (fun i => (n i : ℤ)) i)
        * X ^ ((HJO.Q' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) (fun i => (n i : ℤ))).toNat)
      = outerFactorP k (rOfGap k n)
          * ((Polynomial.map (Nat.castRingHom ℤ)
              (HJO.SumToSum.ThreeOne.lhsTerm k (rOfGap k n)
                (finspan {3, 3 * k + 1}).gaps n)).toPowerSeries) := by
  by_cases hcone : OnConeP k (rOfGap k n) (aOfGap k n) (zOfGap k n)
  · exact multiplicand_onCone_eq_plus k hk hQbin n hcone
  · rw [offCone_lhs_zero_plus k hk n hcone, zero_mul,
      offCone_rhs_zero_plus k hk n hcone]

/-- **`r`-partition/Fubini reassembly (plus)** — assembles `stmt6_reassembly` from the kernel.
Restricts the defining `zNat` sum over `n : G → ℤ` to the nonnegative cone `n : G → ℕ` (off-cone
`multiplicand` vanishes), applies `multiplicand_term_eq_plus` pointwise, then reindexes the
`∑'_n` by the boundary tuple `rOfGap` (via `fiberEquivAZ`, using `Fact8`/`hPD` summability for
the discrete Fubini), pulls the `r`-only `outerFactorP` outside the fibre sum, and recognizes the
inner fibre sum as `SbPlus k r` (its `∑ᶠ`-of-`lhsTerm` definition).  The nonnegativity + cone
constraints force each boundary tuple `r` antitone, giving the `∑'` over `{r // Antitone r}`. -/
lemma zNatTermP_summable (k : ℕ) (hk : 1 ≤ k) (hPD : Fact8 3 (3 * k + 1)) :
    Summable (fun n : (finspan {3, 3 * k + 1}).gaps → ℤ =>
      (∏ i, HJO.multiplicand (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) n i)
        * X ^ ((HJO.Q' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) n).toNat)) := by
  -- Use Axiomlib's `HJO.summable_of_posDefOn` at `G = gaps`, `a=3`, `b=3k+1`.
  -- It needs `PosDefOn (Q' G 3 (3k+1)) (cone' G 3 (3k+1))`, which follows from Fact8's
  -- `(Q 3 (3k+1)).PosDefOn (cone 3 (3k+1))` via `Q'_eq_Q` and `cone = cone'` at gaps.
  have hq : QuadraticMap.PosDefOn
      (HJO.Q' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1))
      (HJO.cone' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1)) := by
    rw [HJO.Q'_eq_Q]
    exact hPD.2.2.2.1
  exact HJO.summable_of_posDefOn (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) rfl hq

/-- The pointwise ℕ → ℤ cast on gap-vectors. -/
def natCastGapP (k : ℕ) (m : (finspan {3, 3 * k + 1}).gaps → ℕ) :
    (finspan {3, 3 * k + 1}).gaps → ℤ := fun i => (m i : ℤ)

lemma natCastGapP_injective (k : ℕ) : Function.Injective (natCastGapP k) := by
  intro m₁ m₂ h
  funext i
  have := congrFun h i
  simpa [natCastGapP] using this

/-- **Gap B, part 1 (off-`ℕ`-range vanishing).**  For an integer gap-vector `n` not in the image
of the `ℕ`-cast, the `zNat` summand is `0` (some `extendedSelfQPochhammer` argument becomes
negative, killing the product). -/
lemma zNatTermP_vanish_off_natRange (k : ℕ) (hk : 1 ≤ k)
    (n : (finspan {3, 3 * k + 1}).gaps → ℤ) (hn : n ∉ Set.range (natCastGapP k)) :
    (∏ i, HJO.multiplicand (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) n i)
        * X ^ ((HJO.Q' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) n).toNat) = 0 := by
  -- SANITY CHECK PASSED: n ∉ ℕ-range ⇒ some coord < 0 ⇒ n ∉ cone'(⊆ Ici 0) ⇒ n ∉ ⋂support
  -- ⇒ some multiplicand factor = 0 ⇒ ∏ = 0.
  have hnge : n ∉ Set.Ici (0 : (finspan {3, 3 * k + 1}).gaps → ℤ) := by
    intro hge
    apply hn
    refine ⟨fun i => (n i).toNat, ?_⟩
    funext i
    simp only [natCastGapP]
    rw [Int.toNat_of_nonneg (hge i)]
  have hncone : n ∉ HJO.cone' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) := fun hc =>
    hnge (HJO.cone'_subset_Ici_zero _ _ _ hc)
  have hniInter : n ∉ (⋂ i, Function.support
      fun x => HJO.multiplicand (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) x i) := fun hi =>
    hncone (HJO.iInter_support_multiplicand_subset_cone _ _ _ rfl hi)
  rw [Set.mem_iInter] at hniInter
  push_neg at hniInter
  obtain ⟨i, hi⟩ := hniInter
  rw [Function.mem_support, not_not] at hi
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul]

/-- **Gap B, part 2 (antitonicity of the boundary tuple on the support).**  If the ℕ-summand for a
gap-vector `m` is nonzero, then its boundary tuple `rOfGap k m` is antitone. -/
lemma rOfGap_antitone_of_nonzero (k : ℕ) (hk : 1 ≤ k)
    (m : (finspan {3, 3 * k + 1}).gaps → ℕ)
    (hm : (∏ i, HJO.multiplicand (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) (natCastGapP k m) i)
        * X ^ ((HJO.Q' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) (natCastGapP k m)).toNat) ≠ 0) :
    Antitone (rOfGap k m) := by
  -- SANITY CHECK PASSED: nonzero ⇒ each multiplicand factor ≠ 0 ⇒ natCastGapP ∈ cone'
  -- ⇒ the `+3` monotonicity constraint gives rⱼ₊₁ ≤ rⱼ.
  -- Step 1: the product of multiplicands is nonzero.
  have hprod : (∏ i, HJO.multiplicand (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1)
      (natCastGapP k m) i) ≠ 0 := left_ne_zero_of_mul hm
  -- Step 2: `natCastGapP k m` lies in the intersection of all multiplicand supports.
  have hmem : natCastGapP k m ∈ (⋂ i, Function.support
      fun x => HJO.multiplicand (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) x i) := by
    rw [Set.mem_iInter]
    intro i
    rw [Function.mem_support]
    intro hzero
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
  -- Step 3: hence it lies in the cone.
  have hcone : natCastGapP k m ∈ HJO.cone' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) :=
    HJO.iInter_support_multiplicand_subset_cone _ _ _ rfl hmem
  -- Extract the `+3` (a = 3) monotonicity constraint from the cone.
  obtain ⟨_, hstep3, _⟩ := hcone
  -- Step 4: prove antitonicity from consecutive decrease.
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Fin.antitone_iff_succ_le]
  intro j
  -- rⱼ₊₁ ≤ rⱼ : reduce both to gap-vector reads.
  rw [rOfGap_apply, rOfGap_apply]
  -- The gap addresses come from `gapSub`/`gapEquiv` (defeq).
  show m ⟨6 * (k' + 1) - 1 - 3 * (j.succ : ℕ), memR_plus (k' + 1) j.succ⟩
      ≤ m ⟨6 * (k' + 1) - 1 - 3 * (j.castSucc : ℕ), memR_plus (k' + 1) j.castSucc⟩
  have hjlt : (j : ℕ) < k' := j.2
  -- membership of the smaller (succ-side) gap
  have hmemSmall : (6 * (k' + 1) - 1 - 3 * ((j : ℕ) + 1)) ∈ (finspan {3, 3 * (k' + 1) + 1}).gaps := by
    have := memR_plus (k' + 1) j.succ
    simpa [Fin.val_succ] using this
  -- `i + 3 ∈ G` where `i` is the small gap; `i + 3` is the `castSucc`-side gap.
  have haddr : (6 * (k' + 1) - 1 - 3 * ((j : ℕ) + 1)) + 3
      = 6 * (k' + 1) - 1 - 3 * (j : ℕ) := by omega
  have hplus : (6 * (k' + 1) - 1 - 3 * ((j : ℕ) + 1)) + 3 ∈ (finspan {3, 3 * (k' + 1) + 1}).gaps := by
    rw [haddr]; exact memR_plus (k' + 1) j.castSucc
  -- Apply the cone `+3` constraint at index `i = small gap`.
  have hle := hstep3 ⟨6 * (k' + 1) - 1 - 3 * ((j : ℕ) + 1), hmemSmall⟩ hplus
  -- Convert the ℤ inequality on `natCastGapP` down to ℕ.
  simp only [natCastGapP] at hle
  have hsub : (⟨(6 * (k' + 1) - 1 - 3 * ((j : ℕ) + 1)) + 3, hplus⟩
        : (finspan {3, 3 * (k' + 1) + 1}).gaps)
      = ⟨6 * (k' + 1) - 1 - 3 * (j.castSucc : ℕ), memR_plus (k' + 1) j.castSucc⟩ := by
    apply Subtype.ext
    simp only [Fin.coe_castSucc]
    omega
  rw [hsub] at hle
  have hle' : m ⟨6 * (k' + 1) - 1 - 3 * ((j : ℕ) + 1), hmemSmall⟩
      ≤ m ⟨6 * (k' + 1) - 1 - 3 * (j.castSucc : ℕ), memR_plus (k' + 1) j.castSucc⟩ := by
    exact_mod_cast hle
  -- Match the succ-side gap address with the small gap.
  have hmatch : (⟨6 * (k' + 1) - 1 - 3 * (j.succ : ℕ), memR_plus (k' + 1) j.succ⟩
        : (finspan {3, 3 * (k' + 1) + 1}).gaps)
      = ⟨6 * (k' + 1) - 1 - 3 * ((j : ℕ) + 1), hmemSmall⟩ := by
    apply Subtype.ext
    simp only [Fin.val_succ]
  rw [hmatch]
  exact hle'

/-- **Fibre summability.**  For a fixed boundary tuple `r`, the family of coerced `lhsTerm` power
series over the fibre `{m // rOfGap k m = r}` is summable (only finitely many `m` give a nonzero
coefficient at each degree). -/
lemma fibre_summable (k : ℕ) (hk : 1 ≤ k) (r : Fin k → ℕ) :
    Summable (fun m : {m : (finspan {3, 3 * k + 1}).gaps → ℕ // rOfGap k m = r} =>
      (Polynomial.map (Nat.castRingHom ℤ)
        (HJO.SumToSum.ThreeOne.lhsTerm k r (finspan {3, 3 * k + 1}).gaps m.1)).toPowerSeries) := by
  classical
  set Φ : Polynomial ℕ →+* ℤ⟦X⟧ :=
    (Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.mapRingHom (Nat.castRingHom ℤ)) with hΦ
  set L : ((finspan {3, 3 * k + 1}).gaps → ℕ) → Polynomial ℕ :=
    fun n => HJO.SumToSum.ThreeOne.lhsTerm k r (finspan {3, 3 * k + 1}).gaps n with hL
  -- The subtype summand equals `Φ (L m.1)`.
  have hsummand : (fun m : {m : (finspan {3, 3 * k + 1}).gaps → ℕ // rOfGap k m = r} =>
      (Polynomial.map (Nat.castRingHom ℤ)
        (HJO.SumToSum.ThreeOne.lhsTerm k r (finspan {3, 3 * k + 1}).gaps m.1)).toPowerSeries)
      = fun m => Φ (L m.1) := by
    funext m
    simp only [hΦ, hL, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_mapRingHom]
  rw [hsummand]
  -- Finite support of L.
  have hfin : Function.HasFiniteSupport L := by
    apply Set.Finite.subset (HJO.SumToSum.ThreeOne.lhsSupport k r).finite_toSet
    exact HJO.SumToSum.ThreeOne.support_lhsTerm k r
  -- `fun n => Φ (L n)` has finite support.
  have hfinΦ : Function.HasFiniteSupport (fun n => Φ (L n)) := by
    apply Set.Finite.subset hfin
    intro n hn
    rw [Function.mem_support] at hn ⊢
    intro hLn
    exact hn (by rw [hLn, map_zero])
  -- The subtype family has finite support.
  have hfinSub : Function.HasFiniteSupport
      (fun m : {m : (finspan {3, 3 * k + 1}).gaps → ℕ // rOfGap k m = r} => Φ (L m.1)) := by
    apply Set.Finite.of_finite_image (f := Subtype.val)
    · apply Set.Finite.subset hfinΦ
      rintro _ ⟨m, hm, rfl⟩
      rw [Function.mem_support] at hm ⊢
      exact hm
    · exact Set.injOn_of_injective Subtype.val_injective
  exact summable_of_hasFiniteSupport hfinSub

/-- **Fibre sum = `SbPlus`.**  For a fixed boundary tuple `r`, the (finitely-supported) sum over the
fibre `{m // rOfGap k m = r}` of the coerced `lhsTerm` power series equals `SbPlus k r`. -/
lemma fibre_tsum_eq_SbPlus (k : ℕ) (hk : 1 ≤ k) (r : Fin k → ℕ) :
    ∑' m : {m : (finspan {3, 3 * k + 1}).gaps → ℕ // rOfGap k m = r},
        ((Polynomial.map (Nat.castRingHom ℤ)
            (HJO.SumToSum.ThreeOne.lhsTerm k r (finspan {3, 3 * k + 1}).gaps m.1)).toPowerSeries)
      = SbPlus k r := by
  classical
  -- The composite ring hom Φ : ℕ[X] →+* ℤ⟦X⟧ = (·.toPowerSeries) ∘ (Polynomial.map (ℕ→ℤ)).
  set Φ : Polynomial ℕ →+* ℤ⟦X⟧ :=
    (Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.mapRingHom (Nat.castRingHom ℤ)) with hΦ
  set L : ((finspan {3, 3 * k + 1}).gaps → ℕ) → Polynomial ℕ :=
    fun n => HJO.SumToSum.ThreeOne.lhsTerm k r (finspan {3, 3 * k + 1}).gaps n with hL
  -- The subtype summand is `Φ (L m.1)`.
  have hsummand : ∀ m : {m : (finspan {3, 3 * k + 1}).gaps → ℕ // rOfGap k m = r},
      ((Polynomial.map (Nat.castRingHom ℤ)
        (HJO.SumToSum.ThreeOne.lhsTerm k r (finspan {3, 3 * k + 1}).gaps m.1)).toPowerSeries)
        = Φ (L m.1) := by
    intro m
    simp only [hΦ, hL, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_mapRingHom]
  rw [tsum_congr hsummand]
  -- SbPlus k r = Φ (∑ᶠ n, L n).
  have hSb : SbPlus k r = Φ (∑ᶠ n, L n) := by
    simp only [SbPlus, hΦ, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_mapRingHom, hL]
  -- Finite support of L (via Axiomlib's support_lhsTerm ⊆ lhsSupport).
  have hfin : Function.HasFiniteSupport L := by
    apply Set.Finite.subset (HJO.SumToSum.ThreeOne.lhsSupport k r).finite_toSet
    exact HJO.SumToSum.ThreeOne.support_lhsTerm k r
  -- Push Φ through the finsum.
  have hpush : Φ (∑ᶠ n, L n) = ∑ᶠ n, Φ (L n) := map_finsum Φ hfin
  -- Off the fibre, L n = 0 so Φ(L n) = 0.
  have hoff : ∀ n, rOfGap k n ≠ r → Φ (L n) = 0 := by
    intro n hne
    have hLn : L n = 0 := by
      simp only [hL, HJO.SumToSum.ThreeOne.lhsTerm]
      rw [if_neg]
      intro hcond
      exact hne ((lhsTerm_support_iff_domAZ_plus k hk r n).1 hcond)
    rw [hLn, map_zero]
  -- The composite `fun n => Φ (L n)` has finite support (subset of L's finite support).
  have hfinΦ : Function.HasFiniteSupport (fun n => Φ (L n)) := by
    apply Set.Finite.subset hfin
    intro n hn
    rw [Function.mem_support] at hn ⊢
    intro hLn
    exact hn (by rw [hLn, map_zero])
  -- The subtype family `fun m => Φ (L m.1)` has finite support: its support injects (via
  -- Subtype.val) into the finite support of `fun n => Φ (L n)`.
  have hfinSub : Function.HasFiniteSupport
      (fun m : {m : (finspan {3, 3 * k + 1}).gaps → ℕ // rOfGap k m = r} => Φ (L m.1)) := by
    apply Set.Finite.of_finite_image (f := Subtype.val)
    · apply Set.Finite.subset hfinΦ
      rintro _ ⟨m, hm, rfl⟩
      rw [Function.mem_support] at hm ⊢
      exact hm
    · exact Set.injOn_of_injective Subtype.val_injective
  -- Convert the tsum over the subtype into a finsum, then to the conditional finsum, then full.
  rw [tsum_eq_finsum hfinSub, hSb, hpush]
  rw [finsum_subtype_eq_finsum_cond (f := fun n => Φ (L n)) (fun n => rOfGap k n = r)]
  symm
  rw [← finsum_mem_univ (fun n => Φ (L n))]
  exact finsum_mem_inter_support_eq' (fun n => Φ (L n)) Set.univ {n | rOfGap k n = r}
    (by
      intro x hx
      simp only [Set.mem_univ, Set.mem_setOf_eq, true_iff]
      by_contra hne
      rw [Function.mem_support] at hx
      exact hx (hoff x hne))

lemma zNat_reassembly_plus (k : ℕ) (hk : 1 ≤ k)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) (hSym : Fact3 Stil)
    (hQbin : Fact6) (hPD : Fact8 3 (3 * k + 1)) (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    HJO.zNat 3 (3 * k + 1)
      = ∑' r : {r : Fin k → ℕ // Antitone r}, outerFactorP k r.1 * SbPlus k r.1 := by
  -- Abbreviation for the ℤ-indexed summand.
  set T : ((finspan {3, 3 * k + 1}).gaps → ℤ) → ℤ⟦X⟧ := fun n =>
      (∏ i, HJO.multiplicand (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) n i)
        * X ^ ((HJO.Q' (finspan {3, 3 * k + 1}).gaps 3 (3 * k + 1) n).toNat) with hT
  -- Step 0: `zNat` unfolds to `∑' n, T n`.
  have hzNat : HJO.zNat 3 (3 * k + 1) = ∑' n : (finspan {3, 3 * k + 1}).gaps → ℤ, T n := by
    rfl
  rw [hzNat]
  have hsummℤ : Summable T := by rw [hT]; exact zNatTermP_summable k hk hPD
  -- Step 1: restrict the ℤ-indexed sum to the ℕ-cone via the injective cast (off-range vanishes).
  have hsupp : Function.support T ⊆ Set.range (natCastGapP k) := by
    intro n hn
    by_contra hnr
    apply hn
    show T n = 0
    rw [hT]
    exact zNatTermP_vanish_off_natRange k hk n hnr
  have hstep1 : ∑' n : (finspan {3, 3 * k + 1}).gaps → ℤ, T n
      = ∑' m : (finspan {3, 3 * k + 1}).gaps → ℕ, T (natCastGapP k m) := by
    rw [← (natCastGapP_injective k).tsum_eq (f := T) hsupp]
  rw [hstep1]
  -- Step 2: pointwise, `T (cast m) = outerFactorP k (rOfGap k m) * (map lhsTerm).toPS`.
  have hstep2 : ∀ m : (finspan {3, 3 * k + 1}).gaps → ℕ,
      T (natCastGapP k m)
        = outerFactorP k (rOfGap k m)
            * ((Polynomial.map (Nat.castRingHom ℤ)
                (HJO.SumToSum.ThreeOne.lhsTerm k (rOfGap k m) (finspan {3, 3 * k + 1}).gaps m)).toPowerSeries) := by
    intro m
    rw [hT]
    exact multiplicand_term_eq_plus k hk hQbin m
  rw [tsum_congr hstep2]
  have hsummℕ : Summable (fun m : (finspan {3, 3 * k + 1}).gaps → ℕ =>
      outerFactorP k (rOfGap k m)
        * ((Polynomial.map (Nat.castRingHom ℤ)
            (HJO.SumToSum.ThreeOne.lhsTerm k (rOfGap k m) (finspan {3, 3 * k + 1}).gaps m)).toPowerSeries)) := by
    have hcast : Summable (fun m : (finspan {3, 3 * k + 1}).gaps → ℕ => T (natCastGapP k m)) :=
      (Function.Injective.summable_iff (natCastGapP_injective k)
        (fun n hn => by rw [hT]; exact zNatTermP_vanish_off_natRange k hk n hn)).2 hsummℤ
    exact hcast.congr hstep2
  -- Step 3: reindex the ℕ-sum by the fibres of `rOfGap` (sigma decomposition).
  set F : ((finspan {3, 3 * k + 1}).gaps → ℕ) → (Fin k → ℕ) := rOfGap k with hF
  set g : ((finspan {3, 3 * k + 1}).gaps → ℕ) → ℤ⟦X⟧ := fun m =>
      outerFactorP k (rOfGap k m)
        * ((Polynomial.map (Nat.castRingHom ℤ)
            (HJO.SumToSum.ThreeOne.lhsTerm k (rOfGap k m) (finspan {3, 3 * k + 1}).gaps m)).toPowerSeries) with hg
  rw [← (Equiv.sigmaFiberEquiv F).tsum_eq g]
  simp only [Equiv.sigmaFiberEquiv_apply]
  have hsummσ : Summable (fun p : Σ r : Fin k → ℕ, {m // F m = r} => g p.2.1) :=
    (Equiv.summable_iff (Equiv.sigmaFiberEquiv F)).2 hsummℕ
  rw [hsummσ.tsum_sigma]
  -- Step 4: inner fibre sum. For each `r`, pull out `outerFactorP k r`, identify with `SbPlus`.
  have hinner : ∀ r : Fin k → ℕ,
      ∑' m : {m // F m = r}, g m.1 = outerFactorP k r * SbPlus k r := by
    intro r
    have hfibre : ∀ m : {m // F m = r},
        g m.1 = outerFactorP k r
          * ((Polynomial.map (Nat.castRingHom ℤ)
              (HJO.SumToSum.ThreeOne.lhsTerm k r (finspan {3, 3 * k + 1}).gaps m.1)).toPowerSeries) := by
      rintro ⟨m, hm⟩
      simp only [hg, hF] at hm ⊢
      rw [hm]
    rw [tsum_congr hfibre, (fibre_summable k hk r).tsum_mul_left (outerFactorP k r),
      fibre_tsum_eq_SbPlus k hk r]
  rw [tsum_congr hinner]
  -- Step 5: restrict `∑' r : Fin k → ℕ` to `∑' r : {r // Antitone r}` (non-antitone ⇒ 0).
  symm
  have hsuppR : Function.support (fun r : Fin k → ℕ => outerFactorP k r * SbPlus k r)
      ⊆ Set.range (Subtype.val : {r : Fin k → ℕ // Antitone r} → (Fin k → ℕ)) := by
    intro r hr
    simp only [Function.mem_support] at hr
    -- if the summand is nonzero, `r` is antitone (so it is in the range of `Subtype.val`)
    have hant : Antitone r := by
      -- `outerFactorP k r * SbPlus k r = ∑' m in fibre, g m.1` (reverse hinner); nonzero ⇒ some
      -- fibre term nonzero ⇒ that `m` has `T (cast m) ≠ 0` ⇒ `rOfGap k m = r` antitone.
      by_contra hrNA
      apply hr
      rw [← hinner r]
      have hz0 : ∀ mm : {m // F m = r}, g mm.1 = 0 := by
        rintro ⟨m, hm⟩
        by_contra hne
        apply hrNA
        have hTne : T (natCastGapP k m) ≠ 0 := by
          have hgT : g m = T (natCastGapP k m) := by rw [hg, hstep2 m]
          rw [← hgT]; exact hne
        have hant2 : Antitone (rOfGap k m) := by
          rw [hT] at hTne; exact rOfGap_antitone_of_nonzero k hk m hTne
        have hmr : rOfGap k m = r := hm
        rwa [hmr] at hant2
      rw [tsum_congr hz0, tsum_zero]
    exact ⟨⟨r, hant⟩, rfl⟩
  rw [← (Subtype.val_injective (p := (Antitone : (Fin k → ℕ) → Prop))).tsum_eq
    (f := fun r : Fin k → ℕ => outerFactorP k r * SbPlus k r) hsuppR]

/-- **Statement 6 — Lemma 3.5, reassembly (eq:reassemble).** `Z_{3,b} = Σ_r (1/(q)_{r₁})
(∏[rᵢ;rᵢ₊₁]) S_b(r)`, where `S_b(r)` is the *unexpanded fixed-boundary sum* (`SbPlus`) — this
is Lemma 3.5 proper.  The outer factor `∏[rᵢ;rᵢ₊₁]` is essential (Remark 3.6).  Uses Facts
1,2,3,6,8,9. -/
theorem stmt6_reassembly (k : ℕ) (hk : 1 ≤ k)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) (hSym : Fact3 Stil)
    (hQbin : Fact6) (hPD : Fact8 3 (3 * k + 1)) (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    HJO.zNat 3 (3 * k + 1)
      = ∑' r : {r : Fin k → ℕ // Antitone r},
          invOfUnit (qPochhammer qX qX (acc r.1 1)) 1
            * (∏ i ∈ Icc 1 (k - 1), qChoose qX (acc r.1 i) (acc r.1 (i + 1)))
            * SbPlus k r.1 := by
  rw [zNat_reassembly_plus Stil Tset invStat tabOf Ja Jz k hk hRC hInv hSym hQbin hPD hInvComp]
  refine tsum_congr (fun r => ?_)
  rw [outerFactorP, mul_assoc]


/-! ### Minus kernel: on-cone predicate and per-factor residue lemmas
(mirror `OnConeP` and `multiplicand_{z,a,r}factor`). -/

/-- **On-cone predicate (minus).**  Boundary tuple `r : Fin k → ℕ`, `a`/`z` tuples over
`Fin (k-1)`.  `Antitone r` plus `domAZ (trim r) (acc r k) a z`. -/
def OnConeM (k : ℕ) (r : Fin k → ℕ) (a z : Fin (k - 1) → ℕ) : Prop :=
  Antitone r ∧ Antitone a ∧ acc a 1 ≤ acc r k ∧ Antitone z ∧
    (∀ i ∈ Icc 1 (k - 1), acc z i ≤ acc (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) i)

lemma OnConeM.antitone_r {k : ℕ} {r : Fin k → ℕ} {a z : Fin (k - 1) → ℕ}
    (h : OnConeM k r a z) : Antitone r := h.1
lemma OnConeM.antitone_a {k : ℕ} {r : Fin k → ℕ} {a z : Fin (k - 1) → ℕ}
    (h : OnConeM k r a z) : Antitone a := h.2.1
lemma OnConeM.a1_le_rk {k : ℕ} {r : Fin k → ℕ} {a z : Fin (k - 1) → ℕ}
    (h : OnConeM k r a z) : acc a 1 ≤ acc r k := h.2.2.1
lemma OnConeM.antitone_z {k : ℕ} {r : Fin k → ℕ} {a z : Fin (k - 1) → ℕ}
    (h : OnConeM k r a z) : Antitone z := h.2.2.2.1
lemma OnConeM.rz {k : ℕ} {r : Fin k → ℕ} {a z : Fin (k - 1) → ℕ}
    (h : OnConeM k r a z) {i : ℕ} (hi : i ∈ Icc 1 (k - 1)) :
    acc z i ≤ acc (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) i := h.2.2.2.2 i hi

/-- `OnConeM` gives the in-file `domAZ` at boundary `s = acc r k` for the trimmed `r`. -/
lemma OnConeM.domAZ {k : ℕ} {r : Fin k → ℕ} {a z : Fin (k - 1) → ℕ} (h : OnConeM k r a z) :
    domAZ (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k) a z :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Z-block factor of the raw multiplicand product (minus). Same form as the plus Z-factor. -/
lemma multiplicand_zfactor_minus (k : ℕ) (hk : 2 ≤ k)
    (n : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (hcone : OnConeM k (rOfGap_minus k hk n) (aOfGap_minus k hk n) (zOfGap_minus k hk n))
    (j : Fin (k - 1)) :
    HJO.multiplicand (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) (fun i => (n i : ℤ))
        (gapEquiv_minus k hk (Sum.inl j))
      = invOfUnit (qPochhammer qX qX
          (acc (zOfGap_minus k hk n) (j + 1) - acc (zOfGap_minus k hk n) (j + 2))) 1 := by
  set z := zOfGap_minus k hk n with hz
  have hval : (gapEquiv_minus k hk (Sum.inl j) : ℕ) = 3 * (k - 1 - (j : ℕ)) - 1 := rfl
  have hnj : (n (gapEquiv_minus k hk (Sum.inl j)) : ℤ) = (acc z (j + 1) : ℤ) := by
    have : n (gapEquiv_minus k hk (Sum.inl j)) = z j := rfl
    rw [this, acc_val z ((j : ℕ) + 1) (by omega) (by have := j.2; omega)]
    congr 1
  have hzdec : acc z (↑j + 2) ≤ acc z (↑j + 1) := acc_succ_le hcone.antitone_z (by omega)
  set x := k - 1 - (j : ℕ) with hx
  have hxk : x < k := by have := j.2; omega
  have hx1 : 1 ≤ x := by have := j.2; omega
  unfold HJO.multiplicand
  beta_reduce
  rw [hnj]
  have hE1 : HJO.extend (fun i => (n i : ℤ)) ((gapEquiv_minus k hk (Sum.inl j) : ℕ) - (3 + (3 * k - 1))) = 0 := by
    rw [hval, show 3 * (k - 1 - (j : ℕ)) - 1 - (3 + (3 * k - 1)) = 0 by omega,
      extend_natCast, HJO.extendNat_gaps_zero]; simp
  have hE2 : HJO.extend (fun i => (n i : ℤ)) ((gapEquiv_minus k hk (Sum.inl j) : ℕ) - 3)
      = (acc z (↑j + 2) : ℤ) := by
    rw [hval, show 3 * (k - 1 - (j : ℕ)) - 1 - 3 = 3 * x - 4 by rw [hx]; omega,
      extend_natCast, extendNat_z4_read_minus k hk n x hx1 hxk, hz,
      show k - x + 1 = (j : ℕ) + 2 by rw [hx]; omega]
  have hE3 : HJO.extend (fun i => (n i : ℤ)) ((gapEquiv_minus k hk (Sum.inl j) : ℕ) - (3 * k - 1)) = 0 := by
    rw [hval, show 3 * (k - 1 - (j : ℕ)) - 1 - (3 * k - 1) = 0 by omega,
      extend_natCast, HJO.extendNat_gaps_zero]; simp
  rw [hE1, hE2, hE3]
  rw [show (0:ℤ) = ((0:ℕ):ℤ) from rfl]
  rw [ESQ_natCast_sub (acc z (↑j+1)) 0 (by omega), Nat.sub_zero,
    ESQInv_natCast_sub (acc z (↑j+1)) (acc z (↑j+2)) hzdec,
    ESQInv_natCast_sub (acc z (↑j+1)) 0 (by omega), Nat.sub_zero]
  have hpi := poch_mul_inv (acc z (↑j+1))
  set A := invOfUnit (qPochhammer qX qX (acc z (↑j+1) - acc z (↑j+2))) 1 with hA
  set P := qPochhammer qX qX (acc z (↑j+1)) with hP
  set IP := invOfUnit (qPochhammer qX qX (acc z (↑j+1))) 1 with hIP
  calc P * A * IP = (P * IP) * A := by ring
    _ = A := by rw [hpi, one_mul]

/-- A-block factor of the raw multiplicand product (minus). -/
lemma multiplicand_afactor_minus (k : ℕ) (hk : 2 ≤ k)
    (n : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (hcone : OnConeM k (rOfGap_minus k hk n) (aOfGap_minus k hk n) (zOfGap_minus k hk n))
    (j : Fin (k - 1)) :
    HJO.multiplicand (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) (fun i => (n i : ℤ))
        (gapEquiv_minus k hk (Sum.inr (Sum.inl j)))
      = invOfUnit (qPochhammer qX qX
          (acc (aOfGap_minus k hk n) (j + 1) - acc (aOfGap_minus k hk n) (j + 2))) 1 := by
  set a := aOfGap_minus k hk n with ha
  have hval : (gapEquiv_minus k hk (Sum.inr (Sum.inl j)) : ℕ) = 3 * (k - 1 - (j : ℕ)) - 2 := rfl
  have hnj : (n (gapEquiv_minus k hk (Sum.inr (Sum.inl j))) : ℤ) = (acc a (j + 1) : ℤ) := by
    have : n (gapEquiv_minus k hk (Sum.inr (Sum.inl j))) = a j := rfl
    rw [this, acc_val a ((j : ℕ) + 1) (by omega) (by have := j.2; omega)]
    congr 1
  have hadec : acc a (↑j + 2) ≤ acc a (↑j + 1) := acc_succ_le hcone.antitone_a (by omega)
  set x := k - 1 - (j : ℕ) with hx
  have hxk : x < k := by have := j.2; omega
  have hx1 : 1 ≤ x := by have := j.2; omega
  unfold HJO.multiplicand
  beta_reduce
  rw [hnj]
  have hE1 : HJO.extend (fun i => (n i : ℤ)) ((gapEquiv_minus k hk (Sum.inr (Sum.inl j)) : ℕ) - (3 + (3 * k - 1))) = 0 := by
    rw [hval, show 3 * (k - 1 - (j : ℕ)) - 2 - (3 + (3 * k - 1)) = 0 by omega,
      extend_natCast, HJO.extendNat_gaps_zero]; simp
  have hE2 : HJO.extend (fun i => (n i : ℤ)) ((gapEquiv_minus k hk (Sum.inr (Sum.inl j)) : ℕ) - 3)
      = (acc a (↑j + 2) : ℤ) := by
    rw [hval, show 3 * (k - 1 - (j : ℕ)) - 2 - 3 = 3 * (x - 1) - 2 by rw [hx]; omega,
      extend_natCast]
    rcases Nat.lt_or_ge x 2 with hlt | hge
    · -- x = 1 (j = k-2): 3*(1-1)-2 = 0 → extend 0 = 0, and acc a (j+2) = acc a k = 0.
      have hx1' : x = 1 := by omega
      rw [hx1', show 3 * (1 - 1) - 2 = 0 by norm_num, HJO.extendNat_gaps_zero]
      have hjk : (j : ℕ) = k - 2 := by omega
      rw [acc, dif_neg (by omega)]
    · rw [extendNat_a2_read_minus k hk n (x - 1) (by omega) (by omega), ha,
        show k - (x - 1) = (j : ℕ) + 2 by rw [hx]; omega]
  have hE3 : HJO.extend (fun i => (n i : ℤ)) ((gapEquiv_minus k hk (Sum.inr (Sum.inl j)) : ℕ) - (3 * k - 1)) = 0 := by
    rw [hval, show 3 * (k - 1 - (j : ℕ)) - 2 - (3 * k - 1) = 0 by omega,
      extend_natCast, HJO.extendNat_gaps_zero]; simp
  rw [hE1, hE2, hE3]
  rw [show (0:ℤ) = ((0:ℕ):ℤ) from rfl]
  rw [ESQ_natCast_sub (acc a (↑j+1)) 0 (by omega), Nat.sub_zero,
    ESQInv_natCast_sub (acc a (↑j+1)) (acc a (↑j+2)) hadec,
    ESQInv_natCast_sub (acc a (↑j+1)) 0 (by omega), Nat.sub_zero]
  have hpi := poch_mul_inv (acc a (↑j+1))
  set A := invOfUnit (qPochhammer qX qX (acc a (↑j+1) - acc a (↑j+2))) 1 with hA
  set P := qPochhammer qX qX (acc a (↑j+1)) with hP
  set IP := invOfUnit (qPochhammer qX qX (acc a (↑j+1))) 1 with hIP
  calc P * A * IP = (P * IP) * A := by ring
    _ = A := by rw [hpi, one_mul]

/-- R-block factor of the raw multiplicand product (minus). Same 3-factor form as plus. -/
lemma multiplicand_rfactor_minus (k : ℕ) (hk : 2 ≤ k)
    (n : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (hcone : OnConeM k (rOfGap_minus k hk n) (aOfGap_minus k hk n) (zOfGap_minus k hk n))
    (j : Fin k) :
    HJO.multiplicand (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) (fun i => (n i : ℤ))
        (gapEquiv_minus k hk (Sum.inr (Sum.inr j)))
      = qPochhammer qX qX (acc (rOfGap_minus k hk n) (j + 1) - acc (zOfGap_minus k hk n) (j + 2))
        * invOfUnit (qPochhammer qX qX
            (acc (rOfGap_minus k hk n) (j + 1)
              - (if (j : ℕ) + 1 < k then acc (rOfGap_minus k hk n) (j + 2)
                  else acc (aOfGap_minus k hk n) 1))) 1
        * invOfUnit (qPochhammer qX qX
            (acc (rOfGap_minus k hk n) (j + 1) - acc (zOfGap_minus k hk n) (j + 1))) 1 := by
  set r := rOfGap_minus k hk n with hr
  set a := aOfGap_minus k hk n with ha
  set z := zOfGap_minus k hk n with hz
  have hval : (gapEquiv_minus k hk (Sum.inr (Sum.inr j)) : ℕ) = 6 * k - 5 - 3 * (j : ℕ) := rfl
  have hnj : (n (gapEquiv_minus k hk (Sum.inr (Sum.inr j))) : ℤ) = (acc r (j + 1) : ℤ) := by
    have : n (gapEquiv_minus k hk (Sum.inr (Sum.inr j))) = r j := rfl
    rw [this, acc_val r ((j : ℕ) + 1) (by omega) (by have := j.2; omega)]
    congr 1
  have hjlt : (j : ℕ) < k := j.2
  -- arg1 = g-(3k+2) → acc z (j+2)
  have hE1 : HJO.extend (fun i => (n i : ℤ)) ((gapEquiv_minus k hk (Sum.inr (Sum.inr j)) : ℕ) - (3 + (3 * k - 1)))
      = (acc z ((j : ℕ) + 2) : ℤ) := by
    rw [hval]
    by_cases hjk : (j : ℕ) + 1 < k
    · rw [show 6 * k - 5 - 3 * (j : ℕ) - (3 + (3 * k - 1)) = 3 * (k - (j : ℕ) - 1) - 4 by omega,
        extend_natCast, extendNat_z4_read_minus k hk n (k - (j : ℕ) - 1) (by omega) (by omega), hz,
        show k - (k - (j : ℕ) - 1) + 1 = (j : ℕ) + 2 by omega]
    · rw [show 6 * k - 5 - 3 * (j : ℕ) - (3 + (3 * k - 1)) = 0 by omega,
        extend_natCast, HJO.extendNat_gaps_zero]
      have : acc z ((j : ℕ) + 2) = 0 := by rw [acc, dif_neg (by omega)]
      rw [this]
  -- arg3 = g-(3k-1) → acc z (j+1)
  have hE3 : HJO.extend (fun i => (n i : ℤ)) ((gapEquiv_minus k hk (Sum.inr (Sum.inr j)) : ℕ) - (3 * k - 1))
      = (acc z ((j : ℕ) + 1) : ℤ) := by
    rw [hval]
    by_cases hjk : (j : ℕ) + 1 < k
    · rw [show 6 * k - 5 - 3 * (j : ℕ) - (3 * k - 1) = 3 * (k - (j : ℕ) - 1) - 1 by omega,
        extend_natCast, extendNat_z1_read_minus k hk n (k - (j : ℕ) - 1) (by omega) (by omega), hz,
        show k - (k - (j : ℕ) - 1) = (j : ℕ) + 1 by omega]
    · rw [show 6 * k - 5 - 3 * (j : ℕ) - (3 * k - 1) = 0 by omega,
        extend_natCast, HJO.extendNat_gaps_zero]
      have : acc z ((j : ℕ) + 1) = 0 := by rw [acc, dif_neg (by omega)]
      rw [this]
  -- arg2 = g-3 → if j+1<k then acc r (j+2) else acc a 1
  have hE2 : HJO.extend (fun i => (n i : ℤ)) ((gapEquiv_minus k hk (Sum.inr (Sum.inr j)) : ℕ) - 3)
      = (↑(if (j : ℕ) + 1 < k then acc r ((j : ℕ) + 2) else acc a 1) : ℤ) := by
    rw [hval]
    by_cases hjk : (j : ℕ) + 1 < k
    · rw [if_pos hjk]
      have hset : 6 * k - 5 - 3 * (j : ℕ) - 3
          = 6 * k - 5 - 3 * (((⟨(j : ℕ) + 1, by omega⟩ : Fin k)) : ℕ) := by
        simp only [Fin.val_mk]; omega
      rw [hset, extend_natCast, extendNat_rgap_read_minus k hk n (⟨(j : ℕ) + 1, by omega⟩ : Fin k)]
      rw [acc_val r ((j : ℕ) + 2) (by omega) (by omega)]
      have hfe : (⟨(j : ℕ) + 2 - 1, by have := j.2; omega⟩ : Fin k)
          = (⟨(j : ℕ) + 1, by omega⟩ : Fin k) := by apply Fin.ext; simp
      rw [hfe]
    · rw [if_neg hjk]
      have hjeq : (j : ℕ) = k - 1 := by omega
      have hset : 6 * k - 5 - 3 * (j : ℕ) - 3
          = 3 * (k - 1 - (((⟨0, by omega⟩ : Fin (k - 1)) : ℕ))) - 2 := by
        simp only [Fin.val_mk]; omega
      rw [hset, extend_natCast, extendNat_agap_read_minus k hk n (⟨0, by omega⟩ : Fin (k - 1))]
      rw [acc_val a 1 (by omega) (by omega)]
  unfold HJO.multiplicand
  beta_reduce
  rw [hnj, hE1, hE2, hE3]
  -- cone inequalities
  have hzr_j1 : acc z ((j : ℕ) + 1) ≤ acc r ((j : ℕ) + 1) := by
    rcases Nat.lt_or_ge ((j : ℕ) + 1) k with hlt | hge
    · have := hcone.rz (i := (j : ℕ) + 1) (by simp only [Finset.mem_Icc]; omega)
      rw [show acc (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) ((j : ℕ) + 1)
            = acc r ((j : ℕ) + 1) from ?_] at this
      · simpa [hr, hz] using this
      · simp only [acc, dif_pos (show 1 ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ k - 1 from ⟨by omega, by omega⟩),
          dif_pos (show 1 ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ k from ⟨by omega, by omega⟩)]
        congr 1
    · -- j+1 ≥ k so j = k-1, j+1 = k: acc z k = 0 ≤ acc r k
      have : acc z ((j : ℕ) + 1) = 0 := by rw [acc, dif_neg (by omega)]
      rw [this]; omega
  have hz2le1 : acc z ((j : ℕ) + 2) ≤ acc z ((j : ℕ) + 1) := acc_succ_le hcone.antitone_z (by omega)
  have hz2le_r : acc z ((j : ℕ) + 2) ≤ acc r ((j : ℕ) + 1) := le_trans hz2le1 hzr_j1
  have hmidle : (if (j : ℕ) + 1 < k then acc r ((j : ℕ) + 2) else acc a 1)
      ≤ acc r ((j : ℕ) + 1) := by
    by_cases hjk : (j : ℕ) + 1 < k
    · rw [if_pos hjk]; exact acc_succ_le hcone.antitone_r (by omega)
    · rw [if_neg hjk]
      have hjeq : (j : ℕ) = k - 1 := by omega
      have h1 : acc a 1 ≤ acc r k := hcone.a1_le_rk
      have : acc r ((j : ℕ) + 1) = acc r k := by rw [hjeq]; congr 1; omega
      rw [this]; exact h1
  rw [ESQ_natCast_sub (acc r ((j : ℕ)+1)) (acc z ((j : ℕ)+2)) hz2le_r,
    ESQInv_natCast_sub (acc r ((j : ℕ)+1)) _ hmidle,
    ESQInv_natCast_sub (acc r ((j : ℕ)+1)) (acc z ((j : ℕ)+1)) hzr_j1]


/-! ## Lemma 3.5 reassembly (Statement 6), minus (`b = 3k-1`): mirror decomposition. -/


/-- **Layer 4 (telescoping): `a`-Gaussian block expansion (minus).**  For `a : Fin (k-1) → ℕ`
(so `acc a k = 0`), the `a`-Gaussian block over `Icc 1 (k-1)` expands. -/
lemma aGaussianBlock_expand_minus (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ℕ) (a : Fin (k - 1) → ℕ)
    (ha : Antitone a) (ha1 : acc a 1 ≤ acc r k) (hQbin : Fact6) :
    (∏ i ∈ Icc 1 (k - 1), qChoose qX (aacc (acc r k) a (i - 1)) (acc a i))
      = qPochhammer qX qX (acc r k)
          * invOfUnit (qPochhammer qX qX (acc r k - acc a 1)) 1
          * ∏ i ∈ Icc 1 (k - 1), invOfUnit (qPochhammer qX qX (acc a i - acc a (i + 1))) 1 := by
  set Prk := qPochhammer qX qX (acc r k) with hPrk
  -- acc a k = 0 since k = (k-1)+1 is out of range for a : Fin (k-1) → ℕ
  have hkm1 : k - 1 + 1 = k := by omega
  have hakm1 : acc a k = 0 := by
    rw [acc]; rw [dif_neg]; omega
  have haccdec : ∀ i ∈ Icc 1 (k - 1 - 1), acc a (i + 1) ≤ acc a i := by
    intro i hi
    exact acc_succ_le ha (Finset.mem_Icc.1 hi).1
  have htel := telescope_qChoose hQbin (acc a) (k - 1 - 1) haccdec
  have hm1 : k - 1 - 1 + 1 = k - 1 := by omega
  rw [hm1] at htel
  have hLsplit :
      (∏ i ∈ Icc 1 (k - 1), qChoose qX (aacc (acc r k) a (i - 1)) (acc a i))
        = qChoose qX (acc r k) (acc a 1)
            * ∏ j ∈ Icc 1 (k - 1 - 1), qChoose qX (acc a j) (acc a (j + 1)) := by
    rw [show (Icc 1 (k - 1)) = insert 1 (Icc 2 (k - 1)) by
          ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega]
    rw [Finset.prod_insert (by simp only [Finset.mem_Icc]; omega)]
    have hfst : aacc (acc r k) a (1 - 1) = acc r k := by rw [aacc, if_pos rfl]
    rw [hfst]
    congr 1
    apply Finset.prod_bij' (fun (i : ℕ) (_ : i ∈ Icc 2 (k - 1)) => i - 1)
      (fun (j : ℕ) (_ : j ∈ Icc 1 (k - 1 - 1)) => j + 1)
    · intro i hi; simp only [Finset.mem_Icc] at *; omega
    · intro j hj; simp only [Finset.mem_Icc] at *; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi; omega
    · intro j hj; simp only [Finset.mem_Icc] at hj; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi
      have haacc2 : aacc (acc r k) a (i - 1) = acc a (i - 1) := by
        rw [aacc, if_neg (by omega)]
      rw [haacc2, show i - 1 + 1 = i by omega]
  have hPa1 := poch_mul_inv (acc a 1)
  have htail :
      (∏ j ∈ Icc 1 (k - 1 - 1), qChoose qX (acc a j) (acc a (j + 1)))
        = qPochhammer qX qX (acc a 1)
            * invOfUnit (qPochhammer qX qX (acc a (k - 1))) 1
            * ∏ j ∈ Icc 1 (k - 1 - 1), invOfUnit (qPochhammer qX qX (acc a j - acc a (j + 1))) 1 := by
    have := htel
    have h2 : qPochhammer qX qX (acc a 1)
          * (invOfUnit (qPochhammer qX qX (acc a 1)) 1
              * ∏ j ∈ Icc 1 (k - 1 - 1), qChoose qX (acc a j) (acc a (j + 1)))
        = qPochhammer qX qX (acc a 1)
          * (invOfUnit (qPochhammer qX qX (acc a (k - 1))) 1
              * ∏ j ∈ Icc 1 (k - 1 - 1), invOfUnit (qPochhammer qX qX (acc a j - acc a (j + 1))) 1) := by
      rw [this]
    have hL2 : qPochhammer qX qX (acc a 1)
          * (invOfUnit (qPochhammer qX qX (acc a 1)) 1
              * ∏ j ∈ Icc 1 (k - 1 - 1), qChoose qX (acc a j) (acc a (j + 1)))
        = ∏ j ∈ Icc 1 (k - 1 - 1), qChoose qX (acc a j) (acc a (j + 1)) := by
      rw [← mul_assoc, hPa1, one_mul]
    rw [hL2] at h2
    rw [h2]; ring
  have hfstexp := qChoose_as_inv_poch hQbin (acc r k) (acc a 1) ha1
  have hRHSprod :
      (∏ i ∈ Icc 1 (k - 1), invOfUnit (qPochhammer qX qX (acc a i - acc a (i + 1))) 1)
        = (∏ i ∈ Icc 1 (k - 1 - 1), invOfUnit (qPochhammer qX qX (acc a i - acc a (i + 1))) 1)
            * invOfUnit (qPochhammer qX qX (acc a (k - 1))) 1 := by
    rw [show (Icc 1 (k - 1)) = insert (k - 1) (Icc 1 (k - 1 - 1)) by
          ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega]
    rw [Finset.prod_insert (by simp only [Finset.mem_Icc]; omega)]
    rw [mul_comm]
    congr 2
    -- last term: acc a ((k-1)+1) = acc a k = 0
    rw [show k - 1 + 1 = k by omega, hakm1, Nat.sub_zero]
  rw [hLsplit, htail, hfstexp, hRHSprod]
  set Pa1 := qPochhammer qX qX (acc a 1) with hPa1def
  set IPa1 := invOfUnit (qPochhammer qX qX (acc a 1)) 1 with hIPa1def
  set IPam := invOfUnit (qPochhammer qX qX (acc a (k - 1))) 1 with hIPam
  set IPrka1 := invOfUnit (qPochhammer qX qX (acc r k - acc a 1)) 1 with hIPrka1
  set TP := ∏ i ∈ Icc 1 (k - 1 - 1), invOfUnit (qPochhammer qX qX (acc a i - acc a (i + 1))) 1 with hTP
  have key : Prk * IPa1 * IPrka1 * (Pa1 * IPam * TP)
      = (Pa1 * IPa1) * (Prk * IPrka1 * (TP * IPam)) := by ring
  rw [key, hPa1, one_mul]

/-- **Layer 4 (telescoping): `z`-Gaussian block expansion (minus).** -/
lemma zGaussianBlock_expand_minus (k : ℕ) (hk : 2 ≤ k) (r' z : Fin (k - 1) → ℕ)
    (hz : Antitone z) (hzr : ∀ i ∈ Icc 1 (k - 1), acc z i ≤ acc r' i) (hQbin : Fact6) :
    (∏ i ∈ Icc 1 (k - 1), qChoose qX (acc r' i - acc z (i + 1)) (acc z i - acc z (i + 1)))
      = ∏ i ∈ Icc 1 (k - 1),
          qPochhammer qX qX (acc r' i - acc z (i + 1))
            * invOfUnit (qPochhammer qX qX (acc z i - acc z (i + 1))) 1
            * invOfUnit (qPochhammer qX qX (acc r' i - acc z i)) 1 := by
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  have hzsucc : acc z (i + 1) ≤ acc z i := acc_succ_le hz hi1
  have hzri : acc z i ≤ acc r' i := hzr i hi
  have hjleN : acc z i - acc z (i + 1) ≤ acc r' i - acc z (i + 1) := by omega
  have hNj : (acc r' i - acc z (i + 1)) - (acc z i - acc z (i + 1)) = acc r' i - acc z i := by omega
  rw [qChoose_as_inv_poch hQbin _ _ hjleN, hNj]

/-- **On-cone block factorization (minus).** -/
lemma pochProduct_eq_outer_sbMinusBody_onCone_minus (k : ℕ) (hk : 2 ≤ k) (hQbin : Fact6)
    (n : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (hcone : OnConeM k (rOfGap_minus k hk n) (aOfGap_minus k hk n) (zOfGap_minus k hk n)) :
    (∏ i, HJO.multiplicand (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) (fun i => (n i : ℤ)) i)
      = outerFactorP k (rOfGap_minus k hk n)
          * (∏ i ∈ Icc 1 (k - 1),
              qChoose qX (aacc (acc (rOfGap_minus k hk n) k) (aOfGap_minus k hk n) (i - 1))
                (acc (aOfGap_minus k hk n) i))
          * (∏ i ∈ Icc 1 (k - 1),
              qChoose qX
                (acc (fun i : Fin (k - 1) => rOfGap_minus k hk n (Fin.castLE (by omega) i)) i
                  - acc (zOfGap_minus k hk n) (i + 1))
                (acc (zOfGap_minus k hk n) i - acc (zOfGap_minus k hk n) (i + 1))) := by
  set r := rOfGap_minus k hk n with hr
  set a := aOfGap_minus k hk n with ha
  set z := zOfGap_minus k hk n with hz
  set r' := (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) with hr'
  -- ============ LHS: reindex through gapEquiv_minus and split into Z/A/R blocks ============
  have hLHS :
      (∏ i, HJO.multiplicand (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) (fun i => (n i : ℤ)) i)
        = (∏ i ∈ Icc 1 (k - 1), invOfUnit (qPochhammer qX qX (acc z i - acc z (i + 1))) 1)
          * ((∏ i ∈ Icc 1 (k - 1), invOfUnit (qPochhammer qX qX (acc a i - acc a (i + 1))) 1)
            * (∏ i ∈ Icc 1 k,
                qPochhammer qX qX (acc r i - acc z (i + 1))
                  * invOfUnit (qPochhammer qX qX
                      (acc r i - (if i < k then acc r (i + 1) else acc a 1))) 1
                  * invOfUnit (qPochhammer qX qX (acc r i - acc z i)) 1)) := by
    rw [← Equiv.prod_comp (gapEquiv_minus k hk)
      (fun x => HJO.multiplicand (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) (fun i => (n i : ℤ)) x)]
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    rw [Finset.prod_congr rfl (fun j _ => multiplicand_zfactor_minus k hk n hcone j)]
    rw [Finset.prod_congr rfl (fun j _ => multiplicand_afactor_minus k hk n hcone j)]
    rw [Finset.prod_congr rfl (fun j _ => multiplicand_rfactor_minus k hk n hcone j)]
    rw [show (fun (j : Fin (k - 1)) =>
        invOfUnit (qPochhammer qX qX (acc z ((j : ℕ) + 1) - acc z ((j : ℕ) + 2))) 1)
        = (fun (j : Fin (k - 1)) => (fun i => invOfUnit (qPochhammer qX qX (acc z i - acc z (i + 1))) 1) ((j : ℕ) + 1))
        from by funext j; norm_num]
    rw [prod_fin_shift_eq_Icc (k - 1) (fun i => invOfUnit (qPochhammer qX qX (acc z i - acc z (i + 1))) 1)]
    rw [show (fun (j : Fin (k - 1)) =>
        invOfUnit (qPochhammer qX qX (acc a ((j : ℕ) + 1) - acc a ((j : ℕ) + 2))) 1)
        = (fun (j : Fin (k - 1)) => (fun i => invOfUnit (qPochhammer qX qX (acc a i - acc a (i + 1))) 1) ((j : ℕ) + 1))
        from by funext j; norm_num]
    rw [prod_fin_shift_eq_Icc (k - 1) (fun i => invOfUnit (qPochhammer qX qX (acc a i - acc a (i + 1))) 1)]
    rw [show (fun (j : Fin k) =>
        qPochhammer qX qX (acc r ((j : ℕ) + 1) - acc z ((j : ℕ) + 2))
          * invOfUnit (qPochhammer qX qX
              (acc r ((j : ℕ) + 1) - (if (j : ℕ) + 1 < k then acc r ((j : ℕ) + 2) else acc a 1))) 1
          * invOfUnit (qPochhammer qX qX (acc r ((j : ℕ) + 1) - acc z ((j : ℕ) + 1))) 1)
        = (fun (j : Fin k) => (fun i =>
            qPochhammer qX qX (acc r i - acc z (i + 1))
              * invOfUnit (qPochhammer qX qX (acc r i - (if i < k then acc r (i + 1) else acc a 1))) 1
              * invOfUnit (qPochhammer qX qX (acc r i - acc z i)) 1) ((j : ℕ) + 1))
        from by funext j; norm_num]
    rw [prod_fin_shift_eq_Icc k (fun i =>
        qPochhammer qX qX (acc r i - acc z (i + 1))
          * invOfUnit (qPochhammer qX qX (acc r i - (if i < k then acc r (i + 1) else acc a 1))) 1
          * invOfUnit (qPochhammer qX qX (acc r i - acc z i)) 1)]
  rw [hLHS]
  -- ============ RHS: expand the outer, a-block and z-block ============
  rw [aGaussianBlock_expand_minus k hk r a hcone.antitone_a hcone.a1_le_rk hQbin,
      zGaussianBlock_expand_minus k hk r' z hcone.antitone_z
        (fun i hi => hcone.rz hi) hQbin]
  -- Split the z-Gaussian 3-factor product (over Icc 1(k-1)) into three separate products.
  rw [show (∏ i ∈ Icc 1 (k - 1),
        qPochhammer qX qX (acc r' i - acc z (i + 1))
          * invOfUnit (qPochhammer qX qX (acc z i - acc z (i + 1))) 1
          * invOfUnit (qPochhammer qX qX (acc r' i - acc z i)) 1)
      = (∏ i ∈ Icc 1 (k - 1), qPochhammer qX qX (acc r' i - acc z (i + 1)))
          * (∏ i ∈ Icc 1 (k - 1), invOfUnit (qPochhammer qX qX (acc z i - acc z (i + 1))) 1)
          * (∏ i ∈ Icc 1 (k - 1), invOfUnit (qPochhammer qX qX (acc r' i - acc z i)) 1)
      from by rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]]
  -- Split the LHS R-block's 3-factor product (over Icc 1 k) likewise.
  rw [show (∏ i ∈ Icc 1 k,
        qPochhammer qX qX (acc r i - acc z (i + 1))
          * invOfUnit (qPochhammer qX qX (acc r i - (if i < k then acc r (i + 1) else acc a 1))) 1
          * invOfUnit (qPochhammer qX qX (acc r i - acc z i)) 1)
      = (∏ i ∈ Icc 1 k, qPochhammer qX qX (acc r i - acc z (i + 1)))
          * (∏ i ∈ Icc 1 k,
              invOfUnit (qPochhammer qX qX (acc r i - (if i < k then acc r (i + 1) else acc a 1))) 1)
          * (∏ i ∈ Icc 1 k, invOfUnit (qPochhammer qX qX (acc r i - acc z i)) 1)
      from by rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]]
  -- interior values of `r` on Icc 1(k-1) coincide with the trimmed `r'`.
  have hr'_eq : ∀ i ∈ Icc 1 (k - 1), acc r' i = acc r i := by
    intro i hi
    simp only [Finset.mem_Icc] at hi
    rw [hr']
    rw [acc_val r' i (by omega) (by have := hi.2; omega),
        acc_val r i (by omega) (by omega)]
    rfl
  -- Split the R-block's "if" middle product at i=k into interior (i<k) and boundary (i=k).
  have hRmid :
      (∏ i ∈ Icc 1 k,
          invOfUnit (qPochhammer qX qX (acc r i - (if i < k then acc r (i + 1) else acc a 1))) 1)
        = (∏ i ∈ Icc 1 (k - 1), invOfUnit (qPochhammer qX qX (acc r i - acc r (i + 1))) 1)
            * invOfUnit (qPochhammer qX qX (acc r k - acc a 1)) 1 := by
    rw [show (Icc 1 k) = insert k (Icc 1 (k - 1)) by
          ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega]
    rw [Finset.prod_insert (by simp only [Finset.mem_Icc]; omega)]
    rw [if_neg (by omega), mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Finset.mem_Icc] at hi
    rw [if_pos (by omega)]
  rw [hRmid]
  -- Split the R-block's PZ and RZ products at i=k; convert interior to `r'`.
  have hPZsplit :
      (∏ i ∈ Icc 1 k, qPochhammer qX qX (acc r i - acc z (i + 1)))
        = (∏ i ∈ Icc 1 (k - 1), qPochhammer qX qX (acc r' i - acc z (i + 1)))
            * qPochhammer qX qX (acc r k - acc z (k + 1)) := by
    rw [show (Icc 1 k) = insert k (Icc 1 (k - 1)) by
          ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega]
    rw [Finset.prod_insert (by simp only [Finset.mem_Icc]; omega), mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [hr'_eq i hi]
  have hRZsplit :
      (∏ i ∈ Icc 1 k, invOfUnit (qPochhammer qX qX (acc r i - acc z i)) 1)
        = (∏ i ∈ Icc 1 (k - 1), invOfUnit (qPochhammer qX qX (acc r' i - acc z i)) 1)
            * invOfUnit (qPochhammer qX qX (acc r k - acc z k)) 1 := by
    rw [show (Icc 1 k) = insert k (Icc 1 (k - 1)) by
          ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega]
    rw [Finset.prod_insert (by simp only [Finset.mem_Icc]; omega), mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [hr'_eq i hi]
  rw [hPZsplit, hRZsplit]
  -- boundary z-terms vanish: z : Fin (k-1) → ℕ so acc z k = acc z (k+1) = 0.
  have hzk : acc z k = 0 := by rw [acc]; rw [dif_neg]; omega
  have hzk1 : acc z (k + 1) = 0 := by rw [acc]; rw [dif_neg]; omega
  simp only [hzk, hzk1, Nat.sub_zero]
  rw [outerFactorP_expand k (by omega) r hcone.antitone_r hQbin]
  ring

/-- **On-cone kernel identity (minus).** -/
lemma multiplicand_onCone_eq_minus (k : ℕ) (hk : 2 ≤ k) (hQbin : Fact6)
    (n : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (hguard : ∀ j : Fin k, HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) = rOfGap_minus k hk n j)
    (hcone : OnConeM k (rOfGap_minus k hk n) (aOfGap_minus k hk n) (zOfGap_minus k hk n)) :
    (∏ i, HJO.multiplicand (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) (fun i => (n i : ℤ)) i)
        * X ^ ((HJO.Q' (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) (fun i => (n i : ℤ))).toNat)
      = outerFactorP k (rOfGap_minus k hk n)
          * sbMinusBody k (rOfGap_minus k hk n) n := by
  set r := rOfGap_minus k hk n with hr
  set a := aOfGap_minus k hk n with ha
  set z := zOfGap_minus k hk n with hz
  set r' := (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) with hr'
  have hdom : domAZ r' (acc r k) a z := hcone.domAZ
  obtain ⟨hAa, hs, hAz, hzr⟩ := hdom
  -- Convert the `sbMinusBody` extendNat product (index `j`) to the acc-form
  -- a-block · z-block product (index `i = k - j`), FACTS-FREE.
  have hprodeq :
      (∏ j ∈ Icc 1 (k - 1),
        (qChoose (X : ℤ⟦X⟧) (HJO.extendNat n (3 * j + 1)) (HJO.extendNat n (3 * j - 2))
          * HJO.SumToSum.extendedQChoose (X : ℤ⟦X⟧)
              ((acc r (k - j) : ℤ) - (HJO.extendNat n (3 * j - 4) : ℤ))
              ((HJO.extendNat n (3 * j - 1) : ℤ) - (HJO.extendNat n (3 * j - 4) : ℤ))))
        = ∏ i ∈ Icc 1 (k - 1),
            (qChoose qX (aacc (acc r k) a (i - 1)) (acc a i)
              * qChoose qX (acc r' i - acc z (i + 1)) (acc z i - acc z (i + 1))) := by
    refine Finset.prod_nbij' (fun j => k - j) (fun i => k - i) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Icc] at *; omega
    · intro i hi; simp only [Finset.mem_Icc] at *; omega
    · intro j hj; simp only [Finset.mem_Icc] at hj; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi; omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      have hj1 : 1 ≤ j := hj.1
      have hjk : j ≤ k - 1 := hj.2
      have hjk' : j < k := by omega
      have acc_r' : acc r' (k - j) = acc r (k - j) := by
        simp only [acc, hr',
          dif_pos (show 1 ≤ k - j ∧ k - j ≤ k - 1 from ⟨by omega, by omega⟩),
          dif_pos (show 1 ≤ k - j ∧ k - j ≤ k from ⟨by omega, by omega⟩)]
        congr 1
      rw [extendNat_a1_read_minus k hk r n hr.symm j hj1 hjk,
        extendNat_a2_read_minus k hk n j hj1 hjk',
        extendNat_z1_read_minus k hk n j hj1 hjk',
        extendNat_z4_read_minus k hk n j hj1 hjk']
      have hzr' : acc z (k - j) ≤ acc r' (k - j) := by
        have := hzr (k - j) (by simp only [Finset.mem_Icc]; omega); simpa [hz] using this
      have hzshift : acc z (k - j + 1) ≤ acc z (k - j) := by
        have : acc (zOfGap_minus k hk n) (k - j + 1) ≤ acc (zOfGap_minus k hk n) (k - j) :=
          acc_succ_le hAz (by omega)
        simpa [hz] using this
      have h1 : (0 : ℤ) ≤ (acc r' (k - j) : ℤ) - (acc z (k - j + 1) : ℤ) := by
        have hle : acc z (k - j + 1) ≤ acc r' (k - j) := le_trans hzshift hzr'
        have := (Nat.cast_le (α := ℤ)).2 hle; omega
      have h2 : (0 : ℤ) ≤ (acc z (k - j) : ℤ) - (acc z (k - j + 1) : ℤ) := by
        have := (Nat.cast_le (α := ℤ)).2 hzshift; omega
      rw [show ((acc r (k - j) : ℤ)) = ((acc r' (k - j) : ℤ)) by rw [acc_r']]
      rw [HJO.SumToSum.extendedQChoose_of_nonneg h1 h2,
        show ((acc r' (k - j) : ℤ) - (acc z (k - j + 1) : ℤ)).toNat
          = acc r' (k - j) - acc z (k - j + 1) from Int.toNat_sub _ _,
        show ((acc z (k - j) : ℤ) - (acc z (k - j + 1) : ℤ)).toNat
          = acc z (k - j) - acc z (k - j + 1) from Int.toNat_sub _ _]
  -- Now assemble: expand sbMinusBody, split combined product, apply pochProduct.
  rw [sbMinusBody, hprodeq, Finset.prod_mul_distrib,
    pochProduct_eq_outer_sbMinusBody_onCone_minus k hk hQbin n hcone]
  ring

/-- **Bridge lemma (minus).** -/
lemma onCone_of_cone'_minus (k : ℕ) (hk : 2 ≤ k)
    (n : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (hcone : (fun i => (n i : ℤ)) ∈ HJO.cone' (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1)) :
    OnConeM k (rOfGap_minus k hk n) (aOfGap_minus k hk n) (zOfGap_minus k hk n) := by
  obtain ⟨-, hstep3, hstepK⟩ := hcone
  -- ℕ-level shift-by-3 monotonicity.
  have N3 : ∀ (i : (finspan {3, 3 * k - 1}).gaps) (h : ((i : ℕ) + 3) ∈ (finspan {3, 3 * k - 1}).gaps),
      n i ≤ n ⟨(i : ℕ) + 3, h⟩ := by
    intro i h
    have h2 := hstep3 i h
    simp only [] at h2
    exact_mod_cast h2
  -- ℕ-level shift-by-(3k-1) monotonicity.
  have NK : ∀ (i : (finspan {3, 3 * k - 1}).gaps) (h : ((i : ℕ) + (3 * k - 1)) ∈ (finspan {3, 3 * k - 1}).gaps),
      n i ≤ n ⟨(i : ℕ) + (3 * k - 1), h⟩ := by
    intro i h
    have h2 := hstepK i h
    simp only [] at h2
    exact_mod_cast h2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Antitone r  (R gaps 6k-5-3j; shift-by-3)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Fin.antitone_iff_succ_le]
    intro j
    rw [rOfGap_minus_apply, rOfGap_minus_apply]
    show n ⟨6 * (k'+1) - 5 - 3 * (j.succ : ℕ), memR_minus (k'+1) hk j.succ⟩
        ≤ n ⟨6 * (k'+1) - 5 - 3 * (j.castSucc : ℕ), memR_minus (k'+1) hk j.castSucc⟩
    have hjlt : (j : ℕ) + 1 < (k'+1) := by have := j.2; omega
    have hmemS : (6 * (k'+1) - 5 - 3 * ((j : ℕ) + 1)) ∈ (finspan {3, 3 * (k'+1) - 1}).gaps := by
      have := memR_minus (k'+1) hk j.succ; simpa [Fin.val_succ] using this
    have haddr : (6 * (k'+1) - 5 - 3 * ((j : ℕ) + 1)) + 3 = 6 * (k'+1) - 5 - 3 * (j : ℕ) := by omega
    have hplus : (6 * (k'+1) - 5 - 3 * ((j : ℕ) + 1)) + 3 ∈ (finspan {3, 3 * (k'+1) - 1}).gaps := by
      rw [haddr]; exact memR_minus (k'+1) hk j.castSucc
    have hle := N3 ⟨6 * (k'+1) - 5 - 3 * ((j : ℕ) + 1), hmemS⟩ hplus
    have hsub : (⟨(6 * (k'+1) - 5 - 3 * ((j : ℕ) + 1)) + 3, hplus⟩ : (finspan {3, 3 * (k'+1) - 1}).gaps)
        = ⟨6 * (k'+1) - 5 - 3 * (j.castSucc : ℕ), memR_minus (k'+1) hk j.castSucc⟩ := by
      apply Subtype.ext; simp only [Fin.coe_castSucc]; omega
    rw [hsub] at hle
    have hmatch : (⟨6 * (k'+1) - 5 - 3 * (j.succ : ℕ), memR_minus (k'+1) hk j.succ⟩ : (finspan {3, 3 * (k'+1) - 1}).gaps)
        = ⟨6 * (k'+1) - 5 - 3 * ((j : ℕ) + 1), hmemS⟩ := by
      apply Subtype.ext; simp only [Fin.val_succ]
    rw [hmatch]; exact hle
  · -- Antitone a  (A gaps 3(k-1-j)-2; a,z : Fin(k-1); shift-by-3)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    apply Fin.antitone_iff_succ_le.mpr
    intro j
    rw [aOfGap_minus_apply, aOfGap_minus_apply]
    show n ⟨3 * ((k'+2) - 1 - (j.succ : ℕ)) - 2, memA_minus (k'+2) hk j.succ⟩
        ≤ n ⟨3 * ((k'+2) - 1 - (j.castSucc : ℕ)) - 2, memA_minus (k'+2) hk j.castSucc⟩
    have hjlt : (j : ℕ) + 1 < (k'+2) - 1 := by have := j.2; omega
    have hmemS : (3 * ((k'+2) - 1 - ((j : ℕ) + 1)) - 2) ∈ (finspan {3, 3 * (k'+2) - 1}).gaps := by
      have := memA_minus (k'+2) hk j.succ; simpa [Fin.val_succ] using this
    have haddr : (3 * ((k'+2) - 1 - ((j : ℕ) + 1)) - 2) + 3 = 3 * ((k'+2) - 1 - (j : ℕ)) - 2 := by
      omega
    have hplus : (3 * ((k'+2) - 1 - ((j : ℕ) + 1)) - 2) + 3 ∈ (finspan {3, 3 * (k'+2) - 1}).gaps := by
      rw [haddr]; exact memA_minus (k'+2) hk j.castSucc
    have hle := N3 ⟨3 * ((k'+2) - 1 - ((j : ℕ) + 1)) - 2, hmemS⟩ hplus
    have hsub : (⟨(3 * ((k'+2) - 1 - ((j : ℕ) + 1)) - 2) + 3, hplus⟩ : (finspan {3, 3 * (k'+2) - 1}).gaps)
        = ⟨3 * ((k'+2) - 1 - (j.castSucc : ℕ)) - 2, memA_minus (k'+2) hk j.castSucc⟩ := by
      apply Subtype.ext; simp only [Fin.coe_castSucc]; omega
    rw [hsub] at hle
    have hmatch : (⟨3 * ((k'+2) - 1 - (j.succ : ℕ)) - 2, memA_minus (k'+2) hk j.succ⟩ : (finspan {3, 3 * (k'+2) - 1}).gaps)
        = ⟨3 * ((k'+2) - 1 - ((j : ℕ) + 1)) - 2, hmemS⟩ := by
      apply Subtype.ext; simp only [Fin.val_succ]
    rw [hmatch]; exact hle
  · -- acc a 1 ≤ acc r k   :  a 0 = n(gap 3(k-1)-2 = 3k-5);  r(k-1) = n(gap 6k-5-3(k-1) = 3k-2); shift-by-3
    rw [acc, dif_pos (by omega), acc, dif_pos (by omega)]
    rw [aOfGap_minus_apply, rOfGap_minus_apply]
    have ha0 : (⟨(1:ℕ) - 1, by omega⟩ : Fin (k - 1)) = (⟨0, by omega⟩ : Fin (k - 1)) := by
      apply Fin.ext; simp
    have hrk : (⟨k - 1, by omega⟩ : Fin k) = (⟨k - 1, by omega⟩ : Fin k) := rfl
    rw [ha0]
    show n ⟨3 * (k - 1 - ((⟨0, by omega⟩ : Fin (k-1)) : ℕ)) - 2, memA_minus k hk ⟨0, by omega⟩⟩
        ≤ n ⟨6 * k - 5 - 3 * ((⟨k - 1, by omega⟩ : Fin k) : ℕ), memR_minus k hk ⟨k - 1, by omega⟩⟩
    have hmemS : (3 * (k - 1 - (0 : ℕ)) - 2) ∈ (finspan {3, 3 * k - 1}).gaps := by
      have := memA_minus k hk ⟨0, by omega⟩; simpa using this
    have haddr : (3 * (k - 1 - (0 : ℕ)) - 2) + 3
        = 6 * k - 5 - 3 * ((⟨k - 1, by omega⟩ : Fin k) : ℕ) := by
      simp only []; omega
    have hplus : (3 * (k - 1 - (0 : ℕ)) - 2) + 3 ∈ (finspan {3, 3 * k - 1}).gaps := by
      rw [haddr]; exact memR_minus k hk ⟨k - 1, by omega⟩
    have hle := N3 ⟨3 * (k - 1 - (0 : ℕ)) - 2, hmemS⟩ hplus
    have hsub : (⟨(3 * (k - 1 - (0 : ℕ)) - 2) + 3, hplus⟩ : (finspan {3, 3 * k - 1}).gaps)
        = ⟨6 * k - 5 - 3 * ((⟨k - 1, by omega⟩ : Fin k) : ℕ), memR_minus k hk ⟨k - 1, by omega⟩⟩ := by
      apply Subtype.ext; simp only []; omega
    rw [hsub] at hle
    have hmatchS : (⟨3 * (k - 1 - ((⟨0, by omega⟩ : Fin (k-1)) : ℕ)) - 2, memA_minus k hk ⟨0, by omega⟩⟩
          : (finspan {3, 3 * k - 1}).gaps)
        = ⟨3 * (k - 1 - (0 : ℕ)) - 2, hmemS⟩ := by
      apply Subtype.ext; simp
    rw [hmatchS]; exact hle
  · -- Antitone z  (Z gaps 3(k-1-j)-1; z : Fin(k-1); shift-by-3)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    apply Fin.antitone_iff_succ_le.mpr
    intro j
    rw [zOfGap_minus_apply, zOfGap_minus_apply]
    show n ⟨3 * ((k'+2) - 1 - (j.succ : ℕ)) - 1, memZ_minus (k'+2) hk j.succ⟩
        ≤ n ⟨3 * ((k'+2) - 1 - (j.castSucc : ℕ)) - 1, memZ_minus (k'+2) hk j.castSucc⟩
    have hjlt : (j : ℕ) + 1 < (k'+2) - 1 := by have := j.2; omega
    have hmemS : (3 * ((k'+2) - 1 - ((j : ℕ) + 1)) - 1) ∈ (finspan {3, 3 * (k'+2) - 1}).gaps := by
      have := memZ_minus (k'+2) hk j.succ; simpa [Fin.val_succ] using this
    have haddr : (3 * ((k'+2) - 1 - ((j : ℕ) + 1)) - 1) + 3 = 3 * ((k'+2) - 1 - (j : ℕ)) - 1 := by
      omega
    have hplus : (3 * ((k'+2) - 1 - ((j : ℕ) + 1)) - 1) + 3 ∈ (finspan {3, 3 * (k'+2) - 1}).gaps := by
      rw [haddr]; exact memZ_minus (k'+2) hk j.castSucc
    have hle := N3 ⟨3 * ((k'+2) - 1 - ((j : ℕ) + 1)) - 1, hmemS⟩ hplus
    have hsub : (⟨(3 * ((k'+2) - 1 - ((j : ℕ) + 1)) - 1) + 3, hplus⟩ : (finspan {3, 3 * (k'+2) - 1}).gaps)
        = ⟨3 * ((k'+2) - 1 - (j.castSucc : ℕ)) - 1, memZ_minus (k'+2) hk j.castSucc⟩ := by
      apply Subtype.ext; simp only [Fin.coe_castSucc]; omega
    rw [hsub] at hle
    have hmatch : (⟨3 * ((k'+2) - 1 - (j.succ : ℕ)) - 1, memZ_minus (k'+2) hk j.succ⟩ : (finspan {3, 3 * (k'+2) - 1}).gaps)
        = ⟨3 * ((k'+2) - 1 - ((j : ℕ) + 1)) - 1, hmemS⟩ := by
      apply Subtype.ext; simp only [Fin.val_succ]
    rw [hmatch]; exact hle
  · -- ∀ i ∈ Icc 1 (k-1), acc z i ≤ acc r' i   (r' = r ∘ castLE; shift-by-(3k-1))
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [acc, dif_pos ⟨hi.1, by omega⟩]
    -- rhs: acc (fun i => r (castLE _ i)) i  = (fun ...) (i-1) = r (castLE (i-1))
    rw [acc, dif_pos ⟨hi.1, hi.2⟩]
    rw [zOfGap_minus_apply, rOfGap_minus_apply]
    -- t := i-1 : Fin (k-1);  z t = n(gap 3(k-1-t)-1); castLE t = (i-1 : Fin k); r = n(gap 6k-5-3t)
    set t : Fin (k - 1) := ⟨i - 1, by omega⟩ with ht
    show n ⟨3 * (k - 1 - (t : ℕ)) - 1, memZ_minus k hk t⟩
        ≤ n ⟨6 * k - 5 - 3 * ((Fin.castLE (by omega) t : Fin k) : ℕ), memR_minus k hk (Fin.castLE (by omega) t)⟩
    have htlt : (t : ℕ) < k - 1 := t.2
    have hmemS : (3 * (k - 1 - (t : ℕ)) - 1) ∈ (finspan {3, 3 * k - 1}).gaps := memZ_minus k hk t
    have hcastt : ((Fin.castLE (show k - 1 ≤ k by omega) t : Fin k) : ℕ) = (t : ℕ) := by
      simp [Fin.coe_castLE]
    have haddr : (3 * (k - 1 - (t : ℕ)) - 1) + (3 * k - 1) = 6 * k - 5 - 3 * (t : ℕ) := by
      have := htlt; omega
    have hplus : (3 * (k - 1 - (t : ℕ)) - 1) + (3 * k - 1) ∈ (finspan {3, 3 * k - 1}).gaps := by
      rw [haddr]; exact memR_minus k hk (Fin.castLE (by omega) t)
    have hle := NK ⟨3 * (k - 1 - (t : ℕ)) - 1, hmemS⟩ hplus
    have hsub : (⟨(3 * (k - 1 - (t : ℕ)) - 1) + (3 * k - 1), hplus⟩ : (finspan {3, 3 * k - 1}).gaps)
        = ⟨6 * k - 5 - 3 * ((Fin.castLE (by omega) t : Fin k) : ℕ), memR_minus k hk (Fin.castLE (by omega) t)⟩ := by
      apply Subtype.ext; simp only [hcastt]; omega
    rw [hsub] at hle
    exact hle

/-- **Off-cone LHS vanishing (minus).** -/
lemma offCone_lhs_zero_minus (k : ℕ) (hk : 2 ≤ k)
    (n : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (hnot : ¬ OnConeM k (rOfGap_minus k hk n) (aOfGap_minus k hk n) (zOfGap_minus k hk n)) :
    (∏ i, HJO.multiplicand (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) (fun i => (n i : ℤ)) i) = 0 := by
  by_contra hprod
  have hmem : (fun i => (n i : ℤ)) ∈ (⋂ i, Function.support
      fun x => HJO.multiplicand (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) x i) := by
    rw [Set.mem_iInter]
    intro i
    rw [Function.mem_support]
    intro hzero
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
  have hcone : (fun i => (n i : ℤ)) ∈ HJO.cone' (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) :=
    HJO.iInter_support_multiplicand_subset_cone _ _ _ rfl hmem
  exact hnot (onCone_of_cone'_minus k hk n hcone)

/-- **Off-cone RHS vanishing (minus).** -/
lemma offCone_rhs_zero_minus (k : ℕ) (hk : 2 ≤ k)
    (n : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (hnot : ¬ OnConeM k (rOfGap_minus k hk n) (aOfGap_minus k hk n) (zOfGap_minus k hk n)) :
    outerFactorP k (rOfGap_minus k hk n) * sbMinusBody k (rOfGap_minus k hk n) n = 0 := by
  set r := rOfGap_minus k hk n with hr
  by_cases hAr : Antitone r
  · have hdom : ¬ domAZ (fun i : Fin (k - 1) => r (Fin.castLE (by omega) i)) (acc r k)
        (aOfGap_minus k hk n) (zOfGap_minus k hk n) := by
      intro hd
      exact hnot ⟨hAr, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2⟩
    rw [sbMinusBody_vanish_of_not_domAZ k hk r hAr n hr.symm hdom, mul_zero]
  · obtain ⟨i, hi1, hik, hlt⟩ := not_antitone_acc_succ hAr
    have hmem : i ∈ Icc 1 (k - 1) := by simp only [Finset.mem_Icc]; omega
    have hfac0 : qChoose qX (acc r i) (acc r (i + 1)) = 0 := qChoose_eq_zero_of_lt hlt
    rw [outerFactorP, Finset.prod_eq_zero hmem hfac0, mul_zero, zero_mul]

/-- **Per-`n` telescoping kernel (minus)** — mirror of `multiplicand_term_eq_plus` for the gap
set of `⟨3,3k-1⟩`.  For a nonnegative gap-vector `n` with boundary tuple `r = rOfGap_minus k hk n`
satisfying the boundary guard, the `multiplicand` product times `X^{Q(n)}` telescopes into
`outerFactorP k r` times the `SbMinus` summand body `sbMinusBody k r n`.  Both sides vanish off
the cone.  Sole irreducible analytic obstruction of `stmt6_reassembly_minus`. -/
lemma multiplicand_term_eq_minus (k : ℕ) (hk : 2 ≤ k) (hQbin : Fact6)
    (n : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (hguard : ∀ j : Fin k, HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) = rOfGap_minus k hk n j) :
    (∏ i, HJO.multiplicand (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) (fun i => (n i : ℤ)) i)
        * X ^ ((HJO.Q' (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) (fun i => (n i : ℤ))).toNat)
      = outerFactorP k (rOfGap_minus k hk n)
          * sbMinusBody k (rOfGap_minus k hk n) n := by
  by_cases hcone : OnConeM k (rOfGap_minus k hk n) (aOfGap_minus k hk n) (zOfGap_minus k hk n)
  · exact multiplicand_onCone_eq_minus k hk hQbin n hguard hcone
  · rw [offCone_lhs_zero_minus k hk n hcone, zero_mul,
      offCone_rhs_zero_minus k hk n hcone]

/-- Summability of the minus `zNat` summand (via `HJO.summable_of_posDefOn`). -/
lemma zNatTermM_summable (k : ℕ) (hk : 2 ≤ k) (hPD : Fact8 3 (3 * k - 1)) :
    Summable (fun n : (finspan {3, 3 * k - 1}).gaps → ℤ =>
      (∏ i, HJO.multiplicand (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) n i)
        * X ^ ((HJO.Q' (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) n).toNat)) := by
  have hq : QuadraticMap.PosDefOn
      (HJO.Q' (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1))
      (HJO.cone' (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1)) := by
    rw [HJO.Q'_eq_Q]
    exact hPD.2.2.2.1
  exact HJO.summable_of_posDefOn (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) rfl hq

/-- The pointwise ℕ → ℤ cast on gap-vectors (minus). -/
def natCastGapM (k : ℕ) (m : (finspan {3, 3 * k - 1}).gaps → ℕ) :
    (finspan {3, 3 * k - 1}).gaps → ℤ := fun i => (m i : ℤ)

lemma natCastGapM_injective (k : ℕ) : Function.Injective (natCastGapM k) := by
  intro m₁ m₂ h
  funext i
  have := congrFun h i
  simpa [natCastGapM] using this

/-- **Gap B, part 1 (off-`ℕ`-range vanishing, minus).** -/
lemma zNatTermM_vanish_off_natRange (k : ℕ) (hk : 2 ≤ k)
    (n : (finspan {3, 3 * k - 1}).gaps → ℤ) (hn : n ∉ Set.range (natCastGapM k)) :
    (∏ i, HJO.multiplicand (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) n i)
        * X ^ ((HJO.Q' (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) n).toNat) = 0 := by
  have hnge : n ∉ Set.Ici (0 : (finspan {3, 3 * k - 1}).gaps → ℤ) := by
    intro hge
    apply hn
    refine ⟨fun i => (n i).toNat, ?_⟩
    funext i
    simp only [natCastGapM]
    rw [Int.toNat_of_nonneg (hge i)]
  have hncone : n ∉ HJO.cone' (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) := fun hc =>
    hnge (HJO.cone'_subset_Ici_zero _ _ _ hc)
  have hniInter : n ∉ (⋂ i, Function.support
      fun x => HJO.multiplicand (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) x i) := fun hi =>
    hncone (HJO.iInter_support_multiplicand_subset_cone _ _ _ rfl hi)
  rw [Set.mem_iInter] at hniInter
  push_neg at hniInter
  obtain ⟨i, hi⟩ := hniInter
  rw [Function.mem_support, not_not] at hi
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul]

/-- **Gap B, part 2 (antitonicity of the boundary tuple on the support, minus).** -/
lemma rOfGap_minus_antitone_of_nonzero (k : ℕ) (hk : 2 ≤ k)
    (m : (finspan {3, 3 * k - 1}).gaps → ℕ)
    (hm : (∏ i, HJO.multiplicand (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) (natCastGapM k m) i)
        * X ^ ((HJO.Q' (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) (natCastGapM k m)).toNat) ≠ 0) :
    Antitone (rOfGap_minus k hk m) := by
  have hprod : (∏ i, HJO.multiplicand (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1)
      (natCastGapM k m) i) ≠ 0 := left_ne_zero_of_mul hm
  have hmem : natCastGapM k m ∈ (⋂ i, Function.support
      fun x => HJO.multiplicand (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) x i) := by
    rw [Set.mem_iInter]
    intro i
    rw [Function.mem_support]
    intro hzero
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
  have hcone : natCastGapM k m ∈ HJO.cone' (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) :=
    HJO.iInter_support_multiplicand_subset_cone _ _ _ rfl hmem
  obtain ⟨_, hstep3, _⟩ := hcone
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  apply Fin.antitone_iff_succ_le.mpr
  intro j
  rw [rOfGap_minus_apply, rOfGap_minus_apply]
  show m ⟨6 * (k' + 2) - 5 - 3 * (j.succ : ℕ), memR_minus (k' + 2) (by omega) j.succ⟩
      ≤ m ⟨6 * (k' + 2) - 5 - 3 * (j.castSucc : ℕ), memR_minus (k' + 2) (by omega) j.castSucc⟩
  have hjlt : (j : ℕ) < k' + 1 := j.2
  have hmemSmall : (6 * (k' + 2) - 5 - 3 * ((j : ℕ) + 1)) ∈ (finspan {3, 3 * (k' + 2) - 1}).gaps := by
    have := memR_minus (k' + 2) (by omega) j.succ
    simpa [Fin.val_succ] using this
  have haddr : (6 * (k' + 2) - 5 - 3 * ((j : ℕ) + 1)) + 3
      = 6 * (k' + 2) - 5 - 3 * (j : ℕ) := by omega
  have hplus : (6 * (k' + 2) - 5 - 3 * ((j : ℕ) + 1)) + 3 ∈ (finspan {3, 3 * (k' + 2) - 1}).gaps := by
    rw [haddr]; exact memR_minus (k' + 2) (by omega) j.castSucc
  have hle := hstep3 ⟨6 * (k' + 2) - 5 - 3 * ((j : ℕ) + 1), hmemSmall⟩ hplus
  simp only [natCastGapM] at hle
  have hsub : (⟨(6 * (k' + 2) - 5 - 3 * ((j : ℕ) + 1)) + 3, hplus⟩
        : (finspan {3, 3 * (k' + 2) - 1}).gaps)
      = ⟨6 * (k' + 2) - 5 - 3 * (j.castSucc : ℕ), memR_minus (k' + 2) (by omega) j.castSucc⟩ := by
    apply Subtype.ext
    simp only [Fin.coe_castSucc]
    omega
  rw [hsub] at hle
  have hle' : m ⟨6 * (k' + 2) - 5 - 3 * ((j : ℕ) + 1), hmemSmall⟩
      ≤ m ⟨6 * (k' + 2) - 5 - 3 * (j.castSucc : ℕ), memR_minus (k' + 2) (by omega) j.castSucc⟩ := by
    exact_mod_cast hle
  have hmatch : (⟨6 * (k' + 2) - 5 - 3 * (j.succ : ℕ), memR_minus (k' + 2) (by omega) j.succ⟩
        : (finspan {3, 3 * (k' + 2) - 1}).gaps)
      = ⟨6 * (k' + 2) - 5 - 3 * ((j : ℕ) + 1), hmemSmall⟩ := by
    apply Subtype.ext
    simp only [Fin.val_succ]
  rw [hmatch]
  exact hle'

/-- Finite support of the guarded `sbMinusBody` finsum (needed to convert `finsum`↔`tsum`).
Its support injects (via the `(a,z)`-reading, a bijection on the fibre) into the finite `domAZ`
box, bounded coordinatewise by `acc r k` (for `a`) and `acc r' i` (for `z`). -/
lemma sbMinusBody_guard_hasFiniteSupport (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ℕ) (hr : Antitone r) :
    Function.HasFiniteSupport
      (fun n : (finspan {3, 3 * k - 1}).gaps → ℕ =>
        (if ∀ j : Fin k, HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) = r j
          then sbMinusBody k r n else 0)) := by
  classical
  set r' : Fin (k - 1) → ℕ := fun i : Fin (k - 1) => r (Fin.castLE (by omega) i) with hr'_def
  -- The finite `(a,z)`-box.
  set box : Set ((Fin (k - 1) → ℕ) × (Fin (k - 1) → ℕ)) :=
    {p | (∀ j : Fin (k - 1), p.1 j ≤ acc r' 1) ∧ (∀ j : Fin (k - 1), p.2 j ≤ acc r' 1)} with hbox
  have hboxfin : box.Finite := by
    apply Set.Finite.subset (Set.finite_Icc
      ((fun _ => 0, fun _ => 0) : (Fin (k - 1) → ℕ) × (Fin (k - 1) → ℕ))
      ((fun _ => acc r' 1, fun _ => acc r' 1) : (Fin (k - 1) → ℕ) × (Fin (k - 1) → ℕ)))
    intro p hp
    simp only [hbox, Set.mem_setOf_eq] at hp
    simp only [Set.mem_Icc, Prod.le_def, Pi.le_def]
    exact ⟨⟨fun j => Nat.zero_le _, fun j => Nat.zero_le _⟩, ⟨fun j => hp.1 j, fun j => hp.2 j⟩⟩
  -- The support maps injectively (via the (a,z)-reading) into `box`.
  apply Set.Finite.of_finite_image
    (f := fun n => (aOfGap_minus k hk n, zOfGap_minus k hk n)) (hboxfin.subset ?_)
  · -- injectivity of the reading on the support
    intro n₁ hn₁ n₂ hn₂ heq
    rw [Function.mem_support] at hn₁ hn₂
    -- extract the fibre condition (guard holds on the support)
    have hg1 : rOfGap_minus k hk n₁ = r := by
      by_contra hne
      apply hn₁; rw [if_neg]; intro hc; exact hne ((boundary_iff_rOfGap_minus k hk r n₁).1 hc)
    have hg2 : rOfGap_minus k hk n₂ = r := by
      by_contra hne
      apply hn₂; rw [if_neg]; intro hc; exact hne ((boundary_iff_rOfGap_minus k hk r n₂).1 hc)
    -- use fiberEquivAZ_minus injectivity: same (r,a,z) ⇒ same n
    have h1 : (fiberEquivAZ_minus k hk r) ⟨n₁, hg1⟩ = (fiberEquivAZ_minus k hk r) ⟨n₂, hg2⟩ := by
      simp only [fiberEquivAZ_minus, Equiv.coe_fn_mk]; exact heq
    have := (fiberEquivAZ_minus k hk r).injective h1
    exact congrArg Subtype.val this
  · -- image of support ⊆ box
    rintro _ ⟨n, hn, rfl⟩
    rw [Function.mem_support] at hn
    have hg : rOfGap_minus k hk n = r := by
      by_contra hne
      apply hn; rw [if_neg]; intro hc; exact hne ((boundary_iff_rOfGap_minus k hk r n).1 hc)
    -- on the support the guard holds so the body is `sbMinusBody`, which is nonzero ⇒ domAZ
    have hbody : sbMinusBody k r n ≠ 0 := by
      intro h0; apply hn
      rw [if_pos ((boundary_iff_rOfGap_minus k hk r n).2 hg), h0]
    have hdom : domAZ r' (acc r k) (aOfGap_minus k hk n) (zOfGap_minus k hk n) := by
      by_contra hnd
      exact hbody (sbMinusBody_vanish_of_not_domAZ k hk r hr n hg hnd)
    obtain ⟨hAa, hs, hAz, hzr⟩ := hdom
    simp only [hbox, Set.mem_setOf_eq]
    -- helper: for antitone `t : Fin (k-1) → ℕ` and `j`, `t j ≤ acc t 1`.
    have hgen : ∀ (t : Fin (k - 1) → ℕ), Antitone t → ∀ (j : Fin (k - 1)),
        t j ≤ acc t 1 := by
      intro t ht j
      rw [acc_val t 1 (le_refl 1) (by omega)]
      apply ht
      simp only [Fin.le_def]; omega
    -- `acc r k ≤ acc r' 1` since `r` is antitone (`r ⟨k-1⟩ ≤ r ⟨0⟩`).
    have hrk_le : acc r k ≤ acc r' 1 := by
      rw [acc_val r k (by omega) (le_refl k), acc_val r' 1 (le_refl 1) (by omega)]
      simp only [hr'_def]
      apply hr
      simp only [Fin.le_def, Fin.coe_castLE]; omega
    constructor
    · intro j
      -- aⱼ ≤ acc a 1 ≤ acc r k ≤ acc r' 1
      exact le_trans (le_trans (hgen _ hAa j) hs) hrk_le
    · intro j
      -- zⱼ ≤ acc z 1 ≤ acc r' 1
      have hjz : zOfGap_minus k hk n j ≤ acc (zOfGap_minus k hk n) 1 := hgen _ hAz j
      have hz1 : acc (zOfGap_minus k hk n) 1 ≤ acc r' 1 :=
        hzr 1 (by simp only [Finset.mem_Icc]; omega)
      exact le_trans hjz hz1

/-- **Fibre summability (minus).** -/
lemma fibre_summable_minus (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ℕ) (hr : Antitone r) :
    Summable (fun m : {m : (finspan {3, 3 * k - 1}).gaps → ℕ // rOfGap_minus k hk m = r} =>
      sbMinusBody k r m.1) := by
  classical
  set G : ((finspan {3, 3 * k - 1}).gaps → ℕ) → ℤ⟦X⟧ :=
    fun n => (if ∀ j : Fin k, HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) = r j
      then sbMinusBody k r n else 0) with hG
  have hfinG : Function.HasFiniteSupport G := sbMinusBody_guard_hasFiniteSupport k hk r hr
  -- The subtype family equals `G ∘ Subtype.val` (guard holds on the fibre).
  have hsummand : (fun m : {m : (finspan {3, 3 * k - 1}).gaps → ℕ // rOfGap_minus k hk m = r} =>
      sbMinusBody k r m.1) = fun m => G m.1 := by
    funext m
    simp only [hG]
    rw [if_pos ((boundary_iff_rOfGap_minus k hk r m.1).2 m.2)]
  rw [hsummand]
  -- finite support of the subtype family
  have hfinSub : Function.HasFiniteSupport
      (fun m : {m : (finspan {3, 3 * k - 1}).gaps → ℕ // rOfGap_minus k hk m = r} => G m.1) := by
    apply Set.Finite.of_finite_image (f := Subtype.val)
    · apply Set.Finite.subset hfinG
      rintro _ ⟨m, hm, rfl⟩
      rw [Function.mem_support] at hm ⊢; exact hm
    · exact Set.injOn_of_injective Subtype.val_injective
  exact summable_of_hasFiniteSupport hfinSub

/-- **Fibre sum = `SbMinus`.** -/
lemma fibre_tsum_eq_SbMinus (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ℕ) (hr : Antitone r) :
    ∑' m : {m : (finspan {3, 3 * k - 1}).gaps → ℕ // rOfGap_minus k hk m = r},
        sbMinusBody k r m.1
      = SbMinus k r := by
  classical
  set G : ((finspan {3, 3 * k - 1}).gaps → ℕ) → ℤ⟦X⟧ :=
    fun n => (if ∀ j : Fin k, HJO.extendNat n (6 * k - 5 - 3 * (j : ℕ)) = r j
      then sbMinusBody k r n else 0) with hG
  have hfinG : Function.HasFiniteSupport G := sbMinusBody_guard_hasFiniteSupport k hk r hr
  -- subtype summand = G ∘ Subtype.val
  have hsummand : ∀ m : {m : (finspan {3, 3 * k - 1}).gaps → ℕ // rOfGap_minus k hk m = r},
      sbMinusBody k r m.1 = G m.1 := by
    intro m
    simp only [hG]
    rw [if_pos ((boundary_iff_rOfGap_minus k hk r m.1).2 m.2)]
  rw [tsum_congr hsummand]
  -- finite support of the subtype family
  have hfinSub : Function.HasFiniteSupport
      (fun m : {m : (finspan {3, 3 * k - 1}).gaps → ℕ // rOfGap_minus k hk m = r} => G m.1) := by
    apply Set.Finite.of_finite_image (f := Subtype.val)
    · apply Set.Finite.subset hfinG
      rintro _ ⟨m, hm, rfl⟩
      rw [Function.mem_support] at hm ⊢; exact hm
    · exact Set.injOn_of_injective Subtype.val_injective
  rw [tsum_eq_finsum hfinSub]
  -- SbMinus = ∑ᶠ n, G n
  rw [sbMinus_body_eq k r]
  -- ∑ᶠ over subtype = ∑ᶠ over cond, restricted to the fibre.
  rw [finsum_subtype_eq_finsum_cond (f := G) (fun n => rOfGap_minus k hk n = r)]
  symm
  rw [← finsum_mem_univ G]
  exact finsum_mem_inter_support_eq' G Set.univ {n | rOfGap_minus k hk n = r}
    (by
      intro x hx
      simp only [Set.mem_univ, Set.mem_setOf_eq, true_iff]
      by_contra hne
      rw [Function.mem_support] at hx
      apply hx
      simp only [hG]
      rw [if_neg]
      intro hc; exact hne ((boundary_iff_rOfGap_minus k hk r x).1 hc))

/-- **`r`-partition/Fubini reassembly (minus)** — assembles `stmt6_reassembly_minus` from the
minus kernel, mirroring `zNat_reassembly_plus`. -/
lemma zNat_reassembly_minus (k : ℕ) (hk : 2 ≤ k)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) (hSym : Fact3 Stil)
    (hQbin : Fact6) (hPD : Fact8 3 (3 * k - 1)) (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    HJO.zNat 3 (3 * k - 1)
      = ∑' r : {r : Fin k → ℕ // Antitone r}, outerFactorP k r.1 * SbMinus k r.1 := by
  classical
  -- Abbreviation for the ℤ-indexed summand.
  set T : ((finspan {3, 3 * k - 1}).gaps → ℤ) → ℤ⟦X⟧ := fun n =>
      (∏ i, HJO.multiplicand (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) n i)
        * X ^ ((HJO.Q' (finspan {3, 3 * k - 1}).gaps 3 (3 * k - 1) n).toNat) with hT
  -- Step 0: `zNat` unfolds to `∑' n, T n`.
  have hzNat : HJO.zNat 3 (3 * k - 1) = ∑' n : (finspan {3, 3 * k - 1}).gaps → ℤ, T n := by
    rfl
  rw [hzNat]
  have hsummℤ : Summable T := by rw [hT]; exact zNatTermM_summable k hk hPD
  -- Step 1: restrict the ℤ-indexed sum to the ℕ-cone via the injective cast (off-range vanishes).
  have hsupp : Function.support T ⊆ Set.range (natCastGapM k) := by
    intro n hn
    by_contra hnr
    apply hn
    show T n = 0
    rw [hT]
    exact zNatTermM_vanish_off_natRange k hk n hnr
  have hstep1 : ∑' n : (finspan {3, 3 * k - 1}).gaps → ℤ, T n
      = ∑' m : (finspan {3, 3 * k - 1}).gaps → ℕ, T (natCastGapM k m) := by
    rw [← (natCastGapM_injective k).tsum_eq (f := T) hsupp]
  rw [hstep1]
  -- Step 2: pointwise, `T (cast m) = outerFactorP k (rOfGap_minus m) * sbMinusBody`.
  have hstep2 : ∀ m : (finspan {3, 3 * k - 1}).gaps → ℕ,
      T (natCastGapM k m)
        = outerFactorP k (rOfGap_minus k hk m)
            * sbMinusBody k (rOfGap_minus k hk m) m := by
    intro m
    rw [hT]
    exact multiplicand_term_eq_minus k hk hQbin m
      (fun j => (boundary_iff_rOfGap_minus k hk (rOfGap_minus k hk m) m).2 rfl j)
  rw [tsum_congr hstep2]
  have hsummℕ : Summable (fun m : (finspan {3, 3 * k - 1}).gaps → ℕ =>
      outerFactorP k (rOfGap_minus k hk m)
        * sbMinusBody k (rOfGap_minus k hk m) m) := by
    have hcast : Summable (fun m : (finspan {3, 3 * k - 1}).gaps → ℕ => T (natCastGapM k m)) :=
      (Function.Injective.summable_iff (natCastGapM_injective k)
        (fun n hn => by rw [hT]; exact zNatTermM_vanish_off_natRange k hk n hn)).2 hsummℤ
    exact hcast.congr hstep2
  -- Step 3: reindex the ℕ-sum by the fibres of `rOfGap_minus` (sigma decomposition).
  set F : ((finspan {3, 3 * k - 1}).gaps → ℕ) → (Fin k → ℕ) := rOfGap_minus k hk with hF
  set g : ((finspan {3, 3 * k - 1}).gaps → ℕ) → ℤ⟦X⟧ := fun m =>
      outerFactorP k (rOfGap_minus k hk m)
        * sbMinusBody k (rOfGap_minus k hk m) m with hg
  rw [← (Equiv.sigmaFiberEquiv F).tsum_eq g]
  simp only [Equiv.sigmaFiberEquiv_apply]
  have hsummσ : Summable (fun p : Σ r : Fin k → ℕ, {m // F m = r} => g p.2.1) :=
    (Equiv.summable_iff (Equiv.sigmaFiberEquiv F)).2 hsummℕ
  rw [hsummσ.tsum_sigma]
  -- Now goal: `∑' r : Fin k → ℕ, (∑' m : {m // F m = r}, g m.1) = ∑' r:{//Antitone}, ...`.
  -- Step 5 (FIRST): restrict `∑' r : Fin k → ℕ` to `∑' r : {r // Antitone r}`.
  symm
  set h : (Fin k → ℕ) → ℤ⟦X⟧ := fun r => ∑' m : {m // F m = r}, g m.1 with hh
  have hsuppR : Function.support h
      ⊆ Set.range (Subtype.val : {r : Fin k → ℕ // Antitone r} → (Fin k → ℕ)) := by
    intro r hr
    simp only [hh, Function.mem_support] at hr
    have hant : Antitone r := by
      by_contra hrNA
      apply hr
      have hz0 : ∀ mm : {m // F m = r}, g mm.1 = 0 := by
        rintro ⟨m, hm⟩
        by_contra hne
        apply hrNA
        have hTne : T (natCastGapM k m) ≠ 0 := by
          have hgT : g m = T (natCastGapM k m) := by rw [hg, hstep2 m]
          rw [← hgT]; exact hne
        have hant2 : Antitone (rOfGap_minus k hk m) := by
          rw [hT] at hTne; exact rOfGap_minus_antitone_of_nonzero k hk m hTne
        have hmr : rOfGap_minus k hk m = r := hm
        rwa [hmr] at hant2
      rw [tsum_congr hz0, tsum_zero]
    exact ⟨⟨r, hant⟩, rfl⟩
  rw [← (Subtype.val_injective (p := (Antitone : (Fin k → ℕ) → Prop))).tsum_eq
    (f := h) hsuppR]
  -- Step 4 (over antitone r): identify the fibre sum with `SbMinus`.
  refine tsum_congr (fun rr => ?_)
  obtain ⟨r, hrant⟩ := rr
  simp only [hh]
  -- fibre sum: pull out `outerFactorP k r`, identify tsum of `sbMinusBody` with `SbMinus`.
  have hfibre : ∀ m : {m // F m = r},
      g m.1 = outerFactorP k r * sbMinusBody k r m.1 := by
    rintro ⟨m, hm⟩
    simp only [hg, hF] at hm ⊢
    rw [hm]
  rw [tsum_congr hfibre]
  -- reindex fibre subtype {m // F m = r} = {m // rOfGap_minus k hk m = r}
  rw [(fibre_summable_minus k hk r hrant).tsum_mul_left (outerFactorP k r),
    fibre_tsum_eq_SbMinus k hk r hrant]

/-- **Statement 6(minus) — Lemma 3.5, reassembly (eq:reassemble), `b=3k-1`.** Uses Facts
1,2,3,6,8,9. -/
theorem stmt6_reassembly_minus (k : ℕ) (hk : 2 ≤ k)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) (hSym : Fact3 Stil)
    (hQbin : Fact6) (hPD : Fact8 3 (3 * k - 1)) (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    HJO.zNat 3 (3 * k - 1)
      = ∑' r : {r : Fin k → ℕ // Antitone r},
          invOfUnit (qPochhammer qX qX (acc r.1 1)) 1
            * (∏ i ∈ Icc 1 (k - 1), qChoose qX (acc r.1 i) (acc r.1 (i + 1)))
            * SbMinus k r.1 := by
  rw [zNat_reassembly_minus Stil Tset invStat tabOf Ja Jz k hk hRC hInv hSym hQbin hPD hInvComp]
  refine tsum_congr (fun r => ?_)
  rw [outerFactorP, mul_assoc]



/-! ### Deliverable B — Corollary 1.2 parts (2), (3) (`cor:closed-form`). -/

/-- **Corollary 1.2(2)**, `b = 3k+1` (`k ≥ 1`). -/
theorem cor_closedForm_plus_from_fact9 (k : ℕ) (hk : 1 ≤ k)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) (hSym : Fact3 Stil)
    (hRecip : Fact5) (hQbin : Fact6) (hPD : Fact8 3 (3 * k + 1)) (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    HJO.zNat 3 (3 * k + 1) = fermPlus k := by
  -- STRATEGY (Cor 1.2(2) = Lemma 3.5 reassembly + Thm 3.1 fixed-boundary + Fact6 telescope):
  --   1. `stmt6_reassembly` rewrites `zNat 3 (3k+1)` as the reassembled `r`-sum
  --      `∑' r, (1/(q)_{r₁})·(∏[rᵢ;rᵢ₊₁])·SbPlus k r` (outer factor kept, Remark 3.6).
  --   2. For each fixed `r`, `SbPlus k r` (the unexpanded fixed-boundary sum) equals — via
  --      the reindexing `stmt_reindexEq_plus` (Q collapses to Σrⱼ²+E⁺) followed by the master
  --      transformation `stmt4_master`/`stmt5_fixedBoundary_plus` — the `m`-fermionic inner
  --      form `∑_m q^{Σ(rᵢ²−rᵢmᵢ+mᵢ²)} [2rₖ;mₖ] ∏[rᵢ−rᵢ₊₁+mᵢ₊₁;mᵢ]`.
  --   3. Substituting (2) into (1), the outer factor `(1/(q)_{r₁})(∏[rᵢ;rᵢ₊₁])` combines with
  --      the inner `m`-sum; the Fact6 telescoping chain (`hQbin.2.2.2.2`) reorganizes the
  --      product of Gaussians so that the whole `∑' r ∑_m` collapses to exactly `fermPlus k`
  --      (the `∑' d : DomP k` in the definition of `fermPlus`, index `d = (r,m)`).
  -- The reassembly (step 1) is `stmt6_reassembly`; the inner rewrite + telescope (steps 2–3)
  -- is the remaining content — deferred to `sorry` (a genuine sub-lemma: "fixed-boundary
  -- expansion + reindex of the DomP sum").
  -- SANITY CHECK PASSED (this is Corollary 1.2(2) of the paper; the three ingredients exist as
  -- separate theorems in this file and the DomP re-indexing is a bijection r,m ↔ d).
  rw [stmt6_reassembly Stil Tset invStat tabOf Ja Jz k hk hRC hInv hSym hQbin hPD hInvComp,
      fermPlus_eq_tsum_perR k hk hPD]
  -- Both sides are `∑' r`; the LHS outer factor is `outerP k ↑r` by def, so match per r.
  refine tsum_congr (fun r => ?_)
  rw [cor_perR_plus Stil Tset invStat tabOf Ja Jz k hk (r : Fin k → ℕ) r.2
        hRC hInv hSym hRecip hQbin hPD hInvComp]
  rfl

/-- **Corollary 1.2(3)**, `b = 3k-1` (`k ≥ 2`); terminal `rₖ²` retained. -/
theorem cor_closedForm_minus_from_fact9 (k : ℕ) (hk : 2 ≤ k)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) (hSym : Fact3 Stil)
    (hRecip : Fact5) (hQbin : Fact6) (hPD : Fact8 3 (3 * k - 1)) (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    HJO.zNat 3 (3 * k - 1) = fermMinus k := by
  -- STRATEGY (Cor 1.2(3), minus case; mirror of the plus case, terminal `rₖ²` retained,
  -- Remark 3.2):
  --   1. `stmt6_reassembly_minus` rewrites `zNat 3 (3k-1)` as
  --      `∑' r, (1/(q)_{r₁})·(∏[rᵢ;rᵢ₊₁])·SbMinus k r`.
  --   2. For fixed `r`, `SbMinus k r` equals — via `stmt_reindexEq_minus` (Q = rₖ²+Σ_{i<k}rᵢ²+E⁻)
  --      and `stmt5_fixedBoundary_minus` (master, minus) — the minus `m`-fermionic inner form
  --      `∑_m q^{rₖ²+Σ_{i<k}(rᵢ²−rᵢmᵢ+mᵢ²)} [r_{k-1}+rₖ;m_{k-1}] ∏[…;mᵢ]` (only m₁…m_{k-1}).
  --   3. Substituting and applying the Fact6 telescope (`hQbin.2.2.2.2`) collapses `∑'r ∑_m`
  --      into `fermMinus k` (the `∑' d : DomM k`, index `d = (r,m)` with the length-(k-1) m-tuple).
  -- SANITY CHECK PASSED (Corollary 1.2(3); terminal `rₖ²` kept in both the exponent here and in
  -- `fermMinus`, consistent with Remark 3.2's fragility warning).
  rw [stmt6_reassembly_minus Stil Tset invStat tabOf Ja Jz k hk hRC hInv hSym hQbin hPD hInvComp,
      fermMinus_eq_tsum_perR k hk hPD]
  -- Both sides are `∑' r`; the LHS outer factor is `outerM k ↑r = outerP k ↑r` by def.
  refine tsum_congr (fun r => ?_)
  rw [cor_perR_minus Stil Tset invStat tabOf Ja Jz k hk (r : Fin k → ℕ) r.2
        hRC hInv hSym hRecip hQbin hPD hInvComp]
  rfl

/-! ### Deliverable A — Theorem 1.1 (`thm:main`): `Z_{3,b} = P_{3,b}`. -/

theorem thm_main_from_fact9 (b : ℕ) (hb : 3 < b) (hcop : Nat.Coprime 3 b)
    (hRC : Fact1 Stil) (hInv : Fact2 Stil Tset invStat) (hSym : Fact3 Stil)
    (hWarnaar : Fact4) (hRecip : Fact5) (hQbin : Fact6) (hSylv : Fact7 3 b) (hPD : Fact8 3 b)
    (hInvComp : Fact9 Stil invStat tabOf Ja Jz) :
    HJO.Conjecture' 3 b := by
  -- `HJO.Conjecture' 3 b` unfolds to `HJO.zNat 3 b = HJO.charge 3 b`.
  -- STRATEGY: `Nat.Coprime 3 b` forces `b % 3 ∈ {1,2}` (3 is prime, 3 ∤ b), so with `3 < b`
  -- either `b = 3*k+1` (k ≥ 1) or `b = 3*k-1` (k ≥ 2). In each case chain the matching
  -- corollary (`cor_closedForm_±`: `zNat = ferm`) with the residue statement
  -- (`stmt7_residue_±`: `ferm = charge`) to conclude `zNat = charge`.
  show HJO.zNat 3 b = HJO.charge 3 b
  -- SANITY CHECK PASSED (definitional unfolding of Conjecture' matches; case-split arithmetic:
  -- coprime 3 b with 3∤b gives b%3 = 1 or 2).
  -- `Nat.Coprime 3 b` gives `¬ 3 ∣ b` hence `b % 3 ≠ 0`, so `b % 3 = 1 ∨ b % 3 = 2`.
  have h3 : ¬ (3 ∣ b) := by
    -- SANITY CHECK PASSED. HINT: `fun hdvd => by have := Nat.Coprime.eq_one_of_dvd hcop.symm ...`
    -- or: `Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)` turns `hcop` into `¬3∣b`.
    intro hdvd
    have hb1 : (3 : ℕ) ∣ Nat.gcd 3 b := Nat.dvd_gcd (dvd_refl 3) hdvd
    rw [hcop] at hb1
    omega
  have hmod : b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases hmod with hm | hm
  · -- b = 3k+1 with k = b/3 ≥ 1 (since b > 3).
    obtain ⟨k, hk1, hbk⟩ : ∃ k, 1 ≤ k ∧ b = 3 * k + 1 := ⟨b / 3, by omega, by omega⟩
    subst hbk
    calc HJO.zNat 3 (3 * k + 1)
        = fermPlus k := cor_closedForm_plus_from_fact9 Stil Tset invStat tabOf Ja Jz k hk1 hRC hInv hSym hRecip hQbin hPD hInvComp
      _ = HJO.charge 3 (3 * k + 1) := stmt7_residue_plus k hk1 hWarnaar
  · -- b = 3k-1 with k = (b+1)/3 ≥ 2 (since b > 3 and b ≡ 2 mod 3 ⇒ b ≥ 5).
    obtain ⟨k, hk2, hbk⟩ : ∃ k, 2 ≤ k ∧ b = 3 * k - 1 := ⟨(b + 1) / 3, by omega, by omega⟩
    subst hbk
    calc HJO.zNat 3 (3 * k - 1)
        = fermMinus k := cor_closedForm_minus_from_fact9 Stil Tset invStat tabOf Ja Jz k hk2 hRC hInv hSym hRecip hQbin hPD hInvComp
      _ = HJO.charge 3 (3 * k - 1) := stmt7_residue_minus k hk2 hWarnaar



end MasterBuild
end Targets
end ProblemHJOa3

namespace ProblemHJOa3

open scoped QTheory PowerSeries.DiscreteTopology Classical
open HJO PowerSeries NumericalSemigroup Finset
open LaurentPolynomial

/-! ## Section 3.4 interface: transport bridges (sketch).

`derive_section34_interface` proves `Fact9` (stated in the `Supernomial` section's
representation: `ProblemHJOa3.azFinset`, `ProblemHJOa3.Eplus/Eminus`,
`ProblemHJOa3.Brs`, and RHS `Stil (T (-1)) [M, ...] (List.ofFn (r+s))`).  The
matching capstones `SupernomialInv.left_supernomial_plus/minus` prove the SAME
identity in the `SupernomialInv` representation (`SupernomialInv.azFinset`,
`SupernomialInv.Eplus/Eminus`, `SupernomialInv.Bweight`, RHS
`invSub (Stil q [M, muSize-M] (muPrime r s))`).  The bridges below equate the two
representations term by term. -/

section Section34Bridges

open SupernomialInv (q invSub)

/-- `toLaurent` of the integer-coefficient Gaussian binomial is the Laurent
Gaussian binomial evaluated at `q = T 1`. -/
theorem toLaurent_qChoose (N k : ℕ) :
    Polynomial.toLaurent (qChoose (Polynomial.X : Polynomial ℤ) N k)
      = qChoose (SupernomialInv.q) N k := by
  induction N generalizing k with
  | zero =>
    rcases k with _ | k
    · simp
    · simp
  | succ N ih =>
    rcases k with _ | k
    · simp
    · rw [qChoose_succ_succ, qChoose_succ_succ]
      rw [map_add, map_mul, map_pow, ih k, ih (k + 1), Polynomial.toLaurent_X]
      rfl

/-- The two inversion statistics agree: the subset inversion count of `S` equals
the word inversion count of its indicator word. -/
theorem invWord_ofFn_indicator {N : ℕ} (S : Finset (Fin N)) :
    LeafABuild.invWord S
      = SupernomialInv.invWord (List.ofFn (fun i : Fin N => decide (i ∈ S))) := by
  classical
  unfold LeafABuild.invWord SupernomialInv.invWord
  rw [List.length_ofFn]
  set w := List.ofFn (fun i : Fin N => decide (i ∈ S)) with hw
  have hget : ∀ i : Fin N, w[(i:ℕ)]! = decide (i ∈ S) := by
    intro i
    rw [hw, getElem!_pos _ (i:ℕ) (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
  set g : ℕ → ℕ → ℕ := fun a b => if a < b ∧ w[a]! = true ∧ w[b]! = false then 1 else 0 with hg
  -- RHS rewritten with g
  have hRHSg : (∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ioo i N,
        (if w[i]! = true ∧ w[j]! = false then 1 else 0))
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ioo i N, g i j := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_Ioo] at hj
    rw [hg]
    simp only [hj.1, true_and]
  rw [hRHSg]
  -- inner Ioo -> range via sum_subset
  have hInner : ∀ i, (∑ j ∈ Finset.Ioo i N, g i j) = ∑ j ∈ Finset.range N, g i j := by
    intro i
    apply Finset.sum_subset
    · intro x hx; simp only [Finset.mem_Ioo] at hx; simp only [Finset.mem_range]; exact hx.2
    · intro x hxr hxn
      simp only [Finset.mem_range] at hxr
      simp only [Finset.mem_Ioo, not_and, not_lt] at hxn
      rw [hg]
      have : ¬ (i < x) := by
        by_contra hlt; exact absurd (hxn hlt) (by omega)
      simp [this]
  simp_rw [hInner]
  -- Now RHS = ∑ i∈range N ∑ j∈range N g i j
  -- convert to Fin N
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range N, g i j) N]
  -- LHS
  rw [Finset.card_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Fin.sum_univ_eq_sum_range (fun j => g (x:ℕ) j) N]
  apply Finset.sum_congr rfl
  intro y _
  simp only [hg]
  rw [hget x, hget y]
  simp only [decide_eq_true_eq, Fin.lt_def]
  by_cases hxy : (x:ℕ) < (y:ℕ)
  · by_cases hxs : x ∈ S <;> by_cases hys : y ∈ S <;>
      simp [hxy, hxs, hys]
  · simp [hxy]


/-- **Bridge 1 (binary-word Gaussian identity holds unconditionally).**
`SupernomialInv.BinaryWordGauss` is derivable, not an external assumption: the
Laurent-coefficient identity `qChoose_eq_sum_invWord_Z N k` expands `[N;k]_q` as a
sum of `q^{inv(S)}` over `k`-subsets `S ⊆ Fin N`, and reindexing subsets `S` by
their indicator words `v i = decide (i ∈ S)` matches both the cardinality
constraint (`|S| = k ↔ #{i : v i = true} = k`) and the inversion statistic
(`LeafABuild.invWord S = invWord (List.ofFn v)`; both count pairs `i < j` with a
`1` at `i` and a `0` at `j`). -/
theorem binaryWordGauss_holds : SupernomialInv.BinaryWordGauss := by
  classical
  intro N k
  have hgauss : SupernomialInv.gauss N k
      = ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin N) => S.card = k)),
          (SupernomialInv.q) ^ LeafABuild.invWord S := by
    unfold SupernomialInv.gauss
    rw [← toLaurent_qChoose N k, LeafABuild.qChoose_eq_sum_invWord_Z N k, map_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [map_pow, Polynomial.toLaurent_X]
    rfl
  rw [hgauss]
  refine (Finset.sum_nbij'
    (i := fun S : Finset (Fin N) => (fun i : Fin N => decide (i ∈ S)))
    (j := fun v : Fin N → Bool => Finset.univ.filter (fun i => v i = true))
    ?_ ?_ ?_ ?_ ?_).symm.symm
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    rw [← hS]
    congr 1
    ext i
    simp [Finset.mem_filter]
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hv
  · intro S _
    ext i
    simp [Finset.mem_filter]
  · intro v _
    funext i
    simp [Finset.mem_filter]
  · intro S _
    rw [invWord_ofFn_indicator S]

/-- `SupernomialInv.shiftNext t j = acc t (j+2)`. -/
theorem shiftNext_eq_acc {ℓ : ℕ} (t : Fin ℓ → ℕ) (j : Fin ℓ) :
    SupernomialInv.shiftNext t j = acc t ((j : ℕ) + 2) := by
  have hj := j.2
  unfold SupernomialInv.shiftNext acc
  by_cases h : (j : ℕ) + 1 = ℓ
  · rw [dif_pos h, dif_neg (by omega)]
  · rw [dif_neg h, dif_pos (by omega)]
    congr 1

/-- `SupernomialInv.shiftPrev bd t j = aacc bd t j`. -/
theorem shiftPrev_eq_aacc {ℓ : ℕ} (bd : ℕ) (t : Fin ℓ → ℕ) (j : Fin ℓ) :
    SupernomialInv.shiftPrev bd t j = aacc bd t (j : ℕ) := by
  have hj := j.2
  unfold SupernomialInv.shiftPrev aacc acc
  by_cases h : (j : ℕ) = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, dif_pos (by omega)]

/-- `acc t (j+1) = t j` for `j : Fin ℓ`. -/
theorem acc_succ_fin {ℓ : ℕ} (t : Fin ℓ → ℕ) (j : Fin ℓ) :
    acc t ((j : ℕ) + 1) = t j := by
  have hj := j.2
  rw [acc_val t ((j : ℕ) + 1) (by omega) (by omega)]
  congr 1

/-- The two domain predicates agree: `ProblemHJOa3.domAZ` (Antitone + boundary, `Icc`/`acc`)
equals `SupernomialInv.azDomain` (adjacent shift inequalities). -/
theorem domAZ_iff_azDomain {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ) (a z : Fin ℓ → ℕ) :
    domAZ r s a z ↔ SupernomialInv.azDomain r s a z := by
  unfold domAZ SupernomialInv.azDomain
  constructor
  · rintro ⟨hAa, ha1, hAz, hzr⟩
    refine ⟨?_, ?_, ?_⟩
    · -- ∀ j, a j ≤ shiftPrev s a j
      intro j
      rw [shiftPrev_eq_aacc s a j]
      unfold aacc
      by_cases hj : (j : ℕ) = 0
      · rw [if_pos hj]
        -- a j ≤ s; j = 0 so a 0 ≤ acc a 1 = a 0 ≤ s
        have : acc a 1 = a j := by
          rw [show (1 : ℕ) = (j : ℕ) + 1 by omega, acc_succ_fin a j]
        omega
      · rw [if_neg hj]
        -- a j ≤ acc a j = a (j-1); antitone
        have hval : acc a (j : ℕ) = a ⟨(j : ℕ) - 1, by have := j.2; omega⟩ := by
          rw [acc_val a (j : ℕ) (by omega) (by have := j.2; omega)]
        rw [hval]
        apply hAa
        apply Fin.mk_le_mk.mpr
        omega
    · -- ∀ j, z j ≤ r j
      intro j
      have := hzr ((j : ℕ) + 1) (Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩)
      rw [acc_succ_fin z j, acc_succ_fin r j] at this
      exact this
    · -- ∀ j, shiftNext z j ≤ z j
      intro j
      rw [shiftNext_eq_acc z j]
      unfold acc
      by_cases hj : (1 : ℕ) ≤ (j : ℕ) + 2 ∧ (j : ℕ) + 2 ≤ ℓ
      · rw [dif_pos hj]
        -- z ⟨j+1⟩ ≤ z j; antitone
        apply hAz
        apply Fin.mk_le_mk.mpr
        omega
      · rw [dif_neg hj]
        exact Nat.zero_le _
  · rintro ⟨haShift, hzr, hzShift⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Antitone a
      intro i j hij
      -- reduce to adjacent steps a (k+1) ≤ a k from haShift
      have hstep : ∀ (k : ℕ) (hk : k + 1 < ℓ), a ⟨k+1, hk⟩ ≤ a ⟨k, by omega⟩ := by
        intro k hk
        have h := haShift ⟨k+1, hk⟩
        rw [shiftPrev_eq_aacc s a ⟨k+1, hk⟩] at h
        unfold aacc at h
        rw [if_neg (by simp)] at h
        have hval : acc a ((⟨k+1, hk⟩ : Fin ℓ) : ℕ) = a ⟨k, by omega⟩ := by
          simp only [Fin.val_mk]
          rw [acc_val a (k+1) (by omega) (by omega)]
          congr 1
        rw [hval] at h
        exact h
      -- now prove monotone-decreasing by induction on the gap
      have hgen : ∀ (d : ℕ) (k : ℕ) (hk : k + d < ℓ),
          a ⟨k+d, hk⟩ ≤ a ⟨k, by omega⟩ := by
        intro d
        induction d with
        | zero => intro k hk; rfl
        | succ n ih =>
            intro k hk
            have h1 : a ⟨k+(n+1), hk⟩ ≤ a ⟨k+n, by omega⟩ := by
              have := hstep (k+n) (by omega)
              have he : (⟨(k+n)+1, by omega⟩ : Fin ℓ) = ⟨k+(n+1), hk⟩ := by
                apply Fin.ext; simp; omega
              rw [he] at this
              exact this
            have h2 : a ⟨k+n, by omega⟩ ≤ a ⟨k, by omega⟩ := ih k (by omega)
            exact le_trans h1 h2
      have hij' : (i : ℕ) ≤ (j : ℕ) := hij
      have hkey := hgen ((j:ℕ) - (i:ℕ)) i (by have := j.2; omega)
      have heq : (⟨(i:ℕ)+((j:ℕ)-(i:ℕ)), by have := j.2; omega⟩ : Fin ℓ) = j := by
        apply Fin.ext; simp; omega
      have heqi : (⟨(i:ℕ), by have := i.2; omega⟩ : Fin ℓ) = i := by
        apply Fin.ext; simp
      rw [heq, heqi] at hkey
      exact hkey
    · -- acc a 1 ≤ s
      by_cases hℓ0 : ℓ = 0
      · subst hℓ0; unfold acc; simp
      · have h := haShift ⟨0, by omega⟩
        rw [shiftPrev_eq_aacc s a ⟨0, by omega⟩] at h
        unfold aacc at h
        rw [if_pos (by simp)] at h
        have : acc a 1 = a ⟨0, by omega⟩ := by
          rw [show (1:ℕ) = ((⟨0, by omega⟩ : Fin ℓ):ℕ)+1 by simp, acc_succ_fin a ⟨0, by omega⟩]
        rw [this]
        exact h
    · -- Antitone z
      intro i j hij
      have hstep : ∀ (k : ℕ) (hk : k + 1 < ℓ), z ⟨k+1, hk⟩ ≤ z ⟨k, by omega⟩ := by
        intro k hk
        have h := hzShift ⟨k, by omega⟩
        rw [shiftNext_eq_acc z ⟨k, by omega⟩] at h
        have hval : acc z ((⟨k, by omega⟩ : Fin ℓ).val+2) = z ⟨k+1, hk⟩ := by
          simp only [Fin.val_mk]
          rw [acc_val z (k+2) (by omega) (by omega)]
          congr 1
        rw [hval] at h
        exact h
      have hgen : ∀ (d : ℕ) (k : ℕ) (hk : k + d < ℓ),
          z ⟨k+d, hk⟩ ≤ z ⟨k, by omega⟩ := by
        intro d
        induction d with
        | zero => intro k hk; rfl
        | succ n ih =>
            intro k hk
            have h1 : z ⟨k+(n+1), hk⟩ ≤ z ⟨k+n, by omega⟩ := by
              have := hstep (k+n) (by omega)
              have he : (⟨(k+n)+1, by omega⟩ : Fin ℓ) = ⟨k+(n+1), hk⟩ := by
                apply Fin.ext; simp; omega
              rw [he] at this
              exact this
            have h2 : z ⟨k+n, by omega⟩ ≤ z ⟨k, by omega⟩ := ih k (by omega)
            exact le_trans h1 h2
      have hij' : (i : ℕ) ≤ (j : ℕ) := hij
      have hkey := hgen ((j:ℕ) - (i:ℕ)) i (by have := j.2; omega)
      have heq : (⟨(i:ℕ)+((j:ℕ)-(i:ℕ)), by have := j.2; omega⟩ : Fin ℓ) = j := by
        apply Fin.ext; simp; omega
      have heqi : (⟨(i:ℕ), by have := i.2; omega⟩ : Fin ℓ) = i := by
        apply Fin.ext; simp
      rw [heq, heqi] at hkey
      exact hkey
    · -- ∀ i ∈ Icc 1 ℓ, acc z i ≤ acc r i
      intro i hi
      rw [Finset.mem_Icc] at hi
      obtain ⟨hi1, hi2⟩ := hi
      have hval_z : acc z i = z ⟨i-1, by omega⟩ := by
        rw [acc_val z i hi1 hi2]
      have hval_r : acc r i = r ⟨i-1, by omega⟩ := by
        rw [acc_val r i hi1 hi2]
      rw [hval_z, hval_r]
      exact hzr ⟨i-1, by omega⟩

/-- **Bridge 2 (index-set identification).**  The two `azFinset` definitions agree:
`ProblemHJOa3.azFinset` (antidiagonalTuple image cut to `domAZ`) and
`SupernomialInv.azFinset` (product of ranges cut to `azDomain` and sum `= M`) both
enumerate the pairs `(a,z)` with `s = a0 ≥ a1 ≥ ... ≥ a_ℓ ≥ 0`, `ri ≥ zi ≥ z_{i+1}`,
and `∑i (ai + zi) = M`. -/
theorem azFinset_eq {ℓ : ℕ} (r : Fin ℓ → ℕ) (s M : ℕ) :
    azFinset r s M = SupernomialInv.azFinset r s M := by
  classical
  ext az
  obtain ⟨a, z⟩ := az
  rw [mem_azFinset]
  unfold SupernomialInv.azFinset
  rw [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset]
  simp only [Finset.mem_range]
  rw [domAZ_iff_azDomain]
  constructor
  · rintro ⟨hdom, hsum⟩
    -- range bounds are redundant under azDomain
    have hbr : ∀ i, z i ≤ r i := hdom.2.1
    have hbs : ∀ i, a i ≤ s := by
      have hdomAZ : domAZ r s a z := (domAZ_iff_azDomain r s a z).mpr hdom
      obtain ⟨haA, ha1, hzA, hzr⟩ := hdomAZ
      intro i
      by_cases hℓ : 1 ≤ ℓ
      · have h0 : a i ≤ a ⟨0, by omega⟩ := haA (by
          show (⟨0, by omega⟩ : Fin ℓ) ≤ i
          exact Fin.mk_le_of_le_val (Nat.zero_le _))
        have hz : a ⟨0, by omega⟩ = acc a 1 := by
          rw [acc_val a 1 (le_refl 1) hℓ]
        rw [hz] at h0
        exact le_trans h0 ha1
      · exact absurd i.2 (by omega)
    refine ⟨⟨fun i => Nat.lt_succ_of_le (hbs i), fun i => Nat.lt_succ_of_le (hbr i)⟩,
      hdom, ?_⟩
    rw [← hsum, Finset.sum_add_distrib]
  · rintro ⟨_, hdom, hsum⟩
    refine ⟨hdom, ?_⟩
    rw [← hsum, Finset.sum_add_distrib]

theorem Eplus_bridge {ℓ : ℕ} (r a z : Fin ℓ → ℕ) :
    Eplus r a z = SupernomialInv.Eplus r a z := by
  unfold Eplus SupernomialInv.Eplus
  rw [← sum_fin_eq_Icc (fun i => ((acc a i : ℤ) ^ 2 + (acc z i : ℤ) ^ 2
      + (acc a i : ℤ) * (acc z i : ℤ) + (acc a (i + 1) : ℤ) * (acc z i : ℤ)
      - (acc r i : ℤ) * ((acc a (i + 1) : ℤ) + (acc z i : ℤ))))]
  apply Finset.sum_congr rfl
  intro j _
  rw [acc_succ_fin a j, acc_succ_fin z j, acc_succ_fin r j,
      show (j : ℕ) + 1 + 1 = (j : ℕ) + 2 by ring, ← shiftNext_eq_acc a j]

/-- **Bridge 4 (minus exponent).**  As Bridge 3 for `E⁻` (uses the left boundary
`a0 = s`, i.e. `aacc s a (i-1) = shiftPrev s a j`). -/
theorem Eminus_bridge {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ) (a z : Fin ℓ → ℕ) :
    Eminus r s a z = SupernomialInv.Eminus r s a z := by
  unfold Eminus SupernomialInv.Eminus
  rw [← sum_fin_eq_Icc (fun i => ((acc a i : ℤ) ^ 2 + (acc z i : ℤ) ^ 2
      + (acc a i : ℤ) * (acc z i : ℤ) + (acc z i : ℤ) * (aacc s a (i - 1) : ℤ)
      - (acc r i : ℤ) * ((acc a i : ℤ) + (acc z i : ℤ))))]
  apply Finset.sum_congr rfl
  intro j _
  rw [acc_succ_fin a j, acc_succ_fin z j, acc_succ_fin r j,
      show (j : ℕ) + 1 - 1 = (j : ℕ) by omega, ← shiftPrev_eq_aacc s a j]

/-- **Bridge 5 (Gaussian weight).**  `Brs` (`Icc 1 ℓ`/`acc`, over `qL = T 1`) equals
`Bweight` (`Fin ℓ`/`shift`, over `gauss = qChoose (T 1)`), factor by factor. -/
theorem Brs_bridge {ℓ : ℕ} (r : Fin ℓ → ℕ) (s : ℕ) (a z : Fin ℓ → ℕ) :
    Brs r s a z = SupernomialInv.Bweight r s a z := by
  unfold Brs SupernomialInv.Bweight SupernomialInv.gauss
  rw [← prod_fin_shift_eq_Icc ℓ (fun i => qChoose qL (aacc s a (i - 1)) (acc a i)
      * qChoose qL (acc r i - acc z (i + 1)) (acc z i - acc z (i + 1)))]
  apply Finset.prod_congr rfl
  intro j _
  rw [show SupernomialInv.q = qL from rfl,
      acc_succ_fin a j, acc_succ_fin r j, acc_succ_fin z j,
      show (j : ℕ) + 1 - 1 = (j : ℕ) by omega, ← shiftPrev_eq_aacc s a j,
      show (j : ℕ) + 1 + 1 = (j : ℕ) + 2 by ring, ← shiftNext_eq_acc z j]

/-- **Bridge 6 (right-hand side reconciliation).**  For every `M`, the Fact9 target
`Stil (T (-1)) [M, ∑(ri+s) - M] (List.ofFn (r+s))` equals the capstone output
`invSub (Stil q [M, muSize - M] (muPrime r s))`.  This uses Fact 2's inversion
expansion (`fact2 : Stil q' [A,B] μ = ∑_{Tset} q'^invStat` for any variable `q'`
when `A+B = |μ|`) at BOTH `q' = q` and `q' = T (-1)`: `invSub (∑ q^inv) = ∑
(T(-1))^inv = Stil (T(-1)) ...`. -/
theorem invSub_Stil_bridge (Stil : LaurentPolynomial ℤ → List ℤ → List ℕ → LaurentPolynomial ℤ)
    {Tab : Type} (Tset : List ℤ → List ℕ → Finset Tab) (invStat : Tab → ℕ)
    (hfact2 : ∀ (q' : LaurentPolynomial ℤ) (lam : List ℤ) (mu : List ℕ),
        lam.sum = (mu.sum : ℤ) → Stil q' lam mu = ∑ Tb ∈ Tset lam mu, q' ^ invStat Tb)
    {ℓ : ℕ} (r : Fin ℓ → ℕ) (s M : ℕ) :
    Stil (T (-1)) [(M : ℤ), (∑ i, ((r i + s : ℕ) : ℤ)) - (M : ℤ)]
        (List.ofFn fun i => r i + s)
      = invSub (Stil q [(M : ℤ), (SupernomialInv.muSize r s : ℤ) - M]
          (SupernomialInv.muPrime r s)) := by
  -- STRATEGY:
  --   0. Normalize the boundary data: `SupernomialInv.muPrime r s = List.ofFn (fun i => r i + s)`
  --      (both are `(finRange ℓ).map (fun i => r i + s)`; `List.ofFn f = (List.finRange _).map f`),
  --      and `(SupernomialInv.muSize r s : ℤ) = ∑ i, ((r i + s : ℕ) : ℤ)` (`muSize = ∑ (r+s)`,
  --      push_cast). After rewriting, both sides use the SAME `lam = [M, |μ|-M]` and
  --      `mu = List.ofFn (r+s)`.
  --   1. The sum condition `lam.sum = (mu.sum : ℤ)`: `[M, |μ|-M].sum = |μ|` and
  --      `(List.ofFn (r+s)).sum = ∑ (r+s) = |μ|`; prove `hsum` once by `simp`/`push_cast`.
  --   2. `hfact2 q lam mu hsum : Stil q lam mu = ∑_{Tset lam mu} q^invStat`, so
  --      `invSub (Stil q lam mu) = ∑_{Tset} invSub (q^invStat) = ∑_{Tset} (T(-1))^invStat`
  --      using `map_sum`, `map_pow`, `invSub_q` (`invSub q = T(-1)`).
  --   3. `hfact2 (T(-1)) lam mu hsum : Stil (T(-1)) lam mu = ∑_{Tset} (T(-1))^invStat`.
  --      Chain (2) and (3): both equal `∑_{Tset} (T(-1))^invStat`. Done.
  -- SANITY CHECK PASSED: Stil is opaque but pinned by Fact2; the two expansions coincide because
  -- `invSub` is a ring hom sending the variable `q` to `T(-1)`, and Fact2 expands `Stil` at ANY
  -- variable value as the same inv-generating polynomial over the fixed tableau set `Tset`.
  -- Step 0: normalize muPrime and muSize on the RHS to match the LHS.
  have hmu : SupernomialInv.muPrime r s = List.ofFn (fun i => r i + s) := by
    unfold SupernomialInv.muPrime
    rw [List.ofFn_eq_map]
  have hsize : (SupernomialInv.muSize r s : ℤ) = ∑ i, ((r i + s : ℕ) : ℤ) := by
    unfold SupernomialInv.muSize
    push_cast
    rfl
  rw [hmu, hsize]
  -- Now both sides use lam = [M, (∑ i, (r i + s)) - M] and mu = List.ofFn (fun i => r i + s).
  set lam : List ℤ := [(M : ℤ), (∑ i, ((r i + s : ℕ) : ℤ)) - (M : ℤ)] with hlam
  set mu : List ℕ := List.ofFn (fun i => r i + s) with hmudef
  have hsum : lam.sum = (mu.sum : ℤ) := by
    rw [hlam, hmudef]
    simp only [List.sum_cons, List.sum_nil, List.sum_ofFn]
    push_cast
    ring
  rw [hfact2 (T (-1)) lam mu hsum, hfact2 q lam mu hsum, map_sum]
  refine Finset.sum_congr rfl (fun Tb _ => ?_)
  rw [map_pow, SupernomialInv.invSub_q]

end Section34Bridges

section FinalTargets

variable {Tab : Type}
  (Stil : LaurentPolynomial ℤ → List ℤ → List ℕ → LaurentPolynomial ℤ)
  (Tset : List ℤ → List ℕ → Finset Tab)
  (invStat : Tab → ℕ)
  (tabOf : (ℓ : ℕ) → (Fin ℓ → ℕ) → (Fin ℓ → ℕ) → (Fin ℓ → ℕ) → ℕ → Bool → Tab)
  (Ja Jz : (ℓ : ℕ) → (Fin ℓ → ℕ) → (Fin ℓ → ℕ) → (Fin ℓ → ℕ) → ℕ → ℤ)

/-- Fact 2 in the two equivalent interfaces needed by the inherited spine and

the concrete Section 3.4 proof. Both conjuncts are specializations of the
single multitableau expansion/permutation-invariance fact. -/
def Fact2Bundle : Prop :=
  Fact2 Stil Tset invStat ∧
  (∀ (ℓ : ℕ) (r : Fin ℓ → ℕ) (s M : ℕ),
      Stil SupernomialInv.q [(M : ℤ),
          (SupernomialInv.muSize r s : ℤ) - M]
          (SupernomialInv.muPrime r s)
        = ∑ T ∈ SupernomialInv.TsetMinus r s M,
            SupernomialInv.q ^ SupernomialInv.invMT T) ∧
  (∀ (ℓ : ℕ) (r : Fin ℓ → ℕ) (s M : ℕ),
      ∑ T ∈ SupernomialInv.TsetMinus r s M,
          SupernomialInv.q ^ SupernomialInv.invMT T
        = ∑ T ∈ SupernomialInv.TsetPlus r s M,
            SupernomialInv.q ^ SupernomialInv.invMT T)

-- These objects occur intentionally in the Section 3.4 interface even though
-- its current definition retains them through `let` bindings. Keep them as
-- explicit parameters of the adapter and public targets.
include tabOf Ja Jz

/-- Sole adapter goal. The binary-word, inversion-decomposition, fiber, and
left-supernomial theorems are proved above. Transport between their equivalent
representations: Boolean words/subsets, polynomial/Laurent Gaussian terms,
Bweight/Brs, the two azFinsets, muPrime/List.ofFn, and inverse substitution. -/
theorem derive_section34_interface
    (h2 : Fact2Bundle Stil Tset invStat)
    (h3 : Fact3 Stil) (h6 : Fact6) :
    Fact9 Stil invStat tabOf Ja Jz := by
  -- ASSEMBLY of the Section-3.4 interface from the six transport bridges above and
  -- the two `SupernomialInv.left_supernomial_plus/minus` capstones (proved earlier).
  -- `Fact9` unfolds (after its `let _keep…` binders) to the conjunction PLUS ∧ MINUS.
  -- For each conjunct we: (1) intro the universals; (2) convert `Antitone r` to the
  -- pairwise form `hr'` the capstones want; (3) rewrite the index finset with
  -- `azFinset_eq` and the summand with `Eplus_bridge`/`Eminus_bridge` and `Brs_bridge`
  -- (via `Finset.sum_congr`) so the LHS is literally the capstone's LHS; (4) apply the
  -- capstone, feeding `binaryWordGauss_holds`, `h2.2.1`, `h2.2.2`, `h3.2`; (5) rewrite
  -- the capstone's RHS `invSub (Stil q …)` back to the Fact9 RHS `Stil (T (-1)) …`
  -- with `invSub_Stil_bridge` (using Fact2's expansion `h2.1.1`).
  refine ⟨?_, ?_⟩
  · -- PLUS branch
    intro ℓ hℓ r hr s M
    -- convert Antitone to pairwise
    have hr' : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i := fun i j hij => hr hij
    -- STEP (3): reindex the finset and rewrite the summand into SupernomialInv form
    have hLHS :
        (∑ az ∈ azFinset r s M, T (Eplus r az.1 az.2) * Brs r s az.1 az.2)
          = ∑ p ∈ SupernomialInv.azFinset r s M,
              LaurentPolynomial.T (SupernomialInv.Eplus r p.1 p.2)
                * SupernomialInv.Bweight r s p.1 p.2 := by
      rw [azFinset_eq]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Eplus_bridge, Brs_bridge]
    rw [hLHS]
    -- STEP (4): apply the plus capstone
    have hcap := SupernomialInv.left_supernomial_plus r s Stil hℓ hr'
      binaryWordGauss_holds (fun M => h2.2.1 ℓ r s M) (fun M => h2.2.2 ℓ r s M)
      (fun A B => (h3.2 SupernomialInv.q A B (SupernomialInv.muPrime r s))) M
    rw [hcap]
    -- STEP (5): reconcile the RHS. The capstone RHS is
    --   T (s*M) * invSub (Stil q [M, muSize-M] (muPrime r s));
    -- Fact9 RHS is T (s*M) * Stil (T (-1)) [M, ∑(r+s)-M] (List.ofFn (r+s)).
    rw [← invSub_Stil_bridge Stil Tset invStat h2.1.1 r s M]
  · -- MINUS branch (identical modulo Eminus_bridge / left_supernomial_minus)
    intro ℓ hℓ r hr s M
    have hr' : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i := fun i j hij => hr hij
    have hLHS :
        (∑ az ∈ azFinset r s M, T (Eminus r s az.1 az.2) * Brs r s az.1 az.2)
          = ∑ p ∈ SupernomialInv.azFinset r s M,
              LaurentPolynomial.T (SupernomialInv.Eminus r s p.1 p.2)
                * SupernomialInv.Bweight r s p.1 p.2 := by
      rw [azFinset_eq]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Eminus_bridge, Brs_bridge]
    rw [hLHS]
    have hcap := SupernomialInv.left_supernomial_minus r s Stil hℓ hr'
      binaryWordGauss_holds (fun M => h2.2.1 ℓ r s M) (fun M => h2.2.2 ℓ r s M)
      (fun A B => (h3.2 SupernomialInv.q A B (SupernomialInv.muPrime r s))) M
    rw [hcap]
    rw [← invSub_Stil_bridge Stil Tset invStat h2.1.1 r s M]

/-- Corollary 1.2(2), b = 3k+1, from Facts 1,2,3,5,6,8 only. -/
theorem cor_closedForm_plus (k : ℕ) (hk : 1 ≤ k)
    (h1 : Fact1 Stil) (h2 : Fact2Bundle Stil Tset invStat)
    (h3 : Fact3 Stil) (h5 : Fact5) (h6 : Fact6)
    (h8 : Fact8 3 (3 * k + 1)) :
    HJO.zNat 3 (3 * k + 1) = fermPlus k := by
  exact cor_closedForm_plus_from_fact9 Stil Tset invStat tabOf Ja Jz k hk
    h1 h2.1 h3 h5 h6 h8
    (derive_section34_interface Stil Tset invStat tabOf Ja Jz h2 h3 h6)

/-- Corollary 1.2(3), b = 3k-1, from Facts 1,2,3,5,6,8 only. -/
theorem cor_closedForm_minus (k : ℕ) (hk : 2 ≤ k)
    (h1 : Fact1 Stil) (h2 : Fact2Bundle Stil Tset invStat)
    (h3 : Fact3 Stil) (h5 : Fact5) (h6 : Fact6)
    (h8 : Fact8 3 (3 * k - 1)) :
    HJO.zNat 3 (3 * k - 1) = fermMinus k := by
  exact cor_closedForm_minus_from_fact9 Stil Tset invStat tabOf Ja Jz k hk
    h1 h2.1 h3 h5 h6 h8
    (derive_section34_interface Stil Tset invStat tabOf Ja Jz h2 h3 h6)

/-- Theorem 1.1, the formal-series identity, from Facts 1–8 only. -/
theorem thm_main (b : ℕ) (hb : 3 < b) (hcop : Nat.Coprime 3 b)
    (h1 : Fact1 Stil) (h2 : Fact2Bundle Stil Tset invStat)
    (h3 : Fact3 Stil) (h4 : Fact4) (h5 : Fact5) (h6 : Fact6)
    (h7 : Fact7 3 b) (h8 : Fact8 3 b) :
    HJO.Conjecture' 3 b := by
  exact thm_main_from_fact9 Stil Tset invStat tabOf Ja Jz b hb hcop
    h1 h2.1 h3 h4 h5 h6 h7 h8
    (derive_section34_interface Stil Tset invStat tabOf Ja Jz h2 h3 h6)

end FinalTargets
end ProblemHJOa3
