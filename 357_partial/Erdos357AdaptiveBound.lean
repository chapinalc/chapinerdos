/-
Copyright (c) 2026 The authors.

Licensed under the Apache License, Version 2.0. See LICENSE.
-/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Lattice

/-!
# The adaptive packing inequality for Erdős Problem 357

This file formalizes the complete finite adaptive-block argument.
No `sorry`, `axiom`, or unsafe declaration is used. Its final integer-valued
theorems use the same `Fin k`, range, strict-monotonicity, and
order-connected-finset hypotheses as the official formulation.

The four exceptional sets have the following meanings.

* `small`: starting values below the adaptive-length cutoff;
* `boundary`: the final `r - 1` starts in each length class;
* `bad`: starts whose block error exceeds the threshold;
* `good`: every remaining start.

For a good start, the chosen consecutive-block sum lies in
`[(n + 1) / 2, n + T]`. Distinct consecutive-block sums make this map
injective. The other three fields are the exact integer versions of the
small-value, boundary, and Markov estimates. The certificate is then
constructed from every admissible finite sequence.

The main exact theorem is `finite_adaptive_bound_int`. The explicit
cube-scale specialization `cube_scale_adaptive_bound_int` proves
`2k ≤ n + 8m² + 4` whenever `n ≤ m³`, which yields
`k ≤ n/2 + O(n^(2/3))`.
-/

namespace Erdos357

open scoped BigOperators

/--
The distinct-consecutive-sums hypothesis from Erdős Problem 357.

Using order-connected finite sets makes the definition apply to any preorder;
for a linearly ordered index set these are precisely the finite intervals.
-/
def HasDistinctSums {ι A : Type*} [Preorder ι] [AddCommMonoid A]
    (a : ι → A) : Prop :=
  {J : Finset ι | (J : Set ι).OrdConnected}.InjOn
    (fun J ↦ ∑ x ∈ J, a x)

/--
The extremal function from Erdős Problem 357. This is the same definition as
the official formal-conjectures entry, under a conflict-free local name.
-/
noncomputable def f357 (n : ℕ) : ℕ :=
  sSup {k : ℕ |
    ∃ a : Fin k → ℤ,
      Set.range a ⊆ Set.Icc 1 n ∧
      StrictMono a ∧
      HasDistinctSums a}

theorem f357_admissible_nonempty (n : ℕ) :
    {k : ℕ |
      ∃ a : Fin k → ℤ,
        Set.range a ⊆ Set.Icc 1 n ∧
        StrictMono a ∧
        HasDistinctSums a}.Nonempty := by
  refine ⟨0, ?_⟩
  let a : Fin 0 → ℤ := fun i ↦ Fin.elim0 i
  refine ⟨a, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro J hJ K hK hsum
    ext x
    exact Fin.elim0 x

theorem exists_cube_upper (n : ℕ) :
    ∃ m, n ≤ m * m * m := by
  refine ⟨n + 1, ?_⟩
  have h1 : 1 ≤ n + 1 := by omega
  have h2 : n ≤ n + 1 := by omega
  have hm : n + 1 ≤ (n + 1) * (n + 1) := by
    simpa using Nat.mul_le_mul_left (n + 1) h1
  have hm2 :
      (n + 1) * (n + 1) ≤ (n + 1) * (n + 1) * (n + 1) := by
    simpa [Nat.mul_assoc] using
      Nat.mul_le_mul_left ((n + 1) * (n + 1)) h1
  exact h2.trans (hm.trans hm2)

/-- The least natural `m` with `n ≤ m³`. -/
noncomputable def cubeCeil (n : ℕ) : ℕ :=
  Nat.find (exists_cube_upper n)

theorem le_cubeCeil_cube (n : ℕ) :
    n ≤ cubeCeil n * cubeCeil n * cubeCeil n :=
  Nat.find_spec (exists_cube_upper n)

theorem cubeCeil_pos (n : ℕ) (hn : 0 < n) :
    0 < cubeCeil n := by
  have h := le_cubeCeil_cube n
  by_contra hm
  have : cubeCeil n = 0 := by omega
  simp [this] at h
  omega

theorem pred_cubeCeil_cube_lt (n : ℕ) (hn : 0 < n) :
    (cubeCeil n - 1) * (cubeCeil n - 1) *
        (cubeCeil n - 1) < n := by
  have hlt : cubeCeil n - 1 < cubeCeil n := by
    have := cubeCeil_pos n hn
    omega
  have hnot :
      ¬n ≤ (cubeCeil n - 1) * (cubeCeil n - 1) *
        (cubeCeil n - 1) := by
    apply Nat.find_min (exists_cube_upper n)
    simpa [cubeCeil] using hlt
  omega

/--
Distinct interval sums induce an injection on any injectively indexed family
of order-connected blocks.
-/
theorem blockSum_inj_of_hasDistinctSums
    {ι A β : Type*} [Preorder ι] [AddCommMonoid A] [DecidableEq β]
    (a : ι → A) (blocks : β → Finset ι) (good : Finset β)
    (ha : HasDistinctSums a)
    (hconnected : ∀ b ∈ good, (blocks b : Set ι).OrdConnected)
    (hblocks : Set.InjOn blocks good) :
    Set.InjOn (fun b ↦ ∑ x ∈ blocks b, a x) good := by
  intro x hx y hy hsum
  apply hblocks hx hy
  exact ha (hconnected x hx) (hconnected y hy) hsum

/--
The adaptive block length attached to a positive value `x`.
-/
def adaptiveLength (n x : ℕ) : ℕ :=
  n ⌈/⌉ (2 * x)

theorem adaptiveLength_lower (n x : ℕ) (hx : 0 < x) :
    n ≤ 2 * x * adaptiveLength n x := by
  simpa [adaptiveLength, nsmul_eq_mul] using
    (le_smul_ceilDiv (b := n) (a := 2 * x) (by omega))

theorem adaptiveLength_upper_pred
    (n x : ℕ) (hx : 0 < x) (hr : 1 < adaptiveLength n x) :
    2 * x * (adaptiveLength n x - 1) < n := by
  have hnot :
      ¬adaptiveLength n x ≤ adaptiveLength n x - 1 := by omega
  rw [adaptiveLength] at hnot ⊢
  rw [ceilDiv_le_iff_le_mul (by omega)] at hnot
  omega

theorem adaptiveLength_antitone
    (n x y : ℕ) (hx : 0 < x) (hxy : x ≤ y) :
    adaptiveLength n y ≤ adaptiveLength n x := by
  rw [adaptiveLength, ceilDiv_le_iff_le_mul (by omega)]
  have hn : n ≤ 2 * x * (n ⌈/⌉ (2 * x)) := by
    simpa [nsmul_eq_mul] using
      (le_smul_ceilDiv (b := n) (a := 2 * x) (by omega))
  have hm :
      2 * x * (n ⌈/⌉ (2 * x)) ≤
        2 * y * (n ⌈/⌉ (2 * x)) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hxy)
  exact hn.trans hm

theorem adaptiveLength_pos
    (n x : ℕ) (hn : 0 < n) (hx : 0 < x) :
    0 < adaptiveLength n x := by
  have hlower := adaptiveLength_lower n x hx
  by_contra h
  have hr0 : adaptiveLength n x = 0 := Nat.eq_zero_of_not_pos h
  rw [hr0] at hlower
  simp at hlower
  omega

theorem adaptiveLength_mul_le
    (n x : ℕ) (hx : 0 < x) (hxn : x ≤ n) :
    adaptiveLength n x * x ≤ n := by
  by_cases hr : adaptiveLength n x ≤ 1
  · have : adaptiveLength n x * x ≤ 1 * x :=
      Nat.mul_le_mul_right x hr
    omega
  · have hrgt : 1 < adaptiveLength n x := by omega
    have hu := adaptiveLength_upper_pred n x hx hrgt
    have hxmul :
        x ≤ x * (adaptiveLength n x - 1) := by
      have : 1 ≤ adaptiveLength n x - 1 := by omega
      simpa using Nat.mul_le_mul_left x this
    have hdecomp :
        adaptiveLength n x * x =
          x * (adaptiveLength n x - 1) + x := by
      have hrdecomp :
          adaptiveLength n x = (adaptiveLength n x - 1) + 1 := by
        omega
      rw [hrdecomp, Nat.add_mul]
      simp [Nat.mul_comm]
    rw [hdecomp]
    have htwice :
        x * (adaptiveLength n x - 1) +
            x * (adaptiveLength n x - 1) < n := by
      rw [show
        x * (adaptiveLength n x - 1) +
            x * (adaptiveLength n x - 1) =
          2 * x * (adaptiveLength n x - 1) by
            calc
              x * (adaptiveLength n x - 1) +
                  x * (adaptiveLength n x - 1) =
                2 * (x * (adaptiveLength n x - 1)) :=
                  (two_mul _).symm
              _ = 2 * x * (adaptiveLength n x - 1) := by ac_rfl]
      exact hu
    omega

theorem adaptiveLength_gt_imp
    (n x R : ℕ) (hx : 0 < x)
    (hlarge : R < adaptiveLength n x) :
    2 * x * R < n := by
  have hnot : ¬adaptiveLength n x ≤ R := by omega
  rw [adaptiveLength, ceilDiv_le_iff_le_mul (by omega)] at hnot
  omega

/--
Starts whose adaptive block length is above the cutoff.
-/
def smallStarts (a : ℕ → ℕ) (n k R : ℕ) : Finset ℕ :=
  (Finset.range k).filter (fun i ↦ R < adaptiveLength n (a i))

/--
There are few small-value starts, because their values are distinct positive
integers below `n/(2R)`.
-/
theorem smallStarts_card_mul_le
    (a : ℕ → ℕ) (n k R : ℕ) (hR : 0 < R)
    (hpos : ∀ i < k, 0 < a i)
    (hinj : Set.InjOn a (Finset.range k : Set ℕ)) :
    (smallStarts a n k R).card * (2 * R) ≤ n + 2 * R := by
  let Q := (n + 2 * R) / (2 * R)
  have hmaps :
      Set.MapsTo a (smallStarts a n k R : Set ℕ)
        (Finset.Icc 1 Q : Set ℕ) := by
    intro i hi
    have hi' : i ∈ smallStarts a n k R := hi
    rcases Finset.mem_filter.mp hi' with ⟨hik', hlarge⟩
    have hik : i < k := Finset.mem_range.mp hik'
    have hai : 0 < a i := hpos i hik
    have hmul : 2 * a i * R < n :=
      adaptiveLength_gt_imp n (a i) R hai hlarge
    have hmul' : a i * (2 * R) ≤ n + 2 * R := by
      rw [show a i * (2 * R) = 2 * a i * R by ac_rfl]
      omega
    have haiQ : a i ≤ Q :=
      (Nat.le_div_iff_mul_le (by omega)).2 hmul'
    simpa only [Finset.coe_Icc, Set.mem_Icc] using
      And.intro (by omega : 1 ≤ a i) haiQ
  have hinjSmall : Set.InjOn a (smallStarts a n k R) := by
    intro i hi j hj hEq
    have hi' : i ∈ smallStarts a n k R := hi
    have hj' : j ∈ smallStarts a n k R := hj
    apply hinj
    · exact (Finset.mem_filter.mp hi').1
    · exact (Finset.mem_filter.mp hj').1
    · exact hEq
  have hcard :
      (smallStarts a n k R).card ≤ (Finset.Icc 1 Q).card :=
    Finset.card_le_card_of_injOn a hmaps hinjSmall
  have hcardQ : (smallStarts a n k R).card ≤ Q := by
    simpa [Q, Nat.card_Icc] using hcard
  calc
    (smallStarts a n k R).card * (2 * R) ≤ Q * (2 * R) :=
      Nat.mul_le_mul_right (2 * R) hcardQ
    _ ≤ n + 2 * R := Nat.div_mul_le_self _ _

/-- The maximum of a natural-valued finset, defaulting to zero when empty. -/
def maxOrZero (s : Finset ℕ) : ℕ :=
  if h : s.Nonempty then s.max' h else 0

theorem le_maxOrZero {s : Finset ℕ} {i : ℕ} (hi : i ∈ s) :
    i ≤ maxOrZero s := by
  have hs : s.Nonempty := ⟨i, hi⟩
  simp only [maxOrZero, dif_pos hs]
  exact Finset.le_max' s i hi

theorem maxOrZero_mem {s : Finset ℕ} (hs : s.Nonempty) :
    maxOrZero s ∈ s := by
  simp only [maxOrZero, dif_pos hs]
  exact Finset.max'_mem s hs

/-- The minimum of a natural-valued finset, defaulting to zero when empty. -/
def minOrZero (s : Finset ℕ) : ℕ :=
  if h : s.Nonempty then s.min' h else 0

theorem minOrZero_le {s : Finset ℕ} {i : ℕ} (hi : i ∈ s) :
    minOrZero s ≤ i := by
  have hs : s.Nonempty := ⟨i, hi⟩
  simp only [minOrZero, dif_pos hs]
  exact Finset.min'_le s i hi

theorem minOrZero_mem {s : Finset ℕ} (hs : s.Nonempty) :
    minOrZero s ∈ s := by
  simp only [minOrZero, dif_pos hs]
  exact Finset.min'_mem s hs

/-- Indices below `k` having adaptive length exactly `q`. -/
def lengthClass (rfun : ℕ → ℕ) (k q : ℕ) : Finset ℕ :=
  (Finset.range k).filter (fun i ↦ rfun i = q)

/--
The last `q-1` potential starts in a length class. The definition uses distance
from the largest index in the class, so its cardinality bound does not require
the class to be nonempty.
-/
def classBoundary (rfun : ℕ → ℕ) (k q : ℕ) : Finset ℕ :=
  (lengthClass rfun k q).filter
    (fun i ↦ maxOrZero (lengthClass rfun k q) < i + q - 1)

/-- Starts whose entire length-`q` block remains before the class maximum. -/
def classInterior (rfun : ℕ → ℕ) (k q : ℕ) : Finset ℕ :=
  (lengthClass rfun k q).filter
    (fun i ↦ i + q - 1 ≤ maxOrZero (lengthClass rfun k q))

theorem classInterior_subset_interval
    (rfun : ℕ → ℕ) (k q : ℕ) (hq : 0 < q) :
    classInterior rfun k q ⊆
      Finset.Icc
        (minOrZero (lengthClass rfun k q))
        (maxOrZero (lengthClass rfun k q) + 1 - q) := by
  intro i hi
  let C := lengthClass rfun k q
  let lo := minOrZero C
  let M := maxOrZero C
  have hi' : i ∈ classInterior rfun k q := hi
  rcases Finset.mem_filter.mp hi' with ⟨hiC', hnear'⟩
  change i ∈ C at hiC'
  change i + q - 1 ≤ M at hnear'
  have hloi : lo ≤ i := minOrZero_le hiC'
  have hihi : i ≤ M + 1 - q := by omega
  simpa only [Finset.mem_Icc] using And.intro hloi hihi

theorem classInterior_interval_nonempty
    (rfun : ℕ → ℕ) (k q : ℕ) (hq : 0 < q)
    (hS : (classInterior rfun k q).Nonempty) :
    minOrZero (lengthClass rfun k q) ≤
      maxOrZero (lengthClass rfun k q) + 1 - q := by
  rcases hS with ⟨i, hi⟩
  have hsub := classInterior_subset_interval rfun k q hq hi
  exact (Finset.mem_Icc.mp hsub).1.trans (Finset.mem_Icc.mp hsub).2

theorem classInterior_last_endpoint
    (rfun : ℕ → ℕ) (k q : ℕ) (hq : 0 < q)
    (hS : (classInterior rfun k q).Nonempty) :
    (maxOrZero (lengthClass rfun k q) + 1 - q) + q - 1 =
      maxOrZero (lengthClass rfun k q) := by
  rcases hS with ⟨i, hi⟩
  have hi' : i ∈ classInterior rfun k q := hi
  have hnear := (Finset.mem_filter.mp hi').2
  omega

theorem classBoundary_card_le (rfun : ℕ → ℕ) (k q : ℕ) :
    (classBoundary rfun k q).card ≤ q - 1 := by
  let C := lengthClass rfun k q
  let M := maxOrZero C
  let d : ℕ → ℕ := fun i ↦ M - i
  have hmaps :
      Set.MapsTo d (classBoundary rfun k q : Set ℕ)
        (Finset.range (q - 1) : Set ℕ) := by
    intro i hi
    have hi' : i ∈ classBoundary rfun k q := hi
    rcases Finset.mem_filter.mp hi' with ⟨hiC', hnear'⟩
    change i ∈ C at hiC'
    change M < i + q - 1 at hnear'
    simp only [Finset.coe_range, Set.mem_Iio]
    have hiM : i ≤ M := le_maxOrZero hiC'
    change M - i < q - 1
    omega
  have hinj : Set.InjOn d (classBoundary rfun k q) := by
    intro i hi j hj heq
    have hi' : i ∈ classBoundary rfun k q := hi
    have hj' : j ∈ classBoundary rfun k q := hj
    have hiC' := (Finset.mem_filter.mp hi').1
    have hjC' := (Finset.mem_filter.mp hj').1
    change i ∈ C at hiC'
    change j ∈ C at hjC'
    have hiM : i ≤ M := le_maxOrZero hiC'
    have hjM : j ≤ M := le_maxOrZero hjC'
    dsimp only [d] at heq
    omega
  have hcard :
      (classBoundary rfun k q).card ≤ (Finset.range (q - 1)).card :=
    Finset.card_le_card_of_injOn d hmaps hinj
  simpa using hcard

/-- The union of the boundary sets for adaptive lengths `1,...,R`. -/
def boundaryStarts (rfun : ℕ → ℕ) (k R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).biUnion (classBoundary rfun k)

theorem boundaryStarts_card_le (rfun : ℕ → ℕ) (k R : ℕ) :
    (boundaryStarts rfun k R).card ≤ R * (R - 1) / 2 := by
  have hcard :
      (boundaryStarts rfun k R).card ≤
        ∑ q ∈ Finset.Icc 1 R, (classBoundary rfun k q).card :=
    Finset.card_biUnion_le
  have hsum :
      (∑ q ∈ Finset.Icc 1 R, (classBoundary rfun k q).card) ≤
        ∑ q ∈ Finset.Icc 1 R, (q - 1) := by
    apply Finset.sum_le_sum
    intro q hq
    exact classBoundary_card_le rfun k q
  calc
    (boundaryStarts rfun k R).card ≤
        ∑ q ∈ Finset.Icc 1 R, (classBoundary rfun k q).card := hcard
    _ ≤ ∑ q ∈ Finset.Icc 1 R, (q - 1) := hsum
    _ = R * (R - 1) / 2 := by
      rw [← Finset.Ico_add_one_right_eq_Icc,
        Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left]
      rw [Finset.sum_range_id]
      congr 1

/--
When the length function is antitone, a non-boundary start remains in its
length class throughout its whole block.
-/
theorem retained_block_in_class
    (rfun : ℕ → ℕ) (k q i t : ℕ)
    (hanti :
      ∀ ⦃x⦄, x < k → ∀ ⦃y⦄, y < k → x ≤ y → rfun y ≤ rfun x)
    (hi : i ∈ lengthClass rfun k q)
    (hnb : i ∉ classBoundary rfun k q)
    (ht : t < q) :
    i + t < k ∧ rfun (i + t) = q := by
  let C := lengthClass rfun k q
  let M := maxOrZero C
  have hiC : i ∈ C := hi
  have hC : C.Nonempty := ⟨i, hiC⟩
  have hMmem : M ∈ C := maxOrZero_mem hC
  have hiData := Finset.mem_filter.mp hi
  have hMData := Finset.mem_filter.mp hMmem
  have hik : i < k := Finset.mem_range.mp hiData.1
  have hMk : M < k := Finset.mem_range.mp hMData.1
  have hri : rfun i = q := hiData.2
  have hrM : rfun M = q := hMData.2
  have hnotNear : ¬M < i + q - 1 := by
    intro hnear
    apply hnb
    exact Finset.mem_filter.mpr ⟨hi, hnear⟩
  have hitM : i + t ≤ M := by omega
  have hitk : i + t < k := hitM.trans_lt hMk
  have hupper : rfun (i + t) ≤ q := by
    rw [← hri]
    exact hanti hik hitk (by omega)
  have hlower : q ≤ rfun (i + t) := by
    rw [← hrM]
    exact hanti hitk hMk hitM
  exact ⟨hitk, hupper.antisymm hlower⟩

/--
Telescoping bound for shifted differences of a monotone natural-valued
sequence.

Although there may be arbitrarily many summands, only the `t` terms crossing
the two ends survive after telescoping. This is the estimate used inside each
adaptive-length class.
-/
theorem sum_shift_tsub_le_span
    (a : ℕ → ℕ) (N t L U : ℕ)
    (hmono : Monotone a) (hL : L ≤ a 0) (hU : a (N + t) ≤ U) :
    ∑ i ∈ Finset.range N, (a (i + t) - a i) ≤ t * (U - L) := by
  induction t generalizing U with
  | zero => simp
  | succ t ih =>
      have hU' : a (N + t) ≤ U := by
        exact (hmono (by omega)).trans hU
      have hrec :
          ∑ i ∈ Finset.range N, (a (i + t) - a i) ≤ t * (U - L) :=
        ih U hU'
      have hsplit :
          ∀ i,
            a (i + (t + 1)) - a i =
              (a (i + t + 1) - a (i + t)) + (a (i + t) - a i) := by
        intro i
        have h₁ : a i ≤ a (i + t) := hmono (by omega)
        have h₂ : a (i + t) ≤ a (i + t + 1) := hmono (by omega)
        have hidx : i + (t + 1) = i + t + 1 := by omega
        rw [hidx]
        omega
      have hshift : Monotone (fun j ↦ a (j + t)) := by
        intro i j hij
        exact hmono (Nat.add_le_add_right hij t)
      have htel :
          ∑ i ∈ Finset.range N, (a (i + t + 1) - a (i + t)) =
            a (N + t) - a t := by
        simpa only [Nat.zero_add, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using Finset.sum_range_tsub hshift N
      have hspan : a (N + t) - a t ≤ U - L := by
        have hLat : L ≤ a t :=
          hL.trans (hmono (Nat.zero_le t))
        omega
      calc
        ∑ i ∈ Finset.range N, (a (i + (t + 1)) - a i) =
            ∑ i ∈ Finset.range N,
              ((a (i + t + 1) - a (i + t)) + (a (i + t) - a i)) := by
                apply Finset.sum_congr rfl
                intro i hi
                exact hsplit i
        _ =
            (∑ i ∈ Finset.range N, (a (i + t + 1) - a (i + t))) +
              ∑ i ∈ Finset.range N, (a (i + t) - a i) := by
                exact Finset.sum_add_distrib
        _ = (a (N + t) - a t) +
              ∑ i ∈ Finset.range N, (a (i + t) - a i) := by
                rw [htel]
        _ ≤ (U - L) + t * (U - L) :=
          Nat.add_le_add hspan hrec
        _ = (t + 1) * (U - L) := by
          simp [Nat.add_mul, Nat.add_comm]

/--
The endpoint-sharp version of `sum_shift_tsub_le_span`. Here `U` need only
bound the largest term that actually occurs, at index `N + t - 1`.
-/
theorem sum_shift_tsub_le_span_tight
    (a : ℕ → ℕ) (N t L U : ℕ)
    (hN : 0 < N) (hmono : Monotone a)
    (hL : L ≤ a 0) (hU : a (N + t - 1) ≤ U) :
    ∑ i ∈ Finset.range N, (a (i + t) - a i) ≤ t * (U - L) := by
  induction t generalizing U with
  | zero => simp
  | succ t ih =>
      have hendpoint : N + (t + 1) - 1 = N + t := by omega
      have hUNt : a (N + t) ≤ U := by
        simpa [hendpoint] using hU
      have hU' : a (N + t - 1) ≤ U := by
        exact (hmono (by omega)).trans hUNt
      have hrec :
          ∑ i ∈ Finset.range N, (a (i + t) - a i) ≤ t * (U - L) :=
        ih U hU'
      have hsplit :
          ∀ i,
            a (i + (t + 1)) - a i =
              (a (i + t + 1) - a (i + t)) + (a (i + t) - a i) := by
        intro i
        have h₁ : a i ≤ a (i + t) := hmono (by omega)
        have h₂ : a (i + t) ≤ a (i + t + 1) := hmono (by omega)
        have hidx : i + (t + 1) = i + t + 1 := by omega
        rw [hidx]
        omega
      have hshift : Monotone (fun j ↦ a (j + t)) := by
        intro i j hij
        exact hmono (Nat.add_le_add_right hij t)
      have htel :
          ∑ i ∈ Finset.range N, (a (i + t + 1) - a (i + t)) =
            a (N + t) - a t := by
        simpa only [Nat.zero_add, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using Finset.sum_range_tsub hshift N
      have hspan : a (N + t) - a t ≤ U - L := by
        have hLat : L ≤ a t :=
          hL.trans (hmono (Nat.zero_le t))
        omega
      calc
        ∑ i ∈ Finset.range N, (a (i + (t + 1)) - a i) =
            ∑ i ∈ Finset.range N,
              ((a (i + t + 1) - a (i + t)) + (a (i + t) - a i)) := by
                apply Finset.sum_congr rfl
                intro i hi
                exact hsplit i
        _ =
            (∑ i ∈ Finset.range N, (a (i + t + 1) - a (i + t))) +
              ∑ i ∈ Finset.range N, (a (i + t) - a i) := by
                exact Finset.sum_add_distrib
        _ = (a (N + t) - a t) +
              ∑ i ∈ Finset.range N, (a (i + t) - a i) := by
                rw [htel]
        _ ≤ (U - L) + t * (U - L) :=
          Nat.add_le_add hspan hrec
        _ = (t + 1) * (U - L) := by
          simp [Nat.add_mul, Nat.add_comm]

/--
Endpoint-sharp telescoping over an arbitrary natural interval.
-/
theorem sum_Icc_shift_tsub_le_span
    (a : ℕ → ℕ) (lo hi t L U : ℕ)
    (hlohi : lo ≤ hi) (hmono : Monotone a)
    (hL : L ≤ a lo) (hU : a (hi + t) ≤ U) :
    ∑ i ∈ Finset.Icc lo hi, (a (i + t) - a i) ≤ t * (U - L) := by
  rw [← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range]
  let N := hi + 1 - lo
  let b : ℕ → ℕ := fun j ↦ a (lo + j)
  have hN : 0 < N := by
    dsimp [N]
    omega
  have hbmono : Monotone b :=
    fun _ _ h ↦ hmono (Nat.add_le_add_left h lo)
  have hbL : L ≤ b 0 := by simpa [b] using hL
  have hidx : lo + (N + t - 1) = hi + t := by
    dsimp [N]
    omega
  have hbU : b (N + t - 1) ≤ U := by
    simpa [b, hidx] using hU
  simpa only [b, Nat.add_assoc] using
    sum_shift_tsub_le_span_tight b N t L U hN hbmono hbL hbU

/--
The error of the length-`r` block beginning at `i`, relative to the constant
block `r * a i`.
-/
def blockError (a : ℕ → ℕ) (i r : ℕ) : ℕ :=
  ∑ t ∈ Finset.range r, (a (i + t) - a i)

/--
Total error over `N` consecutive starts inside one value class.

The quadratic factor is independent of `N`; this is the key telescoping gain
over estimating each start separately.
-/
theorem sum_blockError_le
    (a : ℕ → ℕ) (N r L U : ℕ)
    (hmono : Monotone a) (hL : L ≤ a 0) (hU : a (N + r) ≤ U) :
    ∑ i ∈ Finset.range N, blockError a i r ≤
      (r * (r - 1) / 2) * (U - L) := by
  calc
    ∑ i ∈ Finset.range N, blockError a i r =
        ∑ t ∈ Finset.range r,
          ∑ i ∈ Finset.range N, (a (i + t) - a i) := by
            simp only [blockError]
            rw [Finset.sum_comm]
    _ ≤ ∑ t ∈ Finset.range r, t * (U - L) := by
      apply Finset.sum_le_sum
      intro t ht
      have htr : t ≤ r := (Finset.mem_range.mp ht).le
      have hUt : a (N + t) ≤ U :=
        (hmono (Nat.add_le_add_left htr N)).trans hU
      exact sum_shift_tsub_le_span a N t L U hmono hL hUt
    _ = (r * (r - 1) / 2) * (U - L) := by
      rw [← Finset.sum_mul, Finset.sum_range_id]

/--
The same block-error estimate for any set of starts contained in an interval.
The upper endpoint assumption is sharp: it mentions only `hi + r - 1`.
-/
theorem sum_blockError_subset_Icc_le
    (a : ℕ → ℕ) (starts : Finset ℕ) (lo hi r L U : ℕ)
    (hr : 0 < r) (hlohi : lo ≤ hi)
    (hstarts : starts ⊆ Finset.Icc lo hi)
    (hmono : Monotone a) (hL : L ≤ a lo)
    (hU : a (hi + r - 1) ≤ U) :
    ∑ i ∈ starts, blockError a i r ≤
      (r * (r - 1) / 2) * (U - L) := by
  calc
    ∑ i ∈ starts, blockError a i r =
        ∑ t ∈ Finset.range r,
          ∑ i ∈ starts, (a (i + t) - a i) := by
            simp only [blockError]
            rw [Finset.sum_comm]
    _ ≤ ∑ t ∈ Finset.range r, t * (U - L) := by
      apply Finset.sum_le_sum
      intro t ht
      have htr : t ≤ r - 1 := by
        have := Finset.mem_range.mp ht
        omega
      have hUlast : a (hi + (r - 1)) ≤ U := by
        rw [show hi + (r - 1) = hi + r - 1 by omega]
        exact hU
      have hUt : a (hi + t) ≤ U :=
        (hmono (Nat.add_le_add_left htr hi)).trans hUlast
      calc
        ∑ i ∈ starts, (a (i + t) - a i) ≤
            ∑ i ∈ Finset.Icc lo hi, (a (i + t) - a i) :=
          Finset.sum_le_sum_of_subset hstarts
        _ ≤ t * (U - L) :=
          sum_Icc_shift_tsub_le_span a lo hi t L U
            hlohi hmono hL hUt
    _ = (r * (r - 1) / 2) * (U - L) := by
      rw [← Finset.sum_mul, Finset.sum_range_id]

/--
Finite Markov counting with no division: if every selected error is at least
`q`, then the selected cardinality times `q` is at most the total error.
-/
theorem card_mul_le_sum_of_threshold
    {α : Type*} [DecidableEq α] (s : Finset α) (e : α → ℕ) (q : ℕ)
    (hlarge : ∀ i ∈ s, q ≤ e i) :
    s.card * q ≤ ∑ i ∈ s, e i := by
  calc
    s.card * q = ∑ _i ∈ s, q := by simp
    _ ≤ ∑ i ∈ s, e i := by
      apply Finset.sum_le_sum
      intro i hi
      exact hlarge i hi

/--
The threshold count and telescoping lemmas combine into the per-class
exception bound used by the adaptive argument.
-/
theorem bad_block_count_le_class_budget
    (a : ℕ → ℕ) (N r L U q : ℕ) (bad : Finset ℕ)
    (hmono : Monotone a) (hL : L ≤ a 0) (hU : a (N + r) ≤ U)
    (hbad : bad ⊆ Finset.range N)
    (hlarge : ∀ i ∈ bad, q ≤ blockError a i r) :
    bad.card * q ≤ (r * (r - 1) / 2) * (U - L) := by
  calc
    bad.card * q ≤ ∑ i ∈ bad, blockError a i r :=
      card_mul_le_sum_of_threshold bad (fun i ↦ blockError a i r) q hlarge
    _ ≤ ∑ i ∈ Finset.range N, blockError a i r :=
      Finset.sum_le_sum_of_subset hbad
    _ ≤ (r * (r - 1) / 2) * (U - L) :=
      sum_blockError_le a N r L U hmono hL hU

/--
Four times the triangular number `r(r-1)/2` is exactly `2r(r-1)`.
The proof records the parity step explicitly, rather than relying on nonlinear
division normalization.
-/
theorem four_mul_triangular (r : ℕ) :
    (r * (r - 1) / 2) * 4 = 2 * r * (r - 1) := by
  have hdvd : 2 ∣ r * (r - 1) := by
    rcases Nat.even_mul_pred_self r with ⟨q, hq⟩
    exact ⟨q, by omega⟩
  have hcancel : r * (r - 1) / 2 * 2 = r * (r - 1) :=
    Nat.div_mul_cancel hdvd
  calc
    (r * (r - 1) / 2) * 4 =
        (r * (r - 1) / 2 * 2) * 2 := by omega
    _ = (r * (r - 1)) * 2 := by rw [hcancel]
    _ = 2 * r * (r - 1) := by ac_rfl

theorem two_mul_triangular (r : ℕ) :
    (r * (r - 1) / 2) * 2 = r * (r - 1) := by
  have hdvd : 2 ∣ r * (r - 1) := by
    rcases Nat.even_mul_pred_self r with ⟨q, hq⟩
    exact ⟨q, by omega⟩
  exact Nat.div_mul_cancel hdvd

/--
Exact width estimate for one adaptive length class.

The hypotheses say that the smallest class value `L` satisfies
`n ≤ 2Lr`, while the largest class value `U` satisfies
`2U(r-1) < n`. Their difference therefore has width at most
`n / (2r(r-1))`, expressed without division or real numbers.
-/
theorem adaptive_class_width
    (n r L U : ℕ) (hr : 0 < r)
    (hLower : n ≤ 2 * L * r)
    (hUpper : 2 * U * (r - 1) < n) :
    2 * r * (r - 1) * (U - L) ≤ n := by
  by_cases hLU : L ≤ U
  · have hU' :
        (2 * r * (r - 1)) * U < n * r := by
      rw [show (2 * r * (r - 1)) * U =
        (2 * U * (r - 1)) * r by ac_rfl]
      exact Nat.mul_lt_mul_of_pos_right hUpper hr
    have hL' :
        n * (r - 1) ≤ (2 * r * (r - 1)) * L := by
      calc
        n * (r - 1) ≤ (2 * L * r) * (r - 1) :=
          Nat.mul_le_mul_right (r - 1) hLower
        _ = (2 * r * (r - 1)) * L := by ac_rfl
    have hrdecomp : r = (r - 1) + 1 := by omega
    have hnr : n * r = n + n * (r - 1) := by
      calc
        n * r = n * ((r - 1) + 1) :=
          congrArg (fun x ↦ n * x) hrdecomp
        _ = n * (r - 1) + n := by simp [Nat.mul_add]
        _ = n + n * (r - 1) := Nat.add_comm _ _
    rw [hnr] at hU'
    have hcomp :
        (2 * r * (r - 1)) * U <
          n + (2 * r * (r - 1)) * L :=
      hU'.trans_le (Nat.add_le_add_left hL' n)
    have hsplit :
        (2 * r * (r - 1)) * (U - L) +
            (2 * r * (r - 1)) * L =
          (2 * r * (r - 1)) * U := by
      rw [Nat.mul_sub_left_distrib,
        Nat.sub_add_cancel (Nat.mul_le_mul_left _ hLU)]
    rw [← hsplit] at hcomp
    exact ((Nat.add_lt_add_iff_right).mp hcomp).le
  · have : U ≤ L := by omega
    simp [Nat.sub_eq_zero_of_le this]

/--
The total block error contributed by every interior start of one adaptive
length class is at most `n/4`.

Unlike `AdaptivePackingCertificate`, this theorem constructs the class
endpoints from the actual adaptive length function; in particular, it
kernel-checks the delicate class-width and endpoint rounding.
-/
theorem four_mul_classInterior_error_le
    (a : ℕ → ℕ) (n k q : ℕ)
    (hn : 0 < n) (hq : 0 < q)
    (hmono : Monotone a)
    (hpos : ∀ i < k, 0 < a i)
    (hclass :
      (classInterior (fun i ↦ adaptiveLength n (a i)) k q).Nonempty) :
    (∑ i ∈ classInterior (fun i ↦ adaptiveLength n (a i)) k q,
        blockError a i q) * 4 ≤ n := by
  let rfun : ℕ → ℕ := fun i ↦ adaptiveLength n (a i)
  let C := lengthClass rfun k q
  let S := classInterior rfun k q
  let lo := minOrZero C
  let M := maxOrZero C
  let hi := M + 1 - q
  have hS : S.Nonempty := hclass
  have hC : C.Nonempty := by
    rcases hS with ⟨i, hiS⟩
    exact ⟨i, (Finset.mem_filter.mp hiS).1⟩
  have hlomem : lo ∈ C := minOrZero_mem hC
  have hMmem : M ∈ C := maxOrZero_mem hC
  have hloData := Finset.mem_filter.mp hlomem
  have hMData := Finset.mem_filter.mp hMmem
  have hlok : lo < k := Finset.mem_range.mp hloData.1
  have hMk : M < k := Finset.mem_range.mp hMData.1
  have hrlo : rfun lo = q := hloData.2
  have hrM : rfun M = q := hMData.2
  have hqEq : adaptiveLength n (a lo) = q := hrlo
  have hqMEq : adaptiveLength n (a M) = q := hrM
  have halopos : 0 < a lo := hpos lo hlok
  have haMpos : 0 < a M := hpos M hMk
  have hlohi : lo ≤ hi :=
    classInterior_interval_nonempty rfun k q hq hS
  have hsubset : S ⊆ Finset.Icc lo hi :=
    classInterior_subset_interval rfun k q hq
  have hendpoint : hi + q - 1 = M :=
    classInterior_last_endpoint rfun k q hq hS
  have hLower : n ≤ 2 * a lo * q := by
    rw [← hqEq]
    exact adaptiveLength_lower n (a lo) halopos
  have hUpper : 2 * a M * (q - 1) < n := by
    by_cases hq1 : q = 1
    · have hqm1 : q - 1 = 0 := by omega
      rw [hqm1]
      simp
      exact hn
    · have hqgt : 1 < q := by omega
      rw [← hqMEq] at hqgt ⊢
      exact adaptiveLength_upper_pred n (a M) haMpos hqgt
  have herr :=
    sum_blockError_subset_Icc_le a S lo hi q (a lo) (a M)
      hq hlohi hsubset hmono (le_refl _) (by rw [hendpoint])
  have hwidth :=
    adaptive_class_width n q (a lo) (a M) hq hLower hUpper
  calc
    (∑ i ∈ S, blockError a i q) * 4 ≤
        ((q * (q - 1) / 2) * (a M - a lo)) * 4 :=
      Nat.mul_le_mul_right 4 herr
    _ = (2 * q * (q - 1)) * (a M - a lo) := by
      rw [show ((q * (q - 1) / 2) * (a M - a lo)) * 4 =
        ((q * (q - 1) / 2) * 4) * (a M - a lo) by ac_rfl,
        four_mul_triangular]
    _ ≤ n := hwidth

/-- Interior starts in one class whose block error exceeds `T`. -/
def badClass (a : ℕ → ℕ) (n k T q : ℕ) : Finset ℕ :=
  (classInterior (fun i ↦ adaptiveLength n (a i)) k q).filter
    (fun i ↦ T < blockError a i q)

theorem badClass_card_mul_le
    (a : ℕ → ℕ) (n k T q : ℕ)
    (hn : 0 < n) (hq : 0 < q)
    (hmono : Monotone a)
    (hpos : ∀ i < k, 0 < a i) :
    (badClass a n k T q).card * (4 * T) ≤ n := by
  let S := classInterior (fun i ↦ adaptiveLength n (a i)) k q
  by_cases hS : S.Nonempty
  · have hcount :
        (badClass a n k T q).card * T ≤
          ∑ i ∈ S, blockError a i q := by
      calc
        (badClass a n k T q).card * T ≤
            ∑ i ∈ badClass a n k T q, blockError a i q := by
          apply card_mul_le_sum_of_threshold
          intro i hi
          have hi' : i ∈ badClass a n k T q := hi
          exact (Finset.mem_filter.mp hi').2.le
        _ ≤ ∑ i ∈ S, blockError a i q := by
          apply Finset.sum_le_sum_of_subset
          intro i hi
          exact (Finset.mem_filter.mp hi).1
    have herr :=
      four_mul_classInterior_error_le a n k q hn hq hmono hpos hS
    calc
      (badClass a n k T q).card * (4 * T) =
          ((badClass a n k T q).card * T) * 4 := by ac_rfl
      _ ≤ (∑ i ∈ S, blockError a i q) * 4 :=
        Nat.mul_le_mul_right 4 hcount
      _ ≤ n := herr
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [badClass, S, hEmpty]

/-- The union of bad starts over the nontrivial classes `2,...,R`. -/
def badStarts (a : ℕ → ℕ) (n k R T : ℕ) : Finset ℕ :=
  (Finset.Icc 2 R).biUnion (badClass a n k T)

theorem badStarts_card_mul_le
    (a : ℕ → ℕ) (n k R T : ℕ)
    (hn : 0 < n)
    (hmono : Monotone a)
    (hpos : ∀ i < k, 0 < a i) :
    (badStarts a n k R T).card * (4 * T) ≤ n * (R - 1) := by
  have hcard :
      (badStarts a n k R T).card ≤
        ∑ q ∈ Finset.Icc 2 R, (badClass a n k T q).card :=
    Finset.card_biUnion_le
  calc
    (badStarts a n k R T).card * (4 * T) ≤
        (∑ q ∈ Finset.Icc 2 R, (badClass a n k T q).card) * (4 * T) :=
      Nat.mul_le_mul_right (4 * T) hcard
    _ = ∑ q ∈ Finset.Icc 2 R,
          (badClass a n k T q).card * (4 * T) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ _q ∈ Finset.Icc 2 R, n := by
      apply Finset.sum_le_sum
      intro q hq
      exact badClass_card_mul_le a n k T q hn
        (by
          have := (Finset.mem_Icc.mp hq).1
          omega)
        hmono hpos
    _ = n * (R - 1) := by
      simp only [Finset.sum_const_nat, Nat.card_Icc]
      rw [show R + 1 - 2 = R - 1 by omega]
      exact Nat.mul_comm _ _

/--
One adaptive class contributes at most `n/4` total error, with the
denominator cleared. This is the crucial estimate behind the global Markov
discard.
-/
theorem four_mul_sum_blockError_le
    (a : ℕ → ℕ) (n N r L U : ℕ)
    (hr : 0 < r)
    (hmono : Monotone a) (hL : L ≤ a 0) (hU : a (N + r) ≤ U)
    (hLower : n ≤ 2 * L * r)
    (hUpper : 2 * U * (r - 1) < n) :
    (∑ i ∈ Finset.range N, blockError a i r) * 4 ≤ n := by
  have herr := sum_blockError_le a N r L U hmono hL hU
  have hwidth := adaptive_class_width n r L U hr hLower hUpper
  calc
    (∑ i ∈ Finset.range N, blockError a i r) * 4 ≤
        ((r * (r - 1) / 2) * (U - L)) * 4 :=
      Nat.mul_le_mul_right 4 herr
    _ = (2 * r * (r - 1)) * (U - L) := by
      rw [show ((r * (r - 1) / 2) * (U - L)) * 4 =
        ((r * (r - 1) / 2) * 4) * (U - L) by ac_rfl,
        four_mul_triangular]
    _ ≤ n := hwidth

/--
Consequently, the number of starts in one adaptive class whose error reaches
threshold `q` satisfies `4q · #bad ≤ n`.
-/
theorem bad_block_count_four_mul_le
    (a : ℕ → ℕ) (n N r L U q : ℕ) (bad : Finset ℕ)
    (hr : 0 < r)
    (hmono : Monotone a) (hL : L ≤ a 0) (hU : a (N + r) ≤ U)
    (hLower : n ≤ 2 * L * r)
    (hUpper : 2 * U * (r - 1) < n)
    (hbad : bad ⊆ Finset.range N)
    (hlarge : ∀ i ∈ bad, q ≤ blockError a i r) :
    bad.card * (4 * q) ≤ n := by
  have hcount :
      bad.card * q ≤ ∑ i ∈ Finset.range N, blockError a i r := by
    calc
      bad.card * q ≤ ∑ i ∈ bad, blockError a i r :=
        card_mul_le_sum_of_threshold bad (fun i ↦ blockError a i r) q hlarge
      _ ≤ ∑ i ∈ Finset.range N, blockError a i r :=
        Finset.sum_le_sum_of_subset hbad
  have herr :=
    four_mul_sum_blockError_le a n N r L U hr hmono hL hU hLower hUpper
  calc
    bad.card * (4 * q) = (bad.card * q) * 4 := by ac_rfl
    _ ≤ (∑ i ∈ Finset.range N, blockError a i r) * 4 :=
      Nat.mul_le_mul_right 4 hcount
    _ ≤ n := herr

/-- The sum of the length-`r` block starting at `i`. -/
def natBlockSum (a : ℕ → ℕ) (i r : ℕ) : ℕ :=
  ∑ t ∈ Finset.range r, a (i + t)

/--
All positive-length blocks contained in the first `k` entries have distinct
sums.
-/
def HasDistinctBlockSums (a : ℕ → ℕ) (k : ℕ) : Prop :=
  Set.InjOn
    (fun p : ℕ × ℕ ↦ natBlockSum a p.1 p.2)
    {p | 0 < p.2 ∧ p.1 + p.2 ≤ k}

theorem natBlockSum_eq (a : ℕ → ℕ) (i r : ℕ)
    (hmono : Monotone a) :
    natBlockSum a i r = r * a i + blockError a i r := by
  calc
    natBlockSum a i r =
        ∑ t ∈ Finset.range r,
          (a i + (a (i + t) - a i)) := by
      apply Finset.sum_congr rfl
      intro t ht
      have hai : a i ≤ a (i + t) := hmono (by omega)
      omega
    _ = (∑ _t ∈ Finset.range r, a i) +
          ∑ t ∈ Finset.range r, (a (i + t) - a i) := by
      rw [Finset.sum_add_distrib]
    _ = r * a i + blockError a i r := by
      simp [blockError]

/-- Interior starts in one class whose block error is at most `T`. -/
def goodClass (a : ℕ → ℕ) (n k T q : ℕ) : Finset ℕ :=
  (classInterior (fun i ↦ adaptiveLength n (a i)) k q).filter
    (fun i ↦ blockError a i q ≤ T)

/-- The union of good starts over adaptive lengths `1,...,R`. -/
def goodStarts (a : ℕ → ℕ) (n k R T : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).biUnion (goodClass a n k T)

theorem classInterior_block_in_class
    (rfun : ℕ → ℕ) (k q i t : ℕ)
    (hanti :
      ∀ ⦃x⦄, x < k → ∀ ⦃y⦄, y < k → x ≤ y → rfun y ≤ rfun x)
    (hi : i ∈ classInterior rfun k q)
    (ht : t < q) :
    i + t < k ∧ rfun (i + t) = q := by
  have hiClass : i ∈ lengthClass rfun k q :=
    (Finset.mem_filter.mp hi).1
  have hnear :
      i + q - 1 ≤ maxOrZero (lengthClass rfun k q) :=
    (Finset.mem_filter.mp hi).2
  have hnb : i ∉ classBoundary rfun k q := by
    intro hib
    have hfar := (Finset.mem_filter.mp hib).2
    omega
  exact retained_block_in_class rfun k q i t hanti hiClass hnb ht

/--
Every start is good, small-valued, a class-boundary exception, or a
large-error exception.
-/
theorem goodStarts_cover
    (a : ℕ → ℕ) (n k R T : ℕ)
    (hn : 0 < n)
    (hpos : ∀ i < k, 0 < a i) :
    Finset.range k ⊆
      goodStarts a n k R T ∪
        smallStarts a n k R ∪
        boundaryStarts (fun i ↦ adaptiveLength n (a i)) k R ∪
        badStarts a n k R T := by
  intro i hik
  simp only [Finset.mem_union]
  have hik' : i < k := Finset.mem_range.mp hik
  let q := adaptiveLength n (a i)
  have hq : 0 < q := adaptiveLength_pos n (a i) hn (hpos i hik')
  by_cases hsmall : R < q
  · have hmem : i ∈ smallStarts a n k R :=
      Finset.mem_filter.mpr ⟨hik, by simpa [q] using hsmall⟩
    exact Or.inl (Or.inl (Or.inr hmem))
  · have hqR : q ≤ R := by omega
    have hqIcc : q ∈ Finset.Icc 1 R :=
      Finset.mem_Icc.mpr ⟨by omega, hqR⟩
    have hiClass :
        i ∈ lengthClass (fun j ↦ adaptiveLength n (a j)) k q :=
      Finset.mem_filter.mpr ⟨hik, rfl⟩
    by_cases hboundary :
        maxOrZero (lengthClass (fun j ↦ adaptiveLength n (a j)) k q) <
          i + q - 1
    · have hmem :
          i ∈ boundaryStarts (fun j ↦ adaptiveLength n (a j)) k R := by
        apply Finset.mem_biUnion.mpr
        exact ⟨q, hqIcc, Finset.mem_filter.mpr ⟨hiClass, hboundary⟩⟩
      exact Or.inl (Or.inr hmem)
    · have hinterior :
          i ∈ classInterior (fun j ↦ adaptiveLength n (a j)) k q :=
        Finset.mem_filter.mpr ⟨hiClass, by omega⟩
      by_cases hgood : blockError a i q ≤ T
      · have hmem : i ∈ goodStarts a n k R T := by
          apply Finset.mem_biUnion.mpr
          exact ⟨q, hqIcc, Finset.mem_filter.mpr ⟨hinterior, hgood⟩⟩
        exact Or.inl (Or.inl (Or.inl hmem))
      · have hbad : T < blockError a i q := by omega
        have hq2 : 2 ≤ q := by
          by_contra h
          have hq1 : q = 1 := by omega
          have herr0 : blockError a i q = 0 := by
            rw [hq1]
            simp [blockError]
          omega
        have hqBad : q ∈ Finset.Icc 2 R :=
          Finset.mem_Icc.mpr ⟨hq2, hqR⟩
        have hmem : i ∈ badStarts a n k R T := by
          apply Finset.mem_biUnion.mpr
          exact ⟨q, hqBad, Finset.mem_filter.mpr ⟨hinterior, hbad⟩⟩
        exact Or.inr hmem

theorem goodStarts_blockSum_inj
    (a : ℕ → ℕ) (n k R T : ℕ)
    (hmono : Monotone a)
    (hpos : ∀ i < k, 0 < a i)
    (hdistinct : HasDistinctBlockSums a k) :
    Set.InjOn
      (fun i ↦ natBlockSum a i (adaptiveLength n (a i)))
      (goodStarts a n k R T) := by
  let rfun : ℕ → ℕ := fun i ↦ adaptiveLength n (a i)
  have hanti :
      ∀ ⦃x⦄, x < k → ∀ ⦃y⦄, y < k → x ≤ y → rfun y ≤ rfun x := by
    intro x hx y hy hxy
    exact adaptiveLength_antitone n (a x) (a y) (hpos x hx) (hmono hxy)
  intro i hi j hj hsum
  have hi' : i ∈ goodStarts a n k R T := hi
  have hj' : j ∈ goodStarts a n k R T := hj
  rcases Finset.mem_biUnion.mp hi' with ⟨qi, hqiR, higi⟩
  rcases Finset.mem_biUnion.mp hj' with ⟨qj, hqjR, higj⟩
  have hiInterior :
      i ∈ classInterior rfun k qi := (Finset.mem_filter.mp higi).1
  have hjInterior :
      j ∈ classInterior rfun k qj := (Finset.mem_filter.mp higj).1
  have hri : rfun i = qi :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hiInterior).1).2
  have hrj : rfun j = qj :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hjInterior).1).2
  have hqipos : 0 < qi := by
    have := (Finset.mem_Icc.mp hqiR).1
    omega
  have hqjpos : 0 < qj := by
    have := (Finset.mem_Icc.mp hqjR).1
    omega
  have hiLast :=
    classInterior_block_in_class rfun k qi i (qi - 1) hanti hiInterior
      (by omega)
  have hjLast :=
    classInterior_block_in_class rfun k qj j (qj - 1) hanti hjInterior
      (by omega)
  have hiValid : i + qi ≤ k := by omega
  have hjValid : j + qj ≤ k := by omega
  have hpairs : (i, qi) = (j, qj) := by
    apply hdistinct
    · exact ⟨hqipos, hiValid⟩
    · exact ⟨hqjpos, hjValid⟩
    · simpa [rfun, hri, hrj] using hsum
  exact congrArg Prod.fst hpairs

theorem goodStarts_blockSum_mem
    (a : ℕ → ℕ) (n k R T i : ℕ)
    (hmono : Monotone a)
    (hpos : ∀ i < k, 0 < a i)
    (hupper : ∀ i < k, a i ≤ n)
    (hi : i ∈ goodStarts a n k R T) :
    (n + 1) / 2 ≤ natBlockSum a i (adaptiveLength n (a i)) ∧
      natBlockSum a i (adaptiveLength n (a i)) ≤ n + T := by
  rcases Finset.mem_biUnion.mp hi with ⟨q, hqR, hiGood⟩
  have hiInterior :
      i ∈ classInterior (fun j ↦ adaptiveLength n (a j)) k q :=
    (Finset.mem_filter.mp hiGood).1
  have herror : blockError a i q ≤ T :=
    (Finset.mem_filter.mp hiGood).2
  have hiClass := (Finset.mem_filter.mp hiInterior).1
  have hiData := Finset.mem_filter.mp hiClass
  have hik : i < k := Finset.mem_range.mp hiData.1
  have hri : adaptiveLength n (a i) = q := hiData.2
  have haiPos : 0 < a i := hpos i hik
  have hbaseLower : (n + 1) / 2 ≤ q * a i := by
    have hlower := adaptiveLength_lower n (a i) haiPos
    rw [hri] at hlower
    have hceil : n ⌈/⌉ (2 : ℕ) ≤ q * a i := by
      rw [ceilDiv_le_iff_le_mul (by omega)]
      rw [show 2 * (q * a i) = 2 * a i * q by ac_rfl]
      exact hlower
    simpa [Nat.ceilDiv_eq_add_pred_div] using hceil
  have hbaseUpper : q * a i ≤ n := by
    rw [← hri]
    exact adaptiveLength_mul_le n (a i) haiPos (hupper i hik)
  have hsum :
      natBlockSum a i q = q * a i + blockError a i q :=
    natBlockSum_eq a i q hmono
  rw [hri]
  rw [hsum]
  exact
    ⟨hbaseLower.trans (Nat.le_add_right _ _),
      Nat.add_le_add hbaseUpper herror⟩

/--
Extend a finite sequence by the ambient upper bound. Under the usual range
hypotheses this is monotone and agrees with the original sequence before `k`.
-/
def extendFin (a : Fin k → ℕ) (n : ℕ) : ℕ → ℕ :=
  fun i ↦ if h : i < k then a ⟨i, h⟩ else n

theorem extendFin_apply_lt (a : Fin k → ℕ) (n i : ℕ) (hi : i < k) :
    extendFin a n i = a ⟨i, hi⟩ := by
  simp [extendFin, hi]

theorem extendFin_monotone
    (a : Fin k → ℕ) (n : ℕ)
    (hmono : Monotone a)
    (hupper : ∀ i, a i ≤ n) :
    Monotone (extendFin a n) := by
  intro i j hij
  by_cases hi : i < k
  · by_cases hj : j < k
    · rw [extendFin_apply_lt a n i hi, extendFin_apply_lt a n j hj]
      exact hmono (by simpa using hij)
    · rw [extendFin_apply_lt a n i hi]
      simp [extendFin, hj]
      exact hupper ⟨i, hi⟩
  · have hj : ¬j < k := by omega
    simp [extendFin, hi, hj]

theorem extendFin_pos
    (a : Fin k → ℕ) (n : ℕ)
    (hpos : ∀ i, 0 < a i) :
    ∀ i < k, 0 < extendFin a n i := by
  intro i hi
  rw [extendFin_apply_lt a n i hi]
  exact hpos ⟨i, hi⟩

theorem extendFin_upper
    (a : Fin k → ℕ) (n : ℕ)
    (hupper : ∀ i, a i ≤ n) :
    ∀ i < k, extendFin a n i ≤ n := by
  intro i hi
  rw [extendFin_apply_lt a n i hi]
  exact hupper ⟨i, hi⟩

theorem extendFin_injOn
    (a : Fin k → ℕ) (n : ℕ)
    (hinj : Function.Injective a) :
    Set.InjOn (extendFin a n) (Finset.range k : Set ℕ) := by
  intro i hi j hj heq
  have hik : i < k := Finset.mem_range.mp hi
  have hjk : j < k := Finset.mem_range.mp hj
  rw [extendFin_apply_lt a n i hik, extendFin_apply_lt a n j hjk] at heq
  have hfin : (⟨i, hik⟩ : Fin k) = ⟨j, hjk⟩ := hinj heq
  exact congrArg Fin.val hfin

/-- The finite interval block `[i,i+r)` represented inside `Fin k`. -/
def finBlock (k i r : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun x ↦ i ≤ x.val ∧ x.val < i + r)

theorem finBlock_ordConnected (k i r : ℕ) :
    (finBlock k i r : Set (Fin k)).OrdConnected := by
  constructor
  intro x hx y hy z hz
  have hx' : x ∈ finBlock k i r := hx
  have hy' : y ∈ finBlock k i r := hy
  rcases (Finset.mem_filter.mp hx').2 with ⟨hix, hxr⟩
  rcases (Finset.mem_filter.mp hy').2 with ⟨hiy, hyr⟩
  rcases hz with ⟨hxz, hzy⟩
  have hxzv : x.val ≤ z.val := by simpa using hxz
  have hzyv : z.val ≤ y.val := by simpa using hzy
  have hz' : z ∈ finBlock k i r := by
    apply Finset.mem_filter.mpr
    exact
      ⟨Finset.mem_univ z,
        ⟨hix.trans hxzv, hzyv.trans_lt hyr⟩⟩
  exact hz'

theorem natBlockSum_extendFin
    (a : Fin k → ℕ) (n i r : ℕ)
    (hvalid : i + r ≤ k) :
    natBlockSum (extendFin a n) i r =
      ∑ x ∈ finBlock k i r, a x := by
  unfold natBlockSum
  apply Finset.sum_bij
      (fun t ht ↦ (⟨i + t, by
        have htr := Finset.mem_range.mp ht
        omega⟩ : Fin k))
  · intro t ht
    have htr := Finset.mem_range.mp ht
    simp only [finBlock, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by omega, by omega⟩
  · intro t ht u hu heq
    exact Nat.add_left_cancel (congrArg Fin.val heq)
  · intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    let t := x.val - i
    have ht : t ∈ Finset.range r := by
      apply Finset.mem_range.mpr
      dsimp [t]
      omega
    refine ⟨t, ht, ?_⟩
    apply Fin.ext
    dsimp [t]
    omega
  · intro t ht
    have htr := Finset.mem_range.mp ht
    rw [extendFin_apply_lt a n (i + t) (by omega)]

theorem finBlock_eq_imp
    (i r j s k : ℕ)
    (hr : 0 < r) (hs : 0 < s)
    (hri : i + r ≤ k) (hsj : j + s ≤ k)
    (heq : finBlock k i r = finBlock k j s) :
    (i, r) = (j, s) := by
  have hik : i < k := by omega
  have hjk : j < k := by omega
  let xi : Fin k := ⟨i, hik⟩
  let xj : Fin k := ⟨j, hjk⟩
  have hxi : xi ∈ finBlock k i r := by
    apply Finset.mem_filter.mpr
    exact
      ⟨Finset.mem_univ _,
        ⟨by simp [xi], by simp [xi]; omega⟩⟩
  have hxj : xj ∈ finBlock k j s := by
    apply Finset.mem_filter.mpr
    exact
      ⟨Finset.mem_univ _,
        ⟨by simp [xj], by simp [xj]; omega⟩⟩
  have hji : j ≤ i := by
    have := (Finset.mem_filter.mp (heq ▸ hxi)).2.1
    simpa [xi] using this
  have hij : i ≤ j := by
    have := (Finset.mem_filter.mp (heq.symm ▸ hxj)).2.1
    simpa [xj] using this
  have hijEq : i = j := hij.antisymm hji
  have hlastI : i + r - 1 < k := by omega
  have hlastJ : j + s - 1 < k := by omega
  let yi : Fin k := ⟨i + r - 1, hlastI⟩
  let yj : Fin k := ⟨j + s - 1, hlastJ⟩
  have hyi : yi ∈ finBlock k i r := by
    apply Finset.mem_filter.mpr
    exact
      ⟨Finset.mem_univ _,
        ⟨by simp [yi]; omega, by simp [yi]; omega⟩⟩
  have hyj : yj ∈ finBlock k j s := by
    apply Finset.mem_filter.mpr
    exact
      ⟨Finset.mem_univ _,
        ⟨by simp [yj]; omega, by simp [yj]; omega⟩⟩
  have hrs : r ≤ s := by
    have := (Finset.mem_filter.mp (heq ▸ hyi)).2.2
    simp [yi] at this
    omega
  have hsr : s ≤ r := by
    have := (Finset.mem_filter.mp (heq.symm ▸ hyj)).2.2
    simp [yj] at this
    omega
  have hrsEq : r = s := hrs.antisymm hsr
  simp [hijEq, hrsEq]

/--
The order-connected-finset formulation used in the official statement implies
the explicit start/length formulation used by the adaptive proof.
-/
theorem hasDistinctBlockSums_extendFin
    (a : Fin k → ℕ) (n : ℕ)
    (hdistinct : HasDistinctSums a) :
    HasDistinctBlockSums (extendFin a n) k := by
  intro p hp q hq hsum
  rcases p with ⟨i, r⟩
  rcases q with ⟨j, s⟩
  change 0 < r ∧ i + r ≤ k at hp
  change 0 < s ∧ j + s ≤ k at hq
  have hsum' :
      (∑ x ∈ finBlock k i r, a x) =
        ∑ x ∈ finBlock k j s, a x := by
    rw [← natBlockSum_extendFin a n i r hp.2,
      ← natBlockSum_extendFin a n j s hq.2]
    exact hsum
  have hblocks : finBlock k i r = finBlock k j s :=
    hdistinct (finBlock_ordConnected k i r)
      (finBlock_ordConnected k j s) hsum'
  exact finBlock_eq_imp i r j s k hp.1 hq.1 hp.2 hq.2 hblocks

/-- Convert a positive integer-valued finite sequence to naturals. -/
def intFinToNat (a : Fin k → ℤ) : Fin k → ℕ :=
  fun i ↦ (a i).toNat

theorem intFinToNat_pos
    (a : Fin k → ℤ)
    (hpos : ∀ i, (1 : ℤ) ≤ a i) :
    ∀ i, 0 < intFinToNat a i := by
  intro i
  apply Nat.pos_of_ne_zero
  intro hz
  have hai0 : a i ≤ 0 := Int.toNat_eq_zero.mp hz
  have hai1 := hpos i
  omega

theorem intFinToNat_upper
    (a : Fin k → ℤ) (n : ℕ)
    (hupper : ∀ i, a i ≤ (n : ℤ)) :
    ∀ i, intFinToNat a i ≤ n := by
  intro i
  exact (Int.toNat_le).mpr (by simpa using hupper i)

theorem intFinToNat_strictMono
    (a : Fin k → ℤ)
    (hpos : ∀ i, (1 : ℤ) ≤ a i)
    (hmono : StrictMono a) :
    StrictMono (intFinToNat a) := by
  intro i j hij
  have hai0 : 0 ≤ a i := by
    have := hpos i
    omega
  have haj0 : 0 ≤ a j := by
    have := hpos j
    omega
  apply (Int.toNat_lt hai0).2
  change a i < ((a j).toNat : ℤ)
  rw [Int.ofNat_toNat, max_eq_left haj0]
  exact hmono hij

theorem hasDistinctSums_intFinToNat
    (a : Fin k → ℤ)
    (hpos : ∀ i, (1 : ℤ) ≤ a i)
    (hdistinct : HasDistinctSums a) :
    HasDistinctSums (intFinToNat a) := by
  intro J hJ K hK hsum
  apply hdistinct hJ hK
  have hcastJ :
      (∑ x ∈ J, (intFinToNat a x : ℤ)) = ∑ x ∈ J, a x := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [intFinToNat]
    have hxpos := hpos x
    rw [Int.toNat_of_nonneg (by omega)]
  have hcastK :
      (∑ x ∈ K, (intFinToNat a x : ℤ)) = ∑ x ∈ K, a x := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [intFinToNat]
    have hxpos := hpos x
    rw [Int.toNat_of_nonneg (by omega)]
  have hcast := congrArg (fun z : ℕ ↦ (z : ℤ)) hsum
  simp only [Nat.cast_sum] at hcast
  rw [hcastJ, hcastK] at hcast
  exact hcast

/--
The finite data produced by the adaptive-block construction.

The inequalities are written with denominators cleared. This makes all
rounding terms explicit and keeps the final theorem over `Nat`.
-/
structure AdaptivePackingCertificate
    (α : Type*) [DecidableEq α] (n k R T : ℕ) where
  indices : Finset α
  good : Finset α
  small : Finset α
  boundary : Finset α
  bad : Finset α
  blockSum : α → ℕ
  k_le_card_indices : k ≤ indices.card
  cover : indices ⊆ good ∪ small ∪ boundary ∪ bad
  blockSum_inj : Set.InjOn blockSum good
  blockSum_mem_interval :
    ∀ i ∈ good, (n + 1) / 2 ≤ blockSum i ∧ blockSum i ≤ n + T
  small_bound : small.card * (2 * R) ≤ n + 2 * R
  boundary_bound : boundary.card * 2 ≤ R * (R - 1)
  bad_bound : bad.card * (4 * T) ≤ n * (R - 1)

/--
Construct the adaptive packing certificate from an actual finite monotone
sequence with distinct positive values and distinct consecutive-block sums.
-/
def adaptivePackingCertificate_of_sequence
    (a : ℕ → ℕ) (n k R T : ℕ)
    (hn : 0 < n) (hR : 0 < R)
    (hmono : Monotone a)
    (hpos : ∀ i < k, 0 < a i)
    (hupper : ∀ i < k, a i ≤ n)
    (hinj : Set.InjOn a (Finset.range k : Set ℕ))
    (hdistinct : HasDistinctBlockSums a k) :
    AdaptivePackingCertificate ℕ n k R T := by
  let rfun : ℕ → ℕ := fun i ↦ adaptiveLength n (a i)
  let bsum : ℕ → ℕ := fun i ↦ natBlockSum a i (rfun i)
  refine
    { indices := Finset.range k
      good := goodStarts a n k R T
      small := smallStarts a n k R
      boundary := boundaryStarts rfun k R
      bad := badStarts a n k R T
      blockSum := bsum
      k_le_card_indices := by simp
      cover := ?_
      blockSum_inj := ?_
      blockSum_mem_interval := ?_
      small_bound := ?_
      boundary_bound := ?_
      bad_bound := ?_ }
  · exact goodStarts_cover a n k R T hn hpos
  · exact goodStarts_blockSum_inj a n k R T hmono hpos hdistinct
  · intro i hi
    exact goodStarts_blockSum_mem a n k R T i hmono hpos hupper hi
  · exact smallStarts_card_mul_le a n k R hR hpos hinj
  · have hcard := boundaryStarts_card_le rfun k R
    calc
      (boundaryStarts rfun k R).card * 2 ≤
          (R * (R - 1) / 2) * 2 :=
        Nat.mul_le_mul_right 2 hcard
      _ = R * (R - 1) := two_mul_triangular R
  · exact badStarts_card_mul_le a n k R T hn hmono hpos

/--
Injective good block sums fit into an interval of length
`n + T + 1 - (n + 1) / 2`.
-/
theorem good_card_le_interval
    {α : Type*} [DecidableEq α] {n k R T : ℕ}
    (c : AdaptivePackingCertificate α n k R T) :
    c.good.card ≤ n + T + 1 - (n + 1) / 2 := by
  have hmaps :
      Set.MapsTo c.blockSum (c.good : Set α)
        (Finset.Icc ((n + 1) / 2) (n + T) : Set ℕ) := by
    intro i hi
    simpa only [Finset.coe_Icc, Set.mem_Icc] using
      c.blockSum_mem_interval i hi
  have hcard :
      c.good.card ≤ (Finset.Icc ((n + 1) / 2) (n + T)).card :=
    Finset.card_le_card_of_injOn c.blockSum hmaps c.blockSum_inj
  simpa only [Nat.card_Icc] using hcard

/--
The good starts alone satisfy the denominator-cleared half-density bound.
-/
theorem twice_good_card_le
    {α : Type*} [DecidableEq α] {n k R T : ℕ}
    (c : AdaptivePackingCertificate α n k R T) :
    c.good.card * 2 ≤ n + 2 * T + 2 := by
  have h := good_card_le_interval c
  omega

/--
The four-way cover bounds the number of starts by the sum of the four
cardinalities. The sets need not be disjoint.
-/
theorem card_indices_le_exceptional_sum
    {α : Type*} [DecidableEq α] {n k R T : ℕ}
    (c : AdaptivePackingCertificate α n k R T) :
    c.indices.card ≤
      c.good.card + c.small.card + c.boundary.card + c.bad.card := by
  have hcover :
      c.indices.card ≤ (c.good ∪ c.small ∪ c.boundary ∪ c.bad).card :=
    Finset.card_le_card c.cover
  have h₁ := Finset.card_union_le c.good c.small
  have h₂ := Finset.card_union_le (c.good ∪ c.small) c.boundary
  have h₃ :=
    Finset.card_union_le (c.good ∪ c.small ∪ c.boundary) c.bad
  omega

/--
Exact finite adaptive-packing bound.

This is the division-bearing form of

`k ≤ n/2 + T + n/(2R) + R(R-1)/2 + n(R-1)/(4T) + rounding`,

with every rounding term retained. Choosing `R` on the scale `n^(1/3)` and
`T` on the scale `n^(2/3)` gives the bound
`k ≤ n/2 + O(n^(2/3))`.
-/
theorem finite_bound_of_adaptive_certificate
    {α : Type*} [DecidableEq α] {n k R T : ℕ}
    (hR : 0 < R) (hT : 0 < T)
    (c : AdaptivePackingCertificate α n k R T) :
    k ≤
      (n + 2 * T + 2) / 2 +
      (n + 2 * R) / (2 * R) +
      (R * (R - 1)) / 2 +
      (n * (R - 1)) / (4 * T) := by
  have hk := c.k_le_card_indices
  have hcover := card_indices_le_exceptional_sum c
  have hgood :
      c.good.card ≤ (n + 2 * T + 2) / 2 :=
    (Nat.le_div_iff_mul_le (by omega)).2 (twice_good_card_le c)
  have hsmall :
      c.small.card ≤ (n + 2 * R) / (2 * R) :=
    (Nat.le_div_iff_mul_le (by omega)).2 c.small_bound
  have hboundary :
      c.boundary.card ≤ (R * (R - 1)) / 2 :=
    (Nat.le_div_iff_mul_le (by omega)).2 c.boundary_bound
  have hbad :
      c.bad.card ≤ (n * (R - 1)) / (4 * T) :=
    (Nat.le_div_iff_mul_le (by omega)).2 c.bad_bound
  omega

/--
The unconditional finite adaptive bound for a natural-valued sequence.

The hypotheses describe the first `k` entries of `a`: they are positive,
bounded by `n`, monotone and injective, and all contained positive-length
block sums are distinct.
-/
theorem finite_adaptive_bound
    (a : ℕ → ℕ) (n k R T : ℕ)
    (hn : 0 < n) (hR : 0 < R) (hT : 0 < T)
    (hmono : Monotone a)
    (hpos : ∀ i < k, 0 < a i)
    (hupper : ∀ i < k, a i ≤ n)
    (hinj : Set.InjOn a (Finset.range k : Set ℕ))
    (hdistinct : HasDistinctBlockSums a k) :
    k ≤
      (n + 2 * T + 2) / 2 +
      (n + 2 * R) / (2 * R) +
      (R * (R - 1)) / 2 +
      (n * (R - 1)) / (4 * T) := by
  exact finite_bound_of_adaptive_certificate hR hT
    (adaptivePackingCertificate_of_sequence
      a n k R T hn hR hmono hpos hupper hinj hdistinct)

/--
Finite adaptive bound in the exact `Fin k`/order-connected-finset language of
Erdős Problem 357.
-/
theorem finite_adaptive_bound_fin
    (a : Fin k → ℕ) (n R T : ℕ)
    (hn : 0 < n) (hR : 0 < R) (hT : 0 < T)
    (hmono : StrictMono a)
    (hpos : ∀ i, 0 < a i)
    (hupper : ∀ i, a i ≤ n)
    (hdistinct : HasDistinctSums a) :
    k ≤
      (n + 2 * T + 2) / 2 +
      (n + 2 * R) / (2 * R) +
      (R * (R - 1)) / 2 +
      (n * (R - 1)) / (4 * T) := by
  exact finite_adaptive_bound (extendFin a n) n k R T
    hn hR hT
    (extendFin_monotone a n hmono.monotone hupper)
    (extendFin_pos a n hpos)
    (extendFin_upper a n hupper)
    (extendFin_injOn a n hmono.injective)
    (hasDistinctBlockSums_extendFin a n hdistinct)

/--
Finite adaptive bound in the exact integer-valued formulation used by the
official `f(n)` definition.
-/
theorem finite_adaptive_bound_int
    (a : Fin k → ℤ) (n R T : ℕ)
    (hn : 0 < n) (hR : 0 < R) (hT : 0 < T)
    (hrange : Set.range a ⊆ Set.Icc 1 n)
    (hmono : StrictMono a)
    (hdistinct : HasDistinctSums a) :
    k ≤
      (n + 2 * T + 2) / 2 +
      (n + 2 * R) / (2 * R) +
      (R * (R - 1)) / 2 +
      (n * (R - 1)) / (4 * T) := by
  have hpos : ∀ i, (1 : ℤ) ≤ a i := by
    intro i
    exact (hrange ⟨i, rfl⟩).1
  have hupper : ∀ i, a i ≤ (n : ℤ) := by
    intro i
    exact (hrange ⟨i, rfl⟩).2
  exact finite_adaptive_bound_fin (intFinToNat a) n R T
    hn hR hT
    (intFinToNat_strictMono a hpos hmono)
    (intFinToNat_pos a hpos)
    (intFinToNat_upper a n hupper)
    (hasDistinctSums_intFinToNat a hpos hdistinct)

/--
An explicit cube-scale corollary, with no asymptotic notation.

If `n ≤ m³`, choosing adaptive cutoff `R = m` and error threshold `T = m²`
gives `2k ≤ n + 8m² + 4`. Thus the certificate theorem has the advertised
`n / 2 + O(n^(2/3))` scale.
-/
theorem cube_scale_bound_of_adaptive_certificate
    {α : Type*} [DecidableEq α] {n k m : ℕ}
    (hm : 0 < m) (hn : n ≤ m * m * m)
    (c : AdaptivePackingCertificate α n k m (m * m)) :
    k * 2 ≤ n + 8 * (m * m) + 4 := by
  have hk : k ≤ c.indices.card := c.k_le_card_indices
  have hcover :
      c.indices.card ≤
        c.good.card + c.small.card + c.boundary.card + c.bad.card :=
    card_indices_le_exceptional_sum c
  have hgood :
      c.good.card * 2 ≤ n + 2 * (m * m) + 2 :=
    twice_good_card_le c
  have hsmall : c.small.card ≤ m * m + 1 := by
    by_contra h
    have hlo : m * m + 2 ≤ c.small.card := by omega
    have hscale :
        (m * m + 2) * (2 * m) ≤ c.small.card * (2 * m) :=
      Nat.mul_le_mul_right (2 * m) hlo
    have hupper : n + 2 * m ≤ m * m * m + 2 * m :=
      Nat.add_le_add_right hn (2 * m)
    have hchain :
        (m * m + 2) * (2 * m) ≤ m * m * m + 2 * m :=
      hscale.trans (c.small_bound.trans hupper)
    have hbasepos : 0 < m * m * m + 2 * m := by omega
    have hlt :
        m * m * m + 2 * m < (m * m + 2) * (2 * m) := by
      calc
        m * m * m + 2 * m <
            (m * m * m + 2 * m) + (m * m * m + 2 * m) := by
              omega
        _ = (m * m + 2) * (2 * m) := by
          simp only [two_mul, Nat.add_mul, Nat.mul_add]
    exact (Nat.not_lt_of_ge hchain) hlt
  have hboundary : c.boundary.card ≤ m * m := by
    have hc : c.boundary.card * 2 ≤ m * (m - 1) :=
      c.boundary_bound
    have hprod : m * (m - 1) ≤ m * m :=
      Nat.mul_le_mul_left m (Nat.sub_le m 1)
    omega
  have hbad : c.bad.card ≤ m * m := by
    by_contra h
    have hlo : m * m + 1 ≤ c.bad.card := by omega
    have hscale :
        (m * m + 1) * (4 * (m * m)) ≤
          c.bad.card * (4 * (m * m)) :=
      Nat.mul_le_mul_right (4 * (m * m)) hlo
    have hrhs : n * (m - 1) ≤ (m * m * m) * m :=
      Nat.mul_le_mul hn (Nat.sub_le m 1)
    have hchain :
        (m * m + 1) * (4 * (m * m)) ≤ (m * m * m) * m :=
      hscale.trans (c.bad_bound.trans hrhs)
    have hm2pos : 0 < m * m := Nat.mul_pos hm hm
    have hfirst :
        (m * m) * (m * m) < (m * m + 1) * (m * m) :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self (m * m)) hm2pos
    have hfactor : m * m ≤ 4 * (m * m) := by omega
    have hsecond :
        (m * m + 1) * (m * m) ≤
          (m * m + 1) * (4 * (m * m)) :=
      Nat.mul_le_mul_left (m * m + 1) hfactor
    have hlt :
        (m * m * m) * m < (m * m + 1) * (4 * (m * m)) := by
      rw [show (m * m * m) * m = (m * m) * (m * m) by ac_rfl]
      exact hfirst.trans_le hsecond
    exact (Nat.not_lt_of_ge hchain) hlt
  omega

/--
Concrete `n/2 + O(n^(2/3))`-scale consequence for an actual sequence.
-/
theorem cube_scale_adaptive_bound
    (a : ℕ → ℕ) (n k m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hnm : n ≤ m * m * m)
    (hmono : Monotone a)
    (hpos : ∀ i < k, 0 < a i)
    (hupper : ∀ i < k, a i ≤ n)
    (hinj : Set.InjOn a (Finset.range k : Set ℕ))
    (hdistinct : HasDistinctBlockSums a k) :
    k * 2 ≤ n + 8 * (m * m) + 4 := by
  exact cube_scale_bound_of_adaptive_certificate hm hnm
    (adaptivePackingCertificate_of_sequence
      a n k m (m * m) hn hm hmono hpos hupper hinj hdistinct)

/--
The explicit cube-scale bound for a finite sequence in the exact problem
language.
-/
theorem cube_scale_adaptive_bound_fin
    (a : Fin k → ℕ) (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hnm : n ≤ m * m * m)
    (hmono : StrictMono a)
    (hpos : ∀ i, 0 < a i)
    (hupper : ∀ i, a i ≤ n)
    (hdistinct : HasDistinctSums a) :
    k * 2 ≤ n + 8 * (m * m) + 4 := by
  exact cube_scale_adaptive_bound (extendFin a n) n k m
    hn hm hnm
    (extendFin_monotone a n hmono.monotone hupper)
    (extendFin_pos a n hpos)
    (extendFin_upper a n hupper)
    (extendFin_injOn a n hmono.injective)
    (hasDistinctBlockSums_extendFin a n hdistinct)

/--
Cube-scale bound in the exact integer-valued formulation used by the official
problem statement.
-/
theorem cube_scale_adaptive_bound_int
    (a : Fin k → ℤ) (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hnm : n ≤ m * m * m)
    (hrange : Set.range a ⊆ Set.Icc 1 n)
    (hmono : StrictMono a)
    (hdistinct : HasDistinctSums a) :
    k * 2 ≤ n + 8 * (m * m) + 4 := by
  have hpos : ∀ i, (1 : ℤ) ≤ a i := by
    intro i
    exact (hrange ⟨i, rfl⟩).1
  have hupper : ∀ i, a i ≤ (n : ℤ) := by
    intro i
    exact (hrange ⟨i, rfl⟩).2
  exact cube_scale_adaptive_bound_fin (intFinToNat a) n m
    hn hm hnm
    (intFinToNat_strictMono a hpos hmono)
    (intFinToNat_pos a hpos)
    (intFinToNat_upper a n hupper)
    (hasDistinctSums_intFinToNat a hpos hdistinct)

/--
Exact finite upper bound on the extremal function itself.
-/
theorem f357_finite_adaptive_bound
    (n R T : ℕ) (hn : 0 < n) (hR : 0 < R) (hT : 0 < T) :
    f357 n ≤
      (n + 2 * T + 2) / 2 +
      (n + 2 * R) / (2 * R) +
      (R * (R - 1)) / 2 +
      (n * (R - 1)) / (4 * T) := by
  apply csSup_le (f357_admissible_nonempty n)
  intro k hk
  rcases hk with ⟨a, hrange, hmono, hdistinct⟩
  exact finite_adaptive_bound_int a n R T
    hn hR hT hrange hmono hdistinct

/--
Explicit cube-scale upper bound on `f357`.
-/
theorem f357_cube_scale_bound
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hnm : n ≤ m * m * m) :
    f357 n * 2 ≤ n + 8 * (m * m) + 4 := by
  have hf :
      f357 n ≤ (n + 8 * (m * m) + 4) / 2 := by
    apply csSup_le (f357_admissible_nonempty n)
    intro k hk
    rcases hk with ⟨a, hrange, hmono, hdistinct⟩
    have hk2 := cube_scale_adaptive_bound_int a n m
      hn hm hnm hrange hmono hdistinct
    exact (Nat.le_div_iff_mul_le (by omega)).2 hk2
  exact (Nat.le_div_iff_mul_le (by omega)).1 hf

/--
Parameter-free exact version, using the least natural cube root from above.
-/
theorem f357_cubeCeil_bound (n : ℕ) (hn : 0 < n) :
    f357 n * 2 ≤
      n + 8 * (cubeCeil n * cubeCeil n) + 4 :=
  f357_cube_scale_bound n (cubeCeil n) hn
    (cubeCeil_pos n hn) (le_cubeCeil_cube n)

end Erdos357
