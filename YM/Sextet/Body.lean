import YM.SU5.Cordial.Scepter
import YM.SU5.Aria.Drape

/-!
# An exact width prescription for six mixed measurements

These are `Apron` marks with all four support tickets on the original resolution. We want
the ***same*** shift prescriptions and widths ALSO on every finer observation (below &
`Apron.throughMark`, `Apron.full_realizes`). Widths here are in physical length units in which
the control periods, smearing centers, selected-cluster heat times and radii `Spine.dew` are
measured; `printedHere` and `Apron.scenery` use **twice** these coordinates. Ticks are full.

This implements `F_Zi`, `A_Zi`, `a'_i`, `w_j^(i)` in `Macropositions`;
see also `SU5/Aria/Grotto.lean` for an earlier (different) width prescription.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Sods

def tickRound (D n : ℕ) : ℕ := ⌈(n:ℝ) / (D:ℝ)⌉₊

lemma tickRound_le {D : ℕ} (h : 0 < D) (n : ℕ) :
    n ≤ D * tickRound D n ∧ D * tickRound D n ≤ n + D := by
  have hd : 0 < (D:ℝ) := by exact_mod_cast h
  have u : (n:ℝ) ≤ (tickRound D n:ℝ)*D := (div_le_iff₀ hd).1 (Nat.le_ceil _)
  have v : (tickRound D n:ℝ)*D ≤ n+D := by
    rw [← le_div_iff₀ hd,add_div,div_self hd.ne']
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ (n:ℝ)/D)).le
  rw [mul_comm D]
  constructor <;> first | exact_mod_cast u | exact_mod_cast v

variable (P : Spine) (Z : Lead.Clan) (s n : ℕ)
local notation "K" => P.calibration
local notation "B" => P.par.block
local notation "D" => (16*(B).val : ℕ)
local notation "R" => ruler B
local notation "ℓ" => P.calibration.ℓ
local notation "M" => timeMesh P.par

def timeJump (n : ℕ) := tickRound D n

lemma timeJump_pos {n : ℕ} (h : 0 < n) : 0 < P.timeJump n := by
  have : 0 < (B).val := (B).property
  exact Nat.ceil_pos.mpr (by positivity)

/-- Equation `timeInc`: both summands with the signs at the actual resolution.
Advances `Apron.full` and grid shifts `chartAll` are on *this* test. -/
def timeDifference : P.Test :=
  P.stockS Z (P.flash n) - P.shifts 3 (P.timeJump n) (P.stockS Z (P.flash n))

def timeSupports :=
  (P.flash n).patio ∪ plow K 3 (P.timeJump n) (P.flash n).patio

lemma timeDifference_local : P.timeDifference Z n ∈ bay K (P.timeSupports n) true :=
  sub_mem
    (tallerBay K (P.flash n).patio true Finset.subset_union_left (P.visibility Z n))
    (tallerBay K _ true Finset.subset_union_right
      (P.shifts_support 3 _ _ (P.visibility Z n)))

lemma timeDifference_singlet : P.timeDifference Z n ∈ enclave K :=
  sub_mem (P.celebrity (flourish _ _))
    (P.shifts_keep _ _ (P.celebrity (flourish _ _)))

def tickBudget := Function.update (fun _ : Axis => ℓ+1) 3
    (1 + tickRound D (2*(ℓ+2*n)+1 + D * P.timeJump n + ℓ))

lemma tickBudget_pos (i : Axis) : 0 < P.tickBudget n i := by
  unfold tickBudget; by_cases h : i=3
  · rw [h, Function.update_self]; omega
  rw [Function.update_of_ne h]; omega

lemma flash_bounds (i : Cover) (h : i ∈ (P.flash n).patio) :
    2*((ℓ:ℤ)+n)+1 ≤ i 3 ∧ i 3 ≤ 2*((ℓ:ℤ)+2*n)+1 := by
  obtain ⟨t, ht, rfl⟩ := Cube.range_leg _ (posDir 3) (2*n) i (List.mem_toFinset.mp h)
  simp [flash,kernel0,nodeC]
  omega

private lemma ruler_eq_D : R = (D:ℤ) := by simp [ruler]

lemma timeSupports_upper :
    Between K 3 0 (R * P.tickBudget n (3:Axis)) (P.timeSupports n) := by
  have hc := (tickRound_le (show 0<D by positivity)
      (2*(ℓ+2*n)+1 + D * P.timeJump n + ℓ)).1
  have he : 2*((ℓ:ℤ)+2*n)+1 + R * P.timeJump n + ℓ ≤ R * (P.tickBudget n (3:Axis)) := by
    unfold tickBudget
    rw [ruler_eq_D]
    let A:ℕ:=D
    have hh:2*(ℓ+2*n)+1 + A * P.timeJump n + ℓ ≤ A*(P.tickBudget n 3):= by
      unfold tickBudget
      rw [Function.update_self]
      exact hc.trans (Nat.mul_le_mul_left A (Nat.le_add_left ..))
    exact_mod_cast hh
  have hv : 0 ≤ R * (P.timeJump n:ℤ) := mul_nonneg (ruler_gene B).le (by positivity)
  intro i u
  rcases mem_union.mp u with h | h
  · have p := P.flash_bounds n i h
    omega
  obtain ⟨a,t,rfl⟩ := plow_stays _ _ _ _ h
  have ha := P.flash_bounds n a t
  rw [SlabMark.moves, if_pos rfl, show ruler (K).B=R from rfl]
  omega

lemma timeSupports_here : Tower.region 3 0 ℓ (P.timeSupports n) := fun i h =>
  (P.timeSupports_upper n i h).1

lemma timeSupports_width (j : Axis) :
    Between K j (-R * P.tickBudget n j) (R * P.tickBudget n j) (P.timeSupports n) := by
  by_cases e:j=3
  · subst j
    have hv : -R * P.tickBudget n (3:Axis) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (ruler_gene _).le) (by positivity)
    exact fun i h => let p:=P.timeSupports_upper n i h; ⟨(add_le_add_left hv _).trans p.1,p.2⟩
  intro i h
  have hv : (ℓ:ℤ)+1 ≤ R * ((ℓ:ℤ)+1) := le_mul_of_one_le_left (by positivity) (ruler_gene _)
  unfold tickBudget
  rw [Function.update_of_ne e, Nat.cast_add, Nat.cast_one, neg_mul]
  rcases mem_union.mp h with h | h
  · rw [P.flash_fixed j n i h e]; omega
  obtain ⟨a,t,rfl⟩ := plow_stays _ _ _ _ h
  rw [SlabMark.moves,if_neg e,P.flash_fixed j n a t e]
  omega

def macroBody : P.Apron :=
  ⟨s, P.tickBudget n, P.tickBudget_pos n, P.timeDifference Z n, P.timeSupports n,
    P.timeDifference_local Z n, P.timeDifference_singlet Z n, P.timeSupports_width n⟩

lemma timeDifference_birth : P.birthF 3 s (P.macroBody Z s n).F :=
  P.criteria 3 s (P.timeDifference_local Z n) (P.timeSupports_here n)
    (P.timeDifference_singlet Z n)

/-- Length of one **full** tick at any height. 8*B matter sites = 16*B gauge sites. -/
def macroTick : ℝ := mill M s

lemma macroTick_pos : 0 < P.macroTick s := mill_pos ..

lemma macroTick_null : Tendsto P.macroTick atTop (𝓝 0) := NNReal.tendsto_coe.mpr (vanishes M)

def transportWidth (j : Axis) : ℝ := bell M s (P.tickBudget n j)

lemma macroBody_width (j : Axis) : (P.macroBody Z s n).realWidth P j =
    P.transportWidth s n j := rfl

def advanceHeat : ℝ≥0 := whenly M s (P.timeJump n)

lemma advanceHeat_pos {n : ℕ} (h : 0<n) : 0 < P.advanceHeat s n :=
  when_pos M s _ (P.timeJump_pos h)

private lemma budget_error_nat (d y : ℕ) (hd : 0 < d) :
    let p := 2*(y+2*n)+1 + d * tickRound d n + y
    let w := d * (1 + tickRound d p)
    5*n ≤ w ∧ w ≤ 5*n + (3*y+1 + 3*d) := by
  intro p w
  have hu := tickRound_le hd p
  have h := tickRound_le hd n
  unfold w; rw [_root_.mul_add,mul_one]
  have h' : 5*n ≤ p ∧ p ≤ 5*n + (3*y+1 + d) := by unfold p; omega
  omega

lemma budget_error :
    5*n ≤ D * P.tickBudget n 3 ∧
      D * P.tickBudget n 3 ≤ 5*n + (3*ℓ+1 + 3*D) := by
  unfold tickBudget; rw [Function.update_self]
  exact budget_error_nat n D ℓ (by positivity)

lemma bell_over_dew {n : ℕ} (p:0<n) (i : ℕ) :
    bell M s i / P.dew s n = (D * i : ℕ) / (2*(n:ℝ)) := by
  have hn := (P.dew_pos s p).ne'
  rw [show bell M s i= ((notch M s i):ℝ) from rfl, mintS .., mul_div_cancel_left₀ _ hn]
  · unfold crewB Heat.gaugeShift
    push_cast; ring
  exact p

private lemma ratio_bounds {F r:ℕ→ℕ} (h:StrictMono r) (p:∀ i, 0<r i) {d e:ℕ}
    (v:∀i, d*r i ≤ F i ∧ F i ≤ d*r i + e) :
    Tendsto (fun i=> (F i:ℝ)/(2*(r i:ℝ))) atTop (𝓝 ((d:ℝ)/2)) := by
  have hr : Tendsto (fun i=>2*(r i:ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp h.tendsto_atTop).const_mul_atTop (by norm_num)
  have hu : Tendsto (fun i=>(d:ℝ)/2+(e:ℝ)/(2*(r i:ℝ))) atTop (𝓝 ((d:ℝ)/2)) := by
    simpa only [add_zero] using tendsto_const_nhds.add (a:= (d:ℝ)/2)
      ((tendsto_const_nhds (x:= (e:ℝ))).div_atTop hr)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu ?_ ?_
  · intro i
    have h : (d:ℝ)*(r i:ℝ) ≤ (F i:ℝ) := by exact_mod_cast (v i).1
    have : 0<(r i:ℝ) := by exact_mod_cast p i
    rw [le_div_iff₀ (by positivity : 0<2*(r i:ℝ))]; linarith
  intro i
  have h : (F i:ℝ) ≤ (d:ℝ)*(r i:ℝ)+(e:ℝ) := by exact_mod_cast (v i).2
  have : 0<(r i:ℝ) := by exact_mod_cast p i
  rw [div_le_iff₀ (by positivity : 0<2*(r i:ℝ)),
      _root_.add_mul,div_mul_cancel₀ _ (by positivity : 2*(r i:ℝ) ≠ 0)]
  linarith

variable {P} {c r : ℕ → ℕ} (H : Launch P c r)
include H
local notation "ρ" i:max => P.dew (c i) (r i)

theorem advanceHeat_ratio :
    Tendsto (fun i=> ((P.advanceHeat (c i) (r i)):ℝ)/(ρ i)) atTop (𝓝 (1/2:ℝ)) := by
  have hx (i):=bell_over_dew P (c i) (H.unitSize i) (P.timeJump (r i))
  have ht:=(ratio_bounds H.eager H.unitSize (F:=fun i=>D * P.timeJump (r i)) (d:=1) (e:=D)
    (fun i=>by rw [one_mul]; exact tickRound_le (by positivity) _))
  simp only [Nat.cast_one] at ht
  have Hs : Tendsto (fun i=>bell M (c i) (P.timeJump (r i))/(ρ i)) atTop (𝓝 (1/2:ℝ)):=ht.congr (fun i=> (hx i).symm)
  exact Hs.congr fun i=> congrArg (· / ρ i) (natural_time ..)

theorem macroTick_ratio :
    Tendsto (fun i=> P.macroTick (c i)/(ρ i)) atTop (𝓝 0) := by
  have hx (i): P.macroTick (c i)/(ρ i)=(D:ℕ)/(2*(r i:ℝ)):=by
    simpa [macroTick,bell] using (bell_over_dew P (c i) (H.unitSize i) 1)
  simp_rw [hx]
  have ht:=(ratio_bounds H.eager H.unitSize (F:=fun _=>D) (d:=0) (e:=D) (fun i=>by simp))
  simpa only [Nat.cast_zero,zero_div] using ht

theorem transportWidth3_ratio :
    Tendsto (fun i=> (P.transportWidth (c i) (r i) 3)/(ρ i)) atTop (𝓝 (5/2:ℝ)) := by
  have hx (i):=bell_over_dew P (c i) (H.unitSize i) (P.tickBudget (r i) 3)
  unfold transportWidth; simp_rw [hx]
  have ht := ratio_bounds H.eager H.unitSize (F:=fun i=>D * P.tickBudget (r i) 3)
    (fun i=>P.budget_error (r i))
  simpa only [Nat.cast_ofNat] using ht

theorem transportWidthCross_ratio {j : Axis} (h : j≠3) :
    Tendsto (fun i=> (P.transportWidth (c i) (r i) j)/(ρ i)) atTop (𝓝 0) := by
  have hx (i):=bell_over_dew P (c i) (H.unitSize i) (ℓ+1)
  unfold transportWidth tickBudget
  simp_rw [Function.update_of_ne h,hx]
  let e := D * (ℓ+1)
  have ht:=(ratio_bounds H.eager H.unitSize (F:=fun _=>e) (d:=0) (e:=e) (fun i=>by simp))
  simpa only [Nat.cast_zero,zero_div] using ht

theorem transportWidth_null (j : Axis) :
    Tendsto (fun i=> P.transportWidth (c i) (r i) j) atTop (𝓝 0) := by
  obtain ⟨L,t⟩ : ∃ L:ℝ,Tendsto (fun i=> (P.transportWidth (c i) (r i) j)/(ρ i))
      atTop (𝓝 L) := by
    by_cases h:j=3
    · subst j; exact ⟨_,transportWidth3_ratio H⟩
    exact ⟨_,transportWidthCross_ratio H h⟩
  simpa only [mul_zero] using
    (t.mul (P.proper_dew c r H)).congr (fun i=> div_mul_cancel₀ _ (P.dew_pos _ (H.unitSize i)).ne')
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
