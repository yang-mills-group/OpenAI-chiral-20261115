import YM.SU5.Same.EdgeLab
import YM.SU5.Reconstruction.UVPrice.Walls
/-! # The unpadded spectra of that continuum

M4 path. Work on a single CP18 Course, no Lorentz sector assertion yet.
See the construction notes. E4 dot even when Mink coordinates.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.SatinEdge.RealSheet
open Function Set Filter Metric Finset MeasureTheory Measure Spectral Analysis Boundary Probe
open OS Semigroup
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators Classical
open Multiplier Roy
open CF.Buffered.Afterglow.Tower.VacuumSelection Spine
variable {H:Hilbert} {a:Axis} (S:OS.Semigroup H a)
local notation "P" => S.ℚmeasure

/- Fold the zero/negative axis times to the bottom, **only for function values
   before pricing**. Real spectrum conclusions use S.bright, e≥0 (resp. no
   zero energy on those profiles used).
-/
def timeOf (a:Axis) (p:E4) : ℝ:= max 0 (p a)
@[fun_prop] lemma tick_cont : Continuous (timeOf a) := by unfold timeOf; fun_prop
def foldBand (a:Axis) (n:ℕ) : Set E4:= timeOf a ⁻¹' Set.Ico (n:ℝ) (n+1:ℕ)
lemma foldBand_meas(n:ℕ):MeasurableSet (foldBand a n):= tick_cont.measurable measurableSet_Ico
lemma foldBand_disjoint(a:Axis): Pairwise (Disjoint on (foldBand a)):= by
 intro i j h; apply Set.disjoint_left.mpr; intro x u v
 change ↑i ≤ timeOf a x ∧ timeOf a x < ((i+1:ℕ):ℝ) at u
 change ↑j ≤ timeOf a x ∧ timeOf a x < ((j+1:ℕ):ℝ) at v
 rcases Nat.lt_or_gt_of_ne h with t|t
 · exact lt_irrefl _ (u.2.trans_le ((((Nat.cast_le (α:=ℝ)).mpr t)).trans v.1))
 exact lt_irrefl _ (v.2.trans_le ((((Nat.cast_le (α:=ℝ)).mpr t)).trans u.1))
lemma foldBand_all(a:Axis): (⋃ n : ℕ, foldBand a n)=univ:=by
 apply Set.eq_univ_of_forall; intro p
 let s:= timeOf a p; refine mem_iUnion.mpr ⟨Nat.floor s,(show ↑(Nat.floor s) ≤ s ∧ s< ((↑(Nat.floor s+1):ℝ)) from ?_)⟩
 rw [Nat.cast_add_one]; exact ⟨Nat.floor_le (le_max_left ..), Nat.lt_floor_add_one s⟩
lemma timeOf_bound(p:E4): timeOf a p ≤ ‖p‖:= max_le (norm_nonneg p) (le_trans (le_abs_self (p a)) (by simpa only [basis_inner, show ‖basis a‖=(1:ℝ) from by simp, one_mul] using abs_real_inner_le_norm (basis a) p)) -- rw potential

abbrev cell (n:ℕ): H.Op:=(P).region (foldBand a n)
abbrev booth (n:ℕ) : Submodule ℂ H := LinearMap.range (cell S n).toLinearMap
local notation "B" n:max => foldBand a n
lemma member {x:H} {n:ℕ}: x∈ booth S n ↔ cell S n x=x:=
 ⟨fun ⟨v,h⟩=> h ▸ (P).idempotent (foldBand_meas n) v, fun h=> ⟨_,h⟩⟩ -- h direction? prove h ▸ defeq
lemma orth_cells : OrthogonalFamily ℂ (fun i=> ↥(booth S i)) (fun i=> (booth S i).subtypeₗᵢ):=by
 intro i j h v w
 let x:H:= v.val; let y:H:= w.val
 change inner ℂ x y=0
 have hv:x=cell S i x:= ((member S).1 v.property).symm
 have hy:y=cell S j y:= ((member S).1 w.property).symm
 rw (occs:=.pos [1]) [hv, show cell S i=(cell S i).adjoint from ((P).real (foldBand_meas i)).symm, ContinuousLinearMap.adjoint_inner_left]
 suffices he: cell S i y=0 by rw [he,inner_zero_right]
 nth_rw 1 [hy]; change (P).region _ ((P).region _ _)=0
 rw [← ContinuousLinearMap.comp_apply,(P).joins (foldBand_meas i) (foldBand_meas j),Set.disjoint_iff_inter_eq_empty.mp (foldBand_disjoint a h), (P).none]; rfl
lemma voting (x:H) : HasSum (fun i=> cell S i x) x:=by
 have he := (P).unites _ foldBand_meas (foldBand_disjoint a) x -- foldBand_meas implicit a, argument expects ... maybe
 rw [foldBand_all,(P).all,ContinuousLinearMap.id_apply] at he; exact he
lemma measure_sum_booths (μ:Measure E4) : μ=Measure.sum (fun i=> μ.restrict (foldBand a i)):=by
 nth_rw 1 [← Measure.restrict_univ (μ:=μ)]; rw [← foldBand_all a, Measure.restrict_iUnion (foldBand_disjoint a) foldBand_meas]

abbrev plusWeight (a:Axis)(t:ℝ≥0)(p:E4):ℂ:=↑(favor a t p)
def charging (a:Axis)(t:ℝ≥0)(n:ℕ): E4 →ℂ:=
 (foldBand a n).indicator (fun p=> (Real.exp ((t:ℝ)*timeOf a p):ℂ))
lemma charge_pay (t:ℝ≥0)(n:ℕ)(x:E4) : ‖charging a t n x‖≤ Real.exp ((t:ℝ)*(n+1:ℕ)):=by
 by_cases h:x∈foldBand a n
 · unfold charging; rw [indicator_of_mem h, Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_monotone (mul_le_mul_of_nonneg_left (show timeOf a x < (n+1:ℕ) from h.2).le t.property)
 unfold charging; rw [indicator_of_notMem h,norm_zero]; exact (Real.exp_pos _).le
lemma tag_charge(t:ℝ≥0)(n:ℕ):Tag (charging a t n):= by refine ⟨Measurable.indicator (by fun_prop) (foldBand_meas n),_,(Real.exp_pos _).le,charge_pay t n⟩
abbrev rewarm (t:ℝ≥0)(n:ℕ) : H.Op:= order (P) (charging a t n)
lemma rewarm_reads (t:ℝ≥0)(n:ℕ) : Registers S.ℚmeasure (charging a t n) (rewarm S t n) := order_reads (P) (tag_charge t n)
lemma rewarm_pays (t:ℝ≥0)(n:ℕ): ‖rewarm S t n‖≤ Real.exp ((t:ℝ)*(n+1:ℕ)):= (rewarm_reads S t n).fare (Real.exp_pos _).le (charge_pay t n)
lemma incell_rewarm (t:ℝ≥0)(n:ℕ): cell S n * rewarm S t n=rewarm S t n:= by
 apply Registers.single ((Registers.box (P) (foldBand_meas n)).times (rewarm_reads S t n)); convert rewarm_reads S t n using 1; funext p; by_cases h:p∈ foldBand a n<;> simp [charging,h]
lemma forward_cell(t:ℝ≥0)(n:ℕ): S.E t * rewarm S t n=cell S n:=by
 apply Registers.single ((costT S t).times (rewarm_reads S t n)); convert Registers.box (P) (foldBand_meas n) using 1
 funext x; by_cases h:x∈foldBand a n; swap; · simp [charging,h]
 simp only [Pi.mul_apply,h,indicator_of_mem,charging,timeOf,favor,← Complex.ofReal_mul, ← Real.exp_add]; rw [neg_mul,neg_add_cancel, Real.exp_zero]; simp
lemma project_commute {U:H.Op} {f:E4→ℂ}(h:Registers S.ℚmeasure f U) (n:ℕ)(y:H): cell S n (U y)= U (cell S n y):=
 DFunLike.congr_fun (h.comm (foldBand_meas n)).eq.symm y
lemma warm_project(t:ℝ≥0)(n:ℕ)(y:H): cell S n (S.E t y)=S.E t (cell S n y):= project_commute S (costT S t) n y

variable (X:ℝ→ H)
abbrev minute (n:ℕ) : ℝ≥0:= (↑(n+1:ℕ))⁻¹
lemma minute_wake(n:ℕ): 0< minute n:=by unfold minute; positivity
abbrev wing (n:ℕ): H:= rewarm S (minute n) n (X (minute n:ℝ))
lemma wing_fixed(n:ℕ): cell S n (wing S X n)=wing S X n:= DFunLike.congr_fun (incell_rewarm S (minute n) n) _
lemma wing_in (n:ℕ): wing S X n∈ booth S n:= (member S).mpr (wing_fixed S X n)
-- exact at EVERY positive real heat, and across the same PVM, no direction limits or phases.
lemma wing_earns (h:SatinJets.Positive S X)(t:ℝ≥0)(u:0<t)(n:ℕ): S.E t (wing S X n)=cell S n (X t):=by
 let y:= wing S X n
 let s:= minute n; have hs:0<s:= minute_wake n
 have v: S.E s y=cell S n (X s):= DFunLike.congr_fun (forward_cell S s n) (X (s:ℝ))
 have p(r q d:ℝ≥0)(g:q=d+r)(u:0<r)(z:H)(e:S.E r z=cell S n (X r)): S.E q z=cell S n (X q):=by
   rw [g,S.time,ContinuousLinearMap.comp_apply,e, ← warm_project]; congr 2
   exact (by rw [add_comm d r, NNReal.coe_add]; exact (SatinJets.Positive.moves S X h (by exact_mod_cast u) d).symm)
 rcases le_total s t with g|g
 · exact p s t (t-s) (tsub_add_cancel_of_le g).symm hs y v
 let w:= rewarm S t n (X t); have hv:S.E t w= cell S n (X t):= DFunLike.congr_fun (forward_cell S t n) (X (t:ℝ))
 have hx: S.E s y=S.E s w:= v.trans (p t s (s-t) (tsub_add_cancel_of_le g).symm u w hv).symm
 have hb:= S.heat_faithful s (y-w) (by rw [map_sub,hx,sub_self])
 exact (congrArg (fun z:H=> S.E t z) (sub_eq_zero.mp hb)).trans hv
-- remember t>0, and ease birth proof exact via backwards-paid
lemma wing_price (h:SatinJets.Positive S X)(t:ℝ≥0)(u:0<t)(n:ℕ): wing S X n=rewarm S t n (X t):= by
 let y:=wing S X n; let z:=rewarm S t n (X t); have he:S.E t y=S.E t z:= (wing_earns S X h t u n).trans (DFunLike.congr_fun (forward_cell S t n) (X (t:ℝ))).symm; exact sub_eq_zero.mp (S.heat_faithful t (y-z) (by rw [map_sub,he,sub_self]))
lemma wings_paying(h:SatinJets.Positive S X)(t:ℝ≥0)(u:0<t): HasSum (fun n=> S.E t (wing S X n)) (X t):= by
 simp_rw [wing_earns S X h t u]; exact voting S _
lemma wing_grows (h:TemperedAtEdge H X): ∃ m:ℕ,∃ C≥(0:ℝ),∀ i:ℕ, ‖wing S X i‖ ≤ C * ((i+1:ℕ):ℝ)^m:=by
 obtain ⟨m,C,hc,b⟩:=h; refine ⟨m,Real.exp 1 * C,mul_nonneg (Real.exp_pos _).le hc,fun n=>?_⟩
 let c:ℝ:=(n+1:ℕ); let t:=minute n; have hp:0<c:=by unfold c; positivity
 have ht:(t:ℝ)= c⁻¹:=by unfold t minute c; push_cast; rfl
 let y:=X (t:ℝ)
 have he:t ≤ 1:= inv_le_one_of_one_le₀ (by exact_mod_cast Nat.le_add_left 1 n) -- type? use coe
 have hz:‖rewarm S t n‖≤ Real.exp 1:= (rewarm_pays S t n).trans_eq (congrArg Real.exp (show (t:ℝ)*c=1 from ht ▸ inv_mul_cancel₀ hp.ne'))
 have h1:‖y‖≤C*c^m:=by
    have hw:(t:ℝ)^m* ‖y‖ ≤ C:= b _ (by exact_mod_cast minute_wake n) he -- ℝ vs NNReal?
    rw [ht,inv_pow, inv_mul_eq_div] at hw; exact (div_le_iff₀ (pow_pos hp m)).mp hw
 rw [mul_assoc]; exact ((rewarm S t n).le_opNorm y).trans (mul_le_mul hz h1 (norm_nonneg _) (Real.exp_pos _).le)

end YM.SatinEdge.RealSheet
open YM.SatinEdge.RealSheet
#print axioms wing_price
#print axioms wing_grows
