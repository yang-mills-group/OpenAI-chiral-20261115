import YM.CF.Graph.Easel
import YM.CF.Fixed.Triangular
import YM.CF.Fixed.ShellVolume

/-!
Lower relative to upper. Tree fixing agrees with actual gauge transform despite
wrap; we don't modify the probability layout, nor need gauge fixed pointwise
norms to be re-established for rank vacuum because this is a bound on Angle.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Fixed.Pivots
open Function Filter MeasureTheory Gauge Lattice Finset Wilson
open scoped Matrix.Norms.Frobenius BigOperators Topology ENNReal InnerProductSpace
variable (G:Gauge) {N:Side}
abbrev cotree(N:Side): Finset (Link N):= (treeLinks N)ᶜ
-- Tree phase choices constructive. Work with fuel steps decreasing.
abbrev slopeL(x:Site N)(h:x≠0): originSum (parentLink x h).1+1=originSum x:= reduced x (gapAxis x h) (gapAxis_nonzero x h)
def rotateSite(x:Site N) (U:Config G N) : G.El:= if h:x=0 then 1 else rotateSite (parentLink x h).1 U * U (parentLink x h)
termination_by originSum x
decreasing_by
  have hp:= slopeL x h; exact Nat.lt_of_succ_le hp.le

lemma rotateSite_c (x:Site N): Continuous (rotateSite G x) := by
  induction n:originSum x using Nat.strong_induction_on generalizing x with
  | _ k ih=>
    by_cases h:x=0
    · rw [show rotateSite G x=(fun U:Config G N=>1) from funext fun y=>by rw [rotateSite,dif_pos h]]; exact continuous_const
    have he:originSum (parentLink x h).1<k:= by rw [←n]; exact Nat.lt_of_succ_le (slopeL x h).le -- rename n
    rw [show rotateSite G x=(fun U:Config G N=>rotateSite G (parentLink x h).1 U * U (parentLink x h)) from funext fun U=>by rw [rotateSite,dif_neg h]]
    exact (ih _ he _ rfl).mul (continuous_apply _)
lemma rotateSite_depends (x:Site N)(U:Config G N)(j:Link N)(z:G.El)(e:j∈cotree N): rotateSite G x (update U j z)=rotateSite G x U:=by
  induction n:originSum x using Nat.strong_induction_on generalizing x with
  | _ a ih=>
    by_cases h:x=0; · rw [rotateSite,dif_pos h,rotateSite,dif_pos h]
    have he:originSum (parentLink x h).1<a:=by rw [←n]; exact Nat.lt_of_succ_le (slopeL x h).le
    let i:= parentLink x h; have hi:i ≠ j:= fun g=>mem_compl.mp e (g ▸ mem_filter.mpr ⟨mem_univ _,tree_is x h⟩)
    rw [rotateSite.eq_1 G x (update U j z),rotateSite.eq_1 G x U,dif_neg h,dif_neg h,ih _ he _ rfl,update_of_ne hi]

def zeroLinks (U:Config G N):Config G N:= gauge (fun x=>rotateSite G x U) U
lemma zero_tree (U:Config G N)(x:Link N)(h:Tree x): zeroLinks G U x=1:=by
  unfold zeroLinks Lattice.gauge; let i:=reach x; change _*(rotateSite G i U)⁻¹=_; have he: rotateSite G i U= rotateSite G x.1 U * U x:=by rw [rotateSite,dif_neg (show i≠0 from reach_tree x h),tree_reduces x h]
  rw [he,mul_inv_cancel]
lemma batch_gauge (U:Config G N)(j:Link N)(h:j ∈ cotree N): batch (cotree N) (fun x (U:Config G N)=>zeroLinks G U x) U j= zeroLinks G U j:= if_pos h
lemma zeroLinks_c: Continuous (zeroLinks G (N:=N)):= continuous_pi (fun (j:Link N)=> ((rotateSite_c G j.1).mul (continuous_apply _)).mul (rotateSite_c G _).inv)
lemma anchor_mp : MeasurePreserving (batch (cotree N) (fun x (U:Config G N)=>zeroLinks G U x)) (prior G N) (prior G N):=by
  apply batch_preserves G.probHaar _ _ _ (fun _=>0)
  · intro i p j h _ e x y; unfold zeroLinks Lattice.gauge; simp_rw [rotateSite_depends G _ _ _ _ p,update_of_ne e.symm]
  · intro i p u; unfold zeroLinks Lattice.gauge; simp_rw [rotateSite_depends G _ _ _ _ p, update_self]; exact G.preserve_two_sided ..
  exact fun i _=> ((continuous_apply i).comp (zeroLinks_c G)).measurable

def anchored(r:ℝ): Set (Config G N):= (batch (cotree N) (fun x (U:Config G N)=> zeroLinks G U x)) ⁻¹' (((cotree N):Set (Link N)).pi (fun _=> G.shell r))
lemma anchored_meas(r:ℝ):MeasurableSet (anchored G (N:=N) r) := (anchor_mp G (N:=N)).measurable (MeasurableSet.pi (Set.to_countable _) fun _ _=>G.shell_meas r)
lemma anchored_volume(r:ℝ): (prior G N).real (anchored G r) = (Extensive.shellMass G r)^(cotree N).card := by rw [anchored, Measure.real, (anchor_mp G (N:=N)).measure_preimage (MeasurableSet.pi (Set.to_countable _) fun i _=>G.shell_meas r).nullMeasurableSet,prior,Measure.pi_pi_finset]; rw [prod_const,ENNReal.toReal_pow]; rfl
lemma anchor_stone(u:ℝ)(p:0 ≤u){x:Config G N}(h:x ∈ anchored G u): zeroLinks G x ∈ Graph.stone G N u:=by
  intro i _; by_cases q:Tree i; · apply (show G.chord (zeroLinks G x i) ≤ u from ?_); rw [zero_tree G _ _ q,G.chord_one]; exact p
  have ht:i∈cotree N:=mem_compl.mpr (fun v=>q (mem_filter.mp v).2)
  have he : batch (cotree N) (fun y (U:Config G N)=>zeroLinks G U y) x i∈ G.shell u:=h i ht -- Set.pi expects index
  rw [batch_gauge G x i ht] at he; exact he
end YM.CF.Fixed.Pivots
namespace YM.CF.Fixed.Extensive
open Function Filter MeasureTheory Gauge Lattice Finset Wilson
open scoped BigOperators Topology ENNReal InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lat SU Cube Fock Skye Scree Girt Graph Pivots RG
variable {N:Side} {P:GramM N}{u t v k a b m x d h:ℝ}
local notation "lit_" => anchored group (N:=More N) u
lemma shell_angle (W : Ward P) (X: P.path.Bounds P.funds a b d)(p:0≤u)(l:4*u≤ P.p.threshold)(g:P.funds.direct≤h)(v:0≤ P.beta)(H:0≤b):
    (Extensive.shellMass group u)^(cotree (More N)).card * Real.exp (-stoutY (More N) P.beta (4*u) h P.p.threshold b d) ≤ Graph.angle P := by
  classical
  let S : Set (Orbit N):= Prod.fst ⁻¹' lit_
  have hs:MeasurableSet S:=measurable_fst (anchored_meas group _); let x:=Real.exp (-stoutY (More N) P.beta (4*u) h P.p.threshold b d)
  have ht(i:Orbit N): S.indicator (fun _=>x) i ≤ dim P i:=by
    by_cases k:i∈ S; swap; · rw [Set.indicator_of_notMem k]; exact Set.indicator_nonneg (fun _ _=> (Real.exp_pos _).le) _
    have he : zeroLinks group i.1 ∈ Graph.stone group (More N) u:= anchor_stone group _ p (show i.1∈ lit_ from k)
    have hz:= rife (G:=group) P.p _ he l; unfold zeroLinks at he hz; rw [RG.gauge_flags] at hz; rw [dim,Set.indicator_of_mem k,Set.indicator_of_mem (show i∈Lace P from hz)]; unfold past; rw [← thumb P X _ (fun x=>rotateSite group x i.1)]; exact Real.exp_le_exp.mpr (neg_le_neg (money X _ _ he g l p v H))
  have he : (city N).real S=(Extensive.shellMass group u)^(cotree (More N)).card:=by
    rw [←anchored_volume group,Measure.real,Measure.real,(measurePreserving_fst (μ:= prior group (More N)) (ν:=Skye.depot N)).measure_preimage (anchored_meas group _).nullMeasurableSet] -- S def
  have hu:= integral_mono ((integrable_const x).indicator hs) ((worth W).integrable (city N)) ht; rw [integral_indicator hs,setIntegral_const,he] at hu; exact hu
end YM.CF.Fixed.Extensive
