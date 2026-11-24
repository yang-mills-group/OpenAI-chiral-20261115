import YM.SU5.Six.PressSmear
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import YM.SU5.Six.TransitWall
import YM.SU5.Six.Photos
import YM.SU5.Six.OrdinaryMist
import YM.SU5.Aria.Grotto
import YM.SU5.Six.KeepCharge
import YM.SU5.Six.MirrorCharge
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
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
open Aria Set
open Cheer (Narrow)
open scoped ContDiff
variable (F G:SampleDose)(p:ℝ)
-- Wall support & open rectangles R
structure Doorway where
 lower : Vantage
 upper : Vantage
 clearance : ∀ j:Axis, lower j < upper j
namespace Doorway
def invites (Y:Doorway): Set Vantage:= Set.univ.pi (fun j=> Set.Ioo (Y.lower j) (Y.upper j))
def sealing(Y:Doorway): Set Vantage:= Set.Icc Y.lower Y.upper
lemma doorOpen (Y:Doorway) : IsOpen Y.invites:= isOpen_set_pi (Set.finite_univ) (fun j _=>isOpen_Ioo)
lemma doorNonempty (Y:Doorway) : Y.invites.Nonempty:= by
 choose k h g using fun i=>exists_between (Y.clearance i); exact ⟨k, fun i _=>⟨h i,g i⟩⟩
lemma door_compact (Y:Doorway) : IsCompact Y.sealing:=isCompact_Icc
lemma doorSeal (Y:Doorway) : closure Y.invites=Y.sealing:= by
 let b:=fun j=> Set.Ioo (Y.lower j) (Y.upper j)
 rw [invites,closure_pi_set]
 simp_rw [show ∀ i:Axis,closure (Set.Ioo (Y.lower i) (Y.upper i))=Set.Icc (Y.lower i) (Y.upper i) from fun i=> closure_Ioo (ne_of_lt (Y.clearance i))]
 exact Set.pi_univ_Icc Y.lower Y.upper
end Doorway
lemma dose_visible (h:F.Normalized) : (tsupport F.val).Nonempty:= by
 by_contra! f
 have u : tsupport F.val=∅:= f -- tune
 have e:F.val=0:= funext fun i=> Classical.byContradiction fun p=> Set.notMem_empty i ((u ▸ (show i∈tsupport F.val from subset_closure (show F.val i≠0 from p))))
 have ht:=h.2; rw [e,integral_zero'] at ht; exact zero_ne_one ht
-- smooth genuinely sized tests and costs
namespace DoseTravel
variable (x:Vantage) (f:ContDiffBump x)
def relative (x:Vantage)(p:ℝ)(u:0<p) : ContDiffBump x:= ⟨p/2,p,half_pos u, half_lt_self u⟩
abbrev chosen (x:Vantage)(i:ℕ): ContDiffBump x:= relative x ((1/2:ℝ)^i) (by positivity)
def slider (x:Vantage)(f:ContDiffBump x): SampleDose:= ⟨f.normed volume, f.contDiff_normed,f.hasCompactSupport_normed⟩
lemma prescribed : (slider x f).Normalized:=⟨fun x=> f.nonneg_normed x, f.integral_normed⟩
lemma supported : tsupport (slider x f).val= Metric.closedBall x f.rOut:= f.tsupport_normed_eq
lemma concentrates (U:Set Vantage)(h:U∈𝓝 x) : ∀ᶠ i:ℕ in atTop, tsupport (slider x (chosen x i)).val ⊆ U := by
 obtain ⟨ε,p,t⟩:= Metric.mem_nhds_iff.mp h
 filter_upwards [(tendsto_pow_atTop_nhds_zero_of_lt_one (r:=(1/2:ℝ)) (by norm_num) (by norm_num)).eventually (gt_mem_nhds p)] with i v
 exact (supported x (chosen x i)).symm ▸ ((Metric.closedBall_subset_ball v).trans t)
-- continuous vector reading on unrestricted center positions (totalize heat off times)
def beam (X:Hilbert)(A:SampleDose)(u:Vantage→X) := ∫ x:Vantage,(A.val x:ℂ) • u x
lemma tol (X:Hilbert)(u: Vantage→X)(hf:Continuous u)(f:SampleDose)(p:f.Normalized)(ε:ℝ)(h:∀ i∈ tsupport f.val, ‖u i-u x‖≤ ε): ‖beam X f u-u x‖≤ ε := by
 let z(p):ℝ:=f.val p
 let V (p):= z p • u p; let T (p:Vantage):=z p • u x
 have hp:Integrable z:= f.smooth.continuous.integrable_of_hasCompactSupport f.budget
 have he : Integrable V:= (f.smooth.continuous.smul hf).integrable_of_hasCompactSupport f.budget.smul_right -- smul ℝ vs ℂ
 have ht:Integrable T:= hp.smul_const (u x)
 unfold beam; simp_rw [Complex.coe_smul]; rw [← show ∫ p,T p=u x from (integral_smul_const ..).trans ((congrArg (· • u x) (show ∫ p,z p=1 from p.2)).trans (one_smul ..))]
 -- warning rewrites `u x` inside? measure
 change ‖(∫ p,V p)-(∫ p,T p)‖≤ ε; rw [← integral_sub' he ht]
 apply (norm_integral_le_integral_norm ..).trans
 have e(i:Vantage): ‖(V-T) i‖ ≤z i*ε:= by
   change ‖z i • u i-z i • u x‖≤ _; rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (p.1 i)]
   by_cases g:z i=0; · rw [g, show f.val i=0 from g,zero_mul,zero_mul]
   exact mul_le_mul_of_nonneg_left (h i (subset_closure g)) (p.1 i)
 exact (integral_mono ((he.sub ht).norm) (hp.mul_const ε) e).trans_eq (by rw [integral_mul_const,show ∫ p,z p=1 from p.2,one_mul])
lemma sprinkle (X:Hilbert)(u:Vantage→X)(h:Continuous u): Tendsto (fun i=>beam X (slider x (chosen x i)) u) atTop (𝓝 (u x)):= by
 apply Metric.tendsto_nhds.mpr; intro ε e
 let S:= u ⁻¹' (Metric.ball (u x) (ε/2)); filter_upwards [concentrates x S ((h.tendsto x).eventually (Metric.ball_mem_nhds _ (half_pos e)))] with i a
 exact (dist_eq_norm ..|>.trans_le (tol x X u h (slider x _) (prescribed ..) _ (fun y p=>(dist_eq_norm (u y) (u x) ▸ (Metric.mem_ball.mp (a p))).le))).trans_lt (half_lt_self e)

-- Lines and neighborhoods of smooth test densities. Supports in a common
-- compact inside the same geometry; ordinary C⁰ sup cost (enough for
-- stability); and closeness in every specified C^k including all derivatives.
def convexSeek (F G:SampleDose)(t:ℝ) : SampleDose where
 val:= F.val+t • (G.val-F.val)
 smooth:= F.smooth.add ((G.smooth.sub F.smooth).const_smul t)
 budget:= F.budget.add ((G.budget.sub F.budget).smul_left)
lemma convex_seal (K:Set Vantage)(f:tsupport F.val⊆K)(h:tsupport G.val⊆K): tsupport (convexSeek F G p).val⊆ K:=
  (tsupport_add _ (p • (G.val-F.val))).trans (Set.union_subset f ((tsupport_smul_subset_right (fun _=>p) _).trans ((tsupport_sub _ _).trans (Set.union_subset h f))))
lemma convex_normal (t:p∈ Set.Icc (0:ℝ) 1)(h:F.Normalized)(g:G.Normalized): (convexSeek F G p).Normalized:= by
 refine ⟨fun i=> ?_,?_⟩
 · change 0≤ F.val i+p*(G.val i-F.val i)
   nlinarith only [mul_nonneg t.1 (g.1 i), mul_nonneg (show 0≤1-p from sub_nonneg.mpr t.2) (h.1 i)]
 have hf: Integrable F.val:= F.smooth.continuous.integrable_of_hasCompactSupport F.budget
 have hg: Integrable G.val:= G.smooth.continuous.integrable_of_hasCompactSupport G.budget
 change (∫ i,F.val i+p • (G.val-F.val) i)=1
 rw [integral_add hf (show Integrable (fun x=> p • (G.val-F.val) x) from Integrable.smul p (hg.sub hf)), integral_smul, integral_sub' hg hf,h.2,g.2,sub_self,smul_zero,add_zero]
-- lengths quantifier (`all observed smooth costs through k`) tolerance
-- use all of position space for the bound, common support containment separately.
def NearSmear (k:ℕ)(ε:ℝ)(F G:SampleDose):Prop:=∀ j:ℕ,j≤k→∀ p, ‖iteratedFDeriv ℝ j G.val p-iteratedFDeriv ℝ j F.val p‖≤ ε
lemma early_costs (k:ℕ)(ε:ℝ)(h:0<ε):∀ᶠ t:ℝ in 𝓝 0, NearSmear k ε F (convexSeek F G t):=by
 have hP(j:ℕ):∀ᶠ t:ℝ in 𝓝 0,∀ p:Vantage, ‖iteratedFDeriv ℝ j (convexSeek F G t).val p-iteratedFDeriv ℝ j F.val p‖≤ ε:=by
   let f:=G.val-F.val
   have hu:ContDiff ℝ j f:= (G.smooth.sub F.smooth).of_le (by exact_mod_cast le_top)
   have ht:HasCompactSupport f:= G.budget.sub F.budget
   obtain ⟨C,x⟩:= (hu.continuous_iteratedFDeriv le_rfl).bounded_above_of_compact_support (ht.iteratedFDeriv j)
   have hf:Continuous (fun t:ℝ=>‖t‖*C):= continuous_norm.mul continuous_const
   filter_upwards [(hf.tendsto 0).eventually (gt_mem_nhds (show ‖(0:ℝ)‖*C<ε by simpa using h))] with t w
   intro p
   change ‖iteratedFDeriv ℝ j (F.val+t • f) p-iteratedFDeriv ℝ j F.val p‖≤ ε
   rw [iteratedFDeriv_add (F.smooth.of_le (by exact_mod_cast le_top)) (show ContDiff ℝ j (t • f) from hu.const_smul t),Pi.add_apply,add_sub_cancel_left, iteratedFDeriv_const_smul_apply hu.contDiffAt,norm_smul]; exact le_trans (mul_le_mul_of_nonneg_left (x p) (norm_nonneg t)) w.le
 filter_upwards [(Finset.eventually_all (Finset.range (k+1))).mpr (fun j _=>hP j)] with t f
 exact fun j e=> f j (Finset.mem_range.mpr (by omega))
private lemma convex_pay (X:Hilbert)(u:Vantage→X)(h:Continuous u):beam X (convexSeek F G p) u=beam X F u+(p:ℂ) • (beam X G u-beam X F u):= by
 have ht(V:SampleDose):Integrable (fun x=> V.val x • u x):= (V.smooth.continuous.smul h).integrable_of_hasCompactSupport V.budget.smul_right
 let D(V:SampleDose)(x:Vantage):=V.val x • u x
 unfold beam; simp_rw [Complex.coe_smul]; change (∫ x,D (convexSeek F G p) x)=_ + p • ((∫ x,D G x)-(∫ x,D F x))
 have he:D (convexSeek F G p)= fun x=> D F x+p • (D G-D F) x:= by
    funext x; simp only [D,convexSeek,Pi.smul_apply,Pi.add_apply,Pi.sub_apply,add_smul,sub_smul,smul_eq_mul,mul_smul,smul_sub]
 have hf:Integrable (D F):=ht F; have hg:Integrable (D G):= ht G
 change (∫ x,D (convexSeek F G p) x)= ((∫ x,D F x)+p • _)
 rw [he]; change (∫ x,D F x+p • (D G-D F) x)= _; rw [integral_add hf (show Integrable (fun x=> p • (D G-D F) x) from Integrable.smul p (hg.sub hf)), integral_smul, integral_sub' hg hf]
lemma seek_zero : convexSeek F G 0=F := by cases F; congr; simp [convexSeek] -- tune
lemma seek_one : convexSeek F G 1=G := by cases G; congr; simp [convexSeek]
lemma seek_beams (X:Hilbert)(u:Vantage→X)(h:Continuous u): AnalyticOnNhd ℝ (fun t=>beam X (convexSeek F G t) u) Set.univ:=by
 intro t _; simp_rw [convex_pay F G _ X u h,Complex.coe_smul]; exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
-- stability of vector prices stronger (uniform without smoothness needed),
-- state with explicit cost bounds.
def AltNear (ε:ℝ)(F G:SampleDose):Prop:=∀ p:Vantage, ‖G.val p-F.val p‖<ε
lemma affordable (X:Hilbert)(u:Vantage→X)(h: Continuous u)(K:Set Vantage)(b:IsCompact K) : ∃ C:ℝ,0<C∧∀ (ε:ℝ),0<ε→ ∀ F G:SampleDose,tsupport F.val⊆K→tsupport G.val⊆K→AltNear ε F G→ dist (beam X F u) (beam X G u) ≤ ε*C:=by
 obtain ⟨Y,e,t⟩:= (b.image h).isBounded.exists_pos_norm_le
 refine ⟨volume.real K * Y + 1,by positivity,?_⟩
 intro a v F G f g s
 let V (p):= F.val p • u p; let T':= fun p=>G.val p • u p
 have hX(i:Vantage): ‖(V-T') i‖≤ K.indicator (fun _=> a*Y) i:= by
   by_cases p:i∈K
   · rw [indicator_of_mem p]; change ‖F.val i • u i-G.val i • u i‖≤ _; rw [←sub_smul,norm_smul]; exact mul_le_mul (((norm_sub_rev ..).trans_lt (s i)).le) (t _ ⟨i,p,rfl⟩) (norm_nonneg _) v.le
   rw [indicator_of_notMem p]
   have hx(M:SampleDose)(t:tsupport M.val⊆K): M.val i=0:=by by_contra e; exact p (t (subset_closure e))
   simp [V,T',hx F f,hx G g]
 have he(U:SampleDose):Integrable (fun x=> U.val x • u x):= (U.smooth.continuous.smul h).integrable_of_hasCompactSupport U.budget.smul_right
 unfold beam; simp_rw [Complex.coe_smul,dist_eq_norm]; change ‖(∫ p,V p)-(∫ p,T' p)‖≤_
 have hV: Integrable V:= he F; have hT: Integrable T':=he G
 rw [← integral_sub' hV hT]; apply (norm_integral_le_integral_norm ..).trans
 apply (integral_mono ((hV.sub hT).norm) ((integrable_indicator_iff b.measurableSet).2 (integrableOn_const b.measure_ne_top)) hX).trans
 rw [integral_indicator_const _ b.measurableSet,smul_eq_mul]; linarith -- tune nonlinear
end DoseTravel
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
