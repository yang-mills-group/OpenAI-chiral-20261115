import YM.SU5.Registration.Rasp.StillMusic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
/-!
 # True time derivative prices of point field.
 Use the M7 prescription as well as Seld's integration by parts in DISTRIBUTIONS
 on Mink areal. Get exact equality there before interpreting the M4 fields. Orders
 of derivatives are all finite. No assuming all these fields also with cap Warrant
 along other axes.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.SatinRegistration
open Set Filter Function MeasureTheory Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ComplexOrder Classical
open OS OS.Semigroup SatinEdge.RealSheet Boundary Probe Multiplier Roy CF.Buffered.Afterglow.Hierarchy.Seld
open Grading SatinJets SatinJets.Drums
variable {H : Hilbert} {a : Axis} (S : OS.Semigroup H a)
local notation "G" => bands S
local notation "D" => radial S
local notation "T" => S.E
local notation "F"=> S.F
local notation "R"=> saucer S
lemma val_angle (p:E4): Commute (S.unit.translation p) (saucer S):= (Picket.story S p).jointly (saucer_reads S)
lemma roped_values {u:ℝ≥0}(h:0<u): let U:=genPrice S u; R*U= R* T u - T u ∧ U*R=T u * R- T u:=by
 let g:=genPrice S u; let e:=T u
 have he:R*(e-g)=e:=by change R* (T u-g)=T u; rw [← S.roots_heat h]; exact dorsal S (duration u) (dur.mpr h)
 have hv:(e-g)* R=e:=by change (T u-g)*R=T u; rw [← S.roots_heat h]; exact jalousie S (duration u) (dur.mpr h)
 rw [mul_sub] at he; rw [_root_.sub_mul] at hv; constructor
 · change R*g=R*e-e; rw [eq_sub_iff_add_eq]; exact Eq.trans (add_comm ..) ((sub_eq_iff_eq_add.mp he).symm)
 change g*R=e*R-e; rw [eq_sub_iff_add_eq]; exact Eq.trans (add_comm ..) ((sub_eq_iff_eq_add.mp hv).symm)
private lemma comm_kit (A B I U K:H.Op) (h:I*U=I*B-B) (v:U*I=B*I-B)(p: K=B*A*B) : I*(U*A*B-B*A*U)*I= I*K-K*I:=by
 rw [mul_sub,_root_.sub_mul, ←mul_assoc I (U*A), ←mul_assoc I U, h] -- assoc pattern inner A* etc
 subst K; simp only [_root_.sub_mul,mul_assoc,v,mul_sub]; abel
lemma roped_action (u:ℝ≥0)(h:0<u)(A B:H.Op)(p:B=T u*A*T u) : R*action S u (genPrice S u) A* R= R* B-B* R:= comm_kit _ _ _ _ _ (roped_values S h).1 (roped_values S h).2 p
-- `valise` of fixed padded operators at a Schwartz test. use pairing R invertibility only as linear (not bounded inverse).
def valMeasure (f:Test4): (H.Op) →ₗ[ℂ] H.Op where
 toFun A:=valise S A f
 map_add' u v:= vadd ..
 map_smul' u v:= vscale ..
lemma val_rope (f:Test4)(A B:H.Op)(h:R*A*R= R*B-B*R): valise S A f= valise S B ( - εpref a f):=by
 let g:= valise S A f; let L:= valise S B f; let q:= εpref a f; let h':= valise S B q; let v:= valise S B (-q)
 have hz:= congrArg (valMeasure S f) h; rw [map_sub] at hz
 change valise S (R*A*R) f= valise S (R*B) f - valise S (B*R) f at hz
 rw [overlap_R _ _ _ _ (val_angle S), overlap _ A _ _ (val_angle S),overlap _ B _ _ (val_angle S),overlap_R _ B _ _ (val_angle S)] at hz
 have hx: L*R= R*L+R*h'*R:= orion S B f
 have hg:v= -h':= map_neg (barren S B) q
 change R*g*R= R*L-L*R at hz
 have ht:R*g*R= R*v*R:=by rw [hz,hx,hg,mul_neg,neg_mul]; abel
 apply DFunLike.coe_injective; exact (saucer_D S).equalizer g.continuous v.continuous (funext (fun x=> paranoid S (DFunLike.congr_fun ht x))) -- Deal with DFunLike.coe implicit target? tune

-- convergence includes heated value on full G. notation F not call
variable (B:ℝ≥0→ H.Op)
local notation "ρ"=> (𝓝[>] (0:ℝ≥0))
open Submodule
lemma vacillate (p:PadPaid B)(h:Sound S B)(f:Test4)(x:D): Tendsto (fun s:ℝ≥0=> valise S (B s) f x.1) ρ (𝓝 (field S B h p f x).1) :=by
 have he := passes_lim S B h p (l:=ρ) (x:=x) f id id tendsto_id tendsto_id (X:=fun _=>x) (fun k=> by simp only [budget,due,sub_self,map_zero,norm_zero,mul_zero,tsum_zero]; exact tendsto_const_nhds)
 let X(s:ℝ≥0):=(B s); apply (Approaches.hilbert (bands S) he).congr' (?_); filter_upwards [self_mem_nhdsWithin] with i h; rw [warm_actual]; unfold bothPads; simp only [_root_.id_eq,min_self,tsub_self, S.eZero]; rfl -- `rfl` ops? need One
variable (p:PadPaid B)(h:Sound S B)(A:ℝ≥0→ H.Op)(t:Sound S A) (u:PadPaid A)
include p h t u
/-- Unpadded identity in the field map from the generator action. See OnRail and M8 for correspondence to physical purchases. -/
abbrev timeJet (a:Axis): Test4 →L[ℂ] Test4:= - εpref a
lemma roster_jet (q:∀ s:ℝ≥0,0<s→ A s=action S (s/2) (genPrice S (s/2)) (B (s/2)))(f:Test4) : field S A t u f = field S B h p (timeJet a f):=by
 ext1 x; apply Subtype.ext;
 have hp(s:ℝ≥0)(u:0<s): valise S (A s) f= valise S (B s) (timeJet a f):= by
    let d:=s/2; have he:d+d=s:= _root_.add_halves s; have hb:0<d:=half_pos u; exact val_rope S f _ _ ((q s u).symm ▸ roped_action S d hb (B d) _ ((congrArg B he).symm.trans (h d hb d))) -- rewrites B s? need `timeJet a f` defeq neg
 let hf:= vacillate S B p h (timeJet a f) x; refine tendsto_nhds_unique_of_eventuallyEq (vacillate S A u t f x) hf (?_); filter_upwards [self_mem_nhdsWithin] with i h; exact DFunLike.congr_fun (hp i h) _ -- universe Filter.NeBot not found?
omit p h t u
lemma time_reach (a:Axis) (f:Test4): tsupport (timeJet a f) ⊆ tsupport f:= by
 refine subset_trans (tsupport_comp_subset (g:=fun z:ℂ=> -(Complex.I * z)) (?_) (shade (basis a) f)) (SchwartzMap.tsupport_lineDerivOp_subset (basis a) f); exact neg_eq_zero.mpr (mul_zero _) -- definitional composition support? check
lemma bar_reach (f:Test4): tsupport (bar f)=tsupport f:=by
  refine le_antisymm (tsupport_comp_subset (g:=star) (star_zero ℂ) f) ?_; nth_rw 1 [← Probe.bar_twice f]; exact tsupport_comp_subset (g:=star) (star_zero ℂ) _
-- linearity in this kernel. holds exactly at each read after positive allowance. Require separate PadPaid on the limit adopted and its adjoints.
variable {I:Type*}(l:Finset I)(J:I→ℝ≥0→ H.Op)(V:I→ℂ)
include h p
lemma field_score (f:Test4)(t:∀ i,Sound S (J i))(v:∀ i,PadPaid (J i))(u:∀ s:ℝ≥0,0<s → B s=∑ i∈l,V i • (J i s)) : field S B h p f = ∑ i∈l,V i • field S _ (t i) (v i) f :=by
 ext1 x; apply Subtype.ext; let Z:= ((∑ i∈l,V i • field S _ (t i) (v i) f) x).1
 have hp:Z=∑ i∈l,V i • (field S _ (t i) (v i) f x).1:= by unfold Z; rw [LinearMap.sum_apply,Submodule.coe_sum]; rfl
 change (field S B h p f x).1= Z; rw [hp]; let M(s:ℝ≥0):=∑ i∈l,V i • valise S (J i s) f x.1
 refine tendsto_nhds_unique_of_eventuallyEq (vacillate S B p h f x) (show Tendsto M ρ _ from ?_) ?_
 · exact tendsto_finset_sum l (fun i _=>(vacillate S (J i) (v i) (t i) f x).const_smul (V i))
 filter_upwards [self_mem_nhdsWithin] with s h; change valMeasure S f (B s) x.1=_; rw [u s h,map_sum]; unfold M; rw [ContinuousLinearMap.sum_apply]; simp only [map_smul]; rfl -- order `_root_.sum_apply` etc
end YM.SatinRegistration
open YM.SatinRegistration
#print axioms roster_jet
#print axioms field_score
#print axioms time_reach
#print axioms bar_reach
#print axioms val_rope
