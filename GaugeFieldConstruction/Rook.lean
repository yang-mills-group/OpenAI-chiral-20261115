import GaugeFieldConstruction.Fathom
/-! Correct phase denominators & stems when chart near on torus -/
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
open Lenten
open Stationary Vault Font
open Bank Laurent Bloch Tap Hove Spire
open Haro Peaks Rush Fir Next.Free Thorn
open Planned.PrimaryIntegral295 Carrier
namespace Boom
variable {f c:Side}{G:Ratio c f}{A:Site f}{o:Skye.Seat f}
def measureG (G:Ratio c f)(o:Skye.Seat f)(x:Cover): Plane →L[ℝ]ℝ:= pointF (downT G o) (deckLoc G (AnchorN o))+rom x
def pairF (G:Ratio c f)(o:Skye.Seat f)(s:DiamP):Views→L[ℝ]ℝ:= -(measureG G o s.1.1|>.comp (ContinuousLinearMap.fst ℝ Plane Plane))+(measureG G o s.2.1|>.comp (ContinuousLinearMap.snd ℝ Plane Plane))
def Timely (c:Side)(x:Mill):Prop := 1000*(1+lateral x.1) < c.val
lemma t_sat (i:Mill)(u:Timely c i) : 100<c.val:=by unfold Timely at u; omega
abbrev Bury (G:Ratio c f)(o:Skye.Seat f)(x:Cover):= ηtag G (AnchorN o)
lemma prompt_stem (p: Odd G.count.val)(o:Skye.Seat f)(i: Mill)(v:Timely c i): let C:=downT G o; let K:=deckLoc G (AnchorN o); let x:=endLoc G (AnchorN o) i.1
  10*separation (node K) C <(More c).val∧10*separation (node x) C <(More c).val∧ spot C x= spot C K+i.1∧ stem K x=i.1:=by
 intro C K x; unfold Timely at v; have hR:= t_sat i v -- tune
 have ht:=jump_leV p o; change separation (node K) C≤ 19 at ht
 have hh:10*separation (node K) C < (More c).val:= by change _< c.val*2; omega
 have hz:= tag_spend p o i; change 1+(separation (node x) C:ℝ) ≤24*(1+(lateral i.1:ℝ)) at hz; have hy:1+separation (node x) C ≤ 24*(1+lateral i.1):= by exact_mod_cast hz
 refine ⟨hh,(show 10*separation (node x) C < c.val*2 from (by omega)),?_,?_⟩
 · have hx:(lateral (spot C K)) ≤ 50:=by
      apply (stem_t _ _).trans; let o:=AnchorN C; have he:= Hove.ζdist K o; have hh: separation (node K) (node o) ≤ 23:= (separation_triangle (node K) C (node o)).trans (show separation (node K) C+separation C (node o) ≤23 from (by have h: separation C (node o) ≤4:=(by rw [separation_comm]; exact still_anchor c C); omega)); change separation (node K) (node o)=2*separation K (AnchorN C) at he; omega
   apply lift_path; · rw [map_add,show wrap c _=K-AnchorN C from (wrap_lift ..)]; change K+wrap c i.1-AnchorN C=_; abel
   have he:= lateral_add (spot C K) i.1; omega
 exact lift_path (by change K+wrap c i.1-K=wrap c i.1; abel) (by omega)
lemma k_viewS (p: Odd G.count.val)(o:Skye.Seat f)(i:Mill)(v:Timely c i): pointF (downT G o) (endLoc G (AnchorN o) i.1) = measureG G o i.1 ∧ Caller (downT G o) (deckLoc G (AnchorN o))*Caller (downT G o) (endLoc G (AnchorN o) i.1)=Rush.wind (deckLoc G (AnchorN o)) i.1:=by
 let B:= deckLoc G (AnchorN o); let x:=endLoc G (AnchorN o) i.1; let C:= downT G o
 obtain ⟨hV,hK,hT,hv⟩:= prompt_stem p o i v; let ht:=t_sat i v; constructor
 · unfold measureG; rw [point_phase _ hK ht, point_phase _ hV ht,hT, rom_sum]; abel
 exact (Layout.Fren.gold_F _ B x (Layout.Fren.delta_o B hV ht) (Layout.Fren.delta_o x hK ht)).trans (congrArg _ hv)
lemma Well (G:Ratio c f)(e:Odd G.count.val)(o:Skye.Seat f) (q:DiamP)(s:Timely c q.1)(p:Timely c q.2) : let A:=AnchorN o; let K:=deckLoc G A; let y:= peakV G A q; let v:=downT G o;
 κviews v y.1.1.1 y.2.1.1 = pairF G o q∧ Caller v y.1.1.1*Caller v y.2.1.1*sliceAB G A y q=1:=by
 intro A K y v; obtain ⟨u,h⟩:=k_viewS e o q.1 s; obtain ⟨t,h'⟩:=k_viewS e o q.2 p; change pointF v y.1.1.1= _ at u; change pointF v y.2.1.1= _ at t
 refine ⟨?_,?_⟩; · unfold κviews pairF; rw [u,t] -- tune
 unfold sliceAB Event; rw [if_pos rfl,if_pos rfl]; unfold A; rw [← h,← h']
 let F:=Caller v K; let X:=Caller v y.1.1.1; let Y:= Caller v y.2.1.1
 have hf:F*F=1:=Rush.fee_one _; have hx:X*X=1:=Rush.fee_one _; have hh:Y*Y=1:=Rush.fee_one _
 change X*Y* ((F*X)*(F*Y))=1; rw [show X*_=X*Y from rfl,show X*Y*((F*X)*(F*Y))=(F*F)*(X*X)*(Y*Y) from (by ring),hf,hx,hh,one_mul,one_mul]
lemma Corr_k (p:Odd G.count.val)(i:Cover) : ‖measureG G o i‖ ≤40*Ladder i:=by
 unfold measureG; apply (norm_add_le ..).trans; apply (add_le_add (point_est ..) (radius_Z i)).trans; have hx:=jump_leV p o; rw [separation_comm (downT _ _)]; unfold Ladder; have h : (separation (node (deckLoc G (AnchorN o))) (downT G o):ℝ)≤19:=(by exact_mod_cast hx); linarith only [h,Nat.cast_nonneg (α:=ℝ) (lateral i)]
abbrev δBase(x:DiamP):ℝ:=max (Ladder x.1.1) (Ladder x.2.1)
abbrev maxTheta:= δBase -- tune
lemma δBase_p(i): 1 ≤ δBase i:= (ladE _).trans (le_max_left ..)
lemma thetaRange(i:DiamP):δBase i^3≤ThetaX i:=by
 rcases le_total (Ladder i.1.1) (Ladder i.2.1) with h|h
 · unfold ThetaX δBase; rw [max_eq_right h]; exact le_add_of_nonneg_left (zero_le_one.trans (wagE ..))
 unfold ThetaX δBase; rw [max_eq_left h]; exact le_add_of_nonneg_right (zero_le_one.trans (wagE ..))
lemma celebrate (p:Odd G.count.val)(x:DiamP): ‖pairF G o x‖ ≤ 96*δBase x∧
 let Gx:= peakV G (AnchorN o) x; ‖κviews (downT G o) Gx.1.1.1 Gx.2.1.1‖≤ 96*δBase x:=by
 let Y:= δBase x; have ht:1≤ Y:=δBase_p _; let f:=measureG G o; let X:=x.1; let K:=x.2
 have he:Ladder X.1≤Y:= le_max_left ..; have hz:Ladder K.1 ≤Y:=le_max_right ..
 constructor
 · have h(i:Cover)(g:Ladder i≤Y)(Q:Views→L[ℝ]Plane)(v:‖Q‖≤1): ‖(f i).comp Q‖≤40*Y:=(ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) v).trans ((Corr_k p _).trans (mul_le_mul_of_nonneg_left g (by positivity))))
   unfold pairF; apply (norm_add_le ..).trans; rw [norm_neg]; have hp:= h X.1 he _ (ContinuousLinearMap.norm_fst_le ℝ Plane Plane); have hv:= h K.1 hz _ (ContinuousLinearMap.norm_snd_le ℝ Plane Plane); apply (add_le_add hp hv).trans; change 40*Y+40*Y≤_; change _≤96*Y; linarith
 intro Q; apply le_trans (b:=4*(24*Y)) (peak_shifts _ _ _ (24*Y) _ _); · exact le_of_eq (by unfold Y; ring)
 · rw [separation_comm]; have h:=tag_spend p o x.1; apply le_trans (b:=24* Ladder x.1.1) _ (mul_le_mul_of_nonneg_left (by exact he) (by positivity)); exact le_trans (le_add_of_nonneg_left zero_le_one) h
 rw [separation_comm]; exact (le_add_of_nonneg_left zero_le_one|>.trans (tag_spend p o x.2)).trans (mul_le_mul_of_nonneg_left hz (by positivity))
end Boom
end YM.CF.TableF
end
