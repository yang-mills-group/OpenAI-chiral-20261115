import GaugeFieldConstruction.Urgent
set_option autoImplicit false
set_option maxHeartbeats 45000
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
variable {f c:Side}{σ Y B:Bool→ℝ} {G: Ratio c f}{M:Male}{A:Site f}{o:Skye.Seat f}{T:Script Male}{p:BudgetPoint}{Q: Op (Single f)}{k m r:ℕ}{b:Bool}
abbrev downT (G:Ratio c f) (o:Skye.Seat f):Skye.Seat c:= (Rush.ratio G).parent o
-- distance in gauge units. pre-L uniformly.
open Layout
lemma spotLength_B (n:Side)(o:Skye.Seat n)(x:Site n): Ladder (spot o x) ≤ 10*(1+ (separation (node x) o:ℝ)):=by
 let a:= AnchorN o
 have hx: separation (node a) o ≤ 4:=by
    rw [show node a= _ from anchor_E o]; unfold separation; rw [add_sub_cancel_left]; exact (wrap_month (siteOffset o)).trans (rent_z o)
 have hp:= separation_triangle (node x) o (node a); rw [Hove.ζdist,separation_comm o (node a)] at hp
 have he:= stem_t a x; change 1+(lateral (stem a x):ℝ) ≤ _; exact_mod_cast (show 1+lateral (stem a x) ≤10*(1+separation (node x) o) from by omega)
lemma still_anchor (n:Side)(o:Skye.Seat n): separation (node (AnchorN o)) o ≤ 4:=by rw [anchor_E]; unfold separation; rw [add_sub_cancel_left]; exact (wrap_month (siteOffset o)).trans (rent_z o)
lemma jump_leV (e:Odd G.count.val)(o:Skye.Seat f) : let K:= deckLoc G (AnchorN o)
 separation (node K) (downT G o)≤ 19:=by -- residual step all orientations
 let A:=AnchorN o; let K:=deckLoc G A; intro D; let Y:=Rush.ratio G; let L:=G.count; let v:= node K; let s:= node A; let t:=downT G o
 have hx: s=Y.embed v +wrap _ ((2:ℕ) • lift (PatchLoc G A)):=by unfold s; rw [show node A=node (isle G (K, PatchLoc G A)) from congrArg node (seal_o G A)]; exact embed_node G e _ _
 have hh:separation s (Y.embed v) ≤ 8*L.val:=by unfold separation; rw [hx,add_sub_cancel_left]; refine (wrap_month _).trans ?_; rw [two_smul]; have he:= lateral_add (lift (PatchLoc G A)) (lift (PatchLoc G A)); have ht:= lift_moon (PatchLoc G A); unfold L; omega
 let k:=Y.parent s
 have hc: L.val * separation k v≤ separation s (Y.embed v)+L.val:=by nth_rw 1 [← Y.embed_parent v]; exact Corona.foreshorten Y s (Y.embed v) -- tune rew rhs
 have he:= Work.E04.parent_separation Y s o
 have hp:= still_anchor f o; change separation k t ≤ _ at he; change separation v t ≤_; apply (separation_triangle v k t).trans; rw [separation_comm v]; refine (Nat.add_le_add (show separation k v ≤ 9 from (Nat.le_of_mul_le_mul_left (le_trans hc (by omega)) L.property)) (show separation k t≤5 from ?_)).trans (by norm_num); change separation s o ≤ _ at hp; omega
abbrev ηtag (G:Ratio c f)(A:Site f)(t: Mill): Single c:= stickW (endLoc G A t.1) t.2
abbrev Λw (o:Skye.Seat f)(i: Single f):= Ladder (μPose o i)
lemma tag_spend (e:Odd G.count.val)(o:Skye.Seat f)(i: Mill): 1+(separation (node (ηtag G (AnchorN o) i).1.1) (downT G o):ℝ) ≤ 24* Ladder i.1:=by
 let A:=AnchorN o; let K:= deckLoc G A; let V:=endLoc G A i.1; let f:=separation (node V) (downT G o); have hp: f ≤ 2*lateral i.1+19:=by
    apply (separation_triangle (node V) (node K) (downT G o)).trans; rw [Hove.ζdist]; refine Nat.add_le_add (Nat.mul_le_mul_left 2 ?_) (jump_leV e o); unfold V K separation endLoc; rw [add_sub_cancel_left]; exact wrap_month _
 change 1+(f:ℝ)≤24*(1+lateral i.1); exact_mod_cast (show 1+f≤24*(1+lateral i.1) from by omega)
lemma seal_tag (A: Site f) (z:Mill)(v:Single c):ηtag G A z=v↔ endLoc G A z.1=v.1.1 ∧ z.2=portB v:=by
 constructor
 · rintro rfl; exact ⟨rfl,rfl⟩
 rintro ⟨p,h⟩; unfold ηtag; rw [p,h]
abbrev Event (G:Ratio c f)(A: Site f)(x:Single c)(y:Mill):ℂ:= if ηtag G A y=x then Rush.wind (deckLoc G A) y.1 else 0
abbrev bowling (G:Ratio c f)(A:Site f)(X: Mill→ℂ)(y: Single c) := ∑' v:Mill, Event G A y v * X v
lemma event_origin (G:Ratio c f)(A:Site f)(x:Single c)(y:Mill):star (Event G A x y)=Event G A x y∧ ‖Event G A x y‖≤1:=by
 unfold Event; split; exact ⟨Rush.fee_real _,(fee_norm _).le⟩; simp
lemma Ev_sum' (A:Site f)(V:Mill→ℂ)(v: Summable fun i=>‖V i‖) (x:Single c) : Summable fun i=> ‖Event G A x i * V i‖:=by
 apply Summable.of_nonneg_of_le _ _ v; · exact fun i=>norm_nonneg _
 intro i; rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (event_origin _ _ _ _).2
-- period
lemma point_tag (u : Honed G.count M b (Y b) (σ b))(e:Odd G.count.val)(p:0<Y b)(s:0<σ b)(v:Use 4 G.count T)(x:Single c)(i: Single f): bowling G (AnchorN o) (Θfull M G o b i) x=Caller o i.1.1 * lensF G e T 4 b M i x:=by
 let j:= i.1.1; let A:=AnchorN o; let Z:= μPose o i; let a:= portB i; let V:=Θfull M G o b i; let n:=x.1.1; let b':=portB x
 have hx:Tap.plot (stickW A a) Z=i:=by unfold Tap.plot; change ((A+wrap _ Z,a.1),a.2)=_; rw [show wrap _ Z=_ from (wrap_lift (j-A)), add_sub_cancel]
 rw [show Caller o i.1.1 * lensF G e T 4 b M i x= flute G e T 4 b M A a Z x from ?_, naive u p s e A T v Z a x] -- tune order
 · unfold bowling; let K (i:Mill):=Event G A x i *V i; change (∑' i:Mill,K i)=_; have hs: Summable fun i=>‖V i‖:=by have he:= (SB_paws u p s A Z a 0).2.1; simp_rw [wl0,one_mul] at he; exact he
   have hz: Summable K := (Ev_sum' A V hs x).of_norm; rw [hz.tsum_prod]; refine tsum_congr fun i'=>?_ ; rw [tsum_fintype,sum_eq_single b'];
   · unfold K Event; split_ifs with t h z
     · rfl
     · have hE:=(seal_tag ..).1 t; exact False.elim (h hE.1)
     · exact False.elim (t ((seal_tag ..).2 ⟨z,rfl⟩)) -- tune hyp names
     exact zero_mul _
   · intro k _ h; unfold K Event; rw [if_neg (fun w=>h ((seal_tag ..).1 w).2),zero_mul]
   simp
 unfold flute; rw [hx]
end Boom
end YM.CF.TableF
end
