import YM.CF.BProof.Mark.Collar
/-! Fundamental extension needed for N Mark. Specify values near both ends.
Perform in `V` coordinates. Read before moving out of gauge at end.
No request for slow through seam at the nontrivial label frame. Use overlap cells.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mark
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {s c:Side}(a:Per s)(l:ℕ)(S: Hall s)(g:Ratio c s)(U:Bkg s)(b:Eyes s)
def seed (x:Site s): Ballot:=scaledV (gown a l U b x)⁻¹ apex
def plot (x: Site s):Ballot:= if x∈ room a g l then scaledV (V a l S U b x) (seed a l U b x) else apex
def XN₀ (x:Site s): Ballot:=year a g l (hall a l S U b) (plot a l S g U b) x
def XN (x:Site s): Ballot:= scaledV (V a l S U b x)⁻¹ (XN₀ a l S g U b x)
lemma XN_rim {x:Site s}(h:x∈ BeltL a l): XN a l S g U b x=seed a l U b x:=by rw [XN,XN₀,turn_year _ _ _ _ _ _ h,plot,if_pos (belt_in ..),←scaled_seq, inv_mul_cancel,scaled_one,id_eq]; exact h
lemma XN_bead (W:Site s→ E) : XN a l S g (Lattice.gauge W U) (b*(eye a l W)⁻¹)= fun x=> scaledV (W x) (XN a l S g U b x):=by
 have he:plot a l S g (Lattice.gauge W U) (b*(eye a l W)⁻¹) =plot a l S g U b:=by
    ext1 x; unfold plot seed gown; split_ifs; swap; · rfl
    rw [V_rot,stage_rot]; simp only [Pi.mul_apply, Pi.inv_apply,mul_inv_rev,inv_inv,←scaled_seq]; rw [show (V a l S U b x*(W x)⁻¹)*(W x * (Angular.stage a l U b x)⁻¹) = V a l S U b x *(Angular.stage a l U b x)⁻¹ from by group]
 ext1 x; unfold XN XN₀; rw [he,hall_rot,V_rot]; simp only [Pi.inv_apply,Pi.mul_apply, mul_inv_rev,inv_inv, scaled_seq]
lemma V_read (W:Bkg s)(t:l+1<s.val)(h:Agrees (Aisle a l) U W) : Set.EqOn (V a l S U b) (V a l S W b) (Aisle a l):=by unfold V; rw [show sight a l S U b=sight a l S W b from funext fun i=>congrArg (fun A:BProof.Face.Sheet s=>BProof.Face.smooth S.g S.X S.k A (b i)) (local_inlet a l U i (by omega) W h)]; exact stage_local a l U (sight a l S W b) t W h -- tune
lemma seed_read(W:Bkg s)(t:l+1<s.val)(h:Agrees (Aisle a l) U W):Set.EqOn (seed a l U b) (seed a l W b) (Aisle a l):= by
 intro x hx; unfold seed gown; rw [stage_local a l U b t W h hx]
lemma XN_here(W:Bkg s)(u:2*l<s.val)(hW:Width g l)(p:4≤c.val)(h:Agrees (Aisle a l) U W):Set.EqOn (XN a l S g U b) (XN a l S g W b) (Aisle a l):= by
 have hP:=hW; unfold Width at hP; have hv:l+1<s.val:=by omega
 have he:=V_read a l S U b W hv h
 intro x hx; unfold XN; rw [he hx]; apply congrArg (scaledV _); refine year_here a g l (hall a l S U b) (hall a l S W b) _ _ x hx u p hW (fun y hy=>?_) ?_
 · unfold plot; split_ifs; rw [he (show y∈ _ from hy.1), seed_read a l U b W hv h (show y∈ _ from hy.1)]; rfl
 exact fun i ai b'=> hall_local a l S U b hv W h i ai.1 b'.1 -- name shadow

-- joint meas.
abbrev Street (s: Side):= Bkg s× Eyes s
lemma seed_m:Measurable (uncurry (@seed s a l)):=by
 apply measurable_pi_lambda; intro x; let f(p:Street s):= gown a l p.1 p.2 x; have h : Measurable f:=(measurable_pi_apply (X:=fun _ : Site s=> E) x).comp (stage_m ..).measurable; exact scaled_cont.measurable.comp (f:=fun p:Street s=>( (f p)⁻¹, apex)) (h.inv.prodMk measurable_const)
lemma plot_m:Measurable (uncurry (plot a l S g)):=by
 apply measurable_pi_lambda; intro x; unfold plot uncurry; dsimp only; split_ifs; exact scaled_cont.measurable.comp (f:=fun p:Street s=>(V a l S p.1 p.2 x,seed a l p.1 p.2 x)) (Measurable.prodMk ((measurable_pi_apply (X:=fun _:Site s=> E) x).comp (V_m a l S)) ((measurable_pi_apply (X:=fun _:Site s=>Ballot) x).comp (seed_m a l))); exact measurable_const -- tune shape
lemma XN_m:Measurable (uncurry (XN a l S g)):=by
 apply measurable_pi_lambda; intro x; let Y:=uncurry (XN₀ a l S g); have h:Measurable Y:= (year_m a g l).comp (f:=fun p:Street s=>(hall a l S p.1 p.2,plot a l S g p.1 p.2)) ((hall_m a l S).prodMk (plot_m a l S g)); exact scaled_cont.measurable.comp (f:=fun p:Street s=>( (V a l S p.1 p.2 x)⁻¹, XN₀ a l S g p.1 p.2 x)) ((((measurable_pi_apply (X:=fun _:Site s=> E) x).comp (V_m a l S)).inv).prodMk ((measurable_pi_apply (X:=fun _:Site s=>Ballot) x).comp h))
-- costs
variable {y r m:ℝ}(W:Width g l)(h:2*l<s.val)(f:Facing a l S U b g y r m)
include f W h
lemma seedP : PaceX (room a g l) U (seed a l U b) (xm*(allowance y+xi y)):=by
 let F:=gown a l U b; let A:= seed a l U b; let C:=Lattice.gauge F U; apply (pace_move _ U F).1; intro x i hx hl; have he(x): scaledV (F x) (A x)=apex:=by unfold A seed; rw [←scaled_seq,show F x*(gown a l U b x)⁻¹=1 from mul_inv_cancel _,scaled_one,id_eq] -- tune `pace_move` direction scope under want
 let B:= C (x,i); change ‖turn B (scaledV _ (A _)).val- (scaledV _ (A _)).val‖≤_; rw [he, he]; calc
   _ =Xd (scaledV B apex) (scaledV 1 apex):=by rw [scaled_one]; rfl
   _ ≤ xm*cd group B 1:= Xd_rate ..
   _ ≤ _:=mul_le_mul_of_nonneg_left (by rw [cd_symm, cd_one]; exact price_belt a l S U b g W h f x i hx hl) xm_p.le
lemma XN_pace (t:4≤c.val)(v:ℝ)(e:can v g.count)(p:xm*(allowance y+xi y)≤ prie g.count)(u:prie g.count≤v) : PaceX (Aisle a l) U (XN a l S g U b) v:=by
 let F:=V a l S U b; let G:=hall a l S U b; let B:= room a g l; let A(x:Site s):= scaledV (F x) (seed a l U b x); have hp: PaceX B G A (prie g.count):=(pace_move _ U _).2 (pace_sub _ _ (seedP a l S g U b W h f) (Set.Subset.refl _) p); let L:=plot a l S g U b; have hv: PaceX B G L (prie g.count):=by intro x i hx q; specialize hp x i hx q; convert hp using 1; unfold L EdgePrice plot; dsimp only; rw [if_pos hx,if_pos q] -- tune
 apply (pace_move _ U F).1; rw [show (fun x=>scaledV (F x) (XN a l S g U b x))=XN₀ a l S g U b from ?_]; swap; · ext1 x; unfold XN; rw [← scaled_seq,show F x * _=1 from mul_inv_cancel (F x),scaled_one,id_eq]
 have hW:= W; unfold Width at hW; apply year_paid a g l G L v e W h t u hv; apply calf a l G (by omega) (tip g.count) (tip_pos _).le; exact cast (calm_move a l U _ F) f.roof
end YM.CF.BProof.Mark
