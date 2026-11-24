import YM.CF.BProof.Mark.Pairs
/-! Purchase inequalities. Width prices keep separate to use in Geometry. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mark
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
-- tunable speed H; choose extremely low interior speed v', think u = global target/Pearl; qH' = Core unit.
structure Herald (u v:ℝ) where
 whole : Side -- size general
 body : Side -- Mark
 yC : ℝ -- X speed target
 good : ℝ -- unextended on safe set
 ready : ℝ -- unextended Mark pace total
 calm : ℝ
 gold : 0<ready
 gold_le : ready ≤ good
 safe : good≤ yC
 y_small : yC < u
 energy : v>0
 grant : ∀ (x y:Ballot), Xd x y ≤ yC → ‖Pair.fullM x.val-Pair.fullM y.val‖ ≤ v
 whole_can : can yC whole
 body_can : can ready body
 caution : 0<calm
 ally : xm*calm ≤ tip whole
 genie : good≤prie whole
 lt_p : prie body≤ready
namespace Herald
variable {u v:ℝ}(H:Herald u v)
include H in
lemma uf : 0<v:= H.energy
lemma yc : 0<H.yC:=H.gold.trans_le (H.gold_le.trans H.safe)
lemma gc : 0<H.good:= H.gold.trans_le H.gold_le
lemma surface(F : Ballot)(x:Ballot)(h:Xd F x≤ H.ready): ‖Pair.fullM F.val-Pair.fullM x.val‖≤v:= H.grant F x (h.trans (H.gold_le.trans H.safe))
theorem buys (p:0<u)(e:0<v): Nonempty (Herald u v):=by
 obtain ⟨q,h,H⟩:= Hero.full_o v e; let a:= min q (u/2); have ha:=lt_min h (half_pos p); change 0<a at ha
 obtain ⟨P,hP⟩:= buyX a ha; let b:= min a (prie P); have hb:=lt_min ha (show 0<prie P from by unfold prie; positivity); obtain ⟨Q,hQ⟩:= buyX (b/4) (by change 0<b at hb; positivity)
 let d:= tip P / xm; have hx:= xm_p; refine ⟨P,Q,a,b,b/4,d,(div_pos hb (by norm_num)),(div_le_self hb.le (by norm_num)),min_le_left ..,(min_le_right ..).trans_lt (half_lt_self p),e,(fun x y h=> H x y (h.trans (min_le_left ..))),hP,hQ,(div_pos (tip_pos _) hx),?_, min_le_right ..,?_⟩
 · rw [show xm*d=tip P from by unfold d; field_simp]
 have hp : 1≤ XF.pay 4:= XF.pay_m (show 0≤4 by norm_num); exact le_trans (div_le_div_of_nonneg_right hp (show 0≤(Q.val:ℝ) by positivity)) hQ
variable {s c:Side}(a:Per s)(l:ℕ)(S: Hall s)(g:Ratio c s)(U:Bkg s)(b:Eyes s)(y:ℝ)
structure Warm (H:Herald u v)(l:ℕ)(y:ℝ) : Prop where
 length : 200* H.body.val+200≤l
 pace : xm*(allowance y+xi y)≤prie H.body
 moveH : Hbudget l y ≤ v
 tip_body : thresh y/2≤ tip H.body
lemma grabs (F:ℝ→ℕ)(h:Tendsto F atTop atTop): ∀ᶠ y in atTop, Warm H (F y) y:=by
 have ha:Tendsto allowance atTop (nhds 0):= coin_purchases (by norm_num); have hb:Tendsto xi atTop (nhds 0):= coin_purchases (by norm_num); have hv:Tendsto thresh atTop (nhds 0):=coin_purchases (by norm_num)
 have x:Tendsto (fun y=>xm*(allowance y+xi y)) atTop (nhds 0):=by simpa using (ha.add hb).const_mul xm
 have z:Tendsto (fun y=> Hbudget (F y) y) atTop (nhds 0):=by
    have e:= @tendsto_natCast_atTop_atTop ℝ; let A:= F; have he : Tendsto (fun y:ℝ=> (F y:ℝ)⁻¹) atTop (nhds 0):= tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp h); unfold Hbudget; simpa only [_root_.div_eq_mul_inv, mul_zero,zero_add] using ((he.const_mul _).const_mul rateH).add ((ha.add hb).const_mul (2*xm))
 filter_upwards [h.eventually_ge_atTop _,x.eventually (ge_mem_nhds (show 0<prie H.body from by unfold prie; positivity)),z.eventually (ge_mem_nhds H.uf), hv.eventually (ge_mem_nhds (show 0<2*tip H.body from mul_pos (by norm_num) (tip_pos _)))] with y hp he hk hl
 exact ⟨hp,he,hk,by change thresh y ≤ _ at hl; linarith⟩
-- Facing hypotheses follow from full fit; pack core Marker band tests
variable {r m:ℝ}
include H
lemma ticketN (t:g.count=H.body)(x:2*l<s.val)(p:4≤ c.val)(h: Warm H l y)(e: Facing a l S U b g y r m):
      Width g l ∧ PaceX (Aisle a l) U (XN a l S g U b) H.ready ∧ ∀ t∈ TimeR, SkinH (Aisle a l) U (fun x=> HN a l S g U b x t) v := by
 have hv: Width g l:= by rw [Width,t]; exact h.length
 have hp := XN_pace a l S g U b hv x e p _ (t ▸ H.body_can) (t ▸ h.pace) (t ▸ H.lt_p); exact ⟨hv, hp, fun t ht=> HN_fast a l S g U b hv x e hp _ H.surface h.moveH _ ht⟩ -- tune param order
end Herald
section
variable {u v:ℝ}(H:Herald u v) {s:Side}(p:Site s)(a:Bond s)(A:Bkg s)
-- D certificate. keep post registration upper bounds cd to identity from true D tests. eventually.
def Ground(K:ℝ)(U:Bkg s)(S:Set (Site s)): Prop:=∀ (i:Bond s),i.1∈S→ i.1+step i.2 ∈ S→ SU.group.chord (U i) ≤ K
lemma grounds(K: Chart SU.group) : ∃ C:ℝ,0<C∧ ∀ᶠ y:ℝ in atTop, ∀ {s:Side} (e:Bond s), cd SU.group 1 (mag y e)≤ C*aA y := by obtain ⟨C,hc,H⟩:= Mag.pay K; refine ⟨C,hc,?_⟩; filter_upwards [H] with y H; intro s e; rcases Angular.whichBond e with ⟨x,p,rfl⟩|⟨x,p,j,rfl⟩; rw [mag_v,cd_self]; exact (mul_pos hc (coin_pos ..)).le; exact H.1 _ -- careful j
-- budgets D deterministic known parameter ≤, following gap can include constant orientation. 
lemma formsD_X (v z:ℝ)(S:Set (Site s))(p:Ground z A S)(u:xm*z ≤ v): PaceX S A (fun _=>apex) v:=by
 intro x i hx ht; let q:=A (x,i); apply le_trans _ u; change ‖turn q apex.val-apex.val‖≤_; have e':Xd (scaledV q apex) (scaledV 1 apex)=‖turn q apex.val-apex.val‖:=by rw [scaled_one]; rfl
 exact e' ▸ ((Xd_rate q 1 apex).trans (mul_le_mul_of_nonneg_left (by rw [cd_symm,cd_one]; exact p _ hx ht) xm_p.le)) -- tune
lemma formsD_H (t u z:ℝ)(S:Set (Site s))(p:Ground z A S)(v:2*xm*z ≤ u): SkinH S A (fun _=> BM 1 t) u:=by
 intro x i hx ht; let a:=A (x,i); let V:=BM 1 t; apply le_trans _ v; have hg:‖V‖≤1:=(moneyB z1).weight t|>.le; have he:=seat_rate a 1 V hg; rw [motion_one,id_eq,mul_one,cd_symm,cd_one] at he; exact he.trans (mul_le_mul_of_nonneg_left (p _ hx ht) (mul_nonneg zero_le_two xm_p.le))
end
end YM.CF.BProof.Mark
