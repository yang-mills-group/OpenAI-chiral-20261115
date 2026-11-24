import YM.CF.BProof.Hero.Route
import YM.CF.BProof.Mark.CoverX
/-! Mark N pairs exact collar H, ramp, then X_H. These functions used after B-PfM as well. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mark
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {s c:Side}(a:Per s)(l:ℕ)(S: Hall s)(g:Ratio c s)(U:Bkg s)(b:Eyes s)
def breath (x:Site s):ℝ := lung ((chip a l x:ℝ)/l)
lemma breath_u (x:Site s): breath a l x ∈Zone:= easeZ _
lemma breath_left {x:Site s}(p:chip a l x*10 ≤ l)(t:0<l): breath a l x=1:=by apply lung_b; rw [div_le_iff₀ (Nat.cast_pos.mpr t)]; linarith [show (chip a l x:ℝ)*10≤(l:ℝ) by exact_mod_cast p]
lemma breath_right{x:Site s}(p:l≤ chip a l x*6)(t:0<l): breath a l x=0:=by apply lung_z; rw [le_div_iff₀ (Nat.cast_pos.mpr t)]; linarith [show (l:ℝ)≤ (chip a l x:ℝ)*6 by exact_mod_cast p]
lemma breath_bounded (W:0<l)(e:2*l<s.val){x y:Site s}(v:x∈Aisle a l)(t:y∈Aisle a l): |breath a l x-breath a l y| ≤rateH*(separation x y:ℝ)/l:=by
 have h:0<(l:ℝ):= Nat.cast_pos.mpr W; let f(x:Site s):ℝ:= ↑(chip a l x)/l; have hh(x): f x∈Zone:= by refine ⟨?_, (div_le_iff₀ h).2 ?_⟩; unfold f; positivity; rw [one_mul]; exact_mod_cast (show chip a l x≤l from (min_le_right ..).trans (Nat.sub_le ..))
 apply le_trans (expenses.lungw _ (hh x) _ (hh y)); rw [Real.dist_eq,mul_div_assoc]; apply mul_le_mul_of_nonneg_left _ rate_p.le; unfold f; rw [←sub_div, abs_div, abs_of_pos h]; apply div_le_div_of_nonneg_right _ h.le; rw [abs_le]; constructor
 · have hv : (chip a l y:ℝ)≤ chip a l x+(separation x y:ℝ):=by exact_mod_cast chip_le a l v t e
   linarith
 have hv : (chip a l x:ℝ)≤ chip a l y+(separation x y:ℝ):=by rw [separation_comm]; exact_mod_cast chip_le a l t v e
 linarith
-- Mark bra fields paths

def HN (x:Site s) : ℝ→Stamp := if x∈ BeltL a l then motion (gown a l U b x)⁻¹ ∘ BM (breath a l x) else fun _=> Pair.fullM (XN a l S g U b x).val
lemma HN_bead (W:Site s→E)(x:Site s): HN a l S g (Lattice.gauge W U) (b*(eye a l W)⁻¹) x=motion (W x) ∘ HN a l S g U b x:=by
 ext1 t; simp only [HN,Function.comp_apply]; split_ifs; rw [gown,Angular.stage_rot,Pi.mul_apply,Pi.inv_apply,mul_inv_rev,inv_inv]; exact motion_seq ..; rw [XN_bead]; exact (compass ..).symm
lemma HN_here(W:Bkg s){x:Site s}(u:2*l<s.val)(hW:Width g l)(p:4≤c.val)(h:Agrees (Aisle a l) U W)(hx:x∈ Aisle a l): HN a l S g U b x=HN a l S g W b x:=by
 unfold HN; split_ifs; unfold gown; rw [stage_local a l U b (by unfold Width at hW; omega) W h hx]; rw [XN_here a l S g U b W u hW p h hx]
scoped instance : MeasurableSpace Stamp:=borel _
scoped instance : BorelSpace Stamp :=⟨rfl⟩
lemma HN_m (t:ℝ): Measurable (fun p:Street s=> fun x=> HN a l S g p.1 p.2 x t):=by
 apply measurable_pi_lambda; intro i; unfold HN; split_ifs
 · let f: Site s→ E→ Stamp:= fun i u=>motion u⁻¹ (BM (breath a l i) t); have he: Continuous (f i):= by unfold f motion congrC; have h:Continuous (fun g:E=> (matter g⁻¹).val):= matter_cont.comp continuous_inv; exact (h.mul continuous_const).mul h.matrix_transpose -- tune
   -- refactor
   --
   exact he.measurable.comp ((measurable_pi_apply (X:=fun _:Site s=>E) i).comp (stage_m a l).measurable)
 exact Pair.full_cont.measurable.comp (f:=fun p:Street s=>(XN a l S g p.1 p.2 i).val) ((continuous_subtype_val (p:=fun x:Vect=> x∈Sphere)).measurable.comp ((measurable_pi_apply (X:=fun _:Site s=>Ballot) i).comp (XN_m a l S g))) -- tune sphere
lemma HN_money (x:Site s): Money (HN a l S g U b x):=by unfold HN; split_ifs; exact (moneyB (breath_u ..)).pile _; exact quietM _ (sealX _ (vote_unit _))
lemma HN_deep {x:Site s}(v:breath a l x=0)(t:ℝ): HN a l S g U b x t=Pair.fullM (XN a l S g U b x).val:=by unfold HN; split_ifs with h; rw [Function.comp_apply,v,BM_0, compass,XN_rim _ _ _ _ _ _ h]; rfl; rfl
lemma HN_first(x:Site s): HN a l S g U b x 0=Pair.fullM (XN a l S g U b x).val:=by unfold HN; split_ifs with h; rw [Function.comp_apply,BM_x,XN_rim _ _ _ _ _ _ h]; exact compass ..; rfl
lemma HN_rim {x:Site s}(h:x∈BeltL a l) : HN a l S g U b x=motion (gown a l U b x)⁻¹ ∘ BM (breath a l x):=if_pos h
lemma HN_close {x:Site s}(W: Width g l)(v:chip a l x*10≤l)(p:x∈Aisle a l) : HN a l S g U b x= motion (gown a l U b x)⁻¹ ∘ BM 1:=by unfold Width at W; rw [HN_rim _ _ _ _ _ _ ⟨p,by unfold life; omega⟩,breath_left a l v (by omega)]
-- motion & consistency. compare both belt nodes internal to belt; or near join at zero.
lemma skinH (x:Site s)(i:Axis)(B:Bkg s)(A:Site s→E)(v w:Stamp):
    ‖motion (B (x,i)) (motion (A (x+step i))⁻¹ v) - motion (A x)⁻¹ w‖= ‖motion (Lattice.gauge A B (x,i)) v-w‖:=by
 rw [←motion_frame (A x),←motion_seq,←motion_seq,←motion_seq, mul_inv_cancel,motion_one,id_eq]; rfl
variable {y r m v q:ℝ}(W:Width g l)(h:2*l<s.val)(f:Facing a l S U b g y r m)
include W h f
abbrev Hbudget (l:ℕ)(y:ℝ) := rateH*(rateH/l)+2*xm*(allowance y+xi y)
lemma HN_fast (e:PaceX (Aisle a l) U (XN a l S g U b) q)(v:ℝ)(he:∀ (x y:Ballot), Xd x y≤q→ ‖Pair.fullM x.val-Pair.fullM y.val‖≤v)
 (ht:Hbudget l y≤v)(t:ℝ)(hc:t∈TimeR): SkinH (Aisle a l) U (fun x=> HN a l S g U b x t) v := by
 let X:=XN a l S g U b; let V:=gown a l U b; have hu:200*g.count.val+200≤l:=W; have hr:0<l:=by omega
 intro x i p u; set Y:=x+step i; change Y∈Aisle a l at u; let A:=breath a l; let Z(x):=BM (A x) t; dsimp only
 by_cases z: x∈BeltL a l ∧ Y∈BeltL a l
 · rw [HN_rim _ _ _ _ _ _ z.1,HN_rim _ _ _ _ _ _ z.2]; apply le_trans _ ht; unfold Hbudget; change ‖motion (U (x,i)) (motion (V _)⁻¹ (Z _))-motion (V x)⁻¹ (Z x)‖≤_
   rw [skinH]; let G:=Lattice.gauge V U (x,i); have hg:G∈Set.univ:=trivial; calc
     _ = ‖motion G (Z Y)-motion 1 (Z x)‖:=by rw [motion_one,id_eq]
     _ ≤ _:= by
       have he: ‖Z x‖≤1:= (CStarRing.norm_of_mem_unitary (BM_seal ..).norm).le; apply le_trans (Hero.seat_co G 1 _ _ he); rw [mul_one]; apply add_le_add
       · have he:separation Y x ≤1:=by unfold Y; rw [separation_comm,← Hero.slide4, ←Hero.Way]; exact Grid.near_slide ..
         refine (expenses.BMw.horizon (breath_u a l Y) hc (breath_u ..)).trans (mul_le_mul_of_nonneg_left ((breath_bounded a l hr h u p).trans ?_) rate_p.le); rw [separation_comm Y x] -- may want separation Y x vs he; tune
         exact div_le_div_of_nonneg_right (mul_le_of_le_one_right rate_p.le (by exact_mod_cast ((separation_comm x Y).trans_le he))) (Nat.cast_pos.mpr hr).le
       exact mul_le_mul_of_nonneg_left (by rw [cd_symm,cd_one]; exact price_belt a l S U b g W h f x i (belt_in a g l z.1) (belt_in a g l z.2)) (mul_nonneg zero_le_two xm_p.le)
 have hp:= approach a l x i p u h; push Not at z; have hh:l ≤ chip a l x*6∧ l ≤ chip a l Y*6:=by
   change chip a l Y≤chip a l x+1∧ _≤chip a l Y+1 at hp; by_cases g:x∈BeltL a l; have hg:= accord a l u (z g); omega; have hg:= accord a l p g; omega
 rw [HN_deep _ _ _ _ _ _ (breath_right a l hh.2 hr) t,HN_deep _ _ _ _ _ _ (breath_right a l hh.1 hr) t,compass]; exact he (scaledV (U (x,i)) (X Y)) (X x) (e x i p u)
end YM.CF.BProof.Mark
