import YM.CF.BPress.Meadow.June
import YM.CF.BPress.Hanger
import YM.CF.BPress.Wealth.Regime
/- eq:B-cost paths Mark prescription paid separately from the integration patches. Budget pointwise on all accepted fields. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Meadow
open Function Finset Filter NormedSpace Metric SU SU.Pair Mesa Fock Lattice Cube Lat Spin Spin.Paint Dial Grid Grid.Entity Delivery Lute Lute.Kite Lute.Fort MeasureTheory Net Tent Sheet Frame Lute.Music Pressure
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {s:Side}{T:Sheet.Atlas}{L y C C':ℝ}{b:ℕ} (W:Tunnel s)(F:Net s T L y C C' b)(U:Micro s)(p:Duo s)(k:Tiling s){v u q:ℝ}
structure Clue {s:Side}(S:Support s)(H:marks s)(F:ℝ→ Paint s) : Prop where
 scheme(t):MatPlan (F t)
 station(t:ℝ)(h:1≤t): F t=F 1
 origin(x): F 0 x=fullM (H x).val
 smooth (x): ContDiff ℝ ∞ (fun t=>F t x)
 pace(x): LipschitzOnWith κ_theme (fun i=> F i x) Meadow.active
structure Grains {s:Side} (S:Support s)(U:Micro s)(H:marks s)(F:ℝ→ Paint s)(r v:ℝ):Prop where
 grow: Alert U S H r
 timing (x:ℝ)(u:x∈Meadow.active)(i)(p:i ∈ inside S): fare U (F x) i ≤ v

lemma rocksN : Clue W.mem (sprigs W F U p k) (whole W F U p k):= ⟨whole_spec W F U p k,fun _ h=> stationary_W W F U p k _ h, beginning_whole W F U p k,whole_smooth W F U p k,price_W W F U p k⟩ -- tune
lemma fun_stand (s:Side)(A:SU.Sheet): True:= trivial

def Poses (r: Side)(t v:ℝ):Prop:= inheritance r ≤ t ∧ κ_tri * inheritance r≤v
lemma seed_capacity (t v:ℝ)(p:0<t)(w:0<v):∃ r:Side,Poses r t v:=by
 let l:ℝ:=1+κ_tri; have hl:0<l:=by unfold l; positivity
 obtain ⟨k,h⟩:= find_s (lt_min p (div_pos w hl)); refine ⟨k,h.slow.trans (min_le_left ..),?_⟩; apply (mul_le_mul_of_nonneg_left (h.slow.trans (min_le_right ..)) κ_tri.property).trans; exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (show (0:ℝ) ≤ 1 by norm_num)) (div_nonneg w.le hl.le)).trans_eq (mul_div_cancel₀ _ hl.ne')
lemma period_N (T:Sheet.Atlas)(G:GapSize)(t v C C':ℝ)(r:Side)(u:Poses r t v)(q:0<v)(hc:0<C)(hc':0<C'): ∀ᶠ L in atTop,∀ᶠ y:ℝ in atTop,∀(s:Side)(J: Record r s)(b:ℕ)(F:Net s T L y C C' b)(X:Bands s (G.select y))(i:X.Index)(U: Micro s)(p:Duo s),let W:= X.mark i; p∈ T.pairs y (W.reads U)→ markN F W U p≠0 →Launch W F U p J.key∧Grains W.mem U (sprigs W F U p J.key) (whole W F U p J.key) t v:=by
 have hx: NPL amt:=(npl_xi.add npl_sigmaN); let f(y):= ((G.select y).marked.val:ℝ); have he :Tendsto (fun i:ℝ=> (κ_theme:ℝ)*(f i)⁻¹+(2*sphereRate)*amt i) atTop (𝓝 0):=by simpa only [f, Function.comp_apply, mul_zero,add_zero] using ((tendsto_inv_atTop_zero.comp G.marked_late).const_mul (κ_theme:ℝ)).add (hx.drop.const_mul (2*sphereRate))
 let R₀:= 80*r.val+80; filter_upwards [flags_N G T C C' hc hc'] with L h; filter_upwards [h.2,T.coasts_y,(hx.const_mul sphereRate).drop.eventually (ge_mem_nhds (inv_pos.mpr (nPos r))), he.eventually (ge_mem_nhds q), npl_temp.drop.eventually (ge_mem_nhds (show 0 < climate r from by unfold climate; positivity)), G.marked_late.eventually_ge_atTop (R₀:ℝ), eventually_gt_atTop (0:ℝ)] with y hb e η hL Z w v' s J b F X i U p; intro W m n
 have ht:(X.mark i).n.val=W.n.val:=rfl; have hy:R₀ ≤ W.n.val:=by exact_mod_cast w
 have hz:30≤ W.n.val:=by unfold R₀ at hy; omega
 have hd: Launch W F U p J.key:=⟨⟨v',e,m,n,by omega⟩,rfl,by have hT:J.key.R=r.val:=J.K; unfold ward Tent.body cloakT Tunnel.lips; unfold R₀ at hy; omega, fun i' t=>(hb _ _ F X i U p m n i' t).trans ((half_le_self (BPress.temp_pos v').le).trans Z) ,η⟩ -- placeholders
 refine ⟨hd,fun k p=> (sprigs_urgent W F U _ _ hd k p).trans u.1,fun r t x T=> (price_Z W F U _ _ hd hz r t x T).trans (max_le hL u.2) ⟩ -- tune
lemma dayH (x:Site s):True:=trivial
abbrev day(s:Side)(x:ℝ):Paint s:= fun _=> theme (0,x)
lemma day_plan (S:Support s) : Clue S (headS s) (day s):=by
 refine ⟨fun u x=> theme_v _,fun x h=>funext (fun _=>theme_exit h _),fun _=> theme_entry 0,fun x=> theme_s.comp (f:=fun x=>(0,x)) (by fun_prop), fun i => ?_⟩; apply LipschitzOnWith.of_dist_le_mul; intro x h y t; apply (Meadow.charge.choose_spec.dist_le_mul (0,x) ⟨H0,h⟩ (0,y) ⟨H0,t⟩).trans_eq; simp [κ_theme]
lemma day_storm (r v:ℝ)(p:0<r)(u:0<v):∀ᶠ y:ℝ in atTop,∀ (s:Side)(W:Support s)(U:Micro s), (BPress.dirichlet W y U)≠0 → Grains W U (headS s) (day s) r v:=by
 obtain ⟨B,hb,H⟩:=Wealth.base_call; have h:NPL (fun y=>xi y+B*aA y):= npl_xi.add (npl_aA.const_mul B); let P:=2*sphereRate; filter_upwards [H,(h.const_mul sphereRate).drop.eventually (ge_mem_nhds p),(h.const_mul P).drop.eventually (ge_mem_nhds u)] with y e f g s W U n; have hx(i:Link s)(t:i∈inside W):chord (U i) 1≤ xi y+B*aA y:= (chord.triangle _ (background y i) _).trans (add_le_add (on_ball W y U n _ ((inside_iff ..).mp t).1 ((inside_iff ..).mp t).2) ((chord.one _).le.trans (e _)))
 constructor; · intro i t; change dist (scaledV (U i) Seed) Seed≤ _; apply le_trans ?_ f; nth_rw 2 [← scaled_one Seed]; exact (scaled_chord ..).trans (mul_le_mul_of_nonneg_left (hx i t) sphereRate_cost.positive.le)
 intro x a i l; have hp:=fare_plain U (day s x) i; unfold day at hp; simp only [sub_self,norm_zero,norm_κ (theme (0,x)) (theme_v _),mul_one,zero_add] at hp; exact hp.trans ((mul_le_mul_of_nonneg_left (hx _ l) (mul_nonneg (by norm_num) sphereRate_cost.positive.le)).trans g)
namespace Stamps
open Bands
variable {B:BandWidth}(X:Bands s B)(i:X.Index)
def plant: marks s:= if i∈X.dc then headS s else sprigs (X.mark i) F U p k -- parameter order auto tune
-- relative orientation used in eq:B-Madd
def brush : ℝ→Paint s:= if i∈X.dc then day s else whole (X.mark i) F U p k
lemma paid : Clue (X.band i) (plant F U p k X i) (brush F U p k X i):=by
 unfold plant brush; split; exact day_plan _; exact rocksN (X.mark i) F U p k
lemma plant_m : Measurable fun u:Micro s × Duo s=> plant F u.1 u.2 k X i:=by unfold plant; split; exact measurable_const; exact sprigs_m ..
lemma brush_m (x:ℝ) : Measurable fun u:Micro s× Duo s=>brush F u.1 u.2 k X i x:=by unfold brush; split; exact measurable_const; exact measurable_pi_lambda _ (fun i=>whole_m _ _ _ _ _)
lemma follows (a:Mach s)(f:i∈X.nc): Set.EqOn (plant F (gauge a U) (p*((X.mark i).framesE a)⁻¹) k X i) (shuffle a (plant F U p k X i)) (X.band i)∧ ∀ v:ℝ, Set.EqOn (brush F (gauge a U) (p*((X.mark i).framesE a)⁻¹) k X i v) (rotateC a (brush F U p k X i v)) (X.band i):=by unfold plant brush; rw [if_neg (mem_sdiff.mp f).2, if_neg (mem_sdiff.mp f).2,if_neg (mem_sdiff.mp f).2,if_neg (mem_sdiff.mp f).2]; exact ⟨gauge_sprigs ..,fun _=> gauge_whole ..⟩
lemma roots(V:Micro s)(h:Lattice.Agrees (X.band i) U V) : plant F U p k X i=plant F V p k X i∧ brush F U p k X i=brush F V p k X i:=by unfold plant brush; split_ifs; exact ⟨rfl,rfl⟩; exact ⟨sprig_local _ _ _ _ _ _ h, whole_l _ _ _ _ _ _ h⟩
lemma crit (T:Sheet.Atlas)(G:GapSize)(r:Side)(s : Poses r q v)(C C':ℝ)(hc:0<C)(hc':0<C')(p:0<q)(h:0<v) : ∀ᶠ L:ℝ in atTop,∀ᶠ y:ℝ in atTop,∀ (s:Side)(J: Record r s)(b:ℕ)(F:Net s T L y C C' b)(X:Bands s (G.select y))(i:X.Index)(U:Micro s)(p:Duo s), let W:= X.mark i; F.takeN X U i p≠0→(i∉ X.dc→ p∈ T.pairs y (W.reads U))→Grains W.mem U (plant F U p J.key X i) (brush F U p J.key X i) q v:=by
 filter_upwards [period_N T G q v C C' r s h hc hc'] with L l; filter_upwards [l,day_storm q v p h] with y t a s J b F X i U p; intro W h u; unfold plant brush; split_ifs with w; · exact a s (X.band i) U (by rw [← takeN_D F X U w p]; exact h)
 exact (t s J b F X i U p (u w) (by simpa only [W, takeN,w, ↓reduceIte] using h)).2
end Stamps
end YM.CF.BPress.Meadow
