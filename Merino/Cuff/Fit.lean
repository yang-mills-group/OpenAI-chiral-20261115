import Merino.Cuff.Tab
import Merino.Cuff.Kerf
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Cuff
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n

open Push.Uniform Planned.JetPort Peaks
open scoped ContDiff
variable {o:Seat n}{d r a b C:ℝ}{k:ℕ}
variable {Y: SOp n} {W:Toll (Single n)} {S: Sa n} {F:Openc (More n) d → Op (Single n)}
variable (h:Room d r C)(ha:0≤a)

def oweS (a C:ℝ)(S:Sa n)(W:Toll I):= C*(Branch.rent a S*ledgerV W)
lemma staple_v {N:Side} {u:Hue} (hu:‖u‖≤1)(i:Screw N):‖staple i u‖≤1:=by
 apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
 intro a; by_cases he:a=i
 · rw [he]; simpa
 simp [he]
lemma staple_x {i:Screw (More n)}(ho:i.1∉S)(u:Hue):Agrees S (staple i u) 0:=by
 intro j l _
 have hn:j≠i:= fun e=>ho (by rw [←e]; exact l)
 simp [hn]

include h ha

lemma earned_piece (p:planS d S W F)(x:W≠0 → o∈S∧S.card<k):
    Linked a (oweS a C S W) o k (silk F):=by
 have symm(u v): silk F u v = silk F v u:=round_symm (glint_smooth h p) _ _
 have hL(u v:Bows n):|silk F u v|≤ledgerV W*C*(‖u‖*‖v‖):= round_le (glint_zero h p) ..
 have m(u v)(q:silk F u v≠0):W≠0:=by


    intro r
    have hu:ledgerV W=0:=by rw [r]; simp [ledgerV]
    have he:=hL u v
    rw [hu,zero_mul,zero_mul] at he
    exact q (abs_eq_zero.mp (he.antisymm (abs_nonneg _)))
 have e(i:Screw (More n))(u:Hue)(v:Bows n)
     (q:silk F (staple i u) v≠0): separation o i.1 < S.card:=by
    have hw:=m _ _ q
    apply (f_then p hw).lim _ (x hw).1 i.1
    by_contra hi
    exact q (silk_kills h p _ v (staple_x hi _))
 have he:0≤ oweS a C S W:= mul_nonneg h.price.le
   (mul_nonneg (Real.exp_pos _).le (positive_led p))
 refine ⟨he,symm,silk_exact h p,?_,?_⟩
 · intro i u j v; by_contra ht
   exact Nat.lt_asymm (e i j v ht) ((x (m _ _ ht)).2.trans u)
 intro i j u v hu hv
 by_cases hx:silk F (staple i u) (staple j v)=0
 · rw [hx,abs_zero]; exact mul_nonneg he (mul_pos (selv_pos ..) (selv_pos ..)).le
 have hz:1 ≤ Branch.rent a S*(selvage a o i*selvage a o j):=by
   have hi:=e i _ _ hx
   rw [symm] at hx; have hj:=e j _ _ hx
   unfold Branch.rent selvage; rw [←Real.exp_add,←Real.exp_add]
   exact Real.one_le_exp (by
      have l:(separation o i.1:ℝ)≤S.card:=by exact_mod_cast hi.le
      have g:(separation o j.1:ℝ)≤S.card:=by exact_mod_cast hj.le


      linarith only [mul_le_mul_of_nonneg_left l ha,mul_le_mul_of_nonneg_left g ha])
 refine (hL _ _).trans ((mul_le_mul_of_nonneg_left ((mul_le_one₀ (staple_v hu i) (norm_nonneg _) (staple_v hv j)).trans hz) (mul_nonneg (positive_led p) h.price.le)).trans_eq ?_)
 unfold oweS; ring


abbrev traceX (Y:SOp n)(U:Pane n):=(Y (profile U)).trace.re

lemma earned (y:Trunk o Y k a b d):
    ∃ H,Linked a (C*b) o k H ∧ (∀ x, H x x=iteratedDeriv 2 (fun t:ℝ=>traceX Y (dyeB n (t • x))) 0/2) ∧ ∀ x:Bows n,‖x‖≤r →
      |traceX Y (dyeB n x) - (traceX Y 1 + H x x)|≤C*b*‖x‖^3:=by
 obtain ⟨P,W,p,v,l,u⟩:=y.home
 let E(S:Sa n):=oweS a C S (W S)
 have hz: ∑ S:Sa n,E S≤ C*b:= by
    unfold E oweS; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left l h.price.le
 let G(S:Sa n):=silk (P S)
 refine ⟨∑ S,G S,Linked.collate (fun S=> earned_piece h ha (p S) (v S)) hz,?_⟩
 have t(x:Bows n)(hx:‖x‖≤r):
     traceX Y (dyeB n x)=∑ S:Sa n,glint (P S) x:=by
   unfold traceX
   have hl:profile (dyeB n x)∈ Openc (More n) d:=h.get x hx
   rw [u ⟨_,hl⟩, Matrix.trace_sum,Complex.re_sum]
   apply sum_congr rfl; intro i _
   change _=(equalizer _ (profile (dyeB n x))).re
   rw [equalizer,dif_pos hl]
 constructor
 · intro x
   let F(s:Sa n):= glint (P s) ∘ bolt x
   have eq:(fun m:ℝ=>traceX Y (dyeB n (m • x))) =ᶠ[𝓝 0] fun m=>∑ s,F s m:=by
     have hv: ‖bolt x 0‖<r:=by rw [map_zero,norm_zero]; exact h.haveR
     filter_upwards [((bolt x).continuous.norm.tendsto 0).eventually (gt_mem_nhds hv)] with m he
     exact t _ (le_of_lt he)
   have hf(s): ContDiffAt ℝ (↑(2:ℕ)) (F s) 0:=by
      apply ContDiffAt.comp _ _ (bolt x).contDiff.contDiffAt; rw [map_zero]; exact glint_smooth h (p s)
   rw [eq.iteratedDeriv_eq,iteratedDeriv_fun_sum (fun s _=>hf s),LinearMap.sum_apply,LinearMap.sum_apply,Finset.sum_div]
   exact sum_congr rfl fun s _=>by unfold G silk F; rw [round_line x (by rw [map_zero]; exact glint_smooth h (p s)),map_zero,iteratedFDeriv_two_apply];rfl
 have h0:dyeB n 0=1:=AnalyticBridge.VerifiedReset.at_zero _
 intro x hx; rw [t x hx,←h0,t 0 (by rw [norm_zero];exact h.haveR.le)]
 simp only [LinearMap.sum_apply]
 rw [←sum_add_distrib,←sum_sub_distrib]
 refine (abs_sum_le_sum_abs ..).trans ?_


 apply le_trans _ (mul_le_mul_of_nonneg_right hz (by positivity))
 rw [sum_mul]
 refine sum_le_sum fun S _=> le_trans (Afford.cubic (glint_cost h (p S)) (glint_first h (p S)) x hx)
    (mul_le_mul_of_nonneg_right ?_ (by positivity))
 rw [mul_comm]; exact mul_le_mul_of_nonneg_left
    (le_mul_of_one_le_left (positive_led (p S)) (Branch.rent_one ha _)) h.price.le
end YM.CF.Merino.Cuff
