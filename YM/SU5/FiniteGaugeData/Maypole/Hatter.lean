import YM.SU5.FiniteGaugeData.Maypole.Cabaret
/-! # Long gaps. Eu point operations, joins and priced measures -/
set_option autoImplicit false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 16000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Mink General Lorentz Real
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
open Poin Celeritas Land Leal Breve Poin.Gem
open Boundary Probe
namespace Luft
open Folio Flute _root_.YM.CF.Buffered.Afterglow.Hierarchy.Vp.Caps
local notation "T"=>timeAxis
abbrev speed:ℝ:=512
abbrev tempo:ℝ:=1/speed
variable {H:Hilbert}(S:OS.Semigroup H timeAxis)(e:Ray) (t s:ℝ≥0)(g:∀ e:Mink.Ray,S.ℚmeasure.region (copyE (magnet e))ᶜ=0)
local notation "H'"=> magnet e
local notation "Qo"=> S.ℚmeasure
local notation "Po" x:max=> S.ℚmeasure.diagonal x
def Slow (S:OS.Semigroup H timeAxis) : OS.Semigroup H timeAxis:={ S with
 U v:= S.U (tempo • v)
 uZero:= (show S.U (tempo • 0)=_ from by rw [smul_zero, S.uZero])
 space v t:= by rw [smul_add]; exact S.space ..
 unitary v w:= S.unitary ..
 independent _ _:= S.independent ..
 continuousU w:= (S.continuousU w).comp (show Continuous (fun v:Cross timeAxis=> tempo • v) from by fun_prop)
 }
omit g
private lemma paceHat(v:Cross T) : ∃ e:Mink.Ray,v=‖v‖ • magnet e :=by
 by_cases p:v=0; · subst v; exact ⟨Ray.fromAxis 0,by simp⟩
 let V:= ‖v‖; have hv:0<V:=norm_pos_iff.mpr p; have he:V= ‖spatial v.val‖:=by
    unfold V; apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1; have hx:‖(v.val:E4)‖^2= _:=squares v.val; rw [show time v.val=0 from v.property] at hx; change ‖v.val‖^2=_; simpa only [zero_pow (by norm_num: 2≠0),add_zero,zero_add] using hx
 let e:Ray:= ⟨V⁻¹ • spatial v.val,by rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv), ← he, inv_mul_cancel₀ hv.ne']⟩; refine ⟨e,Subtype.ext (ext_by ?_ ?_)⟩; · change spatial v.val = spatial (V • position e.val 0); simp; change _= V • (V⁻¹ • spatial v.val); rw [smul_smul,mul_inv_cancel₀ hv.ne',one_smul]
 exact (show time v.val=0 from v.property).trans (show time (V • position e.val 0)= 0 from (by simp)).symm -- tune eh v property defin
include g
lemma paceX (v:Cross T)(x:H)(h:‖v‖≤1): ∀ᵐ p∂ Po x, |ped p (tempo • v)|≤ p T :=by
 obtain ⟨e,a⟩:= paceHat v; let u:=magnet e; have he: (Po x) (copyE u)ᶜ=0:= ((Qo).null_pair (copy_c u).isOpen_compl.measurableSet x).2 (by rw [show (Qo).region (copyE u)ᶜ=0 from g e]; rfl); filter_upwards [(show ∀ᵐ p∂Po x,p∈copyE u from he), S.bright x] with p q w
 have hz:|ped p u|≤ speed * p T:=q; have ht:|ped p (tempo • v)| = tempo* ‖v‖* |ped p u|:=by
    nth_rw 1 [a]; unfold ped; change |inner ℝ p (tempo • (‖v‖ • u.val))|= _; rw [real_inner_smul_right,real_inner_smul_right,abs_mul,abs_mul,abs_of_nonneg (norm_nonneg _),abs_of_nonneg (by norm_num [tempo,speed]:0≤tempo),mul_assoc]
 rw [ht]; calc
    _ ≤ tempo*1*(speed*p T):=mul_le_mul (mul_le_mul_of_nonneg_left h (by norm_num [tempo,speed])) hz (abs_nonneg _) (by norm_num [tempo,speed])
    _ = _:=by unfold tempo speed; ring
omit g in
private lemma flipPay {a:Axis}(v:OS.Cross a)(x:E4)(e:|ped x v|≤ x a) : rateX a ((s:ℝ) • v.val) (t+s) x ≤ rateT a (t+s) t x:=by
 let D:= metal a (t+s) x; let E:= metal a t x; let V:= Real.exp ((s:ℝ)*x a:ℝ); have hp:=e; have he:E=D*V:=by unfold D E V; unfold metal; rw [←Real.exp_add]; push_cast; ring_nf
 have hg:‖Probe.plane x ((s:ℝ) • v.val)-1‖ ≤ V-1:= by rw [plane_rate]; apply (whiff ..).trans; rw [abs_of_nonneg s.coe_nonneg]; nlinarith only [mul_le_mul_of_nonneg_left hp s.coe_nonneg, (show (s:ℝ)*x a+1 ≤ V from Real.add_one_le_exp _)]
 let ε:=‖Probe.plane x ((s:ℝ) • v.val)-1‖; have hD:0≤D:=metal_0 ..; unfold rateX; rw [metal_add,←pow_two]; change D^2*ε^2 ≤ (E -D)^2; rw [←mul_pow,he]; apply pow_le_pow_left₀ (mul_nonneg hD (norm_nonneg _)); nlinarith only [mul_le_mul_of_nonneg_left hg hD]
open Mist Mist.Utah
lemma courtP(x:H)(k:ℝ): Velocity (Slow S) t k x:=by
 intro v w s p; let z:=tempo • v; let c:= (s:ℝ) • z; have hz:tempo • ((s:ℝ) • v)=c:=smul_comm tempo (s:ℝ) v; have he:= paceX S g v x w
 obtain ⟨u,e⟩:=paid_P S x c.val (t+s); obtain ⟨vA,hA⟩:=paid_T S x (t+s) t; change dist (S.U (tempo • ((s:ℝ) • v)) (S.E _ x)) (S.E _ _) ≤ dist (S.E _ _) (S.E _ _); rw [hz,←vacancy S]; exact (sq_le_sq₀ (by positivity) (by positivity)).1 (e ▸ hA ▸ integral_mono_ae u vA (he.mono (fun x v=> Luft.flipPay t s z x v))) -- tune
lemma atSlow : Cinema (Slow S):= free_run (Slow S) 1 zero_lt_one (fun x=>courtP S _ g x 1)
abbrev reduced (v:Cross T):= tempo • v
noncomputable def budget :Shelf S (reduced (magnet e)):=by
 let E:= Lobby (Slow S) (atSlow S g) e; refine ⟨E.cup, E.hol, E.norm, fun u p t=> ?_⟩; rw [E.realC _ p t]; change S.U (tempo • (t • _))*_= S.U (t • (tempo • _))* _; rw [smul_comm]; rfl
#check @budget
#print axioms budget
end Luft
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp
