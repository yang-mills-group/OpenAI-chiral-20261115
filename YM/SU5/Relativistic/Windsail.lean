import YM.SU5.Relativistic.Kinetic
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Rows
import YM.Push.SECTOR_MEASURE.Bounds
/-! # Uniform L² exponential tails even in clipped sector and holes counted. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Pharos
open Function Finset Filter MeasureTheory Lattice Wilson RG RG.PathData Work.F03
open scoped Matrix Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{W:PathData G}{p:Clip}{σ C Λ:ℝ}(B:W.Bounds p σ C Λ){N:Side}

-- unified response sheet abstraction
local notation "H_"=> Face (Per N)
local notation "Q"=> Site N
structure Ticket {G:Gauge}(N:Side) (σ :ℝ) (C:ℝ) (V: Slot→Site N→ G.Color) : Prop where
 pos:0≤ C
 owns (i:Slot): (∑ j:Site N,‖V i j‖^2) ≤ (Real.exp (σ/2*i.length))^2*C
variable (V: Slot→Site N→ G.Color) {P:ℝ}
abbrev column (W:PathData G)(V: Slot→Site N→ G.Color)(i: H_):= ∑' j,(W.row i.2 j).1 • V (W.row i.2 j).2 i.1
def cutlow (W:PathData G)(V:Slot→ Site N→ G.Color)(f:H_)(R:ℕ):= ∑' j, if (W.row f.2 j).2.length≤R then (W.row f.2 j).1 • V (W.row f.2 j).2 f.1 else 0
include B in
lemma tail_C (D:Ticket N σ P V) (i : PlaqAxes)(R:ℕ) : (∑ j:Q, ‖column W V (j,i)-cutlow W V (j,i) R‖^2) ≤ (Real.exp (-(σ/2)*R)*C)^2*P ∧ (∑ j:Q,‖cutlow W V (j,i) R‖^2) ≤ C^2*P:=by
 let Z:=PiLp 2 (fun _:Q=> G.Color)
 let F(j:ℕ):PiLp 2 (fun _:Q=> G.Color) := WithLp.toLp 2 (fun x=> (W.row i j).1 • V (W.row i j).2 x)
 let l(j:ℕ):=(W.row i j).2.length; let X(j:ℕ):PiLp 2 (fun _:Q=> G.Color):= if l j≤R then F j else 0; let s:=Real.exp (-(σ/2)*R)
 let t(j:ℕ):=|(W.row i j).1| *Real.exp (σ*l j); let r:=Real.sqrt P
 have he:=B.width; have hb:P≥0:=D.pos; have hv:C≥0:=le_trans (tsum_nonneg ((B.rows i).1)) (B.rows i).2.2
 have hp(j:ℕ): ‖F j‖ ≤ |(W.row i j).1| * Real.exp (σ/2*l j)*r:= by
    have hP:=D.owns (W.row i j).2
    rw [← sq_le_sq₀ (norm_nonneg _) (by unfold r; positivity),PiLp.norm_sq_eq_of_L2]; simp only [F,WithLp.ofLp_toLp,norm_smul,Real.norm_eq_abs,mul_pow,← Finset.mul_sum]; rw [sq_abs,show r^2=P from Real.sq_sqrt hb,mul_assoc]; exact mul_le_mul_of_nonneg_left hP (by positivity)
 have hs(j:ℕ):‖F j‖≤ t j*r:= by
    refine (hp j).trans ?_; unfold r t; gcongr; linarith
 have hm := (show Summable t from (B.rows i).2.1); have he': Summable F:=Summable.of_norm_bounded (hm.mul_right r) hs
 have hg(j:ℕ):‖X j‖≤‖F j‖:=by unfold X; split; rfl; rw [norm_zero]; apply norm_nonneg
 have hX:Summable X:= Summable.of_norm_bounded (hm.mul_right r) fun j=>(hg j).trans (hs j)
 let Y(j:ℕ):= F j-X j; have ht: Summable Y:=he'.sub hX
 have hx(j:ℕ):‖Y j‖≤ t j*r*s:=by
    unfold Y X; split_ifs with g
    · rw [sub_self,norm_zero]; unfold t r s; positivity
    rw [sub_zero]; refine (hp j).trans ?_
    have hl: Real.exp (σ/2*l j) ≤ Real.exp (σ*l j)*s:= by
       unfold s; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; have hl:(R:ℝ)≤ l j:=by exact_mod_cast (le_of_lt (lt_of_not_ge g))
       nlinarith only [hl, he]
    calc _ ≤ |(W.row i j).1| * (Real.exp (σ*l j)*s)*r := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl (abs_nonneg _)) (Real.sqrt_nonneg _)
         _ = _:=by unfold t; ring
 have hz(v:ℝ)(h:0≤v)(X:ℕ→PiLp 2 (fun _:Q=>G.Color))(x:Summable X)(z:∀ j,‖X j‖≤ t j*r*v) : (∑ k:Q,‖(∑' j,X j) k‖^2)≤ (v*C)^2*P:=by
    rw [←PiLp.norm_sq_eq_of_L2]; have he: Summable (fun j=>‖X j‖):=x.norm
    have hw:‖∑' j,X j‖≤ v*C*r:=le_trans (norm_tsum_le_tsum_norm he) (((he.tsum_le_tsum z ((hm.mul_right r).mul_right v))).trans (by rw [tsum_mul_right,tsum_mul_right]; exact ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (B.rows i).2.2 (Real.sqrt_nonneg _)) h)).trans_eq (by ring)))
    exact (pow_le_pow_left₀ (norm_nonneg _) hw 2).trans_eq (by rw [mul_pow,show r^2=P from Real.sq_sqrt hb])
 have hP (f:ℕ→PiLp 2 (fun _:Q=>G.Color))(p:Summable f)(i:Q): (∑' j,f j) i=∑' j, f j i:=by
    exact (PiLp.proj (𝕜:=ℝ) 2 (fun _:Q=> G.Color) i).map_tsum p -- tune field
 have he''(u:Q):(∑' j,X j) u=cutlow W V (u,i) R:=by rw [hP X hX]; apply tsum_congr; intro j; unfold X; split_ifs <;> rfl
 have hW(u:Q):column W V (u,i)-cutlow W V (u,i) R=(∑' j,Y j) u:=by rw [show (∑' j,Y j)= _ from he'.tsum_sub hX]; change _= (∑' j,F j) u-(∑' j,X j) u; rw [he'',hP F he']
 constructor; · simp_rw [hW]; exact hz s (Real.exp_nonneg _) Y ht hx
 simp_rw [←he'']; simpa using hz 1 zero_le_one X hX (fun j=>by rw [mul_one]; exact (hg j).trans (hs j))

def vane (σ C:ℝ)(r:ℕ):=(Fintype.card PlaqAxes:ℝ)*(Real.exp (-(σ/2)*r)*C)^2
lemma late (σ C:ℝ)(h:0<σ) : Tendsto (vane σ C) atTop (𝓝 0):=by
 have he:Tendsto (fun r:ℕ=>Real.exp (-(σ/2)*r)) atTop (𝓝 0):= Real.tendsto_exp_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith)) -- tune
 simpa only [zero_mul,zero_pow (OfNat.ofNat_ne_zero 2),mul_zero] using! (he.mul_const C |>.pow 2 |>.const_mul (Fintype.card PlaqAxes:ℝ))
include B in
lemma tail_G(p:Ticket N σ P V)(r:ℕ) : (∑ i:H_,‖column W V i-cutlow W V i r‖^2)≤ vane σ C r * P∧ (∑ i:H_,‖cutlow W V i r‖^2) ≤ Fintype.card PlaqAxes*C^2*P:=by
 unfold Face; rw [Fintype.sum_prod_type, Fintype.sum_prod_type,sum_comm (f:=fun (a:Four _) (b:PlaqAxes)=> ‖column W V (a,b)-cutlow W V (a,b) r‖^2),sum_comm (f:=fun (a:Four _) (b:PlaqAxes)=>‖cutlow W V (a,b) r‖^2)]; constructor
 · exact (sum_le_sum (fun i _=> (tail_C B V p i r).1)).trans_eq (by unfold vane; rw [sum_const,card_univ,nsmul_eq_mul,mul_assoc])
 exact (sum_le_sum (fun i _=> (tail_C B V p i r).2)).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul,mul_assoc]) -- tune

open scoped Classical
abbrev kiosk {G:Gauge}(p:Clip)(t:ℝ)(U:Config G N)(i :Slot)(j:Q): G.Color:= if PathData.kept p t j U then i.atSite U j else 0
def tollD (G:Gauge)(p: Clip) (t:ℝ)(U:Config G N) := ∑ i:H_, PathData.clipped p t (G.chord (faceValue U i))
theorem clip_pos (p:Clip){t r:ℝ}(h:0≤t)(g:0≤r):0≤ PathData.clipped p t r:=by have he:=p.quadratic_pos; have hp:=p.tail_pos; unfold PathData.clipped; split <;> positivity
lemma toll_pos {t:ℝ}(U:Config G N)(p:Clip)(h:0≤t) : 0≤ tollD G p t U:=sum_nonneg fun _ _=>clip_pos _ h (G.chord_nonneg _)
open Work.F03
open AnalyticBridge.VerifiedReset (slot_length offset_inside)
theorem ticket_s {t:ℝ}(h:1 ≤ p.relaxation * σ)(q:0≤t)(U:Config G N): Ticket N σ (p.linear⁻¹*tollD G p t U) (kiosk p t U):=by
 have hs:=p.tail_pos; have hx:=p.radius_pos; have hd:=p.quadratic_pos; have he:0≤σ:=by by_contra v; nlinarith only [h,v,hx] -- tune
 refine ⟨mul_nonneg (by positivity) (toll_pos U p q),fun i=> ?_⟩
 let V(u:H_):= PathData.clipped p t (G.chord (faceValue U u)); let A:= (Real.exp (σ/2*i.length))^2
 have hw:A=Real.exp (σ*i.length):=by unfold A; rw [sq,←Real.exp_add]; congr 1; ring
 have ht:A≥1:=by rw [hw]; exact Real.one_le_exp (by positivity)
 have hk(j:Q): ‖kiosk p t U i j‖^2 ≤ A*(p.linear⁻¹* V (slotFace i j)):= by
    unfold kiosk; split_ifs with v; swap
    · rw [norm_zero]; simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]; exact mul_nonneg (zero_le_one.trans ht) (mul_nonneg (by positivity) (clip_pos _ q (G.chord_nonneg _))) -- tune
    rw [atSite_path,G.norm_adjoint]; apply (pow_le_pow_left₀ (norm_nonneg _) (G.curvature_norm _) 2).trans
    let y:= G.chord (faceValue U (slotFace i j)); have ha:0≤ y:= G.chord_nonneg _
    have hg:y≤t*A:= (v _).trans (mul_le_mul_of_nonneg_left (by
        rw [hw]; apply Real.exp_le_exp.mpr; rw [div_le_iff₀ hx]; have hc:(separation j (slotFace i j).1:ℝ) ≤ (i.length:ℝ) := by exact_mod_cast (separation_comm _ _).trans_le (slot_length i j (offset_inside i j))
        nlinarith only [h,hc,show (0:ℝ)≤ i.length by positivity,mul_le_mul_of_nonneg_right h (show (0:ℝ)≤ i.length by positivity)]) q)
    change y^2≤ A*(p.linear⁻¹*PathData.clipped p t y); unfold PathData.clipped; split
    · refine le_trans ?_ (le_mul_of_one_le_left (by positivity) ht); rw [←div_eq_inv_mul,le_div_iff₀ hs]; nlinarith only [mul_le_mul_of_nonneg_right p.kink.le (sq_nonneg y),p.kink,sq_nonneg y, mul_nonneg (sq_nonneg y) hd.le]
    exact (mul_le_mul_of_nonneg_right hg ha).trans_eq' (by rw [sq]) |>.trans_eq (by field_simp)
 let f:= slotFace (n:=N) i
 refine le_trans (sum_le_sum (s:=univ) fun z _=>hk z) ?_
 rw [←mul_sum,←mul_sum]; refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (zero_le_one.trans ht)
 exact FreeResolvent.Cost.sum_comp_le (f:=f) (fun i j v=> add_left_cancel (congrArg Prod.fst v)) V (fun _=>clip_pos _ q (G.chord_nonneg _)) -- tune
-- linear with no widths except σ positive
open Precision Exterior
abbrev curling (a:fieldDir G N 1)(i: Slot)(x:Q):= faceCurl (slotFace i x) a
def curlE (a:fieldDir G N 1):= ∑ x : Face (Per N), ‖faceCurl x a‖^2
lemma ticket_q (a:fieldDir G N 1)(h:0≤σ): Ticket N σ (curlE a) (curling a):=by
 have he:0≤curlE a:=sum_nonneg fun _ _=>by positivity
 refine ⟨he,fun i=>le_trans ?_ (le_mul_of_one_le_left he (one_le_pow₀ (Real.one_le_exp (by positivity))))⟩ -- tune
 exact FreeResolvent.Cost.sum_comp_le (f:= slotFace (n:=N) i) (fun i j v=> add_left_cancel (congrArg Prod.fst v)) (fun x=> ‖faceCurl x a‖^2) (fun _=> sq_nonneg _)
end YM.CF.Papyrus.Pharos
#print axioms YM.CF.Papyrus.Pharos.ticket_s
