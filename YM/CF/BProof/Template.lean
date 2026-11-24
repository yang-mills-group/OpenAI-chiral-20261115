import YM.CF.BProof.FaceDesign
import YM.CF.BProof.Grid.Lerp

/-! The template horizontal profile read in smooth frame coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Face
open Function SU Mag Lattice Cube Pressure Filter Set MeasureTheory Chart
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
local notation "G" => SU.group
variable {c s : Side} (g : Ratio c s)(X : Design)(K : Chart G)(u : ℝ)(k : ℕ)
variable (U V : Sheet s)

lemma react_mul (u v : Frame s) : react (u*v) U=react u (react v U):=by ext1 i; simp only [react,Pi.mul_apply]; group
@[simp] lemma react_identity : react 1 U=U:=by ext1 i; simp [react]
lemma react_inv (u : Frame s) : react u⁻¹ (react u U)=U:=by rw [← react_mul,inv_mul_cancel,react_identity]

/-- Smooth frame given that face label. -/
def smooth (h : Frame s) := X.frames g k (react h U)*h
lemma smooth_move (h p:Frame s): smooth g X k (react p U) (h*p⁻¹)=smooth g X k U h * p⁻¹:=by unfold smooth; rw [← react_mul,show h*p⁻¹*p=h by group,mul_assoc]

/-- Flat horizontal interpolating field in the common smooth coordinates (U,V already
expressed in those frames). -/
def link (a b : E) := group.lieExp (lerp u (slog K a) (slog K b))
def profile : Sheet s:=fun i=> link K u (U i) (V i)

lemma profile_c : Measurable (Function.uncurry (profile (s:=s) K u)) := by
 apply measurable_pi_lambda
 intro i; have hL:= (slog_m K); refine group.lieExp_cont.measurable.comp (g:=group.lieExp) ?_; exact ((measurable_const (a:=1-u)).smul (hL.comp ((measurable_pi_apply (X:=fun _ : Space s × TAxis => E) i).comp measurable_fst))).add ((measurable_const (a:=u)).smul (hL.comp ((measurable_pi_apply i).comp measurable_snd))) -- tune
lemma react_c : Continuous (Function.uncurry (@react s)) := by apply continuous_pi; intro i; unfold react Function.uncurry; fun_prop
lemma smooth_c : Measurable (Function.uncurry (smooth g X k)) := by
 let f(p : Sheet s × Frame s):= X.frames g k (react p.2 p.1); have h : Measurable (fun p : Sheet s × Frame s=>react p.2 p.1):= (react_c (s:=s)).measurable.comp (f:=Prod.swap) (continuous_swap.measurable); have h: Measurable f:= (X.meas g k).comp h
 exact h.mul measurable_snd

structure Firm (U : Sheet s) (r w : ℝ) : Prop where
  pay (i : Space s × TAxis) : group.chord (U i) ≤ K.radius
  logs (i) : ‖slog K (U i)‖≤r
  squares (p i) : group.chord (read U p i)≤w

lemma link_a (a b : E) (h : group.chord a≤ K.radius) : link K 0 a b=a:=by rw [link,lerp_zero,slog_leg _ _ h]; exact (K.exposes _ h).2 -- tune
lemma link_b (a b : E) (h : group.chord b≤ K.radius) : link K 1 a b=b:=by rw [link,lerp_one,slog_leg _ _ h]; exact (K.exposes _ h).2
lemma link_small (e:u∈ Icc 0 1)(a b:E){r:ℝ}(h:‖slog K a‖ ≤ r)(h':‖slog K b‖ ≤ r)(hr:r≤K.size): group.chord (link K u a b) ≤ K.C*r:= (K.step _ ((lerp_bound u _ _ h h' e).trans hr)).trans (mul_le_mul_of_nonneg_left (lerp_bound u _ _ h h' e) (zero_le_one.trans K.C_one))
lemma link_step (a b:E)(v:ℝ)(hu:u∈Icc 0 1)(hv:v∈ Icc 0 1){r:ℝ}(h:‖slog K a‖ ≤ r)(h':‖slog K b‖ ≤ r)(hr:r≤K.size):
    cd G (link K u a b) (link K v a b) ≤ K.C*(|u-v| * (2*r)) := (K.cost _ _ ((lerp_bound u _ _ h h' hu).trans hr) ((lerp_bound v _ _ h h' hv).trans hr)).trans (mul_le_mul_of_nonneg_left (lerp_distance _ _ _ _ _ h h') (zero_le_one.trans K.C_one)) -- tune

lemma profile_square (hu:u∈Icc 0 1) {r w:ℝ}(u':Firm K U r w)(v':Firm K V r w)(hr:r≤K.size)(p:Space s)(i:Fin 3):
    group.chord (read (profile K u U V) p i) ≤ w+(4*K.bump/group.colorScale)*r^2 := by
 let F' : Fin 4→ Space s× TAxis:= ![(p,f₂ i),(Grid.slide p (f₂ i),f₁ i),(p,f₁ i),(Grid.slide p (f₁ i),f₂ i)]
 let f(W:Sheet s)(i:Fin 4):=slog K (W (F' i)); let A(g:Fin 4→Lie):=group.lieExp (g 0)*group.lieExp (g 1); let B(g:Fin 4→ Lie):=group.lieExp (g 2)*group.lieExp (g 3)
 have hh(W)(h:Firm K W r w) : cd G (A (f W)) (B (f W))≤w:=by
    have hh:=h.squares p i; rw [square_price] at hh
    have hx(n:Fin 4) : group.lieExp (f W n)=W (F' n):=by rw [show f W n=logG G (W (F' n)) from slog_leg ..]; exact (K.exposes _ (h.pay _)).2; exact h.pay _ -- tune
    unfold A B; rw [hx,hx,hx,hx]; exact hh
 rw [square_price]; exact K.smooth_lerp hu hr (f U) (f V) (fun i=> u'.logs _) (fun i=> v'.logs _) A (fun _=>rfl) B (fun _=>rfl) (hh U u') (hh V v') -- implicit order tune

-- `w` bound per face from before tilt, `r` on smooth frame. Estimate formulation of eq:B-frames/template with C_L / R. Use for y large.
def blendR (X:Design)(K:Chart G)(g:Ratio c s) : ℝ:=K.C*(X.K/g.count.val)
lemma blend_p : 0<blendR X K g:=by have ht:=zero_lt_one.trans_le K.C_one; have hp:=X.budget; unfold blendR; positivity
lemma firm_read (v:ℝ)(h:0<v) : ∃ C > (0:ℝ), ∀ᶠ y:ℝ in atTop,∀ {c s:Side} (g:Ratio c s)(k), Sized v g y k → X.k₀≤k →
    ∀ U:Sheet s,∀ u: Frame s, Lift K y U u → Firm K (react (smooth g X k U u) U) (blendR X K g) (C*mA y) ∧ blendR X K g ≤ K.size:= by
 obtain ⟨C,hc,H⟩:= bounds K
 refine ⟨C,hc,?_⟩
 have hx:=X.positive; have ht:=K.positive; have hz:=zero_lt_one.trans_le K.C_one; have hg:=K.admitted
 have hp : Tendsto rY atTop atTop:= by
     have hl:= coin_purchases (a:= -1/4) (b:=1/2) (c:=0) (by norm_num)
     have hy: Tendsto (fun y=>coin y (-1/4) (1/2) 0) atTop (𝓝[>]0):= tendsto_nhdsWithin_iff.mpr ⟨hl, Eventually.of_forall fun i=>coin_pos ..⟩; apply (tendsto_inv_nhdsGT_zero.comp hy).congr; intro y; simp only [Function.comp_apply, coin_inv]; unfold rY; ring_nf
 filter_upwards [H,(hp.const_mul_atTop h).eventually_ge_atTop (max (X.K/K.radius) (K.C*X.K/K.size)), coin_budget (a:=0) (b:= -1/4) (c:=0) (d:=0) (e:=0) (f:=0) (by norm_num) (C*(2*v)^2) X.toll hx] with y H Hy pq
 intro c s g k w q U u V; let f:= react (smooth g X k U u) U; let K':= g.count.val; have hk:0<(K':ℝ):=by unfold K'; positivity
 have he(p i) := H s U p _ (V.1 p) i
 have hy(p i)(v:Frame s): group.chord (read (react v U) p i) ≤ C*mA y:=by rw [read_eq,Gauge.chord_conj]; exact he p i
 have h₀: max (X.K/K.radius) (K.C*X.K/K.size) ≤ (K':ℝ):= Hy.trans w.lower
 have H' (i:Space s×TAxis): group.chord (f i)≤ X.K/g.count.val:=by
    unfold f smooth; rw [react_mul]; refine X.costs g k _ w.fine w.power q (fun p i=> le_trans (hy p i u) ?_) i.1 i.2
    rw [le_div_iff₀ (sq_pos_of_pos hk)]; have hp:0<mA y:=coin_pos ..
    refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk.le w.upper.le 2) (by positivity : 0≤C*mA y)).trans ?_; have hl:mA y*rY y^2=coin y 0 (-1/4) 0:=by rw [coin_pow,coin_mul]; ring_nf
    simp only [coin_zero,mul_one] at pq; rw [mul_pow]; linear_combination (norm:=ring_nf) hl * (C*(2*v)^2) + pq.le -- tune
    exact le_rfl
 have hb (i): group.chord (f i)≤ K.radius:= le_trans (H' i) ((div_le_iff₀ hk).2 (le_trans ((div_le_iff₀ ht).1 ((le_max_left ..).trans h₀)) (Eq.le (mul_comm ..))))
 refine ⟨⟨hb,fun i=>?_,fun p i=>hy p i _⟩,?_⟩
 · have hh:=hb i; rw [slog_leg _ _ hh]; exact (K.width _ hh).trans (mul_le_mul_of_nonneg_left (H' _) hz.le)
 unfold blendR; rw [← mul_div_assoc]; exact (div_le_iff₀ hk).2 (le_trans ((div_le_iff₀ hg).1 ((le_max_right ..).trans h₀)) (Eq.le (mul_comm ..)))
end YM.CF.BProof.Face
