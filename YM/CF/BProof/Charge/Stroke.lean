import YM.CF.BProof.Charge.Cancel
import YM.CF.BProof.Charge.Aff
import YM.CF.BProof.PL

/-! From per-heavy support hypotheses on oriented core links to template Taylor model. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge.Form
open Function Filter RG Wilson Lattice Finset Work Micro Moment MeasureTheory Angular AnalyticBridge.SectorAffine Mag
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
local notation "E"=> SU.group.lieExp
variable (K:Chart G) {s:Side}(W: Argument s)(y:ℝ)(σ:Signed)(b:Bond s)(U:Config G s)

def Lay (y:ℝ)(σ:Signed)(i:Axis):= E (aA y • pointed σ i)
lemma uses (i:Axis) : E (aA y • chargeX i)=Angular.starts y i:=by cases i using Fin.cases with|zero=>simp [chargeX,Angular.starts] |succ i=>rfl -- tune newline
lemma used : lRead σ U b=if σ.flip b.2 then (U (sendEdge σ 0 b))⁻¹ else U (sendEdge σ 0 b):= by unfold lRead Lattice.pull Step.read; simp only [Step.rotate,posDir,sendEdge,Bool.false_xor]
@[simp] lemma lay_link : lRead σ (mag (s:=s) y) b=Lay y σ b.2:=by
 cases b with|mk x i=>
 unfold Lay; rw [used]; dsimp only; rw [part_key,pointed]; unfold mag turn; dsimp only; split; rw [LinearMap.neg_apply,LinearMap.id_apply,smul_neg, F03.exp_neg_color, uses]; rw [LinearMap.id_apply,uses]
def baseF (p:PlaqAxes):= curl (Lay y σ (a₁ p)) (Lay y σ (a₂ p)) (Lay y σ (a₁ p)) (Lay y σ (a₂ p))
lemma desc (l:Cell s) (U:Config G s) : faceValue U l=curl (U (positions l 0)) (U (positions l 1)) (U (positions l 2)) (U (positions l 3)):=Angular.price_eq ..
lemma fixed_face (l:Cell s) : faceValue (lRead σ (mag (s:=s) y)) l=baseF y σ l.2:=by rw [desc]; simp_rw [lay_link]; rfl

-- C relative price licenses. use of exp chart also buys width `t`.
abbrev stepC (C y:ℝ):= C*aA y
abbrev thin (C y:ℝ):= C*aA y*thresh y
structure Ink (K:Chart G)(C y:ℝ): Prop where
  t_size : thresh y≤K.size
  up : 0<C
  pay (σ i): SU.group.chord (Lay y σ i)+thresh y/16 ≤ stepC C y
  draw (σ i): Aff G 1 (baseF y σ i) (mA y • mark σ i) (thin C y)
  simple (σ i) : SU.group.chord (baseF y σ i) ≤ thresh y/2 -- permit all faces
  r_step : ((K.C/SU.group.colorScale*thresh y+SU.group.colorScale*stepC C y)*thresh y+ xi y) ≤ (1+SU.group.colorScale)* thin C y
  small : thin C y≤ thresh y
-- purchase first chart; Ink for all bigger constants, flags calendars.
lemma ink_w : ∀ᶠ C:ℝ in atTop, ∀ᶠ y:ℝ in atTop, Ink K C y :=by
 have h₀:= K.C_one; have he:=SU.group.colorScale_pos; obtain ⟨D,hD,H⟩:= K.bracket_cost
 let s':=SU.group.colorScale; let R:=1+∑ i:Axis,‖chargeX i‖; let A:=1+ ∑ σ:Signed,∑ a:PlaqAxes,‖mark σ a‖; have hv:0<A:=by unfold A; positivity
 have hp(σ i):‖mark σ i‖≤ A:= le_trans ((single_le_sum (f:=fun i=>‖mark σ i‖) (fun _ _=> norm_nonneg _) (mem_univ i)).trans (single_le_sum (f:=fun σ: Signed=>∑ i:PlaqAxes,‖mark σ i‖) (fun _ _=> Finset.sum_nonneg (fun _ _=>norm_nonneg _)) (mem_univ σ))) (by unfold A; simp)
 have ht:0<R:=by unfold R; positivity
 filter_upwards [eventually_ge_atTop (K.C*R+1),eventually_ge_atTop ((D/s')*R^3)] with C hx hk
 have hz:0<C:=lt_of_lt_of_le (by positivity : 0<K.C*R+1) hx
 filter_upwards [(coin_purchases (a:=-1/2) (b:=1) (c:=0) (by norm_num)).eventually (ge_mem_nhds K.admitted),(coin_budget (a:= -1/4) (b:=3/8) (c:=0) (d:=0) (e:=0) (f:=0) (by norm_num) R K.size K.admitted),coin_budget (a:=-1/2) (b:=1) (c:=0) (d:= -1/4) (e:=3/8) (f:=0) (by norm_num) (K.C/s'+1) (C/2) (by positivity), coin_budget (a:=-3/2) (b:=0) (c:=0) (d:= -3/4) (e:=11/8) (f:=0) (by norm_num) 1 (C/2) (by positivity), coin_budget (a:=-1/2) (b:=1) (c:=0) (d:=-1/4) (e:=3/8) (f:=0) (by norm_num) (1/16) 1 (by norm_num),coin_budget (a:= -3/4) (b:=9/8) (c:=0) (d:= -3/4) (e:=11/8) (f:=0) (by norm_num) 1 1 one_pos, coin_budget (a:= -1/2) (b:=3/4) (c:=0) (d:= -1/2) (e:=1) (f:=0) (by norm_num) A (1/4) (by norm_num),coin_budget (a:= -1/4) (b:=3/8) (c:=0) (d:=0) (e:=0) (f:=0) (by norm_num) C (1/4) (by norm_num)] with y H1 H2 h1 h2 h3 h4 h5 h6
 have hv':0<aA y:=coin_pos ..; have hh:0<thresh y:=coin_pos ..; have hu:0<mA y:=coin_pos ..
 have el : coin y (-3/4) (11/8) 0=aA y*thresh y:=by rw [coin_mul]; ring_nf
 have eq:(aA y)^3=coin y (-3/4) (9/8) 0:=by rw [coin_pow]; ring_nf
 rw [el,← eq] at h4; rw [el] at h2; rw [coin_zero] at H2 h6
 change (K.C/s'+1)*thresh y< _*aA y at h1; change 1*xi y<_ at h2; change A*mA y<(1/4)*thresh y at h5; change (1/16)*thresh y<1*aA y at h3; change C*aA y<_ at h6
 have hy(σ i): ‖aA y • pointed σ i‖ ≤ R*aA y:=by
    rw [norm_smul,Real.norm_of_nonneg hv'.le,mul_comm]; apply mul_le_mul_of_nonneg_right _ hv'.le; rw [pointed,turn_size]; exact (single_le_sum (f:=fun i=>‖chargeX i‖) (fun i _=> norm_nonneg _) (mem_univ _)).trans (by unfold R; simp)
 have hw:R*aA y≤K.size:=by simpa only [mul_one] using H2.le
 have hm(σ i): Aff G 1 (baseF y σ i) (mA y • mark σ i) (thin C y):=by
    let B:=a₁ i; let L:=a₂ i; have heq:SU.group.ad (aA y • pointed σ B) (aA y • pointed σ L)=mA y • mark σ i:=by simp only [map_smul,LinearMap.smul_apply,smul_smul]; rw [show aA y*aA y=mA y from by rw [coin_mul]; ring_nf]; rfl -- tune
    rw [← heq]; refine le_trans (H (R*aA y) _ _ hw (hy σ B) (hy σ L)) ?_; have hv:D*R^3≤s'*C:=by change 0<s' at he; field_simp at hk; linarith
    rw [mul_pow, ←mul_assoc]; unfold thin; change _≤ s'*(C*aA y*thresh y); have u : 0≤s'*C:=(by unfold s'; positivity); exact (mul_le_mul hv (by simpa only [one_mul] using h4.le : aA y^3≤ aA y*thresh y) (by positivity) u).trans_eq (by ring)
 have hq: thin C y≤ thresh y/4:=by unfold thin; nlinarith
 refine ⟨H1,hz,fun σ i=>?_,hm,fun σ i=>?_,?_,by linarith⟩
 · have he:= (K.step _ ((hy σ i).trans hw)).trans (mul_le_mul_of_nonneg_left (hy σ i) (zero_le_one.trans h₀)); unfold stepC Lay; nlinarith
 · have ht(σ i):= expense (hm σ i); specialize ht σ i; rw [cd_one,norm_smul, Real.norm_of_nonneg hu.le] at ht; linarith [mul_le_mul_of_nonneg_left (hp σ i) hu.le, le_abs_self (SU.group.chord (baseF y σ i)- mA y*‖mark σ i‖)]
 unfold thin stepC; unfold s' at h1; linarith only [mul_le_mul_of_nonneg_right h1.le hh.le,h2.le,sq_nonneg (thresh y)] -- tune s'
end YM.CF.BProof.Charge.Form
