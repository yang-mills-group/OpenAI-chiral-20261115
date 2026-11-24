import YM.CF.BPress.Wealth.Net
import YM.CF.BPress.Count
/-! `eq:B-wn`, VolB-gauge. buys with universal constants at scale C_I fixed then power families in y; includes log rel for kept.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Finset Filter MeasureTheory Lattice Wilson RG Precision Grid Pressure Push.AbsoluteSums Branch Ledger
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
open Push.Local ConnectedActivityE6.Raw
variable {s:Side}{G:Gauge} {σ a C Λ y : ℝ} (d:Clip)(R:PathData G)(p:BudgetPoint)(β:ℝ)(M:ℕ)
-- keep payments tracked through real addition order. atom sum.
def debt (a:Signed)(P : Support s)(U:Config G s) := (β*((∑ x:PlaqAxes,longG M R p d a x P U) + atom R.cubic p a P U + atom R.quartic p a P U) + atom R.loop p a P U)
def totalWeak (P : Support s)(U:Config G s) := ∑ a:Signed, chPrice * debt d R p β M a P U
def credit (a:Signed)(P : Support s) := (|β| *((∑ x:PlaqAxes, longFee M R a x P) + atomFee R.cubic p a P + atomFee R.quartic p a P) + atomFee R.loop p a P)
def fullWeak (P : Support s) := ∑ a:Signed, |chPrice| * credit R p β M a P

-- poly purchase
def clipbill (σ C Λ β t:ℝ)(M:ℕ) := β * ((Fintype.card PlaqAxes:ℝ)* (Wt (σ/2) (M+2) * refund σ C M) + Wt σ 8*(t^3*C) + Wt σ 8*(t^4*C)) + Wt σ 8*(t^2*Λ)

lemma total_script (h:R.Bounds d σ C Λ)(w:Checks M p d)(t:0≤β)(g:0≤ a)(f:a*17^4≤σ/2)(k:a*17^4*5≤1)(l:a≤σ/4)(j:a*(3+((2:ℝ)*M+5)^4)≤1) :
    Thinner (s:=s) (totalWeak d R p β M) (fullWeak R p β M) a (clipbill σ C Λ β p.threshold M) ∧ ∀ U:Config G s,
    R.inChannels d p β U= ∑ x:Face (Per s), hide d p β U x + ∑ z:Signed, (∑ x:Face (Per s), kept d p R β M z U x)+ ∑ P,totalWeak d R p β M P U:=by
 let y:=p.threshold; let z:=clipbill σ C Λ β y M
 have he(A:Signed) (r:ℕ)(F:ℕ→Atom G r)(v:r ≤ 4) (e:ℝ) (H:SumBudget (fun x=> (F x).budget σ) e)(I:∀ i,(F i).Invariant) := atom_thin (s:=s) F p A H I h.width g f (le_trans (mul_le_mul_of_nonneg_left (show (r:ℝ)+1≤5 by exact_mod_cast (show r+1≤5 by omega)) (by positivity)) k)
 let W(A:Signed):= Thinner (s:=s) (debt d R p β M A) (credit R p β M A) a z
 have cp:(Fintype.card Signed:ℝ)*chPrice=1:=by unfold chPrice; field_simp
 let Z(A:Signed):= fun x:Config G s=> PathData.principal R d p β (pull A 0 x)
 have hp(A:Signed): W A ∧ ∀ U:Config G s,
     ∑ P,debt d R p β M A P U= β*(∑ x:Face (Per s),tails R d M 1 p.threshold x (pull A 0 U)) +
      ∑ i, (β*(PathData.atomSeries R.cubic p (pull A 0 U) i + PathData.atomSeries R.quartic p (pull A 0 U) i) + PathData.atomSeries R.loop p (pull A 0 U) i):=by
    let X1 := R.cubic; obtain ⟨x1,x⟩:= he A 2 R.loop (by decide) Λ h.two (fun i=> (h.invariant i).1); obtain ⟨y1,y⟩:= he A 3 R.cubic (by decide) C h.three (fun i=>(h.invariant i).2.1); obtain ⟨z1,z'⟩:= he A 4 R.quartic (by decide) C h.four (fun i=>(h.invariant i).2.2); let Z':=fun i:PlaqAxes=> long_thin (s:=s) M R p d A i h w g l j; constructor
    · unfold W z clipbill; convert (((((Thinner.sumThin univ fun i=>(Z' i).1).plus y1).plus z1).scale β).plus x1) using 1 <;> (first| rfl| simp only [abs_of_nonneg t,sum_const,nsmul_eq_mul, card_univ]); all_goals rfl -- tune
    intro U; unfold debt; simp only [sum_add_distrib,←mul_sum,mul_add]; rw [x U,y U,z' U,sum_comm (f:=fun P v=> longG M R p d A v P U)]; simp_rw [show ∀ i, ∑ P,longG M R p d A i P U= _ from fun i=>(Z' i).2 U,Fintype.sum_prod_type_right]; ring
 constructor; · convert Thinner.sumThin univ (fun A=> ( (hp A).1).scale chPrice) using 1 <;> (first| rfl| simp only [abs_of_nonneg chPrice_pos.le, sum_const, nsmul_eq_mul, ←mul_assoc,card_univ,cp,one_mul]); all_goals rfl -- tune Show notation
 intro U; rw [separate R β U (M:=M)]; unfold totalWeak; simp_rw [sum_comm (f:=fun P A=> chPrice * debt d R p β M A P U),←mul_sum]; congr 1; conv_rhs=> rw [mul_sum];
 apply sum_congr rfl; intro i _; rw [(hp i).2 U]; ring
-- actual choices

def CI (A y : ℝ):= ⌈A*Real.log y⌉₊
lemma CL (u:ℝ)(p:0<u): Tendsto (CI u) atTop atTop:= by
 apply tendsto_nat_ceil_atTop.comp (Real.tendsto_log_atTop.const_mul_atTop p)
lemma CPL (u:ℝ)(p:0<u): PL fun y=> (CI u y:ℝ) := PL.ceil ((PL.const u).mul PL.log) ((eventually_gt_atTop (1:ℝ)).mono fun i t=>mul_nonneg p.le (Real.log_pos t).le)
lemma pli : NPL fun i:ℝ=> i⁻¹:= by refine npl_congr ((eventually_gt_atTop (0:ℝ)).mono fun i p=> (hat_price p)) ?_; simpa only [zpow_zero,mul_one] using root_tall 0 4 (by decide)
lemma purchaseWeak {σ : ℝ} (g:0<σ)(C Λ:ℝ) : ∀ᶠ u:ℝ in atTop, 0<u ∧
    NPL (fun y=> clipbill σ C Λ (2*y) (temp y) (CI u y)) := by
 have h : NPL (fun y=> y* temp y^3):=by
    refine npl_congr (F:=fun i=> root i ^2*heigh i ^24) ((eventually_gt_atTop (0:ℝ)).mono fun i t=>?_ ) (root_tall 24 2 (by omega)); have h : i=(root i ^4)⁻¹:=by rw [hat_price t,inv_inv]
    have he := root_pos t; rw [temp_price t]; nth_rw 1 [show i * _= _ from (congrArg (fun b:ℝ=> b*(root i^2 * heigh i^8)^3) h)]; field_simp -- tune
 have h4:= npl_congr (G:=fun y=> y* temp y^4) (Eventually.of_forall fun i=>by change _ * temp i= _; ring) (h.mul npl_temp.pl)
 have ht : NPL (fun y=> 2*y* ((Wt σ 8*(temp y^3*C))+ Wt σ 8*(temp y^4*C))) := by
    convert (h.const_mul (2*C*Wt σ 8)).add (h4.const_mul (2*C*Wt σ 8)) using 1; ext; ring
 let v:=(4:ℝ)/σ; have hv:0<v:=div_pos (by norm_num) g; filter_upwards [eventually_ge_atTop v] with L q; have hL:0<L:=hv.trans_le q; refine ⟨hL,?_⟩
 have p : NPL fun y:ℝ=> y*Real.exp (-σ/2*(CI L y)):= by
    refine pli.mono ((eventually_gt_atTop (1:ℝ)).mono fun i v=>?_ ); have hz:=Real.log_pos v; have hy:0 < i:= zero_lt_one.trans v; have ht:4≤ L*σ:=(div_le_iff₀ g).mp q; have hp: L*Real.log i ≤ CI L i:=Nat.le_ceil _; rw [abs_of_pos (by positivity : 0 < i*_),abs_of_pos (inv_pos.mpr hy)]
    have he: -σ/2*(CI L i) ≤ -Real.log i - Real.log i:= by nlinarith only [g,hp,mul_le_mul_of_nonneg_right ht hz.le]
    refine (mul_le_mul_of_nonneg_left (Real.exp_monotone he) hy.le).trans_eq ?_; rw [Real.exp_sub,Real.exp_neg,Real.exp_log hy]; field_simp
 have he : NPL (fun y=>2*y*((Fintype.card PlaqAxes:ℝ)*(Wt (σ/2) (CI L y+2)*refund σ C (CI L y)))) := by
    have hu : PL (fun y=> Wt (σ/2) (CI L y+2)):=by
       unfold Wt; push_cast; apply PL.mul _ (PL.const _); apply PL.mul _ (PL.const _); exact (((PL.const _).mul ((CPL L hL).add (PL.const 2))).add (PL.const 3)).pow _
    convert ((p.mul hu).const_mul (2*(Fintype.card PlaqAxes:ℝ)*2*C^2)) using 1; ext; unfold refund; ring
 convert ((he.add ht).add ((npl_power npl_temp 2 (by omega)).const_mul (Wt σ 8*Λ))) using 1; ext; unfold clipbill; ring
lemma tau_buy (M:ℝ→ℕ) (h:PL fun y=> (M y:ℝ))(g:0<σ) : ∃ a:ℝ→ℝ, PL (fun y=>(a y)⁻¹) ∧ ∀ y, 0<a y ∧ a y*17^4≤σ/2 ∧ a y*17^4*5≤1 ∧ a y≤σ/4 ∧ a y*(3+((2:ℝ)*M y+5)^4)≤1:=by
 let L:ℝ:= min 1 (σ/(4*17^4)); let x(y:ℝ):=17^4*5 +3+((2:ℝ)*M y+5)^4; have v(y:ℝ):3≤x y:= by unfold x; nlinarith [show 0≤ ((2:ℝ)*M y+5)^4 by positivity]
 have hx(y:ℝ):0<x y:=by linarith [v y]
 have k:L≤1:=min_le_left ..; have t:0<L:=lt_min zero_lt_one (by positivity); refine ⟨fun y=>L/x y,?_ ,?_⟩
 · simp_rw [inv_div,div_eq_mul_inv]; apply PL.mul _ (PL.const _); exact (PL.const _).add ((((PL.const 2).mul h).add (PL.const _)).pow 4)
 intro y; have hh(y) : 17^4*5 ≤ x y:= by unfold x; nlinarith [show 0≤ ((2:ℝ)*M y+5)^4 by positivity]
 have H:=hx y; have he: L/x y ≤ L:= div_le_self t.le (show 1≤ x y by linarith [v y]); have l:L≤ σ/(4*17^4):=min_le_right ..; have i(y) : (3+((2:ℝ)*M y+5)^4) ≤ x y:=by unfold x; linarith
 refine ⟨div_pos t H, by linarith [hh y], ?_, by linarith,?_⟩; rw [mul_assoc (L/_ ) _ _,div_mul_eq_mul_div, div_le_iff₀ H, one_mul]; nlinarith [hh y]
 rw [div_mul_eq_mul_div,div_le_iff₀ H,one_mul]; nlinarith only [i y,t,k,H]
lemma checks_purchase : ∀ᶠ u in atTop, 0<u ∧ ∀ᶠ y in atTop,∀ p : BudgetPoint,p.threshold=temp y→ Checks (CI u y) p d:=by
 let x:=2*d.relaxation; have h:=d.radius_pos; have hx:0<x:=by unfold x; positivity
 filter_upwards [eventually_ge_atTop x] with u p; refine ⟨hx.trans_le p,?_⟩; filter_upwards [eventually_ge_atTop (2:ℝ)] with y v p' q i g
 apply Nat.add_le_add_right (le_of_not_gt (fun ht : CI u y < i => not_lt_of_ge ?_ g)) _; rw [q]; have he : 2*Real.log y ≤ (i:ℝ)/d.relaxation :=by
    rw [le_div_iff₀ h]; apply le_trans _ (Nat.cast_le.mpr ht.le); have hl: 0≤ Real.log y:= Real.log_nonneg (by linarith); have hp:u*Real.log y ≤ CI u y:=Nat.le_ceil _; unfold x at p; nlinarith
 have hv:=Real.exp_monotone he; rw [two_mul, Real.exp_add,Real.exp_log (by linarith : 0<y)] at hv; have hz:0<y:=by linarith
 have hp:y⁻¹ ≤ temp y:=by
   rw [temp_eq]; apply le_trans _ (le_mul_of_one_le_right (g_pos hz).le (drift_one _)); rw [←gscale hz.le]; have ht:BPress.g y ≤1:=by unfold BPress.g Next.Scheduling.Clock.gap; apply inv_le_one_of_one_le₀; nlinarith [Real.sq_sqrt hz.le,Real.sqrt_nonneg y]
   nlinarith [g_pos hz] -- tune
 apply le_trans _ (mul_le_mul hp hv (by positivity) (temp_pos hz).le); field_simp; nlinarith -- tune neg

/-- eq:B-wn with the selected charges. Supports fixed from VolB-gauge text. All germs on the physical variables *before* axial integration. -/
theorem weak_purchase (g:0<σ)(C Λ:ℝ): ∀ᶠ u:ℝ in atTop, 0<u ∧ ∃ r a:ℝ→ ℝ, NPL r ∧ PL (fun y=>(a y)⁻¹) ∧ (∀ y,0<a y) ∧ ∀ᶠ y in atTop, ∀ (p : BudgetPoint), p.threshold=temp y→ Checks (CI u y) p d ∧ ∀ (s:Side)(G:Gauge)(R:PathData G)(β:ℝ), R.Bounds d σ C Λ →β∈ Set.Icc (y/2) (2*y) → Thinner (s:=s) (totalWeak d R p β (CI u y)) (fullWeak R p β (CI u y)) (a y) (r y) ∧ ∀ U:Config G s,
    R.inChannels d p β U= ∑ x:Face (Per s), hide d p β U x + ∑ z:Signed, (∑ x:Face (Per s), kept d p R β (CI u y) z U x) + ∑ P,totalWeak d R p β (CI u y) P U:=by
 filter_upwards [purchaseWeak g C Λ,checks_purchase d] with u l h; obtain ⟨a,H,T⟩:= tau_buy (CI u) (CPL _ h.1) g
 refine ⟨h.1,_,a,l.2,H,fun i=> (T i).1,?_⟩; filter_upwards [h.2,eventually_ge_atTop (0:ℝ)] with y Q t p q; have hp:= Q p q; refine ⟨hp,fun s G R β v w=>?_⟩; obtain ⟨f,b⟩:= w; obtain ⟨i,h',q',l,P⟩:= T y; obtain ⟨w,H⟩:= total_script (s:=s) d R p β (CI u y) v hp (by linarith) i.le h' q' l P; refine ⟨w.low le_rfl ?_,H⟩; unfold clipbill; rw [←q]; gcongr; have hb:=budget_nonneg v.three; unfold Wt refund; positivity [p.threshold_pos] -- tune def expansion
end YM.CF.BPress.Wealth
