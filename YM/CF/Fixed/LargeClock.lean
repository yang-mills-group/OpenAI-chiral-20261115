import YM.CF.Fixed.Leak
import YM.CF.Mint.Cash

/-!
# Superlog windows

Cancellation for same gauge/fermion comparison. Powers of `Teller.price` are
prioritized over **any poly-log** exponent. Can admit (subject to decisions
AFTER Teller constants but BEFORE every period wager) C*(kinetic suppressor):
`vast = x*t²`. In THIS file, no license to use at literally unrestricted
increasing volumes with a **fixed** x. That still breaks the budget. See
later audit. Nothing changes in `Mint.Roe.echo`; we will need its *analogue*
not relying on the old polynomial window path assumptions. Here we still
prescribe identical scalar clock functions.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Fixed.Extensive
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial Nacre Font Laic Graph Skye Wilson MeasureTheory Paige Vault Pivots RG Emu Flare
open Sods Vale Nova Pressure
open Mint Roe
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
variable {x β U A:ℕ→ℝ}
lemma vast_temp (h:Tendsto x atTop atTop): Aqua (vast x) (tame x) := by
  let V:=lum x; let F(i:ℕ):= Real.log (V i)
  have hp:Tendsto V atTop atTop:= Mint.tc h
  have he:Tendsto (fun i=> F i^2/V i) atTop (𝓝 0):= by have he:= Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero; simpa [F,Function.comp_def] using he.comp hp
  intro n
  let C:= (2*(n:ℝ)+1); have hu:0<C:=by unfold C; positivity
  let f(i:ℕ):= Real.exp (-(1/4:ℝ)*V i); have hf:Tendsto f atTop (𝓝 0):=(Aqua.exp_neg hp _ (by positivity : 0<(1:ℝ)/4)).shrinks
  have hb:= ((he.const_mul C).eventually (ge_mem_nhds (show C*0 < 1/4 by rw [mul_zero]; norm_num)))
  refine squeeze_zero' ?_ ?_ hf
  · filter_upwards [h.eventually_gt_atTop 0,vital h|>.eventually_gt_atTop 0] with i e k; exact mul_nonneg (pow_nonneg k.le _) ((Work.E09.temp_pos e).le)
  filter_upwards [burn h,h.eventually_gt_atTop 0,hb,hp.eventually_gt_atTop 0] with i v hX k s; have hx:0<tame x i:=Work.E09.temp_pos hX
  change (vast x i)^n * tame x i ≤ f i
  have hv: (vast x i)^n=Real.exp (n*(2*(F i)^2)):=by rw [v, Real.exp_nat_mul]
  rw [hv]; nth_rw 1 [← Real.exp_log hx]; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
  have hm: Real.log (tame x i) = -(V i)/2+(F i)^2:=by unfold tame temp; rw [Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_sqrt hX.le, Real.log_exp]; unfold F V Mint.lum; ring
  rw [hm]; change C*(F i^2/V i)≤1/4 at k; rw [← mul_div_assoc] at k; nlinarith [(div_le_iff₀ (show 0 < V i from s)).1 k]

def tariff (β t C L:ℝ):= β*C*(t^3+t^4)+L*t^2
def measureGold (β A T B H:ℝ):= 6*β * (goldY T A T B)+H -- A=direct, T=4z, H=tariff; gauge side only
lemma true_card (n:Side): Fintype.card (Face (Per n))=6*n.val^4:=by change Fintype.card (Site n × PlaqAxes)=_; rw [Fintype.card_prod,site_card, show Fintype.card PlaqAxes=6 from by decide]; omega
lemma tax_eq (n:Side)(β t C L:ℝ): taxY n β t C L=(n.val:ℝ)^4*tariff β t C L:=by unfold taxY tariff; ring
lemma charge_eq (n:Side)(v η C:ℝ): chargeE n v η C=(n.val:ℝ)^4*(4*C+16*(v+v+η)+180*45*(6*C)):=by unfold chargeE pittance doorF lark More; push_cast; ring
lemma total_eq (n:Side)(k β t C L:ℝ): totalTitle n k t β C L=(n.val:ℝ)^4*(6*k + tariff β t C L):=by unfold totalTitle; rw [tax_eq,true_card]; push_cast; ring
lemma measuredGold (n:Side)(t k β h C L:ℝ): stoutY n β t h k C L=(n.val:ℝ)^4*measureGold β h t C (tariff β k C L):=by unfold stoutY; rw [tax_eq,true_card]; unfold measureGold goldY; push_cast; ring
lemma income (C L:ℝ)(P:RangeH x β (1/2) 2): Tendsto (fun i=> tariff (β i) (tame x i) C L) atTop (𝓝 0):= by
  let A:=lum x; let V:=vast x; let T:=tame x; have ht:=vast_temp P.rank; have hx:= vital P.rank
  have he: Gray V (fun i=> β i/x i):=by
    refine ⟨2,by norm_num,0,?_⟩; filter_upwards [P.bound,P.infl] with i t v; rw [Real.norm_eq_abs,abs_of_pos (div_pos v.2.1 v.1),pow_zero,mul_one]; exact (div_le_iff₀ v.1).mpr t.2
  let f(i:ℕ):=β i/x i; have hu:= ht.pays (Gray.thin hx ht.shrinks) hx
  refine (Aqua.panel ((Aqua.fed (G:=fun i=>f i*C*V i) (ht.panel hu) ((he.mul (Gray.coef hx C)).mul (Gray.arg hx)) hx)) (hu.fed (Gray.coef hx L) hx)).shrinks.congr' ?_
  filter_upwards [P.infl] with i u; change f i*C*V i*(T i+T i*T i)+L*(T i*T i)=_; unfold f V T vast tariff; field_simp [u.1.ne']
open Mint
lemma printB (y:ℝ)(p:0<y) : y * (((Real.sqrt y)⁻¹/4)^2)=1/16 := by rw [div_pow,inv_pow,Real.sq_sqrt p.le]; field_simp; norm_num
lemma compareShell (x':ℝ)(u:ℝ)(h:0<x')(hu:u=(Real.sqrt x')⁻¹/4)(hp:u≤1): -(Real.log (shellMass group u)) ≤ (Module.finrank ℝ group.Mat:ℝ)*(Real.log x'/2 + (Real.log 4 + Real.log 4)):= by
  subst u; let u:=(Real.sqrt x')⁻¹/4; have hV:0<u:=by unfold u; positivity; -- benchmark
  have he:= Real.log_le_log (show 0 < (u/4)^Module.finrank ℝ group.Mat by positivity) (group.shell_ge u hV hp)
  rw [Real.log_pow] at he; change -Real.log (shellMass _ u)≤_
  change ↑(Module.finrank ℝ group.Mat)*Real.log (u/4)≤ Real.log (shellMass _ u) at he
  have ht:Real.log (u/4) =-(Real.log x'/2 + (Real.log 4 + Real.log 4)):=by unfold u; rw [Real.log_div (by positivity) (by norm_num),(Real.log_div (by positivity) (by norm_num)), Real.log_inv,Real.log_sqrt h.le]; ring
  rw [ht] at he; linarith

variable {L:Side}{k b A' w C0 C1 C2 C3:ℝ}
-- post-L BEFORE bounds. `D` stencil mass absolute coefficient, `P.paths` prior clinic template.
-- use total ceiling exactly at powers of `vast`.
def borderK(C L R T A E H:ℝ):= -- Cost per matter volume; H allowance both v and η
  64*Real.log T + (4*C+48*H+180*45*(6*C)) + 16*(6*A+1) + 16*(12*(E/2+L^2/2)+1)+R
-- L gauge path, E direct, R fermion lower, T Haar upper, A=saltK.
lemma foretell {D L B T β u k t v η C b F w X:ℝ}(n:Side)
    (p:tariff β t L B ≤ 1)(W:w/4*X≤ β*(w*t^2)/2)(θ:0≤ D)(e:β*u^2≤1/8)(hx:v≤F)(hy:η≤F):
    volumeBand n u T b (chargeE n v η C+flagTitle (More n) k t β w L B) (stoutY (More n) β (4*u) D t L B) ≤ (n.val:ℝ)^4* borderK C L b T k D F - w/4*X -4*Real.log (shellMass group u):=by
  unfold volumeBand flagTitle; rw [charge_eq,total_eq,measuredGold]
  have he: measureGold β D (4*u) L (tariff β t L B)≤12*(D/2+L^2/2)+1:=by
    unfold measureGold goldY; apply add_le_add _ p; calc 6*β*(D*(4*u)^2/2+(L*(4*u))^2/2)=96*(β*u^2)*(D/2+L^2/2) := by ring
                                                          _ ≤ _:=by nlinarith [mul_le_mul_of_nonneg_right e (show 0≤D/2+L^2/2 by positivity)]
  have hg: ((More n).val:ℝ)^4=16*(n.val:ℝ)^4:=by unfold More; push_cast; ring
  rw [hg]; unfold borderK; let q :ℝ:=n.val^4; have hp : 0 ≤ (n.val:ℝ)^4:=by positivity
  linarith [mul_le_mul_of_nonneg_left p hp,mul_le_mul_of_nonneg_left he hp, mul_le_mul_of_nonneg_left hx hp,mul_le_mul_of_nonneg_left hy hp]

-- α path is an eventually-in-x statement; threshold to be quantified later.
abbrev saltBudget (k:ℝ):= k/64
def penaltyK (w C:ℝ):= w/(16*(1+|C|))
lemma penalty_pos (h:0<w)(B:ℝ):0<penaltyK w B:=by unfold penaltyK; positivity
lemma weather(P:RangeH x β (1/2) 2)(h:0<w)(F:ℕ→Clip)(hx:∀ᶠ i in atTop,w≤(F i).linear): let B:=hemp x
    ∀ᶠ i in atTop, β i*(B i)^2 ≤1/8 ∧ 2*saltBudget w≤β i*((F i).direct*(B i)^2/2) ∧ 2*saltBudget w≤β i*((F i).linear*tame x i*B i) := by
  intro B
  filter_upwards [hx,P.bound,P.infl,P.helm] with i e u v k
  have he:x i*(B i)^2 =1/16:= printB (x i) v.1; have ht:= v.2.1; have hp:0 < B i:=k.1
  have hv:1/32≤β i*(B i)^2:=by nlinarith [mul_le_mul_of_nonneg_right u.1 (sq_nonneg (B i))]
  have hu:4*B i≤tame x i:= k.2.2
  unfold saltBudget; have hq:= (F i).tail_pos; have hd:= (F i).kink
  refine ⟨?_ ,?_,?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right u.2 (sq_nonneg (B i))]
  · nlinarith only [mul_le_mul_of_nonneg_left hv ((F i).quadratic_pos.le), hd, h, e]
  nlinarith only [mul_le_mul_of_nonneg_left hv hq.le, e, h, mul_le_mul_of_nonneg_left hu (show 0≤ β i*(B i)*(F i).linear by positivity)]

lemma barred (P:RangeH x β (1/2) 2)(w_ : 0<w)(v η:ℕ→ℝ)(F:ℝ)(p:∀ᶠ i in atTop, v i≤ F∧η i≤ F)
    (D L k T b B H:ℝ)(θ:0≤D) : ∀ᶠ i in atTop,∀ n:Side,(n.val:ℝ)^4 ≤ penaltyK w (borderK H L b T k D F)*vast x i → volumeBand n (hemp x i) T b (chargeE n (v i) (η i) H+flagTitle (More n) k (tame x i) (β i) w L B) (stoutY (More n) (β i) (4*hemp x i) D (tame x i) L B) ≤ -(w/8)*vast x i:=by
  let C:= borderK H L b T k D F; let M:= vast x
  let U:= hemp x; let A:= lum x; let V(i:ℕ):= 4*(Module.finrank ℝ group.Mat:ℝ)*(A i/2 +(Real.log 4+Real.log 4)); have he:Tendsto (fun i=>V i / M i) atTop (𝓝 0):=by
    have ht:= Mint.tc P.rank; have hp:= Aqua.fed (G:=V) (frost P.rank) (by
      unfold V; simp only [div_eq_mul_inv]; exact (Gray.coef ht _).mul <| Gray.add ht ((Gray.arg ht).mul (Gray.coef ht _)) (Gray.coef ht _)) ht; simpa only [div_eq_mul_inv] using hp.shrinks
  filter_upwards [p,P.helm,P.bound,P.infl, he.eventually (ge_mem_nhds (show 0<w/16 by positivity)),(income L B P).eventually (ge_mem_nhds one_pos)] with i ℓ h e xH s t n z
  have hv:0<U i:= h.1; have hM:0<M i:= xH.2.2.2
  have hw:= foretell (C:=H) (u:=U i) (T:=T) (k:=k) (b:=b) n t (by
    show w/4*M i ≤ β i*(w*tame x i^2)/2; unfold M vast; nlinarith only [mul_le_mul_of_nonneg_right e.1 (show 0 ≤ w*tame x i^2 by positivity)]) θ (by
    have hp: x i * (U i)^2=1/16:= printB (x i) xH.1; nlinarith [mul_le_mul_of_nonneg_right e.2 (sq_nonneg (U i))]) ℓ.1 ℓ.2
  have hu : -4*Real.log (shellMass group (U i)) ≤ w/16*M i:=by have ht:= compareShell (x i) (U i) xH.1 rfl h.2.1; have hp:= (_root_.div_le_iff₀ hM).mp (show V i/M i≤w/16 from s); unfold V A Mint.lum at hp; linarith
  apply hw.trans; change _*C - w/4*M i -4*_ ≤ _ -- tune not_eq
  have hp : (n.val:ℝ)^4*C ≤ w/16*M i:=by
    let K:=1+|C|; have hC:(n.val:ℝ)^4≤ w/(16*K)*M i:=z; calc
      _ ≤ (n.val:ℝ)^4 * K := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (by unfold K; linarith)) (by positivity)
      _ ≤ (w/(16*K)*M i)*K := mul_le_mul_of_nonneg_right hC (by unfold K; positivity)
      _ = _ := by unfold K; field_simp
  linarith
end YM.CF.Fixed.Extensive
