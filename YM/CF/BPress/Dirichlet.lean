import YM.CF.BPress.Schedule
import YM.CF.BPress.Count
import YM.CF.BPress.Curved
import YM.CF.BPress.Lifts
import YM.CF.BPress.Test
import Mathlib.MeasureTheory.Integral.Pi
/-! VolumeB-gate pp. Dirichlet angular mark. Closed ball densities.
Proof of eq:B-ang-M for the initial mark using FiniteGaugeData shell estimate (coarser ambient-dimensional
volume price is enough; not changing the ball measure). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function Filter Finset Lattice Wilson RG Pressure SU LocalH Mag Cube Fixed Fock
open scoped Topology BigOperators Classical Matrix
abbrev Micro (s : Side) := Wilson.Config group s
variable {s : Side}
abbrev Link (s : Side) := Edge (Site s)
def inside (S : Support s) : Finset (Link s) := univ.filter fun i=> i.1∈S ∧ i.1+step i.2∈S
@[simp] lemma inside_iff (S : Support s) (i : Link s) : i∈inside S ↔ i.1∈S ∧ i.1+step i.2∈S:=by simp [inside]
lemma inside_bound (S : Support s) : (inside S).card≤ S.card * 4:= (card_le_card (show inside S ⊆ S ×ˢ univ from fun i p=> mem_product.mpr ⟨((inside_iff ..).mp p).1, mem_univ _⟩)).trans_eq (by simp [Axis])

def backgroundDir : Axis → group.Color:= Fin.cons 0 generator
def background (y : ℝ) : Micro s:= fun i=> group.lieExp (aA y • backgroundDir i.2)
lemma square_background (y : ℝ) (i : Face (Per s)) : faceValue (background y) i=
    chord.panel (backgroundDir i.2.val.1) (backgroundDir i.2.val.2) (aA y):= by simp [faceValue,background,chord.panel,travel,square,mul_assoc]
lemma background_normal (y : ℝ) (x : Site s): background y (x,0)=1:= by simp [background,backgroundDir]

-- initial Mark density (not beta-weighted)
def dirichlet (S : Support s) (y : ℝ) (U : Micro s) : ℝ:= ∏ i∈inside S, chord.ballDensity (xi y) (background y i) (U i)
variable (S : Support s) (y : ℝ)
lemma dirichlet_local : LocalOn S (dirichlet S y):= by
  intro U V p; apply prod_congr rfl; intro i h; rw [p i ((inside_iff ..).mp h).1 ((inside_iff ..).mp h).2]
open MeasureTheory
lemma dirichlet_meas : Measurable (dirichlet S y):= by
 unfold dirichlet; apply Finset.measurable_fun_prod; intro i _; exact (chord.density_meas (G:=group) (xi y)).comp (f:=fun x : Micro s=>(background y i,x i)) (measurable_const.prodMk (measurable_pi_apply i))
lemma dirichlet_bound (U : Micro s) : |dirichlet S y U|≤chord.charge group (xi y) ^ (inside S).card:=by
  rw [dirichlet,Finset.abs_prod,← prod_const]; refine prod_le_prod (fun _ _=>abs_nonneg _) fun _ _=>chord.bound ..
lemma on_ball (U : Micro s)(p : dirichlet S y U≠0) : chord.Close U (background y) S (xi y) := fun i l g=> chord.density_ne _ _ _ (fun h=>p (prod_eq_zero ((inside_iff ..).mpr ⟨l,g⟩) h))
lemma dirichlet_prob (p : 0<xi y) (q : xi y ≤ 1) : ∫ U, dirichlet S y U ∂prior group s=1 := by
  let f(i:Link s)(x:E):=if i∈inside S then chord.ballDensity (xi y) (background y i) x else 1
  have hi : dirichlet S y=fun U=>∏ i,f i (U i):=funext fun U=> by simp [dirichlet,f,←prod_filter, -inside_iff]
  rw [hi,prior,integral_fintype_prod_eq_prod]; apply prod_eq_one; intro i _; by_cases h:i∈ inside S
  · simp only [f,h,↓reduceIte]; exact chord.density_integral _ p q
  simp only [f,h,↓reduceIte]; simp

section frob
open scoped Matrix.Norms.Frobenius Asymptotics
-- polylog-one estimate on log density
lemma ball_charge_bound : ∃ C : ℝ, 0<C ∧ ∀ᶠ y:ℝ in atTop,
    1 ≤ chord.charge group (xi y) ∧ chord.charge group (xi y) ≤ Real.exp (C*Real.log y):=by
  let d:= Module.finrank ℝ group.Mat; let C:ℝ:= (d:ℝ)*4+1; have hc:0<C:= by unfold C; positivity
  refine ⟨C,hc,?_⟩; filter_upwards [npl_xi.drop.eventually (ge_mem_nhds zero_lt_one),eventually_gt_atTop (4:ℝ)] with y p q
  have hy : 1<y:= by linarith
  have hp:=xi_pos (zero_lt_one.trans hy); refine ⟨chord.charge_high hp p,?_⟩; unfold chord.charge; have h:= group.shell_ge (xi y) hp p
  apply le_trans (inv_anti₀ (pow_pos (show 0< xi y/4 by positivity) _) h); rw [← inv_pow]; have ht : (xi y/4)⁻¹ ≤ y^4:= ?_
  · unfold C; rw [add_mul,one_mul,Real.exp_add, mul_assoc,Real.exp_nat_mul, show (4:ℝ)=↑(4:ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log (by linarith : 0<y)]; exact le_trans (pow_le_pow_left₀ (by positivity) ht d) (le_mul_of_one_le_right (by positivity) hy.le)
  -- ξ^-1 = y^1.5, bound crude via sqrt
  have hz : Real.sqrt y≥1:=by nlinarith [Real.sqrt_nonneg y,Real.sq_sqrt (zero_lt_one.trans hy).le]
  rw [xi,g,Next.Scheduling.Clock.gap,inv_div]; have hh: 4/ (Real.sqrt y)⁻¹^3=4 * Real.sqrt y ^ 3:= by field_simp
  rw [hh,pow_succ' _ 3]; gcongr; nlinarith [Real.sq_sqrt (zero_lt_one.trans hy).le]

/-- fixed-constant Taylor estimate including curvature used by the N face. -/
theorem background_cost (W : chord.Chart group) : ∃ C : ℝ, 0<C ∧ ∀ᶠ y in atTop,
    ∀ (s : Side) (i : Face (Per s)), let H:= faceValue (background y) i
    group.chord H < W.δ ∧ group.chord H ≤ C*mA y ∧
    dist (snap group H) (mA y • group.ad (backgroundDir i.2.val.1) (backgroundDir i.2.val.2)) ≤ C*(aA y)^3 := by
  choose C c t using fun i j : Axis=> chord.panel_log_bound (backgroundDir i) (backgroundDir j) W
  obtain ⟨K,h⟩:= chord.exp_lip group W.eps; let f(i j:Axis):= group.ad (backgroundDir i) (backgroundDir j)
  let Q:=1+∑ i:Axis,∑ j:Axis,(‖f i j‖ + C i j); have hh(i j:Axis): ‖f i j‖+C i j ≤ Q:=by
    have hc(i j:Axis) : 0 ≤ ‖f i j‖+ C i j:= add_nonneg (norm_nonneg _) (c i j).le
    refine le_trans ?_ (le_add_of_nonneg_left (b:=1) (by norm_num)); exact (single_le_sum (f:=fun j=>‖f i j‖+C i j) (fun j _=> hc i j) (mem_univ j)).trans (single_le_sum (f:=fun i=>∑ j:Axis,(‖f i j‖+C i j)) (fun i _=>sum_nonneg fun j _=>hc i j) (mem_univ i))
  let F:ℝ:= K/group.colorScale; have hF:0≤F:=div_nonneg K.property group.colorScale_pos.le; have he(i j:Axis): C i j≤Q:=(le_add_of_nonneg_left (norm_nonneg (f i j))).trans (hh ..)
  have hQ:0<Q:=(c 0 0).trans_le (he 0 0); refine ⟨ Q + F* Q, by positivity,?_ ⟩; filter_upwards [eventually_all.mpr (fun i : Axis=> eventually_all.mpr (fun j : Axis=> npl_aA.drop.eventually (t i j))),eventually_gt_atTop (0:ℝ),npl_aA.drop.eventually (ge_mem_nhds zero_lt_one)] with y p l v
  intro s k; dsimp only; let i:=k.2.val.1; let j:=k.2.val.2; let Y:=(f i j); let m:= mA y; let X:= faceValue (background y) k; have hx:=square_background y k; change X=_ at hx
  obtain ⟨x,g⟩:=p i j; rw [abs_of_pos (aA_positive l), aA_sq l,←hx] at g; rw [←hx] at x; refine ⟨x,?_,g.trans (mul_le_mul_of_nonneg_right ((he i j).trans (le_add_of_nonneg_right (by positivity))) (pow_nonneg (aA_positive l).le _))⟩
  let V':= snap group X
  have hu:= h.dist_le_mul V' (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact (W.snap_small X x.le).le)) 0 (Metric.mem_closedBall_self W.radius.le)
  have hm: 0≤m:=(mA_pos l).le; have ha: ‖V'‖ ≤ Q*m:=by
     have hv:=hh i j; rw [dist_eq_norm] at g; have hc:= (norm_le_norm_sub_add V' (m • Y)); rw [norm_smul, Real.norm_of_nonneg hm] at hc; have hj : aA y ^3≤m:=by rw [pow_succ,aA_sq l]; exact mul_le_of_le_one_right hm v
     replace g:=g.trans (mul_le_mul_of_nonneg_left hj (c i j).le); change ‖V'-m • Y‖ ≤ C i j * m at g; nlinarith only [hc,g,mul_le_mul_of_nonneg_left hv hm]
  change group.chord X≤_; rw [← chord.one, chord.mat_eq]; change _ ≤ _ * m
  unfold chord.emb at hu; rw [dist_eq_norm,W.read _ x.le,group.mat_lieExp_zero,dist_zero_right] at hu; refine le_trans (div_le_div_of_nonneg_right (hu.trans (mul_le_mul_of_nonneg_left ha K.property)) group.colorScale_pos.le) ?_; apply le_trans (b:= F*Q*m) _ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hQ.le) hm); exact Eq.le (by unfold F; ring)
set_option maxHeartbeats 550000 in
lemma dirichlet_support : ∃ C : ℝ, 0<C ∧ ∀ᶠ y in atTop, ∀ (s : Side) (S : Support s) (U : Micro s),
    dirichlet S y U≠ 0 → ∀ i : Face (Per s), touched i ⊆ S → group.chord (faceValue U i) ≤ C*mA y := by
  obtain ⟨C,p,Q⟩:= background_cost (chord.chart group).some; have he:=npl_congr (F:=fun y=> root y^4 * heigh y ^ (-6:ℤ)) (G:=fun y=> xi y/mA y) ((eventually_gt_atTop (0:ℝ)).mono fun y p=> by have ht:=root_pos p; have hk:=heigh_pos y; rw [xi_price p,mA_price p,zpow_neg]; field_simp) (root_tall _ _ (by norm_num)); refine ⟨4+C,by positivity,?_⟩; filter_upwards [Q,npl_a1 _ _ he zero_lt_one ((eventually_gt_atTop (0:ℝ)).mono fun i p=> mA_pos p)] with y q u s S U X i k; rw [one_mul] at u; have h:= (q s i).2.1; rw [← chord.one]; calc
    _ ≤ 4*xi y+ C*mA y:= (chord.triangle _ (faceValue (background y) i) _).trans (add_le_add (chord.face U _ i _ (chord.Close.smaller _ _ (r:=xi y) k (on_ball S y U X))) (by rw [chord.one]; exact h))
    _ ≤ _:=by linarith only [u]
end frob

open scoped Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
lemma dirichlet_isMark {N : Side} (S : Support (More N))(y:ℝ) : IsMark S (fun U => (dirichlet S y U: ℂ) • (1:FC (Tulip.Single N))) (chord.charge group (xi y) ^ (inside S).card) := by
  rw [← mul_one (chord.charge group (xi y)^_)] -- tune
  apply (IsMark.one S).factor (c:=fun U=> ↑(dirichlet S y U)) (fun _ _ p=>congrArg _ (dirichlet_local S y _ _ p)) (Complex.continuous_ofReal.measurable.comp (dirichlet_meas S y))
  intro U; rw [Complex.norm_real]; exact dirichlet_bound S y U
lemma angular_bill : ∃ C : ℝ, 0<C ∧ ∀ᶠ y : ℝ in atTop, ∀ (N : Side) (B : BandWidth) (X : Bands (More N) B) (i : X.Index),
    IsMark (X.band i) (fun U=> (dirichlet (X.band i) y U:ℂ) • 1) (Real.exp (C * B.P * Real.log y * (More N).val^3)) := by
  obtain ⟨C,v,Q⟩:= ball_charge_bound; refine ⟨8*C,by positivity,?_⟩; filter_upwards [Q,eventually_gt_atTop (1:ℝ)] with y p q N B X i
  let T:=X.band i; apply (dirichlet_isMark T y).weaken (Subset.refl _); apply le_trans (pow_le_pow_left₀ (zero_le_one.trans p.1) p.2 _); rw [← Real.exp_nat_mul]; apply Real.exp_monotone
  have h:(inside T).card≤ B.P*2*(More N).val^3*4:=by
     apply (inside_bound T).trans; rw [X.band_card]; gcongr; unfold BandWidth.P; apply le_trans (b:= B.marked.val*2); · have e : 0 < B.marked.val:= B.marked.property; omega
     exact Nat.mul_le_mul_right _ (by omega)
  have hx:( (inside T).card:ℝ) ≤ (B.P:ℝ)*2*((More N).val:ℝ)^3*4:= by exact_mod_cast h
  refine (mul_le_mul_of_nonneg_right hx (mul_nonneg v.le (Real.log_pos q).le)).trans ?_; exact Eq.le (by ring)
end YM.CF.BPress
