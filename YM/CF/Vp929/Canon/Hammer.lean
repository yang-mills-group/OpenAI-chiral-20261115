import YM.CF.Vp929.Canon.Reel
import YM.CF.Vp929.Phase.Lien
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
set_option quotPrecheck false
open Cycle929 Salt
variable {P:BudgetPoint}{n L:Side} {h c w q a d:ℝ} {F:Scree.InkD n} {T: RegBudget n}
local notation "D'"=> RegBudget n
local notation "t"=> P.threshold
local notation "G"=> SU.group
local notation "bι"=> (More n).val
local notation "Θ"=> transverse (s:=n) q
local notation "λt"=> AnalyticBridge.VerifiedReset.line
abbrev unRl (F:Scree.InkD n):= Complex.reCLM ∘ Taxi.lifeH F
abbrev weightB (q:ℝ)(T:RegBudget n)(X:Scree.Hub n):=logHessian (unRl (T X)) (transverse q) (transverse q)
local notation "V'"=> Skye.Seat n
variable {X:Scree.Hub n}
local notation "o"=> X.val.1
section
variable (g:PressB P X F h c)(u:1≤ h)
include g u
lemma lintR:BandS P X (unRl F) (‖Complex.reCLM‖*c):= cashR F X g (zero_le_one.trans u) Complex.reCLM ‖Complex.reCLM‖ le_rfl
lemma rind (x:tangD n):ContDiffAt ℝ ((↑(2:ℕ):WithTop ℕ∞)) (unRl F ∘ λt x) 0:=by
 have hg: ContDiffAt ℝ 2 (unRl F ∘ increment 1) 0:= AnalyticBridge.VerifiedReset.germ_diff (lintR g u).regular; norm_num; exact (show ContDiffAt ℝ 2 _ ((0:ℝ) • x) by rw [zero_smul]; exact hg).comp _ (f:=fun y:ℝ=>y • x) (by fun_prop)
lemma alongR (x:tangD n):iteratedDeriv 2 (unRl F ∘ λt x) 0=logHessian (unRl F) x x:=Work.F03.line_second (AnalyticBridge.VerifiedReset.germ_diff (lintR g u).regular) (AnalyticBridge.VerifiedReset.flat_critical Thera.yet_one (lintR g u).regular) x
lemma reohl : logHessian (unRl F) Θ Θ= logHessian (unRl F) (pitch q o) (pitch q o):=by
 simp only [← alongR g u]; have he:unRl F ∘ λt Θ=unRl F ∘ λt (pitch q o):=by
    funext w; unfold AnalyticBridge.VerifiedReset.line; simp only [Function.comp_apply]; rw [←jaunty];
    unfold Taxi.lifeH; rw [g.gaugeV]; exact congrArg Complex.reCLM (Pastry.center_b ..).symm
 rw [he]
omit g u
private lemma dir_price (a:ℝ)(e:0<a)(Z:tangD n)(p:∀ i:Edge V',‖Z i‖≤ a*(1+(separation i.1 o:ℝ))^2) (k:P.power=2) : P.dirBound o ((P.threshold/a) • Z):=by
 have h:=P.threshold_pos; intro i; rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg (by positivity : 0≤ t/a),k]; exact (mul_le_mul_of_nonneg_left (p i) (by positivity : 0≤t/a)).trans_eq (by rw [←mul_assoc,div_mul_cancel₀ _ e.ne'])
include g u
private lemma projections {x y:tangD n}{p p':ℝ}(a:0<p)(a':0<p')(hx:P.dirBound o (p • x))(hy:P.dirBound o (p' • y)): |logHessian (unRl F) x y|≤ ‖Complex.reCLM‖*c/(p*p'):=by
 have hp: ∀ i:Fin 2,P.dirBound o ((![(p • x), (p' • y)]:Fin 2→tangD n) i):=fun i=> by fin_cases i; exact hx; exact hy
 have he:‖logHessian (unRl F) (p • x) (p' • y)‖ ≤ _ := ((lintR g u).toll 1 (ping_f P _)).token 2 ((show 2≤6 by norm_num).trans P.order_ge) _ hp; rw [show logHessian (unRl F) (p • x) (p' • y)= p*p'*logHessian (unRl F) x y by rw [hessian_eq,hessian_eq,map_smul,map_smul,_root_.smul_apply]; simp only [smul_eq_mul]; ring,Real.norm_eq_abs,abs_mul,abs_of_pos (mul_pos a a')] at he; exact (le_div_iff₀ (mul_pos a a')).2 (by rw [mul_comm]; exact he)
lemma spin_long (hB:4≤ bι)(H:Frequency L n q)(k:P.power=2) : |logHessian (unRl F) Θ Θ|≤ (90000*‖Complex.reCLM‖)*P.threshold⁻¹^2*c :=by
 rw [reohl g u]; let W:= dir_price (X:=X) 300 (by norm_num) (pitch q o) (pitch_L hB H o) k; have he:=P.threshold_pos; refine (projections g u (show 0<t/300 by positivity) (show 0<t/300 by positivity) W W).trans_eq ?_; field_simp; ring
private lemma null_aff (s: Beau.spark o F)(x: tangD n)(hx:IsAffineDirection o x):logHessian (unRl F) x x=0:=by
 have ht:= s.2 _ _ hx hx; have h:iteratedFDeriv ℝ 2 (Taxi.lifeH F ∘ increment 1) 0 ![x,x]=0:=ht
 change iteratedFDeriv ℝ 2 (Complex.reCLM ∘ (Taxi.lifeH F ∘ increment 1)) 0 _=_; rw [Complex.reCLM.iteratedFDeriv_comp_left (profit g (zero_le_one.trans u)) le_rfl]; exact (congrArg Complex.reCLM h).trans (map_zero _)
lemma spin_short (hB:4≤ bι)(H:Frequency L n q)(k:P.power=2)(p: Vast L.val P.B n)(h': shortHub P L.val X)(s: Beau.spark o F) : |logHessian (unRl F) Θ Θ|≤ 2*‖Complex.reCLM‖* q * P.threshold⁻¹^2*c:=by
 let x:= pitch q o; let y:= soundX q o; let w:=tiltX q o; let v:=y-w; let p0:=H.pos
 have hg:P.dirBound o (t • y):=div_one P.threshold ▸ dir_price (X:=X) 1 zero_lt_one y (fun i=> (sound_L H o i).trans (by rw [one_mul]; have hp : (0:ℝ) ≤ separation i.1 o:=(by positivity); nlinarith)) k;
 have he:P.dirBound o (t • w):=div_one P.threshold ▸ dir_price (X:=X) 1 zero_lt_one (tiltX q o) (fun i=> (tilt_L o i).trans (by rw [one_mul]; have hp : (0:ℝ) ≤ separation i.1 o:=(by positivity); nlinarith)) k
 have hs:P.dirBound o ((t/q) • v):=dir_price (X:=X) q p0 v (fun i=> difference_L H o i) k
 have h:=P.threshold_pos; have hx:=null_aff g u s w (affineTilt q o)
 rw [reohl g u,AnalyticBridge.VerifiedReset.hessian_agrees Thera.yet_one (lintR g u).regular (meet p X h' hB) (meet p X h' hB), show logHessian (unRl F) y y=logHessian (unRl F) v y +logHessian (unRl F) w v by unfold v; simp_rw [hessian_eq] at *; simp only [map_sub,_root_.sub_apply,hx,sub_zero]; abel]; refine (abs_add_le _ _).trans ((add_le_add (projections g u (div_pos h p0) h hs hg) (projections g u h (div_pos h p0) he hs)).trans_eq ?_); field_simp; ring
end
lemma exponent_track (x:tangD n)(p:BudgetPoint)(F: RegBudget n): (fun z=> (Pastry.pane (exponentL p F (λt x z))).re)=ᶠ[𝓝 0] (fun z:ℝ=>∑ i, unRl (F i) (λt x z)) := by
 have hab: Tendsto (fun i:ℝ=> i • x) (𝓝 0) (𝓝 0):= by simpa only [zero_smul] using (show Continuous (fun i:ℝ=> i • x) by fun_prop).tendsto 0
 have hu: ∀ᶠ i:ℝ in 𝓝 0,∀ a:Scree.Hub n,pingS p.threshold a.val.2 (λt x i):= eventually_all.mpr fun a=> hab.eventually (Chaff.wind_p (1:Pane n) (ContinuousLinearMap.id ℝ (tangD n)) (ping_f p _))
 filter_upwards [hu] with i hi; unfold exponentL numbE; simp_rw [fun j:Scree.Hub n=> Set.indicator_of_mem (show λt x i∈ setOf (fun x:Pane n=>pingS p.threshold j.val.2 x) from hi j) (F j)]; rw [Pastry.pane_f,Complex.re_sum]; rfl
local notation "ℳ"=>mstar L.val
variable {Z0:Sweep n→Prop}
section
-- expose test sum; licensed/offreal integration via Logic
variable (p:IncX Z0 T P h c)(u:1≤h)
include p u
lemma measure_debt : gaugeTest q T P= (sites n)⁻¹*∑ i:Scree.Hub n, weightB q T i:= by
 obtain ⟨s,z,w⟩:=p.weight; unfold gaugeTest; congr 1; let F(i:Scree.Hub n):=unRl (T i) ∘ λt Θ
 have he:iteratedDeriv 2 (fun z:ℝ=>∑ i:Scree.Hub n,F i z) 0=∑ i:Scree.Hub n,weightB q T i:= (iteratedDeriv_fun_sum (x:=0) (n:=2) (fun i _=>rind (z i) u Θ)).trans (sum_congr rfl (fun i _=> alongR (z i) u Θ))
 exact (exponent_track Θ P T|>.iteratedDeriv_eq (n:=2)).trans he
lemma conductor (hB:4≤ bι)(H:Frequency L n q)(k:P.power=2)(w:P.supportExponent=1)(g: Vast L.val P.B n)(e:Ionic P L.val T) : |gaugeTest q T P|≤ (90000*‖Complex.reCLM‖)*t⁻¹^2*c*Real.exp (- (ℳ:ℝ)) :=by
 obtain ⟨s,z,l⟩:=p.weight
 let d:=Real.exp (- (ℳ:ℝ)); let A:=90000*‖Complex.reCLM‖ * t⁻¹^2; have he:d>0:=Real.exp_pos _; have hg:H.pos.le=H.pos.le:=rfl; have hp:A≥0:=by unfold A; positivity
 have hv(i:Scree.Hub n):0 ≤ s i:=Beau.grit_p P (z i) (zero_le_one.trans u)
 have ht(i:Scree.Hub n) : |weightB q T i|≤ A*(d*P.mass i.val.2 (s i)) :=by
    by_cases h:shortHub P L.val i
    · have hq: q≤d:=H.small.trans (Real.exp_monotone (neg_le_neg (by exact_mod_cast root_le L.val))); let t₀:= hv i; have p₀:= H.pos; refine (spin_short (z i) u hB H k g h (e i (g.unwrap L.val i h) h)).trans ?_; calc
       _ = (2*‖Complex.reCLM‖ * t⁻¹^2)*(q*s i):=by ring
       _ ≤ A*(d*P.mass i.val.2 (s i)):=by unfold A; gcongr; norm_num; apply P.loMass _ _ t₀
    have hx:s i ≤ d*P.mass i.val.2 (s i) := by
       have hs: (ℳ:ℝ) ≤ coverNumber P.B i.val.2 :=by exact_mod_cast le_of_not_gt (fun e=> h ((paves L.val _).2 e))
       unfold d BudgetPoint.mass; rw [←mul_assoc,w,one_mul, ←Real.exp_add]; exact le_mul_of_one_le_left (hv i) (Real.one_le_exp (by linarith))
    exact (spin_long (z i) u hB H k).trans (mul_le_mul_of_nonneg_left hx hp)
 have hV:0<sites n:=lt_of_lt_of_le zero_lt_one (sites_pos _)
 have hz:∑ i:Scree.Hub n,P.mass i.val.2 (s i) ≤ sites n*c:=calc
    _ = ∑ j:Scree.Hub n,∑ x:V',if x=j.val.1 then P.mass j.val.2 (s j) else 0:=by simp only [sum_ite_eq',mem_univ,ite_true]
    _ ≤ _:=by rw [sum_comm]; exact (sum_le_sum (fun i _=> l i)).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul,site_card]; rw [Nat.cast_pow,sites]
                                                                )
 rw [measure_debt p u,abs_mul,abs_of_pos (inv_pos.mpr hV)]; apply (mul_le_mul_of_nonneg_left (le_trans (abs_sum_le_sum_abs ..) (sum_le_sum (fun i _=> ht i))) (inv_pos.mpr hV|>.le)).trans; rw [←mul_sum,←mul_sum]; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz he.le) hp) (inv_pos.mpr hV|>.le)).trans_eq; change _=A*c*d; field_simp
end
variable (q:ℝ)
lemma logic_gauge (u:1 ≤h):Logic P h (fun T: RegBudget n=> gaugeTest q T P):=by
 apply Logic.flex (Logic.tune (Logic.ballot univ _ (fun i _=>flow_hess (n:=n) i u Complex.reCLM (transverse q) (transverse q))) (sites n)⁻¹); intro x V; obtain ⟨c,p⟩:=V; exact measure_debt (show IncX Utrue x P h c from p) u
end Test
end YM.CF.Py.Rate
