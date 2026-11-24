import YM.CF.Cloak.Treas
import YM.CF.Rill.Oboe
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cloak
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
open Forge Reine Rill
open Rill
local notation "m₀"=> SU.group.colorScale
section smooth
variable {Y Z:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y][NormedAddCommGroup Z][NormedSpace ℝ Z][FiniteDimensional ℝ Z](F:Y×ℝ→Z) (C u:ℝ)
open Cay AnalyticBridge.RelativeLogdet.Ink
lemma axis_c (k:ℕ)(x a:Y×ℝ)(p:ℝ)(h : ContDiffAt ℝ ((k+1:ℕ):ℕ∞ω) F (x+p•a)):
 HasDerivAt (fun t=>∑ i∈range (k+1),Cay.grade i t • Cay.tear i F (x+t•a) a) (Cay.grade k p • Cay.tear (k+1) F (x+p•a) a) p:=by
 induction k with
 | zero=> simp only [Nat.zero_add,sum_range_one]; simp [Cay.grade]; exact turn_d 0 F x a p h
 | succ k ih=>
    simp_rw [sum_range_succ _ (k+1)]; have ht:= ih (h.of_le (by exact_mod_cast Nat.le_succ _)); let U(u:ℝ):=Cay.grade (k+1) u • Cay.tear (k+1) F (x+u•a) a; have hv:HasDerivAt U _ p:= (note_g k p).smul (turn_d (k+1) F x a p h); refine (show _=Cay.grade (k+1) p • Cay.tear (k+1+1) F (x+p • a) a from ?_) ▸ ht.add hv; rw [neg_smul]; abel -- tune
lemma coup_b(n k:ℕ)(p:∀ t∈interval,Allows (n+(k+1)) F (0,t*u) C)(hp:|u| ≤1): let a: Y×ℝ:=(0,u); let f(t:ℝ)(x:Y):=∑ i∈ range (k+1), Cay.grade i t • Cay.tear i F ((x,0)+t • a) a;
 Allows n (fun y=> f 1 y-f 0 y) 0 ((2^n*|u|)^(k+1)*Jet.composeCost n C 1) :=by
 intro a f; let Q(w:Y×ℝ):=((w.1,0)+w.2 • a:Y×ℝ); let U(w:Y×ℝ):=Cay.grade k w.2 • Cay.tear (k+1) F (Q w) a; have he(s y): Q (y,s)=(y,s*u):=by simp [Q,a] -- tune
 have hQ(t)(g:t∈ interval):ContDiffAt ℝ ((n+(k+1):ℕ):ℕ∞ω) F (Q (0,t)):= (he t 0) ▸ (p t g).smooth -- tune cast
 have hr: ContDiff ℝ (n:ℕ∞ω) Q:= ContDiff.add (by fun_prop) (contDiff_snd.smul contDiff_const)
 have hx := onward (r:=fun i:Y×ℝ=>ContDiffAt ℝ ((n+(k+1):ℕ):ℕ∞ω) F (Q i)) (fun t h=> hr.continuous.continuousAt.tendsto.eventually ((hQ t h).eventually (by norm_cast; simp only [ENat.coe_ne_top, not_false_eq_true])))
 have hU:∀ᶠ y in 𝓝 0, Arc U n y:=by filter_upwards [hx] with y h t g; unfold U; refine ContDiffAt.smul ?_ (tear_C (k+1) n F _ Q _ hr.contDiffAt contDiffAt_const (h t g)); unfold Cay.grade; fun_prop
 have hp(t)(l:t∈ interval): Allows n (fun y=>U (y,t)) 0 ((2^n*|u|)^(k+1)*composeCost n C 1) :=by
    let V(y):=Q (y,t); have hf : Allows n V 0 1:=by
       have h : ∀ y,V y=(y,t*u):=fun y=> he t y
       have hn:‖t*u‖ ≤ 1:=calc
          _ = |t| * |u|:= by rw [Real.norm_eq_abs,abs_mul]
          _ ≤ 1:= mul_le_one₀ (by rw [abs_of_nonneg l.1]; exact l.2) (abs_nonneg _) hp
       exact ((allows_linear (x:=(0:Y)) (L:=ContinuousLinearMap.id ℝ Y) ContinuousLinearMap.norm_id_le (by simp)).pair (allows_const (0:Y) hn)).germ (Eventually.of_forall fun i=> Eq.symm (h i))
    have hu:‖a‖≤|u|:=by rw [Prod.norm_def]; simp [a,Real.norm_eq_abs]; -- tune
    have ht := tear_p (k+1) n F 0 V _ hf (allows_const (0:Y) hu) (show Allows _ F _ _ from (he t 0).symm ▸ p t l)
    refine (ht.smul (Cay.grade k t)).mono (mul_le_of_le_one_left ht.nonneg ?_); unfold Cay.grade; have hd:0 ≤1-t:=sub_nonneg.mpr l.2; exact (abs_of_nonneg (by positivity)).trans_le (div_le_one_of_le₀ ((pow_le_one₀ hd (sub_le_self _ l.1)).trans (Nat.one_le_cast.mpr (Nat.factorial_pos _))) (by positivity))
 refine (Newt.spirit hU.self_of_nhds hp).germ ?_; filter_upwards [hx,hU] with y h l
 rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun t=> f t y) ?_ (l.slice.intervalIntegrable_of_Icc zero_le_one)]
 intro t hp; exact axis_c F k (y,0) _ t ((h _ (by simpa only [Set.uIcc_of_le zero_le_one] using hp)).of_le (by exact_mod_cast Nat.le_add_left (k+1) n))
end smooth
end YM.CF.Cloak
