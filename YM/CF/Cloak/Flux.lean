import YM.CF.Cloak.Light
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
section bound
variable {E X:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x₀:E}{U:E→ Config G f}{u v C D:ℝ}{T:E→X}[NormedAddCommGroup X][NormedSpace ℝ X]
local notation "m"=> SU.group.colorScale
def priceK(n j:ℕ)(D:ℝ):ℝ:= n.factorial * Real.exp (n*D)*(1+(j:ℝ))^n
lemma prince {ι:Type}[DecidableEq ι] (S:Finset ι)(F:ι→E→ℝ)(D:ℝ)(p:0≤D)(hp:∀ i∈S, Allows n (F i) x₀ D)(h:∀ i∈S,|F i x₀| ≤ 1): Allows n (fun x=>∏ i∈S,F i x) x₀ (priceK n S.card D):=by
 let r:ℝ:= (1+S.card:ℝ)⁻¹; have ht:0<r:=by unfold r; positivity
 have hg:r≤1:=inv_le_one_of_one_le₀ (le_add_of_nonneg_right (by positivity))
 have hu(i)(v:i∈S):potash r n (F i) x₀ ≤ Real.exp (n*D*r):= (nob_earn (hp i v) ht.le hg).trans ((add_le_add_left ((Real.norm_eq_abs _).trans_le (h i v)) _).trans (by rw [add_comm]; exact Real.add_one_le_exp _)) -- add side tune
 let K:=Real.exp (n*D*r)
 have hx(s:Finset ι)(l:s⊆ S):potash r n (fun x=>∏ i∈s,F i x) x₀ ≤ K^s.card:=by
    induction s using Finset.induction_on with
    | empty=> simp [pot_const]
    | insert i s v ih=>
      obtain ⟨a,b⟩:=insert_subset_iff.mp l; simp_rw [prod_insert v]; rw [card_insert_of_notMem v,pow_succ']; let X(x):=∏ i∈s,F i x; have he:= pot_s (g:=X) ht.le (hp i a).smooth (show ContDiffAt ℝ ((n:ℕ∞):WithTop ℕ∞) X x₀ from contDiffAt_prod fun i t=> (hp i (b t)).smooth) -- tune g
      exact he.trans (mul_le_mul (hu i a) (ih b) (sum_nonneg fun i _=>pos_nob ht.le _) (Real.exp_pos _).le)
 let T (x):=∏ i∈S,F i x; have hr:potash r n T x₀≤Real.exp (n*D) :=by
    apply (hx S (Subset.refl _)).trans; unfold K; rw [←Real.exp_nat_mul]; apply Real.exp_le_exp.mpr; unfold r; field_simp; nlinarith
 refine ⟨contDiffAt_prod (fun i t=> (hp i t).smooth),fun i t=>?_⟩; exact (nob_out ht hg hr i t).trans_eq (by simp [r,priceK])
-- clamp through hord. pg halo test.
variable {q:Chi}{F:Finset (Cell f)} {t :ℝ}
def wrapM(q:Chi)(t:ℝ)(F:Finset (Cell f))(U:Config G f):= shutters q (t/2) F U
lemma pure_w(q:Chi)(F:Finset (Cell f))(U:Config G f)(p:0<t)(h:∀ i∈F, Pressure.toll U i ≤ t/2): wrapM q t F U=1:=prod_eq_one fun i v=>pad_eq (x₀:=(0:ℝ)) q _ p (fun _=>faceValue U i) (h i v)
lemma starchy (q:Chi)(C:ℝ)(n:ℕ)(g: m ≤ C): ∃ D:ℝ,0 ≤ D∧∀ (t:ℝ),0<t→∀{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{f:Side}(F:Finset (Cell f))(U:E→ Config G f)(x:E), (∀ i∈F,Tender (fun y=>faceValue (U y) i) x (C*t) n)→ Allows n (wrapM q t F∘ U) x (priceK n F.card D) :=by
 obtain ⟨D,h,H⟩:=cost_χ q true n; let w:= m⁻¹*C; let K:=Jet.composeCost n D (4*(2^n*w*w)) -- tune
 have hh:0 ≤ K:=by have hp:=SU.group.colorScale_pos; have hx:0 ≤ C:=hp.le.trans g; unfold K w Jet.composeCost; positivity
 refine ⟨K,hh,@fun t p E _ _ f F U x hp=> ?_⟩; exact prince F _ K hh (fun i v=>shoulder q D C n g H _ p _ (hp i v)) fun i v=> (abs_of_nonneg (q.range _).1).trans_le (q.range _).2 -- tune quantifier f after t fix
lemma aboard(q:Chi)(F:Finset (Cell f))(p:0<t)(U:E→ Config G f)(z:x₀∈tsupport (wrapM q t F ∘ U))(i:Cell f)(u:i∈F)(h:Tender (fun y=>faceValue (U y) i) x₀ v n): Pressure.toll (U x₀) i≤ t:= shade_s q _ p (fun y=>faceValue (U y) i) h (closure_mono (fun j hp=> not_imp_not.mpr (fun H:q.innerShare (t/2) _=0 => prod_eq_zero u H) (show wrapM q t F (U j)≠0 from hp)) z) -- tune function implicit
end bound
end YM.CF.Cloak
