import WakeRoad.Mature
import WakeRoad.Tackle
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark SatinVerification Vacancy Tapestry
open CF.Pannier.Chancel
open Preparation.Yoke EmberWind Jewel
open Lamour.Bridge.Celeste Morn
open Ballad
open SpinReceipt Shuttle
open Papal (Weaver household)
open WakeInvestment
open Gleam Gleam.Wake YM.WakeRoad CF.Hiro Hearth
open Precision Regis.Head.Brecht Regis.Circuit Exterior
namespace GramSignal
set_option quotPrecheck false
set_option linter.unusedSectionVars false
open ArborJet Preparation Yoke.ArborJet
open Dial Pressure Stationary Regis.Circuit
variable {q:Clip}{n:Side}{M:Bed}{Z:PathData SU.group}{η σ θ C w a:ℝ}
   (B:Z.Bounds q θ w a)(P:Attached M Z)(D:Floor M q n η C)(U:M.covered σ C)(e:0<σ)(h:Even n.val)
variable {J I:Type}[Fintype J][Fintype I][DecidableEq J][DecidableEq I]
section generic
variable {F:Type}[NormedAddCommGroup F][InnerProductSpace ℝ F][FiniteDimensional ℝ F][MeasurableSpace F][BorelSpace F]
variable (Y:J→ F)(T:I→F)
local notation "μ"=>stdGaussian F
private def cup (u:F)(v:F):ℝ:=inner ℝ u v
private abbrev imprint (K:WakeRoad.Press J)(v:F):ℂ:=WakeRoad.Score K (fun i=>cup (Y i) v)
private theorem avg_one (x z:F): Integrable (fun v:F=>cup x v*cup z v) μ ∧ (∫v:F,cup x v*cup z v ∂μ)=cup x z:=by
 have h(p:F):MemLp (fun Z:F=> inner ℝ p Z) 2 μ:=by simpa using coats p 1
 exact ⟨(h _).integrable_mul (h _),appraisal ..⟩
-- products via 4-pol. Store in ℂ
local notation "$$" i:max j:max=> (↑(cup (i:F) (j:F)):ℂ)
lemma consultation (K:WakeRoad.Press J) : (∫v:F,imprint Y K v ∂ μ)= ∑ i:J,∑j:J, $$ (Y i) (Y j) * K i j:= by
 let h(i j:J):=avg_one (Y i) (Y j); let f(i j:J)(v:F):=((cup (Y i) v*cup (Y j) v):ℝ) • K i j
 have g(i j):Integrable (f i j) μ:=(h i j).1.smul_const _
 change (∫ v:F,(∑ i:J,∑ j:J,f i j v)∂μ)=_
 rw [integral_finsetSum _ (fun i _=> integrable_finsetSum _ (fun j _=>g i j))] -- identify names
 refine sum_congr rfl fun i _=> ?_; rw [integral_finsetSum _ (fun j _=>g i j)]
 refine sum_congr rfl fun j _=> ?_; unfold f; rw [integral_smul_const,(h i j).2]; rfl
variable (K:WakeRoad.Press J)(L:WakeRoad.Press I)
lemma consultation2:
 (∫v:F, imprint Y K v * imprint T L v ∂μ)-(∫v:F,imprint Y K v ∂μ)*(∫v:F,imprint T L v ∂μ)=
   ∑ i:J,∑ j:J,∑ t:I,∑ d:I,
   ( K i j*L t d) * ($$ (T t) (Y i)* $$ (T d) (Y j)+ $$ (T d) (Y i) * $$ (T t) (Y j)):=by
 let X(i j t d)(v:F):=cup (Y i) v*cup (Y j) v*cup (T t) v*cup (T d) v
 let G(i j t d)(v:F):= (X i j t d v) • (K i j*L t d)
 have P(v:F): imprint Y K v* imprint T L v=∑ i:J,∑j:J,∑t:I,∑d:I,G i j t d v:=by
    unfold imprint WakeRoad.Score G X; simp_rw [sum_mul,mul_sum]; refine sum_congr rfl (fun i _=> sum_congr rfl (fun j _=> sum_congr rfl (fun t _=> sum_congr rfl (fun d _=>?_)))); simp only [Complex.real_smul]; push_cast; ring
 let c₂(i j t d):= moments (Y i) (Y j) (T t) (T d)
 let S(i j t d):= cup (Y i) (Y j)*cup (T t) (T d)
 let R(i j t d):= cup (T t) (Y i)*cup (T d) (Y j)+cup (T d) (Y i)*cup (T t) (Y j)
 have h(i j t d): Integrable (G i j t d) μ ∧ (∫v:F,G i j t d v∂μ)=(S i j t d+R i j t d) • (K i j* L t d):=by
    refine ⟨(c₂ i j t d).1.smul_const _,?_⟩; unfold G X S R cup; rw [integral_smul_const,(c₂ i j t d).2]; rw [real_inner_comm (T t) (Y i), real_inner_comm (T d) (Y j),real_inner_comm (T d) (Y i),real_inner_comm (T t) (Y j),add_assoc]
 simp_rw [P]; rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>integrable_finsetSum _ (fun t _=> integrable_finsetSum _ (fun d _=>(h ..).1))))]
 simp_rw [integral_finsetSum _ (fun j _=>integrable_finsetSum _ (fun t _=>integrable_finsetSum _ (fun d _=>(h ..).1))),integral_finsetSum _ (fun t _=>integrable_finsetSum _ (fun d _=>(h ..).1)),integral_finsetSum _ (fun d _=>(h ..).1)]
 rw [consultation,consultation]; simp_rw [Finset.sum_mul,Finset.mul_sum, ←Finset.sum_sub_distrib]
 refine sum_congr rfl (fun i _=> sum_congr rfl (fun j _=> sum_congr rfl (fun t _=> sum_congr rfl (fun d _=>?_)))); rw [(h ..).2, Complex.real_smul]; unfold S R; push_cast; ring
#print axioms consultation2
end generic
-- unbend vessels on the actual stamen
local notation "F₀"=>stamen B P n
abbrev salver (ρ:ℝ)(V:Vessel SU.group n I)(i:I):stamen B P n := plar B P ((V.ua i).1,plaquette (V.ua i).2) ρ (V.lens i)
variable (V:Vessel SU.group n I)(W:Vessel SU.group n J)(K:WakeRoad.Press J)(L:WakeRoad.Press I)
private lemma charge(S:(I→ℝ)→ℂ)(c:ℝ)(u:stamen B P n): V.basin c S q u.val= S (fun i=>cup (salver B P c V i) u):=by
 let f:=tiler B P (n:=n); obtain ⟨t,rfl⟩:= f.surjective_rangeRestrict u; change V.basin c S q (tiler B P t)= _; rw [Vessel.belly B P V]; refine congrArg S (funext (fun i=>?_))
 let v:=V.ua i
 have hp: elbow B P (v.1,plaquette v.2) c (f.rangeRestrict t)= c • Regis.Head.Etch.river q (v.1,v.2) (f.rangeRestrict t).val := bare_elbow B P (f.rangeRestrict t)
 have hx:= congrArg (fun x:SU.group.Color=> x (V.lens i)) hp
 rw [show Regis.Head.Etch.river q _ (f.rangeRestrict t).val= _ from Regis.Head.Etch.river_now q B P v t] at hx; exact hx.symm

def chipbook (i:I)(j:J) := coupon (V.ua i) (W.ua j) (V.lens i) (W.lens j) M -- A occupancy dimensions
include D U e h
lemma metal(ρ:ℝ)(i:I)(j:J): ((cup (salver B P ρ V i) (salver B P ρ W j) :ℝ):ℂ) = (ρ:ℂ)^2 * chipbook V W (M:=M) i j:=by -- notation $$ F outside scope?
 unfold salver chipbook coupon cup; rw [limb_component B P D U e h]; ring

-- S : formulation for cone credit
section Atlas
variable {m: Side}
variable (R:Bool→WakeRoad.Press J)(X:Bool→ Vessel SU.group (More m) J)
local notation "A₁" x:max=> stamen B P (More x)
def affinity(K:I→I→ℂ)(U V:WakeRoad.Press I):ℂ:=∑ i:I,∑ j:I,∑ t:I,∑ l:I,U i j*V t l*(K t i*K l j+K l i*K t j)
omit D U h in
lemma regally(ρ:ℝ)(D:Floor M q (More m) η C)(U:M.covered σ C):
 let V:=stdGaussian (stamen B P (More m))
 (∫ x:stamen B P (More m), (ArborJet.planter X).basin ρ (ArborJet.brushpot R) q x.val ∂V) -
   (∫ x:stamen B P (More m), (X false).basin ρ (WakeRoad.Score (R false)) q x.val ∂V)*(∫x:stamen B P (More m), (X true).basin ρ (WakeRoad.Score (R true)) q x.val ∂V)=
 (ρ:ℂ)^4 * affinity (chipbook (M:=M) (X true) (X false)) (R false) (R true):=by
 intro V
 have k {J:Type}[Fintype J][DecidableEq J](X:Vessel SU.group (More m) J)(T:(J→ℝ)→ℂ): (fun u:stamen B P (More m)=>X.basin ρ T q u.val)=(fun u=>T (fun i=>cup (salver B P ρ X i) u)):= funext (fun v=>charge B P X T ρ v)
 rw [k,k,k]; change (∫x:A₁ m, imprint (salver B P ρ (X false)) (R false) x* imprint (salver B P ρ (X true)) (R true) x∂V) - (∫x:A₁ m, imprint (salver B P ρ (X false)) (R false) x∂V) * (∫x:A₁ m, imprint (salver B P ρ (X true)) (R true) x∂V)=_
 rw [consultation2]; simp_rw [metal (n:=More m) B P D U e (show Even (More m).val from ⟨m.val,by change m.val*2=m.val+_; omega⟩)]
 unfold affinity;simp_rw [mul_sum]; apply sum_congr rfl; intro i hi; apply sum_congr rfl; intro j hj; apply sum_congr rfl;intro k hk; apply sum_congr rfl;intro l hl; ring
end Atlas
#print axioms regally
