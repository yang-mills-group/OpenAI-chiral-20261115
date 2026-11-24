import SatinThinGalaxy
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.Regis.Head.Brecht
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset Exterior Precision RG Work.F03 Gleam MeasureTheory NormedSpace ProbabilityTheory Wilson Matrix
open Circuit
open scoped Matrix Topology BigOperators NNReal ENNReal InnerProductSpace ContDiff Classical Matrix.Norms.Frobenius
variable {q: Clip}{n: Side}{M: Bed}{G:Gauge}{Z:PathData G}{η C v σ θ w a k t u:ℝ}
variable (B: Z.Bounds q θ w a)(P:Attached M Z)(L:Floor M q n η C)(H:M.covered σ C)(e:0<σ)
local notation "r"=> stamen B P n
-- one clover comparison at an arbitrary (shifted) site
open Etch Garland
variable (z:PlaqAxes→ℝ) (u':ℝ) (h:0<k)
variable (x y:Site n)
open CF.Lamour.Bridge.Celeste.Clock.Hookah.Blaze
abbrev zipOne (x:Site n)(s:Signed:=1) :Tour Unit n:= ⟨fun _=>x,fun _=>s⟩
abbrev zipBoth (x y:Site n)(s t:Signed:=1):Tour Bool n:= ⟨fun i=>if i then x else y,fun i=> if i then s else t⟩
def singleV :ℝ:= visionCost B P (zipOne x) (amaryllis z G k h) u'
def bothV :ℝ := visionCost B P (zipBoth x y) (amaryllis z G k h) u'
-- independent common center on torus
lemma mean_slat (v:r) : (amaryllis z G k h).chalk q u' 1 x v.val=∑ i,z i*cljAt B P x i (k:=k) (u:=u') v:= by
 rw [chalk_form]; change (salix _ _).sketch q u' x v.val= _; have he: (amaryllis z G k h).sketch q u' x v.val= ∑ i,z i*(mellow G i k h).sketch q u' x v.val:=rfl; rw [← show amaryllis ..=salix .. from rfl]; simp_rw [← mellow_form B P x _ h] -- tune
 exact he
include h
private lemma integr_one (v:PlaqAxes) : Integrable (cljAt (u:=u') (k:=k) B P x v) (stdGaussian (r)):= (clipped _ h).integrable (show (1:ℝ≥0∞)≤2 by norm_num)
private lemma integr_both (v w:PlaqAxes) : Integrable ((cljAt (u:=u') (k:=k) B P x v)*(cljAt (u:=u') (k:=k) B P y w)) (stdGaussian (r)):= (clipped _ h).integrable_mul (clipped _ h)
local notation "Ψ" i:max=>cljAt B P x i (u:=u') (k:=k)
local notation "Φ" i:max=>cljAt B P y i (u:=u') (k:=k)
omit h in
abbrev wholeV (K:PlaqAxes→PlaqAxes→ℂ):ℂ:= ∑ i,∑ j, (z i:ℂ)*(z j:ℂ)*K i j
lemma single_turn : singleV B P z u' h x=∑ i, z i* cloudV B P (Ψ i):=by
 unfold singleV visionCost clouds cloudV; simp only [Tour.reading, zipOne, Fintype.prod_unique]; simp_rw [mean_slat B P]; rw [integral_finsetSum]; swap; · exact fun i _=> (integr_one B P u' h x i).const_mul _
 simp_rw [integral_const_mul]
lemma both_turn : bothV B P z u' h x y=∑ i, ∑ j, z i*z j*cloudV B P ((Ψ i)*(Φ j)):=by
 unfold bothV visionCost clouds cloudV; simp only [Tour.reading,Fintype.prod_bool,zipBoth,↓reduceIte,Bool.false_eq_true]; simp_rw [mean_slat B P]; let Z(i j:PlaqAxes)(v:r):= z i*z j* ((Ψ i)*(Φ j)) v; simp_rw [Fintype.sum_mul_sum]; have hh(i j:PlaqAxes)(v:r): z i * ((Ψ i) v)*(z j*((Φ j) v))= Z i j v:= by unfold Z; simp only [Pi.mul_apply]; ring
 simp_rw [hh]; have hp(i j:PlaqAxes):Integrable (Z i j) (stdGaussian (r)):= (integr_both B P u' h x y i j).const_mul _
 rw [integral_finsetSum]; swap; · exact fun i _=> integrable_finsetSum _ fun j _=> hp i j
 simp_rw [integral_finsetSum _ fun j _=> hp _ j]; unfold Z; simp_rw [integral_const_mul]
lemma single_tariff (p:|u'|≤2) : |singleV B P z u' h x|≤ meritG z * glamourK q G:=by
 rw [single_turn]; refine (abs_sum_le_sum_abs ..).trans (?_); unfold meritG; rw [sum_mul]; refine sum_le_sum (fun i _=> ?_); rw [abs_mul]; refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _); obtain ⟨x,l,v,_⟩:= phaseNorm B P x i h p; rw [abs_of_nonneg x]; exact l.trans v
include L H e in
lemma assigned (p: Even n.val)(f:|u'|≤2) :
 ‖(↑(bothV B P z u' h x y-singleV B P z u' h x*singleV B P z u' h y):ℂ)- (u':ℂ)^4 * wholeV z (fun i j=> duoPower G (pairR x y M i j))‖≤ meritG z ^2 *(tollK q G/k):=by
 let G'(i j:PlaqAxes):ℂ:= (↑(cloudV B P ((Ψ i)*(Φ j)) - cloudV B P (Ψ i)*cloudV B P (Φ j)):ℂ)-(u':ℂ)^4 * duoPower G (pairR x y M i j)
 let c:=tollK q G/k; have ht(i j:PlaqAxes): ‖G' i j‖ ≤ c:= twoVision B P L H e x y i j h p f -- check h order
 rw [both_turn, single_turn B P z u' h x,single_turn B P z u' h y]; push_cast; let W:= wholeV z G'; rw [show _-_ * wholeV z _ = W from (?_)]
 · unfold W wholeV; refine (norm_sum_le ..).trans ((sum_le_sum (fun i _=>?_)).trans_eq (b:= ∑ i:PlaqAxes, ∑ j:PlaqAxes, |z i| * ( |z j| * c)) (?_)); swap
   · unfold meritG; rw [sq, Finset.sum_mul_sum]; simp_rw [←mul_assoc,← mul_sum,←sum_mul, ← mul_sum,←sum_mul]; rfl -- tune
   refine (norm_sum_le ..).trans (sum_le_sum fun j k=>?_); simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left (ht i j) (by positivity)
 unfold W wholeV; simp_rw [Fintype.sum_mul_sum,mul_sum]; rw [← sum_sub_distrib,← sum_sub_distrib]; apply sum_congr rfl; intro i _; rw [← sum_sub_distrib, ←sum_sub_distrib]; apply sum_congr rfl; intro j _; unfold G'; push_cast; ring
end YM.Regis.Head.Brecht
#print axioms YM.Regis.Head.Brecht.assigned
