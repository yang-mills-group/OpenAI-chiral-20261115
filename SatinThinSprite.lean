import SatinThinStellar
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
omit h in
def windLord (q:Clip) (G:Gauge) :ℝ:=3*glamourK q G^2
local notation "Kξ"=> 2*(Real.sqrt q.direct)⁻¹
local notation "Ι"=> G.ColorIndex
local notation "R"=> glamourK q G
local notation "μ"=> stdGaussian r
include h
lemma silhouette (i j:PlaqAxes)(p:|u'|≤2) : |cloudV B P ((cljAt B P x i (u:=u') (k:=k))*(cljAt B P y j (u:=u') (k:=k)))| ≤ windLord q G:=by
 let F:=cljAt B P x i (u:=u') (k:=k); let Fx:=sparkZ B P x i; let X:= fun i=> Fx i u'; let A':= cljAt B P y j (u:=u') (k:=k); let Y:= fun i=> sparkZ B P y j i u'
 obtain ⟨g,t,_⟩:= phaseNorm B P x i (u:=u') h p; obtain ⟨c,d,_⟩:=phaseNorm B P y j (u:=u') h p; have he: ∀ x:r, 0 ≤ F x:= fun i=> (clipμ h (coalK X i) (talent_non ..)).1; have hy:∀ x:r,0 ≤ A' x:=fun i=> (clipμ h (coalK Y i) (talent_non ..)).1
 rw [abs_of_nonneg (integral_nonneg (f:=(F*A')) fun x=> mul_nonneg (he x) (hy x))]; have hu(i): ‖X i‖≤ Kξ:= currency_bound B P _ _ _ p -- tune
 have hv(i): ‖Y i‖≤ Kξ:= currency_bound B P _ _ _ p; apply (clipE (B:=Kξ) X Y (by positivity) hu h hv).1.trans; rw [workDuet]; have ht(g j: Ι): inner ℝ (X g) (Y j) ^2 ≤ (Kξ * (Kξ))^2:= by
   apply (le_of_eq (sq_abs (inner ℝ (X g) (Y j))).symm).trans; refine pow_le_pow_left₀ (abs_nonneg _) ?_ _; refine (abs_real_inner_le_norm ..).trans (mul_le_mul (hu g) (hv j) (norm_nonneg _) (le_trans (norm_nonneg _) (hu g)))
 have ha: ( ∫ x, coalK X x ∂μ) ≤ R:= (phaseNorm B P x i h p).2.2.1
 have hb: ( ∫ x, coalK Y x ∂μ) ≤ R:= (phaseNorm B P y j h p).2.2.1
 have hh: ∑ i, ∑ j,inner ℝ (X i) (Y j)^2 ≤ R^2:= (sum_le_sum (fun i _=> sum_le_sum (fun j _=> ht i j))).trans_eq (by simp [glamourK]; ring) -- simp tune
 refine (add_le_add (mul_le_mul ha hb (integral_nonneg (fun i=> talent_non ..)) (by unfold glamourK; dsimp; positivity)) (mul_le_mul_of_nonneg_left hh (by norm_num))).trans_eq (?_); unfold windLord; ring
lemma double_fine (p:|u'|≤2): |bothV B P z u' h x y|≤ meritG z * meritG z * windLord q G:=by
 rw [both_turn]; refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (s:=univ) (fun i _=> (abs_sum_le_sum_abs ..).trans (sum_le_sum (s:=univ) (fun j _=> (?_ : |_| ≤ |z i| *( |z j| *(windLord q G))))))).trans_eq (?_))
 · simp_rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (silhouette B P u' h x y i j p) (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq (mul_assoc ..)
 unfold meritG; simp_rw [←Finset.mul_sum,← Finset.sum_mul]; ring
end YM.Regis.Head.Brecht
#print axioms YM.Regis.Head.Brecht.double_fine
