import Anomaly.Ward.Screen
/-!
Vote the price stencil in the spherical-linear H projection, before amplification in
slit pressure. Retain pencils/gauge-mask economics on the same layouts as used in the signed survey.

This proves the orientation-adjusted version of the positive response for the projected
pseudoscalar, not *plane* positivity by itself. Summation normalization of H projector.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Swell.Sonar
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Cube Lat Tenant Tulip Spire Scroll Scree Jet Skye Pastry Dial Fock Branch Drapes Rill Sour
open Nacre Next.Free Exterior Precision Wilson _root_.Zephyr.Chern SpectrumQ
open Ione.Clock Hove Spire Regis.Head Next.Rank.Spindle LampP
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace StageQ
local notation "Γ"=> More n
local notation "χν" => fieldDir SU.group (More n) 1
local notation "Πp"=> tangD n
open PotQ
variable {b k m:ℕ}{d c α C M w a:ℝ}{P:BudgetPoint}{K:Loom n}{X:SOp n}{T:tableQ SU.group (More n) ℂ} {x:Site n} (R:Knit X (node x) b d α M C w m T) (L:mintQ α C d m) (H:Roof n c d k K)(hb:b+k+10 ≤ P.B)(hp:P.threshold ≤ c)
structure Jig (x:Site n)(b:ℕ)(f:Pane n→ℂ)(X:SOp n)(T E:tableQ SU.group (More n) ℂ)(B:BudgetPoint)(α x' w:ℝ):Prop where
   nearValue: ∀ (V:Pane n),pingS B.threshold (halo B.B {node x}) V →∀ Q:fieldDir SU.group (More n) 1,Agrees (halo b {node x}) V (represent Q)→‖collect SU.group Q‖<α → ‖onStage x f V-tariff E (receipt Q)‖≤x'*‖collect SU.group Q‖^3
   transfer(Q:fieldDir SU.group (More n) 1): tariff E (receipt Q)=∑ j:Signed,dollar j • tariff T (receipt (sailH (gridTulip j x) Q))
   gain: costs E≤w
   legs: Regional (node x) (b+2) E

abbrev gainN(w:ℝ):ℝ:=Fintype.card Signed*((Fintype.card SU.group.ColorIndex:ℝ)^2*w)
abbrev feeN(x c:ℝ):ℝ:=Fintype.card Signed*(2*c*x)
include R H hp hb L
lemma jigEra (y:3 ≤ m):∃ E:tableQ SU.group (More n) ℂ,Jig x b (traceMeter P K x X) X T E P α (feeN M C) (gainN w):=by -- include R L
 let g(s:Signed):=gridTulip s x
 choose Q τ h Z using fun s:Signed=> branchQ (g s) T (node x) b R.inHall
 let S:= ∑ i:Signed,dollar i • Q i
 have he(V:χν): tariff S (receipt V)=∑ j:Signed,dollar j • tariff T (receipt (sailH (g j) V)):=by
    simp_rw [Z]; unfold S tariff; simp_rw [Finset.sum_apply,smul_sum,Pi.smul_apply]; rw [sum_comm]; exact sum_congr rfl fun i _=> sum_congr rfl fun j _=>smul_comm ..
 refine ⟨S,⟨fun V t Q p v=> screenCash R L H hb hp S he V t Q p v y,he,?_,?_⟩⟩
 · unfold costs S; simp_rw [Finset.sum_apply,Pi.smul_apply]; refine (sum_le_sum (fun (i:ChainKey SU.group Γ) _=>norm_sum_le univ _)).trans ?_; rw [sum_comm]; simp_rw [norm_smul,Real.norm_eq_abs,dollar_fixed,one_mul]; refine (sum_le_sum (fun i _=> (τ i).trans (mul_le_mul_of_nonneg_left R.card (sq_nonneg _)))).trans (?_); simp [gainN] -- tune
 intro i p j
 unfold S at p; rw [Finset.sum_apply] at p; obtain ⟨s,t,u⟩:=exists_ne_zero_of_sum_ne_zero p
 have hv:= h s i (fun v=>u (by rw [Pi.smul_apply,v,smul_zero])) j; rw [←nodeA,tieA] at hv; exact hv

variable {E:tableQ SU.group (More n) ℂ}
lemma verbal (H0:x=0) (J:Jig x b (traceMeter P K x X) X T E P α (feeN M C) (gainN w)) (A:StemA n)(u:2 ≤ m)(s:Signed): let i:=gridTulip s x
 bud (traceMeter P K x X ∘ flashA i ∘ _root_.Zephyr.Chern.petals A) 2=tariff T (receipt (sailH i (pattern A))):=by -- tune need hears x general, generalize
 -- fail subst x implicitly included!? write let x' notation
 intro i
 let F:=traceMeter P K x X; let V:= _root_.Zephyr.Chern.petals A; let A':=payAng i A
 have hpY:sailH i (pattern A)=pattern A':=by
    -- trans direction agreement. use chart rule.

    apply collect_inj
    apply separatePath; funext t
    rw [← survey,←survey, colorTravel, SpectrumQ.march, SpectrumQ.march, travels]
 rw [hpY,show F ∘ flashA i ∘ V= _ from (show F ∘ flashA i ∘ V=F ∘ _root_.Zephyr.Chern.petals A' from funext fun t=> congrArg F (travels ..))]
 subst x; exact hears R L H hb hp A' u
where collect_inj {n:Side} : Injective (collect (n:=n) SU.group):=by intro p q t; funext i; obtain ⟨k,j⟩:=i; obtain ⟨j,rfl⟩:=axisEquiv.surjective j; exact congrFun t (k,j)
lemma leader (p:x=0)(U:Jig x b (traceMeter P K x X) X T E P α (feeN M C) (gainN w))(g:2 ≤ m)(t:4*(b+2)+4 < n.val):
 tariff E frameμ = ∑ j:Signed,dollar j • bud (traceMeter P K x X ∘ flashA (gridTulip j x) ∘ _root_.Zephyr.Chern.petals (_root_.Zephyr.Chern.stream n)) 2:=by
 subst x; have hl:∀ Q:tableQ SU.group (More n) ℂ,Regional (node (0:Site n)) (b+2) Q → tariff Q frameμ=tariff Q (receipt (pattern (_root_.Zephyr.Chern.stream n))):=by
    intro Q h; apply sum_congr rfl; intro i hi; by_cases y:Q i=0; · rw [y,smul_zero,smul_zero]
    apply congrArg (· • Q i); exact prod_congr rfl fun j _=>(congr_arg (fun z:SU.group.Color=> z (i j).2) (agreesSD t _ (h i y j) _)).symm
 rw [hl E U.legs,U.transfer]; simp_rw [verbal R L H hb hp rfl U _ g]; -- tune arguments order
end StageQ
end YM.CF.Swell.Sonar
