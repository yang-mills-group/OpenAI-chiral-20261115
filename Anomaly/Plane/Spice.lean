import Anomaly.Plane.Payers
/-! positive tolerances with reflected axis-E, clipped cut-off wind vector.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 455000
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Head.Brecht.Pier
open Function Filter Metric MeasureTheory NormedSpace ProbabilityTheory Finset GeometryP
open Lattice RG Wilson Tree Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Circuit Gleam Etch Next.Free
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal InnerProductSpace
variable {n:Side}{G:Gauge}{q:Clip}{S:Bed}{Z:PathData G}{η θ ζ w D c d u K t R:ℝ}{U:Config G n}{O:Support n}{o x z:Site n}{L:ℕ}
open CF CF.Lat CF.Cube CF.Onyx CF.Ember
open CF.Swell.Sonar Garland
open Circuit.Pier
local notation "bZ"=> Signed.mirror 3
variable (W:tableQ G n ℂ)(B: Z.Bounds q η θ ζ) (P:Attached S Z)(H_:Floor S q n w D)(p:S.covered c D)(v:0<c)(E:Even n.val)(U': Bid.Sworn S n G)
variable (C:spoken G→ℝ){τ M:ℝ} (hq:0<τ)(hτ:τ ≤ (tariff W (C ∘ spit)).re)(hv:0<t)(hu:1/2 ≤ u)(hl:u ≤ 2)
def tinder (C:spoken G→ℝ)(u w:ℝ):=2*(paysW (1/2) u)^2*(w^2/priva C)
include hv hq
lemma tinder_w:tinder C t τ>0:=by unfold tinder paysW; have he:=fare_w hv; unfold priva; positivity -- include
include hτ hv hu hq
lemma objective_price:tinder C t τ≤ (lodging (objective u t) W (star W)).re:=by
 change _≤(lodging (breve spit (paysW u t)) W _).re
 rw [positive_X,Complex.real_smul,Complex.re_ofReal_mul,Complex.ofReal_re]; have he:=framed W spit C τ hq.le hτ; have hb:0<priva C:=by unfold priva; positivity
 let X:=∑ i:plumK (spoken G),‖glaze (ledger spit W) i‖^2; have ht: τ^2/priva C≤ X:=by rw [div_le_iff₀ hb]; exact he.trans_eq (mul_comm ..)
 have hz:0 ≤ paysW u t:=mul_nonneg (sq_nonneg _) (fare_w hv).le
 change _ ≤ _*X; unfold tinder; apply mul_le_mul _ ht (by positivity:0 ≤ τ^2 / priva C) (by positivity)
 exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0 ≤ paysW (1/2) t from mul_nonneg (sq_nonneg _) (fare_w hv).le) (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num: (0:ℝ)≤1/2) hu 2) (fare_w hv).le) 2) (by norm_num)
omit hτ hv hu hq
private lemma stageD {a z:ℂ}{t:ℝ}(h:‖a-z‖≤ t): z.re-t≤a.re:=by have ht: |a.re-z.re| ≤ t:=(Complex.abs_re_le_norm (a-z)).trans h; linarith only [(abs_le.mp ht).1] -- include?
include hτ hv hu hq hl p v E U' H_
variable {ε:ℝ}
lemma priced_goal (a:Site n) (Q:Regional o L W)(β: costs W ≤ M)(d:0 ≤ ε)(θq: doorsW S L o (affine bZ a o) R t ε) (z:1 ≤ K) :
 let X:= choppy W (canonZ B P 1 0 u) K; let X':= choppy (star W) (canonZ B P bZ a u) K
 tinder C t τ-recordB t ε*M^2-R^8*fare4 (2*(Real.sqrt q.direct)⁻¹) K*M^2 ≤ R^8*(tally X X').re:=by
 intro X X'; let F:= canonZ B P 1 (0:Site n) u; let H:=canonZ B P bZ a u; let Z:=tally (curly W F) (curly (star W) H); let Z':= R^8 • lodging (spun F H) W (star W); let Q':=R^8 • tally X X'
 have ht:|u|≤2:= abs_le.mpr ⟨by linarith only [hu],hl⟩
 have h:= registrations B P H_ p v E a t R hv W Q ht d θq; let u':=tinder C t τ; let L':= recordB t ε; let w':=costs W; let V:= fare4 (2*(Real.sqrt q.direct)⁻¹) K; let x:= R^8; have hx: 0 ≤ x:=by unfold x; positivity
 have hy:0 ≤ w':=sum_nonneg fun _ _=>norm_nonneg _
 have hg:0 ≤ L':=by unfold L' recordB; have hx:= fare_w hv; positivity
 have hp: 0 ≤ V:=by unfold V fare4; have hx: 0≤K:=(by linarith only [z]); positivity
 have he:u'-L'*M^2 ≤ Z'.re:= sub_le_sub_right (objective_price W C hq hτ hv hu) _ |>.trans (stageD (h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy β 2) hg))) -- remove extras
 have ha:(Z').re ≤ x*Z.re:=by
    let A:= stdGaussian (stamen B P n); let Y:=∫ i, curly W F i∂A
    unfold Z Z'; rw [spurn,Complex.real_smul,Complex.re_ofReal_mul,Complex.add_re, show ∫ i,curly (star W) H i ∂A=star Y from mean_plus B P H_ W bZ a U' u]; change x*_ ≤ x*((Y*star Y).re+_); apply mul_le_mul_of_nonneg_left _ hx; apply le_add_of_nonneg_left; rw [show Y*star Y= ((‖Y‖^2:ℝ):ℂ) from (Complex.mul_conj Y).trans (by rw [Complex.normSq_eq_norm_sq])]; simp -- tune
 have hv': ‖tally X X'-Z‖ ≤ V*M^2:=by
    have ht' := relief W F H (star W) z (fun i=>brightP B P 1 0 i ht) (fun i=>brightP B P bZ a i ht)
    simp_rw [Pi.star_apply,norm_star,←pow_two] at ht'; exact ht'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy β 2) hp)
 have hrZ:=le_trans he ha; have hw:=mul_le_mul_of_nonneg_left (stageD hv') hx
 change u'-L'*M^2-x*V*M^2≤x*_ ; linarith only [hrZ,hw]
end YM.Regis.Head.Brecht.Pier
