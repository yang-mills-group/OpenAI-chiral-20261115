import Anomaly.Plane.Destination
import Anomaly.Market.Scar
/-!
Robust Estimate iii:
Continuity with actually rotated receipts, polarized FD vectors (P,L) retain costs.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 425000
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Head.Brecht.Pier
open Function Filter Metric MeasureTheory NormedSpace ProbabilityTheory Finset GeometryP
open Lattice RG Wilson Tree Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Circuit Gleam Etch Next.Free
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal InnerProductSpace
variable {n:Side}{G:Gauge}{q:Clip}{S:Bed}{Z:PathData G}{η θ ζ w D c d u K:ℝ}{U:Config G n}{O:Support n}{o x z:Site n}{L:ℕ}
open CF CF.Lat CF.Cube CF.Onyx CF.Ember
open CF.Swell.Sonar Garland
open Circuit.Pier
abbrev spoken(G:Gauge):= PlaqAxes × G.ColorIndex
def spit (p:TrackKey G n):spoken G:= (p.1.2,p.2)
local notation "w0"=> Site
local notation "bZ"=> Signed.mirror 3
local notation "Pl"=> plaquette
variable (B: Z.Bounds q η θ ζ) (P:Attached S Z)(H_:Floor S q n w D)(p:S.covered c D)(v:0<c)(E:Even n.val)
variable (a:Site n)(t R:ℝ)(hv:0<t) {ε:ℝ}
abbrev paysW(u t:ℝ):= u^2 * fareX t
abbrev cuts (B: Z.Bounds q η θ ζ) (P:Attached S Z)(a:Site n)(R u:ℝ):TrackKey G n→TrackKey G n→ ℝ:=fun k l=> R^4*spun (canonZ B P 1 0 u) (canonZ B P bZ a u) k l
abbrev objective (u t:ℝ) : TrackKey G n→ TrackKey G n→ ℝ:= breve spit (paysW u t)
def doorsW (S:Bed)(r:ℕ)(x y:Site n)(R t ε:ℝ):Prop:=∀ f g:PlaqAxes,∀ z w:Site n,separation x z≤r+2 → separation y w≤r+2 → ‖(R:ℂ)^4*rimble n S (z,Pl f) (w,Pl g)-specter f g (t • YM.basis 3)‖ ≤ ε
include p v E H_ hv
lemma budgetθ (k l:TrackKey G n)(hk:k.1.1 ∈ halo L {o})(hl: l.1.1 ∈ halo L {o})(w:|u| ≤2)
  (Y:doorsW S L o (affine bZ a o) R t ε) : |cuts B P a R u k l-objective u t k l|≤4*ε:=by
 let X:= Face.send (1:Signed) 0 k.1; let y:=Face.send bZ a l.1
 let C:= turned bZ l.1.2*u^2*sch (G:=G) k.2 l.2
 let M:=rimble n S (X.1,Pl k.1.2) (y.1,Pl l.1.2); let V:=specter k.1.2 l.1.2 (t • YM.basis 3)
 have he(k:TrackKey G n)(v:k.1.1∈halo L {o})(s:Signed)(b:Site n): separation (affine s b o) (Face.send s b k.1).1 ≤ L+2:=by
    refine (separation_triangle _ (affine s b k.1.1) _).trans (add_le_add (?_) (featherS ..)); simp only [affine,separation_translate,separation_signed]; exact (doors _).1 v
 have hu: ‖(R:ℂ)^4*M-V‖ ≤ ε:= Y _ _ _ _ (by simpa only [affine,Signed.act_one,add_zero] using he k hk 1 0) (he l hl bZ a)
 have hg(k:PlaqAxes): turned bZ k*turned bZ k=1:=turned_sq ..
 have hC:|C|≤4:=by
    have hb: |turned bZ l.1.2|=1:=by apply (sq_eq_sq₀ (abs_nonneg _) zero_le_one).1; rw [sq_abs, one_pow,pow_two,hg]
    have hp: (|u|)^2≤(2:ℝ)^2:=pow_le_pow_left₀ (abs_nonneg _) w 2
    unfold C; by_cases r:k.2=l.2
    · rw [sch,if_pos r,mul_one,abs_mul,hb,one_mul,abs_of_nonneg (sq_nonneg _)]; simpa only [sq_abs] using hp.trans_eq (by norm_num : (2:ℝ)^2=4)
    rw [sch,if_neg r,mul_zero,abs_zero]; norm_num
 have hx:(↑(cuts B P a R u k l):ℂ)=(C:ℂ)*((R:ℂ)^4*M):=by
    unfold cuts; push_cast; let T₁:= canonZ B P 1 (0:Site n) u; let T₂:=canonZ B P bZ a u
    have hr :(↑(spun T₁ T₂ k l):ℂ)=_:= official B P H_ 1 0 p v E bZ a k l
    have ht: y.2=l.1.2:= rotated_down _; have hy:X.2=k.1.2:= rotated_one _
    rw [show (spun _ _ k l)=_ from (show spun (canonZ B P 1 0 u) (canonZ B P bZ a u) k l=spun T₁ T₂ k l from rfl),hr, original,ht,hy]; unfold C M; push_cast; ring
 have hf: (↑(objective u t k l):ℂ)=(C:ℂ)*V:=by
    unfold V objective breve spit C sch; rw [gladsome _ _ t hv]; by_cases r:k.1.2=l.1.2 <;> by_cases f:k.2=l.2 <;> simp [r,f]; have ht:(↑(turned bZ l.1.2):ℂ)*↑(turned bZ l.1.2)=1:=by exact_mod_cast (hg l.1.2)
    let X:= (↑(turned bZ l.1.2):ℂ); let z:= (u:ℂ)^2; let D':ℂ:= (((t:ℂ)^4)⁻¹*(4*↑Maxwell.normal))
    change z *D'=X*z*(X*D'); rw [show X*z*(X*D')=(X*X)*(z*D') from by ring,show X*X=1 from ht,one_mul]
 have hi:= mul_le_mul (show ‖(C:ℂ)‖≤4 from (by simpa using hC)) hu (norm_nonneg _) (by norm_num); rw [←norm_mul,mul_sub,←hx,←hf,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hi; exact hi
omit p v E H_ hv
private lemma logicle {K:Type}[Fintype K]{Z P:K→K→ℝ}(V:plumK K→ℂ){c E:ℝ}(hp:0≤E) (p:∀ i j,V i≠0→V j≠0→∀ s t:Fin 2, |Z (i s) (j t) - P (i s) (j t)| ≤ E)(ho:∀ i j,|P i j|≤c):
 ‖lodging Z V (star V)-lodging P V (star V)‖ ≤ (2*(E*(c+E)+c*E))*((∑ i,‖V i‖)^2):=by -- remove include extras
 unfold lodging; simp_rw [←sum_sub_distrib,←sub_smul]; rw [pow_two,sum_mul_sum]; simp_rw [mul_sum]
 refine (norm_sum_le ..).trans (sum_le_sum (fun i _=> (norm_sum_le ..).trans (sum_le_sum (fun j _=>?_)))) -- orientation
 rw [Pi.star_apply,norm_smul,norm_mul,norm_star]; by_cases a:V i=0; · rw [a,norm_zero,zero_mul,mul_zero,mul_zero]
 by_cases b:V j=0; · rw [b,norm_zero,mul_zero,mul_zero,mul_zero]
 apply mul_le_mul_of_nonneg_right _ (by positivity:0≤ ‖V i‖*‖V j‖)
 have ht(r t s w:Fin 2): |Z (i r) (j s)*Z (i t) (j w)-P (i r) (j s)*P (i t) (j w)| ≤ E*(c+E)+c*E:=by
    let V:= P (i r) (j s); let X':= Z (i t) (j w); let y:=P (i t) (j w); let R:= Z (i r) (j s)
    have hx:|X'|≤ c+E:=(le_trans (eq_abs_for X' y) ?_); swap; · exact add_le_add (ho ..) (p _ _ a b t w)
    have h:(R-V)*X'+V*(X'-y)=R*X'-V*y:=by ring
    change |R*X'- V*y| ≤ _; rw [←h]; refine (abs_add_le ..).trans (add_le_add (?_) (?_)) <;> rw [abs_mul]
    · exact mul_le_mul (p _ _ a b r s) hx (abs_nonneg _) hp
    exact mul_le_mul (ho ..) (p _ _ a b t w) (abs_nonneg _) ((abs_nonneg _).trans (ho (i r) (j s)))
 unfold twinB; rw [add_sub_add_comm,Real.norm_eq_abs]; exact (abs_add_le ..).trans ((add_le_add (ht 0 1 0 1) (ht 0 1 1 0)).trans_eq (by ring))
where
 eq_abs_for (x y:ℝ) : |x| ≤ |y|+|x-y|:= le_trans (le_of_eq (congrArg (|·|) (add_sub_cancel ..).symm)) (abs_add_le y (x-y))
lemma sufficesB {u t:ℝ}(x:0<t)(p:|u| ≤ 2)(i j:TrackKey G n):|objective u t i j|≤4*fareX t:=by
 unfold objective breve; have h0:= fare_w x
 split; swap; · rw [abs_zero]; positivity
 unfold paysW; rw [abs_of_nonneg (by positivity)]; apply mul_le_mul_of_nonneg_right _ h0.le; rw [← sq_abs]; exact (pow_le_pow_left₀ (abs_nonneg _) p 2).trans_eq (by norm_num)
lemma book_scale (V:TrackKey G n→TrackKey G n→ℝ)(P:tableQ G n ℂ)(r:ℝ) : r^8 • lodging V P (star P)=lodging (fun i j=>r^4*V i j) P (star P):=by
 unfold lodging; simp_rw [smul_sum,smul_smul]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; apply congrArg (· • _); unfold twinB; ring
abbrev recordB (t ε:ℝ):=2*(4*ε*(4*fareX t+4*ε)+4*fareX t*(4*ε))
include H_ p v E hv
lemma registrations(W:tableQ G n ℂ)(Z':Regional o L W)(w:|u|≤2)(ε':0 ≤ ε)(X:doorsW S L o (affine bZ a o) R t ε) : ‖R^8 • lodging (spun (canonZ B P 1 0 u) (canonZ B P bZ a u)) W (star W)-lodging (objective u t) W (star W)‖ ≤ recordB t ε*costs W^2:=by
 rw [book_scale]; exact logicle W (by positivity) (fun i j hi hj s z=> budgetθ B P H_ p v E a t R hv _ _ (Z' i hi s) (Z' j hj z) w X) (sufficesB hv w)
end YM.Regis.Head.Brecht.Pier
