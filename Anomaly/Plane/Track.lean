import Anomaly.Plane.Echelon
import SatinThinGalaxy
/-!
# Pearl pass: split stencil so on receipt k full tourism and single axis vs variable centers.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 633000
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Head.Brecht.Pier
open Function Filter Metric MeasureTheory NormedSpace ProbabilityTheory Finset GeometryP
open Lattice RG Wilson Tree Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Gleam
open Circuit
open Etch Next.Free
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal InnerProductSpace
variable {n:Side}{G:Gauge}{q:Clip}{S:Bed}{Z:PathData G}{η θ ζ w D c d u K:ℝ}{U:Config G n}{O:Support n}{o x z:Site n}{L:ℕ}
variable (B:Z.Bounds q η θ ζ) (P:Attached S Z)(H_:Floor S q n w D)
open CF.Swell.Sonar Garland
local notation "μ"=>stamen B P n
local notation "r"=> stdGaussian μ
variable (F W:tableQ G n ℂ)(s:Signed)(a:Site n)
def canonZ (u:ℝ)(i:TrackKey G n) : μ :=
 let p:= i.1; let b:= Face.send s a p; turned s p.2 • plar B P (b.1, plaquette b.2) u i.2
lemma harbor_w (i:TrackKey G n)(y:μ): giveAt s a q u y.val i=A (canonZ B P s a u i) y:=by
 let b:= Face.send s a i.1; unfold giveAt canonZ A; have he(x y:μ)(k:ℝ): inner ℝ (k • x) y=k*inner ℝ x y:=real_inner_smul_left x y k; simp_rw [plar,he,joy]; rw [inspire, Prod.eta, mul_assoc]
 -- tune
lemma crystalV(y:μ): crystalT F s a q u y.val= curly F (canonZ B P s a u) y:=by
 unfold crystalT tariff curly treasury; simp_rw [harbor_w B P]; simp [Fin.prod_univ_succ,mats]
lemma coverV(y:μ): coverT F s a q u K y.val= choppy F (canonZ B P s a u) K y:=by
 unfold coverT tariff choppy treasury; simp_rw [harbor_w B P]; simp [Fin.prod_univ_succ,pat]
lemma brightP (i:TrackKey G n)(p:|u| ≤ 2): ‖canonZ B P s a u i‖ ≤ 2*(Real.sqrt q.direct)⁻¹:=by
 unfold canonZ; rw [norm_smul]; have he:‖turned s i.1.2‖=1:=by
    rw [Real.norm_eq_abs]; apply (sq_eq_sq₀ (abs_nonneg _) zero_le_one).1; rw [sq_abs,pow_two,turned_sq,one_pow]
 rw [he,one_mul]; exact mintBudget _ _ _ _ p -- tune arity
lemma gauge_1 (V : Dir G n) : bank 1 (0:Site n) V=V:=by
 funext j; obtain ⟨w,i⟩:= j; obtain ⟨p,rfl⟩:= axisEquiv.surjective i; -- tune transport
 simp [bank, arbor,dusk,Bid.pulled,reorient, Step.rotate,Step.used,affine,posDir]; rw [show axisEquiv.symm (coord p)=p from axisEquiv.symm_apply_apply p] -- tune
include H_
-- exact covariance all pairs, incl same-copy mirror with offset & color. use Head shift law loans.
lemma echoed (U:Bid.Sworn S n G) (u:ℝ)(i j:TrackKey G n): spun (canonZ B P s a u) (canonZ B P s a u) i j=spun (canonZ B P 1 0 u) (canonZ B P 1 0 u) i j:=by
 let f (e:Signed)(b:Site n):Altar G n→ℝ:= fun y=>giveAt e b q u y i*giveAt e b q u y j
 have hh(e:Signed)(b:Site n):spun (canonZ B P e b u) (canonZ B P e b u) i j= clouds B P (f e b):=by
    unfold clouds f spun; simp_rw [harbor_w]; exact (appraisal ..).symm
 rw [hh,hh]; symm; apply cover_calms s a B P H_ U; exact (offerCont ..|>.continuous).mul (offerCont ..|>.continuous)
 intro x; unfold f; simp_rw [projected_cursor q P B,gauge_1]
lemma official (U: S.covered c D)(p:0<c)(v:Even n.val) (t:Signed)(b:Site n)(i j:TrackKey G n): let k:= canonZ B P s a u; let l:=canonZ B P t b u; let x:= Face.send s a i.1; let y:=Face.send t b j.1; (↑(spun k l i j):ℂ)= ↑(turned s i.1.2)*↑(turned t j.1.2)*(u:ℂ)^2*(sch (G:=G) i.2 j.2:ℂ)*rimble n S (x.1,plaquette x.2) (y.1,plaquette y.2):=by
 intro k l x y; let b':= (x.1,plaquette x.2); let a':= (y.1,plaquette y.2); have he:= chimes B P H_ U p i.2 j.2 b' a' v; simp_rw [←joy,appraisal] at he; unfold spun A k l canonZ plar; have hp (X Y:μ)(m:ℝ): inner ℝ (m • X) Y=m*inner ℝ X Y ∧ inner ℝ X (m • Y)=m*inner ℝ X Y:= ⟨real_inner_smul_left X Y m,real_inner_smul_right X Y m⟩; simp_rw [(hp _ _ _).1,(hp _ _ _).2]; push_cast; unfold b' a' x y at he; rw [he]; unfold x y; ring
lemma mean_plus (U:Bid.Sworn S n G) (u:ℝ):let X:= curly F (canonZ B P 1 0 u); let Z:= curly (star F) (canonZ B P s a u); (∫ y,Z y∂r)=star (∫ y,X y∂r):= by
 intro x y; unfold y x; rw [values_K,values_K,star_sum]; refine sum_congr rfl fun i _=> ?_; rw [Pi.star_apply,star_smul,star_trivial (_:ℝ)]; exact congrArg (fun t:ℝ=> t • star (F i)) (echoed B P H_ s a U u (i 0) (i 1))
omit H_
lemma polished :tally (choppy F (canonZ B P 1 0 u) K) (choppy W (canonZ B P s a u) K)= ∫ y:μ,coverT F 1 0 q u K y.val * coverT W s a q u K y.val∂r:=by simp_rw [coverV B P]; rfl
lemma pairs_integrate (a0:0<K): Integrable (fun y:μ=>coverT F 1 0 q u K y.val *coverT W s a q u K y.val) r :=by simp_rw [coverV B P]; exact integral_k F W (fun i j=> (pat_bold a0).integrable_mul (pat_bold a0))
end YM.Regis.Head.Brecht.Pier
