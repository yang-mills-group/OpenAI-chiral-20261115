import YM.SU5.Selected.Airy.Income
import YM.SU5.Selected.Lantern.Particle
/-! # Preparation of the geometry/cost stages. Economics already pays for native-size estimator.
Fee requested via Supplier, not after-observation. Does not claim there already ARE
tiles, especially on elected data. Full counts allow reflection in one phase. Future generator.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
-- Wlog one prepared tender. any eventual t foothold s, m on SAME Y.
namespace Tender
open Stencil (pulseNode pval pace heats)
def widthK (G D:Side)(i:ℕ):ℕ:= 10000*D.val*G.val*i
def powerK (G D:Side)(u i:ℕ):ℕ:=u*G.val*D.val^3*i^4
-- Actual geometry allocation size, use in profile later.
abbrev Weeks (G:Side)(q:ℕ):= Fin (G.val*q)
abbrev Mile (D:Side)(q:ℕ):= Fin (D.val*q)
abbrev Acres (G D:Side)(u q:ℕ):= Weeks G q × Mile D q × Mile D q × Mile D q × Fin (10*u)
lemma power_acre (G D:Side)(u q:ℕ):Fintype.card (Acres G D u q) = 10* powerK G D u q:=by unfold Acres Weeks Mile powerK; simp; ring
private def crux (G:Side)(T:ℝ) := max (1:ℝ) (T*((8*10000)^4*1000* (G.val:ℝ)^3))
def folio (G:Side)(T:ℝ): ℕ := (exists_nat_gt (crux G T)).choose
lemma folred (G:Side)(T:ℝ): folio G T>0:= by have h: (0:ℝ)< folio G T:=lt_of_le_of_lt ((show 0 ≤ crux G T from (show (0:ℝ) ≤ 1 by norm_num).trans (le_max_left ..))) (exists_nat_gt (crux G T)).choose_spec; exact_mod_cast h
def rentL (D:Side):ℝ:= D.val/1000
lemma effort (G D:Side)(T:ℝ)(q ℓ:ℕ)(p:0<q)(e: ℓ ≤ widthK G D q) :
    rentL D * ((powerK G D (folio G T) q:ℝ)/( (4:ℝ)*↑(widthK G D q+ℓ))^ (4:ℕ)) ≥ T:= by
 let B:=widthK G D q; let F:=powerK G D (folio G T) q; let δ:ℝ:= (8*(B:ℝ))^ (4:ℕ); have hB:0<B:=by unfold B widthK; positivity; -- P0 maybe instances
 have hp : (4* (((B+ℓ:ℕ):ℝ)))^ (4:ℕ) ≤ δ:= pow_le_pow_left₀ (by positivity) (by push_cast; have h:(ℓ:ℝ)≤ (B:ℝ):= (by exact_mod_cast e); linarith) _
 apply le_trans _ (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (Nat.cast_nonneg (n:=F)) (by positivity) hp) (by unfold rentL; positivity)) -- tune implicit denom type
 unfold δ B F rentL powerK widthK; rw [←mul_div_assoc]; apply (le_div_iff₀ (by positivity)).mpr; push_cast
 let s:ℝ:=(D.val:ℝ)^4*(q:ℝ)^4*(G.val:ℝ); have h:T*((8*(10000:ℝ))^4*1000* (G.val:ℝ)^3) ≤ folio G T:= ((le_max_right ..).trans_lt (exists_nat_gt (crux G T)).choose_spec).le
 have hs: 0 ≤ s :=by unfold s; positivity
 nlinarith only [mul_le_mul_of_nonneg_right h (show 0≤ (D.val:ℝ)^4*(q:ℝ)^4*G.val from hs)]

-- Cost of norm per-patch B & expected. It suffices to control columns separately, at a normalized level not depending on tile size. Estimate via shop ticket.
variable {J n:Type}[Fintype n][DecidableEq n][Fintype J][DecidableEq J] (i:ℕ)
def dueW (R:ℝ):= 1+( (2*R)^(20:ℕ)*(∑ i,‖Stencil.rho i‖))
lemma due_pos (R:ℝ) (p:0≤R): 1≤ dueW R := le_add_of_nonneg_right (by positivity)
section mark
variable {N:Side}{S:Finset (Seat N)} (A:Station S n J) (x:Fields N)
lemma workW {n:Type*}[Fintype n][Nonempty n][LinearOrder n](X:WRect n J)(T:ℝ) (f:∀ i:J,‖col X i‖≤ T) (b:Bool) : ‖tape b X‖ ≤ T ^ Fintype.card J:= by
 suffices h:∀ L:List J,‖party (col X) b L‖ ≤ T^L.length by
    unfold tape; simpa only [Finset.length_toList,Finset.card_univ] using h univ.toList
 intro L; induction L with
 |nil=>simp [party,Stencil.foil]
 |cons i L ih=>
    rw [show party _ b _= creed b (col X i) * party (col X) b L from rfl]; simp only [List.length_cons,pow_succ']; apply (norm_mul_le ..).trans; exact mul_le_mul ((Flare.cost_pe ..).trans (f _)) ih (norm_nonneg _) ((norm_nonneg _).trans (f i))
lemma counter (p:Fintype.card J=10)(i:n)(R:ℝ)(pR:0≤R)(e₁:∀ (c:Bool)(j:J), ‖col (A.low i c x) j‖ ≤ R)(e₂:∀ (c:Bool)(j:J),‖col (A.high i c x) j‖ ≤ R) : ‖(flickH S x) (Stencil.tonality Stencil.rho (A.roster i))‖ ≤ dueW R:=by
 have e(k:pulseNode):‖flickH S x (A.roster i k)‖≤ (2*R)^ (20:ℕ):=by
    change ‖-(tape true (A.fLow i k x)*tape false (A.fHigh i k x))‖ ≤ _; unfold Station.fLow Station.fHigh; rw [norm_neg,show (2*R)^ (20:ℕ)=(2*R)^ Fintype.card J*(2*R)^ Fintype.card J by rw [←pow_add,p]]; -- unfold tune
    refine (norm_mul_le ..).trans (mul_le_mul (workW _ _ ?_ _) (workW _ _ ?_ _) (norm_nonneg _) (by positivity));
    · intro j; rw [mixt_a,col_add,col_scale]; apply (norm_add_le ..).trans; rw [norm_smul,norm_pow,Complex.norm_of_nonneg (pace k).1]; refine le_trans ?_ (le_of_eq (two_mul R).symm); apply add_le_add _ (e₁ false _); exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (pace k).1 (pace k).2)).trans (e₁ true _)
    intro j; rw [mixt_b,col_scale,norm_smul,Complex.norm_of_nonneg (heats _ (pace k).1).1.le]; apply (mul_le_of_le_one_left (norm_nonneg _) (heats _ (pace k).1).2).trans; rw [col_add,col_scale,two_mul]; apply (norm_add_le ..).trans; rw [norm_smul,Complex.norm_of_nonneg (pace k).1]; exact add_le_add ((mul_le_of_le_one_left (norm_nonneg _) (pace k).2).trans (e₂ true _)) (e₂ false _)
 rw [Stencil.tonality,map_sum]; simp_rw [map_smul]; apply (norm_sum_le ..).trans; simp_rw [norm_smul]; apply (sum_le_sum (fun a (_:a∈ univ)=> mul_le_mul_of_nonneg_left (e a) (norm_nonneg _))).trans; rw [←sum_mul,mul_comm]; exact le_add_of_nonneg_left zero_le_one
end mark
lemma toll_pos {R:ℝ}(p:0≤R): 1≤ Station.tollK (dueW R):= by
 have hQ:1 ≤ (2:ℝ)^ (13:ℕ)*(dueW R)^ (10:ℕ):= one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (due_pos _ p)); exact hQ.trans (le_max_right ..)

-- W future geometry. `tight` errors θ. Clock rates. `θ` pays Winter too.
def clouds (D:Side):ℝ:= (Real.exp (-((1:ℝ)/100)))^D.val
def levyH (D:Side)(R:ℝ):ℝ:= clouds D^ (3:ℕ)/(100* R^ (2:ℕ))
def tightH (D:Side)(R:ℝ):ℝ:= levyH D R / (100* R ^ (4:ℕ))
lemma cloudsK (D:Side):clouds D∈ Set.Ioc (0:ℝ) 1:= ⟨by unfold clouds; positivity,pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by norm_num))⟩
lemma mugs {R:ℝ}(p:1≤R) (D:Side): 0< tightH D R:= by have h:0<R:=(by linarith); have hf:0<clouds D:= (cloudsK ..).1; unfold tightH levyH; positivity
lemma mill {R:ℝ}(p:1≤R) (D:Side): levyH D R+(levyH D R+tightH D R*R) ≤ 1/3 ∧ levyH D R+tightH D R*R+(R*2)*(levyH D R+(levyH D R+tightH D R*R)) ≤ clouds D^3 := by
 let a:= levyH D R; let b:= tightH D R; let v:ℝ:=clouds D^3; have hp:0<R:=(by linarith); have ha:0<a:=by have hv:0<clouds D:=(cloudsK ..).1; unfold a levyH; positivity; -- cleanup
 have h:b*R≤a:=by
    unfold b tightH; change a/(100* _) * _≤_; rw [div_mul_eq_mul_div]; apply (div_le_iff₀ (by positivity)).mpr; gcongr; nlinarith [show 1 ≤ R^3 from one_le_pow₀ p,show 1 ≤ R^2 from one_le_pow₀ p]
 have hv : v≤1:= pow_le_one₀ (cloudsK ..).1.le (cloudsK ..).2
 have ht:(100*a)*R ≤ v:=by unfold v; apply le_trans _ (le_of_eq (div_mul_cancel₀ (clouds D^3) (show (100*R^2:ℝ) ≠ 0 by positivity))); -- defeq a
                                       change _ ≤ a*(100*R^2); nlinarith [mul_le_mul_of_nonneg_left (show R≤R^2 by nlinarith) ha.le]
 constructor
 · change a+(a+b*R)≤_; nlinarith
 change a+b*R+(R*2)*(a+(a+b*R)) ≤ v; nlinarith [mul_le_mul_of_nonneg_left h hp.le]

end Tender
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Tender
#print axioms effort
#print axioms counter
#print axioms mill
