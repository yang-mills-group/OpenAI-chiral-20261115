import SatinThinLittle
import SatinThinReport
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 260000
noncomputable section
namespace YM.CF.Lamour.Bridge.Celeste.Clock
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye CF.Pannier.Chancel Brace Velvet Hours Flare Cliplet RG Reed
open Py.Rate.Pannier
open Buffered.Afterglow
open Next.Rank.Thirst
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{N m:Side}{j r p d t:ℕ}{M:Tulip.Male}{ε ξ σ C D:ℝ}
namespace Hookah.Blaze
open Regis.Head Etch Regis.Head.Garland
open scoped Classical
private lemma one_trial (w:ℂ)(x:ℝ): ‖1+w*(x:ℂ)‖ ≤ Real.exp (w.re*x+ (‖w‖* |x|)^2):=by
 let y:=w*(x:ℂ); let q:=w.re*x; let a:=q+‖y‖^2; have he:y.re=q:=by unfold y; simp; rfl
 have hp:‖y‖=‖w‖* |x|:=by unfold y; simp
 rw [←hp]; change ‖1+y‖≤Real.exp a
 refine (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).1 ?_; rw [show Real.exp a^2=Real.exp (2*a) from (by rw [two_mul, sq, Real.exp_add a a])]; apply le_trans _ (Real.add_one_le_exp _)
 unfold a; rw [←he]; rw [Complex.sq_norm]; simp only [Complex.normSq_add]; rw [Complex.sq_norm]; simp; nlinarith [Complex.normSq_nonneg y]
abbrev plenitS (τ:ℂ)(X:ℝ):=‖τ‖^2 * X^2
abbrev portraitS (τ:ℂ)(X:ℝ):=1+ ‖τ‖*X
lemma portraits_h {X:ℝ}(t:0≤X)(τ:ℂ) :1 ≤ portraitS τ X:= le_add_of_nonneg_right (by positivity)
variable {I:Type*}[Fintype I](A:Tour I (More N))(x:ℝ)(z:PlaqAxes→ℝ)(P:BudgetPoint)(τ:ℂ)
abbrev plainMark (a:ℂ)(U: Pane N):ℂ:=1+a*(A.exhibit z x P.threshold U:ℝ)
lemma plainCost {a:ℂ}(p:a=τ∨a=star τ)(U: Pane N) : ‖plainMark A x z P a U‖≤Real.exp (τ.re*A.exhibit z x P.threshold U+ plenitS τ (costG z P.threshold x^Fintype.card I)):=by -- a
 have he:a.re=τ.re ∧ ‖a‖=‖τ‖:= by rcases p with p|p <;> rw [p] <;> simp [Complex.star_def];
 apply (one_trial a _).trans (Real.exp_monotone ?_); rw [he.1,mul_pow,he.2]; apply add_le_add_right; apply mul_le_mul_of_nonneg_left _ (sq_nonneg _); exact pow_le_pow_left₀ (abs_nonneg _) (A.exhibit_cost z x) _
variable {A x z τ} {L:List (Hookah N)}
variable {B:Hookah N} (H: Vote z A x P.threshold τ B)
local notation "W"=>Etch.costG z P.threshold x ^ Fintype.card I
local notation "W'" A:max a:max=>plainMark A x z P a
lemma Vote.early (H: Vote z A x P.threshold τ B)(U:Fields N): ‖B.x U‖ ≤ portraitS τ W:=by
 obtain ⟨s,o,a,h,y,_⟩:=H.issued; rw [y,bootF,norm_smul,norm_one,mul_one]
 have hp: ‖a‖=‖τ‖:= h.elim (by intro t; rw [t]) (by intro t; rw [t,norm_star]); apply (norm_add_le ..).trans; rw [norm_one,norm_mul,hp,Complex.norm_real,Real.norm_eq_abs]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (silk_price z (A.moves s o) x P U.1) (norm_nonneg _)) -- note add_le_add_left
lemma Sown.rain (v:Sown z A x P.threshold τ p L)(U:Fields N):‖buffet L U‖≤portraitS τ W ^ L.length:=by
 induction L with| nil=>simp [Hookah.buffet]| cons i L ih=> rw [List.length_cons,pow_succ',buffet_more,Pi.mul_apply]; refine (norm_mul_le ..).trans (mul_le_mul ((v.core i List.mem_cons_self).early P U) (ih ⟨fun i t=> v.core i (List.mem_cons_of_mem _ t), (List.pairwise_cons.mp v.annex).2⟩) (norm_nonneg _) (zero_le_one.trans (portraits_h (by unfold costG meritG; positivity) _)))
open Scree
lemma Sown.chart (v:Sown z A x P.threshold τ p L) (h:CF.Rue.IsleB SU.group P.threshold) (F:Scree.Loom N) : ∃ (f: Fin L.length→ Tour I (More N))(U:Pane N→ℂ), Stationed f ∧ Copied A f ∧ (∀ᵐ i∂ (city N), Hookah.buffet L (i.1,F i)=U i.1 • 1) ∧ ∀ i:Pane N, ‖U i‖≤ Real.exp (τ.re*panorama z x f P.threshold i+L.length*plenitS τ W) :=by
 let T:= Fin L.length; let Z(i:T):=L.get i; have hp(i:T):= (v.core _ (List.get_mem L i)).issued
 choose s o a u g z' using hp; let f(i:T):=A.moves (s i) (o i); let n:= Fin L.length; let K(i:Pane N):=∏ k:T, (W' (f k) (a k)) i
 have hf(y:I)(i j:T)(t:i<j): interest f y i ≠interest f y j:=fun k=> by
    have h: p+1 ≤ separation (interest f y i) (interest f y j):= v.annex.rel_get_of_lt t _ (z' i y) _ (z' j y); rw [k,separation_self] at h; omega
 refine ⟨f,K,fun i j k g=>le_antisymm (le_of_not_gt (fun h=>hf i _ _ h g.symm)) (le_of_not_gt (fun h=>hf i _ _ h g)),⟨fun i=>⟨s i,o i,rfl⟩⟩,?_,fun i=>?_⟩
 · filter_upwards [(measurePreserving_fst (μ:= prior SU.group (More N)) (ν:=depot N)).quasiMeasurePreserving.ae (Filter.eventually_all.mpr (fun i:T=> silk_warm z (f i) x h))] with y v;
   apply buffet_head (z:=fun i=> (W' (f i) (a i)) y.1); intro i; rw [g i]; unfold bootF; change (1+a i * (silk z (f i) x P.threshold y.1:ℝ)) • 1= _; rw [show silk z (f i) x P.threshold y.1=_ from v i]
 unfold K; rw [norm_prod]; refine (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=> plainCost (f j) x z P τ (u j) i)).trans_eq ?_; rw [←Real.exp_sum,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,← mul_sum]; simp [panorama,T] -- tune
end Hookah.Blaze
end YM.CF.Lamour.Bridge.Celeste.Clock
#print axioms YM.CF.Lamour.Bridge.Celeste.Clock.Hookah.Blaze.Sown.chart
