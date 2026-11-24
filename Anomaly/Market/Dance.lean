import Anomaly.Market.Propeller
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
private lemma one_ask (w:ℂ)(x:ℝ): ‖1+w*(x:ℂ)‖ ≤ Real.exp (w.re*x+ (‖w‖* |x|)^2):=by
 let y:=w*(x:ℂ); let q:=w.re*x; let a:=q+‖y‖^2; have he:y.re=q:=by unfold y; simp; rfl
 have hp:‖y‖=‖w‖* |x|:=by unfold y; simp
 rw [←hp]; change ‖1+y‖≤Real.exp a
 refine (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).1 ?_; rw [show Real.exp a^2=Real.exp (2*a) from (by rw [two_mul, sq, Real.exp_add a a])]; apply le_trans _ (Real.add_one_le_exp _)
 unfold a; rw [←he]; rw [Complex.sq_norm]; simp only [Complex.normSq_add]; rw [Complex.sq_norm]; simp; nlinarith [Complex.normSq_nonneg y]
open GeometryP Exterior CF.Swell.Sonar
variable {I:Type*}[Fintype I]
variable {τ:ℂ}{H H':I→Pane N→ℂ}{O:I→Seat N}{fp:ℂ→L[ℝ] ℝ}{L:Tour I (More N)}{s:Hookah N}(v:Propeller O H L fp τ s) {T:List (Hookah N)}(V:Spangled O H L fp τ p T)
lemma visorG {t:ℝ}(p:‖fp‖≤1) (h:∀ i x, ‖H i x‖≤t) (o:Tour I (More N))(x:Pane N): |booth o H fp x|≤ t^Fintype.card I := by
 apply (contracts fp p _).trans; rw [norm_prod]; refine (prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>h i _)).trans_eq ?_; rw [prod_const,card_univ]
include v
lemma spinGuts (p:‖fp‖≤1)(h:∀ i x, ‖H i x‖ ≤ C)(x:Fields N) : ‖s.x x‖≤ portraitS τ (C ^ Fintype.card I):=by -- include v
 obtain ⟨t,o,V,q,y,u⟩:=v.issued; rw [y,floorℓ,norm_smul,norm_one,mul_one]; have hp:‖V‖=‖τ‖:= q.elim (by intro t; rw [t]) (by intro t; rw [t,norm_star]); apply (norm_add_le ..).trans; rw [norm_one,norm_mul,hp,Complex.norm_real,Real.norm_eq_abs]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (visorG p h _ _) (norm_nonneg _))
omit v
include V
lemma taunt (p0:‖fp‖≤1) (h:∀ i x,‖H i x‖≤C)(w:0≤C)(x:Fields N): ‖buffet T x‖≤ portraitS τ (C ^ Fintype.card I) ^ T.length:=by -- same adapters
 induction T with| nil=>simp [Hookah.buffet]| cons i t ih=> rw [List.length_cons,pow_succ',buffet_more,Pi.mul_apply]; refine (norm_mul_le ..).trans (mul_le_mul (spinGuts (V.core i List.mem_cons_self) p0 h _) (ih ⟨fun i f=>V.core i (List.mem_cons_of_mem _ f), (List.pairwise_cons.mp V.annex).2⟩) (norm_nonneg _) (zero_le_one.trans (portraits_h (pow_nonneg w _) _)))
open Scree
-- H' closed surrogate.Soe.Area.
lemma cardSeat (J:∀ i,H i=ᵐ[prior SU.group (More N)] H' i)(Y:∀ i x,‖H' i x‖≤C)(w:0≤C)(pl:‖fp‖ ≤ 1)(F:Scree.Loom N) : ∃ (f: Fin T.length→ Tour I (More N))(U:Pane N→ℂ), scopes f O ∧ Copied L f ∧ (∀ᵐ i∂ (city N), buffet T (i.1,F i)=U i.1 • 1) ∧ ∀ i:Pane N, ‖U i‖≤ Real.exp (τ.re*bistro H' fp f i + T.length*plenitS τ (C ^ Fintype.card I)):=by
 let Q:=Fin T.length; let P(i:Q):= T.get i; have he(i:Q):= (V.core _ (List.get_mem T i)).issued
 choose s o a u g z using he; let f(i:Q):=L.moves (s i) (o i); let U(i:Q)(V: Pane N):ℂ:=1+a i*(booth (f i) H' fp V:ℝ); let R(V:Pane N):=∏ i:Q,U i V
 have hf(y:I)(i j:Q)(t:i<j): seats (f i) O y ≠seats (f j) O y:=fun v=> by
    have h: p+1 ≤ separation (seats (f i) O y) (seats (f j) O y):= V.annex.rel_get_of_lt t _ (z i y) _ (z j y); rw [v,separation_self] at h; omega
 refine ⟨f,R,(fun i j k q=>le_antisymm (le_of_not_gt (fun t=>hf i _ _ t q.symm)) (le_of_not_gt (fun t=>hf i _ _ t q))),⟨fun i=>⟨s i,o i,rfl⟩⟩,?_,?_⟩
 · have h(i:Q): booth (f i) H fp=ᵐ[prior SU.group (More N)]booth (f i) H' fp:=by filter_upwards [Filter.eventually_all.mpr (fun j:I=> (prior_pull ((f i).orient j) ((f i).loc j)).quasiMeasurePreserving.ae (J j))] with j e; exact congrArg fp (prod_congr rfl (fun i _=> e i))
   filter_upwards [(measurePreserving_fst (μ:= prior SU.group (More N)) (ν:=depot N)).quasiMeasurePreserving.ae (Filter.eventually_all.mpr h)] with y hY; apply buffet_head (z:=fun i=> U i y.1); intro i; rw [g i]; unfold floorℓ; rw [show booth _ H fp _=_ from hY i]; -- tune
 intro i; refine (norm_prod ..).trans_le ((prod_le_prod (f:=fun j:Q=> ‖U j i‖) (g:=fun j:Q=>Real.exp (τ.re*booth (f j) H' fp i+plenitS τ (C^Fintype.card I))) (fun _ _=> norm_nonneg _) (fun j _=>?_)).trans_eq (?_)); -- Lean wire ambiguity, annotate
 · let p':=booth (f j) H' fp i; change ‖U j i‖≤_
   apply le_trans (one_ask (a j) p'); apply Real.exp_monotone
   have ht:(a j).re=τ.re ∧ ‖a j‖=‖τ‖:=by rcases u j with p|p <;> rw [p] <;> simp [Complex.star_def]
   rw [ht.1, ht.2,mul_pow]; apply add_le_add_right; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (visorG pl Y _ _) _) (sq_nonneg _)
 rw [←Real.exp_sum,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,← mul_sum]; simp [Q,bistro]
end Hookah.Blaze
end YM.CF.Lamour.Bridge.Celeste.Clock
