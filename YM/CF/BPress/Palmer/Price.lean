import YM.CF.BPress.Palmer.Root
import YM.CF.Palot.Fond
/-! lem:B-rootK parts 1 and 2 variants with quantitative thresholds (pure constants * γ/spare; reduce rate if needed and epower). Uses manuscript graph coefficients and trees. All applications here on **finite labels**; log an actual sum over all ordered tuple multiplicities. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Palmer
open Function Relation Filter NormedSpace MeasureTheory Finset Lattice RG Grid Branch Ledger Push.AbsoluteSums Ursell Trees Animals Graph
open scoped Topology BigOperators InnerProductSpace Classical
variable {s:Side}{Y I Ω:Type}[Fintype I][Fintype Y][DecidableEq Y] {F:Branch.Field Y}{X:I→Seal Y}{c a γ δ:ℝ}{w:I→ℝ}{m: Side}
variable (X)
def cash (w:I→ℝ) := lump (carrier X) (fun z=>tax X z w)
def logL (w:I→ℂ) := lump (carrier X) (Palot.guava (relate X) w)
lemma η_reader (x: Seal Y) (f g:I→ℂ)(h:∀ i,X i ⊆ x→ f i=g i): logL X f x=logL X g x:=by
 apply tsum_congr; intro b; split; next v=> unfold Palot.guava; rw [prod_congr rfl (show ∀ i∈ (univ:_), f (b.2 i)=g (b.2 i) from fun i _=> h _ (v.symm ▸ subset_biUnion_of_mem (fun j=>X (b.2 j)) (mem_univ i)))]
 next v=>rfl
lemma tax_frame (f:I→ℂ)(w:I→ℝ)(h:∀ i,‖f i‖ ≤ w i)(z:Clusters I): ‖Palot.guava (relate X) f z‖ ≤ tax X z w:=by
 unfold tax clusters Palot.guava; rw [norm_smul,Real.norm_eq_abs, abs_div,abs_of_nonneg (by positivity : 0 ≤ (↑((z.1+1).factorial):ℝ)), norm_prod,div_mul_eq_mul_div]; gcongr; exact h _ -- tune
variable {X} (g: evenT F X)(p:Sole F m)(S: Stakes m a γ)(H:Cash X w (a+a) γ)
include g p S H
lemma bookTax : Summable (fun z=>tax X z w):=by
 have he:= cluster_pay X g p S H; apply (he.total S.he.le ?_ ).2.1; intro i v; obtain ⟨x,t⟩:= Grid.inhabited_grove (g (i.2 none)); have ht:x∈ carrier X i:=mem_biUnion.mpr ⟨none,mem_univ _,t⟩; exact False.elim (notMem_empty x (v ▸ ht))
lemma book : Cash id (cash X w) a (till_cost m γ):= (cluster_pay X g p S H).lump _ _ (bookTax g p S H) -- arg
lemma log_cost (f:I→ℂ)(h:∀ i,‖f i‖≤ w i)(x):‖logL X f x‖ ≤ cash X w x:= lump_bound _ _ _ (bookTax g p S H) (tax_frame _ f w h) x
lemma log_grove {x}(h: cash X w x≠0) : Grove F x:=by
 obtain ⟨i,e⟩:= Classical.not_forall.mp (show ¬ ∀ i:Clusters I,(if x=carrier X i then tax X i w else 0)=0 from fun v=>h (by unfold cash Ledger.lump; simp_rw [v]; exact tsum_zero)); split at e; next v=> rw [v]; exact carries X i e g
 next t=> contradiction -- tune

lemma bindingL (f:I→ℂ)(h:∀ i,‖f i‖≤w i) : Complex.exp (∑ t, logL X f t)=∑ i:Finset I,Palot.pace (relate X) f i:=by
 obtain ⟨s,π,e,x⟩:=reports F p; let V(i):=(X i).image π; have hw:=fare_p F π S g (fun i=> e _ (g i)) x H; have ht(i:I):‖f i‖≤fareX X a w i:= (h _).trans (fare_le X w H.pos S.he.le _); have he:= Palot.shineP f (R:=relate X) ⟨fun i k=> (?_),fun i j v u=> v u.symm⟩ (brute X V (?_)) le_rfl ht hw; swap; next i k=>
    obtain ⟨x,u⟩:= Grid.inhabited_grove (g i); exact disjoint_left.mp k u u
 swap; · intro i j t; apply Finset.not_disjoint_iff.mpr; obtain ⟨u,x,y⟩:=Finset.not_disjoint_iff.mp t; exact ⟨π u,mem_image_of_mem π x,mem_image_of_mem π y⟩
                                                                        -- tune order
 let J:= Palot.guava (relate X) f; unfold logL; rw [lump_sum _ _ he.1.of_norm]; exact (congrFun Complex.exp_eq_exp_ℂ (∑' z,J z)).trans he.2
lemma cash_f [TopologicalSpace Ω](f:Ω→I→ℂ)(h:∀ i x, ‖f x i‖≤w i)(t:∀ i:I,Continuous fun x=> f x i)(T:Seal Y): Continuous fun u=> logL X (f u) T:=by
 unfold logL Ledger.lump; refine continuous_tsum (u:=fun z=>tax X z w) ?_ (bookTax g p S H) ?_; · intro i; unfold Palot.guava; split; exact Continuous.smul (f:=fun _:Ω=> (coefficient (relate X) i.2/(i.1+1).factorial:ℝ)) continuous_const (continuous_finsetProd _ (fun j _=> t _)); exact continuous_const
 intro i x; split; exact tax_frame _ _ _ (fun i=> h i x) i; rw [norm_zero]; exact (cluster_pay X g p S H).pos _
omit g p S H in
lemma cash_meas [MeasurableSpace Ω] (X:I→Seal Y)(f:Ω→ I→ℂ)(h: Measurable f)(t:Seal Y): Measurable fun x=> logL X (f x) t:=by
 unfold logL Ledger.lump; apply Measurable.tsum; intro i; split; unfold Palot.guava; exact Measurable.smul (f:=fun _:Ω=> (coefficient (relate X) i.2/(i.1+1).factorial:ℝ)) measurable_const (g:=fun x:Ω=> ∏ j,f x (i.2 j)) (Finset.measurable_fun_prod _ fun i _=>(measurable_pi_apply _).comp h); exact measurable_const -- tune
omit g p S H in
lemma log_idle (T:Seal Y): logL X (fun _=>0) T=0:=by unfold logL Ledger.lump; apply HasSum.tsum_eq; apply (hasSum_zero).congr_fun; intro i; symm; rw [show Palot.guava _ (fun _=> (0:ℂ)) i=0 from ?_]; simp; unfold Palot.guava; rw [prod_eq_zero (mem_univ none) rfl, smul_zero]
end YM.CF.BPress.Palmer
