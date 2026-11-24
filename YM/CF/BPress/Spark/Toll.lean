import YM.CF.BPress.Spark.Stairs
import YM.CF.BPress.Vesper.Air
/-! TraceC activity price after fixing Strong grant. J families all over nodes, masks retained at each site. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Spark
open Function NormedSpace Finset Filter Lattice Branch Push.AbsoluteSums Grid RG Ledger MeasureTheory SU Pastry Tulip Skye Girt Scree Cube Lat Fock Vesper Spin Spin.Paint Pine Lily Pledge DoughBag --
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ContDiff Real ENNReal Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
variable {N:Side}{g h b Ω a t u:ℝ}{U: Token (Force N) N}{T: Token (LocB N) N}
open Story -- Ω bound prereq h
abbrev card_page :ℕ:= Fintype.card Bias.Page -- tune
abbrev seedJ (g:ℝ):= g*Real.exp (Chalk.ν^2)
def title(g a:ℝ):=seedJ g*a^card_page*(2^card_page)
lemma cardsJ(x: Site N): (Chalk.den x).card=card_page:=by
 -- Mantel.bears private.
 let f(a: Bias.Page):Single N:=((x,a.1),a.2); have hu: Chalk.den x=univ.image f:=by ext i; simp only [Chalk.den,mem_filter,mem_univ,true_and,mem_image]; constructor; intro v; exact ⟨(i.1.2,i.2),by unfold f; rw [← v]⟩; rintro ⟨a,rfl⟩; rfl
 rw [hu,card_image_of_injective,card_univ]; intro i j h; exact Prod.ext (Prod.mk.inj (Prod.mk.inj h).1).2 (Prod.mk.inj h).2
lemma card_team(x:Site N): (team x).card ≤ 2^card_page:= (card_le_card (filter_subset ..)).trans_eq (by simp only [card_univ,Lily.Bot, Lily.Course.stem,Fintype.card_coe,card_powerset,cardsJ]) -- tune
lemma len_j(i:WantJ N):(jBand i).length≤ card_page:=by rw [tune_len, ← cardsJ i.1]; apply card_le_card; exact mem_powerset.mp i.2.val.property
lemma capAJ(B:ℕ): δPort B ≤1:=by
 have he:=beam_x B; unfold δPort; rw [div_le_one (by positivity)]; have ht:0<prec B:= by exact_mod_cast he
 exact_mod_cast (show 1≤2*prec B from by omega)
abbrev hereP(g a:ℝ):= Real.exp 1 * title g a
lemma horizon_j(q:0≤g)(U:1≤a)(B:ℕ): Cash (storyJ (N:=N)) (fun i=> seedJ g*a^(jBand i).length) (δPort B) (hereP g a):=by
 have ht:0≤ seedJ g:=mul_nonneg q (Real.exp_pos _).le; have hx(i:WantJ N):0≤ seedJ g*a^(jBand i).length:= by have hp:=zero_lt_one.trans_le U; positivity; -- tune syntax
 apply stairs (I:=Site N) (N:=N) (J:=fun i: Site N=>↥(team i)) (X:=fun i=>{node i}) _ (v:=fun _=>title g a) ?_ hx ?_
 · have he:0≤ title g a:=by unfold title; have hp:=zero_lt_one.trans_le U; positivity
   refine ⟨fun _=>he,fun i=>?_⟩; let X(j:Site N): Support (More N):={node j}; let S:=Ledger.score X (fun _=>title g a) (δPort B) i; have ht(j):0≤ S j:=by unfold S Ledger.score; split; exact mul_nonneg (Real.exp_pos _).le he; exact le_rfl
   refine ⟨ht,(hasSum_fintype _).summable,?_⟩; rw [tsum_fintype]; by_cases t:∃ j:Site N,i=node j
   · obtain ⟨j,v⟩:=t; rw [sum_eq_single j]; unfold Ledger.score; rw [if_pos (mem_singleton.mpr v)]; simp only [card_singleton,Nat.cast_one,mul_one]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (capAJ B)) he; intro k _ e; exact if_neg (fun z => e (Tenant.needle ((mem_singleton.mp z).symm.trans v))); simp
   change (∑ i, S i)≤_; rw [sum_eq_zero (f:=S) (fun j _=> if_neg (fun v=> t ⟨j, mem_singleton.mp v⟩))]; exact mul_nonneg (Real.exp_pos _).le he
 · intro i; refine (sum_le_sum (g:=fun _: ↥(team i)=> seedJ g*a^card_page) (fun j _=> mul_le_mul_of_nonneg_left (pow_le_pow_right₀ U (len_j ..)) ht)).trans ?_; rw [sum_const,nsmul_eq_mul,card_univ,Fintype.card_coe,title,mul_comm ((team i).card:ℝ)]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_team i) (mul_nonneg ht (pow_nonneg (zero_le_one.trans U) _))
end YM.CF.BPress.Spark
