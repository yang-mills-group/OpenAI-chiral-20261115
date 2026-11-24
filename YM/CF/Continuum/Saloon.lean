import YM.CF.Ups.Shea
import YM.CF.Graph.Coif
import YM.CF.Ups.Gala
set_option autoImplicit false
set_option maxHeartbeats 980000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars true
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Jade.Earn
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Larch Rue Salt Vow Bake Push.AbsoluteSums Ione
variable {n:Side}(P:BudgetPoint)

local notation "Ω"=> Fintype.card (Site (More n))
lemma autumn_full (V:Orbit n)(K:Cusp n){H a δ γ w:ℝ}{v:Aura n→ℝ}(W: Trees.Ready Palot.stern P.B v a γ δ w)(h:1 ≤ H)(t:∀ i:Aura n,Vow.Medal P i.val ∅ (K i ∅) H (v i))(u:0 ≤ a) : ‖coldE P (FeeD P (fun i=>K i ∅)) V‖≤ Ω*(γ*w^0*(1-w)⁻¹):=by
 let p':= γ*w^0*(1-w)⁻¹; have hw':0 ≤ p':=by unfold p'; have z:=W.1; have hp:=sub_pos.mpr W.2.2.2.1; positivity
 have ht(i:Aura n):= glenP i h t W u 0; have hh(i:Aura n):0≤ spanD i v 0:= (ht i).wage (zero_le_one.trans h);
 have hg(i:Skye.Seat n): (∑ j:Aura n with i∈j.val, spanD j v 0) ≤ p':=((sum_le_sum fun j _=> le_mul_of_one_le_right (hh j) (show 1 ≤ Trees.currency P.B a j.val from Real.one_le_exp (by positivity)))).trans (thinX W u _ _)
 calc
    _ ≤ ∑ j:Aura n, spanD j v 0 := by
       apply (norm_sum_le ..).trans; rw [sum_filter]; refine sum_le_sum fun i _=>?_ ; split; next p=> exact (ht i).capF h V (by rw [sdiff_empty]; exact p)
       exact hh i -- indent
    _ ≤ ∑ i:Aura n,∑ j:Skye.Seat n,if j∈ i.val then spanD i v 0 else 0 := by
       refine sum_le_sum fun i _=>?_; have h(j:Skye.Seat n):0 ≤ if j∈ i.val then spanD i v 0 else 0 := by split; exact hh _; exact le_rfl
       obtain ⟨q,r⟩:= i.property; exact le_trans (b:=if q∈ i.val then spanD i v 0 else 0) (by rw [if_pos r]) (single_le_sum (s:=univ) (fun j _=>h j) (mem_univ q))
    _ ≤ ∑ _:Skye.Seat n,p':=by rw [sum_comm]; refine sum_le_sum fun i _=>?_ ; rw [←sum_filter]; exact hg i
    _ = _:=by rw [sum_const,card_univ, nsmul_eq_mul]
private lemma expCap(K: Cipher n) : ‖exp K‖ ≤ Real.exp ‖K‖:=by
 have hg(v:ℝ)(Y:Cipher n): ‖v • Y‖ = ‖v‖*‖Y‖:=norm_smul v Y.val
 letI : NormedAlgebra ℚ (Cipher n):=NormedAlgebra.restrictScalars ℚ ℝ _
 rw [congrFun (exp_eq_tsum ℝ), Real.exp_eq_exp_ℝ,congrFun (exp_eq_tsum ℝ)] -- tune
 refine (norm_tsum_le_tsum_norm (norm_expSeries_summable' (𝕂:=ℝ) K)).trans (?_)
 exact Summable.tsum_mono (norm_expSeries_summable' (𝕂:=ℝ) K) (by apply Summable.of_norm; exact norm_expSeries_summable' (𝕂:=ℝ) ‖K‖) (fun j=> by rw [hg,Real.norm_of_nonneg (by positivity)]; exact mul_le_mul_of_nonneg_left (norm_pow_le ..) (by positivity))
private lemma expSafe(K:Cipher n) : Real.exp (-‖K‖) ≤ ‖exp K‖ :=by
 letI : NormedAlgebra ℚ (Cipher n):=NormedAlgebra.restrictScalars ℚ ℝ _
 rw [Real.exp_neg,←one_div, div_le_iff₀ (Real.exp_pos _)]
 calc
    _ = ‖(1: Cipher n)‖:=by simp
    _ = ‖exp K*exp (-K)‖:=by rw [←exp_add,add_neg_cancel,exp_zero]
    _ ≤ ‖exp K‖ * ‖exp (-K)‖:=norm_mul_le ..
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [norm_neg K] using expCap (-K)) (by positivity)
lemma bulge_E(d γ h v:ℝ)(hp:1 ≤ h):∀ (K:Cusp n)(W:Aura n→ℝ), Trees.Ready Palot.stern P.B W (P.supportExponent+1+1) γ d (Trees.degreePrice P.B γ d) → (∀ i:Aura n,Vow.Medal P i.val ∅ (K i ∅) h (W i)) →∀ (E: RegBudget n)(C':ForceBudget n)(L:ℝ)(T:Ids n),IncX Ione.Utrue E P h v → (let V:Orbit n:=(1,T); Palot.hGas (flags P.threshold V.1) (keyL P K (fun i=>K i ∅) V) = Real.exp L • (exp (exponentL P E V.1)*fueled P C' V)) → Real.exp (-(Fintype.card (Site (More n)):ℝ)*(v+γ*(1-Trees.degreePrice P.B γ d)⁻¹)) ≤ Real.exp L:=by
 intro K W T p E Q L i hpQ h; -- fix h shadows real h
 let V:Orbit n:=(1,i); let F(x:Aura n):=K x ∅; let X:= coldE P (FeeD P F) V
 have hf:flags P.threshold V.1=∅:=by
    have hz:= (ping_le (ping_f (G:=SU.group) P (univ:Support (More n)))); change Disjoint univ (flags _ V.1) at hz; exact Finset.eq_empty_iff_forall_notMem.mpr fun i p=> Finset.disjoint_left.mp hz (mem_univ _) p
 have hi : FleetS P.threshold V.1:=fun j=> by change SU.group.chord (faceValue (1:Config SU.group (More n)) j) ≠_; rw [YM.SectorNext.Vacuum.chord_suc]; exact P.threshold_pos.ne
 have hl:exp X=Real.exp L • exp (exponentL P E 1):=by
    let ξ:=(0:Cusp n); let Eν:=budgetR (roomV P F K ξ); have hY:X+fuelV P ξ V=X:=by unfold ξ; rw [prizes0,add_zero]
    have hμ:= asterT (K:=K) T (show 0≤P.supportExponent+1 by linarith [P.exponent_pos]) p (show 0<(1:ℝ) by norm_num) hp V hi X hY -- y' etc
    change hGas _ _ = Real.exp L • (_*fueled P Q V) at h; rw [fuel_one _ Q V hf,mul_one] at h; rw [fuel_one _ _ _ hf, mul_one] at hμ; exact hμ.symm.trans h

 let J:= exponentL P E 1; have hx:= Graph.toeE (x:=1) hpQ (zero_le_one.trans hp)
 have hu:‖X‖ ≤ _:=autumn_full P V K T hp p (by linarith [P.exponent_pos]); rw [pow_zero,mul_one] at hu
 have hE:‖J‖ ≤ Ω*v:= (Pastry.lies hp J).trans (hx.trans_eq (by rw [site_card,mul_comm]; push_cast; rfl)) -- indent tune
 have hg:‖exp X‖=Real.exp L * ‖exp J‖:=by rw [show exp X=Real.exp L • exp J from hl, show ‖Real.exp L • exp J‖ = ‖Real.exp L‖ * ‖exp J‖ from norm_smul (Real.exp L) (exp J).val,Real.norm_of_nonneg (Real.exp_pos _).le]
 have he:= (Real.exp_monotone (neg_le_neg hu)).trans ((expSafe X).trans (le_trans (le_of_eq hg) (mul_le_mul_of_nonneg_left ((expCap J).trans (Real.exp_monotone hE)) (Real.exp_pos L).le)))
 calc
    _ = Real.exp (-(Ω*(γ*(1-Trees.degreePrice P.B γ d)⁻¹))) / Real.exp (Ω*v):=by rw [←Real.exp_sub]; congr 1; ring
    _ ≤ _:= by apply (div_le_iff₀ (Real.exp_pos _)).2 he
end YM.CF.Jade.Earn
