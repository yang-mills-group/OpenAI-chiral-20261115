import YM.CF.Ups.Tot
import YM.CF.Ups.Gala
set_option autoImplicit false
set_option maxHeartbeats 980000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Jade
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
def era_v (n:Side)(δ:ℝ):ℝ:=Fintype.card (Scree.Hub n)*δ
lemma tax_G (s:Skye.Seat n)(D:Finset (Dwell n))(h:ℝ)(hp:1≤h): 1≤Scree.tariff P s h D:=by unfold Scree.tariff; exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))) (one_le_pow₀ hp)
lemma debt_E (s:RegBudget n)(H:Sweep n→Prop)(δ h:ℝ)(p:IncX H s P h δ)(hp:1≤h)(V:Pane n): ‖exponentL P s V‖ ≤ era_v n δ:=by
 obtain ⟨F,g,x⟩:=p.weight; choose b G v e using fun i=> (g i).worth; have he(i:Scree.Hub n):(∑ j,b i j)≤ F i:= (sum_le_sum fun j _=>le_mul_of_one_le_left (G i j) (tax_G P i.val.1 j h hp)).trans (e i)
 have hh(i):0 ≤ F i:=(sum_nonneg fun j _=>G i j).trans (he i)
 have hx(i:Scree.Hub n): F i ≤ δ:=by
    refine (P.loMass i.val.2 _ (hh i)).trans (le_trans ?_ (x i.val.1)); simpa only [↓reduceIte] using (single_le_sum (f:=fun j:Scree.Hub n=> if i.val.1=j.val.1 then P.mass j.val.2 (F j) else 0) (fun j _=>by split; exact mul_nonneg (Real.exp_pos _).le (hh _); exact le_rfl) (mem_univ i)) -- cast exponent support implicit
 apply (norm_sum_le ..).trans; unfold era_v; apply (le_trans _ (show (∑ i:Scree.Hub n,δ)=_ from by simp).le); refine sum_le_sum fun i _=>?_; unfold numbE; by_cases p:pingS P.threshold i.val.2 V
 · rw [Set.indicator_of_mem (show V∈ _ from p)]; exact (Girt.trust _ _ _ _ _ (ping_le p) (v i _ p)).trans ((he i).trans (hx i))
 rw [Set.indicator_of_notMem (show V∉ _ from p),norm_zero]; exact (hh i).trans (hx i)
lemma autumn_X (V:Orbit n)(K:Cusp n){H a δ γ w:ℝ}{v:Aura n→ℝ}(W: Trees.Ready Palot.stern P.B v a γ δ w)(h:1 ≤ H)(t:∀ i:Aura n,Vow.Medal P i.val ∅ (K i ∅) H (v i))(u:0 ≤ a) : ‖coldE P (FeeD P (fun i=>K i ∅)) V‖≤ Fintype.card (Aura n)*(γ*w^0*(1-w)⁻¹):=by
 let p':= γ*w^0*(1-w)⁻¹; have hw':0 ≤ p':=by unfold p'; have z:=W.1; have hp:=sub_pos.mpr W.2.2.2.1; positivity
 have ht(i:Aura n):= glenP i h t W u 0; have hh(i:Aura n):0≤ spanD i v 0:= (ht i).wage (zero_le_one.trans h); have hg(X:Aura n):spanD X v 0≤ p':=by
    obtain ⟨i,p⟩:=X.property; exact ((le_mul_of_one_le_right (hh X) (show 1 ≤ Trees.currency P.B a X.val from Real.one_le_exp (mul_nonneg u (by positivity)))).trans (single_le_sum (s:= univ.filter fun x:Aura n=> i∈x.val) (f:=fun x:Aura n=>spanD x v 0 * Trees.currency P.B a x.val) (fun j _=>mul_nonneg (hh j) (Real.exp_pos _).le) (mem_filter.mpr ⟨mem_univ _,p⟩))).trans (thinX W u i _)
 apply (norm_sum_le ..).trans -- might target.Mt.Fp
 rw [sum_filter]; apply le_trans _ (show (∑ j:Aura n,p')=_ from by simp [p']).le; refine sum_le_sum fun j _=>?_ ; split; next p=> exact ((ht j).capF h V (by rw [sdiff_empty]; exact p)).trans (hg j)
 exact hw'
lemma cap_exp(n:Side)(u:ℝ): ∃ d:ℝ,0 < d∧ ∀ Z: Cipher n, ‖Z‖ ≤ u → d≤ ‖NormedSpace.exp Z‖ ∧ ‖NormedSpace.exp Z‖ ≤ d⁻¹:=by
 let w:=max 0 u; let s:= Metric.closedBall (0: Cipher n) w; have he: s.Nonempty:=⟨0,Metric.mem_closedBall_self (le_max_left ..)⟩
 letI: NormedAlgebra ℚ (Cipher n):=NormedAlgebra.restrictScalars ℚ ℝ _
 let f(Z:Cipher n):= ‖exp Z‖; have hz:Continuous f:=exp_continuous.norm; have hg(Z):0 < f Z:=norm_pos_iff.mpr fun p=>by have he:= exp_zero (𝔸:=Cipher n); rw [←add_neg_cancel Z, exp_add,show exp Z = 0 from p,zero_mul] at he; exact zero_ne_one he
 obtain ⟨Y,hY,i⟩:= (isCompact_closedBall (0:Cipher n) w).exists_isMaxOn he hz.continuousOn; obtain ⟨X,hX,j⟩:= (isCompact_closedBall (0: Cipher n) w).exists_isMinOn he hz.continuousOn; let u:= min (f X) (f Y)⁻¹; have ht:0<u:=lt_min (hg _) (inv_pos.mpr (hg _))
 refine ⟨u,ht,fun Z v=>?_⟩; have hZ:Z∈s:=mem_closedBall_zero_iff.mpr (v.trans (le_max_right ..)); exact ⟨(min_le_left ..).trans (j hZ),(i hZ).trans ((inv_inv (f Y)) ▸ inv_anti₀ ht (min_le_right ..))⟩ -- tune shadow p0
-- use generic assembly cap_exp. Supplier hZ.
lemma bulge_M (S:ℕ)(d γ h v:ℝ)(hp:1 ≤ h):∃ C:ℝ,0 < C∧∀ (K:Cusp n)(W:Aura n→ℝ), Trees.Ready Palot.stern P.B W (P.supportExponent+1+1) γ d (Trees.degreePrice P.B γ d) → (∀ i:Aura n,Vow.Medal P i.val ∅ (K i ∅) h (W i)) →∀ (E: RegBudget n)(C':ForceBudget n)(L:ℝ)(T:Ids n),IncX Ione.Utrue E P h v → (let V:Orbit n:=(1,T); Palot.hGas (flags P.threshold V.1) (keyL P K (fun i=>K i ∅) V) = Real.exp L • (exp (exponentL P E V.1)*fueled P C' V)) → C ≤ Real.exp L:=by
 let w:= Trees.degreePrice P.B γ d; let q:=Fintype.card (Aura n)*(γ*w^0*(1-w)⁻¹); obtain ⟨x,u,hx⟩:=cap_exp n q; obtain ⟨c,hc,hQ⟩:= cap_exp n (era_v n v); refine ⟨x/c⁻¹,by positivity,?_⟩
 intro K W T p E Q L i hpQ h; -- fix h shadows real h
 let V:Orbit n:=(1,i); let F(x:Aura n):=K x ∅; let X:= coldE P (FeeD P F) V
 have hf:flags P.threshold V.1=∅:=by
    have hz:= (ping_le (ping_f (G:=SU.group) P (univ:Support (More n)))); change Disjoint univ (flags _ V.1) at hz; exact Finset.eq_empty_iff_forall_notMem.mpr fun i p=> Finset.disjoint_left.mp hz (mem_univ _) p
 have hi : FleetS P.threshold V.1:=fun j=> by change SU.group.chord (faceValue (1:Config SU.group (More n)) j) ≠_; rw [YM.SectorNext.Vacuum.chord_suc]; exact P.threshold_pos.ne
 have hl:exp X=Real.exp L • exp (exponentL P E 1):=by
    let ξ:=(0:Cusp n); let Eν:=budgetR (roomV P F K ξ); have hY:X+fuelV P ξ V=X:=by unfold ξ; rw [prizes0,add_zero]
    have hμ:= asterT (K:=K) T (show 0≤P.supportExponent+1 by linarith [P.exponent_pos]) p (show 0<(1:ℝ) by norm_num) hp V hi X hY -- y' etc
    change hGas _ _ = Real.exp L • (_*fueled P Q V) at h; rw [fuel_one _ Q V hf,mul_one] at h; rw [fuel_one _ _ _ hf, mul_one] at hμ; exact hμ.symm.trans h
 apply (div_le_iff₀ (inv_pos.mpr hc)).2; apply (hx X (autumn_X P V K T hp p (by linarith [P.exponent_pos]))).1.trans; rw [hl, show ‖Real.exp L • exp (exponentL P E (1:Pane n))‖ = ‖Real.exp L‖ * ‖exp (exponentL P E 1)‖ from norm_smul (Real.exp L) (exp (exponentL P E 1)).val,Real.norm_of_nonneg (Real.exp_pos ..|>.le)]; exact mul_le_mul_of_nonneg_left (hQ _ (debt_E P E _ _ _ hpQ hp _)).2 (Real.exp_pos _).le
end YM.CF.Jade
