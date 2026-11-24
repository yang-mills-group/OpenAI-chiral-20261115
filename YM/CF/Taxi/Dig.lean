import YM.CF.Taxi.Talk
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations StressFlux AnalyticBridge.VerifiedReset Push.Local
open Vow
variable(T:RegBudget n)(F:InkD n)(X0: Scree.Hub n){U':Scree.Hub n→ℝ}
variable (p: Pant T)
local notation "Tx"=> (T X0)
local notation "N"=> (Single n)
local notation "G"=> SU.group
local notation "Xr"=> X0.val.2
local notation "OpH"=> X0.val.1
variable(g:∀ X,PressB P X (T X) h (U' X))(hw:0≤h)(A:DayT P.order a)(ha:0 ≤a)
-- alpha trajectory updates $Z=eBeta virtual`.
variable(hn:60 < (More n).val)
include p g hw A ha hn
lemma rootB(q:Nonwrapping (villa X0) OpH): Siete.Acceptance P (villa X0) OpH (lifeH (mowR T X0)) (inS P a*U' X0):=by
 let L:= stateT X0; let U:= U' X0
 let K:= crescent T X0 g hw A ha; let f:= realH T X0; let y:=mowR T X0; let b(i:tangD n):= lifeH y (increment 1 i); let θ:=payout X0 (realH T X0)
 have hp(W:Pane n) : lifeH y W= (lifeH Tx W-lifeH Tx 1)-Complex.ofRealCLM (θ W):=by
    unfold y lifeH; change panHom (Dwell n) (Tx W-porch T X0 W-bankT T X0 W)=_; rw [map_sub,map_sub]; change Pastry.pane _ - Pastry.pane _ - Pastry.pane _=_; rw [porch,bankT,hullB,hullB]; rfl-- tune
 have hv:payout X0 (realH T X0) (1:Pane n)=0:=by unfold payout; rw [Finset.sum_apply]; simp [fuelC,counter,AnalyticBridge.VerifiedReset.quad,AnalyticBridge.VerifiedReset.petals_one] -- recursion note big.
 refine ⟨fun V u=> eraF y L K hw V u,L.property,(by change lifeH y _=_; rw [hp,show θ _= _ from hv]; simp),fun x z u v=>?_ ,fun i j p=> congrArg Pastry.pane (K.term i j p), fun x y=> Eq.trans (congrArg Pastry.pane (K.gaugeV _ _)) (Pastry.center_b ..), ?_ ⟩ -- hv typo
 · have hP:= (eraF _ L K hw _ (ping_f P L.val.2)).paid; have ht:ContDiffAt ℝ 2 b 0:=(show ContDiffAt ℝ (P.order:WithTop ℕ∞) b 0 from hP).of_le (show (2:WithTop ℕ∞) ≤ P.order from by exact_mod_cast ((by norm_num : 2 ≤ 6).trans P.order_ge))
   let U:= ![x,z]; change iteratedFDeriv ℝ 2 b 0 _= _; apply Complex.ext
   · let t:=cashR _ X0 (g X0) hw Complex.reCLM ‖Complex.reCLM‖ le_rfl; change Complex.reCLM (iteratedFDeriv ℝ 2 b 0 U)=(0:ℝ); rw [←show iteratedFDeriv ℝ 2 (Complex.reCLM ∘ b) 0 U= Complex.reCLM (iteratedFDeriv ℝ 2 b 0 U) from (by rw [Complex.reCLM.iteratedFDeriv_comp_left (i:=2) ht (by norm_num : ((2:ℕ):WithTop ℕ∞)≤2)]; rfl)] -- norm_cast
     let H:Pane n→ℝ:=f-θ; rw [show Complex.reCLM ∘ b=AnalyticBridge.VerifiedReset.germ (H-(fun _=>f 1)) from funext fun i=>?_]; swap; · unfold b; simp only [hp, Function.comp_apply,map_sub]; change _-_ - θ _ = (f _ - θ _) - f _; unfold f realH; simp only [Function.comp_apply]; abel -- tune
     change logHessian _ _ _ = 0; let H0:= t.regular; have hr := AnalyticBridge.VerifiedReset.reg_sub (AnalyticBridge.VerifiedReset.reg_larger H0 (show Xr⊆villa X0 from Finset.subset_union_left)) (rent (P:=pintK P) X0 (F:=f) univ)
     rw [hessian_sub (show (pintK P).Regular (villa X0) H from hr) (reg_const _), hessian_zero,sub_zero]; exact zeroQ X0 t hn q x z u v
   let t:= cashR _ X0 (g X0) hw Complex.imCLM ‖Complex.imCLM‖ le_rfl; let F:= magi T X0; change Complex.imCLM (iteratedFDeriv ℝ 2 b 0 U)= (0:ℝ)
   rw [←show iteratedFDeriv ℝ 2 (Complex.imCLM ∘ b) 0 U= Complex.imCLM (iteratedFDeriv ℝ 2 b 0 U) from (by rw [Complex.imCLM.iteratedFDeriv_comp_left (i:=2) ht (by norm_num : ((2:ℕ):WithTop ℕ∞)≤2)]; rfl),show Complex.imCLM ∘ b=AnalyticBridge.VerifiedReset.germ (F- fun _ => F 1) from ?_]; swap; · funext i; unfold b; simp only [hp,Function.comp_apply,map_sub]; change _-_- 0=F _- F _; rw [sub_zero]; rfl
   change logHessian _ _ _= 0; rw [hessian_sub (show (pintK P).Regular Xr F from t.regular) (reg_const _),hessian_zero,sub_zero]; have he:=zeroQ X0 t hn q x z u v; let S:=fluxP X0 F; have hr: payout X0 F=0:=by
      have ht:S=0:= pureK T X0 p hw g -- tune
      unfold payout fuelC; rw [show fluxP _ _ = 0 from ht]; funext V; simp [counter,AnalyticBridge.VerifiedReset.quad]; -- tune zero function
   rw [show payout X0 _= _ from hr,sub_zero] at he; exact he
 exact ((show Continuous (Pastry.pane (n:=LeanV (Single n))) from mast_cont.comp (g:=mast (n:=LeanV (Single n))) continuous_subtype_val).measurable.comp K.measureV)
omit A ha
lemma cash_b (B:ℝ)(b:∀ i:Site (More n),(∑ X:Scree.Hub n with X.val.1=i,U' X)≤ B) : let L:= lureC (realH T); P.threshold^2 * |L| ≤ ‖Complex.reCLM‖ * B:=by
 let S(X:Scree.Hub n):=cashR (T X) X (g X) hw Complex.reCLM ‖Complex.reCLM‖ le_rfl; intro L; let q:= AnalyticBridge.VerifiedReset.Averaging.axes01
 let v := realH T; have he := era T p; let D(i:Site (More n)):=∑ X:Scree.Hub n, motto X.val.1 i * U' X; have hp(o: Site (More n)):P.threshold^2 * |L| ≤ ‖Complex.reCLM‖ * D o:=by
    have he:payoutF v o q q=L:= (betaK v he S hn o q q).trans (if_pos rfl); rw [←he]; unfold payoutF; apply le_trans (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs ..) (sq_nonneg _)); unfold D; rw [Finset.mul_sum, Finset.mul_sum]; apply sum_le_sum; intro i _; rw [abs_mul,abs_of_nonneg (mot_l ..), mul_left_comm]; exact (mul_le_mul_of_nonneg_left (payC i (S i) q q) (mot_l ..)).trans_eq (mul_left_comm ..)
 let N':=Site (More n); let R:ℝ:=Fintype.card N'; apply le_of_mul_le_mul_left (a:=R) _ (Nat.cast_pos.mpr Fintype.card_pos); let A:ℝ:= P.threshold^2* |L|
 calc
    R*A = ∑ o':N',A:=by simp [R]
    _ ≤ ∑ o':N', ‖Complex.reCLM‖ * D o':= sum_le_sum fun i _=> hp i
    _ = ‖Complex.reCLM‖ * ∑ X:Scree.Hub n,U' X := by rw [← Finset.mul_sum]; unfold D; apply congrArg; rw [sum_comm]; refine sum_congr rfl fun i t=>?_ ; change (∑ o:Site (More n),motto i.val.1 o * U' i)=U' i; rw [← Finset.sum_mul,mot_b,one_mul]
    _ ≤ ‖Complex.reCLM‖ * ∑ i: N', B:= mul_le_mul_of_nonneg_left (by rw [←sum_fiberwise _ (fun i:Scree.Hub n=> i.val.1)]; exact sum_le_sum (fun i _=>b i)) (norm_nonneg _)
    _ = _ := by simp [R] -- tune holes
 -- lean goal
end YM.CF.Taxi
