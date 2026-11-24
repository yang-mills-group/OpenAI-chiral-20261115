import YM.CF.Moto.Pin
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Moto
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
open Taxi
open Vow
local notation "G₅"=> SU.group
open Ione
local notation "QZ"=> More n
variable (P) (L:Skate)(Q:InkD n)(Xo:Scree.Hub n)
local notation "o"=> Xo.val.1
local notation "X"=> Xo.val.2
local notation "θ"=> P.threshold
local notation "tX"=> tooth o P
local notation "Uz"=> plateZ o P L
local notation "N"=> (Single n)
variable (w:PressB P Xo Q h c)(he:0≤h)
variable (d'':Taxi.DayT P.order a)(hs: 0 ≤ a)(hX: halo 2 {Xo.val.1}⊆ Xo.val.2) (p:∀ i j,‖L i j‖≤x)
lemma litho (L: Pane n→ℂ)(p:LocalOn X L)(s:GaugeInvariant L)(q:Measurable L)(x:ℝ)(ht:0 ≤x)(u:∀ U,pingS P.threshold X U→ Signs P o (L ∘ increment U) x): PressB P Xo (fun (U:Pane n)=> (hollow (L U) : Cipher n)) h x:=by
 refine ⟨fun i j w=> congrArg _ (p i j w),fun _=> Flour.grainE.smul _,?_,fun i j=>?_,Pi.single ∅ x,fun i=>?_,fun U u' i=>?_,?_⟩ -- tune
 · let K:ℂ→Cipher n:=fun i=> hollow i; exact (Continuous.measurable (f:=K) (Continuous.subtype_mk (continuous_id.smul continuous_const) _)).comp q
 · rw [s]; exact Subtype.ext (Eq.symm ((twist_scalar _ _ _).trans (by rw [map_one]; rfl)))
 · rw [Pi.single_apply]; split_ifs; exact ht; exact le_rfl
 · by_cases j:i=∅; · subst i; rw [Pi.single_eq_same]; apply Prism.mint (u _ u'); exact Eventually.of_forall (fun j=> (hullB _).symm) -- tune .Pane Hess
   rw [Pi.single_eq_of_ne j]; refine Prism.mint (Prism.hail (v:=(0:ℝ)) (show ‖(0:ℂ)‖≤0 by rw [norm_zero])) ?_; exact Eventually.of_forall fun k=>by change (0:ℂ)= ((L _) • (1:FC (LeanV (Single n)))) i ∅; simp [j]
 simp [Pi.single_apply,Scree.tariff,endL,mul_ite] -- simp recursion.
local notation "Θl"=> (a*tollV P x)
abbrev imago (c:ℂ):ℝ→L[ℝ]ℂ:= ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) c
lemma plexF (L:ℂ)(f:PlaqAxes→PlaqAxes→ℝ)(a:ℝ):imago L a=(a:ℂ)* L:= rfl -- tune
include hX d'' hs
-- directional canonical contributions in Ξ
lemma firm_K(f:PlaqAxes→PlaqAxes→ℝ)(p:∀ i j,|f i j| * θ^2 ≤ x)(L:ℝ→L[ℝ]ℂ)(K:ℝ)(w:‖L‖ ≤ K): PressB P Xo (fun V=>hollow (L (counter f o V))) h (K*Θl):=by
 let F:=counter (G:=SU.group) f o; let s:=tollV P x; have hM: AnalyticBridge.VerifiedReset.Bill P o (Healthy θ {o}) s F:=by
    refine AnalyticBridge.VerifiedReset.Bill.le (counter_bill _ f P) ?_; unfold s tollV; refine mul_le_mul_of_nonneg_left ?_ (by norm_num); let K:=x*pairBill SU.group P; have hk:∑ i:PlaqAxes,∑ j:PlaqAxes,K=(Fintype.card PlaqAxes:ℝ)*((Fintype.card PlaqAxes:ℝ)*K):=by simp
    refine (sum_le_sum fun i _=>sum_le_sum fun j _=>?_).trans hk.le; exact (le_of_eq (by rw [mul_comm (pairBill SU.group P), ←mul_assoc])).trans (mul_le_mul_of_nonneg_right (p i j) (pair_nonneg ..))
 have ht(V:Pane n)(p:pingS θ X V):Signs P o ((L∘F) ∘ increment V) (K*Θl):=Prism.skills ((Prism.skin (d'' _ P _ o s F hM rfl V (Finset.disjoint_of_subset_left ((halo_subset 2 _).trans hX) (ping_le p)))).linear L w)
 let A:= reg_larger (G:=SU.group) (counter_regular o f P) hX; exact litho P Xo (L ∘ F) (fun i j p=> congrArg L (A.sites i j p)) (fun i j=>congrArg L (A.symmetry ..)) (L.continuous.measurable.comp A.borel) _ (ht 1 (ping_f P X)).grade ht
omit d'' hs hX
local notation "KR" i:max j:max=> ((L i j).re/θ^2)
local notation "KI" i:max j:max=> ((L i j).im/θ^2)
abbrev trotΦ (P:BudgetPoint)(x a:ℝ):= ‖Complex.ofRealCLM‖*(a*tollV P x) + ‖imago Complex.I‖*(a*tollV P x)
include hX p hs d''
lemma champ : PressB P Xo Uz h (trotΦ P x a):=by
 have he:0 < θ^2:=pow_pos P.threshold_pos _
 have hR:=firm_K (h:=h) P Xo d'' hs hX (fun i j=>KR i j) (fun i j=>by rw [abs_div,abs_of_pos he,div_mul_cancel₀ _ he.ne']; exact (Complex.abs_re_le_norm _).trans (p i j)) Complex.ofRealCLM ‖Complex.ofRealCLM‖ le_rfl
 have hi:=firm_K (h:=h) P Xo d'' hs hX (fun i j=>KI i j) (fun i j=>by rw [abs_div,abs_of_pos he,div_mul_cancel₀ _ he.ne']; exact (Complex.abs_im_le_norm _).trans (p i j)) (imago Complex.I) ‖imago Complex.I‖ le_rfl
 let W := Larch.prop_add P Xo hR hi; have ht:∀ Y' F H, PressB P Xo F h H→F=Y'→ PressB P Xo Y' h H:=fun _ _ _ g v=> v ▸ g
 refine ht _ _ _ W (funext fun U: Pane n=> Subtype.ext ?_); unfold plateZ kerP; rw [Pi.add_apply]; let v:= counter (fun i j=>KI i j) o U
 rw [show imago Complex.I v= _ from plexF Complex.I (fun _ _=>0) v]; exact (add_smul _ _ _).symm
include he
lemma suit_l (u:20 < (More n).val)(s:Verc L): lifeH Uz 1=0∧ tX Uz=L:=by
 have hk(V:Pane n): lifeH Uz V=kerP o P L V:=hullB _
 let pR:=fun i j=>KR i j; let pI:=fun i j=>KI i j; have hR:Complex.reCLM ∘ lifeH Uz=counter (G:=SU.group) pR o:=funext fun i=> by unfold Function.comp; rw [hk]; simp [kerP,pR]
 have hI:Complex.imCLM ∘ lifeH Uz=counter (G:=SU.group) pI o:=funext fun i=> by unfold Function.comp; rw [hk]; simp [kerP,pI] -- layout!
 refine ⟨by rw [hk]; simp [kerP,counter,AnalyticBridge.VerifiedReset.quad],?_⟩; funext i j; apply Complex.ext
 · change Complex.reCLM (tooth o P _ _ _)=_; rw [cym P Uz Xo (champ P L Xo d'' hs hX p) he,hR,yew P o pR i j u]; unfold pR; rw [s j]; have ht:=P.threshold_pos; field_simp; ring
 · change Complex.imCLM (tooth o P _ _ _)=_; rw [cym P Uz Xo (champ P L Xo d'' hs hX p) he,hI,yew P o pI i j u]; unfold pI; rw [s j]; have ht:=P.threshold_pos; field_simp; ring
end YM.CF.Moto
