import YM.CF.Taxi.Rack
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
local notation "Q"=> (T X0)
local notation "N"=> (Single n)
local notation "G"=> SU.group
local notation "Xr"=> X0.val.2
local notation "o"=> X0.val.1
def bankT (T:RegBudget n)(X:Scree.Hub n):InkD n:= fun U=> hollow (↑(payout X (realH T X) U))
variable (g:∀ X,PressB P X (T X) h (U' X))(hw:0 ≤h)
-- NORMALIZATION REAL pressure anchor.F moments. does not handle missing PF slip $calibrating phase gamma.G Round.
abbrev porch (T:RegBudget n)(X:Scree.Hub n): InkD n:=fun U=> hollow (lifeH (T X) 1) -- remove unused
variable {ε:ℝ}
include g hw
private lemma litho (L: Pane n→ℂ)(p:LocalOn Xr L)(s:GaugeInvariant L)(q:Measurable L)(x:ℝ)(ht:0 ≤x)(u:∀ U,pingS P.threshold Xr U→ Signs P o (L ∘ increment U) x): PressB P X0 (fun (U:Pane n)=> (hollow (L U) : Cipher n)) h x:=by
 refine ⟨fun i j w=> congrArg _ (p i j w),fun _=> Flour.grainE.smul _,?_,fun i j=>?_,Pi.single ∅ x,fun i=>?_,fun U u' i=>?_,?_⟩ -- tune
 · let K:ℂ→Cipher n:=fun i=> hollow i; exact (Continuous.measurable (f:=K) (Continuous.subtype_mk (continuous_id.smul continuous_const) _)).comp q
 · rw [s]; exact Subtype.ext (Eq.symm ((twist_scalar _ _ _).trans (by rw [map_one]; rfl)))
 · rw [Pi.single_apply]; split_ifs; exact ht; exact le_rfl
 · by_cases j:i=∅; · subst i; rw [Pi.single_eq_same]; apply Prism.mint (u _ u'); exact Eventually.of_forall (fun j=> (hullB _).symm) -- tune .Pane Hess
   rw [Pi.single_eq_of_ne j]; refine Prism.mint (Prism.hail (v:=(0:ℝ)) (show ‖(0:ℂ)‖≤0 by rw [norm_zero])) ?_; exact Eventually.of_forall fun k=>by change (0:ℂ)= ((L _) • (1:FC (LeanV (Single n)))) i ∅; simp [j]
 simp [Pi.single_apply,Scree.tariff,endL,mul_ite] -- simp recursion.
variable(hA:DayT P.order a)(ha:0≤a)
include hA ha
abbrev uprank (P:BudgetPoint)(X:ℝ)(v:ℝ) := ‖Complex.ofRealCLM‖ * (priceV P X*(‖Complex.reCLM‖*v))
lemma vigor : PressB P (stateT X0) (bankT T X0) h (uprank P a (U' X0)):=by
 let W:= pigment X0 (cashR _ X0 (g _) hw Complex.reCLM ‖Complex.reCLM‖ le_rfl) ha hA; let L:=payout X0 (realH T X0); let T':= stateT X0; let V:= uprank P a (U' X0); have hz(U:Pane n)(u:pingS P.threshold T'.val.2 U): Signs P T'.val.1 ((Complex.ofRealCLM ∘ L) ∘ increment U) V:=Prism.skills ((Prism.skin (W.toll U u)).linear _ le_rfl); have hp:= (hz 1 (ping_f _ T'.val.2)).grade; let h:=W.regular; apply litho (L:=Complex.ofRealCLM ∘ L) T T' g hw (fun i j p=> congrArg Complex.ofReal (h.sites _ _ p)) (fun i j=>congrArg Complex.ofReal (h.symmetry _ _)) (Complex.ofRealCLM.continuous.measurable.comp h.borel) V hp hz -- tune args
omit hA ha
lemma pureP :PressB P X0 (porch T X0) h (U' X0):=by
 have h := (eraF (T X0) X0 (g X0) hw 1 (ping_f P Xr)); have hp: ‖lifeH (T X0) (1:Pane n)‖ ≤ U' X0:=by
    have hv:= h.token 0 (by omega) 0 (fun i=> by exact i.elim0); rw [iteratedFDeriv_zero_apply] at hv; simpa only [Function.comp_apply,Work.G07.at_zero_increment] using hv
 exact litho T X0 g hw (L:=fun _=>lifeH (T X0) 1) (fun _ _ _=> rfl) (fun _ _=>rfl) measurable_const (U' X0) h.grade fun _ _=> Prism.hail hp
lemma strike {F F':InkD n}(p:PressB P X0 F h a)(u:PressB P X0 F' h b):PressB P X0 (F-F') h (a+b):=by
 obtain ⟨A,e,r,x⟩:=p.worth; obtain ⟨B,v,q,y⟩:=u.worth
 refine ⟨fun X Y h=> congrArg₂ (·-·) (p.term X Y h) (u.term X Y h), fun i=>?_,p.measureV.sub u.measureV,fun i j=>(congrArg₂ (·-·) (p.gaugeV _ j) (u.gaugeV i j)).trans (map_sub ..).symm, A+B,fun i=>add_nonneg (e i) (v i),fun i k t=> ?_,by simp only [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add x y⟩
 · exact (stretch_ok _).mp ((stretch (camp Xr)).sub_mem ((stretch_ok _).mpr (p.fitted _)) ((stretch_ok _).mpr (u.fitted i))) -- tune
 have ht:= Prism.tack  (r i k t) (Prism.skills (A:=fun x:tangD n=> (-1:ℝ) • crumb (F' (increment i x)).val t) (((Prism.skin (q i k t)).smul (-1)))); simp only [abs_neg,abs_one,one_mul,neg_one_smul,←sub_eq_add_neg] at ht
 exact ht -- tune ht comp trunk.H
lemma farther_v (Y:Scree.Hub n){s:PressB P X0 F h a} (u:Xr⊆ Y.val.2)(v:o=Y.val.1): PressB P Y F h a:=by
 obtain ⟨x,f,m,b,V,t,h,l⟩:=s; exact ⟨fun _ _ t=> x _ _ (agrees_mono t (Finset.coe_subset.mpr u)),fun i=>(f i).lift (fun i v=> mem_filter.mpr ⟨mem_univ _,u (mem_filter.mp v).2⟩),m,b,V,t,fun i p=> (by specialize h i (grow_b u p); rw [v] at h; exact h), (by rw [←v]; exact l)⟩ -- h notation
abbrev mowR (T:RegBudget n)(X:Scree.Hub n): InkD n:=T X - porch T X-bankT T X
abbrev inS (P:BudgetPoint)(C:ℝ):=2+uprank P C 1
include ha hA
lemma crescent :PressB P (stateT X0) (mowR T X0) h (inS P a* U' X0):=by
 let D:=U' X0; unfold mowR
 let V':= farther_v T (Q-porch T X0) X0 g hw (stateT X0) (s:=strike T X0 g hw (g _) (pureP T X0 g hw)) (show Xr⊆villa X0 from Finset.subset_union_left) rfl
 rw [show inS P a*U' X0=U' X0+U' X0+uprank P a (U' X0) from by unfold inS uprank; ring]
 exact strike T (stateT X0) g hw V' (vigor T X0 g hw hA ha)
end YM.CF.Taxi
