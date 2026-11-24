import GaugeFieldConstruction.Moire
import GaugeFieldConstruction.Berylla
import GaugeFieldConstruction.Ablated
import GaugeFieldConstruction.Pendant
import YM.CF.Hove.Hood
import GaugeFieldConstruction.Butane
import GaugeFieldConstruction.Vuoto
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
open Prism Haro Tap
section
open Tap Haro Prism SU
open FlightFlux TableF Boom Axon Flot Taxi
open AnalyticBridge.VerifiedReset
open Lenten.Bank Lenten.ModuleB Lenten
-- pure pull.LP
section
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
def Shorten (r:ℕ): Ole E F → Ole E F
 | (x,y,z)=> (x,(if 1 ≤ r then y else 0),if 2 ≤ r then z else 0)
lemma Short_sub (r:ℕ)(x y:Ole E F) :Shorten r (x-y)= Shorten r x-Shorten r y:=by
 rcases x with ⟨x,y,z⟩ -- shadow
 unfold Shorten; split_ifs <;> apply Prod.ext <;> first|rfl|apply Prod.ext <;> first| rfl| exact (sub_zero (0:Lenten.Bank.Duo E F)).symm|exact (sub_zero (0: OneF E F)).symm
lemma Short_add (r:ℕ)(x y:Ole E F): Shorten r (x+y) = Shorten r x + Shorten r y:=by
 unfold Shorten; split_ifs <;> apply Prod.ext <;> first|rfl|apply Prod.ext <;> first| rfl | exact (add_zero 0).symm
lemma Short_s (r:ℕ)(a:ℝ)(x:Ole E F):Shorten r (a • x)=a • Shorten r x:=by unfold Shorten; split_ifs <;> apply Prod.ext <;> first|rfl|apply Prod.ext <;> first|rfl|exact (smul_zero a).symm
lemma Short_N (r:ℕ)(x:Ole E F): CostOle (Shorten r x)≤ CostOle x:=by
 have ht: CostOle x ≥ 0:=Ole_non _; unfold Shorten; split_ifs <;> refine max_le (le_max_left ..) (max_le ?_ ?_) <;> first | exact le_trans (le_max_right ..) (le_max_right ..) | exact le_trans (le_max_left ..) (le_max_right ..) | exact (@norm_zero (OneF E F) _).le.trans ht|exact (@norm_zero (Lenten.Bank.Duo E F) _).le.trans ht
end
variable {K U:PalOne}
lemma Short_X (r:ℕ)(v:r ≤2)(p:∀ i≤r,∀ x:Views, PartT K i x= PartT U i x):Shorten r K=Shorten r U:=by
 apply Prod.ext; · exact p 0 (by omega) 0
 apply Prod.ext
 · unfold Shorten; dsimp only; split; next h=> exact ContinuousLinearMap.ext fun i=>p 1 h i
   rfl
 unfold Shorten; dsimp only; split; next h=> exact dual_uni _ _ (fun i=>p 2 h i)
 rfl
lemma ShortThick (r:ℕ)(v:r ≤ 2)(α:Side)(p:∀ i≤r,∀ x:Views, PartT K i x=αN α ^(3+i) • PartT U i x)(h:KappaF r U): Shorten r K= Shorten r (αN α ^(3+r) • U):=by -- quote_B type
 apply Short_X _ v; intro i h0 x; rw [p i h0]; rcases eq_or_lt_of_le h0 with rfl|h0
 · interval_cases i <;>rfl
 have h: PartT U i x=0:=by
    rcases show i=0∨i=1 by omega with e|e
    · subst i; exact h.u (by omega)
    subst i; change U.2.1 x=0; rw [h.v (by omega)]; rfl
 rw [show PartT (_ • _) i x=αN α ^(3+r) • PartT U i x from ?_,h,smul_zero,smul_zero]; have hv:i≤1:=by omega
 interval_cases i <;>rfl
variable {N:Side}
def tagLine(M:Tulip.Male)(p:BudgetPoint)(h:ℝ)(o:Skye.Seat N)(r:ℕ): Op (Single N) →L[ℝ] PalOne:=by
 let F:Op (Single N)→ₗ[ℝ]PalOne:={
    toFun := fun X=> Shorten r (winJ o M h X)
    map_add' := fun i j=>by rw [winP_add,Short_add]
    map_smul' := fun i j=>by rw [winP_scale,Short_s]; rfl } -- tune
 exact LinearMap.toContinuousLinearMap (𝕜:=ℝ) (E:=Op (Single N)) (F':=PalOne) F
-- *explicit tests Probe.Gem directions with Toll. Result Dock.Prop.*
abbrev TirB (N:Side): Type:= tangD N→ FC (LeanV (Single N))
abbrev captain {N:Side}(X:TirB N)(J:Finset (Dwell N))(w:tangD N):= crumb (X w) J
abbrev siphon (X:TirB N)(t:tangD N):Op (Single N):= Matrix.of fun i j=> winsock i j (X t)
abbrev Charter(N:Side)(P:TirB N):Prop:=∀ J:Finset (LeanV (Single N)),ContDiffAt ℝ (6:ℕ∞ω) (captain P J) 0
lemma siphon_C (X:TirB N)(t:Charter N X):ContDiffAt ℝ (6:ℕ∞ω) (siphon X) 0:=by
 let K:=Nacre.coordL (k:=Single N); let Cx(i j:Single N):= Fock.parity ((true,i):LeanV (Single N)) {(false,j)}
 have hp: ContDiffAt ℝ (6:ℕ∞ω) (K∘ siphon X) 0:=by
    apply contDiffAt_pi.mpr; intro i; apply contDiffAt_pi.mpr; intro j; change ContDiffAt ℝ _ (fun y=>K (siphon X y) i j) 0
    rw [show (fun y=> K (siphon X y) i j)=fun y=> Cx i j * captain X (tray i j) y from ?_]; exact contDiffAt_const.mul (t _) -- tune
    funext y; change Prism.portB _ _ _=_; rw [Prism.port_eq,if_neg]; simp
 simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using K.symm.contDiff.contDiffAt.comp 0 hp
-- abstract detector equivalence OF.Fin. Precedes `MetaB`.
abbrev deskC (p:BudgetPoint)(x:ℕ)(o:Skye.Seat N)(V:Support (More N))(A:ComG):= Manor p o V x (gateC o p.threshold A)
abbrev deskT (p:BudgetPoint)(x:ℕ)(o:Skye.Seat N)(V:Support (More N))(A:ComT):= Manor p o V x (gateT o p.threshold A)
abbrev Tall (o:Skye.Seat N)(p:BudgetPoint)(m:ℕ)(r:ℕ)(X:TirB N)(M:Male)(h:ℝ):= tagLine M p h o r (siphon X 0)
abbrev Desk4 (o:Skye.Seat N)(p:BudgetPoint)(V:Support (More N))(m:ℕ)(X:TirB N)(A B:ComG):ℂ:= iteratedFDeriv ℝ 2 (captain X ∅) 0 ![deskC p m o V A,deskC p m o V B]
abbrev Desk5 (o:Skye.Seat N)(p:BudgetPoint)(V:Support (More N))(m:ℕ)(X:TirB N)(A:ComG)(B:ComT):ℂ:= iteratedFDeriv ℝ 2 (captain X ∅) 0 ![deskC p m o V A,deskT p m o V B]
abbrev SiphonT (o:Skye.Seat N)(p:BudgetPoint)(V:Support (More N))(m:ℕ)(X:TirB N)(M:Tulip.Male)(h:ℝ)(a:ComG):= (αxp M o h) (fderiv ℝ (siphon X) 0 (deskC p m o V a))
-- Prop.Direct Probe.DEFs functionals.Domain bonds finite. 
variable (A: ℝ)
structure BookTarget where -- stores arbitrary answers.All need linear on them
  S:PalOne
  v:ComG→ ComG→ℂ
  l:ComG→ ComT→ℂ
  p:ComG→Pal
abbrev book_zero: BookTarget := ⟨0,fun _ _ =>0,fun _ _=>0,fun _=>0⟩
abbrev HeadX (k:ℕ)(ι:TirB N)(p:BudgetPoint)(o:Skye.Seat N)(V: Support (More N))(M:Tulip.Male)(h:ℝ)(n:ℕ)(T:BookTarget)(C:ℝ):Prop:= CostOle (Tall o p n k ι M h - T.S) ≤ C ∧ (1 ≤ k → ∀ i j:ComG,‖i‖≤1/50→ ‖j‖≤1/50→ ‖Desk4 o p V n ι i j-T.v i j‖≤ C) ∧ (2≤k→∀ i:ComG,‖i‖≤1/50→ ( (∀ j:ComT,‖j‖≤1/50→ ‖Desk5 o p V n ι i j-T.l i j‖≤ C) ∧ ‖SiphonT o p V n ι M h i-T.p i‖≤ C))
-- contributions from Charter. sites. Gauge irrelevant here. BookTarget.
end
end YM.CF.Oath
end
