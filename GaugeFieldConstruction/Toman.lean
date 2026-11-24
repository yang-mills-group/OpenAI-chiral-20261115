import GaugeFieldConstruction.Cortile
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
open SU FlightFlux TableF Boom Axon Flot Taxi Tap
open Lenten.Bank Lenten.ModuleB Lenten
variable {N:Side}{X Y:TirB N}{T:BookTarget}{p:BudgetPoint}{o:Skye.Seat N}{U:Support (More N)}{M:Tulip.Male}{h c d:ℝ}{n m:ℕ}
-- charter calculus of detectors, real scalar closure
lemma captain_Z (p:LeanV (Single N)) (T:Finset (LeanV (Single N))) :captain (0:TirB N) T=0:=rfl
lemma captain_add (K H:TirB N)(J:Finset (Dwell N)):captain (K+H) J= captain K J+captain H J:=rfl
lemma captain_neg (K:TirB N)(J:Finset (Dwell N)): captain (-K) J = -captain K J:=rfl
lemma Charter.add (x:Charter N X)(y:Charter N Y):Charter N (X+Y):=by intro i; rw [captain_add]; exact (x i).add (y i)
lemma Charter.zero:Charter N 0:=fun _=> contDiffAt_const (c:=(0:ℂ))
lemma Charter.diff (x:Charter N X)(y:Charter N Y):Charter N (X-Y):=by rw [sub_eq_add_neg]; apply x.add; intro i; rw [captain_neg]; exact (y i).neg
lemma Charter.germ (x:Charter N X)(h:X=ᶠ[𝓝 0] Y): Charter N Y:=by intro i; refine (x i).congr_of_eventuallyEq (h.mono (fun v p=> (congrArg (fun x=> crumb x i) p.symm))) -- tune
lemma siphon_Z : siphon (0:TirB N)=0:=by funext i; ext j k; rw [siphon,Matrix.of_apply]; unfold winsock; rw [Prism.port_eq]; simp [crumb] -- tune
lemma siphon_add (H K:TirB N) : siphon (H+K)=siphon H+siphon K:= by funext i; ext j k; change Prism.portB _ _ _=_+_; rw [show (H+K) i=H i+K i from rfl]; unfold Prism.portB; rw [act_add,inner_add_right]; rfl
lemma siphon_germ (p:X=ᶠ[𝓝 0] Y):siphon X=ᶠ[𝓝 0]siphon Y:=by filter_upwards [p] with i p; unfold siphon; rw [p]
lemma HeadX.rise (p₀:HeadX m X p o U M h n T c)(e:c≤d): HeadX m X p o U M h n T d:=⟨p₀.1.trans e,fun a b v i j=>(p₀.2.1 a b v i j).trans e,fun a b i=>⟨fun t h=> ((p₀.2.2 a b i).1 t h).trans e,((p₀.2.2 a b i).2).trans e⟩⟩
lemma HeadX.germ (p₀:HeadX m X p o U M h n T c)(e:X=ᶠ[𝓝 0] Y):HeadX m Y p o U M h n T c:=by
 have he(i): captain X i=ᶠ[𝓝 0]captain Y i:= e.mono fun v p=> congrArg (fun t=> crumb t i) p; unfold HeadX Tall SiphonT Desk4 Desk5; rw [←(EventuallyEq.iteratedFDeriv ℝ (he ∅) 2).eq_of_nhds,←(siphon_germ e).eq_of_nhds,←(EventuallyEq.fderiv_eq (siphon_germ e) (𝕜:=ℝ))]; exact p₀
lemma HeadX.zero_X : HeadX m (0:TirB N) p o U M h n book_zero 0:=by
 have ht:captain (0:TirB N) ∅= fun _=> (0:ℂ):=rfl
 unfold HeadX Tall Desk4 Desk5 SiphonT; rw [siphon_Z,ht,iteratedFDeriv_const_of_ne (by decide), Pi.zero_apply,map_zero]; -- book_zero. 
 refine ⟨ ?_,fun i a b u v=> ?_,fun i a u=> ⟨fun b v=> ?_,?_⟩⟩; rotate_left
 · change ‖(0:ℂ)-0‖ ≤ 0; simp
 · change ‖(0:ℂ)-0‖ ≤ 0; simp
 · rw [show fderiv ℝ _ _=0 from (show fderiv ℝ (0 : tangD N→ Op (Single N)) 0=0 from (hasFDerivAt_const ..).fderiv),_root_.zero_apply,map_zero]; change ‖(0:Pal)-0‖≤0; simp -- tune
 exact (show ∀ {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F],CostOle ((0: Ole E F)-0)≤0 from (fun {E F} _ _ _ _=>by unfold CostOle; exact (congrArg norm ((sub_zero (0: Ole E F)))).trans (@norm_zero (Ole E F) _)|>.le))
lemma Tall_plus (x y:TirB N)(n:ℕ): Tall o p n m (x+y) M h=Tall o p n m x M h+ Tall o p n m y M h:=by unfold Tall; rw [siphon_add,Pi.add_apply,map_add]
lemma SiphonT.plusX (x:Charter N X)(y:Charter N Y)(u:ComG): SiphonT o p U n (X+Y) M h u= SiphonT o p U n X M h u+ SiphonT o p U n Y M h u:=by unfold SiphonT; rw [siphon_add,fderiv_add (siphon_C _ x|>.differentiableAt (by norm_num)) (siphon_C _ y |>.differentiableAt (by norm_num)), _root_.add_apply,map_add]
lemma Desk4.plusX (x:Charter N X)(y:Charter N Y)(u v:ComG): Desk4 o p U n (X+Y) u v=Desk4 o p U n X u v+ Desk4 o p U n Y u v :=by unfold Desk4; rw [captain_add,iteratedFDeriv_add_apply ((x _).of_le (by decide)) ((y _).of_le (by decide))]; rfl
lemma Desk5.plusX (x:Charter N X)(y:Charter N Y)(u:ComG)(v:ComT): Desk5 o p U n (X+Y) u v=Desk5 o p U n X u v+ Desk5 o p U n Y u v :=by unfold Desk5; rw [captain_add,iteratedFDeriv_add_apply ((x _).of_le (by decide)) ((y _).of_le (by decide))]; rfl
abbrev plus_B(T V:BookTarget):BookTarget:=⟨T.S+V.S, T.v+V.v,T.l+V.l,T.p+V.p⟩
private lemma νοplus {E:Type}[NormedAddCommGroup E]{x y z w:E}(p:‖x-y‖≤c)(v:‖z-w‖≤d):‖(x+z)-(y+w)‖≤ c+d:=by rw [show x+z-(y+w)=x-y+(z-w) from (by abel)]; exact (norm_add_le ..).trans (add_le_add p v)
private lemma νοplusO {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{x y z w:Ole E F}(p:CostOle (x-y) ≤ c)(v:CostOle (z-w) ≤ d): CostOle ((x+z)-(y+w))≤ c+d:= νοplus (x:=x) (y:=y) (z:=z) (w:=w) p v
lemma HeadX.plusX (x:Charter N X)(y:Charter N Y) {T W:BookTarget}(P:HeadX m X p o U M h n T c)(V:HeadX m Y p o U M h n W d): HeadX m (X+Y) p o U M h n (plus_B T W) (c+d):=by
 constructor
 · rw [Tall_plus]; exact νοplusO P.1 V.1
 constructor
 · intro i a b v g; rw [Desk4.plusX x y]; exact νοplus (P.2.1 i a b v g) (V.2.1 i a b v g)
 intro i a v; constructor; · intro b g; rw [Desk5.plusX x y]; exact νοplus ((P.2.2 i a v).1 b g) ((V.2.2 i a v).1 b g)
 rw [SiphonT.plusX x y]; exact νοplus ((P.2.2 i a v).2) ((V.2.2 i a v).2)
end
end YM.CF.Oath
end
