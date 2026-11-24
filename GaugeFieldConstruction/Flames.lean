import GaugeFieldConstruction.Jigsaw
import GaugeFieldConstruction.Bough
import GaugeFieldConstruction.Kasol
import GaugeFieldConstruction.Bracer
import GaugeFieldConstruction.Savio
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
section
open Py Riant Lattice Prism Tap FlightFlux TableF Boom Axon Flot Taxi
open Lenten.ModuleB
open Trees Hake Vow Bake Rue Larch
open TableF Lenten.Bank Lenten
open Layout Fren
open TableF Lenten.Bank Lenten Lenten.Layout Fren
variable {N:Side}{P:BudgetPoint}{o:Seat N}{E:InkD N}{X:Scree.Hub N}{M:Tulip.Male}{h t a v k b d:ℝ}{r l L:ℕ}
def Intent {N:Side}(p:BudgetPoint)(V:Zone N)(U:Orbit N): Cipher N:= Pastry.hollow V.2.2+ exponentL p V.1 U.1+ fuelV p V.2.1 U
abbrev Strew(P:BudgetPoint)(V:Zone N): ℝ→ℝ:=fun _=>0 -- remove
lemma Intent_0 (p:BudgetPoint)(V: Orbit N): Intent p 0 V=0:=by
 change Pastry.hollow 0+exponentL p 0 V.1+fuelV p 0 V=0; rw [show Pastry.hollow (n:=LeanV (Single N)) 0=0 from Subtype.ext (zero_smul ..),zero_add,prizes0, add_zero]; unfold exponentL; apply sum_eq_zero; intro i _; rw [Pi.zero_apply, numb_b p i 0 V]; unfold Vow.march; split <;> rfl -- tune
lemma Intent_plus (p:BudgetPoint)(V W:Zone N)(U:Orbit N): Intent p (V+W) U= Intent p V U+ Intent p W U:=by
 unfold Intent
 rw [show exponentL p (V + W).1 U.1= _ from ripe_H p U V.1 W.1, show fuelV p (V+W).2.1 U= _ from toast U V.2.1 W.2.1 (P:=p), show Pastry.hollow (n:=LeanV (Single N)) (V+W).2.2 =Pastry.hollow V.2.2+Pastry.hollow W.2.2 from Subtype.ext (add_smul ..)]
 abel
lemma Intent_sum {I:Type*}(T:Finset I)(G:I→ Zone N)(p:BudgetPoint)(U:Orbit N): Intent p (∑ i∈T,G i) U=∑ i∈T,Intent p (G i) U:=by induction T using Finset.induction_on with | empty=> rw [sum_empty,Intent_0,sum_empty]|insert i Y t ih=> rw [sum_insert t,sum_insert t, Intent_plus,ih]
def singleP (i:Scree.Hub N)(F:InkD N):RegBudget N:= Pi.single i F
def locusH (i:Scree.Hub N)(F:InkD N):Zone N:= (singleP i F,0,0)
abbrev bury(K:Cusp N)(a:ℂ): Zone N:= (0,K,a)
lemma single_E (i:Scree.Hub N)(F:InkD N)(U:Orbit N): exponentL P (singleP i F) U.1=march P (lagE i) (oV F) U:=by
 unfold exponentL; rw [sum_eq_single i,singleP,Pi.single_eq_same]; exact numb_b ..
 intro b _ h; unfold singleP; rw [Pi.single_eq_of_ne h,numb_b P b 0 U]; unfold Vow.march; split <;> rfl
 simp
lemma locus_c (i:Scree.Hub N)(F:InkD N)(U: Orbit N): Intent P (locusH i F) U= Vow.march P (lagE i) (oV F) U:=by unfold Intent locusH; simp only [single_E]; rw [show Pastry.hollow (n:=LeanV (Single N)) 0=0 from Subtype.ext (zero_smul ..),prizes0,zero_add,add_zero]
lemma bury_U (K:Cusp N)(s:ℂ)(v:Orbit N):Intent P (bury K s) v=hollow s+fuelV P K v:=by
 unfold Intent; rw [show exponentL P (bury K s).1 v.1=0 from ?_]; swap
 · rw [show (bury K s).1=0 from rfl,←show Intent P 0 v=exponentL P 0 v.1 from (by unfold Intent; change hollow 0+exponentL P 0 v.1+fuelV P 0 v= _; rw [show hollow (n:=LeanV (Single N)) 0=0 from Subtype.ext (zero_smul ..), zero_add,prizes0,add_zero]), Intent_0]
 rw [add_zero]
lemma bury_budget (K:Cusp N)(s:ℂ)(p: HasCopper L o P h K d) : Basalt P o l L (bury K s) ‖s‖ a d h r M:=by
 have hx : ArenaC P 0 o (0:Scree.Hub N→ℝ) a h 0:=by
    refine ⟨fun i=>Vale.rinse ..,?_,fun i=>le_rfl,fun i _=> ⟨rfl,rfl⟩⟩; simp [ΩBook]
 change _; refine ⟨⟨0,ArenaC.moveup hx ?_⟩,(show Basalt P o l L 0 0 a 0 h r M from Basalt.none).tags,p⟩; change 0≤ ‖s‖-‖s‖; exact (sub_self ..).ge
lemma locusH_g (p:PressB (KeyUp P) X E h t)(q:0≤h)(u:Cresc l (KeyUp P) X →lifeH E 1=0∧ (X≠ Zhub X.val.1→ MSlot r (SealT X E (KeyUp P) h M)=0)): Basalt P X.val.1 l L (locusH X E) (Trees.currency P.B a (X.val.2)*t) a 0 h r M:=by
 let I:= X.val.1
 let w:=p; have hp:= skim p q; let V:= singleP X E
 refine ⟨⟨Pi.single X t,?_⟩,?_,HasCopper.zero⟩
 · constructor
   · intro i; change PressB _ _ (V i) _ _; unfold V singleP; by_cases h:i=X; · subst i; rw [Pi.single_eq_same,Pi.single_eq_same]; exact p
     rw [Pi.single_eq_of_ne h,Pi.single_eq_of_ne h]; exact Vale.rinse ..
   · unfold ΩBook; simp only [Pi.single_apply,mul_ite,mul_zero, sum_ite_eq', mem_univ,↓reduceIte]; change _ ≤ _- ‖(0:ℂ)‖; rw [norm_zero,sub_zero]; rfl -- rfl compar le
   · intro i; rw [Pi.single_apply]; split; exact hp; exact le_rfl
   intro i h; have ht:i≠ X:=fun p=> h (p ▸ rfl); change V i=0∧ _; exact ⟨(by unfold V singleP; rw [Pi.single_eq_of_ne ht]),by rw [Pi.single_eq_of_ne ht]⟩
 intro i p'; change lifeH (V i) 1=0∧ (_→ MSlot _ (SealT _ (V i) _ _ _)=0); unfold V singleP; by_cases h:i=X
 · subst i; rw [Pi.single_eq_same]; exact u p'
 rw [Pi.single_eq_of_ne h, meter_zero]; exact ⟨rfl, fun _=>void_M _⟩
-- for X that contains Z0
abbrev UTicket (N:Side) := Nat -- remove
abbrev χE(X:Scree.Hub N)(E:InkD N):= lifeH E 1
abbrev splinter (n:ℕ)(X:Scree.Hub N)(P:BudgetPoint)(h:ℝ)(M:Tulip.Male)(E:InkD N):= shoulder X.val.1 (KeyUp P) M h (MSlot n (SealT X E (KeyUp P) h M))
def ℓParcel (n:ℕ)(X:Scree.Hub N)(P:BudgetPoint)(h:ℝ)(M:Tulip.Male)(E:InkD N): Zone N:= let Z:=Zhub X.val.1; let F:=splinter n X P h M E; let K:=Vow.stroke (lagE X) (lagE Z) (lagE X) (oV F) (oV F)+Ωχ X (χE X E);(singleP X (E-(χGhost N (χE X E)+F))+singleP Z F,K,χE X E)
lemma Parcel_cut (X:Scree.Hub N)(P:BudgetPoint)(h:ℝ)(M:Tulip.Male)(E:InkD N)(V:Orbit N)(v: FleetS P.threshold V.1)(k:ℕ) (e:(Zhub X.val.1).val.2⊆ X.val.2): Intent P (ℓParcel k X P h M E) V= Vow.march P (lagE X) (oV E) V:=by
 let F:= splinter k X P h M E; let Q:= Zhub X.val.1; let Y:= lagE X; let Z:= lagE Q;
 let U:= χGhost N (χE X E); let H:= Vow.stroke Y Z Y (oV F) (oV F); let T:= Ωχ X (χE X E)
 change hollow (χE X E)+ exponentL P (singleP X (E-(U+F))+singleP Q F) V.1 +fuelV P (H+T) V=_
 let I(K):= Vow.march P Y (oV K) V
 have hp(A B: InkD N): I (A+B)=I A+I B:= march_add V P Y (oV A) (oV B); have ht:=amends V Y Z Y (Subset.refl _) e (fun _ _=>rfl) v (f:=oV F) (g:=oV F)
 rw [ripe_H (V:=V),single_E _ _ V,single_E _ _ V,Vow.toast]; have hh:hollow (χE X E)+fuelV P T V=I U:= (Φaccord V v X _).symm
 change _+ (I (E-(U+F))+march P Z (oV F) V)+_ = I E
 calc _= I (E-(U+F))+(I U+I F):=by change march P Z (oV F) V+fuelV P H V= I F at ht; rw [←hh,← ht]; abel
      _=_:=by rw [←hp,←hp,sub_add_cancel] -- tune rw position
end
end YM.CF.Oath
end
