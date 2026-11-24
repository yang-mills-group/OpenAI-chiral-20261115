import GaugeFieldConstruction.Lariat
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
variable {N:Side}{P:BudgetPoint}{o:Seat N}{E:InkD N}{X:Scree.Hub N}{M:Tulip.Male}{h t a v k b d:ℝ}{r l L n:ℕ}
-- local against outside.Be always before, Qty.c transported. no Req Ast stencil.Act
abbrev Enlarge (X:Scree.Hub N):Scree.Hub N:= ⟨(X.val.1,X.val.2 ∪ (Zhub X.val.1).val.2),mem_union_left _ X.property⟩
abbrev Propulse (E:InkD N)(X Y:Scree.Hub N):Zone N:= bury (Vow.stroke (lagE X) (lagE Y) (lagE Y) (oV E) (oV E)) 0
lemma shift_Z (X Y:Scree.Hub N)(v:X.val.2⊆ Y.val.2)(V:Orbit N)(u: FleetS P.threshold V.1): march P (lagE X) (oV E) V = Intent P (Propulse E X Y) V+ march P (lagE Y) (oV E) V:=by rw [Propulse,bury_U, show hollow (n:=LeanV (Single N)) 0=0 from Subtype.ext (zero_smul ..),zero_add, add_comm,amends V _ _ _ v (Subset.refl _) (fun x _=>rfl) u]
def Ling (E:InkD N)(P:BudgetPoint)(K X:Scree.Hub N)(h:ℝ)(M:Tulip.Male)(l n:ℕ):Zone N:=if Cresc l P X then Propulse E X K+ℓParcel n K P h M E else locusH X E
lemma shift_earn (V:Orbit N)(u: FleetS P.threshold V.1)(f:ℕ)(h:ℝ)(M:Tulip.Male)(l:ℕ): Intent P (Ling E P (Enlarge X) X h M f l) V= march P (lagE X) (oV E) V :=by
 unfold Ling; split; rename_i hp; · rw [Intent_plus, Parcel_cut _ _ _ _ _ _ u _ subset_union_right]; exact (shift_Z X _ subset_union_left V u).symm
 exact locus_c ..
lemma cen_pr (Y:Scree.Hub N)(p:PressB (KeyUp P) X E h t)(g:X.val.2⊆Y.val.2)(b: X.val.1=Y.val.1)(s:0<h)(v:P.power=2)(k:coverNumber P.B Y.val.2≤L): Basalt P X.val.1 l L (Propulse E X Y) 0 a (Trees.currency P.B 3 Y.val.2*(2*chi_f P.order*t)) h r M:=by
 have hg:= (transport_X X Y k g b.symm p s.le v).2.1; rw [show (chi_f P.order*t+chi_f P.order*t)= 2*chi_f P.order*t from (by ring)] at hg; rw [← show ‖(0:ℂ)‖=0 from norm_zero]; exact bury_budget _ _ hg -- rewrite 0 inside Lean? ok
lemma enL(X:Scree.Hub N)(v:24≤P.B):coverNumber P.B (Enlarge X).val.2 ≤coverNumber P.B X.val.2+1:=by
 apply (Corona.meets_sum X.property (show X.val.1∈ (Zhub X.val.1).val.2 from (Zhub X.val.1).property) P.B).trans -- tune s binder
 refine Nat.add_le_add_left (le_trans (b:=coverNumber P.B (halo P.B {X.val.1})) ?_ ?_) _ -- order. tune
 exact Corona.cover_mono (D:= (Zhub X.val.1).val.2) (X:=halo P.B {X.val.1}) (Corona.halo_mono v (Subset.refl _)) _
 exact AnalyticBridge.CouplingShape.ballPaid ..
abbrev Etching (a w:ℝ):= PieceFee (Real.exp a*w)
abbrev Flame_B (P:BudgetPoint)(L:ℕ)(t:ℝ):= Real.exp (3*(L:ℝ)) *( (2*chi_f P.order*t)+(2*chi_f P.order*Jε*t+chi_f P.order*t))
lemma runlet (w:PressB (KeyUp P) X E h t)(tA:0≤a)(s:0<h)(p:300< N.val)(u:P.order=6)(p0:P.power=2)(M:Tulip.Male)(e:r ≤ 2)(v:24≤P.B) : Basalt P X.val.1 l (l+1) (Ling E P (Enlarge X) X h M l r) (Etching a (currency P.B a X.val.2*t)) a (Flame_B P (l+1) t) h r M:=by
 unfold Ling; let A:= Enlarge X; have ht:= skim w s.le; have hμ:0≤ chi_f P.order:=spicy_f _; have hJ:= Jε₀
 split
 next hz=>
    have hv:coverNumber P.B A.val.2≤l+1:=le_trans (enL X v) (by unfold Cresc at hz; have hp: coverNumber P.B X.val.2 ≤ coverNumber P.B X.val.2^3:=Nat.le_self_pow (by omega) _; omega)
    have hp: PressB (KeyUp P) A E h t:=cut_further w subset_union_left rfl s.le
    have hK:= (piece_B (l:=l) hp tA s p u p0 M e subset_union_right hv) -- tune named param position
    apply ((cen_pr A w subset_union_left rfl s p0 hv).terms hK s.le).sharpen
    · rw [zero_add,Etching]; unfold PieceFee; have hC:0≤3+2*Jε:=by positivity
      apply mul_le_mul_of_nonneg_left _ hC; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ ht; unfold Trees.currency; rw [←Real.exp_add]; apply Real.exp_monotone
      have he: (coverNumber P.B A.val.2:ℝ)≤ (coverNumber P.B X.val.2:ℝ)+1:=by exact_mod_cast enL X v
      exact (mul_le_mul_of_nonneg_left he tA).trans_eq (by ring)
    have hf: currency P.B 3 (Enlarge X).val.2 ≤ Real.exp (3*((l+1:ℕ):ℝ)):= Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hv) (by positivity)); unfold PieceCost Flame_B; rw [mul_add (Real.exp _)]; gcongr
 next k=>
    have h:Basalt P X.val.1 l (l+1) (locusH X E) _ a 0 h r M:=locusH_g w s.le (fun i=>False.elim (k (show Cresc l P X from i))); apply h.sharpen; unfold Etching PieceFee; apply le_trans (b:=Real.exp a*(currency P.B a X.val.2*t)) (le_mul_of_one_le_left (mul_nonneg (Real.exp_pos _).le ht) (Real.one_le_exp tA)); exact le_mul_of_one_le_left (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le ht)) (by linarith : 1≤3+2*Jε); unfold Flame_B; positivity -- tune
end
end YM.CF.Oath
end
