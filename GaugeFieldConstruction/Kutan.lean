import GaugeFieldConstruction.ZoneH
import GaugeFieldConstruction.Caliber
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
variable {N:Side}{P:BudgetPoint}{o:Seat N}{K H:Vow.Pax N}{h a v k b d:ℝ}{r l L n:ℕ} (Tp:Ids N)(M:Tulip.Male)
variable (Q:Scree.Hub N)
variable (t:Crafts P Q.val.1 K h 2 b)(p:0<h) (q:P.order=6)(s:P.power=2)(u:24≤P.B)(w:coverNumber P.B Q.val.2 ≤ L) (g:(Zhub Q.val.1).val.2⊆ Q.val.2) (hv:300<N.val)(e:n≤2) (hk:TarKen (KeyUp P) Q.val.1 (lagE Q) h 2 a d K)
-- Incl.Envelop.Limit.M.* small deviation on root by exactly leading scale not all grades.L
abbrev CardT (T:Zone N)(p:BudgetPoint)(M: Male)(h:ℝ)(o:Seat N)(r:ℕ):= let X:= Zhub o; MSlot r (SealT X (T.1 X) p h M)
include hk e hv g w u s q p t
lemma plate_X {P₀: BudgetPoint}{A N':Side}{O₀:Scree.Hub N'}{M':Tulip.Male}{W:InkD N'}{Y₀: Waves}{x:ℝ}(hx: P.threshold=temp x)(y:Lumin (lagE Q) Q.val.1 K (KeyUp P) x M h v r (MoonBook _ r h (KeyUp P) P₀ A O₀.val.1 M' W))(w':r ≤n)(h':MetaB O₀.val.1 M' Y₀ W P₀ h): ‖CardT (Fetch Tp M P h Q K l n) (KeyUp P) M h Q.val.1 r- MoonIdeal r A (KeyUp P) P₀ Y₀‖ ≤ 2500*v+ SectorVal*Etching 2 d:=by
 let F:= heart Tp Q K; let A':=integers Tp M P h Q K n; let X:=fract_Z Tp M P h Q K l n; let T:= Zhub Q.val.1; let P':= KeyUp P
 obtain ⟨c,H,z,e'⟩:= cub_B Tp Q t p q s u w g hv e hk
 obtain ⟨xP,xZ⟩:= y Tp
 have hB:= Bequeath _ (w'.trans e) Y₀ z p.le hx h' (show Charter _ (OratorX _ P' _ F x (Q.val.1)) from xP) xZ
 obtain ⟨p_i,hB'⟩:= (Deal_u (l:=l) Tp M Q t p q s u w g hv e hk); -- tune existential
 -- simplify.LocalQual obtains for each.W.W.Bp
 obtain ⟨C₀,c₀⟩:= p_i.rates; obtain ⟨D,p₀⟩:= (Tax_C (l:=l) Tp M Q t p q s u w g hv e hk).rates
 have he₁:= SeT_add p.le (c₀.fits T) (p₀.fits T) M
 let V(T':Zone N):=SealT T (T'.1 T) P' h M
 have hp:CardT (Fetch Tp M P h Q K l n) P' M h Q.val.1 r=MSlot r (SealT Q F P' h M) + MSlot r (V X):=by -- tune binder
    change MSlot r (SealT T _ _ _ _)= _; rw [show (Fetch Tp M P h Q K l n).1 T=A'.1 T+X.1 T from rfl,he₁, MSlot_k]; rw [hB' r w'] -- tune
 have hP:‖MSlot r (V X)‖ ≤ SectorVal*Etching 2 d:= by
    apply (MSlot_m _ r).trans; apply (S_along (p₀.fits T) p.le M).trans; have h:(0:ℝ) ≤ SectorVal:= le_trans (by norm_num :0≤(2500:ℝ)) (le_max_left ..);
    exact mul_le_mul_of_nonneg_left ((p₀.earns _ (by norm_num)).trans (sub_le_self _ (norm_nonneg _))) h
 let A₁:= MSlot r (SealT Q F P' h M); let A₀:=MoonIdeal r A P' P₀ Y₀; rw [hp]; -- t
 change ‖A₁ + MSlot r (V X) - A₀‖ ≤ _ ; rw [show A₁+MSlot r (V X)-A₀=(A₁-A₀)+MSlot r (V X) from ((show ∀ (E:Type) [G:AddCommGroup E] (x y z:E), x+y-z=x-z+y from (fun E g x y z=> add_sub_right_comm x y z)) Waves (G:=kinnA) _ _ _)]; exact (norm_add_le ..).trans (add_le_add hB hP)
end
end YM.CF.Oath
end
