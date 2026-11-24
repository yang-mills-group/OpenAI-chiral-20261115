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
variable {N B : Side}
variable (V:Op (Single (mid N B)))(i j:Single (mid N B))(s:ℂ)
local notation "Ω"=> LeanV (Single (mid N B))
-- Pkg generic
lemma ink_wave : InjectPH 1 V= ∑ i: Single (mid N B),∑ j:Single (mid N B), V i j • (put ((true,i):Ω)*put ((false,j):Ω)):=by
 have hx(p q:Rock (mid N B)):star (putX 1 p) * frame_w V p q * putX 1 q=frame_w V p q:=by
    have hp(p:Rock (mid N B)): putX 1 p=1:=by unfold putX mater; simp
    rw [hp,hp,star_one,mul_one,one_mul]
 unfold InjectPH lineY; conv_rhs=> rw [Fintype.sum_prod_type]
 refine sum_congr rfl fun i _=>?_ ; simp_rw [hx]; rw [sum_comm]; apply sum_congr rfl; intro k _; -- tune orientation need line sums commute
 conv_rhs=> rw [Fintype.sum_prod_type]
 rfl
lemma part_U : crumb (s • (1:FC Ω)+ InjectPH 1 V) ∅=s:=by
 have h(i j:Single (mid N B)): crumb (put ((true,i):Ω)*put (false,j)) ∅=0:=by
    -- by Ione
    exact Ione.bloom_M _ _ _ (by simp)
 rw [ink_wave,crumb_add]; simp_rw [crumb_sum,crumb_scale,h]; rw [show crumb (1:FC Ω) ∅ = 1 from ?_]; swap; · simp [crumb]
 simp
abbrev winsock {J:Side} (i j:Single J)(U:FC (LeanV (Single J))):=Prism.portB U (true,i) (false,j)
private lemma moves (i j:Single (mid N B)) : acts (put ((true,i):Ω)*put (false,j)) (vacuum Ω)= parity ((true,i):Ω) {(false,j)} • basisKet (tray i j):=by rw [act_mul,Fock.vacuum,put_act]; simp only [notMem_empty, ↓reduceIte]; rw [show parity ((false,j):Ω) ∅=1 from (by simp [parity]),one_smul, put_act,if_neg]; all_goals simp -- tune
lemma pick (x y: Single (mid N B)): winsock i j (put ((true,x):Ω)*put (false,y))=if i=x∧j=y then 1 else 0:=by
 unfold winsock Prism.portB; rw [moves,moves]; by_cases p:(i=x∧j=y)
 · rw [if_pos p,p.1,p.2,inner_self_eq_norm_sq_to_K,norm_smul, show ‖parity ((true,x):Ω) {(false,y)}‖=1 from (by simp [parity])]; simp [basisKet]
 rw [if_neg p,inner_smul_left, inner_smul_right,basis_inner]; -- tune
 have hh: tray i j≠ tray x y:=by
    intro h; let ht:= Haro.tray_in (a₁:=(i,j)) (a₂:=(x,y)) h; exact p ⟨congrArg Prod.fst ht, congrArg Prod.snd ht⟩ -- syntax
 simp [basisKet,hh]
lemma part_W : winsock i j (s • (1:FC Ω)+ InjectPH 1 V) = V i j:= by
 have he:winsock i j (1:FC Ω)=0:=by unfold winsock; rw [Prism.port_eq]; simp [crumb,Matrix.one_apply] -- tune
 rw [ink_wave,winsock, Prism.portB]; simp_rw [act_add,act_sum,act_smul,inner_add_right,inner_sum,inner_smul_right]; change _*winsock i j 1+∑ v:Single (mid N B),∑ w: Single (mid N B), V v w*winsock i j ( _ )= _
 simp_rw [he,pick]; simp only [mul_zero,zero_add]; rw [sum_eq_single i,sum_eq_single j]; · simp
 · intro b _ h; simp [Ne.symm h]
 · simp
 · intro b _ h; simp [Ne.symm h]
 simp
omit i j
-- data basis maps to detect master white
end
end YM.CF.Oath
end
