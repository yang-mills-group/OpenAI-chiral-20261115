import YM.CF.BProof.Hill.Net
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
open YM.CF.Floral Ione Haro Beau Oise Larch Lilt Vow
open scoped YM.CF.Mew
namespace Cupboard
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{V:Grace K R L}{N B:Side}{d x:ℝ}{U:Grasp V.U B d}{W:GivenX V U}{q:Chi}{e a h γ w:ℝ}{order power:ℕ}
-- Bough spine geometry keeps Hue, lifts genuine fields. h rt fixed at hq; no size when comparing l0 theta step. Spans Estimate. Need access S.ρ uniforms.
open Bake PushA Episode Salt
variable {m:Side}{hx N0 n:ℕ}{T': Month x a order power N0 V W}
namespace Realm
variable {P:Realm V T' m n}
local notation "νγ"=>hat R.L x
local notation "Xκ"=> (cell m B R.L)
local notation "Lr"=>dleaf R.L
variable {J:Robes N V W}{Z:Cape m B R.L}{F R0 R1 ψ:ℝ→ℝ}{ρ:ℕ→ℝ}{η αP:ℝ}{Lm:ℕ}
namespace Shell
variable (Y:Shell P q Z J h F R0 R1 ψ ρ η αP Lm)
open FundingL Day
variable {Y} {v: StarPS n}{Θ:∀ j,Parcel (cell m B R.L j)}
namespace Journey
variable (p:Y.wish.Ship v Θ)
include p
lemma leaf(j:ℕ)(u:j≤n): TopK P h j (Θ j):= (p.fee j (Nat.zero_le _) u).1
lemma beta{j:ℕ}(u:j≤ n): (Θ j).βx= (ruler P).aim v j:= (p.fee j (Nat.zero_le _) u).2
lemma matched {j:ℕ}(u:j≤ n): matchedX (νγ j) (P.astr j (Θ j)).beta:=by
 change matchedX _ (Θ j).βx; rw [beta p u]; exact βcheck P _ Y.hot.pos Y.hot.pay u
lemma ledger{j:ℕ}(u:j<n):∃ i: BF P F h j, i.val=Θ (j+1) ∧ Θ j=(Y.book j u).out i:= p.anchor j (Nat.zero_le _) u u
noncomputable def document{j:ℕ}(u:j<n):BF P F h j:=Classical.choose (ledger p u) -- implicit `p`? include.Merk.F expensive
lemma document_1{j:ℕ}(u:j<n):(document p u).val= Θ (j+1):= (Classical.choose_spec (ledger p u)).1
lemma document_2{j:ℕ}(u:j<n): Θ j=(Y.book j u).out (document p u):= (Classical.choose_spec (ledger p u)).2
lemma price{j:ℕ}(u:j<n): ShiftQ (P.ref (j+1)).p h (Lr (νγ j)) (document p u).val:=by rw [document_1]; exact FundingL.tollR (q0:=none) (leaf p _ (by omega)) (Y.expense (show j≤ j+1 from by omega)).1
noncomputable def H(j):= if u:j<n then (Y.book j u).rot (document p u) else 0
noncomputable def Δ(j):= if u:j<n then (Y.book j u).dPS (document p u) else 0
lemma sea {j:ℕ}(u:j<n) : ‖Complex.exp (P.astr (j+1) (Θ (j+1))).v‖*ρ j≤ ‖Complex.exp (P.astr j (Θ j)).v‖:=by rw [document_2 p u,←document_1 p u]; exact (Y.book j u).lowP _
open Rue
lemma real_θ{j:ℕ}(u:j<n) : H p j=(Y.book j u).rot (document p u):=dif_pos u
lemma shift {j:ℕ}(u:j<n): (Θ (j+1)).βx+(P.β j-P.β (j+1))-Δ p j= (Θ j).βx:=by rw [document_2 p u,←document_1 p u, (Y.book j u).core,Δ,dif_pos u]; rfl
lemma realShip : Pull_P V a power order N0 T' m P.hp n P.β J q h R0 ψ Z (fun j=> P.astr j (Θ j)) (H p) (Δ p):=by
 refine ⟨?_,fun j v=>?_,fun j v=>?_,fun _ _=> ⟨rfl,rfl,rfl,rfl⟩,leaf p,fun j v=> matched p v,?_,?_,?_⟩
 · intro j t z v; let B:=Y.book j t; have he:= (B.step (document p t)) z; change FleetS (P.ref j).p.threshold z.1 at v
   rw [document_2 p t,←document_1 p t,real_θ p t]; exact (by simpa only [Pi.zero_apply,Real.exp_zero,one_smul] using he v)
 · rw [real_θ p v]; exact ((Y.book j v).trueP _ (price p v)).2.2
 · rw [Δ,dif_pos v]; exact ((Y.book j v).trueP _ (price p v)).2.1
 · intro j t; let h:= shift p t; change (Θ _).βx-_ - ((Θ _).βx-_)=_; linarith only [h]
 · change (Θ 0).βx=_; rw [beta p (Nat.zero_le _), Air.aim_z]; change P.β 0+(0:ℝ)=_; rw [add_zero]
 dsimp only []; rw [p.orbit]
end Journey
end Shell
end Realm
end Cupboard
end YM.CF.Py
