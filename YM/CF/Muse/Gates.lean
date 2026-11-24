import YM.CF.Urn.Haven
import YM.CF.Oath.Dazzle
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open Eire.Dress Yaw PetalP Feu Feu.Corset Haro
variable {r K0:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]{f c:Type}[Fintype f][LinearOrder f][Fintype c][LinearOrder c]
local notation "κ"=> (Scree.mid P B)
local notation "Kx"=> (Scree.mid N B)
local notation "hT"=> (LeanV f)
local notation "Zx"=> LeanV c
local notation "BF"=> (Eire.Ride S)
local notation "Fm"=> (LeanV (Single κ))
local notation "CM"=> (LeanV (Single Kx))
-- Exact resolve PH.Wick all shares.SupportX both senses. 
variable (p q: Single (mid P B))(Tg:Rill.Arch G t)(W: Meter TailB G t)(Y:Meter Grave G t)(g_: Odd G.count.val)(t':0<t)(kR:ℕ)
local notation "ρ"=> Support (Domain P B)
lemma yu_G(g:Seat N→SU.E)(b:Bool)(x:Rock N)(i:SU.Slot):lotY false false (tradew N g) (put (b,x,i))= ∑ j:SU.Slot, gemT (g (node x.1)) b j i • (put ((b,(x,j)):LeanV (Single N))):=by
 rw [Urn.mold]; let Q:=(spice (tradew N g) false).val
 have ht (x y:Rock N)(b z:Bool)(i j:SU.Slot): Q (b,x,i) (z,y,j)=if b=z∧x=y then gemT (g (node x.1)) b i j else 0:=by by_cases hx:x=y <;> cases b <;> cases z <;> simp [Q,hx,Ne.symm,Scree.spice,gemT,closeV,Pastry.thread, tradew,jump_apply,ccU]
 change ∑ k:LeanV (Single N),Q k (b,x,i) • put k= _; rw [Fintype.sum_prod_type,sum_eq_single b]; swap; · intro a _ h; refine sum_eq_zero fun j _=>?_ ; rw [ht,if_neg,zero_smul]; tauto
 swap; · simp
 rw [Fintype.sum_prod_type,sum_eq_single x]; exact sum_congr rfl fun j _=>by rw [ht,if_pos ⟨rfl,rfl⟩]; -- tune inner notation
 intro a _ p; exact sum_eq_zero fun i _=> by rw [ht,if_neg,zero_smul]; tauto
 simp
private lemma slashF{A B C D X:Type}[AddCommMonoid X](u:Finset A)(v:Finset B)(a: Finset C)(b:Finset D)(F:A→B→C→D→X): (∑ i∈u,∑ j∈v,∑ k∈a,∑ l∈b,F i j k l)=∑ k∈a,∑ l∈b,∑ i∈u,∑ j∈v,F i j k l:=by
 simp_rw [sum_comm (s:=v) (t:=a),sum_comm (s:=v) (t:=b),sum_comm (s:=u) (t:=a),sum_comm (s:=u) (t:=b)]
variable (i j:Rock (mid N B))
lemma rite_G(g:Seat (mid N B)→SU.E)(Z:Op SU.Slot): lotY false false (tradew (mid N B) g) (lineY i j Z) = lineY i j (putX g i * Z * star (putX g j)):=by
 let U:=gemT (g (node i.1)) true; let V:=gemT (g (node j.1)) false; let S:=univ (α:=SU.Slot); let f:= putX g j
 let X(x y u v:SU.Slot):=Z x y • ( U u x • put ((true,(i,u)):CM) * (V v y • put ((false,(j,v)):CM)))
 unfold lineY gateY; simp_rw [map_sum,lonY,map_mul,yu_G,sum_mul,mul_sum,smul_sum]; change ∑ x∈S,∑ y∈S,∑ i∈S,∑ j∈S,X x y i j= _
 rw [slashF]; refine sum_congr rfl fun x _=>sum_congr rfl fun y _=>?_ ; simp only [Matrix.mul_apply,sum_mul,Finset.sum_smul]; rw [sum_comm] -- tune
 refine sum_congr rfl fun ia _=> sum_congr rfl fun ja _=>?_ ; unfold X; rw [smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul]; congr 1; -- tune shadow
 change _ = U x ja * Z ja ia * V y ia; ac_rfl
#check Haro.care
end YM.CF.Oath
