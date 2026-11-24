import YM.CF.DPress.Gate.Fund
import YM.CF.DPress.Awake.Quip
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open Tap Bloch
variable {n:Side}
def Ru (Q:Sweep n→Prop)(E:RegBudget n):Prop:=∀ s:Sweep n, Q s→∀ U,JetS s.s s.charge (detX s.s) U→∀ X:Scree.Hub n,∀ V:Pane n, E (moveHub s X) (flashA s V)=paintR s.charge (detX s.s) (prepU (castX s) U (xtra s.charge) n) (E X V)
def Du (Q:Sweep n→Prop)(F:ForceBudget n):Prop:=∀ s:Sweep n, Q s→∀ U,JetS s.s s.charge (detX s.s) U→∀ X:Force n,∀ (V:Pane n)(τ:Ids n),Injective (priorP τ) → F (moveForce s X) (flashA s V,bun s τ)=paintR s.charge (detX s.s) (prepU (castX s) U (xtra s.charge) n) (F X (V,τ))
variable {n:Side} {Q V: Sweep n→Prop}{E F:RegBudget n}{G H:ForceBudget n}
lemma Ru.sub (p:Ru Q E)(t:Ru Q F):Ru Q (E-F):=fun i h U v j z=> (congrArg₂ (·-·) (p i h U v j z) (t i h U v j z)).trans (map_sub ..).symm
lemma Du.sub (p:Du Q G)(t:Du Q H):Du Q (G-H):=fun i h U v j V a s=> (congrArg₂ (·-·) (p i h U v j V a s) (t i h U v j V a s)).trans (map_sub ..).symm
lemma Ru.add (p:Ru Q E)(t:Ru Q F):Ru Q (E+F):=fun i h U v j z=> (congrArg₂ (·+·) (p i h U v j z) (t i h U v j z)).trans (map_add ..).symm
lemma Ru.smol (p:Ru Q E)(z:ℝ):Ru Q (z • E):=fun i h U v j f=> (congrArg (z • ·) (p i h U v j f)).trans (map_smul ..).symm -- hueV complex vs real exact
lemma rust :Ru Q 0:=fun _ _ _ _ _ _=>(map_zero _).symm
lemma dust :Du Q 0:=fun _ _ _ _ _ _ _ _=>(map_zero _).symm
lemma cred_zero(C:Finset (Scree.Hub n)):Cred 0 C:=fun _ _ _ _ _=>(map_zero _).symm
lemma cred_sub(C:Finset (Scree.Hub n)){E F:RegBudget n}(u:Cred E C)(v:Cred F C): Cred (E-F) C:= fun i h U g j=> (congrArg₂ (·-·) (u i h U g j) (v i h U g j)).trans (map_sub ..).symm
-- Rank projection real linear
open Sour.BondL
lemma stack_sub(C:Finset (Scree.Hub n))(E F:RegBudget n):StackL (E-F) C=StackL E C-StackL F C:=by apply eq_sub_of_add_eq; rw [←mark_T,sub_add_cancel]
lemma stove_sub(C:Finset (Scree.Hub n))(k:ℕ)(M:Male)(U V:RegBudget n): Tap.potion k M (heroP (StackL (U-V) C))= Tap.potion k M (heroP (StackL U C))-Tap.potion k M (heroP (StackL V C)):= funext fun i=> by rw [potion,stack_sub,Exa.weights,mul_sub,sub_mul]; rfl
lemma mint_sub(C:Finset (Scree.Hub n))(k:ℕ)(M:Male){E F:RegBudget n}(u:mintv C k M E)(v:mintv C k M F) : mintv C k M (E-F):=by
 unfold mintv; rw [stove_sub]; constructor; · rw [Pi.sub_apply,u.still,v.still,sub_self]
 intro i; exact (u.free i).fun_sub (v.free i) |>.congr_deriv (by rw [sub_self]) -- convert fun_sub
lemma mint_zero(C:Finset (Scree.Hub n))(k:ℕ)(M:Male) : mintv C k M 0:=by
 have he:= stove_sub C k M 0 0; rw [sub_self,sub_self] at he; unfold mintv; rw [he]; exact ⟨rfl,fun i=>hasDerivAt_const ..⟩
structure SecureD (Q:Sweep n→Prop)(M:Male)(p:BudgetPoint)(L k:ℕ)(X:Yds n):Prop where
 ru : Ru Q X.1
 du : Du Q X.2
 care : Cred X.1 (treeΘ p L)
 mint : mintv (treeΘ p L) k M X.1
namespace SecureD
variable {p:BudgetPoint}{L k:ℕ}{M:Male}{X Y:Yds n}
lemma sub (v:SecureD Q M p L k X)(w:SecureD Q M p L k Y): SecureD Q M p L k (X-Y):=⟨v.ru.sub w.ru,v.du.sub w.du,cred_sub _ v.care w.care,mint_sub _ _ _ v.mint w.mint⟩
lemma small(v:SecureD Q M p L k X)(g:∀ i,V i→ Q i) : SecureD V M p L k X:=⟨fun i f=> v.ru i (g i f),fun i f=> v.du i (g i f),v.care,v.mint⟩
lemma zero : SecureD Q M p L k 0:=⟨rust,dust,cred_zero _,mint_zero ..⟩
end SecureD
end YM.CF.Py.Kay
