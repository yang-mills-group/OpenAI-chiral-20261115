import YM.CF.Reed.Trio
import YM.CF.Ridge.Trio
import YM.CF.Ridge.Ply
import YM.CF.Paxos.Heron
import YM.CF.Tar.Run
import YM.CF.Paxos.Luz
import YM.CF.Bloom.Kale
set_option autoImplicit false
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Beau Haro Ione Salt
set_option maxHeartbeats 1000000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W)(M:Side)(ht:T.q ≤ M.val)(l0:ℕ)(k₀:ℕ)
variable (B0:ℕ→ℝ)(D:Due V a p i N0 T M ht l0 B0)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)
local notation "Xc"=> cell M B R.L
local notation "Lr"=>dleaf R.L
local notation "Fh"=> hueR V a p i N0 T M ht l0 B0
local notation "μh"=> hat R.L x
open Oise
abbrev RankX:= Option ℕ
@[reducible] def Provides(R:Side)(k:ℕ)(Y:GramM (mid N B))(h δ:ℝ)(x:RankX):Prop:= match x with
 | none => Laurel (B:=B) Y k h δ δ R.val
 | some i=> IncX (ply_U R i) Y.F Y.p h δ ∧ Y.slip=0 ∧ Dark (ply_U R i) Y.K Y.p h δ
variable(R':Side)(t:ℂ)
namespace Provides
variable {xQ:RankX}{D' Z:ℝ}

lemma liftE(Y:GramM (mid N B))(F:RegBudget (mid N B))(v:Sweep (mid N B)→Prop)(p:IncX v F Y.p h D')(g:D'≤Z): IncX v F Y.p h Z:=by obtain ⟨⟨A,h,t⟩,p⟩:=p; exact ⟨⟨A,h,fun i=>(t i).trans g⟩,p⟩
lemma liftQ(Y:GramM (mid N B))(F:ForceBudget (mid N B))(v:Sweep (mid N B)→Prop)(p: Dark v F Y.p h D')(g:D'≤Z): Dark v F Y.p h Z:=by obtain ⟨⟨A,h,t⟩,p⟩:=p; exact ⟨⟨A,h,fun i=>(t i).trans g⟩,p⟩
variable {h} {Y:GramM (mid N B)}{R':Side}(u:Provides R' k Y h D' xQ)
include u
lemma lot : LotR Y h D' D':=by
 cases xQ; · exact (show Laurel _ _ _ _ _ _ from u).lot_p le_rfl le_rfl
 exact ⟨⟨u.1.weight,fun _ p=>p.elim⟩,u.2.1,⟨u.2.2.weight,fun _ p=>p.elim⟩⟩
lemma arc (u': D' ≤Z)(p:0≤Z) : Arc_r Y h Z Z Z:=by
 cases xQ with
 | none=> exact (show Laurel _ _ _ _ _ _ from u).vest Z Z Z u' u' p
 | some v=>
    have ht:IncX primeU Y.slip Y.p h Z:=by
       rw [u.2.1]; exact ⟨⟨0,fun i=>Vale.rinse i Y.p _,fun i=>by simp [BudgetPoint.mass]; exact p⟩, fun s _ T t i V=> (map_zero _).symm⟩
    exact ⟨⟨(liftE h Y _ _ u.1 u').weight,fun s p=>p.elim⟩,ht,⟨(liftQ h Y _ _ u.2.2 u').weight,fun s p=>p.elim⟩⟩
lemma towers (p:D'≤Z): Provides R' k Y h Z xQ:=by
 cases xQ with
 | none=>
    obtain ⟨p1,t,y,hQ,z⟩:=u; exact ⟨liftE h Y _ _ p1 p,t,liftQ h Y _ _ y p,hQ,z⟩
 | some i=> exact ⟨liftE h Y _ _ u.1 p,u.2.1,liftQ h Y _ _ u.2.2 p⟩
omit u
lemma scene_U{r:ℕ} (v:Provides R' k Y h D' (some r))(S:Sweep (mid N B))(g:ply_U R' r S): StandX Y S:=by
 refine ⟨?_,?_,?_⟩
 · exact fun x V=> v.1.face S g _ (spinZ ..) x V
 · rw [v.2.1]; exact fun i x=> (map_zero _).symm
 intro i t y h; exact v.2.2.face S g _ (spinZ ..) i y t h
open BudgetPoint
lemma tone_v (R1:RegBudget (mid N B))(V1:GramM (mid N B))(Z1:ForceBudget (mid N B))(e:ℝ)(b:ℝ)(u:Provides R' k (spark_B V1 R1 Z1 b t) h D' xQ): Provides R' k (color_b V1 e R1 0 Z1 t) h D' xQ:=by cases xQ; exact ⟨u.1,u.2,u.3,u.4,u.5⟩; exact ⟨u.1,u.2.1,u.2.2⟩ -- projection expanded not work
end Provides
structure Duty (S:StepData (Domain N B) (Domain P B))(G:Ratio (mid N B) (mid P B))(x RΘ M D0 D1 hμ:ℝ)(Q0 Q1:RankX) : Prop where
 step (T: Tube SU.group S)(A0:Scree.Loom (mid N B))(B_: Scree.Loom (mid P B))(X:GramM (mid N B))(Y: GramM (mid P B))(pA:Roof _ J.k J.roomX J.n A0)(pB: Roof _ J.k J.roomX J.n B_)(wB:∀ F' U' V', JointB G (seine G F' q J.d U' (A0 V'), A0 V') J.roomX)(H:Girt.BaseL U G Y A0 B_ q J.d)(hL:S.patch.L=R.L)(hG:G.count=R.L){Z' γ:ℝ}(b:StatV V G T U W X Y Z' γ a x p i)(g:N0*radiusB x ≤ (Domain N B).val)(c:60< (Domain N B).val):∀ (I:Type)[TopologicalSpace I][FirstCountableTopology I][Nonempty I](bu:I→ℝ)(F0 F1:I→ RegBudget (mid P B))(F2:I→ForceBudget (mid P B))(Jk:I→ℂ)(ij:I→ Haro.ΘS RΘ), let X'(c):=color_b X (bu c+(Z'+γ)) 0 0 0 0; let Vu(c):=color_b Y (bu c) (F0 c) (F1 c) (F2 c) (Jk c); Continuous bu→ Tone_u F0 Y.p → Tone_u F1 Y.p → Tone_v F2 Y.p→ Continuous ij → (∀ c,Girt.BaseL U G (Vu c) A0 B_ q J.d) →(∀ c,StatV V G T U W (X' c) (Vu c) Z' γ a x p i) → (∀ c, Provides R.L K.j (Vu c) h D1 Q1)→∃ (W1:I→Haro.ΘS RΘ)(R1:I→RegBudget (mid N B))(Z1:I→ForceBudget (mid N B))(Q:I→ℂ)(Δ:I→ℝ), Continuous W1∧Continuous Δ ∧ Beau.LampF R1 ∧(∀ j:Force (mid N B),∀ v,Continuous fun z=> Z1 z j v)∧∀ c,Provides R.L K.j (spark_B (X' c) (R1 c) (Z1 c) (Δ c) (Q c)) h D0 Q0∧|Δ c|≤M ∧ (ij c=W1 c→(∀ V':Orbit (mid N B), Rue.FleetS X.p.threshold V'.1→stove U A0 (Vu c) B_ G S q J.d (Haro.riseV (W1 c)) V'=denZ (spark_B (X' c) (R1 c) (Z1 c) (Δ c) (Q c)) U A0 V')∧ ‖Complex.exp (Vu c).v‖*hμ ≤ ‖Complex.exp (Q c)‖)
lemma Duty.weakX {Rθ hμ hν v z v' z' M M':ℝ}{Q0 Q1:RankX}(D:Duty V a p i N0 J q h S G x Rθ M v z hμ Q0 Q1)(pM:M ≤ M')(hz:z'≤z)(hv:v≤v')(hx:hν ≤ hμ):Duty V a p i N0 J q h S G x Rθ M' v' z' hν Q0 Q1:=by
 constructor; intro T A0 B1 X Y ht hp wX H hL hg ZN WN b n hk I _ _ _ bu F0 F1 F2 P θ X' Y' t p q u w σ γ Ω; obtain ⟨W1,R1,Z1,Q,Δ,s,v,w,z,u⟩:= D.step T A0 B1 X Y ht hp wX H hL hg b n hk I bu F0 F1 F2 P θ t p q u w σ γ (fun c=> (Ω c).towers hz)
 exact ⟨W1,R1,Z1,Q,Δ,s,v,w,z, fun c=>⟨((u c).1.towers hv), (u c).2.1.trans pM,fun p=>⟨((u c).2.2 p).1,(mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans ((u c).2.2 p).2⟩⟩⟩
end YM.CF.Py
