import SatinThinOpening

set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise


/- Overwrite the old unit & put in a NEW zero-shape price -/
variable {N B:Side}{J I:Type}[Fintype J][LinearOrder J][Fintype I][LinearOrder I]
attribute [-instance] instDecidableEqLex
local notation "Ω"=> mid N B
local notation "Ξ"=> Article I
local notation "Υ"=> Key (Article I)
variable (U:Side)(X:GramM (mid N B))(p:I→ Site (mid N B))(q A h:ℝ)(E:Key (Article I)→ RegBudget (mid N B))(F:Key (Article I)→ ForceBudget (mid N B))(T: Fin 2→ Topic (mid N B))
local notation "P"=>X.p
local notation "Q"=> clothTable X.p q p
local notation "W"=> Bulletin
variable {T U X p q A h E F}
variable {K:Teller SU.group}{L:ChartRatio SU.group}{R:Patch}(V: Grace K R L){d:ℝ}(P_:Grasp V.U B d)(Lo:Scree.Loom (mid N B))
noncomputable abbrev directZ(X:GramM (mid N B))(E:Key J→RegBudget (mid N B))(F:Key J→ForceBudget (mid N B))(x:Orbit (mid N B))(z:Key J) := Scree.denZ (dayShift X E F z) P_ Lo x
noncomputable def beforeCost (p:I→ Site (mid N B))(q:ℝ)(U: BudgetPoint)(x:Pane Ω)(j: Ξ): ℂ:= clothMark (readFee q (layer j)) U.threshold (p (host j)) x
noncomputable def openingCost (p:I→ Site (mid N B))(q:ℝ)(U: BudgetPoint)(x:Pane Ω)(j: Ξ): ℂ:= if layer j=0 then 0 else -↑(clothMark q U.threshold (p (host j)) x)
variable (X E F p q)
lemma before_gate (l:List Ξ)(u:l.Nodup)(x:Orbit Ω): tipI (directZ V P_ Lo X Q 0 x) l=(l.map (beforeCost p q X.p x.1)).prod • Scree.denZ X P_ Lo x:=by rw [show directZ V P_ Lo X Q 0 x=(fun z=> oath (beforeCost p q X.p x.1) z • _) from funext fun z=>density_ticket ..]; exact tip_oath _ _ _ u
lemma price_SX {A:Type*}[AddCommMonoid A] (f:Article I→A): (∑ i:Article I,f i)= ∑ i:I,(f (Prin i)+f (Astr i)):=by
 let F':=fun (j:I×Fin 2)=> f (toLex j); rw [show _=(∑ i:I×Fin 2,F' i) from Equiv.sum_comp ((toLex: I×Fin 2 ≃ Article I)) f|>.symm,Fintype.sum_prod_type]; simp_rw [Fin.sum_univ_two]; rfl -- tune spelling equivalence
include X
lemma strikeE (x:Pane Ω)(z:Υ): creed (beforeCost p q X.p x) (strike z) = creed (openingCost p q X.p x) z:=by
 unfold creed; rw [price_SX,price_SX]; apply sum_congr rfl; intro i _; unfold beforeCost openingCost; simp only [show layer (Prin i)=0 from rfl,show layer (Astr i)=1 from rfl,note_P,note_Q,(read_up q).1,ite_true, if_neg (show ¬(1:Fin 2)=0 from by decide),zero_mul,mul_zero,zero_add,add_zero,neg_mul,mul_neg]; rfl
local notation "Zq"=> openTabs X p q E
local notation "Fq"=> F ∘ unison
lemma open_gate (x:Orbit Ω)(l:List Ξ)(u:CasePage l)(b:Notice (treeO p) E F): tipI (directZ V P_ Lo X Zq Fq x) l= spray (openingCost p q X.p x.1) (fun l=> tipI (directZ V P_ Lo X E F x) (l.map toPrin)) l:=by
 let w:=openingCost p q X.p x.1; let f:= directZ V P_ Lo X E F x; let g:= f ∘ unison; rw [show directZ V P_ Lo X Zq Fq x=(fun z=> oath w z • g z) from ?_,tip_flow w (h:=g) (chapter V P_ Lo b x _ note_dif) l u.keys]; exact spray_e w l fun i v=> united f i (u.trim v)
 exact funext fun z=> (density_fee X V P_ Lo x (E (unison z)) _ _ (exponent_cloth X x q p (strike z))).trans (congrArg (fun v:ℂ=> Complex.exp v • (g z)) (strikeE X p q x.1 z)) -- tune
variable {X E F p q}
lemma fee_absent (x:Pane Ω)(i:I): beforeCost p q X.p x (Prin i)= (clothMark q X.p.threshold (p i) x:ℝ):=by simp only [beforeCost,show layer (Prin i)=0 from rfl,(read_up q).1]; rfl
lemma fee_opening (x:Pane Ω)(i:I): openingCost p q X.p x (Astr i)= -↑(clothMark q X.p.threshold (p i) x):=if_neg (show ¬ layer (Astr i)=0 from by show (1:Fin 2)≠0; decide)
lemma fee_station (x:Pane Ω)(i:I): openingCost p q X.p x (Prin i)=0:=if_pos rfl
#print axioms before_gate
#print axioms open_gate
end YM.CF.QuadClock
