import YM.CF.Bloom.Apse
import YM.CF.DPress.Fees.Pillar
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
open scoped YM.CF.Mew
variable {n:Side}{h a b: ℝ}{L:ℕ}{q:BudgetPoint} (u:1≤h)
local notation "pp" => primeU
abbrev Yds(n:Side) := RegBudget n × ForceBudget n
-- Zero slip.Press Costs only No identity vanish? demanded.
structure AccountY(q:BudgetPoint)(h:ℝ)(X:Yds n)(p:ℝ):Prop where
 E: IncX pp X.1 q h p
 K: Dark pp X.2 q h p
structure Léon (q:BudgetPoint)(h:ℝ)(L:ℕ)(X:Yds n)(p:ℝ):Prop extends AccountY q h X p where
 oily: Ionic q L X.1
variable {x y:Yds n}
namespace AccountY
include u
lemma nn (v:AccountY q h x a):0≤a:=(billP (n:=n) q u).priceQ x.1 v.E
lemma more (v:AccountY q h x a)(t:a≤b):AccountY q h x b:= ⟨(billP (n:=n) q u).toReceipt.relax v.E t,(billF (n:=n) q u).toReceipt.relax v.K t⟩
lemma add (v:AccountY q h x a)(w:AccountY q h y b):AccountY q h (x+y) (a+b):=⟨(billP (n:=n) q u).add v.E w.E,(billF (n:=n) q u).add v.K w.K⟩
lemma scale (v:AccountY q h x a)(z:ℂ):AccountY q h (z • x) (‖z‖*a):=⟨(billP (n:=n) q u).scale z v.E,(billF (n:=n) q u).scale z v.K⟩
lemma sub(v:AccountY q h x a)(w:AccountY q h y b): AccountY q h (x-y) (a+b):=⟨(billP (n:=n) q u).sub v.E w.E,(billF (n:=n) q u).sub v.K w.K⟩
lemma zero : AccountY (n:=n) q h 0 0:=⟨(billP (n:=n) q u).zero_p,(billF (n:=n) q u).zero_p⟩
end AccountY
namespace Léon
include u
lemma more(v:Léon q h L x a)(t:a≤b):Léon q h L x b:=⟨v.toAccountY.more u t,v.oily⟩
lemma add(v:Léon q h L x a)(w:Léon q h L y b): Léon q h L (x+y) (a+b):=⟨v.toAccountY.add u w.toAccountY,Beau.wage_add v.oily w.oily v.E w.E (zero_le_one.trans u)⟩
omit u in
private lemma spark_c(v:InkD n)(c:Scree.Hub n) (p:PressB q c v h a)(u: spark c.val.1 v)(w:1≤h)(t:ℂ): spark c.val.1 (t • v):=by
 have hp:=Beau.profit p (zero_le_one.trans w); change ContDiffAt ℝ _ (pot ∅ ∘ v ∘ increment 1) _ at hp
 constructor; · let l:=u.1; exact Eq.trans (show pot ∅ ((t • v) 1)= t • pot ∅ (v 1) from rfl) (by rw [l,smul_zero])
 intro x y a b; rw [show pot (n:=n) ∅∘ (t • v) ∘ increment 1=t • (pot ∅ ∘ v ∘ increment 1) from rfl, iteratedFDeriv_const_smul_apply (i:=2) hp, _root_.smul_apply,u.2 _ _ a b,smul_zero]
lemma scale (v:Léon q h L x a)(z:ℂ): Léon q h L (z • x) (‖z‖*a):=⟨v.toAccountY.scale u z, fun i p h=> spark_c (x.1 i) i (Rosy.values q u v.E i) (v.oily i p h) u z⟩
lemma sub(v:Léon q h L x a)(w:Léon q h L y b) : Léon q h L (x-y) (a+b):=by
 have he:Léon q h L (-y) b:=by simpa only [neg_smul,one_smul,norm_neg,norm_one,one_mul] using w.scale u (-1)
 exact sub_eq_add_neg x y|>.symm ▸ v.add u he -- tune nested tactic
lemma zero : Léon (n:=n) q h L 0 0:= ⟨AccountY.zero u,fun _ _ _=>Beau.none_q _⟩
end Léon
end YM.CF.Py.Kay
