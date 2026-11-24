import YM.CF.Vp929.Pre.Ambit
import YM.CF.Mica.Near
import YM.CF.Fixed.Voltage.Grant

/-! XXI: buy the extra unit of support rate in worth_R and in Pre/Ambit.priceRun, no cost or geometry changes. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
open Vow Salt
variable (P:BudgetPoint)(s:Sweep n)
local notation "Ta"=> actY s
local notation "HQ"=> (hail_Q s).val
local notation "Φg"=> (Finset (Dwell n))
open Vow Larch
open Bake Lilt Rue Trees
abbrev editRate (P:BudgetPoint) (u:ℝ) (p:0<u) : BudgetPoint := { P with
 supportExponent:=u
 exponent_pos:=p }

def ups (P:BudgetPoint) := editRate P (P.supportExponent+1) (add_pos P.exponent_pos zero_lt_one)

variable {Q : BudgetPoint}{i : Scree.Hub n}{F:InkD n}
lemma editPress (z:PressB Q i F h a) (u:ℝ)(p:0<u): PressB (editRate Q u p) i F h a := by
 obtain ⟨x,v,t,j,G,f,T,w⟩:=z
 refine ⟨x,v,t,j,G,f,?_,w⟩
 intro V v k
 let Z:= T V v k
 exact ⟨Z.grade,Z.paid,Z.token⟩
lemma upsPress (z:PressB Q i F h a): PressB (ups Q) i F h a:= editPress z _ _

lemma onlyPositive {X:RegBudget n}{z:Sweep n → Prop}(u:IncX z X Q h a) : IncX (fun _=>False) (head_L X) Q h a := by
 obtain ⟨v,t,h⟩:=u.weight; exact ⟨⟨v,fun i=> easy_W Q (t i),h⟩,fun _ q=>q.elim⟩

variable (E:Pax n)(τ:Ids n) {v:Aura n→ℝ}(qE:Sym_a E)(p:Turf E)(s_:0≤h) (t:∀ i:Aura n, Vow.Medal P i.val ∅ (E i) h (v i))
local notation "Hz"=>Scree.Hub n
include t s_
lemma loanHigh(i:Aura n)(o:Seat n)(j:Hz)(p:lagE j=i): (ups P).mass j.val.2 (pence_Q P v j)≤ reserveT P.power P.order P.B 1 * (v i* Trees.currency P.B (P.supportExponent+1+1) i.val):=by
 let R:=reserveT P.power P.order P.B 1; let T:= i.val; let x:= pence_Q P v j; have hf:=t i; have hv:=hf.wage s_; have hx:0≤R:=by unfold R reserveT coin_n stilK; positivity
 have hp:j.val.2=i.val:= congrArg Subtype.val p; change (ups P).mass _ x ≤_; rw [show x=bassH i* (v i*fareX P.B P i.val) from ?_] -- x not folded tune
 swap; · unfold x pence_Q; rw [p,hp,mul_comm (Vow.fareX ..)]
 rw [hp]; let A:= (ups P).mass i.val (v i); unfold BudgetPoint.mass; have hU: 0≤ A:=mul_nonneg (Real.exp_pos _).le hv; have hh : (1:ℝ) ≤ (i.val.card:ℝ):= Nat.one_le_cast.mpr (card_pos.mpr i.property)
 calc
    _ ≤ A*fareX P.B P i.val:=by
       unfold A BudgetPoint.mass; rw [mul_assoc (Real.exp _)]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; refine mul_le_of_le_one_left (mul_nonneg hv (health_f ..)) ?_; exact inv_le_one_of_one_le₀ hh
    _ ≤ A*(R*Real.exp (1 *coverNumber P.B i.val)):=by exact mul_le_mul_of_nonneg_left (coinPay P _ 1 zero_lt_one) hU
    _ = R*(v i* Trees.currency P.B (P.supportExponent+1+1) i.val):= by unfold Trees.currency A BudgetPoint.mass R; simp only [ups, editRate]; rw [add_mul (P.supportExponent+1),Real.exp_add]; ring
include qE p
lemma worthHigh (u:∀ i:Seat n,tallB v P.B (P.supportExponent+1+1) i≤b): IncX Utrue (cast_E E τ) (ups P) h (reserveT P.power P.order P.B 1*b):=by
 let V:=pence_Q P v; refine ⟨⟨V,fun i => upsPress (dare_L P E τ p s_ t i),fun i=> ?_⟩,(worth_R P E τ qE p s_ t u).face ⟩
 let R:= reserveT P.power P.order P.B 1; let X:= univ.filter (fun j:Hz=>i=j.val.1); let G:= univ.filter (fun z:Aura n=>i∈z.val); apply le_trans _ (mul_le_mul_of_nonneg_left (u i) (show 0≤R from (by unfold R reserveT coin_n stilK; positivity)))
 rw [←sum_filter,←sum_fiberwise_of_maps_to (s:=X) (t:=G) (g:=lagE) (fun j p=>mem_filter.mpr ⟨mem_univ _, (mem_filter.mp p).2.symm ▸ j.property⟩), tallB,mul_sum]; apply sum_le_sum; intro j y; let Z:Hz:=⟨(i,j.val),(mem_filter.mp y).2⟩; have hk : lagE Z=j:=Subtype.ext rfl; rw [sum_eq_single_of_mem (s:=X.filter fun i=>lagE i=j) Z (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,rfl⟩,hk⟩)]; exact loanHigh P E s_ t j i Z hk
 intro v t' h; have hx:v=Z:= Subtype.ext (Prod.ext ((mem_filter.mp (mem_filter.mp t').1).2.symm) (congrArg Subtype.val (mem_filter.mp t').2)); exact False.elim (h hx)

end YM.CF.Ione
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate
open Forge Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Vow Salt
open Ione Beau Haro Cascade
open scoped Mew
open Mew
variable {X Y:Type*}{n:Side}{P:BudgetPoint}{h v w:ℝ}{F:RegBudget n}{K:ForceBudget n}{t:Cusp n}
open Pressure
open Push.AbsoluteSums Trees Ursell Push.AbsoluteSums.Graph Bake Gas Wray Larch Nor
variable {a s d δ γ:ℝ}{G H:Pax n}
variable (p:0<d)(vx:0≤a)(h':1≤h)
open Wray
-- sweep obligations. elementary linear algebra lemmas.
open Lilt
namespace Cash
variable {F G:Pax n}(τ:Ids n)(pL:MonoQ P h (prominence P) F w)(pA: poise F)

local notation "dF"=> due τ F
local notation "fQ"=> Cash.returnV τ P F
include h' pL pA
lemma priceRunHigh : IncX Utrue (Cash.earn τ P F) (ups P) h (reserveT P.power P.order P.B 1*(w+w)) ∧ Packed P h (prominence P) (Cash.owe τ F) w:=by
 obtain ⟨S,T,V⟩:= charter h' τ pL; have hc(X:Aura n):Vow.Medal P X.val ∅ (cashV dF X) h (S X):= (Medal.oneT.rum (dF X)).big (by rw [mul_one]; exact T X)
 have hg(x:Aura n):0 ≤ S x:=(norm_nonneg _).trans (T x); refine ⟨?_ ,S,⟨hg,fun i D v l=>Larch.nom_F h' P i _ (hc i) D ⟩,V⟩
 let H:MonoQ P h (prominence P) (F-cashV dF) (w+w):= pL.sub ⟨S,hc,V⟩; obtain ⟨L,b,q⟩:=H; exact worthHigh P fQ τ (booths τ pA).2 (booths τ pA).1 (zero_le_one.trans h') (fun i=>zen_B P (b i)) q
end Cash
end YM.CF.Py.Rate
