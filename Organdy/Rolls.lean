import Organdy.Owl
import Organdy.Boreal
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Sault Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive Vow.TreasuryFog Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Levier Tulip Lat Spire Tenant Salt
open QuadClock Py Neon
abbrev deepKick (n:Side):= Fintype.card (Seat n)+1

structure Tassel (p:BudgetPoint)(F:ForceBudget n)(q:ℕ)
   (h:ℝ)(σ:I→Seat n)(V:I→Bag n) where
  M:ℕ
  f:ℝ
  g:ℝ
  γ:ℝ
  full:I→Aura n→ℝ
  birth:I→Aura n→ℝ
  r:Aura n→Support (More n)→ℝ
  tumble:Tumble p h q F M f g γ σ V full birth r

namespace Tassel
variable {F:ForceBudget n}{σ:I→Seat n}{V:I→Bag n}
variable (w:Tassel p F q h σ V)
local notation "B₀"=> w.tumble.tine.toPollen
local notation "QP"=>w.tumble.pow.sleigh
local notation "τ₀"=> (Classical.arbitrary _:Ids n)
abbrev dresses := pend B₀
abbrev layer := lensCells F ((B₀).soar) (deepKick n)
abbrev faceL :=lensPort (P:=p) F (B₀).soar (deepKick n)
abbrev Ev:= awake σ (lensD (P:=p) F (B₀).soar (deepKick n) τ₀) (dresses w)
abbrev Fv:= bustle σ w.faceL

lemma weave (x:Key I)(e:x∈hill I):Unravel p (Jade.nixV (w.layer x)) h:=by
 let u:= urnL (paidLayers w.r (∑ i:I,w.full i) (∑ i:I,w.birth i) (deepKick n))
 let η:=(QP).η
 have l:= (QP).hη
 have g:= p.exponent_pos
 have ht:=w.tumble.tall
 refine ⟨w.tumble.paid.plain x _,p.B,p.supportExponent+η+η+η,(QP).γ,η,_,u,by unfold η; linarith,
   (rackMoney _ _ _ _ _ _ w.tumble.paid _ ht).1,?_⟩
 exact (layerSuit _ _ _ _ _ _ w.tumble.paid _ ht x e).1
end Tassel

section Gram
variable {N M:Side}
local notation "N₀"=>mid N M
variable {R:GramM (mid N M)}
variable {σ:I→Seat (mid N M)}{V:I→Bag (mid N M)}
variable {J:Type}[LinearOrder J][Fintype J]
variable {σ':J→Seat (mid N M)}{V':J→Bag (mid N M)}
variable (w:Tassel R.p R.K q h σ V)
         (y:Tassel R.p R.K q h σ' V')

lemma Tassel.vanguard (i:I):νTip w.Ev i=pend (w.tumble.tine.toPollen) i ∧
    emberTip w.Fv i=emberTip w.faceL i:=
 ⟨value_E .., (value_F σ _ i).trans (funext₂ fun _ _=> cue_1 ..)⟩
lemma Tassel.raygun (x:Force N₀)(u:Orbit N₀):
    River (fun z=>w.faceL z x u):=
 flows_K _ _ _ _ _ w.tumble.paid _ w.tumble.tall _ _

variable (s:Sweep (mid N M))(u:passingF (mid N M) s R.K R.K)
include u
lemma Tassel.bric
 (i:I) (j:J) (r:ℝ)(a:|r|≤1)
 (z:(boxA s).symm (σ i)=σ' j)
 (t:whirlB s (V i)=r • V' j):
   passingR N₀ s (νTip w.Ev i) (r • νTip y.Ev j) ∧
   passingF N₀ s (emberTip w.Fv i) (r • emberTip y.Fv j):=by
 rw [(w.vanguard i).1,(w.vanguard i).2,(y.vanguard j).1,(y.vanguard j).2]
 refine ⟨passingPend s w.tumble.tine.toPollen y.tumble.tine.toPollen r t z,?_⟩
 have d(x:ℝ)(g:|x|≤1):
     passingF N₀ s (w.faceL (realKey i x)) (y.faceL (realKey j (x*r))):=by
    have l:|x*r|≤1:=by rw [abs_mul]; exact mul_le_one₀ g (abs_nonneg _) a
    have m : passingU N₀ s (w.layer (realKey i x)) (y.layer (realKey j (x*r))):=
       passingLayer s R.K u _ _ (wist s w.tumble.tine.toPollen y.tumble.tine.toPollen r t x) _
    exact (MirrorBill.vest s _ _ m (w.weave _ (realKey_mem _ _ g))
       (y.weave _ (realKey_mem _ _ l)) w.tumble.tall).lamp 0 0 (fun _ _ _ _ _ _=> (map_zero _).symm)

 intro b c l
 exact turnAxis s i j _ _ (w.raygun b c) (y.raygun _ _) r fun x g=>d x g b c l
end Gram
end YM.CF.Organdy
