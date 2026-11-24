import Bay.C.Tuny
import Bay.Flare
import YM.SU5.Exchange.Seed.Pension
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay.C
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf



open Levier Urn Ione
open Peaks


open QuadClock TreasuryFog Mew
open scoped YM.CF.Mew
open Bake Salt
variable {I J:Type}[Fintype I][LinearOrder I][Fintype J][LinearOrder J]
variable {n:Side}{P:BudgetPoint}{q i:ℕ}{h:ℝ}{σ:I→Seat n}{τ:J→Seat n}

lemma mint_U {C:Occlus P}{F:ForceBudget n}
 {K:Key I→Rinse (Seat n) (Copy n)}
 {z b:Aura n→ℝ}{r:Aura n→Support (More n)→ℝ}
 {m:Key I→ Orbit n→ Aura n→ FC (Dwell n)}
 (p: OrbitRack C σ q F h K z b r m)(d:1≤h)(u:ℕ)
 {k:Key I}(v:k∈hill I):
 Unravel P (Jade.nixV (lensCells F K u k)) h:=by
 refine ⟨p.plain k u,P.B,_,_,_,_,_,?_,
       (rackMoney C F K σ q m p u d).1,(layerSuit C F K σ q m p u d k v).1⟩
 linarith only [P.exponent_pos,C.hη]

variable
  {m:I→ Sour.Bag n}{a l:I→Aura n→ℝ}
  (e:∀i, Orchard P q h (m i) (a i) (l i))
  (s:Sweep n)
  {M:J→Sour.Bag n}{A L:J→Aura n→ℝ}
  (g:∀ i, Orchard P q h (M i) (A i) (L i))
  (t:ℝ)

lemma flare_r (i:I) (X:Aura n)(D:Support (More n))(Y:Aura n)(m:Copy n)(x:Orbit n):
 flare e (realKey i t) X D Y m x=t • (Orchard.hyp (e i) X D Y m x):=by
 unfold flare; rw [Finset.sum_apply,sum_eq_single i]
 · rw [Pi.smul_apply,realKey,update_self];rfl
 · intro j _ k; rw [realKey,update_of_ne k,Pi.zero_apply,zero_smul];rfl
 simp

variable (i:I)(j:J){F:ForceBudget n}
lemma pin_S (u:ℕ)(p: Steering s (m i) (M j))(w:passingF n s F F):
 passingU n s
 (lensCells F (flare e) u (realKey i t))
 (lensCells F (flare g) u (realKey j t)):=by
 intro X x h D v
 refine tuny s (settleK F) _ _ x ?_ (fun Y D d=>settler s w Y x h D d) u X D v
 intro X D Y a b c
 rw[flare_r,flare_r,map_smul]
 exact congrArg (fun z:Cipher n=>t • z)
    (leaps s (asBias (e i).fullUp) (asBias (g j).fullUp) p D x X Y c)

variable {e s g t i j}
-- economical credits can differ M,m,F but must P,h,q and physical ForceBudget.
structure Chromatic {m:I→Sour.Bag n}{z r:I→Aura n→ℝ}
 (P:BudgetPoint)(q:ℕ)(h:ℝ)(F: ForceBudget n)
 (d:∀i,Orchard P q h (m i) (z i) (r i))(u:ℕ):Prop where
   high:1≤h
   born:∀k∈hill I, Unravel P (Jade.nixV (lensCells F (flare d) u k)) h
   spends(Q:Force n)(x):River (fun k=>lensPort (P:=P) F (flare d) u k Q x)

lemma pin_T {u:ℕ}(p:Steering s (m i) (M j))(w:passingF n s F F)
 (k:Chromatic P q h F e u)(b:Chromatic P q h F g u)(v:|t|≤1):
 passingF n s (lensPort (P:=P) F (flare e) u (realKey i t))
   (lensPort (P:=P) F (flare g) u (realKey j t)):=by
 exact (MirrorBill.vest s _ _
   (pin_S e s g t i j u p w) (k.born _ (realKey_mem _ t v)) (b.born _ (realKey_mem _ t v)) k.high).lamp 0 0
    (fun _ _ _ _ _ _=>(map_zero _).symm)

lemma pin_U {u:ℕ}(p:Steering s (m i) (M j))(w:passingF n s F F)
 (k:Chromatic P q h F e u)(b:Chromatic P q h F g u):
 passingF n s (Py.νΦK (lensPort (P:=P) F (flare e) u) {i})
   (Py.νΦK (lensPort (P:=P) F (flare g) u) {j}):=by

 intro X x ok
 unfold Py.νΦK
 simp only [Mew.gemI,Mew.Cue,Finset.sort_singleton] -- namespace
 let hx:= b.spends (moveForce s X) (yellA s x)
 rw [← one_smul ℝ (tipI _ [j])]
 apply turnAxis s i j _ _ (k.spends _ _) hx 1
 intro z v
 rw [mul_one]
 exact pin_T p w k b v X x ok
