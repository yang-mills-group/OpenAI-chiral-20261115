import YM.SU5.Exchange.Seed.Pension
import Organdy.Apse
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

open Py QuadClock Neon Roots
structure PortRates {p:BudgetPoint}(C:Occlus p)(t:ℕ)
  (X W:ℝ)(f ν ν₁:ℝ):Prop where
  rise:0≤X
  radius:1 ≤ W
  grows:2*W ≤ Real.exp X
  gate:9*X*t≤ C.η/2*(p.B:ℝ)^2
  fee:0≤f
  yF:0≤yσF p C
  label:W*f ≤ν₁
  fixed:W*yσF p C ≤ ν₁
  moon:TreasuryFog.sigma C.η p.B * yσF p C ≤ ν
  solar:TreasuryFog.sigma (C.η+C.η) p.B * yσE p C ≤ ν


open Roots Neon QuadClock Py
variable {N B₁:Side}{L:Side}
local notation "n₁"=>mid N B₁
variable (o:I→Site (mid N B₁)) 
variable {R:GramM (mid N B₁)}
variable (C:Occlus R.p)
variable (K : Key I→ Rinse (Seat (mid N B₁)) (Copy (mid N B₁))) {ζ β: Aura (mid N B₁)→ℝ} {r:Aura (mid N B₁)→Support (More (mid N B₁))→ℝ}
variable (q:ℕ)(M:Key I→ Orbit (mid N B₁)→ Aura (mid N B₁)→ FC (Dwell (mid N B₁))) (T:OrbitRack C (node ∘ o) q R.K h K ζ β r M) (s:ℕ)(v:1≤h)(τ:Ids (mid N B₁))
variable {t:ℕ}(W: Force_M R.p.B (node ∘ o) t)
local notation "DK"=>lensD (P:=R.p) (R.K) K s τ
local notation "DV"=>lensPort (P:=R.p) (R.K) K s
local notation "σ'" => (node ∘ o)
local notation "Y₁" => yσE R.p C
local notation "Y₂" => yσF R.p C

include T v
private lemma fixFuel (i:I): FixedF R.p h Y₂ (νΦK DV {i}):=by
 let τ:Ids n₁:= Classical.arbitrary _
 have l z w:=lowLens C R.K K σ' q M T s v τ z w
 exact fixedService σ' _ (sealF C K σ' q M T s v) C.η C.hη.le (zero_lt_one.trans_le v) _ (fun z w=>(l z w).2.1) (l 0 roots).2.2 _

include W
lemma buoyancy {X A f ν ν₁:ℝ}(r:PortRates C t X A f ν ν₁)
      (m:ℕ)(E:I→RegBudget n₁)
      (α:I→ArcΦ)
      (e:∀ i:I,Axon m (o i) R.p (E i) h f (α i)):
     PanoramaBill R.p h A ν ν₁ (awake σ' DK E) (bustle σ' DV):=by
 intro z w
 let Y(i:I):= νΦK DV {i}
 have hv:=zero_lt_one.trans_le v
 have cap {g} (x:0≤g) (u:A*g ≤ν₁):(∑ i:I,‖z i‖*g) ≤ ν₁* Fintype.card I:=by
   refine (Finset.sum_le_sum (g:=fun _=>ν₁) (fun i _=> (mul_le_mul_of_nonneg_right (w i) x).trans u)).trans (le_of_eq ?_)
   rw [sum_const,nsmul_eq_mul,card_univ,mul_comm]
 have hx:bustle σ' DV z=(∑ i:I,z i • Y i)+mixedForce σ' DV z:=by
    unfold bustle mixedForce
    rw [sumOpen]
    simp [Mew.pine,Y]
 refine ⟨_,rim_C σ' DK z,_,_,rfl,hx,(sum_FixedE E (fun _=>f) z (fun i=>Axon_fixedE (e i) hv.le)).more (cap r.fee r.label),
   (sum_FixedF Y (fun _=>Y₂) z (fun i=>fixFuel o C K q M T s v i)).more (cap r.yF r.fixed),?_,?_⟩ -- E metavars explicit? 

 · refine Provides.liftE h R _ _ ?_ r.solar
   have l(z t):=(lowLens C R.K K σ' q M T s v τ z t).1
   have ht : 9*X*t ≤ ((C.η+C.η)/2)*(R.p.B:ℝ)^2:=
     r.gate.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_add_of_nonneg_right C.hη.le) (by norm_num)) (sq_nonneg _))
   refine manyBudget σ' W _ (sealE C K σ' q M T s v τ) z A w _ X r.radius r.grows r.rise (add_nonneg C.hη.le C.hη.le) hv _ (fun i t=>(l i t).1) ?_ ht
   rw [←add_assoc]
   exact (l 0 roots).2
 · refine Provides.liftQ h R _ _ ?_ r.moon
   have l(z t):=(lowLens C R.K K σ' q M T s v τ z t).2
   exact mixedService σ' W _ (sealF C K σ' q M T s v) z A w _ X r.radius r.grows r.rise C.hη.le hv _ (fun z w=>(l z w).1) (l 0 roots).2 r.gate
end YM.CF.Organdy
