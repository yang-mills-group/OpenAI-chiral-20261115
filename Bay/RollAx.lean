import Bay.Dagger
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf
open Mew PowerSeries
open scoped YM.CF.Mew
variable {n:Side} {P:BudgetPoint}

open TreasuryFog Roots Py Moto


variable {J:Type} [LinearOrder J][Fintype J]
local notation "Η"=> Scree.Hub n
variable {h Γφ:ℝ}
section

variable (P)(σ:J→Seat n)(tT:ℕ) (hX:1 ≤ h)
variable (E:J→ RegBudget n)(pc:Force_M P.B σ tT) 
 (q_ν:∀ i, IncX primeU (E i) P h Γφ 
   ∧ (∀X:Scree.Hub n, X.val.1≠σ i → E i X=0))
include pc q_ν hX
lemma lean_D (z:Key J)(u:∀ i, ‖z i‖ ≤ 2)(hB:0≤ Γφ): IncX primeU (∑ i:J,z i • E i) P h (2*Γφ*tT):=by
 choose G p w using fun i=>(q_ν i).1.weight; let L(j:J)(x:Η):= if x.val.1=σ j then G j x else 0
 have hv:=zero_le_one.trans hX; have hz(i:J)(x:Η):PressB P x (E i x) h (L i x):=by unfold L; split; exact p ..; next t=> rw [show E i x=0 from (q_ν i).2 _ t]; exact Vale.rinse ..
 let v(x:Η):=∑ i:J,‖z i‖ * L i x; refine ⟨⟨v,fun x=>?_,fun r=>?_ ⟩,fun _ p=>p.elim⟩
 · rw [Finset.sum_apply]; exact Larch.prop_sum univ _ _ _ _ x (fun j _=>súe _ _ (hz ..) (z j)) -- tune
 let I:=univ.filter fun i : J=> σ i=r; have he:I.card ≤tT:=(card_le_card (show I⊆ _ from ?_)).trans (pc.2 r)
 swap; · intro k t; refine mem_filter.mpr ⟨mem_univ _,?_⟩; rw [(mem_filter.mp t).2,separation_self]; omega
 rw [←sum_filter]; let U:= univ.filter fun x:Η=>r=x.val.1
 have hp(x:Η)(b:x∈ U): v x= ∑ i∈ I,‖z i‖* L i x:= Eq.symm (Finset.sum_subset (filter_subset ..) fun i _ q=> by unfold L; rw [if_neg (fun e=> q (mem_filter.mpr ⟨mem_univ _, e.symm.trans (mem_filter.mp b).2.symm⟩)),mul_zero])
 refine (le_trans ?_ (show (I.card:ℝ)*(2*Γφ)≤_ from (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr he) (mul_nonneg (by norm_num) hB)).trans_eq (mul_comm ..))); rw [← nsmul_eq_mul, ←sum_const]; calc
    (∑ i∈ U,P.mass i.val.2 (v i)) = ∑ i∈U,∑ j∈I,‖z j‖* P.mass i.val.2 (L j i):=by
       refine sum_congr rfl fun i p=>?_ ; unfold BudgetPoint.mass; rw [hp i p,Finset.mul_sum]; exact sum_congr rfl fun j _=>mul_left_comm ..
    _ ≤ _:=by
       rw [Finset.sum_comm]; refine sum_le_sum fun i x=>?_ ; rw [←Finset.mul_sum]; have ht:∑ j∈ U,P.mass j.val.2 (L i j) ≤ Γφ:=by
          apply le_trans ?_ (w i r); rw [←sum_filter]; apply sum_le_sum; intro j p; rw [show L i j= G i j from if_pos ((mem_filter.mp p).2.symm.trans (mem_filter.mp x).2.symm)]
       exact (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans (mul_le_mul_of_nonneg_right (u i) hB)


end


def Quince(W:Type)[AddCommMonoid W][Module ℂ W](σ:J→Seat n)(E:Mew.Key J→W):Prop:=
 ∃ f:Finset J → W,∀ z,E z=∑ S∈trueSet σ,pine S z • f S

def spake (E:Mew.Key J→ RegBudget n)(G:J→RegBudget n)(T:Finset J) :RegBudget n:=
 if u:T.card=1 then G (Classical.choose (Finset.card_eq_one.mp u)) else νΦX E T

lemma quinceE (σ:J→Seat n)(E:Mew.Key J→RegBudget n)(G:J→RegBudget n):
 Quince _ σ (awake σ E G):=by
 refine ⟨spake E G,fun z=>?_⟩

 have h(i:J):spake E G {i}=G i:=by
   unfold spake
   have p:({i}:Finset J).card=1:=card_singleton _
   rw [dif_pos p]
   exact congrArg G (Finset.singleton_injective (Classical.choose_spec (card_eq_one.mp p))).symm
 rw [awake,sumOpen]
 refine congrArg₂ (·+·) ?_ ?_
 · simp only [Mew.pine,prod_singleton,h]; rfl
 unfold rim_C
 apply sum_congr rfl
 intro i t
 rw [spake, dif_neg (ne_of_gt (mem_filter.mp t).2.1)]

open QuadClock

structure BillRoll (σ:J→Seat n) (E:Mew.Key J→RegBudget n)(K:Mew.Key J→ForceBudget n):Prop where
 roll: E 0=0 ∧ K 0=0
 col: ∀ x: Scree.Hub n,Quiet σ x.val.2 (fun z=> E z x)
 varE: ∀ x y, Differentiable ℂ (fun z:Mew.Key J=> E z x y)
 joinF: ∀ i:Force n,Quiet σ i.val.1.val.2 (fun z=> K z i)
 varF: ∀ x y, Differentiable ℂ (fun z:Mew.Key J=> K z x y)
 head: ∀ i:J, ∀ w:ℂ, E (update 0 i w)=w • νTip E i ∧ K (update 0 i w)=w • emberTip K i
-- uses Topic while seating labels. Repetition OK (2 uses per call). W multiple =1 unit qualification, or 2 for stronger. H price. Real Ξ.

variable {N B₁:Side}{R:GramM (mid N B₁)}
lemma BillRoll.noticed {o:J→Site (mid N B₁)}
 {E:Mew.Key J→RegBudget (mid N B₁)}{K:Mew.Key J→ForceBudget (mid N B₁)}
 (b:BillRoll (node ∘ o) E K):Notice o E K:=
 ⟨b.roll,b.col,b.varE,b.joinF,b.varF,b.head⟩
local notation "n1"=>mid N B₁
variable {I:Type}[LinearOrder I][Fintype I]
variable (C:Occlus R.p)
variable (F:ForceBudget (mid N B₁))(K : Mew.Key I→ Rinse (Seat (mid N B₁)) (Copy (mid N B₁))) {z b: Aura (mid N B₁)→ℝ} {r:Aura (mid N B₁)→Support (More (mid N B₁))→ℝ}
variable (σ:I→Seat (mid N B₁))(q:ℕ)(M:Mew.Key I→ Orbit (mid N B₁)→ Aura (mid N B₁)→ FC (Dwell (mid N B₁))) (T:OrbitRack C σ q R.K h K z b r M) (s:ℕ)(p:1≤h)(τ:Ids (mid N B₁))
local notation "Ψg"=>lensG (P:=R.p) (R.K) K s
local notation "DK"=>lensD (P:=R.p) (R.K) K s τ
local notation "DV"=>lensPort (P:=R.p) (R.K) K s
local notation "Θ"=>lensCells (R.K) K s
local notation "η"=>layerRay C R.K K σ q M T s p
local notation "Υ"=> Phys n1
local notation "P'"=> (settleK R.K)
open Bake Spire Dial
include p T

variable (L:ℕ)(E:I→ RegBudget (mid N B₁))(C0:ℝ)
variable (Q:∀ i, Dagger R.p L (σ i) (E i) h C0)
include Q
local notation "Vξ"=> awake σ DK E
local notation "Vζ"=> bustle σ DV
lemma displayD : BillRoll σ Vξ Vζ ∧ (∀ i:I,νTip (Vξ) i=E i ∧ emberTip Vζ i = νΦK DV {i}):=by
 let e0:= sealE C K σ q M T s p τ; let f0:= sealF C K σ q M T s p; have a(j:I)(X:Scree.Hub n1)(v:E j X≠0):σ j∈ X.val.2:=by
    have h: X.val.1=σ j:=of_not_not (fun t=>v ((Q j).ax.2.1 _ t)); rw [←h]; exact X.property
 have he(i:I):νTip (awake σ DK E) i=E i:=value_E σ E DK i
 have hf(i:I):= value_F σ DV i
 refine ⟨⟨cash0 σ E DK DV, fun i=> ?_,eReady σ E DK,fun i=> ?_, fReady σ DV, fun i w=> by rw [he,hf]; exact ⟨crest_E σ E DK i w,crest_K σ DV i w⟩⟩,fun i=>⟨he i,hf i⟩⟩
 · have ht:= quietE σ E DK e0 a i -- Notice takes Quiet with node composition
   -- exact map Λ.Not R.J.De.Ωx
   exact ht
 have hv:= quietF σ DV f0 i; exact hv
lemma loans {t:ℕ}(a:ℝ)(hx:4 ≤ Real.exp a)(hA:0 ≤ a)(hv:9*a*t ≤ C.η*(R.p.B:ℝ)^2)(W: Force_M R.p.B σ t)(hC:0 ≤ C0): ∀ z':Mew.Key I,(∀ i, ‖z' i‖≤2) →
   IncX primeU (awake σ (lensD (P:=R.p) R.K K s τ) E z') R.p h ((2*C0*t)+sigma (C.η+C.η) R.p.B*yσE R.p C) ∧ Dark primeU (bustle σ (lensPort (P:=R.p) R.K K s) z') R.p h (Real.exp (a*t)*yσF R.p C):=by
 intro z hp; have hz:= many_e C K σ q M T s p τ z hp a hx hA hv W; have he:= lean_D R.p σ t p E W (fun i=> ⟨(Q i).ax.1,(Q i).ax.2.1⟩) z hp hC
 have hg:= force_inc C K σ q M T s p z hp a hx hA (show 6*a*t≤ _ from (le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num : (6:ℝ) ≤ 9) hA) (Nat.cast_nonneg t)) hv)) W
 exact ⟨Larch.add_v _ _ _ he hz, hg⟩
end YM.CF.Bay
