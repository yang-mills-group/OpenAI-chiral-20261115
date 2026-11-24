import Bay.FlowBank
import YM.SU5.Exchange.Seed.Pip
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



/-- (52), core and chose. A full Press schedule excludes either,
   prices at ordinary power (may upgrade core power anyway). -/
abbrev mind (P:BudgetPoint) (x:Seat n):=Lattice.halo (10000*P.B) {x}
abbrev mine (P:BudgetPoint)(x:Seat n):Scree.Hub n:=
 ⟨(x,mind P x),Lattice.halo_spec.mpr ⟨x,Finset.mem_singleton.mpr rfl,by rw [separation_self]; omega⟩⟩
abbrev outmint (P:BudgetPoint)(L:ℕ)(x:Seat n)(Y: Support (More n)): Prop:=
   x∈Y ∧ L ≤ (coverNumber P.B Y)^3 ∧ ¬ (Y⊆ mind P x)
abbrev bracer (P:BudgetPoint):ℝ:=(1+(P.B:ℝ))^100
abbrev fired (o:Seat n)(P:BudgetPoint)(L:ℕ)(X:Scree.Hub n):Prop:=
  X.val.1=o∧outmint P L o X.val.2

/-- price of E. (Can widen to ANY power/core on request, core is literally zero.) -/
structure Dagger (P:BudgetPoint)(L:ℕ)(x:Seat n)(F:RegBudget n)(h W:ℝ):Prop where
  sheathed : ∃ l:Scree.Hub n→ℝ,
   (∀ X,0≤l X ∧ PressB P X (F X) h (l X) ∧
     (¬fired x P L X → l X=0 ∧ F X=0)) ∧ 
   bracer P * (∑ i:Scree.Hub n,P.mass i.val.2 (l i)) ≤ W


namespace Dagger
variable {L:ℕ}{x:Seat n}{F:RegBudget n}{W h:ℝ}
lemma raise (d:Dagger P L x F h W){W':ℝ}(p:W≤W'):Dagger P L x F h W':=
 match d.sheathed with | ⟨_,u,v⟩=> ⟨_,u,v.trans p⟩
lemma ax (d:Dagger P L x F h W):
 IncX primeU F P h W∧
   (∀ X:Scree.Hub n,X.val.1≠x→ F X=0) ∧
   (∀ X:Scree.Hub n,Moto.chose L P X→ F X=0):= by
 obtain ⟨g,k,t⟩:= d.sheathed
 refine ⟨⟨⟨g,fun X=>(k X).2.1,fun y=>?_⟩,fun _ u=>u.elim⟩,fun X z=>
    ((k X).2.2 (fun w=> z w.1)).2,fun X z=> ((k X).2.2 ?_).2⟩
 · have e(i:Scree.Hub n):0 ≤ P.mass i.val.2 (g i):=
     mul_nonneg (Real.exp_pos _).le (k i).1
   
   have r:1 ≤ bracer P:=one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))
   exact (sum_le_sum (fun i _=> by split; exact le_rfl; exact e i)).trans
      ((le_mul_of_one_le_left (sum_nonneg fun i _=>e i) r).trans t)

 · exact fun w=> Nat.not_lt.mpr w.2.2.1 z


-- Axon on node. flair zero from stillQ.
lemma axon {N B:Side} {x:Site (mid N B)} {F:RegBudget (mid N B)}
 (d:Dagger P L (node x) F h W):
 Neon.Axon L x P F h W 0:=by
 obtain ⟨k,o,v⟩:=d.ax
 refine ⟨k,o,fun X g=>?_⟩
 rw [v X g,ite_self]
 exact (by exact ⟨(stillQ x P).1, Prod.ext (stillQ x P).2.1 (stillQ x P).2.2⟩)

-- Chapter compatibility: fee assertion for CoreBoost, state as bundled perhaps
end Dagger

/-- receipt directly usable even on higher cap version:
 A first Reg Outer-version price of (52) with core = 0, any secondary Budget.
 includes optional case P itself. -/
structure XIIbill (P:BudgetPoint)(x:Seat n)(F: RegBudget n)(h W:ℝ):Prop where
  core : ∀ S:BudgetPoint, PressB S (mine P x) (F (mine P x)) h 0
  attics : ∃ l:Scree.Hub n→ℝ, (∀ X,
    0≤l X ∧ PressB P X (F X) h (l X) ∧ 
    (X.val.1≠x ∨ X.val.2⊆mind P x → F X=0 ∧ l X=0)) ∧
    bracer P * (∑ i:Scree.Hub n,P.mass i.val.2 (l i)) ≤ W

lemma Dagger.bill {L:ℕ}{x:Seat n}{F:RegBudget n}{W h:ℝ}
 (d:Dagger P L x F h W):XIIbill P x F h W:=by
 obtain ⟨l,H,J⟩:=d.sheathed
 refine ⟨fun S=>?_,l,fun i=>⟨(H i).1,(H i).2.1,fun t=>
    and_comm.mp ((H i).2.2 (fun p=>t.elim (fun g=>g p.1) (fun g=>p.2.2.2 g)))⟩,J⟩
 rw [((H (mine P x)).2.2 (fun g=>g.2.2.2 le_rfl)).2]
 exact Vale.rinse ..
-- Extra prices
variable {q:ℕ}{h:ℝ}
namespace Orchard
variable {v:Sour.Bag n} {c r:Aura n→ℝ}
variable (g:Orchard P q h v c r)


variable (o:Seat n)
open Bake

-- choose default tag (value independent)
def petalReg (o:Seat n)(g:Orchard P q h v c r)(t:Ids n):RegBudget n:=
 fun X=>if X.val.1=o then (fun V=> g.budL (lagE X) (V,t)) else 0

lemma angled (u:3 ≤ P.B)(p:0≤h)(τ:Ids n)
 (X:Scree.Hub n):
 PressB P X (fun V=>g.budL (lagE X) (V,τ)) h
     (fareX P.B P X.val.2 * r (lagE X)) := by
 let W:InkD n:=fun V=>g.budL (lagE X) (V,τ)
 have h:=g.budFray u p (lagE X)|>.merit
 rw [show g.budL (lagE X)=oV W from funext (fun U=>g.budLease _ U τ)] at h
 exact h.preservesE τ p P.B


open Nor
lemma repaid {s a R:ℝ}(u:3 ≤ P.B)(p:0≤h)(t:Ids n)(a0:0<a)
 (e:P.supportExponent+a ≤ s)
 (L:ℕ)
 (outer:∀ X:Aura n,v X≠0→ outmint P L o X.val)
 (fee:voyageB r P.B s ≤ R):
 Dagger P L o (petalReg o g t) h (bracer P * (reserveT P.power P.order P.B a * R)):= by
 let qX (X:Scree.Hub n):=fareX P.B P X.val.2 * r (lagE X)
 have hr(X:Aura n):0≤r X:=(g X).forms.choose_spec.1.price
 let l(X:Scree.Hub n):= if fired o P L X then qX X else 0
 refine ⟨l,fun X=>?_,?_⟩
 · unfold l
   let K:= (petalReg o g t) X
   by_cases m:fired o P L X
   · rw [if_pos m]
     refine ⟨mul_nonneg (health_f ..) (hr ..),?_,fun w=>False.elim (w m)⟩
     rw [petalReg,if_pos m.1]; exact angled g u p t _
   rw [if_neg m]
   have z:K=0:=by
      unfold K; rw [petalReg]; split
      · rename_i k
        have h : v (lagE X)=0:=Classical.byContradiction (fun w=>m ⟨k,outer _ w⟩)
        have h0:g.budL (lagE X)=0:=lampOff g.fullUp _ _ _ h _
        funext Y;rw[h0]; rfl
      rfl

   exact ⟨le_rfl,show PressB P X K h 0 from by rw [z]; exact Vale.rinse ..,fun _=>⟨rfl,z⟩⟩

 let T:=reserveT P.power P.order P.B a
 have ht:0≤T:=by unfold T reserveT coin_n stilK; positivity
 let G:=univ.filter fun Y:Scree.Hub n=>fired o P L Y
 let V(Y:Aura n):=T * (r Y * Sour.tact s P.B Y)
 have hp(i:Scree.Hub n): P.mass i.val.2 (qX i) ≤ V (lagE i):=by
    let Y:= lagE i
    have hx: 0≤ P.mass i.val.2 (r Y):= mul_nonneg (Real.exp_pos _).le (hr _)
    calc
      _ = P.mass i.val.2 (r Y)*fareX P.B P i.val.2:= by unfold BudgetPoint.mass qX Y;ring
      _ ≤ P.mass i.val.2 (r Y)*(T*Real.exp (a*coverNumber P.B Y.val)):=mul_le_mul_of_nonneg_left (coinPay P _ a a0) hx
      _ = T * (r Y * Sour.tact (P.supportExponent+a) P.B Y):= by 
          unfold BudgetPoint.mass Sour.tact;rw [add_mul,Real.exp_add]; change
            (Real.exp _ * r Y)*(_*Real.exp _) = T*(r Y*(Real.exp (P.supportExponent * ↑(coverNumber P.B i.val.2))*Real.exp (a * ↑(coverNumber P.B Y.val))))
          ring
      _ ≤ V _:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (tact_para e _) (hr _)) ht

 apply mul_le_mul_of_nonneg_left _ (show 0 ≤ bracer P by unfold bracer;positivity)
 have he:Set.InjOn (lagE (n:=n)) G:=by
    intro i h j g z; exact Subtype.ext (Prod.ext
      ((mem_filter.mp h).2.1.trans (mem_filter.mp g).2.1.symm)
      (congrArg Subtype.val z))
 calc
   _=∑ i∈G,P.mass i.val.2 (qX i):= by
       rw [sum_filter]
       exact sum_congr rfl (fun i _=> by unfold BudgetPoint.mass l; split<;>[rfl;rw [mul_zero]])
   _ ≤ ∑ i∈G,V (lagE i):= sum_le_sum fun i _=>hp i
   _ = ∑ i∈ G.image lagE,V i:=(Finset.sum_image he).symm
   _ ≤ ∑ i,V i:= sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>mul_nonneg ht (mul_nonneg (hr _) (Real.exp_pos _).le))
   _ ≤ _:=by unfold V; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left fee ht
end Orchard

section
open Bake
variable {I:Type}[LinearOrder I][Fintype I]
 {v:I→Sour.Bag n}{c r:I→Aura n→ℝ}

abbrev kilnTip (p:∀ i,Orchard P q h (v i) (c i) (r i))(σ:I→Seat n)
 (τ:Ids n)(i:I):RegBudget n:=Orchard.petalReg (σ i) (p i) τ

lemma kBud (F:I→ Cipher n)(i:I) :
 tipI (fun z=>∑ j:I,z j • F j) [i]=F i:=by
 have t(j:I)(z:Mew.Key I):pine {j} z=z j:=prod_singleton (a:=j) ..
 simp_rw [show ∀ (j:I)(z:Mew.Key I),z j • F j=pine {j} z • F j
    from fun j z=>by rw [t]]
 rw [show tipI _ _= _ from (tip_bank univ (fun j z=>pine {j} z • F j)
      (fun _ _=>lift_b _ _)).2 [i]]
 simp only [tip_tape _ (by simp:[i].Nodup)]
 simp

variable (σ:I→Seat n)(p:∀ i,Orchard P q h (v i) (c i) (r i))
lemma sparksRaise (zσ:Tether σ v)(τ:Ids n)(i:I) :
 SpanTip P (kilnTip p σ τ i) (σ i) (flare p) τ i:=by

 have e(X:Aura n)(u:Orbit n):tipI (fun z=>flare p z X ∅ X 1 u) [i]=(p i).budL X u:=by
    simp only [flare, Finset.sum_apply, Pi.smul_apply]; exact kBud (fun j=>Orchard.hyp (p j) X ∅ X 1 u) i
 refine ⟨fun X U _=>?_,fun X U _ k=>?_⟩
 · rw [e (lagE X),kilnTip,Orchard.petalReg]
   split<;>rfl
 rw [e,Orchard.budL,Orchard.hyp,lampOff (p i).fullUp _ _ _ (zσ i _ k)]
 rfl


end
end YM.CF.Bay
#print axioms YM.CF.Bay.sparksRaise
