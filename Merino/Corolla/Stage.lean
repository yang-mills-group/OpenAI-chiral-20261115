import Merino.Corolla.Follies
import Merino.Corolla.Honey
import Merino.Corolla.Visits

set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 360000
noncomputable section
namespace YM.CF.Merino.Corolla
open Finset Lattice RG Scree Skye Vow
open scoped Topology Classical Matrix Matrix.Norms.L2Operator
open Cadre Sour Push.AbsoluteSums.Trees Vow.TreasuryFog
open Cube Stax Mew Fock
open scoped YM.CF.Mew

variable {I:Type}[LinearOrder I][Fintype I]
variable {n:Side}{P:BudgetPoint}{q:ℕ}{h:ℝ}

open Rill Rue


open Roots Rive
structure Progress (P:BudgetPoint)(q:ℕ)(h:ℝ)(σ:I→Seat n)(y:I→Bag n)(c d:I→Aura n→ℝ)(a b:ℝ): Prop extends Sep P q h σ y c d where
 spare:∀ i X, σ i∉X.val→ c i X=0∧d i X=0
 wedge:∀ i, voyageB (c i) P.B (eighth P.B)≤a∧ voyageB (d i) P.B (eighth P.B)≤b
variable {σ:I→Seat n}{y:I→Bag n}{e f:ℝ}
lemma rooted (k:∀i,Barrage P q {σ i} h (y i) (eighth P.B) e f):
 ∃ c d,Progress P q h σ y c d e f:=by
 choose c d w using fun i=> (k i).price
 exact ⟨c,d,⟨fun i=>(w i).1,fun i X h=> ((w i).2.1 X (by rwa [singleton_subset_iff])).1⟩, fun i X h=> ((w i).2.1 X (by rwa [singleton_subset_iff])).2,fun i=> (w i).2.2⟩


/-- Caps to equip the rack. -/
structure Girdle (P:BudgetPoint)(h:ℝ)(a b v g:ℝ)(m:ℕ):Prop extends Thimble P g where
 upright : 1≤h
 levy : 3 ≤ P.B
 room : lapel P.B≤P.supportExponent+1/2
 honey : chi_f P.order*v<g
 cloth : visits m P.B*a ≤ zpay P.B
 tag : visits m P.B*b ≤ bpay P.B g
 waist : 0 ≤ a
 ankle : 0 ≤ b

variable {c d:I→Aura n→ℝ}
lemma mz (c:I→Aura n→ℝ): meterZ c = ∑j,c j:=by
 funext X; exact (Finset.sum_apply ..).symm

theorem hem {v g:ℝ}{m:ℕ}{F:ForceBudget n}
 (k:Force_M P.B σ m)
 (s:Girdle P h e f v g m)(w:Progress P q h σ y c d e f)
 (u:FlagWidth P F (cipherK q))
 (x: SanB F (giftK P (P.supportExponent+(1:ℝ)/2)) P h (fun _=> v)):
 ∃ r, OrbitRack (till s.toThimble) σ q F h w.toSep.stripe (meterZ c) (meterZ d) r (scores y):=by
 have hh:= zero_le_one.trans s.upright
 obtain ⟨r,hr,hR⟩:=repast P F s.room hh s.honey u x
 let S:=w.toSep
 have p(a i):= S.staged a i hh s.levy
 refine ⟨r,hr, fun a v=>(p a v).1, fun a v=>(p a v).2,S.gam,fun u X D _=>S.turn F u X D,fun a m=> S.plain a F m,fun u=>S.void F u,?_⟩

 exact escapement s.toThimble _ _ _ (fun X=>sum_nonneg fun i _=>(S.sign i X).1)
    (fun X=>sum_nonneg fun i _=>(S.sign i X).2) (fun X D e=>(hr X D e).merit.wage hh)
    ⟨fun i=> by
       rw [mz]
       exact (richVisits _ _ k i _ _ s.waist (fun x y=>(S.sign x y).1)
         (fun a b z=>not_not.mp fun l=>z (w.spare _ _ l).1) (fun i=>(w.wedge i).1)).trans s.cloth,
     fun i=> by
       rw [mz]
       exact (richVisits _ _ k i _ _ s.ankle (fun x y=>(S.sign x y).2)
         (fun a b z=>not_not.mp fun l=>z (w.spare _ _ l).2) (fun i=>(w.wedge i).2)).trans s.tag,
     hR⟩
end YM.CF.Merino.Corolla
