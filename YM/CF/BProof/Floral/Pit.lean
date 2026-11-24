import YM.CF.Rue.Coin
import YM.CF.BProof.Floral.Pear
import YM.CF.BProof.Floral.Nary
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floral
open Function NormedSpace Filter Metric Lattice Wilson MeasureTheory RG Fock
open Tenant Pastry Skye Scree Cube Spire Tulip Scroll
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {L:ℝ}
def pick {X:Type*}[Sub X] (F:ℂ→X)(x:Points L):X:=Option.elim x (F 1-F 0) (fun v=>F v)
lemma pick_apply {I X:Type*}[Sub X](F:ℂ→ I→X)(x:Points L)(i:I):pick F x i=pick (fun z=>F z i) x:=by cases x <;> rfl
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{F:ℂ→ E→ℂ}
lemma iter_pup (p:1<L)(x:Points L){j:ℕ}(y:E)(T:∀ z∈disk L, ContDiffAt ℝ (j:WithTop ℕ∞) (F z) y)(v:Fin j→E): pup x (fun z=>iteratedFDeriv ℝ j (F z) y v)=iteratedFDeriv ℝ j (pick F x) y v:=by
 cases x; swap; · rfl
 rw [pupd]; change _= iteratedFDeriv ℝ j (F 1-F 0) y v; rw [iteratedFDeriv_sub_apply (T _ (d1 p)) (T _ (d0 p))]; rfl
open Jet
variable {n:Side}{Y:Set (Pane n)}{I:Finset (Pressure.Bond (More n))}{G:ℂ→Pane n→ℂ}{P:BudgetPoint}{o:Seat n}
section Signs
open Forge
variable {C:ℝ}(s:IsOpen Y)(m:∀ x∈Y,∀ z∈disk L, Signs P o (G z ∘ gyrate I x) C)(g:∀ x∈Y,Hol (disk L) (fun z=> G z x))
include s m g
lemma stokes (u:1<L)(U:Pane n)(w:U∈Y){j:ℕ}(v:Fin j→ tangD n)(p:j≤P.order):Hol (disk L) (fun z=>iteratedFDeriv ℝ j (G z ∘ gyrate I U) 0 v):=by
 let V(x):= gyrate I U x; let X:= V ⁻¹' Y ∩ ball 0 1; have he:0∈X:= ⟨by unfold V; simpa [born], mem_ball_self zero_lt_one⟩
 let K:=composeCost P.order C ‖Prism.silo P o‖; obtain ⟨A,h,H⟩:= Arbor.lime (α:=Unit) (E:=ℂ) SU.group I P.order 1 K (Rue.price_s (m U w 0 (d0 u))).nonneg
 refine hol_iterated (fun z=> G z ∘ V) isOpen_ball ((s.preimage (stickU ..)).inter isOpen_ball) (fun y (p:y∈X)=>g (V y) p.1) (C:=A) (fun y (p:y∈X) z k=>?_ ) p 0 he v
 apply @H Y (fun _=> G z) ?_ () U y p.1 p.2; intro U i a; have ht:= Rue.price_s (m U i z k); exact ⟨Warm.simple _ ht.smooth,ht⟩
lemma bed_rule (u:1<L)(U:Pane n)(w:U∈Y): Rule fun (x:Points L) c=> Signs P o (pick (fun z=> G z ∘ gyrate I U) x) c :=by
 let F(z:ℂ):= G z ∘ gyrate I U; have ht(z)(e:z∈disk L):ContDiffAt ℝ P.order (F z) 0:= (m U w z e).paid
 let V(j):={v:Fin j→tangD n// ∀ i,P.dirBound o (v i)}
 let K:=Σ j:Fin (P.order+1),V j.val
 let T (i:K)(z:ℂ):=iteratedFDeriv ℝ i.1.val (F z) 0 i.2.val
 have hh(i:K):Hol (disk L) (T i):=stokes s m g u U w i.2.val (Nat.le_of_lt_succ i.1.isLt)
 have he(x:Points L)(i:K): pup x (T i) = iteratedFDeriv ℝ i.1.val (pick F x) 0 i.2.val:= iter_pup u x 0 (fun z h=>(ht z h).of_le (by exact_mod_cast Nat.le_of_lt_succ i.1.isLt)) i.2.val
 refine (Rule.max_cost (fun i:K=> Rule.solo (hh i))).rose fun x c=> ⟨fun ⟨v,p⟩=> ⟨v,?_,fun j q y u=>?_⟩,fun p=>⟨p.grade,fun i=> ?_⟩⟩
 · cases x with
   | none=> exact (ht _ (d1 u)).sub (ht _ (d0 u))
   | some i=> exact ht i i.property
 · let i:K:=⟨⟨j,Nat.lt_succ_iff.mpr q⟩,⟨y,u⟩⟩; have hx:=p i; change ‖pup x (T i)‖ ≤ c at hx; rw [he] at hx; exact hx
 rw [he]; exact p.token _ (Nat.le_of_lt_succ i.1.isLt) i.2.val i.2.property
end Signs
end YM.CF.Floral
