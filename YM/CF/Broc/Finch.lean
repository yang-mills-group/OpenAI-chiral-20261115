import YM.CF.Broc.Wisdom
import YM.CF.Phase.Expect
set_option autoImplicit false
noncomputable section
namespace YM.CF.Broc
open Function Filter Lattice Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Paige Phase Phase.Sample Brace Cube Peaks Tulip Rush
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m B:Side}
abbrev Funds(m B:Side):= Site (Domain m B)→ SU.E
def bSplit(m B:Side)(x:Sheen m B): Cue m:=fun i=> x (address m B i)
lemma split_g(m B:Side)(x: Sheen m B)(t): bSplit m B (feast t x)=partner m B t (bSplit m B x):=rfl
def ranK(m B:Side)(e p:ℝ)(x:BinK (CSide m B) e p): Plan (Index m) cloud:= loft m B x.val.1 (bSplit m B x.val.2.1) (bSplit m B x.val.2.2)
def forestB(m B:Side)(e p:ℝ): Lit (ranK m B e p) (foamK _ e p) (complexA m B) where
 pollen p:= (pass m B p).toMeasurableEquiv
 level t:= rain_g m B t
 gauge x t g:=Phase.oriented m B x.val.1 (bSplit m B x.val.2.1) (bSplit m B x.val.2.2) t g
 phase:=by
   let X:= BinK (CSide m B) e p; let P:=(↑X) × Cue m
   let f(i:P):=((i.1.val.1,bSplit m B i.1.val.2.1),bSplit m B i.1.val.2.2)
   have hb:Continuous (bSplit m B):= continuous_pi fun _=>continuous_apply _
   let F(i:P):Gaz (CSide m B):=i.1.val; have he:Continuous F:= continuous_subtype_val.comp continuous_fst
   have hx:Continuous f:= ((continuous_fst.comp he).prodMk (hb.comp (continuous_fst.comp (continuous_snd.comp he)))).prodMk (hb.comp (continuous_snd.comp (continuous_snd.comp he)))
   let K :=fun i:((Skin m B × Cue m) × Cue m)× Cue m=> bid m B i.1.1.1 i.1.1.2 i.1.2 i.2
   let h(i:P):=(f i,i.2); change Continuous (K ∘ h)
   exact (show Continuous K from bid_conn m B).comp (hx.prodMk continuous_snd)
 spread:= complex_up m B
variable (m B) {e p:ℝ}
abbrev backS(m B:Side)(e p:ℝ):= Sam (ranK m B e p)
lemma sealS (x:backS m B e p): let A:=x.val.1.val; tiedC m B A.1 A.2.1 A.2.2 x.val.2:=by
  intro A; let y:=x.val.2; have he:bid m B A.1 (bSplit m B A.2.1) (bSplit m B A.2.2) y≠0:=x.property
  have hx(a:Index m):= ready_vertex _ _ _ he a -- needs name
  have hm(a) (v:Sheen m B)(h:fundF m B A.1 (Phase.twin m (bSplit m B v) y) (insert 1 {0}) (a,1) ≠0): Cap m B A.1 (tailP m B v y) (insert 1 {0}) (a,1):=by
    have H := Ne.symm h; intro l hl; exact broad_margin.trans (pay _ _ _ _ _ _ (lt_of_le_of_ne (fund_pos ..) H) l (fee_in hl))
  have hb(v) (h:∀ a:Index m,Cap m B A.1 (tailP m B v y) (insert 1 {0}) (a,1)): mantle m B A.1 v y:=by
    intro a p; rcases a with ⟨a,i⟩; change i∈_ at p; simp only [mem_insert,mem_singleton] at p; rcases p with p|p <;> subst i
    · exact h a
    intro l k; cases l with
    | nil=> simp only [train,restrain,vote_unit]; exact small_margin m B
    | cons i l=>exact False.elim ((show singleU _ (a,0) (i::l) from (mem_filter.mp k).2).1 rfl)
  exact ⟨hb _ (fun a=> hm a _ (hx a).1),hb _ (fun a=>hm a _ (hx a).2)⟩
lemma cover_s (S:Table m B)(x: BinK (CSide m B) e p): Bank (ranK m B e p x) (complexA m B S):= complex_down m B S
lemma overB {S:Table m B}(x y: BinK (CSide m B) e p)(h:(foamK _ _ _).rel S x y)(z): sails (ranK m B e p x) (complexA m B S) z=sails (ranK m B e p y) (complexA m B S) z:=by
 refine prod_congr rfl ?_; intro i k
 have hf: room m B i⊆ S:= (mem_filter.mp k).2
 have hx(y):y∈faces m i→ address m B y∈S:=fun p=>hf (room_in (mem_filter.mp p).2 (raddr ..))
 exact bid_limit i (fun i u v=>h.1 i (hf u) (hf v)) (fun i p=> h.2.1 _ (hx i p)) (fun i p=>h.2.2 _ (hx i p)) (fun _ _=>rfl)
end YM.CF.Broc
