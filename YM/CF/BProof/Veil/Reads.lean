import YM.CF.BProof.Veil.Kite
/-! Certificate relation for the arguments consulted in budgets. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BProof.Veil
open Function Filter NormedSpace Finset MeasureTheory
open Cube Lattice Tenant SU Lat Dial Tulip Skye Spin Branch Hearth Tape Hero
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N:Side}{j:ℕ}{a b l r c δ v η:ℝ}{P:Ready j a b l r}{F:Core j a b l r N}
abbrev Window.weather(x:Window N): Pane N:=x.1.1
def sion (x:Loft F δ c v η):Window N:= ((Tape.carried x.val.1,x.val.1.val.2),x.val.2.val)
@[fun_prop] lemma carol : Measurable (sion (v:=v) (η:=η) (c:=c) (δ:=δ) (F:=F)):= by
 unfold sion carried; fun_prop
-- Standard Borel Space on all Loft + fields at Reading
structure Occasion(c v η:ℝ):Prop where
 charge:0<c
 lev: c ≤1
 hi : 1≤v
 lid : η<1
lemma standard(h:Honor P F δ)(v':Occasion c v η) : StandardBorelSpace (Loft F δ c v η):=by
 haveI:PolishSpace (Loft F δ c v η):= Tape.mainC h v'.charge v'.lev v'.lid v'.hi; infer_instance
variable (h:Honor P F δ)(S:Support (More N))
lemma stateD(x y:Loft F δ c v η) (d:(window N).agree S (sion x) (sion y)):
 let T:= (h.1.beam c).st.eval S x.val.1 y.val.1; let U:=(Tape.kiln h.1 c v η).st.eval S x y; T=0 ∧ U=0:=by
 intro T U; obtain ⟨z,t⟩:= (paired S).mp d; have ht:Agrees (↑S) (Tape.carried x.val.1) (Tape.carried y.val.1):=(pine_eq S).mp (((paired S).mp z).1); have he:= (shoots_rule S).mp (((paired S).mp z).2); have hc:= (curve_rule S).mp t
 let A:=x.val.1; let B:=y.val.1
 have hp:T=0:=by
   change fa (Tape.carried x.val.1) (Tape.carried y.val.1) S/ |P.hT|+ (∑ i∈ S,dots i x.val.1.val.2 y.val.1.val.2)=0; rw [fa_total, sum_eq_zero (fun i hi=>?_ ),sum_eq_zero (fun i hi=>(show dots i x.val.1.val.2 y.val.1.val.2=0 from if_pos (he i hi))),zero_div,zero_add]; rw [ht i (mem_filter.mp hi).2.1 (mem_filter.mp hi).2.2]; unfold scenery; rw [sub_self,norm_zero]
 refine ⟨hp,?_⟩; change T+∑ i∈S,Skein.toll i x.val.2 y.val.2=0; -- bind args missing!
 rw [hp,sum_eq_zero,add_zero]; intro i hi; unfold Skein.toll; apply sum_eq_zero; intro j _; unfold wage; dsimp only; rw [show x.val.2.val i=y.val.2.val i from hc i hi,sub_self,norm_zero]
lemma sion_turn(x:Loft F δ c v η)(g:Geometry N): sion (Oasis.runH h x g)= (window N).act g (sion x):=rfl
lemma equalize(x y:Window N): (window N).agree S x y ↔ (pine N).agree S x.weather y.weather ∧ (shoots N).agree S x.1.2 y.1.2 ∧ (curving N).agree S x.2 y.2:=by unfold window; rw [paired,paired]; exact and_assoc -- tune assoc
end YM.CF.BProof.Veil
