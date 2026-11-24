import YM.CF.Vp929.Borel.Gather
import YM.CF.Vp929.Borel.Measure
set_option autoImplicit false
set_option maxHeartbeats 640000
noncomputable section
namespace YM.CF.VolumeCape.Borel
open Filter Function Finset MeasureTheory ProbabilityTheory
open Mesh Lattice Atlas Skye Cane Spire Scroll SU Cube Lat Aerial Sample Gather
open scoped Classical Topology ENNReal NNReal Matrix.Norms.Frobenius
namespace Gather
variable (n:Side)(r:ℕ)(M:Finset (Seat n))
local notation "S_"=>Stain n r M
variable {I:Type} [Nonempty I][Fintype I][MeasurableSpace I][MeasurableSingletonClass I][StandardBorelSpace I]
variable (p:Ticket I)(R:Sweep n→Equiv.Perm I) (v:∀s,MeasurePreserving (R s) p.Law p.Law)
include v
def decode(w:Wave n)(x:S_) : I:= memo n p R x.val w
omit v
lemma scentedPr : iIndepFun (fun i:S_ =>memo n p R i.val) (valsw n):= by
 apply Borel.separate; intro i X m; let Y:= X.biUnion (fun i:S_=>i.val); have a(S:S_)(x y:Wave n)(h:∀ k∈ S.val,x k=y k): memo n p R S.val x=memo n p R S.val y:=by unfold memo; rw [glance _ _ S.property.1 x y h]
 apply independenceTape (pale.prod (paperMeas (Sweep n))) (memoM ..) (measurable_pi_lambda _ (fun i=>memoM ..)) (S:=i.val) (T:=Y) (a i); · intro x y t; funext j; exact a j x y (fun k v=> t k (mem_biUnion.mpr ⟨j,j.property,v⟩))
 exact Finset.disjoint_left.mpr fun a p q=> by obtain ⟨j,b,q⟩:= mem_biUnion.mp q; have u:= Gather.separate n r M i j (fun t=>m (t ▸ b)) _ p _ q; rw [separation_self] at u; omega
include v
lemma decode_law : MeasurePreserving (decode n r M p R) (valsw n) (Measure.pi fun _:S_=>p.Law):= by
   constructor
   · unfold decode
     apply measurable_pi_lambda
     intro i; exact memoM n p R _
   · calc
       _=(Measure.pi fun i:S_=> (valsw n).map (memo n p R i.val)):= by

           change (valsw n).map (fun w (x:S_)=>memo n p R x.val w)=_
           exact (scentedPr n r M p R).map_fun_eq_pi_map fun i=>(memoM n p R i.val).aemeasurable
       _= _ := congrArg (fun m:S_ → Measure I => Measure.pi m) (funext fun i:S_=> (Sample.law n p R v i.val).map_eq)
omit v

variable {A:Type} [Fintype A][MeasurableSpace A][MeasurableSingletonClass A]
abbrev deck(f:ℕ)(F:I→Seat n→A) (i:Stain n r M):= Vision (moat n r M i f) F
abbrev Plot(f:ℕ)(F:I→Seat n→A)(x:I)(i:Stain n r M):= deck n r M f F i x
variable (f k:ℕ) (T:Budget r f k) (F:I→Seat n→A)
variable (h:∀ S V,stone (More n) S V k→ Ticket.Indep p (Vision S F) (Vision V F))
include T h
lemma price_map : p.Law.map (Plot n r M f F) = Measure.pi (fun i:S_=> p.Law.map (deck n r M f F i)):=by
 let g(i:S_):= moat n r M i f; suffices u:iIndepFun (deck n r M f F) p.Law from u.map_fun_eq_pi_map fun i=>(measurable_of_countable _).aemeasurable; apply Borel.separate; intro i X m
 let V:= X.biUnion g; have hz:stone (More n) (g i) V k:=by intro z a y b; obtain ⟨j,v,b⟩:= mem_biUnion.mp b; exact Gather.apart n r M _ _ (show i≠j from fun H=>m (H ▸ v)) _ _ T _ a y b
 let W:= h (g i) V hz; apply p.cashInd; apply Ticket.less _ _ _ W; · exact fun _ _ _ _ x=> x
 intro a b _ _ v; funext x y; exact congrFun v (⟨y,mem_biUnion.mpr ⟨x,x.property,y.property⟩⟩: ↑V)
theorem price_tape : p.Law.map (Plot n r M f F)=(Measure.pi fun _:S_=> p.Law).map (fun w i=> deck n r M f F i (w i)) :=by rw [price_map n r M p f k T F h, Measure.pi_map_pi]; exact fun i=> (measurable_of_countable _).aemeasurable
end Gather
end YM.CF.VolumeCape.Borel
