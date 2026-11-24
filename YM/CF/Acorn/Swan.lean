import YM.CF.Acorn.Laurel
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Paige
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase MeasureTheory Tulip Peaks Rush Brace
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{L:Side}{ho:Odd L.val}{T:Script Male}
lemma grip_repair(HR:Acorn.Repair j) (Y:Pricing j L ho T)(hp:1≤j) : ∃ n0:ℕ,∀ b:Side,n0≤b.val→ ∃ n:ℕ, ∀ B: Side,n≤B.val→(∃ K,b*K=B)→∃ e:ℝ,0<e∧∀ w:ℝ, 0<w→ w≤e → ∃ g: Grasp Y B w,g.b=b ∧ e≤HR.d ∧ g.baseline≤HR.d ∧ HR.n ≤g.roundZ:=by
 obtain ⟨l,d,a,t,v,n,pA,k,H⟩:=coin_v j hp
 obtain ⟨N,V⟩:=resolve d H.posT
 refine ⟨N, fun b x=>?_⟩; obtain ⟨q,p,hp',hx⟩:= V b x; -- structure Foil Guide? resolve returns ⟨e,p,h,...⟩
 let δ:=min (min Y.e p) HR.d; have hd:0<δ:=lt_min (lt_min Y.range hx.pPositive) HR.pd
 obtain ⟨u,h,hQ,W⟩:=kip L.val δ hd
 obtain ⟨N',R⟩:= scalable _ h; obtain ⟨x,A⟩:= all_room;
 refine ⟨max x N',?_⟩; intro B he' hM; obtain ⟨K,r⟩:=hM
 obtain ⟨c,r',Q⟩:= R B ((le_max_right ..).trans he'); obtain ⟨e,pE,Q'⟩:= A B ((le_max_left ..).trans he')
 obtain ⟨w,pW,v',Wy⟩:= drift_l j hp
 let m:=min (min (min u q) c) (min e w); have hm:0<m:=lt_min (lt_min (lt_min h hp') r') (lt_min pE pW)
 let b':= HR.n+v+v'+Y.N+(2*rankS L.val)+1
 refine ⟨m,hm,fun M hk h'=>?_⟩ -- shadow k q
 have hg:= h'.trans (min_le_right .. : m≤ min e w); have hl := hg.trans (min_le_right ..); have hx' := h'.trans (min_le_left .. : m≤min (min u q) c)
 have hv:=hx'.trans (min_le_left ..); have hd':= hQ.le.trans ((min_le_left ..).trans (min_le_left ..) : δ≤Y.e)
 have hh :billK L.val M u < δ:= (by
   apply lt_of_le_of_lt _ W; unfold billK; gcongr <;> exact hv.trans (min_le_left ..))
 refine ⟨⟨l,n,v,b',b,K,r,d,t,a,pA,k,p,u,h,H,hx.pull hk.le (hv.trans (min_le_right ..)), Q' _ hk.le (hg.trans (min_le_left ..)),Q _ (hx'.trans (min_le_right ..)),(hv.trans (min_le_left ..)).trans hd',hQ.le.trans ((min_le_left ..).trans (min_le_right ..)),hd', hh.trans_le ((min_le_left ..).trans (min_le_right ..)),hh.trans_le ((min_le_left ..).trans (min_le_left ..)),?_,?_,?_, fun N hx M=> (Wy N (le_trans (show v'≤ b' from ?_) hx) M).red hl⟩,rfl,le_trans (le_trans (min_le_left ..) ((min_le_left ..).trans (min_le_left ..) : min (min u q) c ≤ u)) (hQ.le.trans (min_le_right ..)),hQ.le.trans (min_le_right ..),show HR.n≤b' from ?_⟩ <;> unfold b' <;> omega
end YM.CF.Paige
