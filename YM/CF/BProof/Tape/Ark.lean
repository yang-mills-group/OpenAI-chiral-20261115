import YM.CF.BProof.Tape.Market
/-! Polished Loft. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Tape
open Function Filter Fock Finset Branch Stint Align Wick Hearth Spin Tenant Lat Lattice Tulip Cube Fig
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth
attribute [local instance] opCStarAlgebra
variable {I D:Type}[Fintype I][DecidableEq I][Nonempty I][TopologicalSpace D] {η:ℝ}
lemma marketS {T U:D→ Op I}(h: Continuous T)(u:Continuous U)(v:η<1): IsClosed {i|Shelf (T i) (U i) η }:=by
 let L:= {i| T i * T i=T i}∩{i|star (T i)= T i}; let W:= {i:D| U i ∈ unitary _}; let M:={i| (U i)ᵀ= -U i}; let X:={i|‖(1-T i)*U i*cc (T i)‖≤η}; have he : {i | Shelf (T i) (U i) η}=L∩W∩M∩X:=by ext i; constructor; intro q; let k:= (show Shelf (T i) (U i) _ from q); exact ⟨⟨⟨⟨k.1.1,k.1.2⟩,k.2⟩, k.3⟩,k.4⟩; rintro ⟨⟨⟨⟨p,q⟩,u⟩,m⟩,t⟩; exact ⟨⟨p,q⟩,u,m,t,v⟩ -- constructor projections?
 rw [he]; apply IsClosed.inter (IsClosed.inter (IsClosed.inter _ (show IsClosed W from ?_)) ?_) ?_
 · exact (isClosed_eq (h.mul h) h).inter (isClosed_eq h.star h)
 · exact (isClosed_unitary).preimage u
 · exact isClosed_eq u.matrix_transpose u.neg
 exact isClosed_le (((((continuous_const (y:=(1:Op I))).sub h).mul u).mul h.star.matrix_transpose).norm) (continuous_const (y:=η))
variable {j:ℕ}{a b l r δ c v:ℝ}{N:Side}{P: Ready j a b l r}{F:Core j a b l r N}(h:Honor P F δ)
include h
lemma mainC (e:0<c)(V':c≤1)(g:η<1)(U':1≤v) : PolishSpace (Loft F δ c v η):=by
 let K:= Shed F δ c v
 let b':= h.1.beam c
 let Pk(i:Bool)(x:K):=cutX i x.1; let f(x:K):=carried x.1; let A(x:K):=F.θ (f x) 1; let U(i:K):= F.upright (f i); let T(i:K):= F.wind (f i); let C' (i:Bool)(u:ℝ)(x:K):= path x (i,false) u; let Q'(u:ℝ)(i:K):=floorH (A i) (Pk true i) (Pk false i) u; let Y'(u:ℝ)(i:K):= rug (U i) (T i) u
 have he : {i:K| dream F δ c v η i}= {i:K| C' true 1 i=C' false 0 i}∩⋂u:Time,{i:K| Shelf (Y' u.val i) (C' true 0 i) η} ∩ {i|Shelf (A i) (C' true u.val i) η} ∩ {i | Shelf (Q' u.val i) (C' true 1 i) η} ∩ {i|Shelf (Q' 0 i) (C' false u.val i) η}:=by
    ext x; simp only [Set.mem_inter_iff,Set.mem_iInter,Set.mem_setOf_eq]; constructor; intro v; exact ⟨v.grips,fun i=>⟨⟨⟨v.rails i.val i.property,v.fires i.val i.property⟩,v.sails i.val i.property⟩,v.pores i.val i.property⟩⟩; rintro ⟨h0,H⟩; refine ⟨F.leaning P _ h.1.minN h.1.shelter x.1.val.1.property,x.1.property,?_,?_,?_,?_,h0,?_, h.2 x.1.val.1⟩
    · exact fun y t=>(H ⟨y,t⟩).1.1.1
    · exact fun y t=>(H ⟨y,t⟩).1.1.2
    · exact fun y t=>(H ⟨y,t⟩).1.2
    · exact fun y t=>(H ⟨y,t⟩).2
    exact ⟨x.1.property,cut_real _,cut_real _,pairCom ..,pairCom ..,(H ⟨1,walk1⟩).2⟩ -- tune
 obtain ⟨p,H⟩:=purchaseV U' P δ c; obtain ⟨hA,hT,hX,ht,u⟩:= H h.1; let M:= Tape.vacuum h.1 v c
 have hu : Feet.Skid b' M Prod.fst:= Feet.doubleSkid b' Skein.move Skein.toll (fun i x y=> Skein.toll_pos i x y); have hz:Earn p M.mark M.mark U:= hu.mark hA; have hT:Earn p M.mark M.mark T:= hu.mark hT; have hX(i:Bool):Earn p M.mark M.mark (Pk i):= hu.mark (hX i); have hB:Earn p M.mark M.mark A:= hu.mark ht
 have hp(s:ℝ)(p':s∈walking):Earn (Pay.simple.wage 1) M.mark M.mark (fun _=>s • 1):= (Earn.one M.mark).wage (upt p'); have hL(s:Bool)(v:ℝ)(t:v∈walking): Continuous (C' s v):=by obtain ⟨T,H⟩:= Skein.earns U'; exact (est (H b' (s,false)) ⟨v,t⟩).cont
 obtain ⟨ℓ,E⟩:= sweepPrice Spin.quota_p.le p p (Pay.simple.wage 1); obtain ⟨v',l,m,w,x,X⟩:= sphere _ _ Spin.quota_p.le e p p p (Pay.simple.wage 1)
 have hf(i:ℝ)(t:i∈walking):Continuous (Y' i):=(show Earn ℓ M.mark M.mark (Y' i) from (E M.cap hz hT (v:=fun _=>i) (hp i t) (fun i=>F.leaning P _ h.1.minN h.1.shelter i.1.val.1.property))).cont -- name τ? function v
 have hq(i:ℝ)(t:i∈walking):Continuous (Q' i):=(show Earn w M.mark M.mark (Q' i) from (X.applies M.cap (hX true) (hX false) hB (τ:=fun _=>i) (hp i t) (fun _=> upt t) (fun i=>i.1.property)).2.2.2.1).cont
 haveI := MarketC h e V'; refine IsClosed.polishSpace (s:={i:K|dream F δ c v η i}) ?_; rw [he]; exact (isClosed_eq (hL _ _ walk1) (hL _ _ walk0)).inter (isClosed_iInter fun i=> (((marketS (hf i.val i.property) (hL true 0 walk0) g).inter (marketS hB.cont (hL true _ i.property) g)).inter (marketS (hq _ i.property) (hL true _ walk1) g)).inter (marketS (hq _ walk0) (hL false _ i.property) g)) -- ambiguous
end YM.CF.BProof.Tape
