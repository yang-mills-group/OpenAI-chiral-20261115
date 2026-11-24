import YM.CF.Vault.Standing
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vault
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip Scroll Branch Paige Brace
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8000
variable {L:Side}{n k:ℕ}{ho:Odd L.val}{j:ℕ}(t:Even j)(g:1≤j)
-- enlarge Joy/Toll
lemma Tollage.near' (h:Tollage j L ho n k){m l:ℕ}(u:n≤m)(v:k≤l): Tollage j L ho m l:=⟨h.p.trans_le u,h.lpos.trans_le v,joyful L h.p h.hd u,joyful L h.p h.hm u,joyful L h.lpos h.hx v,joyful L h.lpos h.hc v⟩
abbrev Thread(j:ℕ):Script Male:= @Peaks.cloth j
structure Stamped (j:ℕ)(L:Side)(ho:Odd L.val)(Y:Pricing j L ho (Thread j)) : Prop where
  fields_one : ∀ N:Side,Y.N≤N.val→∀ x:Bkg (More N),Guard x Y.e→PaidG j Y.e x
  due : Tollage j L ho Y.n Y.k
  craft {N P:Side}(G: Ratio N P)(h:G.count=L)(v:Y.N≤N.val)(x:Sew N P)(l:Gild G x Y.e): Tollday j L ho Y.n Y.k x G
  flux {N P:Side}(G:Ratio N P)(h:G.count=L)(v:Y.N≤N.val)(x:Sew N P)(l:Gild G x Y.e) (M:Male): Matrix.trace (cExp j L ho (Thread j) Y.n M G (post x))=terms true j L ho Y.n M G x ∧ trace (eExp (Thread j) Y.k M G (post x))=lots true j Y.k M G x
include t g
lemma sparkling (ho:Odd L.val): ∃ Y: Pricing j L ho (Thread j),Stamped j L ho Y:=by
 let R:=Thread j; let p:= canUse j L ho; have H:=brass j L ho t g (Thread j) p true; have B:=bonus j L ho t g R p
 obtain ⟨a,l,G⟩:= taxed j L ho g t; obtain ⟨s,h,hv⟩:=H.youth ho; obtain ⟨b,q,t'⟩:= B.youth ho; let n:=max a s; let k:=max l b; have hn:s≤n:=le_max_right ..; have hk:b≤ k:=le_max_right ..; have hm:=G.near' (le_max_left a s) (le_max_left l b); have hs:=joyful L h hv hn; have hp:=joyful L q t' hk
 have ht : BoxD L (false,true) (false,true) (cExp j L ho R n):=H.stable ho hm.p hs
 have hT : BoxD L (false,true) (false,true) (eExp R k):= B.stable ho hm.lpos hp
 obtain ⟨a,C,e,r,w,J,v,hC,hK⟩:=ht.brood hT
 obtain ⟨⟨F,f⟩,⟨I,Y⟩⟩:=scour j L ho t g R p true
 obtain ⟨a',C',e',s',w',he',v',hA,H'⟩:= (show BoxD L _ _ (iExp j) from I).brood (show BoxD L _ _ (fExp j L ho) from F)
 have he := (((f.plus Y).plus (lobeInvoice j L ho t g R p k hp hm.lpos)).plus (parentheses j L ho t g R p true n hm.p hs)).plus ((festival j g L).plus (marginH j L ho t g R p))
 have hh:= (deserving j L ho g t hm).plus ((H.taxes ho hm.p hs).plus (B.taxes ho hm.lpos hp))
 obtain ⟨x,c,Z,m⟩:= he.plus hh
 obtain ⟨y,U,v'',W⟩:= radiance j g
 let z:=min (min (min e e') x) y; have ht:0<z:=lt_min (lt_min (lt_min J he') c) U
 let C₀:= max C C'; let b₀:= min a a'; let v₀:= max (max v v') Z+v''
 have hv:v≤ v₀:= by unfold v₀; omega
 have hw:v'≤ v₀:=by unfold v₀; omega
 have hy:z≤ y:=min_le_right ..; have hh':z≤min (min e e') x:=min_le_left ..
 have hf':z≤min e e':=hh'.trans (min_le_left ..); have hk':z≤x:=hh'.trans (min_le_right ..); have hZ:Z≤v₀:=by unfold v₀; omega
 let P : Pricing j L ho (Thread j):= ⟨n,k,z,ht,v₀,b₀,C₀,lt_min r s',
   (fun i _ _ G he hk=> (((neck ht (hf'.trans (min_le_left ..)) hC) i G he (hv.trans hk)).drop (min_le_left ..)).books (le_max_left ..)),
   (fun i _ _ G he hk=> (((neck ht (hf'.trans (min_le_left ..)) hK) i G he (hv.trans hk)).drop (min_le_left ..)).books (le_max_left ..)),
   (fun i _ _ G he hk=> (((neck ht (hf'.trans (min_le_right ..)) hA) i G he (hw.trans hk)).drop (min_le_right ..)).books (le_max_right ..)),
   (fun i _ _ G he hk=> (((neck ht (hf'.trans (min_le_right ..)) H') i G he (hw.trans hk)).drop (min_le_right ..)).books (le_max_right ..)), by
      intro N F G hx d M X u
      obtain ⟨⟨⟨⟨s,t⟩,c⟩,l⟩,g,p⟩:= (m G hx (hZ.trans d) X (u.breadth G hk')).1
      exact ⟨p M,(g _).2,(g _).1,(c _).1,t M,s M,(l M).2,(c M).2⟩⟩
 refine ⟨P,fun F h X u=>W F ((show v''≤v₀ from Nat.le_add_left ..).trans h) _ (u.shrink hy),hm,fun {N Q} G hx h x k=> (m G hx (hZ.trans h) x (k.breadth G hk')).2.1,?_⟩
 intro N Q G hx h x k M
 let H':=(m G hx (hZ.trans h) x (k.breadth G hk')).2.2; exact ⟨(H'.1 M).1, (H'.2 M).1⟩
omit t g
variable {Y:Pricing j L ho (Thread j)}
namespace Stamped
variable (p:Stamped j L ho Y) (g:1≤j) {N P: Side}
include p g
lemma blaze_X (M:Male)(G: Ratio N P)(h:G.count=L)(hp:Y.N≤N.val)(x:Sew N P)(l:Gild G x Y.e)(A:Shape){b r:Bool}(Z: ColorT b)(U:UNI SpinIdx)(Gx:JetS A.s b r U): hireT j L ho Y.n Y.k M G (lotX G A Z x)=cSignX (b.xor r) (hireT j L ho Y.n Y.k M G x):=by
 let B:=Y.cap G h hp M x l
 have hu : Y.N≤ P.val:=by rw [G.exact_size]; exact hp.trans (Nat.le_mul_of_pos_right _ G.count.property)
 have he:= stand_roar g p.due G h x A Z U Gx l.covW (p.fields_one _ hp) (p.fields_one _ hu) (p.craft G h hp x l) M (B.chart true)
 unfold hireT; obtain ⟨hx,hx'⟩:=p.flux G h hp x l M; obtain ⟨ht,hk⟩:=p.flux G h hp _ (guild G x A Z l) M; rw [hx,hx',ht,hk]; exact he
end Stamped
end YM.CF.Vault
