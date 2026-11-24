import YM.SU5.Relativistic.Lamina
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Mosaic
open Function Finset Filter MeasureTheory Lattice Wilson Fixed.Pivots GaugeFlux
open scoped Matrix BigOperators
variable {N C: Side}(L:Ratio C N)
local notation "W_"=> L.count
local notation "T_"=> Site C
local notation "F_"=> Site N
local notation "P_"=> Site L.count
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
open RG RG.PathData Work.F03 Pharos
variable {V : Side}
lemma seam_door {x:Link N}{f:Face (Per N)} (h:x∈ support f) : ∃ U:Walk,U.length≤1∧ stop f.1 U=x.1:=by
 obtain ⟨p,⟨⟨i,j⟩,e⟩⟩:=f; simp only [Fixed.Pivots.support,window,mem_insert,mem_singleton] at h; rcases h with rfl|rfl|rfl|rfl
 · exact ⟨[],by simp,rfl⟩
 · exact ⟨[posDir i],by simp,rfl⟩
 · exact ⟨[posDir j],by simp,rfl⟩
 exact ⟨[],by simp,rfl⟩
lemma doorway {x:Link W_}{f:Face (Per N)} (i:T_)(h: raise L i x ∈ support f) (g:deep 2 x.1) : f∈ mounted L i:=by
 obtain ⟨a,t,v⟩:=seam_door h
 let A:= reverse a; have he:A.length=a.length:=by simp [A,Lattice.reverse]
 obtain ⟨q,r⟩:= rolling L 1 A x.1 i (fade_d 2 _ (by omega) _ g)
 let y:=stop x.1 A; have hy:f=chip L i (y,f.2):=by
    refine Prod.ext ?_ rfl; change f.1=setDown L i y; unfold y; rw [← r,show setDown L i x.1=_ from (show setDown L i x.1=stop f.1 a from v.symm),reverse_stop]
 exact mem_map.mpr ⟨(y,f.2),mem_filter.mpr ⟨mem_univ _, (subdeep _ _ 0 q).2.1,(subdeep _ _ 0 q).2.1⟩,hy.symm⟩
lemma doorway_p {D:ℕ}(i:T_){x:Link W_}{p :Face (Per N)}(v:Slot)(q:v.length≤ D)(e:raise L i x∈ support (slotFace v p.1))(g:deep (2*D+2) x.1) : p∈ plumage L D i:=by
 obtain ⟨a,t,k⟩:= seam_door e
 let R:= v.walk ++ a; let A:= reverse R; have he:stop p.1 R=setDown L i x.1:= by rw [show stop p.1 R = stop (stop p.1 v.walk) a from stop_append ..,← offset_f v]; exact k
 have hp: A.length+D≤2*D+2:=by unfold A R Lattice.reverse; simp only [List.length_map,List.length_reverse,List.length_append]; unfold Slot.length at q; omega
 obtain ⟨u,h⟩:= rolling L D A x.1 i (fade_d _ _ hp _ g)
 let y:= stop x.1 A; refine mem_map.mpr ⟨(y,p.2),mem_filter.mpr ⟨mem_univ _, u⟩,Prod.ext ?_ rfl⟩
 exact h.symm.trans (by rw [←he,reverse_stop])

def edgeT (V:Side)(m:ℕ):= ((univ:Finset (Link V)).filter fun i=> ¬deep m i.1)
lemma edge_card (V:Side)(m:ℕ) : (edgeT V m).card≤32*m*V.val^3:=by
 let S(j:Axis)(g:Per V):=((univ:Finset (Site V)).filter fun i=> i j=g)×ˢ(univ:Finset Axis)
 let K:=(Finset.range m).image (fun i:ℕ=>(i:Per V)); let T:= K.image fun i=>-i-1; let H(a:Axis):=(K ∪ T).biUnion (S a); have hv(k:ℕ)(h:k < m): (k:Per V)∈K:=mem_image_of_mem _ (mem_range.mpr h)
 have he : edgeT V m⊆ univ.biUnion H:=by
    intro i t; have h:¬deep m i.1:= (mem_filter.mp t).2; unfold deep at h; push Not at h; obtain ⟨j,g⟩:= h
    apply mem_biUnion.mpr; refine ⟨j,mem_univ _,mem_biUnion.mpr ⟨i.1 j,?_,mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,rfl⟩,mem_univ _⟩⟩⟩
    let x:= i.1 j; by_cases f:(i.1 j).val < m; · apply mem_union_left; exact (by simpa using hv _ f)
    specialize g (not_lt.mp f); let k:=V.val-1-x.val
    have hp:x.val+1 ≤ V.val:=ZMod.val_lt _; have hh:k+(x.val+1)= V.val:=by unfold k; omega
    have hr:k < m:=by change _≤x.val + _ at g; omega
    have hx:-(k:Per V)-1=x:=by
       have ht: ((k:Per V)+(x+1))=0:=by
         have he: ((k+(x.val+1):ℕ) : Per V)=0:=by rw [hh]; exact ZMod.natCast_self _
         simpa using he
       calc _= -(k:Per V)-1+0:=by rw [add_zero]
            _ = x:=by nth_rw 1 [←ht]; abel
    exact mem_union_right _ (mem_image.mpr ⟨k, hv k hr,hx⟩)
 have hp : K.card ≤ m:= card_image_le.trans (card_range _|>.le); have hr: T.card ≤ m:=card_image_le.trans hp; have hh:(K∪T).card ≤ 2*m:=(card_union_le ..).trans (by omega)
 have hf(i:Axis)(g:Per V) : (S i g).card ≤ V.val^3*4:=by unfold S; rw [card_product,card_univ,show Fintype.card Axis=4 from rfl]; exact Nat.mul_le_mul_right _ (wool_links V i g)
 have ht(i:Axis): (H i).card ≤ 2*m*(V.val^3*4):= card_biUnion_le.trans ((sum_le_sum (fun j _=> hf i j)).trans (by rw [sum_const,nsmul_eq_mul]; exact Nat.mul_le_mul_right _ hh))
 exact (card_le_card he).trans (card_biUnion_le.trans ((sum_le_sum (fun i _=> ht i)).trans_eq (by rw [sum_const,nsmul_eq_mul,card_univ,show Fintype.card Axis=4 from rfl]; ring)))
end YM.CF.Papyrus.Mosaic
#print axioms YM.CF.Papyrus.Mosaic.edge_card
