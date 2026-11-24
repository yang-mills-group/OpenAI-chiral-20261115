import GaugeFieldConstruction.Argyll
import YM.CF.Roots.Sail
set_option autoImplicit false
noncomputable section
namespace YM.CF.Roots
open GJ Function Set Metric Mew MeasureTheory Filter Finset
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I E F X N : Type}[Fintype I][LinearOrder I][NormedRing N][NormedAlgebra ℂ N][CompleteSpace N]
variable (H:I→N)
def brewK (L:List I)(z:Key I): N:= (L.map fun i=>1+ z i • H i).prod
lemma brew_R (L:List I): River (brewK H L):=by
 induction L with
 | nil=> exact zeroR _
 | cons i L h=> apply (show River (pulseV (ContinuousLinearMap.mul ℂ N) (fun z:Key I=>1+z i • H i) (brewK H L)) from prodR _ (dub_V (zeroR _) (by simpa [pine] using lift_b ({i}:Finset I) (H i))) h); -- exact?
lemma brew_off (L:List I)(z:Key I)(i:I)(x:ℂ)(v:i∉L):brewK H L (update z i x)=brewK H L z:=congrArg List.prod (List.map_congr_left (fun j w=>by rw [update_of_ne]; intro p; exact v (p ▸ w))) -- tune exposed
lemma lift_W (B:N)(L:Key I→ N)(p:River L)(q:List I):tipI (fun x=> B*L x) q = B* tipI L q:=sim_H p (ContinuousLinearMap.mul ℂ N B) q roots -- tune name
lemma survey_cash (L:List I)(h:L.Nodup)(q:List I)(p:q.Nodup):tipI (brewK H L) q=if q⊆L then (((L.filter fun i=>decide (i∈ q)).map H).prod) else 0:=by
 induction L generalizing q with
 | nil=> cases q with|nil=> simp [tipI, lance,brewK]|cons i q=> rw [show tipI (brewK H []) (i::q)=0 from proper (1:N) i q]; simp
 | cons i L ih=>
    obtain ⟨a,b⟩:=List.nodup_cons.mp h
    by_cases ht:i∈ q; swap
    · rw [←tip_V i q ht]; rw [show brewK H (i::L) ∘ dune i= brewK H L from ?_]; swap
      · funext z; change (1+dune i z i • _)*brewK H L _= _; rw [dune,update_self, brew_off _ _ _ _ _ a]; simp
      have hh: q⊆ i::L ↔ q⊆ L:=⟨fun p j q=> (List.mem_cons.mp (p q)).resolve_left fun s=> ht (s ▸ q),fun p j q=>List.mem_cons_of_mem _ (p q)⟩
      rw [ih b q p]; simp_rw [hh]; simp [ht]
    obtain ⟨u,v,hq⟩:= List.append_of_mem ht; let D:=u++v; have hv:q.Perm (i::D):=hq ▸ List.perm_middle; have hu:= List.nodup_cons.mp (hv.nodup_iff.mp p)
    have hx:Set.EqOn (cutI (brewK H (i::L)) i) (fun z=>H i*brewK H L z) (hill I):=by
       intro z y; apply (mitt (brew_R H _) y i).unique
       have hz(w:ℂ):brewK H (i::L) (update z i w)= 1 * brewK H L z+ w • (H i*brewK H L z):=by
          change (1+_)*brewK H L _=_; rw [brew_off _ _ _ _ _ a,update_self,add_mul,smul_mul_assoc]
       simp_rw [hz]; have hx:= ((hasDerivAt_id' (0:ℂ)).smul_const (H i*brewK H L z)).const_add (1 * brewK H L z); rw [one_smul] at hx; exact hx
    calc
     _ = tipI (brewK H (i::L)) (i::D):= move_ζ hv (brew_R ..) roots
     _ = H i * tipI (brewK H L) D:=(lace_C D hx roots).trans (lift_W (H i) _ (brew_R ..) D)
     _ = _ := by
          rw [ih b D hu.2]; have he:q⊆ i::L↔D ⊆ L:=by
             constructor
             · intro p j u'; exact (List.mem_cons.mp (p (hv.mem_iff.mpr (List.mem_cons_of_mem i u')))).resolve_left fun z=>hu.1 (z ▸ u')
             intro p j t; exact (List.mem_cons.mp (hv.mem_iff.mp t)).elim (fun z=> z ▸ List.mem_cons_self) (fun u=> List.mem_cons_of_mem _ (p u))
          simp_rw [he]; split; swap; · next x=> rw [mul_zero] -- tuning
          next z=>
             rw [List.filter_cons_of_pos (by simpa),List.map_cons,List.prod_cons]; congr 3; apply List.filter_congr; intro j h
             have hu:j ≠ i :=by intro p; rw [p] at h; contradiction
                  
             simp_rw [hv.mem_iff, List.mem_cons, or_iff_right hu]

#print axioms survey_cash
end YM.CF.Roots
end
