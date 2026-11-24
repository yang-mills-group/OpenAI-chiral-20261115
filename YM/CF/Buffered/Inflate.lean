import YM.CF.Buffered.Through
import YM.CF.Buffered.Mark
import YM.CF.Buffered.Bing -- for env helper later
/-!
# Full CAR inclusion for a subbox, preserving the matched bra sandwiches
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.Buffered.Cin
open Function Fock NormedSpace SU Lat Lattice Cube Finset MeasureTheory Branch Reflect Window Reed
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
attribute [local instance] opCStarAlgebra
variable {I J : Type*} [LinearOrder I] [LinearOrder J] [Fintype I] [Fintype J]
-- basis embedding, complement occupation `s`
local notation "⟪" x ", " y "⟫" => inner ℂ x y
variable (f : I↪J)
private lemma pail_zero {s t:Finset J}(p:Deck f s)(u:Deck f t)(h:s≠t)(x:Wave I): pailL f t (hoist f s x)=0 := by
 nth_rw 1 [←basis_expand x]; rw [map_sum,map_sum]; refine sum_eq_zero fun i _=> ?_; rw [map_smul,map_smul]; apply smul_eq_zero_of_right
 apply PiLp.ext; intro j; change _=0; rw [←basis_inner,pails _ _ u,hoops,hoops]; obtain ⟨a,hx,he⟩:= knotW f s p i; obtain ⟨b,hb,hj⟩:= knotW f t u j; rw [he,hj,inner_smul_right,inner_smul_left]; have ht:fog f t j≠fog f s i:=by
    intro hk
    have hv(k:Finset J)(s:Finset I)(p:Deck f k) : fog f k s \ lows f=k:=by unfold fog; rw [Finset.union_sdiff_distrib,_root_.sdiff_eq_self_iff_disjoint.mpr p.splitL, Finset.sdiff_eq_empty_iff_subset.mpr (show s.map f ⊆ lows f from map_subset_map.mpr (subset_univ s)), Finset.union_empty]
    exact h (by rw [←hv _ _ u, ←hv s i p,hk]) -- tune
 simp only [basis_inner,basis_apply, if_neg ht,mul_zero]

private def load (f : I↪J) (A:FC I) : (Wave J →L[ℂ] Wave J) := by
 classical exact ∑ s∈ (lows f)ᶜ.powerset, (hoist f s).comp ((acts A).comp (pailL f s))

def inject (f:I↪J)(A:FC I) : FC J := (Matrix.toEuclideanCLM (n:=Finset J) (𝕜:=ℂ)).symm (load f A)
lemma insert_act (A:FC I)(x:Wave I){s:Finset J}(p:Deck f s) : acts (inject f A) (hoist f s x)=hoist f s (acts A x):=by
 classical
 have he : acts (inject f A) = load f A:= (Matrix.toEuclideanCLM (n:=Finset J) (𝕜:=ℂ)).apply_symm_apply _
 rw [he,load,ContinuousLinearMap.sum_apply]; simp_rw [ContinuousLinearMap.comp_apply]; rw [sum_eq_single s]
 · rw [pourL f s p]
 · intro i u h; rw [pail_zero _ p (⟨Disjoint.mono (le_refl _) (mem_powerset.mp u) disjoint_compl_right⟩) h.symm,map_zero,map_zero]
 exact fun h=> (h (mem_powerset.mpr fun i v=> mem_compl.mpr fun e=> disjoint_left.mp p.splitL e v)).elim
lemma totalBasis {K Q : FC J} (p:∀ x:Wave I,∀ s,Deck f s→ acts K (hoist f s x)=acts Q (hoist f s x)) : K=Q :=by
 apply op_columns; intro i
 let s:= i\lows f; let t:= i.preimage f f.injective.injOn
 have he: Deck f s := ⟨disjoint_sdiff_self_right⟩
 have hs: fog f s t=i:= by
   ext x; unfold fog s t; by_cases p:x∈lows f <;> simp only [mem_sdiff,mem_union,mem_map,mem_preimage]
   · obtain ⟨y,b,rfl⟩:= mem_map.mp p; simp [lows]
   rw [and_iff_left (show x ∉ lows f from p)]; refine or_iff_left ?_; rintro ⟨y,_,rfl⟩; exact p (coil_hit ..)
 obtain ⟨z,h,t'⟩:= knotW f s he t; have v:= p (basisKet t) s he; rw [hoops,t',hs,map_smul,map_smul] at v; exact smul_right_injective (Wave J) (by intro u; rw [u,mul_zero] at h; exact zero_ne_one h) v

-- API priority. injection all ops
lemma inject_one : inject f 1=1 := totalBasis f (fun i s p=> by rw [insert_act f _ _ p,act_one,act_one])
lemma inject_mul (F K : FC I) : inject f (F*K)=inject f F * inject f K:= totalBasis f (fun i s p=> by rw [insert_act f _ _ p,act_mul,act_mul,insert_act f _ _ p,insert_act f _ _ p])
lemma inject_smul (F:FC I)(z:ℂ) : inject f (z • F)=z • inject f F:= totalBasis f (fun i s p=>by rw [insert_act f _ _ p, act_smul,map_smul,act_smul,insert_act f _ _ p])
lemma inject_add (F K:FC I): inject f (F+K)=inject f F+inject f K:= totalBasis f (fun i s p=>by rw [insert_act f _ _ p,act_add,map_add,act_add,insert_act f _ _ p,insert_act f _ _ p])
lemma inject_star (F:FC I) : inject f (star F)=star (inject f F):=by
   unfold inject; rw [←show (Matrix.toEuclideanCLM (n:=Finset J) (𝕜:=ℂ)).symm (star (load f F))=star ((Matrix.toEuclideanCLM (n:=Finset J) (𝕜:=ℂ)).symm (load f F)) from (Matrix.toEuclideanCLM (n:=Finset J) (𝕜:=ℂ)).symm.map_star' _]; apply congrArg
   change _=ContinuousLinearMap.adjoint (load f F); unfold load; rw [map_sum]; refine sum_congr rfl fun i _=> ?_
   rw [show acts (star F)=ContinuousLinearMap.adjoint (acts F) from Matrix.toEuclideanCLM.map_star' F]
   change _ = ContinuousLinearMap.adjoint (ContinuousLinearMap.comp (hoist f i) _); simp [pailL,ContinuousLinearMap.comp_assoc]

def into (f:I↪J) : FC I→ₐ[ℂ] FC J :=
 AlgHom.mk' {toFun:=inject f, map_add' :=inject_add f, map_one':=inject_one f, map_mul' :=inject_mul f, map_zero':=by simpa using inject_smul f (0:FC I) 0} fun c x=> inject_smul f x c
lemma put_in (i:I): into f (put i)=put (f i):= totalBasis f (fun x s h=>by rw [show into f _=inject f _ from rfl,insert_act f _ _ h,hoist_put])
lemma take_in (i:I): into f (takeF i)=takeF (f i):= totalBasis f (fun x s h=>by rw [show into f _=inject f _ from rfl,insert_act f _ _ h,hoist_t f s h])
lemma into_cont : Continuous (into f) := (into f).toLinearMap.continuous_of_finiteDimensional
lemma into_star (A:FC I) : into f (star A) = star (into f A) := inject_star ..
lemma into_inj : Injective (into f):=by
 let T:=Fock.hoist f ∅; have hp: Deck f ∅:=⟨by simp⟩; intro a b k; apply op_columns; intro i
 rw [←pourL _ _ hp (acts a _), ←pourL _ _ hp (acts b _), ←insert_act _ _ _ hp, ←insert_act _ _ _ hp,show inject f a=inject f b from k]
lemma sector_in {b : Bool} {S:Finset I}{A:FC I} (h:Sector S b A) : Sector (S.map f) b (into f A):=by
 induction h with
 | zero=> rw [map_zero]; exact Sector.zero _
 | one=> rw [map_one]; exact Sector.one
 | up i u=> rw [put_in f i]; exact .up _ (mem_map_of_mem _ u)
 | down i u=> rw [take_in f i]; exact .down _ (mem_map_of_mem _ u)
 | scale _ c p=> rw [map_smul]; exact p.scale _
 | add _ _ p u=> rw [map_add]; exact p.add u
 | mul _ _ p u=> rw [map_mul]; exact p.mul u
lemma preimage {b:Bool}{G:Finset I}{A:FC J}(p:Sector (G.map f) b A) : ∃ B:FC I, Sector G b B ∧ into f B=A := by
 induction p with
 | zero=> exact ⟨_,.zero _,map_zero _⟩
 | one=> exact ⟨_,.one,map_one _⟩
 | up i u=> obtain ⟨x,v,rfl⟩:= mem_map.mp u; exact ⟨_,.up x v,put_in ..⟩
 | down i u=> obtain ⟨x,v,rfl⟩:= mem_map.mp u; exact ⟨_,.down x v,take_in ..⟩
 | scale _ c p=> obtain ⟨A,t,rfl⟩:=p; exact ⟨_,t.scale c,map_smul ..⟩
 | add _ _ p u=> obtain ⟨A,t,rfl⟩:=p; obtain ⟨B,w,rfl⟩:=u; exact ⟨_,t.add w,map_add ..⟩
 | mul _ _ p u=> obtain ⟨A,t,rfl⟩:=p; obtain ⟨B,w,rfl⟩:=u; exact ⟨_,t.mul w,map_mul ..⟩
lemma into_state (A:FC I){s:Finset J}{t:Finset I}(p:∀ x:I,f x∈s↔ x∈t): into f A s s = A t t:=by
 let v := s\lows f; have ht:Deck f v:=⟨disjoint_sdiff_self_right⟩; have hv:fog f v t=s:=by
    ext x; unfold fog v; by_cases h:x∈lows f
    · obtain ⟨i,hi,rfl⟩:= mem_map.mp h; simp [h,p]
    simp [h, show x ∉ t.map f from fun u=> h (map_subset_map.mpr (subset_univ t) u)]
 obtain ⟨z,e,T⟩:= knotW f v ht t; let F:=into f A; have hz := sigh f v ht (basisKet t) (acts A (basisKet t))
 rw [← insert_act _ _ _ ht, hoops,T,hv,map_smul,inner_smul_right,inner_smul_left] at hz; change z*(star z* _) = _ at hz; rw [←mul_assoc, mul_comm z,e,one_mul,basis_inner,basis_act,basis_inner,basis_act] at hz; exact hz
end YM.CF.Buffered.Cin
#print axioms YM.CF.Buffered.Cin.sector_in
#print axioms YM.CF.Buffered.Cin.into_inj
