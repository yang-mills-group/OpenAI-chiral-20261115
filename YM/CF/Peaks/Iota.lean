import YM.CF.Peaks.Pall
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
lemma crest_pose (t e) : endorse G 1*((torch G e).run t).val=endorse G ((bail N e).run (scaleG G t)).val ∧ ((torch G e).run t).val *endorse G 1 =endorse G ((bail N e).run (scaleG G t)).val:=by
  have he: (endorse G 1)=Fock.cutM (univ.filter fun x=> en G x):=by -- remove i
    ext x y; by_cases h:en G x <;> by_cases g:en G y
    · have hq : (modest G x=modest G y)=(x=y):=by apply propext; constructor; intro e; exact (ride_mod G x h|>.symm).trans ((congr_arg _ e).trans (ride_mod G y g)); rintro rfl; rfl
      simp only [endorse,extendK,Matrix.of_apply,h,g, and_self,ite_true,Matrix.one_apply,hq]; by_cases l:x=y <;> simp_all [Fock.cutM]
    all_goals by_cases l:x=y <;> simp_all [endorse,extendK,Fock.cutM]
  have C (y z:Iota G): endorse G ((bail N e).run (scaleG G t)).val y z = if en G y ∧ en G z then ((torch G e).run t).val y z else 0:=by
    obtain ⟨⟨x,r,a⟩,i⟩:=y; obtain ⟨⟨j,w,b⟩,v⟩:=z; by_cases h:r=0 <;> by_cases g:w=0 <;> simp [h,g, endorse,bail, extendK,torch,spur,tradew,en,scaleG,jump_apply,modest]
  constructor <;> ext i j <;> rw [show endorse G ( (1:Op _))=Fock.cutM (univ.filter fun x=> en G x) from he, C] -- matches other endorse1? inspect
  · rw [Fock.cutM,Matrix.diagonal_mul]; by_cases h:en G i <;> by_cases g:en G j <;> simp [h,g]
    have hh:i.1 ≠ j.1:=fun e=>g (by unfold en at *; simpa only [← e] using h)
    simp [torch,jump_apply,hh]
  rw [Fock.cutM, Matrix.mul_diagonal]; by_cases h:en G i <;> by_cases g:en G j <;> simp [h,g];
  have hh:i.1 ≠ j.1:=fun e=> h (by unfold en at *; simpa only [e] using g)
  simp [torch,jump_apply,hh]
variable {a c e d:ℝ}
def tallyP (L:Side) : ℝ:= 16*(L.val+1:ℝ)^4
lemma hail (ho:Odd G.count.val) {F:Chin N → Op (Single N)}(h:Solo a c F e)(hs:0≤d)(hb:d*tallyP G.count≤a): Crown (badge _) (torch G e) (torch G e) d c (fun x=> endorse G (F x.val.2)):=by
  obtain ⟨M,K,p,q,l⟩:=h
  let f:legal G e→Openc (More N) e:=fun x=> ⟨x.val.2,rightL G x.property⟩
  have hf: Continuous f := (continuous_snd.comp continuous_subtype_val).subtype_mk _
  let T S:=poolG G S; let H S (x:legal G e):=endorse G (M S (f x)); let U S:= extendK G (K S)
  have he (S): Suite (badge (legal G e)) (torch G e) (torch G e) (T S) (U S) (H S):=by
    refine ⟨⟨fun t v=> ?_,fun i j=>?_⟩,fun i j=>?_⟩
    · let V:= ((torch G e).run t).val; let W':=((tempo G e).drive t v); let w:= scaleG G t
      let B:= ((bail N e).run w).val
      have hh:N = N:=rfl
      have hg: M S (f W')*B=B*M S (f v):=(p S).frame w (f v)
      change H S W'*V= V*H S v
      let R:=endorse G 1; have ⟨h1,h2⟩:=crest_pose G t e
      calc
        _ = H S W'*(R*V):=by rw [← mul_assoc]; unfold H R; rw [rude,mul_one]
        _ = endorse G (M S (f W') * B):=by unfold H; rw [show R*V=endorse G B from h1, rude]
        _ = (V*R)* H S v:= by rw [hg, ← rude,show V*R=endorse G B from h2]
        _ = _:=by rw [mul_assoc]; unfold H R; rw [rude,one_mul]
    · by_cases h:en G i ∧ en G j; swap
      · simp_rw [H,U, endorse,Matrix.of_apply,extendK,if_neg h]; exact nothing ..
      simp_rw [H,U,endorse,Matrix.of_apply,extendK,if_pos h]
      have hh: S⊆ cloudG G (T S):=cloud_pool ..
      have hu: (forum N e).home (modest G i)∈ S→ (tempo G e).home i∈ T S:=fun p=>by rw [pledge _ _ h.1 e ho]; exact (mem_filter.mp (hh p)).2
      have hw:= (p S).expo (modest G i) (modest G j)
      refine ⟨hw.positive,fun e'=>?_,fun d=> hw.bounded _,fun x y=>(hw.variation (f x) (f y)).trans ?_, hw.connected.comp hf⟩
      · obtain ⟨hg,ha,hb⟩:=hw.triggered e'
        refine ⟨grove_pool G S hg,hu ha,?_⟩; rw [pledge _ _ h.2 _ ho]; exact (mem_filter.mp (hh hb)).2
      apply mul_le_mul_of_nonneg_left _ hw.positive
      change fare S x.val.2 y.val.2/ _≤ (fare (T S) x.val.1 y.val.1 + _)/ _
      exact div_le_div_of_nonneg_right ((fare_inc hh ..).trans (le_add_of_nonneg_left (fare_t ..))) (abs_nonneg _)
    by_cases h:en G i∧en G j
    · simp_rw [H,endorse,Matrix.of_apply,extendK,if_pos h]; exact fun V h γ q=> (p S).fuel _ _ V h (f ∘ γ) q.snd -- simplify
    simp_rw [H,endorse,Matrix.of_apply,extendK,if_neg h]; exact (badge _).con _
  have hp(S): rent d (T S)≤rent a S:=by
    apply Real.exp_monotone; calc
      _ ≤ d*(S.card*tallyP G.count):=mul_le_mul_of_nonneg_left (pool_card ..) hs
      _ = (d*tallyP G.count)*S.card:=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_right hb (by positivity)
  refine Crown.absorb T _ _ d q.posP _ he (fun x=>by change endorse G (F _)=_; rw [show F x.val.2= _ from l (f x),endorse_sum]) ?_ ?_
  · intro i; by_cases hi:en G i; swap
    · simp only [U,extendK,hi,false_and,ite_false,mul_zero,sum_const_zero]; exact q.posP
    let s:=univ.image (rideG G); rw [← sum_subset (subset_univ s)]; swap
    · intro j _ hh; have hp:¬en G j:= fun p=> hh (mem_image.mpr ⟨_,mem_univ _,ride_mod G j p⟩); simp [hp,U,extendK]
    unfold s; rw [sum_image (injG _).injOn]; apply le_trans _ (q.rows (modest G i)); apply sum_le_sum; intro j _; unfold U; simp only [extendK,hi,en_ride,and_self,modestR,ite_true]; exact sum_le_sum (fun s _=> mul_le_mul_of_nonneg_right (hp s) ((p s).nonn _ _))
  intro j; by_cases hi:en G j; swap
  · simp only [U,extendK,hi,and_false,ite_false,mul_zero,sum_const_zero]; exact q.posP
  let s:=univ.image (rideG G); rw [← sum_subset (subset_univ s)]; swap
  · intro i _ h; have hp:¬en G i:=fun p=>h (mem_image.mpr ⟨_,mem_univ _, ride_mod G i p⟩); simp [hp,U,extendK]
  unfold s; rw [sum_image (injG _).injOn]; apply le_trans _ (q.cols (modest G j)); apply sum_le_sum; intro i _; unfold U; simp only [extendK,hi,en_ride,and_self,modestR,ite_true]; exact sum_le_sum (fun s _=>mul_le_mul_of_nonneg_right (hp s) ((p s).nonn _ _))
lemma hailing {ι:Type*}(L:Side)(ho:Odd L.val)(A:WG ι)(h:Lively A): Save L false false (fun i N _ G x=> endorse G (A i N x.2)):=by
  obtain ⟨a,r,e,k,hR,hp,v,t⟩:=h; have hf:0<tallyP L:=by unfold tallyP; positivity
  exact ⟨a/tallyP L,r,e,div_pos k hf,hR,hp,v,fun i N F G he hv=> hail _ (he.symm ▸ ho) (t i N hv) (div_nonneg k.le hf.le) (by rw [he,div_mul_cancel₀ _ hf.ne'])⟩
end YM.CF.Peaks
