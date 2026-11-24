import YM.CF.BProof.Garden.Esker
/-! Orthogonal polynomials at site. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Garden
open Function Filter Fock NormedSpace Finset Align Wick Double Pastry
open scoped Topology Matrix MatrixOrder InnerProductSpace Kronecker BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I] {s p q:Finset I}{C:Op I}
def tiara (s:Finset I)(C:Op I)(p:Finset I):Wave I:=acts (crown C p) (pairWave (square s C))
def tube(C:Op I)(i:I):FC I:= thorn C i*star (thorn C i)
@[simp] lemma tube_self(i:I):star (tube C i)=tube C i:=by simp [tube]
theorem thorn_death(m:C∈unitary _)(h:Commute C (cutM s))(x:Cᵀ= -C)(i:I)(g:i∈s)(t:Finset I)(f:i∉t): acts (star (thorn C i)) (tiara s C t)=0:=by
 induction t using Finset.induction_on with
 | empty=>simp only [tiara,crown,sort_empty,List.map_nil,List.prod_nil,act_one,outlet h x g]
 | insert k t u ih=>
    rw [mem_insert,not_or] at f; let T:=thorn C i; let X:=thorn C k; have ht:star T*X= -(X*star T):=eq_neg_of_add_eq_zero_left ((thorn_mixed m i k).trans (if_neg f.1)); rw [tiara,← roofW_eq x,Poly.tag_any _ _ _ u,act_smul,map_smul,act_mul,←act_mul,show star (thorn C i)*(roofW C x).term k= -(X*star (thorn C i)) from ht,act_neg,act_mul, roofW_eq]; rw [←tiara,ih f.2,map_zero,neg_zero,smul_zero] -- tune
lemma thorn_form(m:C∈unitary _) (i:I) : star (thorn C i)*thorn C i = 1-tube C i:=eq_sub_of_add_eq ((thorn_mixed m i i).trans (if_pos rfl)) -- formula eq
lemma tube_heart(x:Cᵀ= -C)(i:I)(g:i∈p): acts (thorn C i) (tiara s C p)=0:=by rw [tiara,← act_mul]; rw [show thorn C i*crown C p=0 from (roofW C x).tag_mute p i g,act_zero]
lemma throne (m:C∈unitary _)(h:Commute C (cutM s))(x:Cᵀ= -C)(i:I)(g:i∈s)(t:Finset I) : acts (tube C i) (tiara s C t)=if i∈ t then tiara s C t else 0:=by
 split; rename_i p; · have ht:=tube_heart (s:=s) x i p; have hx:=congrArg (acts (star (thorn C i))) ht; rw [←act_mul,thorn_form m, act_sub,act_one, map_zero] at hx; exact (sub_eq_zero.mp hx).symm
 rw [tube,act_mul,thorn_death m h x i g t ‹_›,map_zero]
lemma tiara_norm(m:C∈unitary _)(h:Commute C (cutM s))(x:Cᵀ= -C)(g:p⊆ s) : ‖tiara s C p‖=‖pairWave (square s C)‖:=by
 induction p using Finset.induction_on with
 | empty=> simp [tiara,crown]
 | insert i p k ih=>
   let v:=tiara s C p; let T:=thorn C i; have he:‖acts T v‖=‖v‖:=by
      have h1:inner ℂ (acts T v) (acts T v)=inner ℂ v v:=by nth_rw 1 [← star_star T]; rw [act_inner, ←act_mul,show star T*T=1-tube C i from thorn_form m i,act_sub,act_one,throne m h x i (g (mem_insert_self ..)),if_neg k,sub_zero]
      have hp:=congrArg (RCLike.re (K:=ℂ)) h1; simp only [inner_self_eq_norm_sq] at hp; nlinarith [norm_nonneg v,norm_nonneg (acts T v)]
   rw [tiara,← roofW_eq x, Poly.tag_any _ _ _ k,act_smul,act_mul, roofW_eq,norm_smul,show ‖parity i p‖=1 by simp [parity], one_mul]; exact he.trans (ih ((subset_insert ..).trans g))
theorem tiara_dice(m:C∈unitary _)(h:Commute C (cutM s))(x:Cᵀ= -C)(g:p⊆ s)(w:q⊆ s)(f:p≠ q) : inner ℂ (tiara s C p) (tiara s C q)=0:=by
 have he {p q:Finset I}(g:p⊆s){i:I}(f:i∈ p)(e:i∉q): inner ℂ (tiara s C p) (tiara s C q)=0:=by nth_rw 1 [← (show acts (star (tube C i)) (tiara s C p)=tiara s C p from (by rw [tube_self,throne m h x i (g f),if_pos f]))]; rw [act_inner,throne m h x i (g f),if_neg e,inner_zero_right]
 by_cases p':p⊆q
 · obtain ⟨i,j,k⟩:= Finset.not_subset.mp (show ¬ q ⊆ p from fun h=> f (Subset.antisymm p' h)); rw [←inner_conj_symm,he w j k,map_zero]
 obtain ⟨i,j,k⟩:= Finset.not_subset.mp p'; exact he g j k
lemma crown_owns (h:Commute C (cutM s))(f:p⊆ s) : Sector s (decide (¬Even p.card)) (crown C p):=by -- no skew needed
 induction p using induction_on_min with
 | empty=> simp only [crown,sort_empty,List.map_nil,List.prod_nil,card_empty,Even.zero,not_true_eq_false,decide_false]; exact Sector.one
 | insert i t H ih=>
   have he:i∉t:=fun v=>lt_irrefl _ (H _ v); have ht:∃ n, t.card=n:=⟨_,rfl⟩; unfold crown; rw [sort_insert _ (fun j g=>(H _ g).le) he,List.map_cons,List.prod_cons,card_insert_of_notMem he]; have hx:¬Even (t.card+1)↔ Even t.card:=by rw [Nat.even_add_one]; simp only [not_not]
   have hy:(true.xor (decide (¬ Even t.card)))=decide (¬ Even (t.card+1)):=by by_cases h: Even t.card<;> simp [hx,h] -- tune hx simpl
   rw [←hy]; exact (thorn_occupy h (f (mem_insert_self ..))).mul (ih ((subset_insert ..).trans f))
theorem tiara_zone (h:Commute C (cutM s))(g:p⊆s) : zone s (tiara s C p):= by unfold tiara; rw [←plump_vac,←act_mul]; exact homeZone ((crown_owns h g).mul (plump_here ..))
end YM.CF.BProof.Garden
