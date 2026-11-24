import YM.SU5.FiniteGaugeData.Signal.Vintage
/-!
Suppression mark and intent: local, overlaps NOT permitted between advanced tiles,
BULK degrees inside tile. Compute replacement using missing-lower creators cost. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Signal.Furnace.Vine
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Scree Pastry
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology ContDiff ComplexOrder Kronecker Classical
attribute [local instance] opCStarAlgebra
open Phase Spire
variable {n I:Type*}[LinearOrder n][Fintype n]
variable {P X:Op n}(h:IsStarProjection P)(q:TagG P X){S T:Finset n}
variable (L:List I)(w y:I→ Ket n)
local notation "Q"=> cutM T
local notation "R↓"=> lineOp (cutM T)
local notation "R" i:max=> remove (w i)
local notation "A↓" i:max=> create (y i)
local notation "D" i:max=> create (acts (cutM T) (y i))

def ignition (T:Finset n)(w y:Ket n):FC n:= 1+ remove w * create (acts (cutM T) y)
def radiate := (L.map (fun i=> ignition T (w i) (y i))).prod -- T implicit still?

variable (a:∀ i∈L,acts (cutM T) (w i)=0)(p:∀ i∈L,∀ j∈L,inner ℂ (w i) (y j)= if i=j then 1 else 0)(r:L.Nodup)
lemma hideL (y:Ket n): lineOp (cutM T) * create (acts (1-Q) y)=0:=by
 let X:=R↓; apply star_injective; rw [star_mul,star_zero]; have hp:IsStarProjection X:=line_proj (cutM_idp _); rw [hp.isSelfAdjoint.star_eq]; apply op_columns; intro j; rw [act_mul,act_zero]; refine tars (cutM_idp T) (by change acts X _=_; rw [←act_mul,hp.isIdempotentElem.eq]) ?_; rw [←act_mul, Porth (cutM_idp _),act_zero] -- syntax?
lemma piling {Z:FC n}(A:I→FC n)(L:List I)(e:∀ i∈L,Commute Z (A i)): Commute Z (L.map A).prod:= Commute.list_prod_right _ _ fun x l=>by
 obtain ⟨y,k,rfl⟩:= List.mem_map.mp l; exact e y k
private lemma punch (Z U W:FC n)(a:Z*U+U*Z=0)(b:Z*W+W*Z=0): Commute Z (U*W):= by
 change Z*_= _; rw [←mul_assoc, eq_neg_of_add_eq_zero_left a, neg_mul, mul_assoc, eq_neg_of_add_eq_zero_left b, mul_neg,neg_neg,←mul_assoc]
include a p
lemma quarry (i j:I)(A:i∈L)(B:j∈L)(x:i≠j):Commute (create (acts (1-Q) (y j))) (ignition T (w i) (y i)):=by
 let f:= acts (1-Q) (y j); let v:=w i; have he:inner ℂ v f=0:=by
    unfold f; rw [←act_inner,(cutM_idp _).one_sub.isSelfAdjoint.star_eq, act_sub,act_one,a i A,sub_zero,p i A j B,if_neg x]
 apply (Commute.one_right _).add_right; exact punch _ _ _ (by rw [add_comm, car, he,zero_smul]) (car_create ..)
include r
lemma falling : R↓*(radiate (T:=T) L w y)= R↓*(L.map (fun i=> R i*A↓ i)).prod:=by
 induction L using List.reverseRecOn with
 | nil=> rfl
 | append_singleton L x ih=>
   let u:= L++[x]; have B:x∈u:=by simp [u]
   have ht(i)(v:i∈L):i∈ u:= by simp [u,v]
   have hN:x∉L:= fun v=> (List.nodup_append'.mp r).2.2 v List.mem_cons_self -- tune
   let Z:= radiate (T:=T) L w y; have hv:= ih (fun i c=> a i (ht i c)) (fun i c j d=> p i (ht i c) j (ht j d)) (List.nodup_append'.mp r).1
   unfold radiate; rw [List.map_append,List.prod_append,List.map_append,List.prod_append,←mul_assoc,←mul_assoc,←hv]; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
   change R↓*Z*_= R↓*Z*(R x*A↓ x)
   have he(i j): i∈L→ j=x→ Commute (create (acts (1-Q) (y j))) (ignition T (w i) (y i)):=by intro l hj; subst j; exact quarry u w y a p _ x (ht i l) B (fun g=>hN (g ▸ l))
   let f:= acts (1-Q) (y x); have hl : y x=f+acts Q (y x):= by unfold f; rw [act_sub,act_one,sub_add_cancel]
   have hs:inner ℂ (w x) f=1:=by unfold f; rw [← act_inner,(cutM_idp _).one_sub.isSelfAdjoint.star_eq,act_sub,act_one,a x B,sub_zero,p x B x B,if_pos rfl]
   rw [show R x*A↓ x = ignition T (w x) (y x)-create f*R x from ?_,mul_sub]; swap
   · nth_rw 1 [hl]; have hy:= car (w x) f; rw [hs,one_smul] at hy; unfold ignition; rw [map_add, mul_add]; rw [←hy]; abel
   rw [show R↓*Z*(create f*R x)=0 from ?_,sub_zero]; rw [←mul_assoc, mul_assoc _ Z, show Z*create f=create f*Z from (piling _ L (fun i h=> he i x h rfl)).eq.symm,←mul_assoc, hideL, zero_mul,zero_mul]

omit r p a
-- anticommute each nonlocal factor creator past subsequent removals, keep phase in left operator
private lemma hike (A: FC n) (f:I→FC n)(L:List I)(v:∀ i∈L,A*f i=-(f i*A)) : ∃ c:ℂ,‖c‖=1∧A*(L.map f).prod=c • ((L.map f).prod*A):=by
 induction L with
 | nil=> exact ⟨1,norm_one,by simp⟩
 | cons i L ih=> obtain ⟨c,h,p⟩:=ih (fun j v'=>v j (List.mem_cons_of_mem _ v')); refine ⟨-c,by rw [norm_neg,h],?_⟩; rw [List.map_cons,List.prod_cons,←mul_assoc,v i List.mem_cons_self,neg_mul,mul_assoc,p,Algebra.mul_smul_comm,neg_smul,mul_assoc]

include p r
lemma traction : ∃ c:ℂ, ‖c‖=1 ∧ (L.map (fun i=> R i*A↓ i)).prod = c • ((L.map (remove ∘ w)).prod*(L.map (fun i=> create (y i))).prod):= by
 induction L with
 | nil=> exact ⟨1,norm_one,by simp⟩
 | cons i L ih=>
                  obtain ⟨h,g⟩:=List.nodup_cons.mp r; have ht(j)(p:j∈L): j∈ i::L:=by simp [p]
                  obtain ⟨c,hC,hp⟩:=ih (fun i x j z=>p i (ht i x) j (ht j z)) g; let R':=remove ∘ w; have ht2(j:I)(v:j∈L): create (y i)*R' j= -(R' j*create (y i)):=by
                    apply eq_neg_of_add_eq_zero_left; rw [add_comm]; change antiB (R j) (A↓ i)=0; rw [antiB, car,p j (ht j v) i List.mem_cons_self, if_neg (fun (p:j=i)=> h (p ▸ v)),zero_smul]
                  obtain ⟨d,t,v⟩:= hike (A↓ i) R' L ht2
                  refine ⟨c*d,by rw [norm_mul,t,hC,mul_one],?_⟩; simp only [List.map_cons,List.prod_cons,hp, Algebra.mul_smul_comm,←smul_smul]
                  let x:= (L.map R').prod; let y':= (L.map (fun i=> create (y i))).prod; apply congrArg; calc
                     R i*A↓ i*(x*y')=R i*(A↓ i*x)*y':= by simp only [mul_assoc]
                     _ = _:= by rw [show A↓ i * x= _ from v]; simp only [R', x,comp_apply,Algebra.smul_mul_assoc,Algebra.mul_smul_comm, mul_assoc]; rfl

include p a r
variable {H c:ℝ}[Nonempty n]
lemma crucible (l:∀ i∈L,acts (cutM S) (y i)=y i)(u:∀ i∈L,acts (cutM S) (w i)=w i)(v:∀ i∈L,Spike.lit P X H c (A↓ i))(k:∀ i∈L,‖w i‖≤1): riveted P X H c S T L.length (radiate (T:=T) L w y):=by
 obtain ⟨d,d',q⟩:=traction L w y p r; let g:= remove ∘ w; let Z:=(L.map g).prod; let M:=L.map (fun i=>create (y i)); obtain ⟨x,hx⟩:= parityOf (S:=S) (L.map g) (by intro i h; obtain ⟨j,t,rfl⟩:=List.mem_map.mp h; exact (Sector.makeP _ (u _ t)).contr)
 refine ⟨M,d • Z,by simp [M],⟨x,hx.scale _⟩,?_,?_,?_⟩
 · intro i a; obtain ⟨j,h,rfl⟩:=List.mem_map.mp a; exact ⟨Sector.makeP _ (l _ h),v _ h⟩
 · rw [norm_smul,d',one_mul];
   have he (L:List I)(t:∀ i∈L,‖w i‖ ≤ 1): ‖(L.map g).prod‖≤1:=by
      induction L with
      | nil=> simp
      | cons i L ih=> exact (norm_mul_le (g i) _).trans ((mul_le_mul ((Flare.cost_pe true _).trans (t i List.mem_cons_self)) (ih (fun i h=>t i (List.mem_cons_of_mem _ h))) (norm_nonneg _) (zero_le_one)).trans_eq (one_mul _))
   exact he L k
 rw [falling L w y a p r,q,Algebra.smul_mul_assoc]
end YM.CF.Signal.Furnace.Vine
#print axioms YM.CF.Signal.Furnace.Vine.crucible
