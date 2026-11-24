import YM.CF.Peaks.Fly
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
def rideG : Single N→ Iota G:=fun x=> ((x.1.1,0,x.1.2),x.2)
def modest (x:Iota G) : Single N:=((x.1.1,x.1.2.2),x.2)
@[simp] lemma modestR (x:Single N): modest G (rideG G x)=x:=rfl
lemma injG:Injective (rideG G):=Function.LeftInverse.injective (modestR G)
def en (j:Iota G): Prop:= j.1.2.1=0
instance en_dec (j:Iota G):Decidable (en G j):=by unfold en; infer_instance
@[simp] lemma en_ride (i:Single N): en G (rideG G i):=rfl
lemma ride_mod (x:Iota G)(h:en G x): rideG G (modest G x)=x:=by
 obtain ⟨⟨i,r,a⟩,k⟩:=x; change r=0 at h; subst r; rfl

def extendK {A:Type*}[Zero A](T:Single N→Single N→A)(i j:Iota G): A:=if en G i∧en G j then T (modest G i) (modest G j) else 0
def endorse (T:Op (Single N)): Op (Iota G):=Matrix.of (extendK G T)
lemma rude (A B:Op (Single N)): endorse G A * endorse G B=endorse G (A*B):=by
  ext x y
  simp only [Matrix.mul_apply,endorse,Matrix.of_apply]; by_cases hy: en G x ∧ en G y; swap
  · rw [show extendK G (A*B) x y=0 from if_neg hy]; apply sum_eq_zero; intro j _; unfold extendK; split_ifs <;> simp_all
  rw [extendK,if_pos hy, Matrix.mul_apply]
  let f i:=extendK G A x i * extendK G B i y
  let Z:=univ.image (rideG G)
  change ∑ i,f i=_
  rw [← sum_subset Z.subset_univ]; swap
  · intro i _ h; have hv:¬ en G i:= fun he=>h (mem_image.mpr ⟨modest G i,mem_univ _, ride_mod _ _ he⟩); simp [f,Z, hv,extendK]
  unfold Z; rw [sum_image (injG G).injOn]; apply sum_congr rfl; intro i _; unfold f; simp [hy.1,hy.2,extendK,en_ride]
lemma endorse_add (A B:Op (Single N)): endorse G (A+B)=endorse G A+endorse G B:=by ext i j; by_cases h:en G i∧en G j <;> simp [h,extendK,endorse]
lemma endorse_sum {J:Type*}(S:Finset J)(A:J→Op (Single N)): endorse G (∑ i∈S,A i)=∑ i∈S, endorse G (A i):=by ext i j; by_cases h:en G i∧en G j <;> simp [h,extendK,endorse,Matrix.sum_apply]
lemma endorse_star(A):endorse G (star A)=star (endorse G A):=by ext i j; by_cases h:en G i <;> by_cases l:en G j <;> simp [h,l,extendK,endorse]
lemma endorsement (A:Op (Site N ×SpinIdx)): endorse G (A ⊗ₖ 1)= putlow G.count A ⊗ₖ 1:=by
  ext ⟨⟨i,r,b⟩,a⟩ ⟨⟨j,w,c⟩,z⟩; by_cases h:r=0 <;> by_cases g:w=0 <;> simp [h,g,en,putlow,endorse,extendK,modest,ite_mul]
lemma pledge (i:Iota G)(h:en G i)(e:ℝ)(ho:Odd G.count.val): (tempo G e).home i= (ratio G).embed ((forum N e).home (modest G i)):=by
  obtain ⟨⟨x,r,b⟩,a⟩:= i; change r=0 at h; rw [h]; change node (isle G (x,0))=(ratio G).embed (node x); rw [embed_node G ho]; simp [lift]
lemma nearR {x y:Site (More N)}(h:separation x y≤1): separation ((ratio G).embed x) ((ratio G).embed y) ≤ G.count.val:=by
  rw [separation,← Ratio.root_embed,← Ratio.root_embed,←map_sub,Ratio.root_embed]; refine Finset.sup_le fun i _=>?_
  have he := (component_le (x-y) i).trans h; rw [Ratio.lift_embed]; simp only [nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply,Int.natAbs_mul]
  exact (Nat.mul_le_mul_left _ he).trans_eq (by simp [ratio]) -- fix

def poolG (S:Seal (Site (More N))): Seal (Site (More P)):= S.biUnion fun i=> bay (terr _) ((ratio G).embed i) G.count.val
lemma cloud_pool (S:Seal (Site (More N))): S⊆ cloudG G (poolG G S) := by
  intro i hi; exact mem_filter.mpr ⟨mem_univ _,mem_biUnion.mpr ⟨i,hi,by simp [terr]⟩⟩
lemma grove_pool (S:Seal (Site (More N)))(h:Grove (terr _) S): Grove (terr _) (poolG G S) :=by
  induction h with
  | single x=> unfold poolG; rw [Finset.singleton_biUnion]; exact glen ..
  | @join S x y _ h g ih=>
    let W i:= bay (terr _) ((ratio G).embed i) G.count.val
    have he:(ratio G).embed y∈ W x:= (bay_mem _).mpr (nearR _ g)
    have hk:(ratio G).embed y∈poolG G S := mem_biUnion.mpr ⟨y,h,by simp [W,terr]⟩
    rw [show poolG G (insert x S)=W x ∪poolG G S from biUnion_insert]; exact Grove.unite (glen ..) ih he hk
lemma pool_card (S:Seal (Site (More N))): ((poolG G S).card:ℝ)≤ S.card*(16*(G.count.val+1:ℝ)^4):=by
  let W i:= bay (terr _) ((ratio G).embed i) G.count.val
  have he:(poolG G S).card≤∑ i∈S,(W i).card:= card_biUnion_le
  calc
    _ ≤ ∑ i∈S,((W i).card:ℝ):=by exact_mod_cast he
    _ ≤ ∑ _i∈S, (16*(G.count.val+1:ℝ)^4):= sum_le_sum fun i _=> Tenant.reach ..
    _ = _:=by simp
end YM.CF.Peaks
