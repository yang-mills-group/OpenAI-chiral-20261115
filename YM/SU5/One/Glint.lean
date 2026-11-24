import YM.SU5.One.Bazaar
/-! # Separated pairs of pencils in support Banach system
Read off each simple component of product in pair lens argument- arrows evaluated at INDEPENDENT field values. This is pointwise label calculus in cost norm, not assertion that product interpretation on a chosen gauge history measure factorizes. Require just disjoint occupancy.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 5000
set_option synthInstance.maxSize 30000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry
open Satin
attribute [local instance] opCStarAlgebra
variable (S T:Finset Cover)(a b:Bool) (K:Calibration)(m: Side)
local notation "N"=> K.c m

lemma noTrespass (h:Disjoint S T)(p:Hosp (S∪T) N): Disjoint (Satin.region S N) (Satin.region T N):=by
 apply Finset.disjoint_left.mpr; intro x u v
 obtain ⟨y,U,rfl⟩:= mem_image.mp u; obtain ⟨z,V,e⟩:= mem_image.mp v
 exact Finset.disjoint_left.mp h U (p.seat_ (mem_union_right S V) (mem_union_left T U) e ▸ V)

variable (p:Hosp S (K.c m))(q:Hosp T (K.c m))(h: Disjoint (region S (K.c m)) (region T (K.c m)))
local notation "O"=> occupy S N p
local notation "W"=> occupy T N q
include h
lemma occupied_separately (i:Finset (Tag S))(j:Finset (Tag T)): Disjoint (i.map O) (j.map W):=by
 apply Finset.disjoint_left.mpr; intro x u v
 obtain ⟨y,H,rfl⟩:= mem_map.mp u; obtain ⟨z,t,e⟩:= mem_map.mp v
 have hp(L:Finset Cover)(J:Hosp L N)(a:Tag L): node (occupy L N J a).1.1 ∈ region L N:= by
   obtain ⟨⟨x,i,j⟩,u⟩:=a; exact mem_image.mpr ⟨nodeC x,u,(node_of ..).symm⟩
 exact Finset.disjoint_left.mp h (hp S p y) (Eq.mp (congrArg (fun x:Single N=> node x.1.1∈ region T N) e) (hp T q z)) -- congr arg
local notation "L₁"=> Squad S a
local notation "L₂"=> Squad T b

def carousel (x: Squad S a)(y: Squad T b): Finset (Single (K.c m)):= x.val.map O ∪ y.val.map W
local notation "P"=>carousel S T a b K m p q -- h? include h

lemma proves_carousel {x y f g} (t:carousel S T a b K m p q x y=carousel S T a b K m p q f g): x=f∧y=g:=by
 have hx(A B: Finset (Tag S))(C D: Finset (Tag T))(t': A.map O∪ C.map W= B.map O ∪ D.map W): A=B∧ C=D:=by
    have ht(S T U V:Finset (Single N))(eq:S∪U=T∪V)(h0:Disjoint S V)(h1:Disjoint T U):S=T:=by
       apply Subset.antisymm; intro x hF; exact (mem_union.mp (eq ▸ mem_union_left U hF)).resolve_right fun k=>Finset.disjoint_left.mp h0 hF k
       intro x hF; exact (mem_union.mp (eq.symm ▸ mem_union_left V hF)).resolve_right fun k=>Finset.disjoint_left.mp h1 hF k
    refine ⟨Finset.map_injective O (ht _ _ _ _ t' (occupied_separately S T K m p q h A D) (occupied_separately S T K m p q h B C)),?_⟩
    rw [union_comm,union_comm _ (D.map W)] at t'; exact Finset.map_injective W (ht _ _ _ _ t' (occupied_separately S T K m p q h B C).symm (occupied_separately S T K m p q h A D).symm)
 exact ⟨Subtype.ext (hx _ _ _ _ t).1,Subtype.ext (hx _ _ _ _ t).2⟩
local notation "φ"=> star (flake (Tset N)ᶜ)
lemma crumbProduct (x:L₁)(y:L₂):∃ z:ℂ,‖z‖=1 ∧ twist φ (spool N (tagWord S x.val) * spool N (tagWord T y.val))= z • poke (P x y):=by
 obtain ⟨z,r,k⟩:= museum S N p x.val
 obtain ⟨w,r',e⟩:= museum T N q y.val
 let i:= x.val.map O; let j:= y.val.map W; let c:= Poly.sail i j
 have hp : Disjoint i j:=occupied_separately S T K m p q h x.val y.val
 refine ⟨w * (z*c),?_,?_⟩
 · rw [norm_mul,r',norm_mul,r, show ‖c‖=1 by unfold c Poly.sail; simp [norm_prod,parity]]; simp
 rw [map_mul,velvetTag,velvetTag,k,e,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,show poke i*poke j=c • poke (P x y) from ?_,smul_smul,smul_smul]
 · rw [mul_assoc]
 change (Pastry.cane (Single N)).tag i * (Pastry.cane (Single N)).tag j=_; rw [Poly.tag_mul,if_pos hp]; rfl
local notation "θ" x:max y:max=> (crumbProduct S T a b K m p q h x y).choose

def pierce (x:Squad S a)(y:Squad T b): FC (Single N) →ₗ[ℂ] ℂ where
 toFun f:= crumb (twist φ f) (P x y)/θ x y
 map_add' _ _:= by rw [map_add,crumb_add,add_div]
 map_smul' _ _:= by rw [twist_scalar,crumb_scale,mul_div_assoc]; rfl
local notation "η"=>pierce S T a b K m p q h

lemma pierce_bound x y F : ‖η x y F‖ ≤ ‖F‖:=by
 change ‖(_/_:ℂ)‖≤ _; rw [norm_div,(crumbProduct S T a b K m p q h x y).choose_spec.1,div_one]; exact (norm_entry ..).trans_eq (twist_norm ..)

lemma pierce_read (x:Squad S a)(y:Squad T b) (u:Fields N)(F:Bazaar S a)(G:Bazaar T b):
   η x y ((fresco S a K F * fresco T b K G) m u)= daub S (F x) (Prod.map (onC _) (onC _) u) * daub T (G y) (Prod.map (onC _) (onC _) u):=by
 change η x y (reveal S a K m F u * reveal T b K m G u)=_
 rw [revealSpool,revealSpool, Finset.sum_mul]; simp_rw [Finset.mul_sum, Algebra.mul_smul_comm,Algebra.smul_mul_assoc,map_sum,map_smul]
 have ht(i:L₁)(j:L₂) : η x y (spool N (tagWord S i.val)* spool N (tagWord T j.val))= if x=i ∧ y=j then 1 else 0 := by
   change (crumb (twist φ _) (P x y) / _:ℂ) = _
   have hZ:= crumbProduct S T a b K m p q h i j|>.choose_spec
   rw [hZ.2,crumb_scale,Pastry.chip]
   split_ifs with k l l
   · obtain ⟨rfl,rfl⟩:=l; rw [mul_one,div_self]; exact norm_pos_iff.mp (zero_lt_one.trans_eq hZ.1.symm)
   · exact (l (proves_carousel S T a b K m p q h k)).elim
   · obtain ⟨rfl,rfl⟩:=l; exact (k rfl).elim
   · rw [mul_zero,zero_div]
 rw [sum_eq_single x,sum_eq_single y]; all_goals simp only [ht];
 · simp [mul_comm];
 · intro b mb hb; rw [if_neg]; simp; simp [Ne.symm hb]
 · simp
 · intro a ma ha; apply sum_eq_zero; intro t ht; rw [if_neg]; simp; simp [Ne.symm ha]
 simp

-- independent gauge points
lemma both_gauges (x y: Fields N) : ∃ z:Fields N, Agrees (region S N) z.1 x.1 ∧ Agrees (region S N) z.2 x.2 ∧ Agrees (region T N) z.1 y.1 ∧ Agrees (region T N) z.2 y.2:=by
 have ht (A B:Pane N): ∃ C:Pane N, Agrees (region S N) C A ∧ Agrees (region T N) C B:=by
   exact ⟨fun i=>if i.1∈ region S N then A i else B i,fun i v _=> if_pos v,fun i u _=> if_neg (fun k=> Finset.disjoint_left.mp h k u)⟩
 obtain ⟨C,r,k⟩:= ht x.1 y.1; obtain ⟨D',v,L⟩:= ht x.2 y.2; exact ⟨(C,D'),r,v,k,L⟩

-- evaluation lens including arguments (all labels use same gauge field and turn convention; decomposition only after purchase. Compare PaneReport CostsPair.)
lemma both_cards (x y: PairsC) (f:L₁)(g:L₂): ∃ u:Fields N,∀ M:Bazaar S a,∀ R:Bazaar T b,
   η f g ((fresco S a K M * fresco T b K R) m u)= daub S (M f) x*daub T (R g) y:=by
 obtain ⟨u,m1,m2,n1,n2⟩:= both_gauges S T K m h (replant S N x) (replant T N y)
 refine ⟨u,fun M R=>?_⟩; rw [pierce_read]
 -- via bounded evaluator and equal evaluations at matching host
 congr 1
 · rw [←glasses_reveal S a K m p,←glasses_readCover S a K m p]; exact congrArg _ ((revealSupport ..).dep _ _ m1 m2)
 rw [←glasses_reveal T b K m q, ←glasses_readCover T b K m q]; exact congrArg _ ((revealSupport ..).dep _ _ n1 n2)

-- uniform norm spectrum degree pin pi
end YM.CF.Buffered.Afterglow.Tapestry
