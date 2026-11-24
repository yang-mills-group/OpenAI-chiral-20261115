import YM.Next.RANK.Axial
import YM.Next.RANK.Ray
/-!
# Upper angular pressure geometry: interior tiles and coverage
- on the *real period*, optional seams. put center in time ≠0 and whole tile never overlaps that seam.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 600000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Galope
open Function Finset Matrix Lattice Wilson RG Next.Rank Spindle
open scoped Topology InnerProductSpace Matrix ContDiff BigOperators Classical Kronecker Matrix.Norms.Frobenius
variable {n:Side}{k w v i:ℕ}
local notation "θ" => YM.timeAxis

namespace Avenue
abbrev shank(M:ℕ):=2*M+1
def degreeP(n:Side)(M:ℕ):ℕ:=(n.val-1)/shank M
abbrev Blocks(n:Side)(M:ℕ):=Axis→Fin (degreeP n M)
theorem num(n:Side)(M:ℕ): Fintype.card (Blocks n M)=(degreeP n M)^4:=by simp [Blocks,Axis]
variable {M:ℕ}
theorem lang(n:Side)(M:ℕ): 1+degreeP n M*shank M≤ n.val ∧ n.val < 1+(degreeP n M+1)*shank M :=by
 have h:= Nat.div_add_mod (n.val-1) (shank M); have hw:0<shank M:=by unfold shank; omega
 change shank M*degreeP n M+_=_ at h; have he:= Nat.mod_lt (n.val-1) hw; rw [add_mul,_root_.one_mul,Nat.mul_comm (degreeP _ _)] -- tune
 have hp0:n.val=n.val-1+1:= (Nat.sub_add_cancel n.property).symm
 generalize (n.val-1)%shank M=q at h he; generalize shank M*degreeP n M=W at h ⊢; omega
abbrev markA(i:Fin (degreeP n M)):ℕ:= i.val *shank M +1
theorem start_bound(i:Fin (degreeP n M)): 0<markA i ∧ markA i+shank M≤ n.val:=by
 have hv:= Nat.mul_le_mul_right (shank M) (i.isLt); change (i.val+1)*shank M ≤ _ at hv; rw [_root_.add_mul,_root_.one_mul] at hv; have hp:= (lang n M).1; unfold markA; omega -- tune
abbrev atM(i:Fin (degreeP n M)):ℕ:=markA i+M
def planM(b:Blocks n M): Site n:=fun i=> ((atM (b i):ℕ):Per n)
lemma rankL(i:Fin (degreeP n M)):atM i<n.val:=by have he:=start_bound i; unfold atM; unfold shank at he; omega
lemma pitchA(b:Blocks n M)(i:Axis):((planM b) i).val=atM (b i):= by rw [planM,ZMod.val_natCast_of_lt (rankL _)]
lemma liftA{a b:ℕ}(v:a*shank M < b*shank M): a<b:=lt_of_not_ge fun h=> not_lt_of_ge (Nat.mul_le_mul_right _ h) v
lemma atM_ins(h:ℕ): Injective (atM (M:=h) (n:=n)):=by intro i j e; apply Fin.ext; unfold atM markA at e; exact mul_right_cancel₀ (Nat.succ_ne_zero _) (Nat.add_right_cancel (Nat.add_right_cancel e))
lemma plan_in(n:Side)(M:ℕ): Injective (planM (n:=n) (M:=M)):= fun i j e=>funext fun k=> atM_ins M (((pitchA i k).symm.trans <| congr_arg (fun x:Site n=>(x k).val) e).trans (pitchA j k))
def zones(n:Side)(M:ℕ):Finset (Site n):=univ.image (fun b:Blocks n M=> planM b)
lemma collect(n:Side)(M:ℕ) : (zones n M).card=(degreeP n M)^4:=by rw [zones,card_image_of_injective,card_univ,num]; exact plan_in n M
/-- markA physical footing (coordinates in [1,n)). Runs in INTEGER natCast val. -/
lemma leaseA(b:Blocks n M) (x:Cover)(hx:x∈box M)(j:Axis):
 (((wrap n x+ planM b: Site n) j).val : ℤ)= x j+ atM (b j):=by
 let i:=b j; let q:=x j+(atM i:ℤ); obtain ⟨l,r⟩:=box_test.mp hx; have hv:= r j; have hL:= l j; have ht:= start_bound i
 have hu: 0≤ q ∧ q < (n.val:ℤ):=by unfold q atM; unfold shank at ht; omega
 have hm: (q.toNat:ℤ)=q:=Int.toNat_of_nonneg hu.1
 rw [show (wrap n x+planM b: Site n) j=(q.toNat:Per n) by change ((x j:ℤ):Per n) + (atM i:Per n)=_; rw [show (q.toNat:Per n)=((q.toNat:ℤ):Per n) by simp only [Int.cast_natCast], hm]; simp only [q,Int.cast_add,Int.cast_natCast], ZMod.val_natCast_of_lt (by omega)]; exact hm
lemma from_lease(b:Blocks n M)(x:Site n)(hx:x∈ Spindle.patch M (planM b))(j:Axis): markA (b j) ≤ (x j).val ∧ (x j).val < markA (b j)+shank M:=by
 rw [patch_eq] at hx; obtain ⟨p,h,rfl⟩:=mem_image.mp hx; have he:=leaseA b p h j; obtain ⟨l,r⟩:=box_test.mp h; have hg:=l j; have hz:=r j; unfold atM at he; unfold shank; omega -- tune
lemma seam_zero {o:Site n}(h:o∈ zones n M) : ∀ x ∈ Spindle.patch M o, x θ≠0:=by -- implicit tune
 obtain ⟨p,-,rfl⟩:=mem_image.mp ‹o∈ zones n M›; intro x hx y; obtain ⟨l,r⟩:=from_lease p x hx θ; have he:= (start_bound (p θ)).1; rw [y,ZMod.val_zero] at l; omega
lemma orderA {i j:Fin (degreeP n M)}(h:i.val< j.val): markA i + shank M≤ markA j :=by
 have ht:= Nat.mul_le_mul_right (shank M) (h); change (i.val+1) *shank M ≤ _ at ht; rw [add_mul,one_mul] at ht; unfold markA; omega
lemma no_double {i j:Site n}(p:i∈zones n M)(q:j∈zones n M){x:Site n} (o:x∈Spindle.patch M i)(o':x∈Spindle.patch M j): i=j:=by
 obtain ⟨f,-,rfl⟩:=mem_image.mp p; obtain ⟨g,-,rfl⟩:=mem_image.mp q; suffices he:f=g by rw [he]
 apply funext; intro k; have he:=from_lease f x o k; have hz:=from_lease g x o' k; apply Fin.ext; apply le_antisymm
 · by_contra! h; have hm:=orderA (i:=g k ) (j:=f k) h; omega
 by_contra! h; have hm:=orderA (i:=f k ) (j:=g k) h; omega
lemma patch_includes(k v:ℕ)(H:k≤v)(o:Site n): Spindle.patch k o⊆Spindle.patch v o:= fun _ p=> (doors _).mpr (((doors _).mp p).trans H)
lemma extend(o:Site n)(i j:Site n)(h:separation i j≤w)(g:i∈ Spindle.patch k o) : j∈Spindle.patch (k+w) o:= (doors _).mpr ((separation_triangle o i j).trans (add_le_add ((doors _).mp g) h))
lemma out_tile(A: Finset (Face (Per n)))(M:ℕ): A.card≥ ((zones n M).filter (fun o=> ∃ x ∈ A,x.1∈Spindle.patch M o)).card:=by
 let D:=(zones n M).filter (fun o=> ∃ x ∈ A,x.1∈Spindle.patch M o)
 choose x hx hz using fun i:↥D=> (mem_filter.mp i.property).2; refine le_trans (b:=Fintype.card (↥A)) ?_ (by simp); rw [← Fintype.card_coe]; exact Fintype.card_le_of_injective (fun i:↥D=> (⟨x i,hx i⟩:↥A)) fun i j h=>Subtype.ext (no_double (mem_filter.mp i.2).1 (mem_filter.mp j.2).1 (hz i) (by rw [show x i=x j from congrArg Subtype.val h]; exact hz j))
abbrev OffA(A:Finset (Face (Per n)))(M:ℕ): Finset (Site n):= (zones n M).filter (fun i=>∃ x∈A, x.1∈Spindle.patch M i)
def glow(A:Finset (Face (Per n)))(M:ℕ): Finset (Site n):= zones n M\OffA A M
lemma glow_in(A:Finset (Face (Per n)))(M:ℕ): glow A M⊆ zones n M:=sdiff_subset
lemma glow_count(A:Finset (Face (Per n)))(M:ℕ): (degreeP n M)^4 ≤ (glow A M).card+A.card:=by
 let q:=OffA A M; exact le_trans (b:=(glow A M).card+q.card) ((Finset.card_sdiff_add_card_eq_card (filter_subset ..)).trans (collect n M)).symm.le (Nat.add_le_add_left (out_tile ..) _)

abbrev Hor:= Finset.univ.erase θ
lemma count_hor: Hor.card=3:=by simp [Hor]; -- tune
lemma time_n{a:Axis}(h:a≠θ): a<θ:=lt_of_le_of_ne (Fin.le_last _) h
lemma patch_fore{k:ℕ}{a b:Cover}(p:2*(k+1)<n.val)(ha:a∈box k)(hb:b∈box k)(h:wrap n a=wrap n b):a=b:=by
 rw [←borne p a ha,←borne p b hb,h]
lemma palette(k:ℕ): ((box k).filter fun i:Cover=> i θ≠0).card=2*k*shank k^3:=by
 let V(i:Axis):= if i=θ then (layers k).erase 0 else layers k
 rw [show ((box k).filter fun i:Cover=>i θ≠0)= Fintype.piFinset V by
       ext p; rw [mem_filter,box_iff_layers,Fintype.mem_piFinset]; constructor
       · rintro ⟨hp,h⟩ j; by_cases hj:j=θ <;> simp [V,hj,hp,h] -- tune
       intro h; constructor
       · intro i; have hi:=h i; by_cases hp:i=θ; rw [show V i=_ from if_pos hp] at hi; exact mem_of_mem_erase hi; rw [show V i=layers k from if_neg hp] at hi; exact hi
       have hp:=h θ; rw [show V θ=_ from if_pos rfl] at hp; exact (mem_erase.mp hp).1, Fintype.card_piFinset, ←mul_prod_erase univ _ (mem_univ θ)]
 have h: (V θ).card=2*k:=by unfold V; rw [if_pos rfl,card_erase_of_mem,card_layers, Nat.add_sub_cancel]; simp [layers] -- tune
 rw [h]; congr 1; rw [prod_congr rfl (g:=fun _=>shank k) (fun i p=>by unfold V; rw [if_neg ((mem_erase.mp p).1), card_layers]),prod_const,show _=3 from count_hor] -- tune
lemma core_count {o:Site n}(u:o∈zones n M)(hv:k≤M)(h:2*(M+1)<n.val) : ((Spindle.patch k o).filter fun (i:Site n)=>i θ≠o θ).card=2*k*shank k^3:=by
 obtain ⟨j,-,rfl⟩:=mem_image.mp u; let b:=planM j
 let v:=fun x:Cover=> wrap n x+b
 rw [←palette] -- tune maybe no goals
 let V:= (box k).filter (fun i:Cover=>i θ≠0)
 have hp(x:Cover)(hx:x∈box k): v x θ≠ b θ ↔ x θ≠0:=by
    rw [ne_eq,← (ZMod.val_injective n.val).eq_iff]; -- tune
    have ht: x∈box M:=box_test.mpr ⟨fun j=>le_trans (neg_le_neg (Int.ofNat_le.mpr hv)) ((box_test.mp hx).1 j),fun j=>le_trans ((box_test.mp hx).2 j) (Int.ofNat_le.mpr hv)⟩
    have he: (((v x θ).val):ℤ)=x θ+(atM (j θ):ℤ):= leaseA j x ht θ -- syntax tune
    rw [show b=planM _ from rfl,pitchA]; omega
 suffices hf: ((Spindle.patch k b).filter fun (i:Site n)=>i θ≠ b θ)=V.image v by
    change ((Spindle.patch k b).filter _).card=_; rw [hf,card_image_of_injOn]; intro a ha t ht eq; exact patch_fore (by omega:2*(k+1)<n.val) (mem_filter.mp ha).1 (mem_filter.mp ht).1 (add_right_cancel eq)
 ext x; rw [mem_filter, patch_eq,mem_image,mem_image]; constructor
 · rintro ⟨⟨y,t,rfl⟩,e⟩; exact ⟨y,mem_filter.mpr ⟨t,(hp y t).mp e⟩,rfl⟩
 rintro ⟨y,t,rfl⟩; obtain ⟨z,e⟩:=mem_filter.mp t; exact ⟨⟨y,z,rfl⟩,(hp y z).mpr e⟩
def slab(o:Site n)(k:ℕ): Finset (Edge (Site n)):= ((Spindle.patch k o).filter (fun (i:Site n)=> i θ≠o θ)) ×ˢ Hor
def buy(Z:Finset (Site n))(k:ℕ) := Z.biUnion (fun i=> slab i k)
lemma buys_count (Z:Finset (Site n))(hv:Z⊆zones n M)(h:k≤M)(u: 2*(M+1)<n.val): (buy Z k).card=Z.card*(2*k*shank k^3*3):=by
 unfold buy; rw [card_biUnion]; swap; · intro i p j q e; exact Finset.disjoint_left.mpr (fun x t t'=> e (no_double (hv p) (hv q) (patch_includes k M h _ (mem_filter.mp (mem_product.mp t).1).1) (patch_includes k M h _ (mem_filter.mp (mem_product.mp t').1).1))) -- tune
 rw [sum_congr rfl (g:=fun _=>2*k*shank k^3*3) (fun i p=> by rw [slab,card_product, core_count (hv p) h u,count_hor]), sum_const]; simp
lemma excluded{Z:Finset (Site n)}(hz:Z⊆zones n M)(h:k≤M)(p:Edge (Site n))(hp:p∈ buy Z k): p.1 θ≠0 ∧ p.2≠θ ∧ p∉ (Axial.axle n).trunks:=by
 obtain ⟨i,v,hv⟩:= mem_biUnion.mp hp; obtain ⟨j,hs⟩:= mem_product.mp hv -- tune
 have hy:= seam_zero (hz v) p.1 (patch_includes _ _ h _ (mem_filter.mp j).1); have he:p.2≠θ:= (mem_erase.mp hs).1; exact ⟨hy,he,fun p'=>hy (((Next.Rank.Axial.trunk_here ..).mp p').2 _ (time_n he))⟩
end Avenue
end YM.SU5.FiniteGaugeData.Galope
