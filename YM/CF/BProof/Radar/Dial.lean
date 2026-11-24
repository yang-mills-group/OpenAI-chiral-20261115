import YM.CF.BProof.Radar.Rej
import YM.CF.BProof.Tetrad.Sport
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Tetra
open Function Finset Equiv Regard
open scoped BigOperators Classical
variable {I:Type*}[AddCommGroup I][Finite I](v:I)
namespace Wrap
abbrev dial :ℕ:= addOrderOf v
instance base(x:I):NeZero (dial x):= ⟨(addOrderOf_pos x).ne'⟩
lemma more(u:v≠0):2≤dial v:=by have hv:addOrderOf v ≠ 1:= mt (AddMonoid.addOrderOf_eq_one_iff|>.mp) u; have hr:= addOrderOf_pos v; unfold dial; omega
abbrev Hub(v:I):= I ⧸ (AddSubgroup.zmultiples v)
abbrev radius (i:I) : Hub v:= (QuotientAddGroup.mk' _) i
def root(i:Hub v) : I:= Classical.choose (QuotientAddGroup.mk'_surjective _ i)
lemma root_p(i:Hub v):radius v (root v i)=i:= Classical.choose_spec (QuotientAddGroup.mk'_surjective _ i)
local notation "T_"=> Fin (dial v)
def old(i:Hub v)(k:Fin (dial v)):= root v i+k.val • v
lemma route_v(i k):radius v (old v i k)= i:=by unfold old radius; rw [map_add,(show (QuotientAddGroup.mk' _) (root v i)= _ from root_p v i)]; apply Eq.trans (congrArg (fun x=>i+x) (show QuotientAddGroup.mk' _ (k.val • v)=(0:Hub v) from QuotientAddGroup.eq_zero_iff _|>.mpr (AddSubgroup.nsmul_mem_zmultiples v k.val))) (add_zero _)
lemma houseB(i:Hub v)(x y:T_):old v i (x+y)=old v i x+y.val • v :=by unfold old; rw [Fin.val_add]; rw [show ((x.val+y.val)% (dial v)) • v= _ from mod_addOrderOf_nsmul v (x.val+y.val),add_smul,add_assoc]
open Fin.NatCast in
lemma house(i:Hub v)(x:T_): old v i (x+1)=old v i x+ v:=by rw [houseB]; change _+ ((↑(1:ℕ):Fin (dial v)).val) • v=_; rw [Fin.val_natCast, show (1 % dial v) • v= _ from mod_addOrderOf_nsmul v 1,one_smul]
lemma bornV : Bijective (Function.uncurry (old v)):=by
 let Q:= finEquivZMultiples (isOfFinAddOrder_of_finite v); have ht(i:T_): i.val • v=(Q i).val:=rfl
 constructor
 · rintro ⟨x,i⟩ ⟨y,j⟩ h; change old v x i=old v y j at h; have hh:x=y:=(route_v v x i).symm.trans (h ▸ route_v v y j); subst y; unfold old at h; rw [ht i,ht j] at h; rw [Q.injective (Subtype.ext (add_left_cancel h))]
 intro x; let i:=radius v x; have hx:x-root v i∈ AddSubgroup.zmultiples v:= (QuotientAddGroup.eq_zero_iff ..).mp (show QuotientAddGroup.mk' (AddSubgroup.zmultiples v) _= 0 from by rw [map_sub,(show (QuotientAddGroup.mk' _) (root v i)= _ from root_p v i)]; unfold i radius; simp )
 obtain ⟨j,h⟩:= Q.surjective ⟨_,hx⟩; exact ⟨(i,j),show root v i+_=_ from (by rw [ht j,h]; simp)⟩
def boy(v:I):Hub v × Fin (dial v)≃ I:= Equiv.ofBijective (Function.uncurry (old v)) (bornV v)
abbrev Hill(v:I) := Hub v→Cage (dial v)
lemma pull_n(p:v≠0):Nonempty (Hill v) :=by have k:= inherit (more v p); infer_instance -- local instance binder?
def pallet(w:Hill v)(i:I):Tone:= let j:=(boy v).symm i; color (w j.1) j.2
lemma tint (w:Hill v)(i:Hub v)(j:T_): pallet v w (old v i j)=color (w i) j:=by unfold pallet; rw [show old v i j=boy v (i,j) from rfl, Equiv.symm_apply_apply]
lemma proper(p:v≠0)(w:Hill v)(i:I): pallet v w i≠ pallet v w (i+v):=by obtain ⟨⟨x,y⟩,rfl⟩:= (bornV v).2 i; change pallet v w (old v x y) ≠ pallet v w (old v x y+v); rw [←house,tint,tint]; exact colors (more v p) (w x) y -- tune
lemma known {a b:Finset I}(p:v≠0)(u:Disjoint a b)(h:∀ i∈a, i+v∉b)(g:∀ i∈b,i+v∉a): Pen a b (pallet v):=by
 let S(s:Finset I)(i:Hub v):=(univ : Finset (Fin (dial v))).filter (fun j=>old v i j∈ s)
 have ht(s i j): j∈ S s i ↔ old v i j∈s:=by simp [S]
 choose Q hQ using fun i=>marked (a:=S a i) (b:=S b i) (more v p) (Finset.disjoint_left.mpr fun t x y=> Finset.disjoint_left.mp u ((ht _ _ _).1 x) ((ht _ _ _).1 y)) (fun t x y=>h _ ((ht _ _ _).1 x) (house v i t ▸ (ht _ _ _).1 y)) (fun t x y=>g _ ((ht _ _ _).1 x) (house v i t ▸ (ht _ _ _).1 y))
 refine ⟨piece (w:=fun _=>Cage (dial v)) _ Q, penMake _ _ _ _ fun x=>?_⟩
 have hx(i):=fromPen (hQ i) (x.1 i,x.2 i)
 have he(s:Finset I)(u w: Hill v)(p:∀ i, Matches (S s i) (color (u i)) (color (w i))):Matches s (pallet v u) (pallet v w):=by intro i hi; obtain ⟨⟨i,j⟩,rfl⟩:= (boy v).surjective i; change pallet _ _ (old v i j)= pallet _ _ (old v i j); rw [tint,tint]; exact p i ((ht s i j).mpr hi)
 exact ⟨he _ _ _ (fun i=>(hx i).1), he _ _ _ (fun i=>(hx i).2.1), he _ _ _ (fun i=>(hx i).2.2.1),he _ _ _ (fun i=>(hx i).2.2.2)⟩
lemma city (x:I) :∃ E: Perm (Hill v),∀ f i,pallet v (E f) i=pallet v f (x+i):=by
 let e:= Equiv.addLeft (radius v x); let k(i:Hub v):= ((boy v).symm (x+root v i)).2
 have hx(i:Hub v)(j:T_): x+old v i j=old v (e i) (j+k i):=by
    rw [add_comm j, houseB]; let Z:= (boy v).symm (x+root v i); have hp:old v Z.1 Z.2=x+root v i:=(boy v).apply_symm_apply _
    have h:e i= Z.1:=by rw [←route_v v Z.1 Z.2,hp]; change radius v x+i=QuotientAddGroup.mk' (AddSubgroup.zmultiples v) (x+root v i); rw [map_add,(show (QuotientAddGroup.mk' _) (root v i)= _ from root_p v i)]
    rw [h, hp]; rw [old]; abel
 choose Ξ hv using fun i:Hub v=>turn (k i); let T:= (Equiv.arrowCongr e.symm (Equiv.refl (Cage (dial v)))).trans (Equiv.piCongrRight Ξ); refine ⟨T,fun f i=>?_⟩; obtain ⟨⟨i,j⟩,rfl⟩:=(boy v).surjective i; change pallet v _ (old v i j)= pallet v f (x+old v i j); rw [hx,tint,tint]; exact hv i (f (e i)) j
end Wrap
end YM.CF.BProof.Tetra
