import YM.CF.Hake.Pick
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hake
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo
variable {ι n:Type*}[LinearOrder n][Fintype n]
variable [DecidableEq ι](P:ι→ FC n)
def QuietV (P:ι→ FC n) := (∀ i,P i *P i=0) ∧ ∀ i, (∀ j,antiB (P i) (P j)=0) ∨ ∃ l,∀ j, antiB (P i) (P j)= if j=l then 1 else 0
def PlayV (F:FC n)(L:List ι):Prop:= F=0 ∨ ∃ s:List ι,s.Sublist L∧ s.Nodup ∧∃ x:ℂ, ‖x‖=1 ∧ F=x • rollC P s
lemma lump (S T:List ι):rollC P (S++T)=rollC P S*rollC P T:=by unfold rollC; simp
lemma back_h (i:ι)(s t:List ι)(h:s.Sublist t):s.Sublist (i::t):=h.cons i
lemma gone(x:ι)(l r:List ι)(p:P x *P x=0)(h:∀ i∈l,antiB (P x) (P i)=0): rollC P (x::(l++x::r))=0:=by
 induction l with
 | nil=> change P x*(P x*rollC P r)=_; rw [←mul_assoc,p,zero_mul]
 | cons i l ih=>
    change P x*(P i*rollC P (l++x::r))=0
    rw [←mul_assoc,show P x*P i= _ from eq_neg_of_add_eq_zero_left (h _ (List.mem_cons_self ..)),neg_mul,mul_assoc,show P x*rollC P (l++x::r)=0 from ih fun j p=>h j (List.mem_cons_of_mem _ p),mul_zero,neg_zero]
lemma swapU (x:ι)(l r:List ι)(h:∀ i∈l,antiB (P x) (P i)=0):rollC P (x::(l++r))=(-1:ℂ)^l.length • rollC P (l++x::r):=by
 induction l with
 | nil=> simp
 | cons i l ih=>
    change P x*(P i*rollC P (l++r))=(-1:ℂ)^(l.length+1) • (P i*rollC P (l++x::r)); rw [←mul_assoc,show P x*P i= _ from eq_neg_of_add_eq_zero_left (h i (List.mem_cons_self ..)),neg_mul,mul_assoc,show P x*rollC P (l++r)= _ from ih fun j p=> h j (List.mem_cons_of_mem _ p),Algebra.mul_smul_comm,pow_succ']; simp
lemma cry_s (L:List ι)(p:QuietV P)(x:ι)(v:L.Nodup)(e:x∈L) : PlayV P (rollC P (x::L)) L:=by
 obtain ⟨l,r,rfl⟩:=List.append_of_mem e; rcases p.2 x with h|⟨j,h⟩
 · exact Or.inl (gone P _ _ _ (p.1 _) fun i _=> h i)
 by_cases hx:j∈l
 · obtain ⟨a,b,rfl⟩:= List.append_of_mem hx
   rw [List.append_assoc,List.cons_append] at v ⊢; let T:= b++x::r
   have hp:(a++T).Sublist (a++j::T):= (List.Sublist.refl a).append ((List.Sublist.refl T).cons _)
   -- extract if_anti
   have hh:∀ i∈ a,antiB (P x) (P i)=0:= by
       intro i q; rw [h,if_neg]; rintro rfl; have hz:= List.pairwise_append.mp v; exact hz.2.2 _ q _ (List.mem_cons_self ..) rfl
   have ht:j∉ T:= (List.nodup_cons.mp (List.pairwise_append.mp v).2.1).1
   have he: rollC P (j::x::T)=0:=by rw [show rollC P _=P j*rollC P (x::T) from rfl,gone P x b r (p.1 _) (fun i e=> by rw [h]; exact if_neg (fun (u:i=j)=> ht (u ▸ List.mem_append_left _ e))),mul_zero]
   refine Or.inr ⟨a++T,hp,hp.nodup v,(-1:ℂ)^a.length,by simp,?_⟩
   rw [swapU P x a (j::T) hh, lump,lump]; congr 2
   change P x*(P j*rollC P T)=_; rw [←mul_assoc, show P x*P j=1-P j*P x from eq_sub_of_add_eq ((h j).trans (if_pos rfl)),sub_mul,one_mul, mul_assoc, show P j*(P x*rollC P T)=0 from he,sub_zero]
 exact Or.inl (gone P _ _ _ (p.1 _) fun i e=> by rw [h]; exact if_neg (fun (u:i=j)=> hx (u ▸ e)))
lemma no_clash(L:List ι)(p:QuietV P) : PlayV P (rollC P L) L:=by
 induction L with
 | nil=> exact Or.inr ⟨[],List.Sublist.refl [],List.nodup_nil,1,by simp,by rw [one_smul]⟩
 | cons i L ih=>
    rcases ih with v| ⟨s,h,k,u,p',v⟩
    · exact Or.inl (show P i*rollC P L=0 by rw [v,mul_zero])
    have hg : rollC P (i::L)=u • rollC P (i::s):= by rw [show rollC P _=P i*rollC P L from rfl,v,Algebra.mul_smul_comm]; rfl
    rw [hg]; by_cases hx:i∈ s
    · rcases cry_s P s p i k hx with f|⟨y,A,g,x,m,g'⟩; exact Or.inl (by rw [f,smul_zero]); exact Or.inr ⟨y,back_h _ _ _ (A.trans h),g,u*x,by rw [norm_mul,m,p',one_mul],by rw [g',smul_smul]⟩
    exact Or.inr ⟨i::s,h.cons_cons i,List.nodup_cons.mpr ⟨hx,k⟩,u,p',rfl⟩
lemma revive: QuietV (bell (n:=n)):=⟨fun (u,i)=> by cases u; exact take_sq _; exact put_sq _,fun (u,i)=>Or.inr ⟨revertP (u,i),fun (b,j)=> Eq.trans (by rw [antiB_comm]; exact orchestra (b,j) (u,i)) rfl⟩⟩ -- orientation! antiB_comm notation rewrites?
lemma retreat: QuietV (put (n:=n)):= ⟨put_sq,fun i=>Or.inl (put_put i)⟩
end YM.CF.Hake
