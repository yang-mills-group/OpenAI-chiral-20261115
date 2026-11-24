import YM.CF.Hake.Pane
set_option autoImplicit false
noncomputable section
namespace YM.CF.Hake
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo
variable {ι I J n m:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]{F:Oboe n→ FC m}(p: Restart F)
def highP : Poly n m:= ⟨fun i=>F (true,i),fun i j=> by rw [p]; simp [revertP] ⟩
def lowP : Poly n m:=⟨fun i=>star (F (false,i)), fun i j=>by
  rw [antiB,←star_mul,←star_mul,←star_add]; change star (antiB (F (false,j)) (F (false,i)))=_; rw [p]; simp [revertP]⟩
abbrev play (x:Finset n × Finset n): FC m:= (highP p).tag x.1 * star ((lowP p).tag x.2)
lemma playB (x:Finset n× Finset n) : play orchestra x=piano x:=by rw [play,piano,show highP (orchestra (n:=n))=cane n from rfl,show lowP (orchestra (n:=n))=cane n from by unfold lowP cane; congr 1; apply funext; intro x; exact star_star _]
def glissUP (i:n)(x: Finset n × Finset n):Finset n × Finset n → ℂ := if i∈x.1 then 0 else Pi.single (insert i x.1,x.2) (parity i x.1)
def glissLO (i:n)(x:Finset n × Finset n): Finset n× Finset n→ℂ := ((-1:ℂ)^x.1.card) • (if i∈x.2 then 0 else Pi.single (x.1,insert i x.2) (star (Poly.sail x.2 {i}))) + (if i∈x.1 then Pi.single (x.1.erase i,x.2) (parity i x.1) else 0)
abbrev wont (w:Finset n × Finset n → ℂ): FC m:= ∑ i : Finset n × Finset n,w i • play p i
lemma wont_s (w u:Finset n×Finset n →ℂ):wont p (w+u)=wont p w+wont p u:=by simp [wont,add_smul,sum_add_distrib]
lemma wont_c (w:Finset n× Finset n→ℂ)(x:ℂ): wont p (x • w)=x • wont p w:=by simp [wont,mul_smul,smul_sum,smul_eq_mul]
lemma wont_σ (S:Finset ι)(w:ι→Finset n × Finset n→ℂ): wont p (∑ i∈S,w i)=∑ i∈S,wont p (w i):=by simp only [wont,Finset.sum_apply,sum_smul]; rw [sum_comm]
lemma wont_pr (i:Finset n×Finset n)(x:ℂ): wont p (Pi.single i x)= x • play p i:=by rw [wont,sum_eq_single i, Pi.single_eq_same]; intro k _ v; rw [Pi.single_eq_of_ne v,zero_smul]; simp
lemma wont_0:wont p 0=0:=by simp [wont]
lemma glissU (x:n)(s t:Finset n):wont p (glissUP x (s,t))= F (true,x)*play p (s,t):=by
 unfold glissUP; dsimp only; split_ifs with h
 · rw [wont_0,play,←mul_assoc,show F (true,x)*_= _ from (highP p).tag_mute s x h,zero_mul]
 rw [wont_pr,play,play,(highP p).tag_any _ _ h,Algebra.smul_mul_assoc,smul_smul,parity_sq,one_smul,mul_assoc]; rfl
lemma glissx (x:n)(s:Finset n)(h:x∉s):F (false,x)*(highP p).tag s=(-1:ℂ)^s.card • ((highP p).tag s*F (false,x)) :=by
 induction s using Finset.induction_on_min with
 | empty=> simp [Poly.tag_void]
 | @insert i s v ih=>
    simp only [mem_insert,not_or] at h; rw [Poly.tag_min _ _ _ v, ←mul_assoc]; let B:=highP p
    have he:F (false,x)*B.term i= -(B.term i * F (false,x)):= eq_neg_of_add_eq_zero_left ((p (false,x) (true,i)).trans (if_neg (by simp [revertP,h.1])))
    rw [he, neg_mul,mul_assoc,ih h.2,Algebra.mul_smul_comm,card_insert_of_notMem (fun u=>lt_irrefl _ (v _ u)),pow_succ',mul_assoc]; simp [B]
lemma glissy (x:n)(s: Finset n)(h:x∈s): F (false,x)*(highP p).tag s=(-1:ℂ)^s.card • ((highP p).tag s* F (false,x))+ parity x s • (highP p).tag (s.erase x):=by
 let t:=s.erase x; let α:=F (false,x); let B:=highP p; have he:x∉ t:=notMem_erase _ _; have hu:= insert_erase h
 have hh:α * B.term x=1-B.term x * α:= eq_sub_of_add_eq ((p (false,x) (true,x)).trans (if_pos rfl))
 have hy:parity x s=parity x t:= by nth_rw 1 [←hu]; simp [parity,t,filter_insert]
 change α*B.tag s=_ • (B.tag s * α) + _ • B.tag t
 have hi : B.tag s= parity x t • (B.term x * B.tag t):=by nth_rw 1 [← hu]; exact B.tag_any _ _ he
 rw [hi,Algebra.mul_smul_comm,←mul_assoc,hh,sub_mul,one_mul,mul_assoc, show α * _= _ from glissx p x t he,Algebra.mul_smul_comm,Algebra.smul_mul_assoc, mul_assoc,show s.card=t.card+1 from show _ by nth_rw 1 [←hu]; exact card_insert_of_notMem he,hy]; rw [pow_succ',smul_sub]; simp only [neg_mul,one_mul, neg_smul,smul_comm (parity x t)]; abel
lemma glissZ (x:n)(s t:Finset n):wont p (glissLO x (s,t))=F (false,x)*play p (s,t):=by
 let B:= lowP p; let C:=highP p; let δ:=F (false,x)
 let V: Finset n×Finset n→ℂ:=if x∈t then 0 else Pi.single (s,insert x t) (star (Poly.sail t {x})); have hp: wont p V= C.tag s*(δ*star (B.tag t)):=by
    rw [show δ=star (B.tag {x}) from (by rw [Poly.tag_once]; exact (star_star _).symm),← star_mul, B.tag_mul]; unfold V; by_cases h:x∈t; · rw [if_pos h,wont_0,if_neg (by simpa),star_zero,mul_zero]
    rw [if_neg h,wont_pr, if_pos (by simpa), star_smul, Algebra.mul_smul_comm]; simp [play,C,B] -- tune t∪{x}
 change wont p (_ • V + (if x∈s then _ else _))=_
 rw [wont_s,wont_c,hp]; change (_:ℂ) • _ + _= δ*(C.tag s*star (B.tag t)); rw [←mul_assoc δ]; split_ifs with h
 · rw [wont_pr,show δ*_ = _ from glissy p _ s h,add_mul]; simp only [Algebra.smul_mul_assoc,mul_assoc]; rfl
 rw [wont_0, show δ *_ = _ from glissx p _ s h,Algebra.smul_mul_assoc,mul_assoc,add_zero]
abbrev peel (i: Oboe n)(s:Finset n × Finset n): Finset n× Finset n→ℂ := if i.1 then glissUP i.2 s else glissLO i.2 s
def chase : List (Oboe n)→ Finset n× Finset n→ℂ
 | []=> Pi.single (∅,∅) 1
 | x::t=>∑ i: Finset n×Finset n,chase t i • peel x i
lemma chasing (t:List (Oboe n)): wont p (chase t)=rollC F t:=by
 induction t with
 | nil=> rw [chase,wont_pr,play,Poly.tag_void,Poly.tag_void, star_one,one_mul,one_smul]; rfl
 | cons i t ih=>
    rw [chase,wont_σ,show rollC F _=F i*rollC F t from rfl,←ih,wont,mul_sum]; -- tune `wont` unfolded first
    apply sum_congr rfl; rintro ⟨s,u⟩ _; rw [wont_c,Algebra.mul_smul_comm]; apply congrArg; rcases i with ⟨i,x⟩; cases i; exact glissZ _ x s u; exact glissU _ x s u
end YM.CF.Hake
