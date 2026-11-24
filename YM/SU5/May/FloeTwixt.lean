import YM.SU5.May.FloePluck
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Arctic
open Function Filter Finset Fock Emu
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators ComplexOrder InnerProductSpace
attribute [local instance] opCStarAlgebra
private abbrev Si (A:Type*) := A ⊕ A
variable {J n:Type*} [LinearOrder n][Fintype n]
local notation "L" => (Si J)
local notation "ι" => @Sum.inl J J
local notation "τ" => @Sum.inr J J
local notation "I"=>Complex.I
-- Wick growth. bounding smooth absolute costs enough. fake implements assuming positive Gram
variable (A:J→Ket n)(B:J→Ket n)(p: J→ℂ)(u:J⊕J→J⊕J→ℂ)(q:∀ i,p i≠0)
def pairOrder (s t:List J): List (J⊕J):= s.map Sum.inl ++ t.map Sum.inr
def veil (p:J→ℂ)(F:List J):ℂ:= (F.map p).prod
local notation "R" => remove
private abbrev liftD (p:J→ℂ)(i:J):ℂ:=-I*(p i)⁻¹
-- ι means primal negative before any τ
private def sword:L→ Ket n:= Sum.elim (fun i=> liftD p i • B i) A
private def knife:L→ Ket n:=Sum.elim (fun i=> star (liftD p i) • A i) B
private def offerX (i:L):ℂ:=liftD p (Sum.elim id id i)
private def payment (i k:L):ℂ:=inner ℂ (knife A B p i) (sword A B p k)
private abbrev Ruling(i:L):= create (sword A B p i)
private abbrev LiftX(i:L):= remove (knife A B p i)
def starve(i:J⊕J): FC n:= Ruling A B p i+ LiftX A B p i
private lemma billOfBasis (L':List L): runes (payment A B p) L'=inner ℂ (vacuum n) (acts (rollC (starve A B p) L') (vacuum n)):=by
 refine Eq.symm (java _ _ (LiftX A B p) (Ruling A B p) (fun _=>rfl) (fun i=> vacuum_take _) (fun i=>vacuum_take _) (fun i j=>car ..) _)
variable (a:∀ i j:J,p i*p j*u (Sum.inl i) (Sum.inl j)=star (u (Sum.inr i) (Sum.inr j)))(h:∀ i j:J,u (Sum.inr i) (Sum.inr j) = -u (Sum.inr j) (Sum.inr i))(b:∀ i j:J,u (Sum.inr i) (Sum.inr j)=inner ℂ (B i) (A j))(w:∀ i j:J,I*p i*u (Sum.inl i) (Sum.inr j)=inner ℂ (A i) (A j))
include a b w q h in
lemma honour (s t:List J): runes u (pairOrder s t)= inner ℂ (vacuum n) (acts (rollC (starve A B p) (pairOrder s t)) (vacuum n)):= by
 rw [←billOfBasis]; apply runners; rw [pairOrder,List.pairwise_append]; refine ⟨List.pairwise_of_forall_mem_list ?_, List.pairwise_of_forall_mem_list ?_, ?_⟩ -- tune
 · rintro i g j w'; obtain ⟨i,_,rfl⟩:= List.mem_map.mp g; obtain ⟨j,_,rfl⟩:=List.mem_map.mp w'; unfold payment; change _= inner ℂ (star _ • A i) (_ • B j); rw [inner_smul_left,inner_smul_right,show (starRingEnd ℂ) (star (liftD p i)) = _ from star_star _,← inner_conj_symm (𝕜:=ℂ),← b j i,h j i,map_neg, show starRingEnd ℂ (u (τ i) (τ j))=_ from (a i j).symm]; unfold liftD; field_simp [q]; linear_combination (norm:=ring_nf) u (ι i) (ι j)*Complex.I_mul_I -- tune
 · rintro i g j w'; obtain ⟨i,_,rfl⟩:= List.mem_map.mp g; obtain ⟨j,_,rfl⟩:=List.mem_map.mp w'; exact b i j
 rintro i g j w'; obtain ⟨i,_,rfl⟩:= List.mem_map.mp g; obtain ⟨j,_,rfl⟩:=List.mem_map.mp w'; unfold payment; change _= inner ℂ (star _ • A i) (A j); rw [inner_smul_left,show (starRingEnd ℂ) (star (liftD p i))=_ from star_star _, ←w i j]; unfold liftD; field_simp [q]; linear_combination (norm:=ring_nf) u (ι i) (τ j)*Complex.I_mul_I -- tune
include q in
lemma behind(i:J) : p i • starve A B p (ι i)= - Complex.I • star (starve A B p (τ i)):=by
 let t:= liftD p i; change p i • (create (t • B i)+remove (star t • A i))=_ • star (create (A i)+ remove (B i)); unfold remove; rw [map_smul,map_smul (f:=create)]; have he:p i*t= -I:=by unfold t liftD; field_simp [q]
 simp [star_add,star_smul,star_star,add_comm,he,smul_smul]
include h b in
lemma frontV (i j:J): antiB (starve A B p (τ i)) (starve A B p (τ j))=0:=by
 let K (i:J):= create (A i); let U (i:J):= remove (B i); have hs (i j:J): antiB (U i) (K j)= u (τ i) (τ j) • 1:=by rw [b]; exact car ..
 change antiB (K i+U i) (K j+U j)=_
 calc
 _ = antiB (K i) (K j) + antiB (U i) (U j)+antiB (U i) (K j)+antiB (U j) (K i):=by unfold antiB; simp only [add_mul,mul_add]; abel
 _ = _:=by rw [hs,hs,h i j,show antiB (K i) (K j)=0 from car_create .., show antiB (U i) (U j)=0 from car_rem ..,zero_add,zero_add]; simp
def markW(A:J⊕J→FC n)(s:List J):=rollC A (s.map Sum.inr)
local notation "K"=> markW (starve A B p)
variable (s t:List J)
include h b in
private lemma shiftS(i:J) : star (starve A B p (τ i)) * star (K s) =((-1:ℂ)^s.length) • (star (K s)*star (starve A B p (τ i))):=by
 let V(i:J):= star (starve A B p (τ i))
 induction s with
 | nil=> simp [markW, rollC]
 | cons j s ih=>
    have he: star (K (j::s))=star (K s) * V j:= by unfold markW rollC; rw [List.map_cons,List.map_cons,List.prod_cons, star_mul]
    have hz: V i*V j = -(V j*V i):=by
       let C (i:J):=starve A B p (τ i); have hw: C j * C i = -(C i*C j):=eq_neg_of_add_eq_zero_left (frontV A B p u h b j i); exact (star_mul (C j) (C i)).symm.trans ((congrArg star hw).trans (by rw [star_neg,star_mul]))
    change V i*_=_ • (_*V i); rw [he, ←mul_assoc (V i), show V i*star (K s)=((-1:ℂ)^s.length) • (star (K s)*V i) from ih,Algebra.smul_mul_assoc,mul_assoc, hz, List.length_cons,pow_succ]; simp [mul_assoc]
-- returns multiply by Reflect.chord grade.K*
include h b q in
lemma rotateStamp : veil p s • (rollC (starve A B p) (s.map Sum.inl))=(if s.length%2=0 then (1:ℂ) else -I) • star (K s):=by
 induction s with
 | nil=> simp [veil,rollC,markW]
 | cons i s ih=>
    let X:= starve A B p; have hx: veil p (i::s) • (rollC X ((i::s).map Sum.inl))=(p i • X (ι i))*(veil p s • rollC X (s.map Sum.inl)):= by unfold veil rollC; simp only [List.map_cons,List.prod_cons,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]; rw [mul_comm (p i)]
    have hb: K (i::s)= X (τ i)*K s:= rfl
    rw [hx,ih,behind A B p q]; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm, shiftS A B p u h b s i,hb,star_mul,List.length_cons]; simp only [smul_smul]
    refine congrArg (fun z:ℂ=> z • _) ?_; by_cases r:s.length%2=0
    · have hv:Even s.length:= Nat.even_iff.mpr r; rw [if_pos r,if_neg (by omega), hv.neg_one_pow]; ring
    rw [if_neg r,if_pos (by omega),(Nat.not_even_iff_odd.mp (by rwa [Nat.even_iff])).neg_one_pow]; norm_num
include q a b w h
lemma quilt : (if s.length%2=0 then (1:ℂ) else Complex.I) * veil p s * runes u (pairOrder s t)=inner ℂ (acts (K s) (vacuum n)) (acts (K t) (vacuum n)):=by
 let X:=starve A B p; have he: rollC X (pairOrder s t)=rollC X (s.map Sum.inl)*K t:=by unfold rollC pairOrder; rw [List.map_append,List.prod_append]; rfl
 set T:= (if s.length%2=0 then (1:ℂ) else Complex.I) with HT; set W:=(if s.length%2=0 then (1:ℂ) else -I) with HW; have hm:T*W=1:=by unfold T W; split <;> simp
 rw [honour A B p u q a h b w, he,act_mul,mul_assoc,← inner_smul_right (𝕜:=ℂ),←act_smul,rotateStamp A B p u q h b,act_smul,inner_smul_right, ←mul_assoc,hm,one_mul,←act_inner,star_star] -- tune `inL` 
end YM.CF.May.Arctic
#print axioms YM.CF.May.Arctic.quilt
