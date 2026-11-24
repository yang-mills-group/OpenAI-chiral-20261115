import GaugeFieldConstruction.Flan
/- Wick rule and centered monitors CAR, similarity metric. */
-/
set_option autoImplicit false
set_option maxHeartbeats 90000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Fock.Flux
open Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Topology BigOperators InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I:Type*} [LinearOrder I][Fintype I]{P E A B : Op I}{u: Wave I}
abbrev Worthy (P A B:Op I)(u:Wave I)(T: FC I):ℂ:= quotation u (translateW P A B 1 0 T)
namespace Pacts
abbrev lampsR(P A B:Op I)(j:Creduct I): Ket I:= acts (if j.1 then star B else A) (basisKet j.2)
abbrev gritC (P A B:Op I)(i j:Creduct I):ℂ:=laceSC i.1 j.1 (acts (penny i.1 P) (lampsR P A B i)) (lampsR P A B j)
abbrev comet (P A B:Op I)(u:Wave I)(L:List (Creduct I)) := Worthy P A B u (rollC RootBay L)
def crestP (P A B:Op I)(u:Wave I): FC I →ₗ[ℂ] ℂ where
 toFun := Worthy P A B u
 map_add' x y:=by unfold Worthy; rw [translateW_sum,quot_sum]
 map_smul' x y:=by unfold Worthy; rw [scale_crest,quot_scale]; rfl
variable {i j k m a b:I}(v:Valve P E A B)(p:IsStarProjection P)(q:Sea P u)
include v p q
lemma cΩ : crestP P A B u 1=1:=by change Worthy _ _ _ _ _=_; unfold Worthy; rw [nilW v p,quot_nil _ q.2]
lemma cork : comet P A B u []=1:= cΩ v p q
lemma tarry (i:Creduct I)(L:List (Creduct I)): comet P A B u (i::L)=((picks L).map fun k=> (cval k.neg)*gritC P A B i k.front * comet P A B u k.back).sum:=by
 let Z:= lampsR P A B; let F:= pieceV Prod.fst Z; let Ω:= quotation u; let T:=star (dustAnn (!i.1) P (Z i)); let R:=dustAnn i.1 P (Z i)
 have he(L: List (Creduct I)): comet P A B u L=Ω (rollC F L):=by
    unfold comet Worthy; rw [warp_word v p]; refine congrArg Ω ?_; congr 1; funext i; rw [warp_root v p,oneWarp,onePeak,neg_zero,chips_zero]; change creed i.1 (acts (if i.1 then star (star (1:Op I)* B *1) else 1*A*1) _)=F i; simp only [star_one,mul_one,one_mul]; rfl -- ext i tactic overdoes tune
 simp_rw [he]; let Y:=rollC F L; change Ω (F i*Y)=_ ; let X:= fun j:Bout (Creduct I)=> tuckC (cval j.neg) j.front F j.back (gritC P A B i)
 have ht (S:List (Bout (Creduct I))) : Ω ((S.map X).sum)=(S.map (fun k=> cval k.neg*gritC P A B i k.front*Ω (rollC F k.back))).sum:=by
    induction S with|nil=> simp [Ω,quotation]|cons j l ih=>rw [List.map_cons,List.sum_cons,List.map_cons,List.sum_cons, show Ω _= Ω (X j)+Ω (List.map X l).sum from quot_sum .., ih, show Ω (X j)=_ from quot_scale ..]
 have hv := groom F R (gritC P A B i) (fun j=> centSC i.1 j.1 (acts (penny i.1 P) (Z i)) (Z j)) L
 rw [show F i=T+R from dust_star ..,add_mul,show Ω _= _ from (show Ω ((T*Y)+(R*Y))=Ω (T*Y)+Ω (R*Y) from quot_sum u _ _),show Ω (T*Y)=0 from ?_, zero_add, show R*Y= _ • (Y*R)+ _ from hv]; swap
 · unfold Ω T quotation; rw [act_mul,← act_inner,star_star, dust_kills _ _ p q,inner_zero_left]
 change Ω (((-1:ℂ)^_) • _+ ((picks L).map X).sum)= _; rw [show Ω _= Ω _+Ω ((picks L).map X).sum from quot_sum ..,ht]; change quotation u _ + _=_; rw [quot_scale, show quotation u (Y*R)=0 from ?_,mul_zero,zero_add]; unfold quotation R; rw [act_mul,dust_kills _ _ p q,map_zero,inner_zero_right]
omit v p q in
lemma cDry (c:Bool)(i j:I): gritC P A B (c,i) (c,j)=0:=by simp [gritC,laceSC]
abbrev chimeP (P A B:Op I)(i j:I):ℂ:= (B*P*A) j i
omit v p q in
lemma paysC (i j:I):gritC P A B (false,i) (true,j)=chimeP P A B i j:=by
 change inner ℂ (acts (star B) (basisKet j)) (acts P (acts A (basisKet i)))=_; rw [show B= _ from rfl] -- tune
 unfold chimeP; rw [act_inner B,← act_mul,← act_mul,basis_inner,basis_act]
lemma pinchK (i j:Creduct I):comet P A B u [i,j]= gritC P A B i j:=by rw [tarry v p q]; simp [picks,cval, cork v p q]
lemma flier (h:i ≠ j): gritC P A B (true,i) (false,j) = -chimeP P A B j i:=by
 rw [←paysC,←pinchK v p q,←pinchK v p q]; let Q:= crestP P A B u; change Q (RootBay (true,i)*(RootBay (false,j)*1)) = - Q (RootBay (false,j)*(RootBay (true,i)*1)) -- tune
 rw [← map_neg,mul_one,mul_one]; congr 1; apply eq_neg_of_add_eq_zero_left; have hx: antiB (RootBay (true,i)) (RootBay (false,j))=0:=by rw [show antiB (RootBay (true,i)) (RootBay (false,j))= _ from centSC true false (basisKet i) (basisKet j)]; simp [laceSC,basis_inner,basis_apply,h,Ne.symm h] -- tune
 exact hx
structure Seated (S:Finset I) where
 cv:I
 rv:I
 cvB : cv∈S
 rvB : rv ∉ S
variable {S: Finset I}
abbrev QueenP (P A B:Op I)(i j: Seated S):ℂ:= chimeP P A B i.cv j.rv
abbrev surge (i:Seated S) :FC I:= RootBay (false,i.cv)*RootBay (true,i.rv)
abbrev paula(P A B:Op I)(i:Seated S):= surge i-(QueenP P A B i i) • 1
lemma jetC (i j:Seated S):gritC P A B (true,i.rv) (false,j.cv)= - QueenP P A B j i:=flier v p q (fun e=>i.rvB (e ▸ j.cvB)) -- direction e tune
lemma lockP (i:Seated S): crestP P A B u (surge i)= QueenP P A B i i:=by
 have hx:= pinchK v p q (false,i.cv) (true,i.rv); rw [paysC] at hx; change crestP _ _ _ _ (RootBay (false,i.cv)*(RootBay (true,i.rv)*1))=_ at hx; rwa [mul_one] at hx -- tune
lemma bill (a b c d:Creduct I):comet P A B u [a,b,c,d]=gritC P A B a b*gritC P A B c d-gritC P A B a c*gritC P A B b d+gritC P A B a d*gritC P A B b c:=by
 rw [tarry v p q]; simp [picks,beside,pinchK v p q,cval]; ring
lemma arrowα (i j:Seated S):crestP P A B u (surge i*surge j)=QueenP P A B i i*QueenP P A B j j-QueenP P A B i j*QueenP P A B j i:=by
 have hx:= bill v p q (false,i.cv) (true,i.rv) (false,j.cv) (true,j.rv); simp_rw [paysC,cDry,jetC v p q] at hx; unfold surge; rw [mul_assoc]; change Worthy _ _ _ _ _= _; unfold comet rollC at hx; simp only [List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one] at hx; refine hx.trans ?_; unfold QueenP; ring
-- polynomial identity keeping multiplication order
omit v p q in
lemma island (L:FC I→ₗ[ℂ]ℂ)(p:L 1=1)(X Y Z: FC I)(x y z:ℂ):
    L ((X-x • 1)*(Y-y • 1)*(Z-z • 1))= L (X*Y*Z)- x * L (Y*Z) - y* L (X*Z) - z*L (X*Y)+ x*y*L Z + y*z*L X + z*x*L Y-x*y*z:=by
 simp only [mul_sub,sub_mul, Matrix.smul_mul,Matrix.mul_smul,one_mul,mul_one,map_sub,map_smul,smul_eq_mul,p]; ring
lemma calyx (i j k:Seated S): let Q:= crestP P A B u; let C:= QueenP P A B; let x:=C i i; let y:=C j j; let z:=C k k; Q (surge i*surge j*surge k)+ y*C i k*C k i+x*C j k*C k j+z*C i j*C j i=x*y*z+C i j*C j k*C k i+C i k*C k j*C j i:=by
 have hx:= tarry v p q (false,i.cv) [(true,i.rv),(false,j.cv),(true,j.rv),(false,k.cv),(true,k.rv)]; simp only [picks,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil, List.map_map, List.map_nil,bill v p q] at hx; dsimp only [Function.comp,beside] at hx -- tune long
 simp only [bill v p q,jetC v p q,cDry,paysC] at hx; intro Q C x y z;
 rw [show surge i*surge j*surge k=rollC RootBay [(false,i.cv),(true,i.rv),(false,j.cv),(true,j.rv),(false,k.cv),(true,k.rv)] by simp [rollC,surge,mul_assoc], show Q _= _ from hx]; unfold x y z C QueenP; norm_num only [cval,Bool.not_false,Bool.not_true,Bool.false_eq_true, ↓reduceIte,if_false]; ring -- tune
lemma cancelR (i:Seated S): crestP P A B u (paula P A B i)= 0:=by simp [paula,lockP v p q,cΩ v p q]
lemma doubleR (i j:Seated S): crestP P A B u (paula P A B i*paula P A B j)= -(QueenP P A B i j*QueenP P A B j i):=by
 simp only [paula,mul_sub,sub_mul,Matrix.smul_mul,Matrix.mul_smul,one_mul,mul_one,map_sub,map_smul,smul_eq_mul,cΩ v p q, arrowα v p q,lockP v p q]; ring
lemma trebleR (i j k:Seated S): let C:=QueenP P A B; crestP P A B u (paula P A B i*paula P A B j*paula P A B k)= C i j*C j k*C k i+C i k*C k j*C j i:=by
 intro W; unfold paula; rw [island _ (cΩ v p q), arrowα v p q,arrowα v p q,arrowα v p q,lockP v p q,lockP v p q,lockP v p q]; unfold W; linear_combination calyx v p q i j k
end Pacts
end YM.CF.Fock.Flux
end
