import YM.CF.Gas.Flip
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gas
open Function Filter Metric Finset NormedSpace Fock Petal Pastry Spire Scroll Scree Ione Branch Lattice Lat Tenant
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Type*}[Fintype n][LinearOrder n]
variable (a:Bool)(V:UNI n)(C Y S:Op n)
private lemma face_a (p q:Bool):windX a (faceD p q S)=faceD p q (windX a S):=by
 simp only [faceD,twinD, win_sum,win_m,win_c, wire]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; cases a; rfl; simp only [windX,ite_true, put_clear]; rfl -- tune
lemma ward : paintR a false (1:UNI n) (hang C Y S)=hang (windX a C) (windX a Y) (windX a S):=by
 apply Subtype.ext; change sauce _ _ _ (quilt C Y S)= _; let U:=spice (n:=n) 1 false
 have he : U=(1:UNI (LeanV n)):=Subtype.ext (by ext i j; rcases i with ⟨u,i⟩;rcases j with ⟨v,j⟩; cases u<;> cases v<;> simp [U,spice,closeV,jump_apply,thread,ccU,Matrix.one_apply]) -- tune
 unfold sauce; rw [Bool.xor_false, singT,show spice (1:UNI n) false=1 from he,show quantU (1:UNI (LeanV n))=1 from Subtype.ext quant_one,Fock.one_des]; have ht: cSignX a (2:ℂ)⁻¹=(2:ℂ)⁻¹:=by cases a<;> simp [cSignX]
 change windX a (quilt _ _ _)=quilt _ _ _; rw [quilt,win_c,win_a,win_l,win_a,face_a,face_a,face_a,face_a,ht,show windX a Yᵀ=(windX a Y)ᵀ from (by cases a<;>rfl)]; rfl
private lemma kindle(b:Bool)(p:n):sauce false true (1:UNI n) (wire b p)=(if b then (-Complex.I) else Complex.I) • (wire (!b) p):=by
 rw [leafU]; rw [sum_eq_single p]; · simp only [Bool.xor_true]; congr 1; cases b <;>simp [spice,invFilm, jump_apply,opBool,thread,ccU,phaseU] -- tune
 · intro i _ l; cases b <;> simp [spice,jump_apply,thread,invFilm,ccU,opBool,l,phaseU]
 simp
local notation "I'"=>Complex.I
private lemma take_m(b c:Bool): sauce false true (1:UNI n) (faceD b c Y)= ((if b then -I' else I')*(if c then -I' else I')) • faceD (!b) (!c) (cc Y):=by
 unfold faceD twinD; let V:= sauce false true (1:UNI n); have he(u v:FC (LeanV n)):V (u*v)=V u*V v:=singm ..
 simp_rw [sauce,singT,win_sum,map_sum, win_c, twist_scalar, smul_sum]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_
 rw [show twist _ _=V (wire b i*wire c j) from rfl, he,show V (wire b i)= _ from kindle b i,show V (wire c j)=_ from kindle c j]; simp only [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]; have hh:cSignX (false.xor true) (Y i j)= cc Y i j:=rfl; rw [hh]; congr 1; ring
lemma Face_neg(a b:Bool): faceD a b (-S)= -faceD a b S:=by simp [faceD,twinD] -- tune
lemma flip_Y: paintR false true (1:UNI n) (hang S C Y)=hang (-(cc Y)) (-(star C)) (-(cc S)):=by
 apply Subtype.ext; change sauce false true 1 (quilt _ _ _)= quilt _ _ _; let V:=sauce false true (1:UNI n); unfold quilt
 have hp : ∀ A: FC (LeanV n),V ((2:ℂ)⁻¹ • A)=(2:ℂ)⁻¹ • V A:=by unfold V sauce; simp only [singT,win_c,twist_scalar]; intro A; congr 1; simp [cSignX]
 change V _= _; rw [hp]; apply congrArg
 have hh(G P Q Z:FC (LeanV n)):V (G+P-Q+Z)=V G+V P-V Q+V Z:=by simp only [V,sauce,singT,win_a,win_l,map_add,map_sub];
 rw [hh]; unfold V; simp_rw [take_m]; have hx : cc Cᵀ=star C:=rfl; rw [Matrix.transpose_neg,Face_neg,Face_neg,Face_neg,Face_neg,hx,show (star C)ᵀ=cc C from rfl]
 simp only [Bool.not_true,Bool.not_false,Bool.false_eq_true,↓reduceIte,mul_neg,neg_mul,Complex.I_mul_I,neg_neg, neg_smul,one_smul]; abel
variable {P:Op n}{C}(h:IsStarProjection P)(e:IsUnit (stage P C))(s:C ∈ unitary _)(t:Cᵀ= -C)
include e h
lemma wind_v' : paintR a false (1:UNI n) (brass P C S)=brass (windX a P) (windX a C) (windX a S) :=by
 have hE(z:Bool)(H:Op n): windX z (cc H)=cc (windX z H) :=by cases z<;>rfl
 have hh(A:Op n):windX a Aᵀ= (windX a A)ᵀ:=by cases a<;>rfl
 unfold brass; rw [ward]; simp only [Tour.Kcc,Tour.Kcg,Tour.Kgg,driftB,weldB,win_l,win_i,win_m,win_n,hh,hE,win_l,win_i,windN e] -- tune
lemma full_X : paintR a false V (brass P C S)=brass (sings a V P) (congrC V (windX a C)) (sings a V S):=by
 let G:=brass P C S; have he: IsUnit (stage (windX a P) (windX a C)):= (windy_stage e a).symm ▸ live_w e a
 change paintR a false V G=_; have hh: paintR false false V (paintR a false (1:UNI n) G)=paintR a false V G:=by rw [hiB]; simp -- tune
 rw [← hh]; unfold G; rw [wind_v' a S h e,brass_X he]; rfl
include s t
lemma cup_x : paintR false true 1 (brass P C S)=brass (1-P) C S:=by unfold brass; obtain ⟨v,w,y⟩:= mirrors_K h e S s t; rw [v,w,y,flip_Y]
lemma poem(r:Bool) : paintR a r V (brass P C S)=brass (swapX r (sings a V P)) (congrC V (windX a C)) (sings a V S):=by
 cases r; exact full_X a V S h e
 let G:=brass P C S; let E:=reserve P C
 have he:IsUnit (stage (1-P) C):=by rw [stage,show 1-(1-P)=P by abel,add_comm]; exact e
 -- compose mirror BEFORE a, receives charge; whiten c 1 simp
 have hu: paintR a false V (paintR false true (1:UNI n) G)=paintR a true V G:=by rw [hiB]; cases a <;> simp [show ccU (1:UNI n)=1 from Subtype.ext (cc_one)] -- tune
 change paintR a true V G=_; rw [←hu,show paintR _ _ _ G= _ from cup_x S h e s t,full_X a V S h.one_sub he]; have hf:sings a V (1-P)=swapX true (sings a V P):=by simp [singT,win_i,swapX]
 rw [hf]
omit e h s t
variable [Nonempty n]
lemma hymn_e (r:Bool)(H₁ H₂:Op n)(s:Safe H₁)(t:Safe H₂)(v:sings a V H₁= hush r H₂)(τ:ℝ): sings a V (decay H₁ τ)=decay H₂ τ:=by
 have hp:= fires_h a r V H₁ H₂ s t v; have ht(A:Op n): polarity A = (2:ℝ) • projector A-1:=by unfold projector; rw [smul_smul]; norm_num -- tune
 have he: sings a V (monad H₁) = monad H₂:=by
    simp only [monad, singm,v,ht]; rw [show sings a V ((2:ℝ) • projector H₁-1)=(2:ℝ) • swapX r (projector H₂)-1 from (by rw [singT,win_l,win_r,win_i,map_sub,map_smul,map_one]; rw [singT] at hp; rw [hp])]; cases r; rfl; rw [swapX,hush_true,if_pos rfl]; rw [smul_sub,show (2:ℝ) • (1:Op n)=(1:Op n)+1 by rw [two_smul]]; rw [show (1:Op n)+1-(2:ℝ) • projector H₂-1= -( (2:ℝ) • projector H₂-1) by abel, neg_mul_neg] -- tune 2 • coercion
 letI : NormedAlgebra ℚ (Op n):= NormedAlgebra.restrictScalars ℚ ℝ (Op n)
 let F:Op n →+* Op n:={ toFun:=sings a V,map_zero':=by simp [win_z],map_add':=by simp,map_mul':=singm a V,map_one':=by simp [win_i] }
 unfold decay grow; change F _=_; have hp: Continuous F:= (breeze V).comp (typ_l _); rw [map_exp F hp,show F (-τ • monad H₁)= -τ • monad H₂ from (by rw [←he]; exact Eq.trans (congrArg (twist V) (win_r ..)) (map_smul ..))]
end YM.CF.Gas
