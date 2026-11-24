import YM.SU5.Lamour.Brim
import YM.SU5.Lamour.Loom
/-!
# Center identification. On flat overlap d by Clad W(1), on tilted Sea by Slant. For EVERY list from T-polarized Ket. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 210000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lamour
open Fock Finset NormedSpace Flare Pannier.Chancel Velvet Pannier.Damask Reed
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I n:Type*}[LinearOrder n][Fintype n][Fintype I][LinearOrder I]{P T Q R L:Op n}{b a:Bool}{i j:I}{x y:Ket n}{X Y:Wave n}{K:Op I}{v z:ℝ}
def coal (b:Bool) (T:Op n)(x:Ket n):= creed b (cardH b T x)
def leaf (b:Bool) (T:Op n)(x:Ket n):= creed b (cardH (!b) T x)
lemma spread_l (b:Bool) (T:Op n)(x:Ket n): leaf b T x+coal b T x=creed b x:=by unfold leaf coal cardH; rw [←creed_a,including,act_sub,act_one,sub_add_cancel]
lemma coal_letter (b:Bool) (T:Op n)(x:Ket n): Letter (coal b T x):=⟨b,_,rfl⟩
lemma falls (p:IsStarProjection T)(h:Sea T X)(b:Bool)(x:Ket n): acts (coal b T x) X=0:=server p h (raft_trim b p x)
lemma rises (p:IsStarProjection T)(h:Sea T X)(b:Bool)(x:Ket n): acts (star (leaf b T x)) X=0:=by
 rw [show star (leaf b T x)=coal (!b) T x from (by cases b; rfl; exact star_star (create _)),falls p h]
def fern (b v:Bool)(K:Op n)(x y:Ket n):ℂ:= if b=v then 0 else if b then - inner ℂ x (acts K y) else inner ℂ y (acts K x)
lemma fern_comm : fern b a L x y= -fern a b L y x:=by cases b <;> cases a <;> simp [fern]
lemma same_cr (b:Bool)(x y:Ket n): antiB (creed b x) (creed b y)=0:=by cases b; exact car_create ..; exact car_rem ..
lemma cold (p:IsStarProjection T)(b a:Bool)(x y:Ket n): antiB (coal b T x) (coal a T y)=0:=by
 have ht: Letter (coal b T x):=coal_letter ..; obtain ⟨u,w⟩:=anticar ht (coal_letter a T y)
 obtain ⟨v,h⟩ : ∃ v,Sea T v:=by obtain ⟨U,s,r⟩:=spot_projection T p; refine ⟨wedge U.val s,?_,wedge_norm ..⟩; rw [r,act_twistLine,inner_self_eq_norm_sq_to_K,wedge_norm]; simp
 have hv:= congrArg (fun l: FC n=>acts l v) w; simp only [act_add,act_mul,falls p h,map_zero,add_zero,act_smul,act_one] at hv
 unfold antiB; rw [w,(smul_eq_zero.mp hv.symm).resolve_right (norm_pos_iff.mp (h.2.trans_gt one_pos)),zero_smul]
lemma tilt_low (p:IsStarProjection T)(q:trim (1-T) x):acts T x=0:=by unfold trim at q; rw [act_sub,act_one,sub_eq_self] at q; exact q
lemma pin_dot (p:IsStarProjection T)(q:trim T x)(y:Ket n): inner ℂ x (acts T y)= inner ℂ x y:= by rw [←act_inner,p.isSelfAdjoint,q]
lemma tilt_pair (p:IsStarProjection T)(q:trim (1-T) x)(h:trim T y): inner ℂ x y=0:=by nth_rw 1 [←h]; rw [←act_inner,p.isSelfAdjoint,tilt_low p q,inner_zero_left]
private lemma dot_scale (p:IsStarProjection P)(x y:Ket n)(z:ℝ): inner ℂ (acts P (z⁻¹ • x)) (acts P (z⁻¹ • y))= ((z^2)⁻¹:ℝ) • inner ℂ x (acts P y):=by
 simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), map_smul,inner_smul_left,inner_smul_right]; nth_rw 1 [←p.isSelfAdjoint,act_inner]; rw [←act_mul,p.isIdempotentElem]; simp [sq,mul_assoc,smul_eq_mul]
theorem froth (t:IsStarProjection T)(p:IsStarProjection P)(u:trim (hand b T) x)(v:trim (hand a T) y)(z:ℝ): antiB (coal b P (z⁻¹ • x)) (leaf a P (z⁻¹ • y))= fern b a (slant T P z) x y • 1:=by
 obtain ⟨V,h⟩ : ∃ V:Ket n→ₗ[ℂ] Ket n,V= (acts T).toLinearMap:=⟨_,rfl⟩ -- tune
 have he (x y:Ket n)(g:trim (1-T) x)(k:trim T y): inner ℂ x (acts P y)=inner ℂ x (acts ((1-T)*P*T) y):=by rw [act_mul,k,act_mul,pin_dot t.one_sub g]
 have hv (x y: Ket n): inner ℂ x (acts (slant T P z) y)= ((z^2)⁻¹:ℝ) • inner ℂ x (acts ((1-T)*P*T) y):=by unfold slant; simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),act_smul, inner_smul_right]; rfl
 cases b <;> cases a
 · rw [coal,leaf,same_cr]; simp [fern]
 · rw [antiB_comm]; change antiB (remove _) (create _) =inner ℂ y (acts (slant T P z) x) • 1; rw [antiB,car]; congr 1; exact (dot_scale p y x z).trans (by rw [hv,←he y x v u])
 · change antiB (remove _) (create _) =(if (true:Bool)=false then 0 else (- inner ℂ x (acts (slant T P z) y))) • 1; -- change wrong if reduction defeq?
   rw [antiB,car,if_neg (by decide)]; congr 1; change inner ℂ (acts (1-P) _) (acts (1-P) _)=_; rw [show inner ℂ _ _= _ from dot_scale p.one_sub x y z, act_sub,act_one,inner_sub_right, tilt_pair t u v, hv,←he x y u v,zero_sub,smul_neg]
 rw [coal,leaf,same_cr]; simp [fern]
theorem read_lane (x: T*L=0)(e:IsStarProjection T)(p:trim T y):cardH false T (acts (1-L) y)=y:=by unfold cardH; change acts T _=_; rw [act_sub,act_one,map_sub,←act_mul,x,act_zero,p,sub_zero]
theorem read_lower (l:L*T=L)(e:IsStarProjection T)(p:trim (1-T) y):cardH true T (acts (1+star L) y)=y:=by
 let P:=1-T; have hp: P*star L=0:=by unfold P; rw [←e.one_sub.isSelfAdjoint,←star_mul, mul_sub,mul_one,l,sub_self,star_zero]
 unfold cardH; change acts P _=_; rw [act_add,act_one,map_add,←act_mul,hp,act_zero,p,add_zero]
-- quasi overlap pair
abbrev present (b:Bool)(K:Op n)(x:Ket n):= acts (if b then 1+star K else 1-K) x
theorem frost_pair(g: Clad P T 1 1 Q)(w:L=laneP T 1 Q)(u:trim (hand b T) x)(v:trim (hand a T) y): antiB (coal b T (present b L x)) (leaf a T (present a L y))=fern b a L x y • 1:=by
 have hv:T*L=0:= w ▸ g.bare; have he:L*T=L:= w ▸ g.chest
 cases b <;> cases a
 · rw [coal,leaf,same_cr]; simp [fern]
 · rw [antiB_comm]; change antiB (remove (cardH false T (acts (1+star L) y))) (create (cardH false T (acts (1-L) x)))=inner ℂ y (acts L x) • 1; rw [read_lane hv g.helm u, antiB,car]; congr 1; unfold cardH; change inner ℂ (acts T _) _=_; nth_rw 1 [←g.helm.isSelfAdjoint]; rw [act_inner, show acts T x=x from u,act_add,act_one,inner_add_left, tilt_pair g.helm v u,act_inner,zero_add]
 · change antiB (remove (cardH true T (acts (1+star L) x))) (create (cardH true T (acts (1-L) y)))=(-inner ℂ x (acts L y)) • 1; rw [read_lower he g.helm u,antiB,car]; congr 1; unfold cardH; change inner ℂ _ (acts (1-T) _)=_; rw [pin_dot g.helm.one_sub u, act_sub,act_one,inner_sub_right,tilt_pair g.helm u v,zero_sub]
 rw [coal,leaf,same_cr]; simp [fern]
variable (b:I→Bool) (f:I→ Ket n)
/-- d matrix, full (already skew, also can screen by χ). -/
def Hail(L:Op n):Op I:= Matrix.of fun i j=> fern (b i) (b j) L (f i) (f j)
lemma hail_turn(L:Op n): (Hail b f L)ᵀ= -(Hail b f L):=by ext i j; exact fern_comm
variable (T:Op n)(z:ℝ)
def Airo(i:I):=coal (b i) T (z⁻¹ • f i)
def Ciro(i:I):=leaf (b i) T (z⁻¹ • f i)
variable {T z}
theorem facing (e:IsStarProjection T)(g:IsStarProjection Q)(u:∀ i,trim (hand (b i) T) (f i))(z:ℝ): Cross (Hail b f (slant T Q z)) (Ciro b f Q z) (Airo b f Q z) univ univ:= fun i _ j _=>⟨froth e g (u i) (u j) _, cold g _ _ _ _⟩ -- remove set_to
variable [Nonempty n]
def boomR {T:Op n}(x:Wave n)(h:IsStarProjection T)(p:0<z): FC n→ₗ[ℂ] ℂ:=(innerSL ℂ x).toLinearMap.comp ((viewer x).comp (moldP h p).toLinearMap)
def alleyR (x y:Wave n):FC n→ₗ[ℂ] ℂ:= (inner ℂ x y)⁻¹ • ((innerSL ℂ x).toLinearMap.comp (viewer y))
theorem cost_creed (b:Bool)(x: Ket n)(p:IsStarProjection T)(c:0<z)(h:trim (hand b T) x): modifyB T z (creed b x) = creed b (z⁻¹ • x):=by -- credo ⇒ creed
 rw [modifies_creed p c]; unfold readW; congr 1; cases b with
 | false=> change acts (castV T z) x=_; unfold castV gate; simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),act_smul,act_add,act_smul, act_sub, act_one, show acts T x=x from h,sub_self,smul_zero,add_zero]
 | true=>
    let V:= acts T x; change acts (castV T z⁻¹) x=_; unfold castV gate; simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),act_smul,act_add,act_smul, tilt_low p h, zero_add,show acts (1-T) x=x from h]; rw [smul_smul,inv_inv]; congr 1; push_cast; field_simp -- tune
-- general prime and references
variable (S:Finset I)
def rawT (S:Finset I):FC n:= fo (fun i=> creed (b i) (f i)) (S.sort (·≤·))
lemma rawPrime(p:0<z)(e:IsStarProjection T)(u:∀ i,trim (hand (b i) T) (f i))(D:Op n): modifyB T z (rawT b f S)=prime (Ciro b f D z) (Airo b f D z) S:=by
 change moldP e p _=_; unfold rawT fo prime; rw [map_list_prod, List.map_map, show Ciro b f D z + Airo b f D z=(moldP e p) ∘ fun i=> creed (b i) (f i) from funext fun i=>(spread_l ..).trans ((cost_creed (b i) (f i) e p (u i)).symm)] -- tune
lemma oatHC (p:0<z)(e:IsStarProjection T)(g:IsStarProjection Q)(q:Sea Q X)(u:∀ i, trim (hand (b i) T) (f i)): boomR X e p (rawT b f S)=pf (Hail b f (slant T Q z)) S:=by
 change inner ℂ X (acts (modifyB T z _) X)=_; rw [rawPrime _ _ S p e u Q,←full_rip _ _ (hail_turn b f (slant T Q z)) (fun i _ j _ _=> facing b f e g u z i (by simp) j (mem_univ _)),main_w (C:=Ciro b f Q z) (A:=Airo b f Q z) q.2 (fun i _=> falls g q _ _) (fun i _=>rises g q _ _)]
lemma armed_pay(g: Clad P T 1 1 Q)(w:L=laneP T 1 Q)(s:Sea T X)(t:Sea P Y)(u:∀ i,trim (hand (b i) T) (f i)): alleyR X Y (rawT b f S)=pf (Hail b f L) S:=by
 have h:=shines g Y X t s; rw [skyGlow,quant_one,act_one] at h; let F(i):= (b i,f i); let D:= S.sort (·≤·); let W:= D.map F; have he:= read0 g Y X t s W; rw [quant_one,mul_one,skyGlow,quant_one,act_one,←w] at he
 let A(i):=coal (b i) T (present (b i) L (f i)); let C (i):= leaf (b i) T (present (b i) L (f i)); change (inner ℂ X Y)⁻¹* inner ℂ X (acts (rawT _ _ _) Y)= _; rw [show rawT b f S=rollC ton W by unfold W; rw [rollC,List.map_map]; rfl,he,inv_mul_cancel_left₀ h,show rollC (iceT L) W=prime C A S by unfold W; rw [rollC,List.map_map,prime, show C+A=(iceT L)∘F from funext fun i=> spread_l ..], ←full_rip C A (hail_turn b f L) (fun i _ j _ _=>⟨frost_pair g w (u i) (u j), cold g.helm _ _ _ _⟩), main_w (C:=C) (A:=A) s.2 (fun i _=> falls g.helm s _ _) (fun i _=> rises g.helm s _ _)] -- tune
lemma tome_rife(T S: Finset n) : tome T S=rawT (shadeK T) basisKet S:=primeC T S
end YM.CF.Lamour
#print axioms YM.CF.Lamour.oatHC
#print axioms YM.CF.Lamour.armed_pay
