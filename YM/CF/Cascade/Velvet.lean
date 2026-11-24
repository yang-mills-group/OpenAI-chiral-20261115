import YM.CF.Cascade.Linen
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
open Spire Vault Laic Kennel Rush Fir Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable (n)
def postR (X: Cloud n→Op (Single n))(Y:Cloud n→Op (Single n))(x:Cloud n):Op (Single n):= tickA n * (1+X x) * Y x
lemma plusInk: tickA n=(love n) (flatV Slot n):=by unfold tickA; rw [plane_diag]; rw [show cutM plusHalf= Aop from raising.trans Adef.symm]; rfl
lemma plus_P : IsStarProjection (tickA n):=by rw [touchP]; exact cutM_idp _
variable (u:CoreX)
variable {n}
def Crops(j:ℕ)(M:Male)(U:Bkg (More n)→ Op (Single n))(x:Bkg (More n)): Op (Single n):=capT (spar j M x) (U x)
-- fully tied
abbrev grace(j:ℕ)(M:Male)(T:Dress n): Cloud n→Op (Single n):= postR n (Crops j M T ∘ represent) (spar j M ∘ represent)
def ArcJ (j:ℕ)(M:Male)(T:Dress n)(x:Air n): Cab Slot n:=(love n).symm (grace j M T (pour n u x))
lemma colorCup(t:Site (More n)→E): (love n).symm (tradew n t).val*flatV Slot n=flatV Slot n *(love n).symm (tradew n t).val:=by rw [twine]; unfold flatV; simp only [jump_mul]; apply congrArg (jump _); funext i; unfold bins; rw [op_kron_mul,op_kron_mul]; simp
lemma tick_g(t:Site (More n)→E): twist (tradew n t) (tickA n)=tickA n:=by
 let W:=(love n).symm; let V:=tradew n t; apply W.injective; rw [plusInk,twist_formula]; change W _=W _; rw [map_mul,map_mul,map_star, StarAlgEquiv.symm_apply_apply,colorCup,mul_assoc,←map_star,←map_mul,V.property.2,map_one,mul_one] -- tune star direction
lemma base_grace (p:1≤j)(M:Male)(T:Dress n)(v:T 1=0):(love n).symm (grace j M T 0)=subHub (fun i=>fuel Slot j M.val (mel i)):=by
 let P:=funde j M n 1; let Q:=bar j M.val; have he:spar j M (1:Bkg (More n))=P:=by unfold spar; rw [profile_trivial]
 unfold grace postR; simp only [Function.comp_apply,link_one,Crops, capT,v,mul_zero,zero_mul,add_zero,mul_one]; rw [he]; have hh:(love n).symm P=subHub (fun i=> Q (mel i)⊗ₖ (1:Op Slot)):=by
    apply (love n).injective; change love n ((love n).symm _)=love n _; rw [StarAlgEquiv.apply_symm_apply]; unfold P; rw [funde_flat _ p]; rw [show cart n (tub (bar j M.val)) = _ from cart_traded (A:=bar j M.val) (cBar j M.val true p M.property) n, ← atmos]; rfl
 rw [plusInk, map_mul, StarAlgEquiv.symm_apply_apply, hh,← show subHub (fun _=>bins Slot)=flatV Slot n from bin_hub,show subHub (fun _:Site n=>bins Slot) * _= _ from Aroma.lung (Equiv.refl _) _ _]
 change subHub (fun i:Site n=>bins Slot*(Q (mel i) ⊗ₖ (1:Op Slot)))= _; unfold bins; simp_rw [op_kron_mul,mul_one]; rfl
lemma core_t(u:CoreX)(V:Air n)(t:Cover):represent (pour n u (rake t V))=Yg (lagX t) (represent (pour n u V)):=by
 let W:= SubMotion t (pour n u V); have ht:W=pour n u (rake t V):=rfl -- tune cast if proof
 rw [←ht]; simpa only [one_smul] using height (pour n u V) t (1:ℝ)
lemma nearB(e:ℝ)(p:0<e):∀ᶠ x:Cloud n in 𝓝 0, Guard (represent x) e:=by
 have hx : Tendsto (fun x:Cloud n=> represent x) (𝓝 0) (𝓝 (represent (0:Cloud n))):= army_repr.cont
 rw [link_one] at hx; exact hx.eventually (near_g _ p)
lemma roll_z(x:Cover)(u:Bkg (More n)): let V:=prepU (lagX x) (1:UNI SpinIdx) inert n; ∀ y:Op (Single n),(love n).symm (twist V y)= mil x ((love n).symm y):=by
 intro T y; rw [show twist T y= _ from (lagQ x y).symm]; ext ⟨v,i,l⟩ ⟨w,j,k⟩; change ZoneH (lagX x) y ((v,i),l) ((w,j),k)=(twist (clime _) _) _ _; rw [limo,Aroma.creep]; rfl
lemma commuteW (x: Cover): twist (prepU (lagX x) (1:UNI SpinIdx) inert n) (tickA n)=tickA n:=by
 apply (love n).symm.injective; change (love n).symm _=(love n).symm _; rw [roll_z x (1:Bkg _),plusInk, StarAlgEquiv.symm_apply_apply]; exact curb _
variable {m B L:Side}{ho:Odd L.val}{e:ℝ}{Y:Pricing j L ho (Vault.Thread j)}{P:Grasp Y B e}
lemma Grace (l:0<e)(p:1≤j)(w:Stamped j L ho Y)(M: Male)(h:P.roundZ ≤ n.val)(T:Dress n)(v:Ample T)(Q: ContDiffAt ℝ ω (spar j M ∘ represent (n:=More n)) 0):Foot (ting u) j M.val (ArcJ u j M T):=by
 let A:=spar j M (N:=n); let K(x):=represent (pour n u x); let J:=ArcJ u j M T; let W:= love n; let S:= (P.broadness n h M)
 have he: K (0:Air n)=1:=by unfold K; rw [map_zero,link_one]
 let f (x:Bkg (More n)):=tickA n*(1+Crops j M T x)* A x; have hp : J=W.symm ∘ f ∘ K:=rfl
 have hk:∀ᶠ x:Air n in 𝓝 0,Guard (K x) e:= (show Tendsto (pour n u) (𝓝 0) (𝓝 0) from by simpa only [map_zero] using (pour n u).continuous.tendsto 0).eventually (nearB e l)
 have hx: ContDiffAt ℝ ω (grace j M T) 0:= (((contDiffAt_const (c:=tickA n)).mul (contDiffAt_const.add (((contDiffAt_const.sub Q).mul v.self.2).mul Q))).mul Q)
 refine ⟨M.property,tingP _,?_,?_,?_,?_,?_⟩
 · let L:= W.symm.toAlgEquiv.toLinearEquiv.toLinearMap|>.toContinuousLinearMap; exact ((L.restrictScalars ℝ).contDiff.contDiffAt.comp _ ((show ContDiffAt _ _ _ ((pour n u) 0) from (by rw [map_zero]; exact hx)).comp (g:=grace j M T) _ (pour n u).contDiff.contDiffAt)) -- tune
 · intro t; filter_upwards [hk] with i hi
   let a:=K i; have hh:K (rake t i)=Yg (lagX t) a:=core_t ..; let u:= prepU (lagX t) (1:UNI SpinIdx) inert n; have hu:twist u (A a)= A (K (rake t i)):=by rw [hh]; exact funde_f (lagX t) inert 1 calmSX a j p _ _ (w.fields_one n (P.needed.trans h)) (hi.shrink P.gem)
   change W.symm (f (K (rake t i)))=mil t (W.symm (f a)); rw [←roll_z t a]; apply congrArg (fun Y=> W.symm Y); have hx: T (K (rake t i))= twist u (T a):=by rw [hh,v.across,lagQ]; done
   change tickA n*(1+(1-A (K (rake t i)))*T (K (rake t i))* A (K (rake t i)))*A (K (rake t i))= twist u (tickA n*(1+(1-A a)*T a * A a)* A a); simp only [map_mul,map_add,map_one,map_sub,hu,hx]; rw [commuteW t] -- tune let u
 · filter_upwards with x; let X:=f (K x); have ht:tickA n * X=X:=by unfold X f; rw [←mul_assoc,←mul_assoc,(plus_P n).1]
   change flatV Slot n* W.symm X=W.symm X; rw [show flatV Slot n=W.symm (tickA n) from (by rw [plusInk,show W.symm _= _ from ?_]; exact StarAlgEquiv.symm_apply_apply ..),←map_mul,ht] -- binder
 · unfold ArcJ; rw [map_zero,base_grace p _ _ v.self.1]
 intro x ho; filter_upwards with t; let i : Site (More n)→ E:=fun i=> rollH u (t * x i); let L:=K (t • lop x); have hv:L=Lattice.gauge i (K 0):=by rw [he]; exact gauge_line x ho u t
 have ht:twist (tradew n i) (f (K 0))= f L:=by
   unfold f A Crops capT; rw [hv, v.ripe, S.covary (K 0) i hk.self_of_nhds]; simp only [map_mul,map_sub,map_add,map_one, tick_g]
 rw [← party u x t]; change W.symm (f L)= _ * W.symm (f (K 0))*star _; rw [←ht,twist_formula,map_mul,map_mul,map_star]
end YM.CF.Cascade
