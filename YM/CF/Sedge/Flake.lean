import YM.CF.Sedge.Revel
/-! Filled-high literal injection. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset NormedSpace Filter Function
attribute [local instance] opCStarAlgebra
variable {n m: Type*} [LinearOrder n][LinearOrder m][Fintype n][Fintype m]
variable (f:m↪n)(s:Finset n)(h:Deck f s)
def knot (t:Finset m): Wave n:= acts (((t.sort (·≤·)).map (fun i=> put (f i))).prod) (basisKet s)
def fog (t:Finset m):=s∪ t.map f
lemma knot_empty:knot f s ∅=basisKet s:=by simp [knot]
lemma knots (t:Finset m) (i:m) (h:∀ j∈t,i<j): knot f s (insert i t)=acts (put (f i)) (knot f s t):= by
  unfold knot; rw [sort_insert _ (fun j g=> (h j g).le) (fun g=>lt_irrefl _ (h _ g)),List.map_cons,List.prod_cons,act_mul]
lemma kinds (t:Finset m) (i:m)(h:i∉t): knot f s (insert i t)=parity i t • acts (put (f i)) (knot f s t):=by
  induction t using induction_on_min with
  | empty=> rw [knots _ _ _ _ (by simp)]; simp [parity]
  | insert j t e ih=>
    have he : j∉t:=fun g=>lt_irrefl _ (e _ g)
    simp only [mem_insert,not_or] at h
    rcases lt_or_gt_of_ne h.1 with ht|ht
    · have hx:∀ k∈insert j t,i<k:=fun k hk=>(mem_insert.mp hk).elim (fun l=>l.symm ▸ ht) (fun p=>ht.trans (e k p))
      rw [knots _ _ _ _ hx]; unfold parity; rw [Finset.filter_eq_empty_iff.mpr (fun _ l=>not_lt.mpr (hx _ l).le)]; simp
    have hx:∀ k∈insert i t,j<k:=fun k hk=>(mem_insert.mp hk).elim (fun l=>l.symm ▸ ht) (fun p=>e k p)
    rw [insert_comm i,knots _ _ _ _ hx,ih h.2, knots _ _ _ _ e,map_smul, parity_lo t i j ht he,←act_mul,←act_mul]
    nth_rw 1 [show put (f j)*put (f i)=_ from eq_neg_of_add_eq_zero_left (put_put ..)]
    simp [act_neg]
def gritL: Wave m →ₗ[ℂ] Wave n where
  toFun x:= ∑ i,x.ofLp i • knot f s i
  map_add' := fun x y=>by simp [add_smul,sum_add_distrib]
  map_smul' := fun c x=>by simp [smul_sum,mul_smul]
def hoist :Wave m→L[ℂ] Wave n:=(gritL f s).toContinuousLinearMap
lemma hoops (t:Finset m):hoist f s (basisKet t)=knot f s t:=by change ∑ i,_=_; simp [ite_smul]
lemma hoist_put (i:m)(x:Wave m): hoist f s (acts (put i) x)=acts (put (f i)) (hoist f s x):=by
  nth_rw 1 2 [←basis_expand x]; rw [map_sum,map_sum,map_sum,map_sum]; apply sum_congr rfl; intro j _
  rw [map_smul,map_smul,map_smul,map_smul]; congr 1; rw [put_act, hoops]; by_cases g:i∈j
  · rw [if_pos g,map_zero]; nth_rw 1 [←insert_erase g]; rw [kinds _ _ _ _ (by simp),map_smul,←act_mul,show put (f i)*_=0 by nth_rw 1 2 [←create_put]; rw [create_sq],act_zero,smul_zero] -- tune
  rw [if_neg g,map_smul, hoops,kinds _ _ j i g, smul_smul,parity_sq,one_smul]
include h
lemma residueD(i:m):f i∉s:= Finset.disjoint_left.mp h.splitL (coil_hit f i)
lemma shade(t:Finset m)(i:m): f i∈fog f s t↔ i∈t:=by simp [fog,residueD _ _ h]
lemma hoist_t (i:m)(x:Wave m):hoist f s (acts (takeF i) x)=acts (takeF (f i)) (hoist f s x):=by
  have hx (t:Finset m):hoist f s (acts (takeF i) (basisKet t))=acts (takeF (f i)) (hoist f s (basisKet t)):=by
    induction t using Finset.induction_on with
    | empty=> rw [hoops,take_act, knot_empty]; rw [take_act,if_neg (residueD _ _ h _)]; simp
    | @insert j t g ih=>
      rw [create_basis_is j t g,map_smul,map_smul,map_smul, map_smul,hoist_put,←act_mul,←act_mul (takeF (f i))]
      rw [show takeF i*put j= _ from eq_sub_of_add_eq (mixed i j),show takeF (f i)*put (f j)=_ from eq_sub_of_add_eq (mixed ..),act_sub,act_sub,map_sub,act_mul,hoist_put,ih,act_mul]; by_cases v:i=j<;> simp [v]
  nth_rw 1 2 [←basis_expand x]; simp_rw [map_sum,map_smul,hx]
lemma hoist_c(v:Ket m)(x:Wave m):hoist f s (acts (create v) x)=acts (create (coat f v)) (hoist f s x):=by
  nth_rw 1 2 [←basis_expand v]; simp_rw [map_sum,map_smul,basis_shell,create_put]; simp_rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,map_sum,map_smul]
  exact sum_congr rfl fun i _=>congrArg (fun x:Wave n=>v.ofLp i • x) (hoist_put f s i x)
lemma hoist_r(v:Ket m)(x:Wave m):hoist f s (acts (remove v) x)=acts (remove (coat f v)) (hoist f s x):=by
  nth_rw 1 2 [←basis_expand v]; simp_rw [map_sum,map_smul]; unfold remove
  simp_rw [map_sum,map_smul,basis_shell,create_put,star_sum,star_smul]; simp_rw [show ∀ i:n,star (put i)=takeF i from fun i=>rfl,show ∀ i:m,star (put i)=takeF i from fun i=>rfl,act_sum,act_smul,map_sum,map_smul,hoist_t _ _ h]
lemma knotW (t:Finset m): ∃ c:ℂ, star c*c=1 ∧ knot f s t=c • basisKet (fog f s t):=by
  induction t using Finset.induction_on with
  | empty=> exact ⟨1,by simp,by simp [knot_empty,fog]⟩
  | @insert i t e ih=>
    obtain ⟨c,hc,hx⟩:=ih; refine ⟨parity i t*c*parity (f i) (fog f s t),?_,?_⟩
    · let a:=parity i t; let b:=parity (f i) (fog f s t)
      have hy (i) (t:Finset m):star (parity i t)=parity i t:=by simp [parity]
      change star (a*c*b)*(a*c*b)=1; rw [star_mul,star_mul, hy,show star b=b by unfold b parity; simp]
      calc b*(_*a)*(a*c*b)=(star c*c)*(a*a)*(b*b):=by ac_rfl
           _ = _:=by rw [hc,parity_sq,parity_sq]; simp
    rw [kinds _ _ _ _ e,hx,map_smul,put_act, if_neg ((shade _ _ h _ _).not.mpr e),smul_smul,smul_smul, show insert (f i) (fog f s t)=fog f s (insert i t) from ?_]
    ext; simp [fog,or_left_comm]
lemma sigma(t u:Finset m) : inner ℂ (hoist f s (basisKet t)) (hoist f s (basisKet u))=inner ℂ (basisKet t) (basisKet u):=by
  obtain ⟨a,A,C⟩:= knotW f s h t; rw [hoops,hoops]; by_cases e:t=u
  · subst u; rw [C,inner_smul_right,inner_smul_left]; change a*(star a*_)=_; rw [←mul_assoc,mul_comm a,A]; simp
  obtain ⟨b,B,F⟩:= knotW f s h u; have he : fog f s t ≠ fog f s u:=by intro g; apply e; ext i; rw [←shade _ _ h, ←shade _ _ h,g]
  rw [C,F,inner_smul_left,inner_smul_right]; simp [he,e]
lemma sigh(x y:Wave m):inner ℂ (hoist f s x) (hoist f s y)=inner ℂ x y:=by
  nth_rw 1 2 [←basis_expand x]; nth_rw 1 2 [←basis_expand y]; simp_rw [map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,sigma _ _ h]
lemma hoistN(x:Wave m): ‖hoist f s x‖=‖x‖:=by
  have he:=sigh f s h x x; rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K] at he
  have hp : ‖hoist f s x‖^2=‖x‖^2:=by exact_mod_cast he
  nlinarith [norm_nonneg x,norm_nonneg (hoist f s x)]
def pailL : Wave n →L[ℂ] Wave m:=ContinuousLinearMap.adjoint (hoist f s)
lemma pails(y:Wave m)(x:Wave n):inner ℂ y (pailL f s x)=inner ℂ (hoist f s y) x:=ContinuousLinearMap.adjoint_inner_right ..
lemma pourL(x:Wave m): pailL f s (hoist f s x)=x:=by apply PiLp.ext; intro i; rw [←basis_inner,pails _ _ h,sigh _ _ h,basis_inner]
end YM.CF.Fock
