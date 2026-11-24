import YM.CF.Mew.Pot
import GaugeFieldConstruction.Harle
import YM.CF.Sault.Faro
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock.Wosk
open Function Set Metric MeasureTheory NormedSpace Filter Finset
open scoped Topology Classical
open Roots Mew Roots.GJ
variable {I J B V W G E:Type}[LinearOrder I][Fintype I][DecidableEq J]
open Pastry
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
attribute [local instance] opCStarAlgebra
variable (Z:Finset J)(y:Key I)(σ:I→J)(x:B)[LinearOrder G][Fintype G] (W:G→ G→ Toil I J B)(r:ℝ)(f:I→Book0 I J G B)
def Keeps: List I → Book0 I J G B
| []=>[]
| i::l=> Keeps l ++ topL W r (Keeps l) (f i)
variable (Γ:Book0 I J G B)
def upperW (i:Option (G×G)):Dough G := ⟨logL put i,by cases i with|none=>exact Flour.grainE|some i=> exact Flour.putPut _ (mem_univ _) (mem_univ _)⟩
def RiseW : PairLog G →ₗ[ℂ] Dough G where
 toFun v:= ∑ i,v i • upperW i
 map_smul' _ _:=by simp [smul_sum,mul_smul]
 map_add' _ _:=by simp [add_smul,sum_add_distrib]
lemma Rise_val (v:PairLog G):(RiseW v).val=binW put v:=by
 -- $Subtype.val$. re markers
 change (pasta _).val _=_
 rw [show ∀(v:PairLog G),RiseW v=∑ i,v i•upperW i from fun _=>rfl,map_sum]; change (∑ i,_:FC G)=binE put v
 rfl
abbrev Bore0 (Q: Book0 I J G B)(z:Key I):=RiseW (cryY Z z x Q)
def μFormal(i:Option (G×G))(W:Dough G):=crumb W.val ∅ -- tune
lemma μStab(g:G→ G→ℂ)(w:Wave G): True:=trivial
lemma γRise_L : River (fun z=>cryY Z z x Γ):=by
 induction Γ with
 | nil=> exact zeroR _
 | cons i l h=>
    simp only [cryY, consA]; refine dub_V ?_ h
    let V:PairLog G:=Pi.single i.val 1; exact prodR (ContinuousLinearMap.lsmul ℂ ℂ) (eg_R _ _ _) (zeroR V) -- $smul order$
lemma γRise_P : River (Bore0 Z x Γ):=by exact sc_V (γRise_L Z x Γ) (LinearMap.toContinuousLinearMap (RiseW (G:=G)))
variable {n:Type}[LinearOrder n][Fintype n]
variable (V': Poly G n)(F A:G→ FC n)(H:G→ G →ℂ)(w:Wave n)(p:Flesh F V'.term A H w)
def surveyR(L: List I)(z:Key I): FC n:= (L.map fun i=> 1+binW F (cryY Z z x (f i))).prod
lemma eval_F (a:PairLog G): V'.cook (RiseW a)= binW V'.term a:=by
 change V'.eval _=_; rw [Rise_val]; change V'.eval (∑ i,_:FC G)=binE V'.term a; rw [map_sum]; refine sum_congr rfl fun i _=>?_; rw [map_smul]; apply congrArg (a i • ·); cases i with|none=> exact V'.eval_one|some i=> exact V'.eval_double ..
-- complex-linear versions
abbrev seeFC : Dough G →L[ℂ] FC n:=(LinearMap.toContinuousLinearMap ({ toFun:= V'.cook,map_add':=fun _ _=>map_add ..,map_smul':=fun _ _=>map_smul (V'.eval) _ _}:Dough G→ₗ[ℂ] FC n)) -- tune
abbrev seeF(g:Wave n): FC n →L[ℂ] Wave n:=LinearMap.toContinuousLinearMap ({ toFun:= fun x => acts x g,map_add':=fun _ _=>act_add ..,map_smul':=fun _ _=>act_smul ..}: FC n →ₗ[ℂ] Wave n)
abbrev fleshB {m:Type}[Fintype m][LinearOrder m]: FC m →L[ℂ] Wave m→L[ℂ]Wave m:=LinearMap.toContinuousLinearMap ({toFun:=fun v=> acts v,map_add':=fun i j=> ContinuousLinearMap.ext (fun z=>act_add ..),map_smul':=fun i j=> ContinuousLinearMap.ext (fun z=>act_smul ..) }: FC m→ₗ[ℂ] Wave m→L[ℂ]Wave m)
lemma kin_eqR (σ:I→J){E:Type}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E](f g:Key I→ E)(h:River f)(p:f=g):Kin σ f g:=p ▸ Kin.refl σ h -- order
lemma Kin_0 {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E](σ:I→ J)(f:Key I→ E)(h:∀ z,f z=0):Kin σ f (fun _=>0):=by rw [show f=(fun _=>0) from funext h]; exact Kin.refl _ (zeroR _)
include p
lemma Formal_Canon(L:List I)(s:∀i:Key I,cryH W Z i x=H)(h:∀ i∈ L,∀z:Key I,z i=0 →cryY Z z x (f i)=0): Kin σ (fun z=> acts (V'.cook (exp (Bore0 Z x (Keeps W r f L) z))) w) (fun z=>acts (surveyR Z x f F L z) w):=by
 induction L with
 | nil=>
    simp only [surveyR,List.map_nil,List.prod_nil, Keeps]
    have hv(z:Key I): Bore0 Z x ([]:Book0 I J G B) z=0:=map_zero _
    simp_rw [hv,exp_zero,map_one]; exact Kin.refl _ (zeroR _)
 | cons i l ih=>
    let U:= Keeps W r f l; let E:=Bore0 Z x U; let T:= topL W r U (f i); let D:= Bore0 Z x T; let M(z:Key I):=binW F (cryY Z z x (f i)); let K(z:Key I):=exp (D z)
    have hp(y:Key I): D y= RiseW (bondR H (cryY Z y x U) (cryY Z y x (f i))):=by unfold D T Bore0; rw [topP,s y]
    have hz:Kin σ K (fun z=>1+D z):=sprigE σ i (γRise_P _ _ _) fun z a=>by rw [hp,h _ (List.mem_cons_self) z a,bondR]; simp
    let J0(z):= exp (E z); have hk:= Kin.refl σ (γRise_P Z x U).exp_V; have hK:Kin σ (fun z=> V'.cook (J0 z*K z)) (fun z=>V'.cook (J0 z*(1+D z))):= Kin.map (hk.mulT hz) (seeFC V')
    let A0:= (fleshB (m:=n)); let Q(z:Key I):=M z; have hf: River M:= sc_V (γRise_L Z x (f i)) (LinearMap.toContinuousLinearMap (binW F))
    let Lm(z:Key I):= 1+M z; have hM :River Lm:= dub_V (zeroR _) hf; have he:= Kin.prod A0 (Kin.refl σ hM) (ih fun j a=>h j (List.mem_cons_of_mem _ a)) -- tune
    let Vz(z:Key I):=surveyR Z x f F l z
    have hplus(z:Key I): V'.cook (exp (Bore0 Z x (Keeps W r f (i::l)) z))= V'.cook (J0 z*K z):=by
       congr 1; letI : NormedAlgebra ℚ (Dough G):=NormedAlgebra.restrictScalars ℚ ℝ _; rw [show Bore0 Z x (Keeps W r f (i::l)) z= E z+D z from ?_,exp_add]; unfold Bore0 Keeps cryY; rw [appA,map_add]; rfl
    have hmul(z:Key I): acts (V'.cook (J0 z*(1+D z))) w= A0 (Lm z) (acts (V'.cook (J0 z)) w):=by
       rw [mul_comm,map_mul,map_add,map_one,add_mul,one_mul,act_add]; change _=acts (1+M z) _; rw [act_add,act_one]; apply congrArg (acts (V'.cook (J0 z)) w+·); rw [act_mul,hp,eval_F, show V'.cook (J0 z)=exp (binW V'.term (cryY Z z x U)) from (V'.rising _).trans (congrArg exp (eval_F ..)),←Tap_P _ _ _ _ _ p]
    have hΓ(z: Key I): acts (surveyR Z x f F (i::l) z) w=A0 (Lm z) (acts (Vz z) w):=act_mul _ _ _
    simp_rw [hplus,hΓ]
    have hr:Kin σ (fun z=> acts (V'.cook (J0 z*K z)) w) (fun z=> acts (V'.cook (J0 z*(1+D z))) w):= Kin.map hK (seeF w); simp_rw [hmul] at hr
    exact hr.trans he
#print axioms Formal_Canon
end YM.CF.Fock.Wosk
end
