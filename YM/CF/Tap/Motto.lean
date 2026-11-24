import YM.CF.Tap.Breeze
import YM.CF.Proa.Wings
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tap
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Thera NormedSpace Branch Proa
variable {n:Type*}[LinearOrder n][Fintype n]{P W H A:Op n}(x:IsStarProjection P)
def cern(P W:Op n):=P*(W-1)*P
def nous(P W:Op n):= (1+cern P W)⁻¹*P
def Bop(P W:Op n):= laneP P W (nous P W)
variable (h: star H * W=1)(p:‖cern P W‖<1)
def charmE(P W:Op n):= pencil (cern P W)
-- power series trunc used in valuation (not trace-paired) later
include x p
lemma clan (h: star H*W=1):Clad P P W H (nous P W):=by
 let T:=cern P W; let A:=1+T; let B:=A⁻¹; have he:IsUnit A:=nearOne (by unfold A; rw [sub_add_eq_sub_sub,sub_self,zero_sub,norm_neg]; exact p)
 have hp : P*A=P*W*P:=by unfold A T cern; rw [mul_add,mul_one,←mul_assoc, ←mul_assoc,x.isIdempotentElem.eq,mul_sub,mul_one, sub_mul, x.isIdempotentElem.eq]; abel
 have hh : A*P=P*W*P:=by unfold A T cern; rw [add_mul,one_mul,mul_assoc _ P P,x.isIdempotentElem.eq, mul_sub,mul_one,sub_mul,x.isIdempotentElem.eq]; abel
 have hv:B*P=P*B:=by
    have ht:A*B=1:=(live he).1; have hl:B*A=1:=(live he).2; calc
      _ =B*(P*A)*B:=by rw [mul_assoc B (P*A),mul_assoc P A,ht,mul_one]
      _ = _ :=by rw [hp,←hh, ←mul_assoc,hl,one_mul]
 change Clad P P W H (B*P); refine ⟨x,x,h,?_,?_,?_,?_⟩
 · rw [←hh,hv,←mul_assoc,mul_assoc P B A,(live he).2,mul_one,x.isIdempotentElem.eq]
 rw [←hp, ←mul_assoc,mul_assoc P A B,(live he).1,mul_one,x.isIdempotentElem.eq]
 rw [hv,←mul_assoc,x.isIdempotentElem.eq]; rw [mul_assoc,x.isIdempotentElem.eq]
variable [Nonempty n]
lemma glorieux (u:Wave n)(e:Sea P u): skyGlow u W u=Complex.exp (Matrix.trace (charmE P W)):=by
 rw [charmE,← tally_log p,factor _ p,meadow x u e]; apply congrArg Matrix.det; unfold cern; rw [mul_sub,mul_one,sub_mul,x.isIdempotentElem.eq]; abel
include h
lemma trumpet (u:Wave n)(e:Sea P u): acts (quant W) u= Complex.exp (Matrix.trace (charmE P W)) • acts (exp (dg (Bop P W))) u:= by rw [broomstick (clan x p h) u u e e,glorieux x p u e]; rfl
omit x h p
-- kernels suitable negative determinant sector. cost support in Solo proven later on corresponding formula before conjugation.
def fabric(P:Op n):Letter (Cod n) n:=⟨Prod.fst, Prod.snd,fun i=> Proa.sprig i.1 P⟩
def elbow(P S W H:Op n)(v:Bool):= Proa.sprig v P * liftJet v S W H * Proa.sprig v P- Proa.sprig v P
def localTax(P S W H:Op n)(v:Bool):= Proa.sprig (!v) P * liftJet v S W H * Proa.sprig v P
private lemma rCalc (P S W H:Op n)(i:Cod n): main (fabric P) P S W H i= Proa.sprig i.1 P + elbow P S W H i.1 ∧ dust (fabric P) P S W H i= localTax P S W H i.1:=by
 unfold fabric main dust aqua elbow localTax; dsimp only; rw [add_sub_cancel]; exact ⟨(mul_assoc ..).symm,(mul_assoc ..).symm⟩ -- tune
private lemma slotC(P:Op n)(i:Cod n): dialL (fabric P) i=cry P i:=by
 rcases i with ⟨p,i⟩; cases p
 · change create _=seekF _ _; rw [seekF,prong_p]; rfl
 change remove _=hideF _ _; rw [hideF,prong_t]; rfl
def neck (V: Cod n→ n→ ℂ)(Q:Op n)(i:Cod n): FC n:= cry Q i + ∑ j,V i j • cry Q (i.1,j)
-- star convention for holes. provide oriented later
def pelic(P W H:Op n)(i:Cod n)(b:n):ℂ:= cSignX i.1 (elbow P (Bop P W) W H i.1 b i.2)
def torque(P W H:Op n): Cod n→Cod n→ℂ:= fuelC (fabric P) P (Bop P W) W H
include x
private lemma oK(i:Cod n): cane (fabric P) P (Bop P W) W H i=neck (pelic P W H) P i:=by
 let F:=fabric P; let S:= Bop P W; let U:=F.seek i; let J:= Proa.sprig U P; let A:=main F P S W H i; let D:= elbow P S W H U
 have ht:A=J+D ∧ dust (fabric P) P S W H i=localTax P S W H U:=rCalc ..
 have hp:J*D=D:=by
    have hk:J*J=J:=by unfold J Proa.sprig; cases U; exact x.one_sub.isIdempotentElem.eq; exact x.isIdempotentElem.eq
    unfold J at hk; unfold J D elbow; rw [mul_sub,←mul_assoc,←mul_assoc,hk]
 change creed U (acts A (basisKet i.2))=cry _ _+_
 rw [ht.1,act_add, creed_a, show creed U (acts J (basisKet i.2))=cry _ _ from slotC P i]; congr 1
 let V:=acts D (basisKet i.2); change creed U V=∑ j, _; have hx : (acts J) V=V:=by unfold V; rw [←act_mul,hp]
 nth_rw 1 [←hx,←basis_expand V]; rw [map_sum]
 cases hc:i with| mk u a=>
    have hv:U=u:=congrArg Prod.fst hc; cases u;
    · rw [hv]; change create _= _; rw [map_sum]; apply sum_congr rfl; intro j hj; rw [map_smul,map_smul]; change _ • create ( (acts J) _) = pelic _ _ _ _ j • seekF P _; rw [show J=1-P from (by unfold J; rw [hv]; rfl), seekF,prong_p]; congr 1; unfold pelic V D; rw [basis_act,hv,hc]; rfl
    rw [hv]; change remove _= _; unfold remove; rw [map_sum,star_sum]; apply sum_congr rfl; intro j hj; rw [map_smul,map_smul,star_smul]; change _ • star (create (acts J _))= _ • hideF _ _; rw [hideF,prong_t, show J=P from (by unfold J; rw [hv]; rfl)]; congr 1; unfold pelic V D; rw [basis_act,hv,hc]; rfl
include h p
-- exact Wave iteration also paid leading bra. H is star-inverse. A local spin cut commutes with W only.
lemma ballad (u m: Wave n)(e: Sea P u){C:Op n}(c:IsStarProjection C)(t:Sea C m)(g:‖cern C W‖<1)(hw:star W=W)(q:Commute W C)(I:List (Cod n)): let z:=skyGlow m W m; let V(y:Wave n):= z⁻¹ • acts (quant W) y
 let M':= neck (pelic P W H) P; let F':= charmE P W - charmE C W
 TagG P (Bop P W) ∧ (∀ y,inner ℂ m (V y)=inner ℂ m y) ∧ V (acts (rollC (cry P) I) u) = Complex.exp (Matrix.trace F') • acts (exp (dg (Bop P W))) (((claps I).map (invest M' u (torque P W H))).sum):=by
 intro z V M F'; let F:=clan x p h; have ht:cern P W= cern _ _:=rfl; let D:=Bop P W
 have hu:=shines (clan c g h) m m t t
 have hl : acts (star (quant W)) m=star z • m:=by
   have hk:star z=z:=by unfold z; rw [starbeam,hw]
   have hA: Bop C W=0:=by unfold Bop laneP; rw [show (1-C)*W=W*(1-C) from (((Commute.one_right W).sub_right q).eq).symm]; let Y:=clan c g h; nth_rw 1 [← Y.tray]; rw [mul_assoc,←mul_assoc (1-C),show (1-C)*C=0 from (by rw [sub_mul,one_mul,c.isIdempotentElem.eq,sub_self]),zero_mul,mul_zero]
   rw [←quant_star,hw,hk, trumpet c h g m t,hA, tallied 0 (by simp),add_zero,quant_one,act_one]; rw [show z=_ from glorieux c g m t] -- tune
 refine ⟨⟨F.bare,F.chest⟩,fun y=>?_,?_⟩
 · unfold V; rw [inner_smul_right,←act_inner,hl,inner_smul_left]; simp [z,hu]
 let L:= quant ((1-D)*W); let Λ:=exp (dg D); have hf:Λ*L=quant W:=by unfold Λ L D Bop; rw [tallied _ F.reef,←quant_mul,←mul_assoc,F.flick,one_mul]
 let T:= fabric P; let J:=chime (cry P) u; let N:=ivy T D W H; let f:=fuelC T P D W H
 have he:acts L u = skyGlow u W u • u:=by unfold L D Bop; rw [quant_mul,act_mul,broomstick F u u e e,map_smul, tallied _ F.reef,←act_mul,←quant_mul,mul_eq_one_comm.mp F.flick,quant_one,act_one]
 have hm (l:List (Cod n)): L*rollC (cry P) l= rollC N l*L:=by
    induction l with
    | nil=>simp [rollC]
    | cons i l ih=> change L*(_*rollC _ _) = _*rollC _ _*L; rw [←mul_assoc,show L*cry P i=N i* L from (by rw [←slotC]; exact super T D W H F.reef F.rain i),mul_assoc,ih, ←mul_assoc] -- tune
 unfold V; rw [←hf,act_mul,←act_mul L, hm, act_mul,he, map_smul,map_smul, smul_smul]; have hx:z⁻¹*skyGlow u W u=Complex.exp (Matrix.trace F'):=by unfold z F'; rw [glorieux x p u e, glorieux c g m t, Matrix.trace_sub, Complex.exp_sub,div_eq_mul_inv,mul_comm]
 rw [hx,show acts (rollC N _) _=chime N u I from rfl,shadeW _ _ _ _ _ (ash_T T P D W H u x e) (ash_F T P D W H) (ivy_v T P D W H)]; rw [funext (oK (W:=W) (H:=H) x)]; rfl
end YM.CF.Tap
