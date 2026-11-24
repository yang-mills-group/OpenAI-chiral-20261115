import YM.CF.Exa.Sight
set_option autoImplicit false
noncomputable section
namespace YM.CF.Exa
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Thera NormedSpace Branch Proa
variable {n:Type*}[LinearOrder n][Fintype n]{P W H A:Op n}(x:IsStarProjection P)
open Tap
variable [Nonempty n]
lemma rCalc (P S W H:Op n)(i:Cod n): main (fabric P) P S W H i= Proa.sprig i.1 P + elbow P S W H i.1 ∧ dust (fabric P) P S W H i= localTax P S W H i.1:=by
 unfold fabric main dust aqua elbow localTax; dsimp only; rw [add_sub_cancel]; exact ⟨(mul_assoc ..).symm,(mul_assoc ..).symm⟩ -- tune
lemma slotC(P:Op n)(i:Cod n): dialL (fabric P) i=cry P i:=by
 rcases i with ⟨p,i⟩; cases p
 · change create _=seekF _ _; rw [seekF,prong_p]; rfl
 change remove _=hideF _ _; rw [hideF,prong_t]; rfl
include x
lemma oK(i:Cod n): cane (fabric P) P (Bop P W) W H i=neck (pelic P W H) P i:=by
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
variable (h: star H * W=1)(p:‖cern P W‖<1)
include h p
lemma jazz(u:Wave n)(e: Sea P u)(I:List (Cod n)) : let M':= neck (pelic P W H) P; let F':= charmE P W
 acts (quant W) (acts (rollC (cry P) I) u) = Complex.exp (Matrix.trace F') • acts (exp (dg (Bop P W))) (((claps I).map (invest M' u (torque P W H))).sum):=by
 intro M F'; let F:=clan x p h; let D:=Bop P W
 let L:= quant ((1-D)*W); let Λ:=exp (dg D); have hf:Λ*L=quant W:=by unfold Λ L D Bop; rw [tallied _ F.reef,←quant_mul,←mul_assoc,F.flick,one_mul]
 let T:= fabric P; let J:=chime (cry P) u; let N:=ivy T D W H; let f:=fuelC T P D W H
 have he:acts L u = skyGlow u W u • u:=by unfold L D Bop; rw [quant_mul,act_mul,broomstick F u u e e,map_smul, tallied _ F.reef,←act_mul,←quant_mul,mul_eq_one_comm.mp F.flick,quant_one,act_one]
 have hm (l:List (Cod n)): L*rollC (cry P) l= rollC N l*L:=by
    induction l with
    | nil=>simp [rollC]
    | cons i l ih=> change L*(_*rollC _ _) = _*rollC _ _*L; rw [←mul_assoc,show L*cry P i=N i* L from (by rw [←slotC]; exact super T D W H F.reef F.rain i),mul_assoc,ih, ←mul_assoc] -- tune
 rw [←hf,act_mul,←act_mul L, hm, act_mul,he, map_smul,map_smul,glorieux x p]; swap; exact e
 rw [show acts (rollC N _) _=chime N u I from rfl,shadeW _ _ _ _ _ (ash_T T P D W H u x e) (ash_F T P D W H) (ivy_v T P D W H)]; rw [funext (oK (W:=W) (H:=H) x)]; rfl
end YM.CF.Exa
