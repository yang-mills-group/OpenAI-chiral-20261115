import YM.CF.Urn.Mellow
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Urn
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Proa
variable {I α ι n m: Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m][LinearOrder ι][Fintype ι]
open Stilo Scree Hake
variable {r:Type*}[LinearOrder r][Fintype r]
abbrev humZ(r n:Type*)[LinearOrder r][Fintype r][LinearOrder n][Fintype n]:FC n := 0
lemma tag_t(P:FC (LinkI ι n)): acts (∑ i:Finset n,(pailL seenH ∅ (acts P (pod _))).ofLp i • Pastry.poke i) (pod n) = pailL seenH ∅ (acts P (pod _)):=by
 rw [act_sum]; simp_rw [act_smul,show ∀ i:Finset n, acts (Pastry.poke i) (pod n)=basisKet i from Pastry.poked]; exact basis_expand _
lemma dueE(P:Pastry.Poly m n)(L:m→m→ℂ)(D:List m): P.eval (rollC (roseB L put) D)=rollC (roseB L P.term) D:=by -- Linear induction
 have hw(x:m):spanP m (roseB L put x):=slap L x
 have hp(x:m):P.eval (roseB L put x)=roseB L P.term x:=by
    unfold roseB; rw [map_sum]; apply sum_congr rfl; intro j _; rw [map_smul]; apply congrArg; rw [show put j=Pastry.poke {j} from (Pastry.Poly.tag_once (Pastry.cane _) _).symm,Pastry.Poly.eval_oneT,Pastry.Poly.tag_once]
 induction D with
 | nil=> exact P.eval_one
 | cons i D ih=>
    rw [show rollC _ _= roseB L put i *rollC _ D from rfl,Scree.fireT P (hw i) ?_, hp,ih]; rfl
    clear ih; induction D with| nil=> exact grandP | cons i l H=> exact spanT (hw _) H
lemma dueW(F:Oboe r→ FC n)(H:Restart F)(L:Oboe r→Oboe r→ℂ)(D:List (Oboe r)): hail H (rollC (roseB L bell) D)= rollC (roseB L F) D:=by
 -- generalize prefix. hailW
 suffices he:∀ S:List (Oboe r), hail H (rollC bell S * rollC (roseB L bell) D)=rollC F S*rollC (roseB L F) D by simpa only [rollC,List.map_nil,List.prod_nil,one_mul] using he []
 intro S; induction D generalizing S with
 | nil=> simpa only [rollC,List.map_nil,List.prod_nil,mul_one] using hailW H S
 | cons i D ih=>
    rw [show rollC _ (i::D)=roseB L bell i*rollC (roseB L bell) D from rfl,show rollC _ (i::D)=roseB L F i*rollC (roseB L F) D from rfl]; conv_lhs=>arg 2; rw [← mul_assoc];
    unfold roseB; simp only [sum_mul,mul_sum, map_sum]; -- tune
    apply sum_congr rfl; intro j _; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,map_smul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm]; apply congrArg; simpa only [rollC,roseB,List.map_append,List.prod_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,mul_assoc] using ih (S++[j]) -- tune rollC app
lemma list_ζ(P:m→ FC n)(h:FC n →+* FC n)(Q:List m):h (rollC P Q)=rollC (h ∘ P) Q:=by unfold rollC; rw [map_list_prod,List.map_map] -- tune
lemma mapT(R:Type*)[Ring R](F:ι→R)(G:ι→ι→R)(Y:R→+*R)(D:List ι):Y (taskC F G D)=taskC (Y ∘ F) (fun i j=> Y (G i j)) D:=by
 suffices hh:∀ n D,Y (ticketB F G n D)=ticketB (Y ∘ F) (fun i j=> Y (G i j)) n D from hh D.length D
 intro n; induction n with
 | zero=> exact fun _=> Y.map_one
 | succ n ih=>intro D; cases D with| nil=> exact Y.map_one| cons i D=> rw [ticketB,ticketB,map_add,map_mul,ih,map_list_sum, List.map_map]; congr 2; apply List.map_congr_left; intro j _; rw [Function.comp_apply,map_mul, ih]; congr 1; split_ifs; exact Y.map_neg _; rfl -- tune
lemma octave (F G:ι→n→ℂ)(P Q:ι→ι→ℂ)(E:FC m→+*FC m)(C:FC r→+*FC r)(H: FC n →+* FC n)(u:m↪ι)(v:Hake.Oboe r↪ι)(L:ι→ι→ℂ)(b:m→m→ℂ)(j:Hake.Oboe r→Oboe r→ℂ)(p:∀ i j,P (u i) (u j)+P (u j) (u i)=0)(hp:∀ i j,P (v i) (v j)+P (v j) (v i)= if i=Hake.revertP j then 1 else 0)(x:∀ i j,Q (u i) (u j)+Q (u j) (u i)=0)(k:∀ i j,Q (v i) (v j)+Q (v j) (v i)= if i=Hake.revertP j then 1 else 0)(t:∀ i j,H (Stilo.price P n i j)=Stilo.price (taxL L Q) n i j)(f: ∀ i,H (lank F i)= roseB L (lank G) i)(he:∀ i,E (put i)=roseB b put i)(hc:∀ i,C (Hake.bell i)=roseB j Hake.bell i)(ℓ:∀ i,roseB L (chim Q G) (u i)=roseB b (chim Q G ∘ u) i)(l:∀ i,roseB L (chim Q G) (v i)=roseB j (chim Q G ∘ v) i)(S:List m)(T:List (Oboe r)): H (pet P F u v p hp (rollC put S) (rollC Hake.bell T))= pet Q G u v x k (E (rollC put S)) (C (rollC Hake.bell T)):=by
 let D:=S.map u ++ T.map v; let U:= taskC (lank F) (Stilo.price P n)
 rw [← show U D= _ from pet_r .., show H (U D)= taskC (roseB L (lank G)) (Stilo.price (taxL L Q) n) D from ?_, list_ζ,list_ζ]
 swap; · dsimp only [U]; rw [mapT]; congr 1 <;> funext i; exact f _; exact funext (t _)
 rw [show (C ∘ bell)=roseB j bell from funext hc,show (E ∘ put)= roseB b put from funext he]
 apply borderE ?_ (pitch_s _ _ _ _ x k _ _); swap; · rw [←tallP]; exact rent_m ..
 rw [rateW]; unfold pet; rw [dueE,dueW _ (hhP Q G v k)]; -- F wrong
 dsimp only; rw [tag_t]; unfold chime D rollC; rw [List.map_append,List.prod_append,List.map_map,List.map_map]; congr 3; rw [show roseB L (chim Q G) ∘ u=roseB b _ from funext ℓ]; rw [show roseB L (chim Q G) ∘ v=roseB j _ from funext l]; rfl
end YM.CF.Urn
