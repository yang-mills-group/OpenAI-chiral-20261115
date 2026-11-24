import YM.SU5.FiniteGaugeData.Brique.Comet
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Fock.Brique
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Tenant Tulip Peaks
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I]
variable {d e:ℝ}
local notation "Β" => Finset I
section
variable (Y P:Op I) (hp:Y*P=Y) (w:P*Y=P) -- P rank d
-- StarProjection onto image. trace without rank purchase.
def Ortho : Op I:= (Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ)).symm ((acts Y).range.starProjection)
lemma Ortho_clm : acts (Ortho Y)=(acts Y).range.starProjection:=by rw [Ortho,acts]; exact StarAlgEquiv.apply_symm_apply _ _ --] -- tune
lemma ortho_project : IsStarProjection (Ortho Y):=by
 have he:= Ortho_clm Y; constructor
 · unfold IsIdempotentElem Ortho; rw [←map_mul,Submodule.isIdempotentElem_starProjection (acts Y).range]
 unfold IsSelfAdjoint Ortho; apply (((Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ)).symm.map_star' _).symm.trans _); rw [(isSelfAdjoint_starProjection _).star_eq]; rfl
lemma refill (x:Ket I): ∃ t,acts Y t=acts (Ortho Y) x:= by rw [Ortho_clm]; exact (acts Y).range.starProjection_apply_mem x
lemma tankL_Y : Ortho Y * Y=Y:= by apply op_columns; intro i; rw [act_mul, Ortho_clm]; apply Submodule.starProjection_eq_self_iff.mpr; exact ⟨_,rfl⟩
include hp w
lemma tankL_quad : Y*(Ortho Y)=(Ortho Y) :=by
 have hx : Y*Y=Y:=by nth_rw 1 [←hp]; rw [mul_assoc,w,hp]
 apply op_columns; intro i; rw [act_mul]; obtain ⟨v,h⟩:= refill Y (basisKet i); rw [←h,←act_mul,hx]
lemma tankL_trace : (Ortho Y).trace=P.trace:= by
 rw [←tankL_quad Y P hp w,Matrix.trace_mul_comm,tankL_Y]; calc
    _ = _:=?_; -- tune
 rw [←w,Matrix.trace_mul_comm,hp]
omit hp w
lemma ortho_cellar {S:Finset I}(w:cutM S*Y=Y):Cellar S (Ortho Y):=by
 apply Cellar.left_data _ (ortho_project _).2; apply op_columns; intro j; rw [act_mul]; obtain ⟨v,h⟩:= refill Y (basisKet j); rw [← h,←act_mul,w]
end
section
variable (T Z S:Finset I) (A:Op I)
set_option quotPrecheck false
local notation "Π₀" => cutM T
local notation "Π₁" => cutM Tᶜ
local notation "Σ" => cutM S
def starBoost (T:Finset I)(A:Op I)(i:I): FC I:=1+create (acts (cutM Tᶜ*A) (basisKet i))*takeF i
abbrev starMark0 (T:Finset I)(A:Op I)(S: Finset I):FC I:= Scree.column (starBoost T A) S
lemma starBoost_star (i:I) : star (starBoost T A i)=1+put i * remove (acts (Π₁*A) (basisKet i)):= by simp only [starBoost,star_add,star_one,star_mul,takeF,star_star]
-- no generator signs in product of even. Present expansion later.
lemma weave (i:I) (x:Ket I):
  create (x+x.ofLp i • acts (Π₁*A) (basisKet i)) * starBoost T A i = starBoost T A i * create x:=by
 let U:= acts (Π₁*A) (basisKet i); let V:= create U; let G:=takeF i
 have he: create x*V= -(V*create x):=eq_neg_of_add_eq_zero_left (car_create ..)
 have hx:x.ofLp i • (1:FC I)= G * create x+create x*G:= by rw [←basis_inner, show G=remove (basisKet i) from (remove_take ..).symm]; exact (car (basisKet i) x).symm
 change create (x+x.ofLp i • U)*(1+V*G)=(1+V*G)*create x
 rw [map_add,map_smul]; change (create x + _ • V)*(1+_)=_
 suffices u: create x*(V*G)+(x.ofLp i) • V=V*G* create x by rw [add_mul,add_mul,mul_add,mul_add, Algebra.smul_mul_assoc (x.ofLp i),Algebra.smul_mul_assoc, ←mul_assoc V, show V*V=0 from create_sq U, zero_mul,smul_zero,mul_one,mul_one,one_mul,add_zero,add_assoc,u] -- order
 rw [←mul_assoc (create x),he,neg_mul,show x.ofLp i • V= V*(x.ofLp i • 1) by rw [Algebra.mul_smul_comm,mul_one],hx,mul_add,←mul_assoc V,←mul_assoc V]; abel
-- First arg resets because upper unperturbed. induces orientation in boost list reversed vs Mark. group trace accessible. 
lemma starM_weave (p:S⊆T) (x:Ket I) :
  create (x+ acts (Π₁*A*Σ) x) * starMark0 T A S= starMark0 T A S * create x:= by
 induction S using induction_on_min with
 | empty=> rw [show starMark0 T A ∅=1 by simp [starMark0,Scree.column]]; simp [cutM]
 | insert i S g ih =>
    have ht: i∉ S:=fun v=>lt_irrefl i (g i v)
    let X:=Π₁*A; let v:= acts (Π₁*A*cutM S) x; have hp:v.ofLp i=0:=by unfold v; rw [mul_assoc Π₁,act_mul,cut_apply]; exact if_neg (by simpa using p (mem_insert_self ..) : ¬ i∈Tᶜ)
    rw [show cutM (insert i S) = cutM {i}+cutM S from cut_disj (by simp [ht] : Disjoint ({i}:Finset I) S)]; -- needs union_insert
    rw [mul_add,act_add, show acts (Π₁*A*cutM {i}) x=x.ofLp i • acts (Π₁*A) (basisKet i) by rw [act_mul,cut_oneAct,map_smul], show starMark0 T A (insert i S)=starBoost T A i*starMark0 T A S by rw [starMark0,Scree.column,sort_insert _ (fun j hj=>(g j hj).le) ht,List.map_cons,List.prod_cons]; rfl]
    change create (x+ (_ + v))*_= _; rw [add_comm _ v,←add_assoc]; -- probably changes x?
    have he:(x+v).ofLp i=x.ofLp i:= by simp [hp]
    let y:=x+v; have hq:create y* starMark0 T A S=starMark0 T A S*create x:= ih ((subset_insert i S).trans p)
    rw [←he,←mul_assoc, weave, mul_assoc,hq,←mul_assoc]
lemma wore (P: Op I)(x: Wave I) (p:IsStarProjection P)(t:Sea P x) : Full P x := by
 intro u h; obtain ⟨U,S,rfl⟩:=spot_projection P p; let A:= acts (quantU U).val (basisKet S); let c := inner ℂ A x
 have he: x=c • A:= by nth_rw 1 [← t.1]; exact (by simp_rw [act_twistLine,←quant_column]; rfl)
 let v:=acts (star U.val) u; have ht:u=acts U.val v:=(act_starUnit ..).symm; have hv:Buffered.withinM S v:= by
    have hl:=congrArg (fun x=>acts (star U.val) x) h; rw [← act_starUnit U u,← Fock.swivel,act_unit] at hl; simpa [act_starUnit] using hl
 have hz: acts (create v) (basisKet S) = 0 :=by rw [create_def,act_sum]; refine sum_eq_zero fun i _=>?_ ; rw [act_smul,put_act]; by_cases h:i∈S; rw [if_pos h,smul_zero]; rw [(Buffered.within_test ..).mp hv _ h,zero_smul]
 rw [ht,←twist_create,he,map_smul, show A=_ from rfl,←swivel,hz,map_zero,smul_zero] -- A reduction

-- spotlight kernel after Boost: requires A columns relevant to S pins, `Y=A*Σ`, `Πo`=S0 as above. Seed mark contains lower component. `Y*Σ* Π₀*Y=Y`.
lemma starM_complete (p:S⊆T)(h: Σ*A*Σ=Σ)(x:Wave I)(v:Sea Π₀ x):Full (Ortho (A*Σ)) (acts (starMark0 T A S) x):=by
 let Y:= A*Σ; intro i hp; obtain ⟨u,g⟩:=refill (A*Σ) i; rw [hp] at g; let t:= acts Π₀ i
 have hx:Σ*Π₀=Σ:=by rw [cut_meet,inter_eq_left.mpr p]
 have hr:Y*Σ=Y:=by unfold Y; rw [mul_assoc,show Σ*Σ=Σ from (cutM_idp _).1]
 have he:i=t+acts (Π₁*A*Σ) t:=by
    have ht: acts Σ t= acts Σ u:=by unfold t; rw [←act_mul,hx,←g,←act_mul,←mul_assoc,h]
    rw [show acts (Π₁*A*Σ) t=acts Π₁ i from (by rw [act_mul _ Σ,ht,act_mul,←act_mul A,g])]; unfold t; rw [←act_add,dim_cut]; abel_nf; simp
 rw [he, ←act_mul,starM_weave T S A p,act_mul,(wore _ x (cutM_idp _) v) t (Cellar.stanch T _),map_zero]
variable [Nonempty I]
lemma starM_cost (e:0 ≤ d) (h:‖A‖ ≤ d) : ‖starMark0 T A S‖ ≤ (1+d)^S.card:=by
 have ht(i:I): ‖starBoost T A i‖ ≤ 1+d:=by
    have hP:‖Π₁*A‖ ≤ d:= (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) ((cutM_idp _).norm_le _)).trans h)
    let U:=create (acts (Π₁*A) (basisKet i)); have hz:‖U‖ ≤ d:=le_trans (Flare.cost_pe false _) ((Flare.opy (Π₁*A) _).trans (by rw [show ‖basisKet i‖=1 by simp, mul_one]; exact hP));
    refine (norm_add_le ..).trans (add_le_add (norm_one (α:=FC I)).le ((norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg U) ?_).trans hz)))
    rw [←remove_take i]; change ‖remove (basisKet i)‖ ≤ 1; exact (Flare.cost_pe true (basisKet i)).trans (show ‖basisKet i‖≤1 by simp)
 induction S using induction_on_min with
 | empty=> simp [starMark0,Scree.column]
 | insert i S g ih=>
    have he : i∉S:=fun u=>lt_irrefl i (g i u); rw [card_insert_of_notMem he,starMark0,Scree.column, sort_insert (·≤·) (fun j p=>(g j p).le) he,List.map_cons,List.prod_cons,pow_succ']; exact (norm_mul_le ..).trans (mul_le_mul (ht i) ih (norm_nonneg _) (by positivity)) -- arrow reduction
end
end YM.CF.Fock.Brique
