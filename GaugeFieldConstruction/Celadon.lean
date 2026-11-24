import YM.CF.Delta.Rebase
import YM.CF.BProof.Wick.Grad
import YM.CF.Aroma.Cyclone
set_option autoImplicit false
set_option maxHeartbeats 160000
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Fock.Celeb
open Filter NormedSpace Function Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ContDiff Topology
attribute [local instance] opCStarAlgebra
open BProof.Wick
-- through genuine Wilson P, no uniform invertibility for line chart cost; lemma is pointwise.
variable {I:Type*}[Fintype I][LinearOrder I]
private abbrev columnM (i j:I):Op I→L[ℝ] ℂ:= (⟨⟨fun x=> x i j,fun _ _=>rfl⟩,fun _ _=>rfl⟩: Op I→ₗ[ℝ]ℂ).toContinuousLinearMap
lemma pair_c: ContDiff ℝ ω (pairWave (n:=I)):=by
 have he:ContDiff ℝ ω (squareP (n:=I)):= ContDiff.sum fun i _=> ContDiff.sum fun j _=> ((columnM i j).contDiff).smul contDiff_const
 have hp:ContDiff ℝ ω (coupl (n:=I)):= he.const_smul (2:ℂ)⁻¹
 refine ContDiff.sum fun k _=> ContDiff.const_smul (f:=fun x:Op I=>acts (coupl x ^ k) (vacuum I)) _ ?_
 exact (((actCL _).contDiff.comp (hp.pow k)).clm_apply contDiff_const)
lemma wove_ω(s:Finset I):ContDiff ℝ ω fun z:Op I=> wedge z s:=by
 induction s using induction_on_min with
 | empty=> simp_rw [wedge_empty]; exact contDiff_const
 | insert i v t ih=>
   simp_rw [wedge_min _ v i t]
   let K(x:Op I): Ket I:= acts x (basisKet i); have he:ContDiff ℝ ω K:= (actCL I).contDiff.clm_apply contDiff_const
   exact ((actCL _).contDiff.comp (((create (n:=I)).toContinuousLinearMap.restrictScalars ℝ).contDiff.comp he)).clm_apply ih
lemma quants_c:ContDiff ℝ ω (quant (n:=I)):=by
 let d := Finset I; let m:=Finset I → Finset I→ℂ
 -- separate pi
 let A:m →ₗ[ℝ] FC I:=⟨⟨fun x=>Matrix.of x,fun _ _=>rfl⟩,fun _ _=>rfl⟩
 refine A.toContinuousLinearMap.contDiff.comp (f:=fun x:Op I=> fun s t:Finset I=> (wedge x t).ofLp s) (contDiff_pi.mpr fun s=> contDiff_pi.mpr fun t=>?_)
 let Y:Wave I→L[ℝ]ℂ:=((innerSL ℂ (basisKet s)).restrictScalars ℝ); convert Y.contDiff.comp (wove_ω t) using 1; ext; first | rfl | simp [Y, comp_def]
-- lineOp potentiation
variable {x:ℝ}{F:ℝ→Op I}{A':Op I}
abbrev DX (D:Op I): ℝ→Op I := fun t=> 1+(t-x) • D
local notation "p"=>F x
local notation "D'"=> A'*p - p*A'
lemma lamp_D (h:∀ᶠ i in 𝓝 x,IsStarProjection (F i)) (hF: HasDerivAt F A' x): D' *p+p*(-D')= A' ∧ p*D'*p=0 :=by
 have e:p*p=p:= h.self_of_nhds|>.1
 have hf := hF.unique ((hF.mul hF).congr_of_eventuallyEq (h.mono fun _ p'=>(show _=_ from p'.isIdempotentElem).symm))
 -- hf A'=A'*p+p*A'
 have g:p*A'*p=0:=by
   have hu:=congrArg (p*·) hf; rw [mul_add, ←mul_assoc p p, e,←mul_assoc p A'] at hu; exact add_right_cancel (by rw [←hu,zero_add])
 constructor
 · rw [sub_mul,mul_assoc A',e,g,mul_neg,mul_sub,←mul_assoc p A',g,←mul_assoc p p A',e,zero_sub,neg_neg,sub_zero]; exact hf.symm
 rw [mul_sub,←mul_assoc p A',g,←mul_assoc p p A',e,zero_sub,neg_mul,g,neg_zero]
private lemma DX_D (D:Op I):HasDerivAt (DX (x:=x) D) D x:=by
 unfold DX; simpa using (show HasDerivAt _ _ _ from ((hasDerivAt_id' x).sub_const x|>.smul_const D).const_add (1:Op I))
private lemma D0 (D:Op I): DX (x:=x) D x=1:=by simp [DX]
lemma DX_K (D:Op I): HasDerivAt (fun t=> quant (DX (x:=x) D t)) (dg D) x:=by
 let G(t:ℝ):= quant (DX (x:=x) D t); have ht:DifferentiableAt ℝ G x:= quants_c.differentiable (by simp) (DX (x:=x) D x) |>.comp x (DX_D D).differentiableAt
 refine ht.hasDerivAt.congr_deriv (op_columns fun i=>?_)
 let H:= drift_der (by rw [D0,mul_one]; exact DX_D D : HasDerivAt (DX (x:=x) D) (D*DX (x:=x) D x) x) (basisKet i); rw [D0,quant_one,act_one] at H; exact (act_der_const ht.hasDerivAt _).unique H
lemma Lamp_J (h:∀ᶠ i in 𝓝 x,IsStarProjection (F i)) (hF:HasDerivAt F A' x) : HasDerivAt (fun t=>lineOp (F t)) (dg D'* lineOp p-lineOp p*dg D') x:=by
 obtain ⟨U,s,hs⟩:= spot_projection p h.self_of_nhds
 have ts:(p).trace=(s.card:ℂ):=by rw [hs,trace_twist,trace_cut]
 let PH := selector I s.card
 have ht (W : Op I) (l: W.trace=(p).trace): lineOp W=quant W*PH:=by
   unfold lineOp; rw [l,ts]; simp_rw [choose_nat _ _ _ (card_le_univ _),ite_smul,one_smul,zero_smul]; rw [sum_ite_eq]; rw [if_pos (mem_range.mpr (Nat.lt_add_one_of_le (card_le_univ _)))]
 let J(t) :=DX (x:=x) D' t*p*DX (x:=x) (-D') t
 have he:J x=p:=by simp [J,D0]
 have hz:HasDerivAt J A' x:= ((((DX_D D').mul_const p).mul (DX_D (-D'))).congr_deriv (by rw [D0,D0,one_mul,mul_one]; exact (lamp_D h hF).1))
 let H(W:Op I):=quant W*PH
 have dg₁:DifferentiableAt ℝ H p:= ((quants_c.differentiable (by simp: (ω:WithTop ℕ∞)≠0) p).mul_const PH)
 let R(t):=quant (DX (x:=x) D' t); let S(t):=quant (DX (x:=x) (-D') t); have hg(t): H (J t)= R t*lineOp p*S t:=by
   unfold H J; rw [ht p rfl,quant_mul,quant_mul, show quant (DX (x:=x) (-D') t)= S t from rfl,mul_assoc (_*_),selector_quant]; unfold R; simp only [←mul_assoc]; rfl
 have hx :HasDerivAt (fun t=>H (J t)) (dg D'* lineOp p-lineOp p*dg D') x:=by
   simp_rw [hg]
   exact (((DX_K D').mul_const _).mul (show HasDerivAt S _ x from DX_K (-D'))).congr_deriv (by dsimp only [S]; rw [D0,D0,quant_one,one_mul,mul_one,dg_neg,mul_neg]; abel)
 have hl:dg D'* lineOp p-lineOp p*dg D'= fderiv ℝ H p A':= by
    have hw: HasFDerivAt H (fderiv ℝ H p) (J x):=he.symm ▸ dg₁.hasFDerivAt -- ▸ tune
    exact hx.unique (hw.comp_hasDerivAt x hz)
 rw [hl]; apply (dg₁.hasFDerivAt.comp_hasDerivAt x hF).congr_of_eventuallyEq
 have hv:=hF.continuousAt; have he: ∀ᶠ i in 𝓝 x,‖F i-p‖<1:= (hv.eventually (Metric.ball_mem_nhds _ zero_lt_one)).mono fun i (q: dist (F i) (F x) < 1) => by rwa [←dist_eq_norm]
 filter_upwards [he,h] with i e t; exact ht _ (Delta.trace_near t h.self_of_nhds e)
lemma Lamp_k (h:∀ᶠ i in 𝓝 x,IsStarProjection (F i)) (hF: HasDerivAt F A' x): lineOp p*dg D'*lineOp p=0:=by
 have hx:IsStarProjection p:= h.self_of_nhds; let T:= lineOp p
 have hz:HasDerivAt (fun t=> p*DX (x:=x) D' t*p) 0 x:= (((DX_D D').const_mul p).mul_const p).congr_deriv (lamp_D h hF).2
 let L := fun P:Op I=>T*quant P*T; have hp:DifferentiableAt ℝ L (p*DX (x:=x) D' x*p):= ((quants_c.differentiable (by simp)) _ |>.const_mul T).mul_const T
 have he:= hp.hasFDerivAt.comp_hasDerivAt x hz; change HasDerivAt (fun t=> T*quant (p*DX (x:=x) D' t*p)*T) _ x at he; rw [map_zero] at he; simp_rw [quant_mul,←mul_assoc,show T*quant p=T from quant_line hx, mul_assoc (T*_),show quant p*T=T from line_quant hx] at he; exact ((((DX_K D').const_mul T).mul_const T)).unique he
end YM.CF.Fock.Celeb
end
