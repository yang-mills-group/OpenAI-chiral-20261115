import YM.SU5.FiniteGaugeData.Poin.Utopia
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set OS OS.Semigroup MeasureTheory Boundary Probe Mink Mink.General Mink.Lorentz
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {n:ℕ}{H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(Ω:H)(hΩ:∀ x:E4, M S x Ω=Ω)(x:Points n) (A:Fin n→H.Op)(ν:Fin n→ℕ)(L:List (Fin n))
lemma grounded (p:ProofOrder x a L): ContinuousAt (fun x=>meanE S Ω A ν x L) x:=by
 let f(y:Points n)(i: Fin n):E4:= (SEP a (y i)).val; let g(y):= fun i=> optx S (A i) (f y i); let J (y):=rho S ν (clockV a y); let T(y:Points n)(L):=Film (g y) (J y) L
 have hb(L:List (Fin n))(z:ProofOrder x a L): ContinuousAt (fun y:Points n=> T y L Ω) x:=by
    let m:= List.length L; cases L with
    | nil=> exact continuousAt_const
    | cons i L=>
       have hv(V:Points n→H)(c:ContinuousAt V x)(i:Fin n): ContinuousAt (fun y:Points n=> g y i (V y)) x:=by
          let u:Points n→E4:=fun y=> f y i; have hu:Continuous u:= continuous_subtype_val.comp ((SEP a).continuous.comp (by fun_prop)); let w(y:Points n):= A i (M S (-u y) (V y)); have he:ContinuousAt w x:= by have hz:=(step_c S).continuousAt.comp (c.prodMk hu.neg.continuousAt); exact (A i).continuous.continuousAt.comp (show ContinuousAt _ _ from hz)
          have hz:=(step_c S).continuousAt.comp (he.prodMk hu.continuousAt); exact hz
       induction L generalizing i with
       | nil=> exact Eq.mp (congrArg (fun f=> ContinuousAt f x) (show (fun y:Points n=>g y i Ω)=(fun y=> T y [i] Ω) from funext fun t=> (DFunLike.congr_fun (solitary (g t) (J t) i) Ω).symm)) (hv _ continuousAt_const i)
       | cons j L ih=>
          apply hv (fun y=> J y i j (T y (j::L) Ω)) _ i; obtain ⟨w,r⟩:= List.pairwise_cons.mp z; refine ContinuousAt.clm_apply ?_ (ih j r); let f(y:Points n):=(clockV a y j-clockV a y i).toNNReal; have ht:Continuous f:=by unfold f clockV; fun_prop
          let K(y:Points n):= duration (f y); exact (Bokeh S (ν i+ν j) (K x) (dur.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr (w j List.mem_cons_self))))).continuousAt.comp (show ContinuousAt K x from (((Complex.continuous_ofReal.comp continuous_subtype_val).comp ht).continuousAt)) -- identifier duration ambiguous
 exact (innerSL ℂ Ω).continuous.continuousAt.comp (hb L p)
-- Translation on point time prices any axis
abbrev moving (u:E4)(x:Points n):= points fun i=>x i+u
variable (u:E4)
lemma convOrder (u:E4): ProofOrder (moving u x) a L ↔ ProofOrder x a L:=by
 unfold ProofOrder Sau moving clockV; simp -- may not simp within relation.Use congr!
include hΩ

local notation "M0"=>moving u x
lemma dragons (p:ProofOrder x a L): meanE S Ω A ν (moving u x) L= meanE S Ω A ν x L:=by
 let V(y:Points n)(i:Fin n):=(SEP a (y i)).val; let Q:= (SEP a u).val; let F(x):=rho S ν (clockV a x)

 have hu(i:Fin n): V (moving u x) i = Q+ V x i:=by unfold V; rw [moving,points_apply,map_add]; rw [Submodule.coe_add,add_comm]
 have he:F M0= F x:= by funext i j; unfold F rho; congr 1; simp [clockV,moving] -- congr maybe generates
 let B(z:Points n)(i:Fin n):=optx S (A i) (V z i); let K:=F x; let V':=M S Q; let P(X:Points n)(L) := Film (B X) K L Ω; have h(L:List (Fin n))(p:ProofOrder x a L): P M0 L=V' (P x L):=by
    have H(i:Fin n): B M0 i* V'= V'* B x i:=by
       unfold B; rw [hu,←opt_act]; change M S Q*_ * M S (-Q) * V'=_; rw [mul_assoc _ _ V',show M S (-Q)* V'=1 from (tgo S _ Q).trans ((congrArg (M S) (neg_add_cancel _)).trans (tini S)),mul_one]
    cases L with
    | nil=> exact (hΩ Q).symm
    | cons i L=> induction L generalizing i with
       | nil=> simp_rw [P,solitary]; exact (congrArg _ (hΩ Q).symm).trans (DFunLike.congr_fun (H i) Ω)
       | cons j L ih=>
          obtain ⟨v,r⟩:= List.pairwise_cons.mp p; change (B M0 i) (K i j (P M0 (j::L)))= _; rw [ih j r]; let X:= P x (j::L); have hh:Commute (K i j) V':= mslot S Q (duration ((clockV a x j-clockV a x i).toNNReal)) (dur.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr (v j List.mem_cons_self)))) _
          have hz: B M0 i*(K i j*V')= V'*(B x i* K i j):=by rw [hh.eq,← mul_assoc,H,mul_assoc]
          exact DFunLike.congr_fun hz X
 change inner ℂ Ω (Film (B M0) (F M0) L Ω)= inner ℂ Ω (P x L); rw [he,show Film (B M0) (F x) L Ω=_ from h L p]; unfold V'; rw [tboth, hΩ]
#print axioms dragons

end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
