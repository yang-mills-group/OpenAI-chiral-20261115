import YM.SU5.Selected.Dais.Ange
import YM.CF.Fock.Rows
/-! Tilt cost on arbitrary number-operator sectors; don't pay on Fock complement after norm. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Dais.Parity
open Function Filter Metric Finset Fock Lat Matrix MeasureTheory
open Pannier.Chancel (Letter Marque)
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators ContDiff InnerProductSpace ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I][Nonempty I] {P:Op I}{S T: Finset I}{M W:Wave I}{v t:ℝ}{x:FC I}{j k:ℕ}
-- H_s
 def Hlow (S:Finset I)(k:ℕ)(x:Wave I): Prop:=∀ t: Finset I,k<(t\S).card → x.ofLp t=0
lemma Hlow.scale(p:Hlow S k W)(z:ℂ):Hlow S k (z • W):=fun i v=>by simp [p i v]
lemma Hlow.add (p:Hlow S k W) (q:Hlow S k M):Hlow S k (W+M):=fun i v=>by simp [p i v,q i v]
lemma Hlow.sub (p:Hlow S k W)(q:Hlow S k M):Hlow S k (W-M):= by rw [sub_eq_add_neg, ← neg_one_smul ℂ M]; exact p.add (q.scale (-1)) -- ambiguity
lemma Hlow.mono(p:Hlow S k W)(u:k≤j): Hlow S j W:=fun i v=>p i (u.trans_lt v)
lemma sum_hlow {X:Type*}(T:Finset X)(f:X→Wave I)(p:∀ i∈T,Hlow S k (f i)): Hlow S k (∑ i∈T,f i):=by intro i v; rw [WithLp.ofLp_sum,Finset.sum_apply,sum_eq_zero fun x u=>p x u i v]
lemma Hlow.put (p:Hlow S k W)(i:I): Hlow S (k+1) (acts (put i) W):=by
 intro t h; rw [put_row]; split
 next v=>
    rw [p,mul_zero]; have he: t\S ⊆ insert i (t.erase i\ S):=by
       intro j ht; obtain ⟨ht,u⟩:= mem_sdiff.mp ht; by_cases e:i=j; · simp [e]
       exact mem_insert_of_mem (mem_sdiff.mpr ⟨mem_erase.mpr ⟨Ne.symm e,ht⟩,u⟩)
    have hv:=(card_le_card he).trans (card_insert_le ..); omega

 rfl
lemma Hlow.takes (p:Hlow S k W)(i:I): Hlow S (k+1) (acts (takeF i) W):=by
 intro t h; rw [take_row]; split; rfl; rw [p,mul_zero]; apply lt_of_lt_of_le (b:=(t\S).card) (by omega); exact card_le_card (sdiff_subset_sdiff (subset_insert ..) le_rfl)
lemma Hlow.entry (p:Hlow S k W)(b:Bool)(x:Ket I): Hlow S (k+1) (acts (creed b x) W):=by
 unfold creed; split
 next=> rw [remove_def,act_sum]; refine sum_hlow _ _ fun i _=>?_ ; rw [act_smul]; exact (p.takes _).scale _
 next=> rw [create_def,act_sum]; refine sum_hlow _ _ fun i _=>?_ ; rw [act_smul]; exact (p.put _).scale _
-- robust guaranteed Sector
abbrev driftW (x:Op I)(v:Wave I):= acts (quant x) v
def Access (P:Op I)(k:ℕ)(v:Wave I):Prop:= ∀ (U:UNI I)(S:Finset I),P=twist U (cutM S)→ Hlow S k (acts (quantU (star U)).val v)
lemma access_unit (p:Sea P W): Access P 0 W:=by
 intro U S h; let K:=quantU (star U); let V:=acts K.val W; have hp:acts (lineOp (cutM S)) V=V:=by
    let F:=lineOp P; have he:lineOp (cutM S)=twist K F:=by unfold F; rw [h,line_twist]; unfold K; rw [quantU_star, twist_inv ..] -- tune
    rw [he]; exact (swivel K F W).symm.trans (congrArg (acts K.val) p.1)
 intro t g; change V.ofLp t= _; nth_rw 1 [← hp]; rw [cutLine,cut_apply,if_neg]; simp only [mem_singleton]; rintro rfl; simp at g
lemma Access.mono(p:Access P k W)(h:k≤j): Access P j W := fun u s e=>(p u s e).mono h
lemma entry_spend(p:Access P k W)(b:Bool)(x:Ket I):Access P (k+1) (acts (creed b x) W):=by
 intro U S u; let K:=quantU (star U); let V:=acts K.val W; rw [swivel,show twist K (creed b x)=creed b (acts (star U).val x) from ?_]; exact (p U S u).entry _ _; cases b; exact twist_create ..; exact twist_remove .. -- tune
lemma access_letter (p:Access P k W)(u: Pannier.Chancel.Letter x):Access P (k+1) (acts x W):=by obtain ⟨b,v,rfl⟩:= u; exact entry_spend p b v
lemma Access.add(p:Access P k W)(u:Access P k M): Access P k (W+M):=fun i s e=> by rw [map_add]; exact (p i s e).add (u i s e)
lemma Access.sub(p:Access P k W)(u:Access P k M): Access P k (W-M):=fun i s e=> by rw [map_sub]; exact (p i s e).sub (u i s e)
lemma Access.scale (p:Access P k W)(c:ℂ): Access P k (c • W):=fun i s e=>by rw [map_smul]; exact (p i s e).scale c
-- exact strength from tilt on lower space
lemma tickF(S: Finset I)(t:ℝ): quant (cards (cutM S) t)= Matrix.diagonal (fun s=> (t:ℂ)^(s \ S).card):=by
 let f(i:I):ℂ:= if i∈ S then 1 else t; have hp:cards (cutM S) t=Matrix.diagonal f:=by
    ext i j; rcases eq_or_ne i j with rfl|h; · by_cases p:i∈ S<;>simp [cards,cutM,f,p,Complex.real_smul]
    simp [cards,cutM,f,h, Matrix.diagonal_apply,Matrix.one_apply]
 rw [hp,quant_diag]; congr 1; funext v; rw [←prod_sdiff (s₁:=v∩ S) (s₂:=v) inter_subset_left]; -- tune
 rw [show v\ (v∩S)=v \ S from (by ext; simp)]; rw [prod_congr rfl (f:=f) (g:=fun _=> (t:ℂ)) (fun i p=>if_neg (mem_sdiff.mp p).2), prod_eq_one (s:=v∩S) (fun i u=>if_pos (mem_inter.mp u).2),prod_const,_root_.mul_one]
lemma Hlow.boundK (p:Hlow S k W)(e:1≤ t) : ‖driftW (cards (cutM S) t) W‖ ≤ t^k * ‖W‖:=by
 unfold driftW; rw [tickF]; apply (sq_le_sq₀ (norm_nonneg _) (by have hp:=zero_lt_one.trans_le e; positivity)).mp; rw [EuclideanSpace.norm_sq_eq,mul_pow,EuclideanSpace.norm_sq_eq,Finset.mul_sum]; apply sum_le_sum; intro i _; rw [Fock.diag_apply, norm_mul,mul_pow, norm_pow,Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans e)]
 by_cases h:k<(i\ S).card; · rw [p i h]; simp
 gcongr; exact not_lt.mp h
lemma Access.cost (p:Access P k W)(u:IsStarProjection P)(e:1≤ t): ‖driftW (cards P t) W‖ ≤ t^k * ‖W‖:=by
 obtain ⟨U,S,h⟩:=spot_projection P u; let K:=quantU (star U); let Q:=cards P t; have hg:twist K (quant Q)=quant (cards (cutM S) t):=by unfold Q; rw [h,←card_twist,quant_twist]; unfold K; rw [quantU_star,twist_inv];
 unfold driftW; rw [← act_unit_norm K (acts (quant (cards P t)) W), swivel K, hg, ← act_unit_norm K W]; exact (p U S h).boundK e -- tune occurrence
lemma income (p:Access P k W)(u:IsStarProjection P) (h:0<t)(f:t≤1):
 ‖inner ℂ M W‖ ≤ ‖driftW (cards P t) M‖ * (t⁻¹^k*‖W‖):=by
 let q(t:ℝ):=quant (cards P t); have hp: inner ℂ M W= inner ℂ (acts (q t) M) (acts (q t⁻¹) W):=by
    have he:star (q t)=q t:=by unfold q; rw [←quant_star,pal_r t u];
    have hh:q t * q t⁻¹=1:=by unfold q; rw [←quant_mul,card_spend u,mul_inv_cancel₀ h.ne',simple,quant_one];
    have hx:= act_inner (star (q t)) M (acts (q t⁻¹) W); rw [star_star,he, ←act_mul,hh,act_one] at hx; exact hx.symm
 rw [hp]; apply (norm_inner_le_norm ..).trans; exact mul_le_mul_of_nonneg_left (p.cost u (one_le_inv₀ h |>.2 f)) (norm_nonneg _)
end YM.CF.Dais.Parity
#print axioms YM.CF.Dais.Parity.access_letter
#print axioms YM.CF.Dais.Parity.income
