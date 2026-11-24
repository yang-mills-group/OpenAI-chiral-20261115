import YM.CF.BProof.Crystal.Focus
/-! B-rootK price with spare exp. Smallness used only at final log extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Crystal
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Sprinkle Lattice Tenant Palot Gas Branch RG Push.AbsoluteSums
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {V I: Type}[DecidableEq V][Fintype V][Fintype I][LinearOrder I]{P:Dew V I}
variable {N:Side}{f:I→I→Support N→ℝ}
lemma tollPrice(B: V→Support N){v:V→ℝ}(x:∀ i,0 ≤ v i)(a C:ℝ) : Moment.Toll B v a C ↔ ∀ i:Site N,bill_X B v a i≤ C:=by
 have hx(i:Site N): (∑ j:V,Moment.hit B v a i j)=bill_X B v a i:=by unfold bill_X; rw [sum_filter]; apply sum_congr rfl; intro j _; unfold Moment.hit; split; rw [mul_comm]; rfl; rfl -- tune
 constructor; · intro g i; rw [← hx]; exact budget_sum (g.pays i) univ
 intro g; refine ⟨x,fun i=>budget_finite ?_ ((hx i).trans_le (g i))⟩; intro j; unfold Moment.hit; split; exact mul_nonneg (Real.exp_pos _).le (x _); rfl
namespace Civic
variable {p:Civic N P}{a α H:ℝ}{w:V→ℝ}(z:Bright p f a H)(x:∀ i,0 ≤ w i)
abbrev scape(i:Deco P N):=∏ j:P.Slots i.1, light f a j.val (i.2 j) -- tune implicit a f unused params? elaborates
include z x
lemma oneD {o:Site N}{i:Deco P N}(e:o∈(p.border i).val)(h:α ≤ a/2)(g:0≤α):
 expense w f i*rent α (p.border i).val ≤ (∑ y∈ (p.zone i.1).val,puff (a/2) o y)*(w i.1*rent α (p.zone i.1).val*scape (f:=f) (a:=a) i):=by
 let E:=expense w f i; let B:=(p.zone i.1).val; let L:= Real.exp (a*countB i); have ht: w i.1 * scape (a:=a) (f:=f) i=E*L:=by
   unfold scape E expense light L countB rent; rw [prod_mul_distrib,←Real.exp_sum, ←mul_sum,mul_assoc]
 rw [mul_right_comm (w i.1),ht]; by_cases t:E=0; · change E*_ ≤ _; rw [t,zero_mul,zero_mul,zero_mul,mul_zero]
 -- location pays
 obtain ⟨y,v,u⟩:= origin_port z i t o e; have hf:(puff (a/2) o y)* (E*L*rent α B)≥ E*rent α (p.border i).val:=by
   rw [show puff (a/2) o y*(E*L*rent α B)= E*(puff (a/2) o y*L*rent α B) from (by ring)]; apply mul_le_mul_of_nonneg_left _ (meter z x i); unfold rent L puff; simp_rw [←Real.exp_add]; apply Real.exp_monotone; let k:=countB i; have hw:=p.border_pay i; have hh: 0≤k:= (Nat.cast_nonneg _).trans u; have ha:0≤a:=by linarith
   nlinarith [mul_le_mul_of_nonneg_left hw g,mul_le_mul_of_nonneg_left u ha,mul_le_mul_of_nonneg_right h hh]
 refine hf.trans (mul_le_mul_of_nonneg_right (single_le_sum (fun x _=>?_ ) v) (mul_nonneg (mul_nonneg (meter z x i) (Real.exp_pos _).le) (rent_pos ..).le)); exact (Real.exp_pos _).le
lemma manyD (C:ℝ)(c:0≤C)(he:Moment.Toll (fun i=>(p.zone i).val) (costW P w H) α C)(h:α≤a/2)(g:0<α): Moment.Toll (fun i=>(p.border i).val) (expense w f) α (puffPrice (a/2)*C):=by
 apply (tollPrice _ (meter z x) _ _).mpr; intro i
 let T(v:Deco P N):= p.border v; let Q(v):=(p.zone v).val; let W(v):=w v*rent α (Q v); let G(v):=∑ y∈Q v,puff (a/2) i y
 have hp(v:V):0≤W v:=mul_nonneg (x v) (rent_pos ..).le; have hz(v:V) : 0 ≤ G v:=sum_nonneg (fun x _=>(Real.exp_pos _).le); have hf(j:I)(i:Prism I N):0≤light f a j i:=mul_nonneg (weightPositive z ..) (rent_pos ..).le; let R(y:Deco P N):=scape (a:=a) (f:=f) y; have hQ(y:Deco P N):0≤R y:=prod_nonneg (fun i _=> hf ..)
 have hh(v:V): (∑ j:P.Lease v (Support N), R ⟨v,j⟩)≤H^(P.line v).length:=by
   change (∑ j:(∀ z:P.Slots v,Prism I N),∏ t:P.Slots v,light f a t.val (j t))≤_; rw [←Fintype.prod_sum (fun (t:P.Slots v) j=>light f a t.val (j:Prism I N))]; refine le_trans (prod_le_prod (g:=fun _=>H) (fun t _=>sum_nonneg fun x _=> hf ..) (fun t _=> totalLight z _)) ?_; rw [prod_const,card_univ,show Fintype.card (P.Slots v)=(P.line v).length from (Fintype.card_coe _).trans (List.toFinset_card_of_nodup (P.fresh _))]
 have ht(y:Site N): ∑ v:V,(if y∈Q v then W v*H^(P.line v).length else 0) ≤ C:=by
   have he:=budget_sum (he.pays y) univ; apply Eq.trans_le _ he; apply sum_congr rfl; intro v _; unfold Moment.hit; dsimp only; by_cases k:y∈Q v; rw [if_pos k,if_pos k]; unfold W Q costW rent; ring; rw [if_neg k,if_neg k]
 unfold bill_X; rw [sum_filter]; apply le_trans (b:=∑ v:Deco P N, G v.1* (W v.1 * R v)) (sum_le_sum (fun v _=>?_)) ?_; swap; · split; exact oneD z x ‹_› h g.le; exact mul_nonneg (hz _) (mul_nonneg (hp _) (hQ _)) -- tune goal order
 unfold Deco Dew.Box; rw [Fintype.sum_sigma]; simp_rw [←mul_sum]; refine le_trans (sum_le_sum (g:=fun v=> G v*(W v * H^(P.line v).length)) (fun v _=>mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hh v) (hp _)) (hz _))) ?_
 have hX(v): G v*(W v*H^(P.line v).length) = ∑ y:Site N,puff (a/2) i y*(if y∈Q v then W v*H^(P.line v).length else 0):=by unfold G; rw [sum_mul,← inter_univ (Q v),inter_comm,← filter_mem_eq_inter, sum_filter]; simp only [mul_ite,mul_zero, mem_filter, mem_univ,true_and] -- tune
 simp_rw [hX]; rw [sum_comm]; simp_rw [←mul_sum]; apply le_trans (sum_le_sum (g:=fun v=>puff (a/2) i v*C) (fun v _=> mul_le_mul_of_nonneg_left (ht _) (Real.exp_pos _).le)); rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (puff_price (a/2) (lt_of_lt_of_le g h) i) c
variable {A:V→ℂ}{F:I→I→Support N→ℂ}
lemma truthAlpha (e:∀ i,‖A i‖≤w i)(u:∀ i j Y,i<j→ ‖F i j Y‖≤f i j Y)(S:Finset (Deco P N)):
 ‖P.quartet A F S‖≤ ∏ i∈S, expense w f i:=by
 unfold Dew.quartet; split; swap; · rw [norm_zero]; exact prod_nonneg (fun i _=>meter z x i)
 unfold Dew.quint; rw [norm_mul,norm_prod]; apply (mul_le_of_le_one_right _ (P.notch_pay ..)).trans; apply prod_le_prod (fun i _=> norm_nonneg _); · intro i _; unfold expense Dew.litmus; rw [norm_mul]; apply mul_le_mul (e _) _ (norm_nonneg _) (x _); unfold Dew.flareC; rw [norm_prod]; apply prod_le_prod (fun i _=>norm_nonneg _); intro j _; unfold Dew.charge weight; cases (i.2 j); simp; dsimp only [Option.elim_some]; split; exact u _ _ _ ‹_›; rw [norm_zero]
 exact prod_nonneg (fun i _=> norm_nonneg _)
omit x in
lemma zCode(u:∀ i j Y,i<j→ ‖F i j Y‖≤f i j Y): p.Code F:= by intro i j S t v; exact (z.lit _ _ _ t ((lt_of_lt_of_le (norm_pos_iff.mpr v) (u i j S t)).ne')).2
end Civic
end YM.CF.BProof.Crystal
