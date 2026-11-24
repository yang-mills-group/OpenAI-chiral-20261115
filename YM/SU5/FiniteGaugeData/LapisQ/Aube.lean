import YM.SU5.FiniteGaugeData.LapisQ.Tanger
set_option autoImplicit false
set_option maxHeartbeats 530000
set_option synthInstance.maxSize 23000
set_option linter.flexible false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.SU5.FiniteGaugeData.LapisQ
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Real
open Lapis Lapis.Motif WithLp
open scoped Topology RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Classical
set_option quotPrecheck false
namespace Apoth
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ι:Type}[Fintype ι] [DecidableEq ι] {a c x' x y v:ℝ} {C:ℝ}
variable (A B:ι→E)
def Dun (x y:ℝ):Prop:= (∀ i j,inner ℝ (A i) (A j)=if i=j then x else 0) ∧ (∀ i j,inner ℝ (B i) (B j)=if i=j then x else 0)∧ (∀ i j,inner ℝ (A i) (B j)= if i=j then y else 0)
def ether (b:Bool×ι):=if b.1 then A b.2+B b.2 else A b.2-B b.2
private lemma lore (p:Dun A B x y): sepOpt (ether A B):=by
 have hr(i j):inner ℝ (B i) (A j)=if i=j then y else 0:=by rw [real_inner_comm,p.2.2]; simp only [eq_comm]
 intro i j h; rcases i with ⟨a,i⟩; rcases j with ⟨b,j⟩; cases a <;> cases b <;> by_cases v:i=j <;> simp_all only [Prod.mk.injEq,and_self, Bool.false_eq_true,true_and,false_and,not_true_eq_false,IsEmpty.forall_iff, ether, inner_add_left,inner_add_right,inner_sub_right,inner_sub_left,↓reduceIte,p.1,p.2.1,p.2.2,hr] <;> first | (exfalso; exact h rfl) | ring -- tune infinite simp.All
lemma spring (p:Dun A B x y)(i:Bool×ι): ‖ether A B i‖^2=if i.1 then 2*(x+y) else 2*(x-y):=by
 rcases i with ⟨a,i⟩; cases a <;> simp_rw [←real_inner_self_eq_norm_sq,ether]; · simp only [Bool.false_eq_true,↓reduceIte,inner_sub_left,inner_sub_right,p.2.2,p.1,p.2.1,show inner ℝ (B i) (A i)=y from (real_inner_comm ..).trans ((p.2.2 ..).trans (if_pos rfl))]; ring -- orientation `real_inner_comm` maybe swaps def order
 simp only [if_true,inner_add_left,inner_add_right,p.2.2,p.1,p.2.1,show inner ℝ (B i) (A i)=y from (real_inner_comm ..).trans ((p.2.2 ..).trans (if_pos rfl))]; ring
section nonempty
variable [Nonempty ι]
include A B
lemma valNon (p:Dun A B x y) : |y|≤ x :=by
 let i:= Classical.arbitrary ι; have h1:=sq_nonneg ‖ether A B (true,i)‖; have h2:=sq_nonneg ‖ether A B (false,i)‖; rw [spring A B p,if_pos rfl] at h1; rw [spring A B p,if_neg (by simp)] at h2; refine abs_le.mpr ⟨?_,?_⟩ <;> linarith
end nonempty
noncomputable abbrev mentor {E:Type*}[SeminormedAddGroup E] (x:E):ℝ:= Real.exp (-‖x‖^2/2)
lemma pollen_a {E:Type*}[SeminormedAddGroup E] (x:E):0 ≤ mentor x∧ mentor x ≤ 1:=⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num))⟩
lemma cello(x y:E): mentor x*mentor y= Real.exp (-(‖x‖^2+‖y‖^2)/2):=by unfold mentor; rw [←Real.exp_add]; ring_nf
lemma cell_j (x:E): mentor (opus A x)*mentor (opus B x)=∏ i:Bool×ι, coatF (inner ℝ (ether A B i) x):=by
 rw [cello,Fintype.prod_prod_type]; unfold coatF; simp_rw [←Real.exp_sum]; congr 2 -- tune
 rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fintype.sum_bool]; change -((∑ i,(inner ℝ (A i) x)^2)+ ∑ i,(inner ℝ (B i) x)^2)/_= _; rw [←sum_add_distrib,←sum_neg_distrib,sum_div, ←sum_add_distrib]; -- tune rw orientation `←`
 apply sum_congr rfl; intro i _; simp [ether,inner_add_left,inner_sub_left]; ring
noncomputable def sheet (x y:ℝ)(k:ℕ):ℝ:= (peso (2*(x+y))* peso (2*(x-y)))^k
lemma canon (p:Dun A B x y): (∫ z:E,mentor (opus A z)*mentor (opus B z) ∂stdGaussian E)= sheet x y (Fintype.card ι) :=by
 simp_rw [cell_j, probate (ether A B) (lore A B p), spring A B p]; rw [Fintype.prod_prod_type,Fintype.prod_bool]; unfold sheet; simp only [prod_const,card_univ,Bool.false_eq_true,↓reduceIte]; ring
variable {k:ℕ}
lemma flesh(h: |y| ≤ x) : sheet x y k= ((Real.sqrt ((1+x)^2-y^2))⁻¹)^k:=by
 have hy:0<1+x+y:=by linarith only [(abs_le.mp h).1]
 have hx:0<1+x-y:=by linarith only [(abs_le.mp h).2]; -- h yields -x≤y & y≤x
 unfold sheet peso; congr 1; rw [show (1+x)^2-y^2=(1+x-y)*(1+x+y) from (by ring),Real.sqrt_mul hx.le,_root_.mul_inv_rev, show 1+2*(x+y)/2=1+x+y from (by ring),show 1+2*(x-y)/2=1+x-y from (by ring)]
private lemma real_h(h:|y|≤x): 0 < (1+x)^2-y^2:=by
 rw [show (1+x)^2-y^2=(1+x-y)*(1+x+y) from (by ring)]; refine mul_pos ?_ ?_<;> linarith only [(abs_le.mp h).1,(abs_le.mp h).2]
private lemma bigger (h:|y|≤x)(t:|v|≤x)(d:v^2<y^2)(u:0<k): sheet x v k<sheet x y k:=by
 rw [flesh t,flesh h]; refine pow_lt_pow_left₀ (inv_lt_inv₀ (Real.sqrt_pos.mpr ?_) (Real.sqrt_pos.mpr ?_) |>.mpr ?_) (by positivity) u.ne'; all_goals try apply real_h <;> assumption
 exact Real.sqrt_lt_sqrt (real_h h).le (sub_lt_sub_left d _)
private def debt (i:ℕ)(x:ℝ×ℝ×ℝ):= sheet x.1 x.2.1 i-sheet x.1 x.2.2 i
private def Reserve (C a:ℝ) : Set (ℝ×ℝ×ℝ):= {p| p.1≤ C∧|p.2.1|≤ p.1∧|p.2.2| ≤ p.1∧ p.2.2^2+a≤ p.2.1^2}
lemma sonic_gap (h:0<a)(p:0<k)(C:ℝ):∃ y:ℝ,0<y ∧∀ x z z':ℝ,x≤C→ |z|≤x → |z'|≤x → z'^2+a≤z^2→ y ≤ sheet x z k - sheet x z' k :=by
 let S:= Reserve C a; by_cases u:Set.Nonempty S; swap; · exact ⟨1,zero_lt_one,fun x z y e i j v=> (u ⟨(x,z,y),e,i,j,v⟩).elim⟩
 let T:=Set.Icc (0:ℝ) C; let Q:= Set.Icc (-C) C; have ht:IsCompact (T ×ˢ (Q ×ˢ Q)):= isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc) -- `×ˢ` syntax finset
 have hs:IsClosed S:=by
    refine (isClosed_le (show Continuous (Prod.fst : ℝ×ℝ×ℝ→_) from continuous_fst) continuous_const).inter ((isClosed_le (f:=fun x:ℝ×ℝ×ℝ=>|x.2.1|) (g:=fun x=>x.1) (by fun_prop) continuous_fst).inter ((isClosed_le (f:=fun x:ℝ×ℝ×ℝ=>|x.2.2|) (g:=fun x=>x.1) (by fun_prop) continuous_fst).inter (isClosed_le (f:=fun x:ℝ×ℝ×ℝ=>x.2.2^2+a) (g:=fun x=>x.2.1^2) (by fun_prop) (by fun_prop)))) -- Def.Property eq check.C.V.
 have hx:IsCompact S:= ht.of_isClosed_subset hs (fun x p=> ⟨⟨le_trans (abs_nonneg x.2.1) p.2.1,p.1⟩, ⟨abs_le.mp (p.2.1.trans p.1),abs_le.mp (p.2.2.1.trans p.1)⟩⟩)
 have hv(x) (p':x∈S):0<debt k x:=sub_pos.mpr (bigger p'.2.1 p'.2.2.1 (by linarith only [h,(show x.2.2^2+a≤ x.2.1^2 from p'.2.2.2)]) p)
 have he: ContinuousOn (debt k) S:=by
    let f(x:ℝ)(y:ℝ):= ((Real.sqrt ((1+x)^2-y^2))⁻¹)^k
    have hg(p:ℝ×ℝ×ℝ)(y:ℝ×ℝ×ℝ→ℝ)(t:Continuous y)(h:|y p|≤p.1): ContinuousAt (fun x:ℝ×ℝ×ℝ=> f x.1 (y x)) p:=((show Continuous (fun x:ℝ×ℝ×ℝ=> Real.sqrt ((1+x.1)^2-(y x)^2)) from (by fun_prop)).continuousAt.inv₀ (Real.sqrt_pos.mpr (real_h h)).ne').pow k
    let v(x:ℝ×ℝ×ℝ):= f x.1 x.2.1-f x.1 x.2.2; refine ContinuousOn.congr (g:=debt k) (f:=v) (fun x p=>((hg x _ (continuous_fst.comp continuous_snd) p.2.1).sub (hg x _ (continuous_snd.comp continuous_snd) p.2.2.1)).continuousWithinAt) ?_ -- unfold v
    intro i p; unfold debt v f; rw [flesh p.2.1,flesh p.2.2.1]
 obtain ⟨x,t,y⟩:= hx.exists_isMinOn u he; exact ⟨debt k x,hv x t, fun x z v' u h p q=> y (show (x,z,v')∈S from ⟨u,h,p,q⟩)⟩
end Apoth
end YM.SU5.FiniteGaugeData.LapisQ
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Apoth.valNon
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Apoth.canon
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Apoth.sonic_gap
