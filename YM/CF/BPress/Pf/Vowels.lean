import YM.CF.BPress.Pf.Sigil
/-! Aversion to the output patch bra, including occupied test on ℙ. `braC` fixes phase convention from exact occupancy projection. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter NormedSpace Finset Fock Spin Spin.Quad Spin.Cellar Spin.Cellar.Pass
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{P Q A T L C:Op I}{X Y S W:Finset I} {u:ℝ}
def braC (P Q:Finset I)(C:Op I):= acts (occupy P Q) (pairWave C)
lemma bra_ref {x:Wave I}(t:Top A x)(h:Pass (cutM S) (cutM W) L A u)(g:Disjoint S W) : inner ℂ (braC S W C) x=inner ℂ (pairWave C) (acts (quant (slide (cutM S) (cutM W) L A 0)) x):=by rw [Arrival.enter h t g,←act_inner,(cutM_idp (light S W)).isSelfAdjoint]; rfl -- tune

namespace Bit
variable {i:I}
lemma gone (v:Wave I)(h:i∈S) : acts (put i) (acts (occupy S W) v)=0:=by
 suffices H: put i*occupy S W=0 by rw [←act_mul,H,act_zero]
 apply op_columns; intro k; rw [act_mul,cut_basis]; split; next p=> rw [put_act,if_pos ((mem_filter.mp p).2.1 h),act_zero]
 next p=>rw [map_zero,act_zero]
lemma null (v:Wave I)(h:i∈W) : acts (takeF i) (acts (occupy S W) v)=0:=by
 suffices H: takeF i*occupy S W=0 by rw [←act_mul,H,act_zero]
 apply op_columns; intro k; rw [act_mul,cut_basis]; split; next p=> rw [take_act, if_neg (fun t=> disjoint_left.mp (mem_filter.mp p).2.2 t h),act_zero]
 next p=> rw [map_zero,act_zero]
lemma van (i:I)(p:i∉S)(g:i∉W) : put i * occupy S W=occupy S W*put i:=by
 let v(k:Finset I):= basisKet k; have he(k:Finset I):k∈ light S W ↔ insert i k∈light S W:=by
    simp only [light,mem_filter,mem_univ,true_and,disjoint_left, Finset.subset_iff,mem_insert]; -- tune
    constructor; · rintro ⟨a,h⟩; exact ⟨fun t b=> Or.inr (a b),fun x t s=> (t.elim (fun l=>g (l ▸ s)) (fun l=> h l s))⟩ -- implicit binder
    rintro ⟨a,h⟩; exact ⟨fun t s=> (a s).elim (fun h=> (p (h ▸ s)).elim) id,fun t s u=> h (Or.inr s) u⟩
 apply op_columns; intro k; rw [act_mul,act_mul,cut_basis,put_act]; by_cases h:i∈k <;> by_cases t:k∈ light S W
 · rw [if_pos t]; simp [put_act,h]
 · rw [if_neg t]; simp [h]
 · rw [if_pos t]; rw [put_act,if_neg h,map_smul,cut_basis,if_pos ((he k).mp t)]
 rw [if_neg t,if_neg h,map_smul,cut_basis,if_neg (mt (he k).mpr t),smul_zero,map_zero]
lemma van' (p:i∉S)(g:i∉W): takeF i* occupy S W=occupy S W*takeF i:=by have hp:= congrArg star (van i p g); rw [star_mul,star_mul,(cutM_idp (light S W)).isSelfAdjoint] at hp; exact hp.symm
lemma lip {x:Ket I}(h:acts (cutM S) x=0)(p:i∈ S):x.ofLp i=0:=by rw [←if_pos p (t:=x.ofLp i) (e:=0),←cut_apply,h]; rfl -- tune
lemma kill_v {x:Ket I}(p:acts (cutM S) x=x) (v:Wave I) : acts (create x) (acts (occupy S W) v)=0:=by
 rw [create_def,act_sum]; refine sum_eq_zero ?_; intro k _; by_cases h:k∈S; rw [act_smul,gone _ h,smul_zero]; rw [show x.ofLp k=0 from lip (S:=Sᶜ) (by rw [dim_cut,act_sub, p,act_one, sub_self]) (mem_compl.mpr h) ,zero_smul,act_zero]
lemma kill_w {x:Ket I}(p:acts (cutM W) x=x)(v:Wave I) : acts (remove x) (acts (occupy S W) v)=0:=by
 rw [remove_def,act_sum]; refine sum_eq_zero ?_; intro k _; by_cases h:k∈W; rw [act_smul,null _ h,smul_zero]; rw [show x.ofLp k=0 from lip (S:=Wᶜ) (by rw [dim_cut,act_sub,p,act_one,sub_self]) (mem_compl.mpr h),star_zero,zero_smul,act_zero]
lemma cut_real_e (v: Ket I)(P:Finset I): echo (acts (cutM P) v)=acts (cutM P) (echo v):= by rw [echo_s,cut_real]
lemma cut_create {x: Ket I}(p:acts (cutM S) x=0)(g:acts (cutM W) x=0): create x*occupy S W=occupy S W*create x:=by
 rw [create_def,sum_mul,mul_sum]; apply sum_congr rfl; intro i _; by_cases e:i∈S; · simp [lip p e];
 by_cases h:i∈W; · simp [lip g h];
 rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,van _ e h]
lemma cut_ann {x y: Ket I} (p:acts (cutM S) x=0)(g:acts (cutM W) x=0)(t:acts (cutM S) y=0)(w:acts (cutM W) y=0): star (letterV x y) *occupy S W=occupy S W*star (letterV x y):=by
 have he: ∀ (v:Finset I),acts (cutM v) y=0→acts (cutM v) (echo y)=0:=fun v h=>by rw [←cut_real_e,h,echo_zero]
 have ht:= congrArg star (cut_create p g); rw [star_mul,star_mul,(cutM_idp (light S W)).isSelfAdjoint] at ht; rw [letterV,remove,star_add,star_star,add_mul,mul_add, cut_create (he _ t) (he _ w), ht] -- tune
end Bit
lemma annihilation (u v:Ket I)(t: PairBoard (cutM S) (cutM W) L C)(hx:Cᵀ= -C)(e:acts (cutM S) u=0)(w:acts (cutM W) v=0)(s:acts L v=acts (cc C) (acts L u)) : acts (star (letterV u v)) (braC S W C)=0:=by
 let H:=t.toEmpties; let P:=cutM S; let Q:=cutM W; let Z(x:Ket I):= acts L x
 have hU:u= acts Q u+ Z u:= by unfold Q Z; rw [t.l0,act_sub,act_one,act_add,e]; abel
 have hV:v= acts P v+ Z v:= by unfold P Z; rw [t.l0,act_sub,act_one,act_add,w]; abel
 have hL: acts (star (letterV (Z u) (Z v))) (braC S W C)=0:=by
    rw [braC,←act_mul, Bit.cut_ann, act_mul, show Z v=acts (cc C) (Z u) from s,left_ann hx,map_zero]; all_goals rw [show ∀ v:Ket I,Z v=acts L v from fun _=>rfl,←act_mul]; all_goals first | rw [H.PL,act_zero]|rw [H.QL,act_zero]
 nth_rw 1 [hU,hV]; rw [l_add,star_add,act_add,hL,add_zero, letterV,star_add,remove,star_star,act_add]; exact (congrArg₂ (·+·) (Bit.kill_w (W:=W) (by rw [←act_mul,t.q.isIdempotentElem.eq] : acts Q (acts Q u)= acts Q u) _) (Bit.kill_v (S:=S) (show acts P (echo (acts P v))=echo (acts P v) from by rw [←Bit.cut_real_e, ←act_mul,t.p.isIdempotentElem.eq]) _)).trans (zero_add _)
end YM.CF.BPress.Pf
