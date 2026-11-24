import YM.CF.Leaf.Wren
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Leaf
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre PowerSeries Vow
open RG
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
variable {ι:Type*}[LinearOrder ι][Fintype ι]{A:Type*}[Fintype A][DecidableEq A]{B:Type*}[AddCommMonoid B]
variable {N:Side}{X Y Z:Aura N}{δ:ℕ}(K:Rinse (Seat N) (Copy N)){Γ: Aura N→ℝ}{M:Orbit N→ Aura N→ FC (Dwell N)}{H:ℝ}{P:BudgetPoint} (T:Pitch P H δ K Γ M)
variable {v₀:ℝ}(hv:1 ≤ H)
variable (E:Aura N→ Copy N)(I:Aura N→ℝ)(pE:∀ X,Span_K P H X (E X) (I X))
variable (x:Orbit N)(z:Rue.FleetS P.threshold x.1)(u:flags P.threshold x.1=∅)
variable {ℓ w' s r a c d e b':ℝ}{v:Aura N→ℝ}(Ψ:Tax_R (V_S (σ_H Γ) I) (σ_H Γ) v b' ℓ w' a c d e)
include z u
lemma lush_K (y:Support (Cube.More N)): pingS P.threshold y x.1:=(Rue.shoreK P.threshold _ z _).mp (by unfold Healthy; simp [u])
include T hv pE Ψ
lemma thorn(X:Aura N): duty_H (Leaf.sailW K E x X):=by
 have hu:0≤I:=fun i=>(pE i).wage (zero_le_one.trans hv); let Q:= (T.dice); let F:= V_S (σ_H Γ) I X; refine Summable.of_nonneg_of_le (fun i=>mul_nonneg (pow_nonneg (by norm_num) i) (norm_nonneg _)) ?_ (Ψ.kite X)
 intro i; refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by norm_num) _); rw [sailW,fP]; exact (era_K K T hv E I pE i X).capF hv x (lush_K x z u _) -- namespace
lemma heat : duty_H (bill_T K E x):=by
 let Q(X:Aura N)(i:ℕ):= (2:ℝ)^i*‖coeff i (sailW K E x X)‖; refine Summable.of_nonneg_of_le (fun i=>mul_nonneg (pow_nonneg (by norm_num) _) (norm_nonneg _)) ?_ (summable_sum (f:=Q) (s:=univ) fun i _=>thorn K T hv E I pE x z u Ψ i) -- tune API
 intro i; rw [bill_T,map_sum]; exact (mul_le_mul_of_nonneg_left (norm_sum_le ..) (by positivity)).trans_eq (by rw [mul_sum])
abbrev bornY(X: Aura N):= lasting P X.val ∅ (fun i=>coeff i (huu_SK K E X))
variable (hp:0≤r)(hμ:r+1≤ℓ-w')
include hp hμ
omit z u
lemma veet: let Q:= bornY K E (P:=P); let V:=hue_SK (σ_H Γ) I; (∀ X:Aura N,Aqua (V X))∧(∀ X:Aura N,Span_K P H X (Q X) (hitU (V X)))∧∀ o:Seat N, nook ((hitU ∘ V)*loom_v r 0 v 0) o ≤ μhcp b' a c d e:=by
 intro Q V; have he(Y):= crispW (σ_H Γ) I Ψ.merits (fun i=>(pE i).wage (zero_le_one.trans hv)) Y
 have hh(X:Aura N): coeff 0 (V X)=0∧∀ i:ℕ,coeff i (derivative ℝ (V X)) ≤ coeff i (ΦD (V_S (σ_H Γ) I) (σ_H Γ) X):=⟨Cadre.tick_r ..,fun i=>by rw [show derivative ℝ (V X)= _ from Cadre.tide ..]⟩
 have hx:=Ψ.born hp hμ V he hh; exact ⟨hx,fun i=>Vow.vaut (fun j=>εlx K T hv E I pE i j) (hx i).of_norm hv,Ψ.toll_V hp hμ V he hh⟩
include z u
-- exact equality on starting measure look from caller **calm global**. arbitrary witness cov. 
lemma hero (WT:Wave (Dwell N)→L[ℂ]Wave ι)(B:FC ι)(w:∀ y: Wave (Dwell N), WT (acts (Qo M x) y)=acts B (WT y))(p:rank2 (Qo M x)) : WT (acts (exp ((∑ X:Aura N,E X x)+(∑ X:Aura N,ξA K X x)+∑ X:Aura N,bornY K E (P:=P) X x)).val (vacuum _))=acts (exp B) (WT (acts (exp (∑ X:Aura N,E X x)).val (vacuum _))):=by
 let F:= bill_T K E x; let L:=sailW K E x; let U:=read_Y F; let G(t):=read_Y (derivative _ F) t; have hx:= heat K T hv E I pE x z u Ψ
 have he(i:ℝ)(p:i∈Set.Icc 0 1): |i|<3/2:=by rw [abs_of_nonneg p.1]; exact lt_of_le_of_lt p.2 (by norm_num)
 let Z:= rock_V WT (Qo M x) B p w U G (fun i q=> (hf_v _ _ (he i q) hx).2) (fun i q=> ride_h (Qo M x) _ hx (break_P K T hv E I pE x z u) _ (he i q))
 have hp0: U 0= ∑ X:Aura N,E X x:=by
    unfold U read_Y F; rw [tsum_eq_single 0]; simp_rw [pow_zero,one_smul, bill_T,map_sum]; refine sum_congr rfl fun Y _=>?_ ; rw [sailW,fP,πU,bud_L,tick_r]; intro i v; rw [zero_pow v,zero_smul]
 have hA(X): Aqua (L X):=by
    let H':=go_p (L X) 1 (by norm_num) (thorn K T hv E I pE x z u Ψ X); simpa only [one_pow,one_smul] using H'
 have hb: U 1= ∑ X:Aura N,hitU (L X):=by unfold U read_Y; simp_rw [one_pow,one_smul]; exact (Aqua.ψ_p univ L (fun i _=>hA i)).2
 let R:= bornY K E (P:=P); have hu(X:Aura N):hitU (L X)=E X x + ξA K X x+ R X x:=by
    let V:=huu_SK K E X; let Y(i):= coeff i V x; have hu(i): coeff i (L X)= (if i=0 then E X x else 0) + (if i=1 then ξA K X x else 0)+Y i:=by
       unfold L sailW; rw [fP,born_p,map_add,map_add,coeff_C,coeff_mk,Pi.add_apply,Pi.add_apply]; split_ifs <;> rfl
    let W(i:ℕ):= if i=0 then E X x else 0; let K'(i:ℕ):= if i=1 then ξA K X x else 0; let H'(i:ℕ):= W i+K' i
    have hv1:Summable W:=summable_of_ne_finset_zero (s:={0}) (fun i v=>if_neg fun h=>v (mem_singleton.mpr h)); have hv2: Summable K':=summable_of_ne_finset_zero (s:={1}) (fun i v=>if_neg fun h=>v (mem_singleton.mpr h)); have hz:Summable H':=hv1.add hv2; have hS:Summable Y:=by refine ((hA X).of_norm.sub hz).congr fun i=>?_ ; rw [hu]; exact add_sub_cancel_left _ _
    have hr:R X x=∑' i,Y i:=if_pos (show visible P X.val ∅ x.1 from hates (lush_K x z u _)); rw [hr,hitU]; simp_rw [hu]; change ∑' i,(H' i+Y i)= _; rw [hz.tsum_add hS,show ∑' i,H' i=_ from hv1.tsum_add hv2,tsum_eq_single 0,tsum_eq_single (f:=K') 1]; simp only [W,K',ite_true]; intro i v; exact if_neg v; intro i v; exact if_neg v
 rw [hb,hp0] at Z; simp_rw [hu,sum_add_distrib] at Z; exact Z
end YM.CF.Leaf
