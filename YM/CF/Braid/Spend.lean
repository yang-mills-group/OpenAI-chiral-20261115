import YM.CF.Braid.Mid
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Braid
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics Stationary
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators
open Work.F06
variable {α ξ:Type}[Fintype α][DecidableEq α][Fintype ξ] {σ τ A C : ℝ}{M N r t:ℕ}
abbrev U2:= CurRun 2→Space 1→ℂ
abbrev V2:= CurRun 2→ℂ
abbrev Paid(M:ℕ)(A:ℝ) (X:U2):=∀ i,Pond M A (X i)
def Fall (F:CurRun (t+1)→Space t→ℂ)(v:Axis→ℝ):= ∀ p:Corn (Keys t),fromCurl (cardR v (axes p)) (fun i=>F i (axes p))=0
lemma zero_p {m:ℕ} (p:Fin m→Momentum):fromCurl p 0=0:=by ext1 b; simp [fromCurl]
lemma add_p {m:ℕ} (p:Fin m→Momentum) (X Y:CurRun m→ℂ): fromCurl p (X+Y)=fromCurl p X+fromCurl p Y:=by ext1; simp [fromCurl, mul_add,sum_add_distrib]
lemma sub_p {m:ℕ} (p:Fin m→Momentum) (X Y:CurRun m→ℂ): fromCurl p (X-Y)=fromCurl p X-fromCurl p Y:=by ext1; simp [fromCurl,mul_sub,sum_sub_distrib]
lemma scal_p {m:ℕ} (p:Fin m→Momentum)(X:CurRun m→ℂ)(r:ℂ):fromCurl p (r • X)=r • fromCurl p X:=by ext1; simp only [fromCurl,Pi.smul_apply, smul_eq_mul,mul_sum]; exact sum_congr rfl fun _ _=> mul_left_comm ..
variable {F U:U2} {s:ℕ}
lemma nilZ: Fall (t:=1) 0 0:= fun p=> zero_p _
lemma Nil_sum{X Y:CurRun (t+1)→Space t→ℂ}{v:Axis→ℝ}(h:Fall X v)(p:Fall Y v):Fall (X+Y) v:=fun i=> (add_p (m:=t+1) (cardR v (axes i)) (fun j=>X j (axes i)) (fun j=> Y j (axes i))).trans (by rw [h i,p i, zero_add])
lemma nilP{r:ℂ}(h: Fall F 0): Fall (r • F) 0:= fun i=> (scal_p _ (fun j=>F j (axes i)) r).trans (by rw [h i,smul_zero])
-- finite module projection
private def roll : U2→ₗ[ℂ] V2:= { toFun:=fun i j=>i j 0,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
def ZeroM: Submodule ℂ U2 where
 carrier := {F | Fall F 0∧ ∃ M A,0≤ A∧ Paid M A F }
 add_mem' := fun {a b} ⟨h,A,C,hC,hx⟩ ⟨p,B,D,hD,hv⟩=>⟨Nil_sum h p,A+B,C+D,add_nonneg hC hD, fun i=> ((hx i).mono le_rfl (Nat.le_add_right ..)).add ((hv i).mono le_rfl (Nat.le_add_left ..))⟩
 smul_mem' c x hx:=by obtain ⟨h,A,C,hC,hp⟩:=hx; exact ⟨nilP h,A,_,mul_nonneg (norm_nonneg c) hC,fun i=> (hp i).scal _⟩
 zero_mem':=⟨nilZ,0,0,le_rfl,fun _=> Pond.zeros⟩
lemma sums {ι:Type}{k:ι→U2}{K:ι→ℝ}{X:Finset ι}(h:∀ i∈X,Paid M (K i) (k i)): Paid M (∑ i∈X, K i) (∑ i∈X,k i):=by
 classical
 induction X using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact fun i=> Pond.zeros
 | @insert i X hx ih=> rw [sum_insert hx,sum_insert hx]; exact fun a=> (h i (by simp) a).add (ih (fun i hi=>h i (by simp [hi])) a)
lemma roller: ∃ (M:ℕ)(K:ℝ),0≤ K∧ ∀ (m:ℕ)(A E:ℝ) (F:U2),0 ≤ A→0≤ E→Fall F 0 → Paid m A F→ (∀ i,‖F i 0‖ ≤ E)→ ∃ Y:U2, Fall Y 0∧ Paid M (E*K) Y∧ ∀ i,Y i 0=F i 0:=by
 classical
 let U:= ZeroM.map roll; let I:= Module.Free.ChooseBasisIndex ℂ U; let b:= Module.Free.chooseBasis ℂ U;
 have hx(i:I):(b i).val∈ U:= (b i).2
 choose x hX hP using hx
 have hp(i):∃ M A, 0≤ A∧ Paid M A (x i):=(show Fall (x i) 0 ∧ _ from hX i).2
 choose m B hb hm using hp
 let C (i:I):= LinearMap.toContinuousLinearMap (b.coord i); let M:=univ.sup m; let K:= ∑ i:I, ‖C i‖ * B i; have hK:0≤ K:=sum_nonneg fun i _=> mul_nonneg (norm_nonneg (C i)) (hb i)
 refine ⟨M,K,hK,fun m' A E f ha he h Hh hf=>?_⟩
 let y: U:=⟨roll f,f,(show f∈ZeroM from ⟨h,m',A,ha,Hh⟩),rfl⟩; let T:=∑ i:I, C i y • x i; have hy:T ∈ZeroM:= ZeroM.sum_mem fun i _=> ZeroM.smul_mem _ (hX i)
 have hv:‖y‖≤ E:=(pi_norm_le_iff_of_nonneg he).mpr hf
 refine ⟨T,(show Fall _ 0 ∧ _ from hy).1,fun i=> ?_,fun i=>?_⟩
 · have ht:= sums (M:=M) (k:=fun i:I=> C i y • x i) (K:=fun i=> ‖C i y‖*B i) (X:=univ) fun i _ j=> ((hm i j).scal (C i y)).mono le_rfl (Finset.le_sup (f:=m) (mem_univ i))
   refine (ht i).mono ?_ le_rfl; apply (sum_le_sum (g:=fun i=>(‖C i‖* E)* B i) fun i _=>mul_le_mul_of_nonneg_right (((C i).le_opNorm _).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg (C i)))) (hb i)).trans; unfold K; rw [mul_sum]; exact sum_le_sum fun i _=> le_of_eq (by ring)
 have he : roll T=y.val:=by unfold T; simp_rw [map_sum,map_smul,hP,← Submodule.coe_smul,←Submodule.coe_sum]; congr 1; exact b.sum_repr y
 exact congr_fun he i
end YM.CF.Braid
