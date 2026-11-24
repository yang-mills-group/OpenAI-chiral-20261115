/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Braid.Lane
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Braid
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics Stationary
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators
open Work.F06
variable {α ξ:Type}[Fintype α][DecidableEq α][Fintype ξ] {σ τ A C : ℝ}{M N r t:ℕ}
private lemma decayms (m : Keys (t+1) ↪ α) : Uniforms _ _ ((stick t).trans m)
    (fun p : Corn α => locus (decaym m) (axes p)) := by
  intro p q H
  have he (i : Fin t) : strands (decaym m) (axes p) i=strands (decaym m) (axes q) i := by
    funext a
    change (p (m (i.succ,a)):ℂ) = ((q (m (i.succ,a)):ℝ):ℂ); congr 1
    apply H
    rintro ⟨b,hb⟩; have hi : (0,b)=(i.succ,a) := m.injective hb; exact (Fin.succ_ne_zero i) (congr_arg Prod.fst hi).symm
  ext w
  change (∀ i (b : Run t), ∑ j : TypeFace 1, symbol 0 (strands _ (axes p) i) j vac * w (update b i j)=0) ↔
    ∀ i (b : Run t), ∑ j : TypeFace 1, symbol 0 (strands _ (axes q) i) j vac * w (update b i j)=0
  simp_rw [he]
section val
variable {m:Phase α→Fin (t+1)→Momentum}{F:CurRun (t+1)→Phase α→ℂ}(i:Keys t↪α)(he:∀ p,Fin.tail (m p)=strands i p)
local notation "Q"=> inlet F (strands i)
include he
lemma turnZ (h:∀ p:Corn α, fromCurl (m (axes p)) (fun x=> F x (axes p))=0): Cycles (fun p=>m p 0) 2 Q ∧ wall (fun p:Corn α=>locus i (axes p)) Q:=by
 constructor
 · intro p; funext b x; have ht:= congr_fun (h p) (Fin.cons b x); rw [fromCurl_cons,he] at ht; simp only [Fin.tail_cons, Fin.cons_zero] at ht; exact ht
 intro p a j b; exact chr (strands i (axes p)) (fun k=> F (Fin.cons a k) (axes p)) j b
-- given cycle lift apply to reduce tail to null, budget pressure on head. separate
lemma transverse (V:SheetLeg α (Run t) 3) (h:0≤ C)(hh:Board M C V)(hu:wall (fun p:Corn α=>locus i (axes p)) V)(hm:∀ p:Corn α, Q (axes p)=cob 2 (fun p=>m p 0) V (axes p)):∃ X: SheetLeg α (CurRun t) 3, Board M (C*mate t M) X ∧ ∀ (a:TypeFace 2)(p:Corn α), (fromCurl (strands i (axes p)) (fun k=> F (Fin.cons a k) (axes p)-stern (fun p=>m p 0) X (Fin.cons a k) (axes p)))=0:=by
 choose X hx hh hX using fun j=>solo t M i C 0 (fun k p=> V p j k) h (fun k=>hh j k) (excited hh j) (fun p=>hu p j)
 let Y:SheetLeg α (CurRun t) 3:=fun p j x=> X j x p
 refine ⟨Y,fun a x=>hx a x,fun a p=>?_⟩; ext1 b
 change ∑ i:CurRun t,_*(_-_) = _; simp_rw [mul_sub, Finset.sum_sub_distrib]
 change Q (axes p) a b-inlet (stern _ Y) (strands i) (axes p) a b=0
 rw [steer, hm, cob,cob]; dsimp only [Y]; simp_rw [hX]; rw [sub_self]
end val
lemma wallS.cheaper (m:Phase α→Fin t→Momentum) {f:CurRun t→Phase α→ℂ}(h:wallS m M r A f)(he:A≤ C)(hp:M ≤ N): wallS m N t C f:=by obtain ⟨X,hx,hP,h⟩:=h; exact ⟨X,hx,fun i=> Board.mono (hP i) he hp,h⟩
def meter(t M:ℕ):ℝ:= (topG 1)^t * puff (M+t) * mate t (M+t)
def rankM: (t M:ℕ)→ℕ
| 0,M=>M
| t+1,M=> M+t+rankM t (1+(M+t))
def rankK: (t M:ℕ)→ℝ
| 0,_=>0
| t+1,M=> meter t M +(1+meter t M*topG 2)*rankK t (1+(M+t))
lemma rank_p(t M:ℕ):0 ≤ rankK t M:=by induction t generalizing M with
 | zero=> exact le_rfl
 | succ t ih=> rw [rankK]; have hm:= ih (1+(M+t)); unfold meter topG mate puff; positivity
lemma rails (m:Keys t↪α)(F:CurRun t→Phase α→ℂ)(h:0≤ A)(hp:∀ i,Pond M A (F i))(hc:∀ p:Corn α,fromCurl (strands m (axes p)) (fun i=> F i (axes p))=0): wallS (strands m) (rankM t M) t (A*rankK t M) F:=by
 induction t generalizing M A with
 | zero=>
    refine ⟨Fin.elim0,fun i=> i.elim0,fun i=> i.elim0,fun p x=>?_⟩; simp only [Finset.univ_eq_empty,sum_empty]; have he:= congr_fun (hc p) default; simpa [fromCurl,Subsingleton.elim x default] using he
 | succ t ih=>
    let U:=strands m; let i:=decaym m; let W:=inlet F (strands i); have ht:∀ p,Fin.tail (U p)=strands i p:=fun _=>rfl
    obtain ⟨hT,hU⟩:=turnZ i ht hc; have he : 0 ≤ A*topG 1^t:=by unfold topG; positivity
    have hW:Board (M+t) (A*topG 1^t) W:=fun j x=>con_s i h (fun a=>F (Fin.cons j a)) (fun k=> hp _) x
    obtain ⟨V,H,hv,hv',hw⟩:= wall_pull ((stick t).trans m) he W hW hT (Or.inl (by norm_num)) (excited hW) (decayms m) hU
    obtain ⟨X,hx,hQ⟩:= transverse (m:=U) (F:=F) i ht V (mul_nonneg he (by positivity)) H hv' hw
    have hx':Board (M+t) (A*meter t M) X:=hx.mono (le_of_eq (by unfold meter puff; ring)) le_rfl; let N:=M+t; let D:=A+A*meter t M * topG 2; have ht:0≤ A*meter t M:=by unfold meter topG puff mate; positivity; 
    have hh:0 ≤ D:= by unfold D; unfold topG; exact add_nonneg h (mul_nonneg ht (by positivity))
    have hP:= cargo ((stick t).trans m) hx' ht
    apply (wallS.cheaper (A:=max (A*meter t M) (D*rankK t (1+N))) _ (growsP X hx' (fun j=> ?_)) ?_ le_rfl)
    · apply max_le
      · rw [rankK,mul_add]; apply le_add_of_nonneg_right; unfold D at hh; have he: 0 ≤ rankK t (1+(M+t)):=rank_p ..; unfold meter topG puff mate; positivity
      unfold D N; rw [rankK,mul_add]; exact le_trans (le_of_eq (by ring)) (le_add_of_nonneg_left ht) -- tune
    apply ih i _ hh _ (fun p=>hQ j p)
    intro k; simp only [stern,Fin.cons_zero,Fin.tail_cons]; exact Pond.rest ((hp (Fin.cons j k)).mono le_rfl (by unfold N; omega : M ≤ 1+N)) (hP j k)
end YM.CF.Braid
