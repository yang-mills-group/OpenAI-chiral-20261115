import YM.CF.Buffered.Ping

/-! tuple cycle comparison to `Kern.τ`. `Measure.count` factors live inside μ here. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Stack
open Function Filter Lattice RG Finset MeasureTheory Push.SectorMeasure
open scoped BigOperators ENNReal Topology InnerProductSpace ComplexOrder
variable {X:Type*} [MeasurableSpace X] {μ:Measure X}[IsFiniteMeasure μ]

namespace Kern
-- branch tail recursion on kernel product with final point appended
def seqmul (K : ℕ→Kern μ) (k:ℕ) : Kern μ := match k with
 | 0 => K 0
 | k+1 => K 0 * seqmul (fun i=>K (i+1)) k
def roll (K : ℕ→Kern μ) (n:ℕ) := seqmul K (n-1)
lemma roll_one (K : ℕ→Kern μ) : roll K 1 = K 0 := rfl
lemma roll_next (K : ℕ→Kern μ) {n:ℕ}(h:0 < n) : roll K (n+1) = K 0*roll (fun i=> K (i+1)) n := by
 rcases n with _|n; · omega
 rfl
lemma roll_congr (F G : ℕ→Kern μ) {n:ℕ} (v:0 < n) (h:∀ j<n,F j=G j): roll F n=roll G n:=by
 induction n,v using Nat.le_induction generalizing F G with
 | base=> exact h _ (by decide:0 < 1)
 | succ n v ih=> rw [roll_next F v,roll_next G v,h 0 (by omega),ih _ (fun i=> G (i+1)) (fun i t=> h (i+1) (by omega))]
lemma roll_chain (K : ℕ→Kern μ){F:Kern μ}{n:ℕ}(t:0 < n)(h:∀ i<n,K i=if i%2=0 then F else star F): roll K n=F.chain n := by
 induction n,t using Nat.le_induction generalizing K F with
 | base => rw [chain_one,roll_one, h 0 Nat.one_pos,if_pos (by decide)]
 | succ n u ih =>
   rw [roll_next K u, h 0 (Nat.succ_pos n), if_pos (by decide), chain_succ _ u, ih (fun i=> K (i+1)) (F:=star F) (fun i t=> by rw [h _ (by omega)]; split_ifs <;> first| rfl| omega| simp only [star_star])]
end Kern


abbrev Many (n:ℕ) (X:Type*) := Fin n → X
abbrev piN (n:ℕ)(μ:Measure X) := Measure.pi fun i:Fin n => μ
lemma pi_succ (n:ℕ)(F : Many (n+1) X→ℂ) : (∫ x,F x∂piN (n+1) μ)=∫ x:X×Many n X, F (Fin.cons x.1 x.2)∂μ.prod (piN n μ) := by
 rw [←((measurePreserving_piFinSuccAbove (fun _:Fin (n+1)=> μ) 0).symm).integral_comp']; simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero] -- check
lemma product_env {I : Type*} (F:I→X→ℂ) (s: Finset I) (h : ∀ i∈s,Envelope (F i)) : Envelope (fun x=> ∏ i∈s,F i x) := by
 classical
 induction s using Finset.induction_on with
 | empty=> simp only [prod_empty]; exact Girt.rite_c _
 | insert i s h' ih => simp_rw [prod_insert h']; exact env_mult (h i (mem_insert_self ..)) (ih fun j u=>h j (mem_insert_of_mem u))
lemma measurable_pre (n:ℕ) : Measurable (fun p:X×Many n X=> Fin.cons p.1 p.2 : X×Many n X → Many (n+1) X) := by
 apply measurable_pi_lambda; intro i; induction i using Fin.cases <;> simp <;> fun_prop
section lines
variable (K:ℕ→Kern μ)
def route (n:ℕ) (p:Many (n+1) X) (y:X) := ∏ i:Fin (n+1), K i.val (p i,Fin.snoc (α:=fun _=>X) p y i.succ)
lemma route_env (n:ℕ) (y:X): Envelope (fun p => route K n p y) := by
 unfold route; apply product_env
 intro i _; apply Env.along (K i.val).paid
 apply measurable_pi_apply (a:=i) |>.prodMk
 generalize hi:i.succ=v; induction v using Fin.lastCases with
 | last=> simp
 | cast j=> simp <;> fun_prop
lemma route_cons (n : ℕ) (p:Many (n+1) X) (x y:X) : route K (n+1) (Fin.cons x p) y = K 0 (x,p 0)* route (fun i=>K (i+1)) n p y:=by
 unfold route; rw [Fin.prod_univ_succ, Fin.cons_zero]; congr 1
 · rw [←Fin.cons_snoc_eq_snoc_cons]; simp
lemma route_head (n : ℕ) (x y:X): (∫ p:Many n X, route K n (Fin.cons x p) y∂piN n μ) = (Kern.seqmul K n) (x,y):=by
 induction n generalizing K x y with
 | zero=> simp [piN,route,Kern.seqmul]
          simp_rw [show (1:Fin 2)=Fin.last 1 from rfl, Fin.snoc_last]; simp [measureReal_def]
 | succ n ih=>
   rw [pi_succ,integral_prod]; swap; · exact Env.integrableX (Env.along (g:=fun i:X×Many n X=> Fin.cons (α:=fun _=>X) (n:=n+1) x (Fin.cons i.1 i.2)) (route_env K (n+1) y) ((measurable_pre _).comp (measurable_const.prodMk (measurable_pre n)))) _
   simp_rw [route_cons,Fin.cons_zero, integral_const_mul]; rw [Kern.seqmul,Kern.mul_at]; simp_rw [ih]
variable {K} {k:ℕ}
def cyclic (K : ℕ→ Kern μ) (n:ℕ)[NeZero n] (p : Many n X) := ∏ i:Fin n,K i.val (p i,p (i+1))
lemma cyclic_env (n:ℕ)[NeZero n]: Envelope (cyclic K n) := product_env _ _ fun i _=> Env.along (K i.val).paid (by fun_prop)
theorem total (K : ℕ→Kern μ) (n:ℕ)[NeZero n]: (∫ p:Many n X,cyclic K n p∂piN n μ) = (Kern.roll K n).τ := by
 rcases n with _|n; · have := NeZero.ne 0; contradiction
 have ht (p:Many (n+1) X): cyclic K (n+1) p=route K n p (p 0):=by
    unfold route cyclic; refine prod_congr rfl fun i _=> ?_
    induction i using Fin.lastCases with
    | last=> simp
    | cast i=> simp [Fin.succ_castSucc,-Fin.castSucc_succ]
 rw [pi_succ,integral_prod]; swap; · exact Env.integrableX (Env.along (cyclic_env _) (measurable_pre n)) _
 simp_rw [ht, Fin.cons_zero,route_head]; rfl
end lines
end YM.CF.Buffered.Stack
