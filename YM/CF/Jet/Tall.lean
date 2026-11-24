import YM.CF.Jet.Gibbs
import YM.CF.Broc.Live
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Function Filter Metric Finset MeasureTheory Phase Phase.Sample Lattice Cube Lat Broc Branch
open scoped Topology BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {Y T D E J Z G H:Type} [Fintype Y][DecidableEq Y][TopologicalSpace D][TopologicalSpace E][Fintype Z][DecidableEq Z]
structure Draw (D:Type) where
 test : ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E], Set E → (E→D) → Prop
variable {b:Light Y D G}{Q:Draw D}{n:ℕ}
def OrderD (Q:Draw D)(n:ℕ)(F:D→ℂ)(w:ℝ):Prop:= ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (V:Set E) (h:IsOpen V)(p:E→D), Q.test E V p→∀ x∈V, Allows n (F ∘ p) x w
-- PLUS continuity bids
structure Flash (b:Light Y D G)(Q:Draw D)(n:ℕ)(S: Seal Y)(F:D→ℂ)(w:ℝ):Prop extends Peak b S F w where
 plot: OrderD Q n F w
def Screen (b:Light Y D G)(Q:Draw D)(n:ℕ)(F:D→ℂ)(a C:ℝ):Prop:=∃ (M:Seal Y→D→ℂ) (X:Seal Y→ℝ),(∀ S,Flash b Q n S (M S) (X S))∧(∀ i,hitE a X i≤ C) ∧ ∀ x,F x=∑ i,M i x
variable {F f:D→ℂ}{S:Seal Y}{a c q d w v:ℝ}
lemma Flash.add(h:Flash b Q n S F w)(p:Flash b Q n S f v): Flash b Q n S (fun x=>F x+f x) (w+v):=⟨h.toPeak.tone p.toPeak, fun A _ _ _ T t g k x l=> (h.plot A T t g k x l).add (p.plot A T t g k x l)⟩
lemma Flash.linear(h:Flash b Q n S F w)(A:ℂ→L[ℝ]ℂ)(p:‖A‖≤a):Flash b Q n S (A ∘ F) (a*w):=⟨h.toPeak.traceF A a p,fun Y _ _ _ V hT Z p' x l=> (h.plot Y V hT Z p' x l).linear A p⟩
lemma Flash.mult(h:Flash b Q n S F w){a:ℝ}(p:w≤a)(g:w=0→a=0):Flash b Q n S F a:=⟨{h.toPeak with pos:=h.pos.trans p, travel:=fun v=>h.travel (fun t=>v (g t)), sumline x:=(h.sumline _).trans p},fun A _ _ _ S t f g x l=> (h.plot A S t f g x l).mono p⟩
lemma Screen.plus(h:Screen b Q n F a d)(p:Screen b Q n f a v): Screen b Q n (fun x=>F x+f x) a (d+v):=by
 obtain ⟨M,K,h,k,U⟩:=h; obtain ⟨P,W,p,q,X⟩:=p
 refine ⟨_,_,fun S=>(h S).add (p S),fun i=> ?_,fun x=>?_⟩
 · simp only [hitE,mul_add,sum_add_distrib]; exact add_le_add (k i) (q i)
 dsimp only; rw [sum_add_distrib, U, X]
lemma Screen.lin(h:Screen b Q n F a c)(A:ℂ→L[ℝ]ℂ)(p:‖A‖ ≤ d):Screen b Q n (A ∘ F) a (d*c):=by
 obtain ⟨M,K,u,k,H⟩:=h; refine ⟨_,_,fun S=> (u S).linear A p,fun i=> ?_,fun x=>?_⟩
 · unfold hitE; simp_rw [mul_left_comm _ d (K _),←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (k i) ((norm_nonneg _).trans p)
 change A (F x)=_; rw [H,map_sum]; rfl
lemma Screen.minus(h:Screen b Q n F a c):Screen b Q n (fun x=> -F x) a c:=by have ht:=h.lin (-(ContinuousLinearMap.id ℝ ℂ)) (d:=1) (by simp); rw [one_mul] at ht; exact ht
lemma Flash.hop {L:E→D}{T:Draw E}{c:Light Z E H}{W:Seal Z}(p:∀ (A:Type)[NormedAddCommGroup A][NormedSpace ℝ A][FiniteDimensional ℝ A],∀ V:Set A, IsOpen V→∀ (f:A→E), T.test A V f→ Q.test A V (L ∘ f)) (u:Continuous L)(h:Flash b Q n S F w)(g:w≠0→Grove c.frame W)(l:∀ x y,c.rel W x y→ b.rel S (L x) (L y))(e:∀ x y,∃ g',L (c.dress y x)=b.dress g' (L x)): Flash c T n W (F ∘ L) w:=by
 refine ⟨⟨h.pos,g,h.cont.comp u,fun x=>h.sumline _,fun x y b=> h.reads _ _ (l x y b),?_⟩,fun A _ _ _ V m f t x hx=> h.plot A V m (L ∘ f) (p A V m f t) _ hx⟩
 intro x y; obtain ⟨g,H⟩:= e x y; simp only [Function.comp_apply,H,h.gauge]
lemma Flash.collects (V: Finset J)(f:J→D→ℂ)(w:J→ℝ)(h:∀ i∈V,Flash b Q n S (f i) (w i)): Flash b Q n S (fun x=>∑ i∈V,f i x) (∑ i∈V,w i):=by
 classical
 refine ⟨Peak.collects _ _ _ (fun i g=>(h i g).toPeak),fun E _ _ _ S s p u x hx=>?_⟩
 exact allows_sum (f:=fun i t=> f i (p t)) (fun i g=>(h i g).plot E S s p u x hx)
variable {b:Light Y D G}{c: Light Z E H}{Φ: Seal Y→ Seal Z}{v w a K q:ℝ}{Ω:Draw E}
lemma ledgerDX(K:Seal Y→ℝ)(h: Exceed b.frame c.frame Φ v w)(X:Seal Y→E→ℂ)(e:∀ i,Flash c Ω n (Φ i) (X i) (K i))(p:ℝ)(g:0≤p)(L:E→ℂ)(u:∀ x,L x=∑ i,X i x)(hq:0≤q)(hv:q*v≤a) (hp:∀ i, K i≠0→Grove b.frame i) (r:∀ i:Y,hitE a K i≤p): Screen c Ω n L q (w*p):=by
 let W(T:Seal Z):=dest Φ T; let k(T:Seal Z):= ∑ i∈ W T,K i
 have he(T): Flash c Ω n T (fun t=>∑ i∈W T, X i t) (k T):= Flash.collects _ _ _ (fun i h=> by rw [←show Φ i=T from (mem_filter.mp (show _ from h)).2]; exact e i)
 refine ⟨_,k,he,(fun i=>?_), fun x=> (u x).trans (lump ..)⟩
 obtain ⟨z,hz,hl⟩:= h.coverage i; let f(S:Seal Y):=if i∈Φ S then Branch.rent q (Φ S)*K S else 0
 have hh : hitE q k i=∑ S,f S:=by
   rw [lump Φ f]; unfold hitE hit0; rw [sum_filter]; apply sum_congr rfl; intro t _; unfold k; rw [mul_sum]; unfold W; by_cases hx:i∈t
   · rw [if_pos hx]; exact sum_congr rfl fun b he=> by unfold f; rw [(mem_filter.mp he).2,if_pos hx]
   rw [if_neg hx,sum_eq_zero]; intro z h; unfold f; rw [(mem_filter.mp h).2,if_neg hx]
 have hm(y:Y): hitE a K y=∑ S, if y∈S then Branch.rent a S*K S else 0:=Finset.sum_filter ..
 rw [hh]; apply le_trans _ (show ∑ y∈z,hitE a K y≤ w*p from (sum_le_sum fun y (_:y∈z)=> r y).trans (by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hz g)); simp_rw [hm]; rw [Finset.sum_comm]
 apply sum_le_sum; intro S _; have ht(y:Y):0≤(if y∈S then Branch.rent a S*K S else 0):=by split; exact mul_nonneg (rent_pos ..).le (e _).pos; rfl
 unfold f; split_ifs with k
 · by_cases he:K S=0; rw [he,mul_zero]; simpa only [←he] using (sum_nonneg (fun y _=> ht y) : 0≤∑ y∈z,if y∈S then Branch.rent a S*K S else 0)
   have hK:= hp S he; obtain ⟨y,z,Y⟩:=hl S hK k
   apply le_trans _ (single_le_sum (f:=fun y=> if y∈S then Branch.rent a S*K S else 0) (fun y _=>ht y) z); rw [if_pos Y]
   apply mul_le_mul_of_nonneg_right _ (e _).pos; exact Real.exp_monotone ( (mul_le_mul_of_nonneg_left (h.band hK) hq).trans (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hv (by positivity)))
 exact sum_nonneg (fun y _=>ht y)
lemma Screen.leaps {F:D→ℂ}{Q: Draw D}{M:ℝ}(h: Screen b Q n F a M)(r:Exceed b.frame c.frame Φ v w) (d:E→D)(H: Continuous d) (hm:0≤M)(s:0≤q)(l:q*v ≤ a)(g:∀ S x z,c.rel (Φ S) x z→ b.rel S (d x) (d z))(f:∀ x y,∃ g':G,d (c.dress y x)=b.dress g' (d x))(t:∀ (A:Type)[NormedAddCommGroup A][NormedSpace ℝ A][FiniteDimensional ℝ A],∀ V:Set A, IsOpen V→∀ (f:A→E), Ω.test A V f→ Q.test A V (d ∘ f)): Screen c Ω n (F ∘ d) q (w*M):=by
 obtain ⟨P,X,h,K,v⟩:=h
 exact ledgerDX X r (fun S=>P S ∘ d) (fun S=> Flash.hop t H (h S) (fun u=>r.plus ((h S).travel u)) (g S) f) M hm _ (fun x=>v _) s l (fun S=> (h S).travel) K
end YM.CF.Jet
