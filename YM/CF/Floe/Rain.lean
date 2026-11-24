import YM.CF.Floe.Paid
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floe
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Filter NormedSpace Function Lattice Lat SU Fock Phase Cube Tenant Branch Drapes Metric Finset
attribute [local instance] opCStarAlgebra
open Jet Phase.Sample MeasureTheory
open scoped ContDiff
variable{K b c d r R A C:ℝ}
variable {m B N:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{n:ℕ}
lemma voteR(x:Cue m) (h:1≤K) (a:E):ToR n (fun _=>x) a K:=fun i=> allows_const _ ((vote_unit (x i)).trans_le h)
lemma scrapR(F G:E→Cue m)(x:E)(h:ToR n F x b)(p:ToR n G x b) : arr n (fun t=> twin m (F t) (G t)) x b:=by
 intro i; unfold Phase.twin capRow; dsimp only; split; exact p i.1; exact h i.1
abbrev TaggedCur(K:ℝ)(n:ℕ)(U:E→Pack m B)(F G:E→Cue m)(x:E):Prop:=TransK n (fun i=>(U i).1) x K∧ToR n (fun i=>(U i).2) x K∧ToR n F x K∧ ToR n G x K
lemma glowF(h:1 ≤ K)(p:0 < R)(B:Side)(n:ℕ):∃ C:ℝ,0≤C∧∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](m:Side)(H:Kelp (CSide m B) R→ℂ), Looks _ H→Continuous H→∀ A:ℝ,(∀ i,‖H i‖ ≤A)→∀ (U:E→Pack m B) (F G:E→Cue m)(x:E)(e:ℝ),Room B e→ (∀ᶠ i in 𝓝 x, ((U i,F i),G i)∈checked m B e)→ TaggedCur K n U F G x →∀ v:Hub m,Allows n (fun x=> inks m B (fun y=>H (uθ y p)) v ((U x,F x),G x)) x (C*A):=by
 obtain ⟨z,k,H⟩:= brimA n p h B; let f:ℂ→ₗ[ℝ]ℂ:=LinearMap.id -- divide build
 let T:ℂ→L[ℝ]ℂ:=((2:ℝ)⁻¹) • ContinuousLinearMap.id ℝ ℂ; have ht(x:ℂ): T x=x/2:=by simp [T,Complex.real_smul,div_eq_mul_inv,mul_comm]
 let W:= ‖T‖*z; have he:0≤W:=by unfold W; positivity
 refine ⟨(way B:ℝ)*(W+W),by positivity,fun E _ _ _ m F L v A y U G x₁ x e V hg p' u=>?_⟩
 let f':Post m B→ℂ:= fun i=> F (uθ i p); have hh(i:ℕ)(l:i<way B)(Y:E→Cue m)(t:∀ᶠ i in 𝓝 x, EdgeP m B (U i).1 (Y i) (x₁ i))(k:ToR n Y x K): Allows n (fun z=>glow m B f' u (U z).1 (Y z) (x₁ z) i) x (W*A):=by
    have he := H E m F L v A y _ _ _ _ u x e _ (day_in B i l.le) (day_in B _ l) (day_gap B i) V p'.1 (scrapR Y x₁ x k p'.2.2.2) ((hg.and t).mono fun i z=> ⟨z.1.1.1.1,z.2⟩)
    unfold glow; simp_rw [←ht]; unfold W; rw [mul_assoc]; exact he.linear T le_rfl
 obtain ⟨p0,hY,u0,w⟩:=p'; have he:= allows_sum (s:=range (way B)) (fun i p=> ((hh i (mem_range.mp p) G (hg.mono fun i h=>h.2.2) u0).add ((hh i (mem_range.mp p) (fun i=>(U i).2) (hg.mono fun i h=>h.2.1) hY).smul (-1)))) -- tune
 unfold inks; simp_rw [sub_eq_add_neg]; simp only [neg_one_smul,abs_neg,abs_one,one_mul] at he; apply he.mono; simp; ring_nf; rfl
lemma rock_v (n:ℕ)(K:ℝ)(h:1≤K)(B:Side):∃ C:ℝ,0≤C∧∀ (m:Side)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](S:Set E),IsOpen S → ∀ (U:E→Pack m B) (X: E→Cue m),(∀ x∈S,TransK n (fun i=>(U i).1) x K∧ ToR n (fun i=>(U i).2) x K∧ ToR n X x K)→ FireK S (fun i=> loft m B (U i).1 (U i).2 (X i)) C n:=by
 obtain ⟨C,hC,H⟩:=zap (Finset.univ:Finset Bool) (by simp) n B h
 refine ⟨C,hC,fun m E _ _ _ S u p X A=>?_⟩; let f(i:E):=loft m B (p i).1 (p i).2 (X i); have hx(x)(v:x∈S)(a:Index m)(t:Cue m):CashCold (fun i=>(f i).run a t) x n C:=by
    unfold f loft; dsimp only; unfold bidW; apply H E S u m _ _ _ ?_ 1 (fun _=>{0}) a x v; intro x t'; refine ⟨(A x t').1,voteR t h x,fun k _ i=>?_⟩; unfold request; split; exact (A x t').2.1 i.1; exact (A x t').2.2 i.1
 exact ⟨u,hC,fun x h i z=>(hx x h i z).1,fun x h i z=> (hx x h i z).2⟩
end YM.CF.Floe
