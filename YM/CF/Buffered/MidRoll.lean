import YM.CF.Buffered.Sailing
/-! # Cauchy reflect for a cyclic stripe with inhomogeneous kernels -/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 390000
noncomputable section
namespace YM.CF.Buffered.Stack
open Function Filter NormedSpace MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Fin.NatCast
variable {I:Type*}[MeasurableSpace I]{μ:Measure I}[IsFiniteMeasure μ]
namespace Kern
variable {n m l:ℕ} (F:ℕ→Kern μ)
lemma roll_append (p:0<n)(v:0< m): roll F (n+m)= roll F n* roll (fun i=>F (i+n)) m:=by
 induction n,p using Nat.le_induction generalizing F with
 | base=> rw [add_comm,roll_next F v,roll_one]
 | succ n h ih=> rw [show n+1+m=n+m+1 from by omega, roll_next F (by omega), roll_next F h, ih,mul_assoc]; congr; -- tune
lemma roll_last (p:0<n): roll F (n+1)=roll F n*F n:= by rw [roll_append F p (by decide),roll_one]; simp
lemma roll_reverse {G:ℕ→ Kern μ}(p:0<n)(t:∀ i<n,G i=star (F (n-1-i))): roll G n= star (roll F n):=by
 induction n,p using Nat.le_induction generalizing G F with
 | base=> simpa [roll_one] using t 0 (by decide)
 | succ n h ih=> rw [roll_next G h,roll_last F h,star_mul,ih F (fun j v=> (t _ (by omega:j+1<n+1)).trans (by rw [show n+1-1-(j+1)=n-1-j by omega])), t 0 (by omega)]; simp
lemma roll_cs (p:0<n) : let Q:=fun i=> F (i+n); ‖τ (roll F (n+n))‖^2 ≤ ‖τ (roll F n * star (roll F n))‖ * ‖τ (star (roll Q n) * roll Q n)‖:=by
 intro Q; rw [τ_count',roll_append F p p]; let x:=roll Q n; let y:=roll F n; change ‖τ (y*x)‖^2≤_*‖τ (star x*x)‖; rw [show τ (star x*x)=(count (star x):ℂ) from ?_]; swap; · nth_rw 2 [←star_star x]; exact τ_count (star x)
 rw [Complex.norm_real,Real.norm_of_nonneg (count_nonneg _), mul_comm,←star_star x]; simpa only [star_star] using τ_schwarz y (star x)

lemma roll_step (p:2 ≤ n)(h:F n=F 0): τ (roll (fun i=>F (i+1)) n)=τ (roll F n):= by
 obtain _|n:=n; · omega
 rw [roll_last _ (by omega), roll_next F (by omega),h,τ_cycle]
variable [NeZero n] (G: Fin n → Kern μ)
lemma roll_rotation (t:Fin n)(p: 2 ≤ n): τ (roll (fun i:ℕ=>G (t+i)) n)=τ (roll (fun i:ℕ=>G (↑i)) n):=by
 let Q(k:ℕ) := τ (roll (fun i:ℕ=> G ((k:Fin n)+i)) n); suffices ∀ k:ℕ,Q k=Q 0 by simpa [Q] using this t.val
 intro k; induction k with | zero=> rfl | succ k ih=> rw [←ih]; unfold Q; have ht:= roll_step (fun i:ℕ=>G ((k:Fin n)+i)) p (by simp); rw [←ht]; congr 2; funext i; push_cast; abel -- tune

-- K matching reordered at t first then mirror. specify a list relative permutation as Nat. 
lemma reflect_rect (G G' G'':Fin n→ Kern μ) (p:Even n)(t:Fin n) (W:n=l+l) -- l:ℕ tune
 (h:∀ (i: Fin n), i.val<l→
 G' (t+i)=G (t+i) ∧ G' (t+i.rev)=star (G (t+i)) ∧ G'' (t+i.rev)=G (t+i.rev) ∧ G'' (t+i)=star (G (t+i.rev))) :
 let U(L:Fin n→ Kern μ):=‖τ (roll (fun i:ℕ=> L (↑i)) n)‖
 U G ^ 2 ≤ U G' * U G'':=by
 intro U; unfold U; rw [←roll_rotation G t (by have h' := NeZero.pos n; omega),← roll_rotation G' t (by have h' := NeZero.pos n; omega),←roll_rotation G'' t (by have h' := NeZero.pos n; omega)]; -- rewrite all n independent
 let A(V:Fin n→Kern μ)(j:ℕ):=V (t+(j:Fin n)); let B(V:Fin n→Kern μ)(j:ℕ):=A V (j+l); let F:=roll (A G) l; let Q:=roll (B G) l
 have he(V:Fin n→Kern μ): roll (A V) n=roll (A V) l*roll (B V) l:=(show _ from ?_)
 · have hv : l>0 :=by have hp:=NeZero.pos n; omega
   -- mirrors identity `rev` of i maps to `(l-1-i)+l`.
   have hx(j:ℕ)(k:j<l): (j:Fin n).rev=((l-1-j+l:ℕ):Fin n):=by apply Fin.ext; rw [Fin.val_rev,Fin.val_cast_of_lt (by omega),Fin.val_cast_of_lt (by omega)]; omega -- tune
   have hy(j:ℕ)(k:j<l) := h (j:Fin n) (show (j:Fin n).val<l by rw [Fin.val_cast_of_lt (by omega)]; exact k)
   have hz(j:ℕ)(k:j<l):B G' j=star (A G (l-1-j)) ∧ B G'' j=B G j:=by
      let d:=l-1-j; have he:d<l:=by unfold d; omega
      obtain ⟨g,t,q,s⟩:=hy d he; rw [hx d he,show l-1-d=j from by unfold d; omega] at t q; exact ⟨t,q⟩
   change ‖τ (roll (A G) n)‖^2≤ ‖τ (roll (A G') n)‖*‖τ (roll (A G'') n)‖
   rw [he,he G'',he G',roll_congr (A G') (A G) hv (fun i t=>(hy i t).1), roll_reverse (A G) hv (fun j p=>(hz j p).1), roll_congr (B G'') (B G) hv (fun i t=>(hz i t).2),roll_reverse (B G) hv (?_ :∀ i<l,A G'' i=star (B G (l-1-i)))]
   · have ht:= roll_cs (A G) hv; rw [←W,he] at ht; exact ht
   intro i p; have hp:=(hy i p).2.2.2; rw [hx i p] at hp; exact hp
 · nth_rw 1 [W]; exact roll_append _ (by have h':=NeZero.pos n; omega) (by have h':=NeZero.pos n; omega)
end Kern
end YM.CF.Buffered.Stack
#print axioms YM.CF.Buffered.Stack.Kern.reflect_rect
