import YM.SU5.FiniteGaugeData.Largo.Skein
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory
open scoped Topology BigOperators ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace
attribute [local instance] opCStarAlgebra
lemma floorInst (l:ℕ)(b:Bool)(i:ℕ): instant l b i= if b then ((l+i:ℕ):ℤ) else -((l+i:ℕ):ℤ):= rfl
lemma floorMono (l:ℕ)(b:Bool): Function.Injective (instant l b):= by intro i j t; cases b <;> rw [floorInst,floorInst] at t <;> simp at t <;> omega
lemma upperUp (b:Bool):upperL b ∈ plusHalf:=by cases b <;> decide
lemma lowerDo (b:Bool):lowerL b ∉ plusHalf:=by cases b <;> decide
lemma upperInj : Injective upperL:=by intro i j t; cases i <;> cases j <;> revert t <;> decide -- tune
lemma lowerInj : Injective lowerL:=by intro i j t; cases i <;> cases j <;> revert t <;> decide
variable {V: Rim}{K:Side}(l n:ℕ)(b:Bool)
lemma slab_compact : IsCompact (setOf Slab):= by
 rw [show setOf Slab = Set.univ.pi (fun (_:Tang)=>Set.Icc (1:ℝ) 2) from ?_]; apply isCompact_univ_pi; intro i; exact isCompact_Icc
 ext i; simp only [Set.mem_setOf_eq,Set.mem_pi, Set.mem_univ, forall_true_left,Set.mem_Icc] ; rfl -- [Slab,Set.mem_pi]
-- lease index purchasing. `k` absolute reserve layer in both ranges. choose another lease of opposite orientation and l' after previous ℓ. 
abbrev chirp {n:ℕ}(V: Flight→Flight→ℂ)(x y:Fin n→ Flight):Op (Fin n):= Matrix.of fun i j => V (x i) (y j)
structure Limit (D:ℕ) (x y:Fin n→ Flight)(K':Flight→Flight→ℂ):Prop where
 fuel (i): (x i).1 < D ∧ (y i).1 < D
 rank : IsUnit (chirp K' x y)
 cost : ‖(chirp K' x y)⁻¹‖ ≤ D
namespace Limit
lemma local_purchase_iff (f:Flight→Flight→ℂ)(x y:Fin n→ Flight) (p:(chirp f x y).det ≠0) : ∃ r:ℕ, (∀ i,(x i).1 < r∧ (y i).1 < r) ∧∀ᶠ g: Op (Fin n) in 𝓝 (chirp f x y), IsUnit g ∧‖g⁻¹‖ ≤ r:=by
 let u:=(univ:Finset (Fin n)).sup fun i=>(x i).1+(y i).1; let A:= chirp f x y; have h:ContinuousAt Inv.inv A:= continuousAt_matrix_inv A (by rw [show Ring.inverse (M₀:=ℂ)=Inv.inv from funext Ring.inverse_eq_inv]; exact continuousAt_inv₀ p)
 obtain ⟨r,hx⟩:=exists_nat_gt ‖A⁻¹‖; refine ⟨r+u+1,fun i=>?_,?_⟩; · have h:(x i).1+(y i).1 ≤ u:= le_sup (f:=fun i=>(x i).1+(y i).1) (mem_univ _); omega
 filter_upwards [h.tendsto.norm.eventually (ge_mem_nhds hx), (show Continuous (Matrix.det (n:=Fin n) (R:=ℂ)) from (show Continuous (fun z:Op (Fin n)=>z.det) from continuous_id.matrix_det)).continuousAt (x:=A)|>.eventually_ne p] with i t u0; exact ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.mpr u0), t.trans (Nat.cast_le.mpr (by omega))⟩
lemma prime (v':V∈setOf Slab) : ∃ x y:Fin n→ Flight, ∃ D:ℕ, ∀ᶠ a:Op (Fin n) in 𝓝 (chirp (loan (Tempo (fun r=> melody (floorPin V r))) l b) x y), IsUnit a ∧ ‖a⁻¹‖ ≤ D:=by obtain ⟨x,y,p⟩:= inch V v' l n b; obtain ⟨r,u,t⟩:= local_purchase_iff n _ x y p; exact ⟨x,y,r,t⟩ -- fuel version actual desired
end Limit
lemma purchaseN : ∃ D:ℕ, ∀ (m N:Side), D ≤ m.val → Odd m.val → D ≤ N.val → Even N.val→∀ (o : Rim), Slab o→∃ x y:Fin n→ Flight, Limit n D x y (loan (berth o m N) l b):= by
 by_contra! k; choose m N a w e g V v h using k -- check order ∃ m, etc
 obtain ⟨W,H,r,t,x⟩:=slab_compact.isSeqCompact (show ∀ i,V i∈setOf Slab from v); obtain ⟨j,k',p⟩:= inch W H l n b; let A:= chirp (loan (Tempo (fun r=> melody (floorPin W r))) l b) j k'; let f(i):= chirp (loan (berth (V (r i)) (m (r i)) (N (r i))) l b) j k'
 have s:Tendsto f atTop (𝓝 A):= by
    refine tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun y=>?_; exact chance_b W H _ _ _ _ (π:=N∘r) (M₁:=m∘r) (fun i=>g _) (tendsto_atTop_mono (fun _=>e _) t.tendsto_atTop) (fun i=>w _) (tendsto_atTop_mono (fun _=> a _) t.tendsto_atTop) _ (fun i=> v _) x
 obtain ⟨u,z,d⟩:=Limit.local_purchase_iff n _ j k' p; obtain ⟨a,h',u'⟩:= ((s.eventually d).and (t.tendsto_atTop.eventually_ge_atTop u)).exists
 exact h (r a) j k' ⟨fun i=> ⟨(z i|>.1).trans_le u',(z i|>.2).trans_le u'⟩,h'.1,h'.2.trans (Nat.cast_le.mpr u')⟩
#print axioms purchaseN
end YM.CF.Window.Largo
