import YM.CF.Skye.Storm
set_option autoImplicit false
noncomputable section
namespace YM.CF.Skye
open Function Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical
variable {n:Side}{u d:ℝ}
-- measurable choice with location tests and ties local
instance seat_meas : MeasurableSpace (Seat n):=⊤ -- tune overlap; consider remove
instance seat_class : MeasurableSingletonClass (Seat n):= ⟨fun _=> trivial⟩
abbrev priorP (X: Ids n) (i:Seat n):= (X i).1
private lemma minSup(X:Finset (Seat n)):∃ f: (Seat n→ℝ)→ Seat n,Measurable f ∧ (X.Nonempty→∀ a,f a∈ X ∧ ∀ i∈X,a (f a)≤a i) ∧ ∀ i j,Set.EqOn i j X→f i=f j:=by
 induction X using Finset.induction_on with
 | empty=>exact ⟨fun _=>0,measurable_const,(by simp),fun _ _ _=>rfl⟩
 | @insert i X h ih=>
    obtain ⟨f,p,hx,H⟩:=ih; by_cases g:X.Nonempty; swap
    · rw [not_nonempty_iff_eq_empty.mp g]; exact ⟨fun _=>i,measurable_const,(by simp),fun _ _ _=>rfl⟩
    let T(a:Seat n→ℝ):= a (f a)≤ a i
    have ht:MeasurableSet {a|T a}:=by
       have he : Measurable (fun a : Seat n→ℝ=> a (f a)) := by
          intro s l; rw [show (fun a : Seat n→ℝ=> a (f a)) ⁻¹' s=⋃ j:Seat n,{a| f a=j} ∩ Function.eval j ⁻¹' s from ?_]; apply MeasurableSet.iUnion; intro j; exact (measurableSet_eq_fun p measurable_const).inter ((measurable_pi_apply _) l) -- tune
          ext a; simp
       exact measurableSet_le he (measurable_pi_apply i)
    let F(a):= if T a then f a else i; refine ⟨F,Measurable.ite ht p measurable_const,fun l a=>?_,fun x y z=>?_⟩
    · obtain ⟨d,v⟩:= hx g a; unfold F; split; next p=> exact ⟨mem_insert_of_mem d,fun j h=> (mem_insert.mp h).elim (fun e=>e.symm ▸ p) (v j)⟩
      next l=>exact ⟨mem_insert_self ..,fun j e=> (mem_insert.mp e).elim (fun e=>le_of_eq (congrArg a e.symm)) (fun k=> (le_of_not_ge l).trans (v j k)) ⟩ -- l : ¬ le, le_of_not_ge
    have he:=H x y (z.mono fun _ v=> Finset.mem_insert_of_mem v); have hz: x i=y i:=z (by simp); have hp' : x (f y)=y (f y):=z (Finset.mem_insert_of_mem (hx g y).1); unfold F T; simp [he,hz,hp']

def greet(X:Finset (Seat n)):= (minSup X).choose
lemma mastM(X:Finset (Seat n)): Measurable (@greet n X):=(minSup X).choose_spec.1
lemma mastP (X:Finset (Seat n))(p:X.Nonempty)(u:Seat n→ℝ): greet X u ∈ X ∧ ∀ i∈X, u (greet X u)≤u i:=(minSup X).choose_spec.2.1 p u
lemma mastL (X:Finset (Seat n))(u v:Seat n→ℝ)(h:Set.EqOn u v X):greet X u=greet X v:=(minSup X).choose_spec.2.2 u v h
lemma mast_rev (M:Finset (Seat n))(s:Sweep n)(k:ℕ)(e:reach n)(X:Ids n)(p:(soup M k e).Nonempty)(g:Injective (priorP X)) : -- k,e undecl; want generic
 boxA s (greet ((soup M k e).map (boxA s).symm.toEmbedding) (priorP (bun s X))) = greet (soup M k e) (priorP X):=by
 set Y:= soup M _ _; let Z:= Y.map (boxA s).symm.toEmbedding; let b:= priorP (bun s X); let u:= priorP X
 obtain ⟨t,T⟩:=mastP Z (Finset.map_nonempty.mpr p) b; obtain ⟨j,hx⟩:=mastP Y p u
 change boxA s (greet Z b)= _; apply g; apply le_antisymm; · have he:(boxA s).symm (greet Y u)∈ Z:=mem_map_of_mem _ j; have hx:=T _ he; change u ((boxA s) (greet Z b)) ≤ u (boxA s ((boxA s).symm _)) at hx; rw [Equiv.apply_symm_apply] at hx; exact hx
 apply hx; simpa [Z] using t
end YM.CF.Skye
