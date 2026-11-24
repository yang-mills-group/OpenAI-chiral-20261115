import YM.CF.Reed.Palm
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology BoundedContinuousFunction ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Phase.Part m B} {A D d e β : ℝ} {W : Scroll m B c}
lemma kReg (ω ε : ℝ) (p:0<ω) (v:0<ε) : ∃ u c:ℝ, 0<u ∧ 0<c ∧ ∃ n:ℕ, ∀ B:Side,n≤B.val → ∃ k:ℝ,0<k∧∀ e:ℝ,0<e → e≤k→∀ β:ℝ,∀ r>0, ∃ R:Reg β e B, 1-r<R.knob ∧ R.knob<1 ∧ (∀ m:Side,RunsB m B (R.c m) (R.W m) u c (quantile u B) e ω ε) ∧ R.Works ∧ (R.c=fun m=>anticut (CSide m B)) := by
  obtain ⟨u,c,g,h,N,H⟩ := schedule ω ε p v; refine ⟨u,c,g,h,N,fun B e=>?_⟩; obtain ⟨k,f,M⟩ := H B e
  refine ⟨k,f,?_⟩; intro e p g β r t
  let c₀ (m : Side) : Foot m B := anticut _; choose W L using fun m:Side=> M e p.le g m (c₀ m)
  let P := (L 1).budget
  obtain ⟨a,hA,T,S⟩ := covered B u c _ _ β _ P p c₀ W (fun i=>(L i).scaleK) t -- tune
  choose F hf hV Z using S
  let R : Reg β e B := ⟨c₀,W,F,a,fun i=> ⟨hf i,hV i⟩, fun i j=> Z j i⟩
  exact ⟨R,hA,T,L,R.supplied _ _ _ (fun i=>(L i).scaleK) P,rfl⟩
end YM.CF.RP
namespace YM.CF.Ave
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology ComplexOrder
open Fock SU Lat Cube Phase Phase.Sample Mir RP MeasureTheory NormedSpace Branch Lattice Tenant Function Pastry Petal Manifest Filter Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Foot m B} {W : Scroll m B c} {e v H σ A d r β b k t : ℝ}
lemma majorK (p : 0<k) : ∃ σ:ℝ,0<σ∧σ<1∧∃ N:ℕ,∀ B:Side,N≤B.val→∃ ε Y:ℝ,0<ε∧∀ e:ℝ, 0<e→ e≤ ε→ ∃ b:Room B e,∀ β:ℝ, ∀ r:ℝ,0<r→ ∃ R:Reg β e B, 1-r<R.knob ∧ Warranty B e β k σ b Y R ∧ (R.c=fun m=>anticut (CSide m B)) := by
  let z:= k+2; have hx : 0<z:= by unfold z; linarith
  obtain ⟨u,c,t,v,o,X⟩:= kReg z (1/32) hx (by norm_num)
  obtain ⟨σ,h,g,l,A⟩:= insurable hx
  obtain ⟨w,N⟩:= thermal p
  obtain ⟨j,P⟩:= exists_nat_gt (z*21^4/u)
  refine ⟨σ,h,g,o+w+l+j,?_⟩; intro B hb
  have hp (e : ℝ) : z*21^4≤ u* (B.val:ℝ) := (le_of_lt ((div_lt_iff₀ t).mp P)).trans (by
    rw [mul_comm]; have he : j≤B.val:= by omega
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast he) t.le)
  obtain ⟨ε,q,E⟩:= X B (by omega); obtain ⟨Y,hY,gY⟩:= N B (by omega)
  refine ⟨ε,Y,q,?_⟩; intro e l' a
  let e₀:= E e l' a; have he : Budget B e (quantile u B) := ((e₀ 0 1 zero_lt_one).choose_spec.2.2.1 1).budget
  refine ⟨he.1,?_⟩; intro β r hr
  obtain ⟨J,r',hJ,hj⟩:= cupSize B c v p hr
  obtain ⟨R,T,y,V,b,ξ⟩:= E e l' a β J r'
  obtain ⟨d,W⟩:= hj _ T y
  refine ⟨R,lt_of_le_of_lt (by linarith) T,⟨b,fun _=>melody _ he.1,fun m U=>?_,fun m U g=>?_,fun m=>gY _ he.1 m (R.c m),fun s v'=>?_⟩,ξ⟩
  · -- from existence ZeroF
    exact unity (R.c m) he.1 U.property -- tune
  · exact band_g (R.c m) he.1 U.property g -- tune
  obtain ⟨K,P⟩:= A B (by omega) s v'
  refine ⟨K,fun n k m=>?_⟩
  obtain ⟨t,Q,F,U⟩:= P n k (R.time n) (R.charges n).1.le (R.charges n).2.le e he.1 m (R.c m)
  obtain ⟨A,L,x⟩:= accordR (V m) t U d (W m) (hp e) v.le p
  exact ⟨A,L,morals v' he (V m).scaleK h g n t x⟩
end YM.CF.Ave
namespace YM.CF.Reed
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect Pastry RP Ave Delta
attribute [local instance] opCStarAlgebra
variable {B : Side} {β e k p K σ L : ℝ} {c : Room B e}
lemma FiniteK (k : ℝ) (h : 0<k) : ∃ σ:ℝ,0<σ∧σ<1∧∃ N:ℕ,∀ B:Side,N≤B.val→∃ ε Y p K:ℝ,0<ε∧0<p∧∀ e:ℝ, 0<e→ e≤ ε→ ∃ b:Room B e,∀ β:ℝ, ∀ r:ℝ,0<r→ ∃ R:Reg β e B, 1-r<R.knob ∧ Cutoff R p Y k K σ b ∧ R.c=(fun m=>anticut (CSide m B)) := by
  obtain ⟨s,p,H,y,G⟩:= Ave.majorK h
  obtain ⟨u,Q⟩:= Delta.flowerV k h
  refine ⟨s,p,H,u+y,fun B g=>?_⟩
  obtain ⟨v,Y,j,L⟩:= G B (by omega)
  obtain ⟨t,b,V,R⟩:= Q B (by omega)
  refine ⟨v,Y,t,b,j,V,fun e h w=>?_⟩; obtain ⟨c,A⟩:= L e h w; refine ⟨c,fun i r hr=>?_⟩; obtain ⟨Z,p,F,hT⟩:= A i r hr; exact ⟨Z,p,Cutoff.awake Z F (fun m=>R e c m (Z.c m)),hT⟩
end YM.CF.Reed
