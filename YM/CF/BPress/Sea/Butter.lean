import YM.CF.BPress.Sea.Pollen
/- hradius stencil ζ. Parameter path may be partial; glue fallback external on complement, thus uses OPEN interval to pay. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Nougat
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Pec Spin SpinSign Spin.Pledge Pledge.Costs Cube Lat SU Spin.Paint Nacre Laic Font Push.AbsoluteSums.Paths Tulip Tenant Dial Scroll Thera
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
variable {B m L N :Side}{q d a b K κ r:ℝ}
open Jet Spire Phase.Sample Brace Phase Kea Pic Sods Broc
namespace Shell
structure plot (q r d κ K:ℝ):Prop where
 high:0<κ
 bill:1≤K
 spot: ∀ {N:Side}{c:ℝ}{T X:Stun N}{U:Bkg (More N)}{S:Support (More N)}, Shell S T U X c→Slow 1 (hook T) q→0<c→c≤κ→∃ (f:ℝ→Bkg (More N))(g:ℝ→Stun N), f 0=1 ∧ g 0=T ∧ Agrees S (f c) U ∧ AgreeF S (g c) X ∧ ∀ y∈ ball (0:ℝ) (2*c),TransK 1 f y K∧ Guard (f y) d ∧ seek g 1 y K ∧ Slow (f y) (hook (g y)) r -- tune precedence
lemma soluble {S:Support (More N)}{T X:Stun N}{U:Bkg (More N)}(p:Shell S T U X q)(t:0≤q): ∃ (V:Bkg (More N))(g:Mach (More N)), Agrees S V U∧AgreeF S (feast g T) X∧lawnK V 1 q∧ ∀ i,Cube.cmp firstF (g i) 1 ≤ q:=by
 let V(z:Link (More N)):=if z∈leaks S then U z else 1; choose g a b using p.rods; let v(i):= if h:i∈S then g i h else 1; refine ⟨V,v,fun i v u=>?_ ,fun i u=>?_,fun i=>?_,fun i=>?_⟩
 · exact if_pos (mem_filter.mpr ⟨mem_univ _,v,u⟩)
 · unfold feast v; rw [dif_pos u]; exact (a i u).symm
 · unfold V; split; next h => obtain ⟨b,v⟩:=mem_filter.mp h|>.2; exact p.tag i b v
   next h=> exact (Cube.cmp_id ..).le.trans t
 unfold v; split; next h=> exact b i h
 next h=> exact (Cube.cmp_id ..).le.trans t
lemma walkX {N : Side}{κ :ℝ}(h:∀ (N:Side) (U V:Bkg N)(k:ℝ),0<k→k ≤ κ→lawnK U V k → ∃ p:ℝ→Bkg N,p 0=U ∧ p k=V ∧ ∀ y∈ ball (0:ℝ) (2*k), TransK 1 p y K ∧ lawnK (p y) U (K*|y|))(p:0< a)(w:a≤κ)(V:Mach (More N))(T: ∀ i,Cube.cmp firstF (V i) 1 ≤ a): ∃ A:ℝ→ Mach (More N), A 0=1 ∧ A a=V ∧ ∀ y∈ball (0:ℝ) (2*a), (∀ i,Allows 1 (fun t=>SU.fund (A t i)) y K) ∧ ∀ i,Cube.cmp firstF (A y i) 1 ≤ K*|y|:=by
 obtain ⟨G,g,v,W⟩:=h (More N) 1 (fun i=>V i.1) a p w (car_v (fun i=>T i.1)); exact ⟨ fun t i=> G t (i,0),funext fun i=>congrFun g (i,0),funext fun i=>congrFun v (i,0),fun i t=>⟨fun j=>(W i t).1 (j,0),fun j=>(W i t).2 (j,0)⟩⟩
lemma grows (h:0<d)(u:q<r):∃ κ K:ℝ, plot q r d κ K:=by
 obtain ⟨K,M,G,p,f⟩:= Pic.allure; obtain ⟨b,e,W⟩:= Pic.boost d h; have he:0<K:=zero_lt_one.trans_le G; have hx:0<r-q:=sub_pos.mpr u
 let κ:=min M (min (b/(2*K)) ((r-q)/(6*K))); have hκ:=lt_min p (lt_min (div_pos e (by positivity:0<2*K)) (div_pos hx (by positivity:0<6*K))); refine ⟨κ,K,hκ,G,?_⟩; intro N c T X U S v s cH c0
 obtain ⟨V,Z,hU,hZ,gA,zF⟩:= v.soluble cH.le; have ht:c≤M:=c0.trans (min_le_left ..); obtain ⟨p,v,uY,B⟩:=f (More N) 1 V c cH ht (car_v gA); obtain ⟨L,v',w,C⟩:=walkX f cH ht Z zF; refine ⟨p,fun y=> feast (L y) T,v,?_,uY.symm ▸ hU,(show AgreeF _ (feast (L c) T) X from w.symm ▸ hZ),fun y hy=>?_⟩; dsimp only; rw [v']; exact Meadow.shuffle_one _ -- tune includes horror
 have ha:|y| < 2*c:= mem_ball_zero_iff.mp hy; have hb:b ≥ 2*K*c:=by have hz:= (le_div_iff₀ (by positivity:0<2*K)).mp (c0.trans ((min_le_right ..).trans (min_le_left ..))); linarith
 have hd:r ≥ q+6*K*c:=by have hx:= (le_div_iff₀ (by positivity:0<6*K)).mp (c0.trans ((min_le_right ..).trans (min_le_right ..))); linarith
 let v:= (B y hy); let u:=(C y hy); refine ⟨v.1,W (More N) (p y) (fun i=>(v.2 i).trans (by nlinarith)),seek_pose _ _ y u.1,fun x i=> (slow_feast T v.2 u.2 s x i).trans_le (by nlinarith)⟩
end Shell
end YM.CF.BPress.Nougat
