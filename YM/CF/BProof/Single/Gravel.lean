import YM.CF.Moire.Niche
import YM.CF.Vale.Honor
import YM.CF.BProof.Single.Stone

/-! Purchases before choosing d, uniform across permitted Choice of Interest. For shear
use the Aim *analytic* local-price certificate (in particular proves the connected
support price for cavil with its winding legs), shrinking d via Tulip local axial,
trivial zero. This uses locality & tickets, not a denominator lower bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Spin
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Stint Moire Laic
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {a b l r :ℝ}(p:0<a)(q:0<b)(u:0<l)(v:0<r)
abbrev Buyer (a b l r:ℝ)(N:Side) := { A:Aim N // A.toll a b l r }
abbrev Bourse (a b l r:ℝ) := ∀ N:Side, Buyer a b l r N
include p q u v
lemma fundsAim : ∃ z c d:ℝ, 0<z∧0<c∧0<d∧∃ V:ℕ,shelf (fun (i:Bourse a b l r) N=>bloom (i N).val) z c V d :=
 terrace (P:=fun (i:Bourse a b l r) N=>(i N).val) u.le v.le p q (fun i n=>(i n).property)
omit p q in
def market {N:Side}(U: Buyer a b l r N): Bourse a b l r:= update (fun i:Side=>(⟨⟨0,0⟩,Vale.empty_pay u.le,Vale.empty_pay v.le⟩: Buyer a b l r i)) N U -- inline flatten
lemma wallet : ∃ z c d:ℝ, 0<z∧0<c∧0<d∧∃ V:ℕ, (∀ {n:Side},V≤n.val→∀ U:Buyer a b l r n,Solo z c (bloom U.val) d) ∧ ∀ f:ℝ, 0<f →∃ x:ℝ, 0<x ∧ ∃ j:ℕ, ∀ {n:Side}, j≤ n.val → ∀ U:Buyer a b l r n, ∀ B:Bkg (More n), Guard B x → ‖U.val.den B‖ ≤ f:=by
 obtain ⟨z,c,d,h,e,hp,V,Q⟩:= fundsAim p q u v
 refine ⟨z,c,d,h,e,hp,V,fun {n} t U=> by simpa only [market,update_self] using (show Solo z c (bloom ((market u v U n).val)) d from Q (market u v U) n t),fun f t=>?_⟩
 obtain ⟨i,m,he,ht,-,-,w,H⟩:= Lively.estate Q h hp e f t (fun i N _=>bloom_zero (i N).val); refine ⟨m,ht,w,fun {n} k S X h=>?_⟩; have hx: Solo i f (bloom ((market u v S n).val)) m:= H (market u v S) n k; simp only [market,update_self] at hx; let x: Openc (More n) m:= ⟨profile X,X,h,by simpa⟩; rw [← bloom_P]; exact hx.lib.boundOp he.le x
/-- Uniform in all qualifying levels here. W.C guarantees CardK along permitted histories. -/
structure Ready (j:ℕ)(a b l r:ℝ) where
 hP : Pay
 hT : ℝ
 hTpos : 0<hT
 minN : ℕ
 mat (N:Side)(q:minN≤N.val)(M:Male)(d:ℝ)(u:d≤hT) : Earn hP (iron N hT d).mark (iron N hT d).mark (fun x=> spar j M x.val) -- notation j_*
 tilt (N:Side)(q:minN≤N.val)(U:Buyer a b l r N)(d:ℝ)(u:d≤hT) : Earn hP (iron N hT d).mark (iron N hT d).mark (fun x=> U.val.den x.val)
 proj (N:Side)(q:minN≤N.val)(M:Male)(X:Bkg (More N)) (p:Guard X hT): IsStarProjection (spar j M X)
 small (ε:ℝ)(q:0<ε): ∃ d:ℝ,0<d ∧ ∃ n:ℕ, ∀ (N:Side)(q:n ≤ N.val)(U:Buyer a b l r N) (X:Bkg (More N)), Guard X d → ‖U.val.den X‖≤ ε
lemma ready (j:ℕ)(h:1≤j) : Nonempty (Ready j a b l r) := by
 obtain ⟨z,c,d,hz,hc,hd,V,F,U⟩:= wallet p q u v; obtain ⟨Z,C,D,hZ,hC,hD,n,P⟩:= funde_s j h; obtain ⟨m,g,k,Gm⟩:= funde_q j h; let s:Pay:= ⟨z,c,hz,hc⟩; let t: Pay:=⟨Z,C,hZ,hC⟩; let w:=lt_min hd (lt_min hD g); refine ⟨s.lodge t,min d (min D m),w,max (max V n) k,fun N h M _ g=>?_,fun N h S _ g=>?_,fun N h M X hp=>Gm M N (by omega) X (hp.shrink ((min_le_right ..).trans (min_le_right ..))),?_⟩
 · exact (drill (k:=t) (axis_down Z C (P M N (by omega)) _ w ((min_le_right ..).trans (min_le_left ..))) w g).change (Pay.lodge_right ..)
 · simpa only [Moire.bloom_P] using (drill (k:=s) (axis_down z c (F (by omega) S) _ w (min_le_left ..)) w g).change (Pay.lodge_left s t)
 intro x g; obtain ⟨i,y,N,X⟩:= U x g; exact ⟨i,y,N,fun n hz U p g=>X hz U p g⟩
omit p q u v in
@[simp] lemma den_void {N:Side}(U:Aim N) : U.den 1=0:= by rw [←bloom_P,profile_trivial]; apply bloom_zero
end YM.CF.BProof.Spin
