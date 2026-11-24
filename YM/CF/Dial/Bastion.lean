import YM.CF.Dial.Keys
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
section
variable {n:Type*}[Fintype n][DecidableEq n]{P C N A:Op n}
lemma nearT {X Y: Op n}{r:ℝ}(e:IsStarProjection P)(h:IsUnit (stage P X))(k:‖(stage P X)⁻¹‖≤r):
 ‖relay P X Y-1‖ ≤ ‖Y-X‖*r:=by
 nth_rw 1 [← relay_base e h]; unfold relay; rw [add_sub_add_right_eq_sub,←sub_mul,show body P Y-body P X=P*(Y-X)*cc P by rw [body,body,mul_sub,sub_mul]]
 apply (norm_mul_le ..).trans
 refine mul_le_mul ?_ k (norm_nonneg _) (norm_nonneg _)
 have hp:= e.norm_le P; apply (norm_mul_le ..).trans; apply le_trans (mul_le_of_le_one_right (norm_nonneg _) ((ccProj e).norm_le _)); exact (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) hp)
lemma lure {x y:ℝ}{m R:ℝ}(hm:0<m)(h:|y-x|≤1/m)(hb: ‖victory P A C N-C‖ ≤R): ‖straightC P A C N y-straightC P A C N x‖≤ R/m:=by
 rw [show straightC P A C N y-straightC P A C N x= (↑(y-x):ℂ) • (victory P A C N-C) by rw [straightC,straightC]; push_cast; module,norm_smul,Complex.norm_real, Real.norm_eq_abs]
 exact (mul_le_mul h hb (norm_nonneg _) (by positivity)).trans_eq (by ring)
lemma straight_skew (p:IsStarProjection P)(h:Cᵀ= -C)(g:Aᵀ= -A)(t:ℝ): (straightC P A C N t)ᵀ= -straightC P A C N t:=by
  have hx: (victory P A C N)ᵀ= -victory P A C N:=by rw [victory, Matrix.transpose_add, skew_form g, body_skew p.one_sub h]; abel
  rw [straightC,Matrix.transpose_add,Matrix.transpose_smul, Matrix.transpose_smul,h,hx]; simp; abel
end
variable {ι:Type*}{L:Side}{ho:Odd L.val}{P A K:Chop ι}
def tonic (P A:Chop ι)(i:ι) {N F:Side}(G: Ratio N F)(U:Bale N F) :=straightC (P i G U) (squareD G true U) (squareD G false U) (A i G U)
def Joy (L:Side)(P A:Chop ι)(m:ℕ) :=Still L fun G x=>∀ i (t:TickZ),
 let S:=P i G (post x); let V:=tonic P A i G (post x);
 IsUnit (stage S (V t.val)) ∧ ∀ z:TickZ, |z.val-t.val| ≤ 1/(m:ℝ)→ ‖relay S (V t.val) (V z.val)-1‖ ≤ 1/2
namespace Land
variable (h:Land L P A K)
include h
lemma youth (ho:Odd L.val):∃ m:ℕ,0<m∧ Joy L P A m:=by
  obtain ⟨s,p,F⟩:= ((h.helper ho).1).assets; obtain ⟨R,hR,H⟩:= ((h.loft ho).sub (tablesB _ false L ho)).assets
  obtain ⟨m,g⟩:= exists_nat_gt (R*s*2); have hp:0<(m:ℝ):= (show 0<R*s*2 by positivity).trans g
  refine ⟨m,Nat.cast_pos.mp hp, (h.sky.plus (F.gilded.plus ((interest_g (h.helper ho).2).gilded.plus H.gilded))).forward ?_⟩
  intro N N' G hC U hh i t; obtain ⟨hZ,M,B,V⟩:=hh -- shadow P?
  let b:= (post U); let T :TickZ:=t
  have hr:=V i
  let S:=P i G b; let Q:=tonic P A i G b
  have he(v:TickZ): zL P A (i,v) G b=stage S (Q v.val):=by rw [show b=post U from rfl,zL_at,lane_at]; rfl
  have hh:IsUnit (stage S (Q t.val)):=he t ▸ B (i,t)
  have hy : ‖(stage S (Q t.val))⁻¹‖≤s:=by rw [←he]; exact M _
  have hl: soar P A i G b=victory S (squareD G true b) (squareD G false b) (A i G b):=by unfold S b victory body soar; rw [charge_p]
  have hv: ‖victory S (squareD G true b) (squareD G false b) (A i G b)-squareD G false b‖ ≤ R:=by rw [←hl]; exact hr
  refine ⟨hh,fun z hx=>?_⟩
  apply _root_.le_trans (nearT (hZ i).1 hh hy); apply _root_.le_trans (mul_le_mul_of_nonneg_right (lure hp hx hv) p.le)
  rw [div_mul_eq_mul_div, div_le_iff₀ hp]; linarith
end Land
end YM.CF.Dial
