import YM.CF.Haro.Torch
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
variable {c f:Side}(G:Ratio c f)(h: Odd G.count.val)
open Branch Laic
variable {t:ℝ}(p:0<t)(Y: cro G t)(W: Meter TailB G t)
open Skye Precision
open Jet Scree
-- open kernel PH transport
variable (g:Seat f→SU.E)(Z:Rill.Arch G t)
lemma hover_G : bring p (herb G g Z)=(Urn.hall G t).drive g (bring p Z):=by apply Subtype.ext; change (unionP (july G g Z.val.1),Tulip.profile (gauge g Z.val.2))=_; rw [Peaks.jig,Tulip.profile_g]; rfl
private lemma arch_l (A:Op (Single f))(F: Op (Iota G)) : arch G (foot G A * F)= A*arch G F:=by ext i j; change (foot G A * F) _ _=_; rw [Matrix.mul_apply,Matrix.mul_apply,←Equiv.sum_comp (switchG G)]; apply sum_congr rfl; intro m _; unfold arch; rw [Matrix.of_apply,Equiv.symm_apply_apply]; rw [foot]; simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply]
lemma chant_g (F:Op (Iota G)): arch G (F*((pinH G t false).run g).val)= arch G F*(tradew c (Peaks.scaleG G g)).val:=by
 let Y(x:Single f):= (switchG G).symm x
 let Q:= ((pinH G t false).run g).val; let V:=(tradew c (Peaks.scaleG G g)).val
 ext x y; obtain ⟨⟨m,i⟩,a⟩:=y; let z:Single c:=((m,i),a)
 change (F*Q) (Y x) (patchQ G z)= (arch G F*V) x z
 have ht (B:SU.Slot): (patchQ G ((m,i),B)).1=(m,0,i):=rfl
 rw [Matrix.mul_apply,Matrix.mul_apply,Fintype.sum_prod_type (fun z:Iota G=> _*Q z _), Fintype.sum_prod_type (fun j:Single c=> _*V j z), Finset.sum_eq_single (ι:=Site c×St G.count) (m,0,i), Finset.sum_eq_single (ι:=Site c × SpinIdx) (m,i)] -- tune sum eq RHS
 · apply sum_congr rfl; intro j _; congr 1; change jump (Equiv.refl _) (fun i=>(spur G g i).val) ((m,0,i),j) ((m,0,i),a)= _; unfold V; rw [jump_apply]; simp only [Equiv.refl_apply,ite_true,z,tradew,jump_apply]; rfl -- tune
 · intro k _ h; apply sum_eq_zero; intro j _; simp [z,V,tradew,jump_apply,h,Ne.symm h]
 · simp
 · intro k _ h; apply sum_eq_zero; intro j _; rw [mul_eq_zero]; right; change jump (Equiv.refl _) (fun i=>(spur G g i).val) (k,j) ((m,0,i),a)=0; simp [jump_apply,h,Ne.symm h] -- tune
 simp
abbrev fyL(G:Ratio c f){t:ℝ}(i:Bool)(W: Meter TailB G t)(x:cro G t)(X:Support (More f))(a:Prism.Rock f)(b:Prism.Rock c):Op Slot:= Matrix.of fun u v=>openQ G x W X i (a,u) (b,v)
abbrev putX {n:Side}(g:Seat n→SU.E)(x:Prism.Rock n):=mater (g (node x.1))
include p
lemma marchG (x:Rill.Arch G t)(i:Bool)(C:Toll (Iota G))(S: Support (More f))(q:Suite (badge _) (pinH G t true) (pinH G t false) S C (W (true,i) S))(a:Prism.Rock f)(b:Prism.Rock c) : fyL G i W (bring p (herb G g x)) S a b * putX (Peaks.scaleG G g) b= putX g a * fyL G i W (bring p x) S a b:=by
 let Y(p:cro G t):= W (true,i) S p; let U:=bring p x; let Z:=bring p (herb G g x); let Q:=tradew c (Peaks.scaleG G g)
 have hu:Y Z*((pinH G t false).run g).val=foot G (tradew f g).val*Y U:=by rw [show Z=_ from hover_G G p g x]; exact (q.frame ..)
 have hv:arch G (Y Z)*Q.val=(tradew f g).val * arch G (Y U):=by rw [←chant_g, ←arch_l,hu]
 ext u v; have hx:= Matrix.ext_iff.mpr hv (a,u) (b,v); rw [Matrix.mul_apply,Matrix.mul_apply,Fintype.sum_prod_type, Fintype.sum_prod_type (fun j:Single f=> _*arch G (Y U) j _),Finset.sum_eq_single b,Finset.sum_eq_single a] at hx -- tune order matches
 · rw [Matrix.mul_apply, Matrix.mul_apply] -- desired sum
   unfold Q at hx; simp only [tradew,jump_apply,Equiv.refl_apply, ite_true] at hx; exact hx
 · intro y _ h; apply Finset.sum_eq_zero; intro i _; simp [tradew,jump_apply,h,Ne.symm h]
 · simp
 · intro y _ h; apply Finset.sum_eq_zero; intro i _; simp [Q,tradew,jump_apply,h,Ne.symm h]
 simp
end YM.CF.Haro
