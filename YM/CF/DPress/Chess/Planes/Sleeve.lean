import YM.CF.DPress.Chess.Planes.Wedge
import YM.CF.DPress.Chess.Lift.Rake
import YM.CF.Scroll.Loma
/-!
 An actual operator reflection. Involutive already on generators because of the *two* i's and the signed Pin square. No use of seam relocation here. Seek top conventions separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.DPress.Chess
open Function Lattice Filter Fock Spire Skye Scroll Lat Rush Wilson MeasureTheory ProbabilityTheory Fixed Tulip SU
open Cube (More assembly node)
open scoped Topology BigOperators NNReal ENNReal Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
namespace Wall
variable (W:Wall){n m:Side}
abbrev Ζ (n:Side): UNI (Single n):= Print.ψθ W.shape (Fixed.pinSpin W.i) n
lemma Ξjet : JetS W.shape.s false true (Fixed.pinSpin W.i):= mirrorX ..
private lemma mark_κ (n:Side) : prepU (Nacre.lagX 0) 1 inert n = 1 :=by
 let x:=prepU (Nacre.lagX 0) 1 inert n; apply mul_left_cancel (a:=x); rw [mul_one]; change (prepU _ 1 _ _)*_ = _; rw [Nacre.kio n,mul_one,Nacre.joinX]; unfold Nacre.lagX; simp; rfl
lemma ξsq (n:Side) : (W.Ζ n).val*(W.Ζ n).val= -1:=by
 change (W.Ζ n* W.Ζ n).val=_; rw [Ζ,Print.ψθ,Nacre.kio n,W.joins]; let X:=Nacre.lagX 0; let v:=pinSpin W.i; have hx: (v*v).val= (-1:ℂ) • (1:UNI SpinIdx).val:= (Mir.pin_square W.i).trans (neg_one_smul ..).symm; rw [Nacre.Ygs _ _ _ hx,mark_κ n,neg_one_smul]; rfl
lemma ξwear (S:Support (More n)) : twist (W.Ζ n) (cutM (matterRegion n S))= cutM (matterRegion n (W.negZ S)):=by
 apply Mir.twist_comm; let M:= Tofu W.shape n; ext ⟨⟨x,i⟩,j⟩ ⟨⟨y,k⟩,l⟩; simp only [cutM, Matrix.mul_diagonal, Matrix.diagonal_mul, mem_matterRegion]; let f(x:Site n):=(milU W.shape (pinSpin W.i) inert x).val; change (jump M f) (x,i,j) (y,k,l)*_=_*(jump M f (x,i,j) (y,k,l)); rw [jump_apply]
 by_cases h:M x=y; swap; · rw [if_neg h,zero_mul,mul_zero]
 subst y; rw [if_pos rfl]; have he:node x∈ W.negZ S ↔ node (M x)∈S:= by rw [W.swipe,show W.site _ (node x)=node (M x) from (W.anon _).symm.trans (W.shape.nodex x).symm]
 split_ifs with a b b <;> simp <;> first | exact (b (he.mpr a)).elim | exact (a (he.mp b)).elim
abbrev θ (n:Side):= theta (W.Ζ n)
abbrev ξS {u}: Finset (Single u)→ Bool→FC (Single u)→ Prop:= Sector
lemma θ_cost (n:Side)(x: FC (Single n)): ‖W.θ n x‖=‖x‖:=by rw [θ,theta,twist_norm,norm_cc] -- Scroll.norm_cc
lemma θsec {A:Finset (Single n)}{x: FC (Single n)}{b:Bool}(p:Sector A b x): W.θ n (W.θ n x)=x:= theta_twice _ (W.ξsq _) p
lemma θwalk {A: Support (More n)}{x:FC (Single n)}{b:Bool}(p:Sector (matterRegion n A) b x) : Sector (matterRegion n (W.negZ A)) b (W.θ n x):= theta_carries _ p (W.ξwear A)
abbrev θt(n:Side):FC (Single n) →L[ℝ] FC (Single n) := ⟨⟨⟨W.θ n,theta_add _⟩, (fun a x=>theta_rsmul _ x a)⟩,theta_cont _⟩ -- tune
@[fun_prop] lemma θ_c(n:Side) : Continuous (W.θ n):=theta_cont _
lemma boostU {x}: (W.boost x).Ζ m= Print.ψθ (W.boost x).shape (pinSpin W.i) m:=rfl
end Wall
end YM.CF.DPress.Chess
