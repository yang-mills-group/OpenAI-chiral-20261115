import YM.CF.Levier.CrestD
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Spire Nacre
-- analytic profiles under affine pullback incl sail seams
variable {N:Side}(b:Bool)(a:Shape)
open Urn
variable {P: Side}(G:Ratio N P)(h: Odd G.count.val)(e:ℝ)(k:Sweep N)(q:Shape)
local notation "κ"=> (Iota G)
variable (g:Site (More P)→E)
lemma tag_r (x y:Single N): ((torch G e).run g).val (patchQ G x) (patchQ G y) = (tradew N (scaleG G g)).val x y:=by
 rcases x with ⟨⟨x,i⟩,u⟩; rcases y with ⟨⟨y,j⟩,t⟩; change jump (Equiv.refl _) (fun i=> (spur G g i).val) ((x,0,i),u) ((y,0,j),t)= jump (Equiv.refl _) (fun i=> (matter (scaleG G g (node i.1))).val) ((x,i),u) ((y,j),t); rw [jump_apply,jump_apply]; simp; rfl -- tune
lemma destN (x:Single N)(i:κ)(p:i∉lows (patchQ G)): ((torch G e).run g).val (patchQ G x) i=0:=by
 rcases x with ⟨⟨x,j⟩,u⟩; rcases i with ⟨⟨z,i,k⟩,t⟩; change jump (Equiv.refl _) (fun i=> (spur G g i).val) ((x,0,j),u) ((z,i,k),t)= _; rw [jump_apply,if_neg]; rintro h; change (_,_)=_ at h; simp at h; obtain ⟨rfl,h,rfl⟩:=h; subst i; exact p (coil_hit (patchQ G) ((x,j),t)) -- tune false
lemma metro_r(W:Op κ): marge G (((temper G e).run g).val * W * star ((torch G e).run g).val)=suburban false ((temper G e).run g) (tradew N (scaleG G g)) (marge G W):=by
 unfold marge suburban; ext i l; let A:= ((temper G e).run g).val* W
 change (A* star ((torch G e).run g).val) i (patchQ G l)= _; rw [Matrix.mul_apply, Matrix.mul_apply,← sum_subset (subset_univ (lows (patchQ G)))]; swap; · intro k _ v; change _*star (((torch G e).run g).val _ _)=_; rw [destN G e g _ _ v,star_zero,mul_zero] -- tune
 unfold lows; rw [sum_map]; apply sum_congr rfl; intro j _; change _*star (((torch G e).run g).val _ (patchQ G j))=_*star ((tradew N _).val l j); rw [tag_r]; congr 1
variable (W:Meter Grave G e)(X:Meter TailB G e)(x:cro G e)(V: Finset (Seal (Site (More P)))) {d p w r c:ℝ}
lemma town_P(n:ℕ)(P:∀ i, OccuS G e true false n p d w (X i)):
 tendA false false ((temper G e).run g) (tradew N (scaleG G g)) (LenT G e X x V) (LenT G e X ((hall G e).drive g x) V):=by
 intro u t; obtain ⟨C,H,Q⟩:=P (u,t); unfold LenT Radix; dsimp only; rw [←metro_r G e]; rw [Finset.mul_sum,sum_mul]; simp only [Bool.xor_false]; rw [sum_congr rfl (fun i (l:i∈V)=> (H i).frame.frame g x)]; rfl
lemma vibe_s (P:∀ i, Bisca G e true true r c (heal G e W i)): playX false false ((temper G e).run g) (KinG G e W x V) (KinG G e W ((hall G e).drive g x) V):=by
 intro u v t q l; let i:Grave:=(u,v,t,q); obtain ⟨C,H,Q⟩:=P i; unfold KinG oakN; simp only [Bool.xor_false]; let BB:= (temper G e).run g; change (∑ S∈V,heal G e W i S _)+_= twist BB ((∑ S∈V,heal G e W i S x)+feeX G i); rw [map_add,map_sum]; congr 1; exact sum_congr rfl fun s _=> (H s).frame.frame ..
 -- fee comm
 unfold feeX; split; rw [twist_scalar,map_one]; rw [map_zero]
end YM.CF.Levier
