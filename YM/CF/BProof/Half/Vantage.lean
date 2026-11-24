import YM.CF.BProof.Half.Aspect
import YM.CF.BProof.Mote.Plan
import YM.Push.GRID_APPROXIMATION.Cone
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide.Half
open Function NormedSpace Lattice Wilson Lat SU Fock Cube Mir Finset Spire Skye Rush
open RG
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N P:Side}(i:Axis) {a b c s:ℕ}
variable {R:Patch} (G:Ratio N P)
structure ClockD (R:Patch)(d l k:ℕ) where
 gF:ℕ -- true support margin
 pF:ℕ -- repair support margin
 uF:ℕ -- ferm margin
 pos:0<gF
 visor:d=gF+4
 duty:l+gF≤pF
 trueCare: Push.GridApprox.reach R+gF ≤ gF*R.L.val
 help: R.L.val+1+pF ≤ pF*R.L.val
 send:2*k+uF ≤ uF*R.L.val
 born: pF ≤ uF
 root:2*k+ R.L.val +(pF+2)*R.L.val ≤ uF*R.L.val
namespace ClockD
open Push.GridApprox
variable {d l k:ℕ}
lemma lucky (R:Patch)(l k d:ℕ)(p:10*(R.J+10)≤d)(v:20*d<R.L.val): Nonempty (ClockD R d l k):=by
 let L:= R.L.val; have hv:2≤ L:=by unfold L; omega
 let a:=d-4; have ha:0<a:=by unfold a; omega
 have he: Push.GridApprox.reach R=10*(R.J+3)*L:=by unfold Push.GridApprox.reach Patch.radius L; ring
 have hx:10*(R.J+3)+1≤ a:=by unfold a; omega
 let b:=l+a+ (L+1); let c:=b+3+2*k
 have h(x:ℕ):2*x ≤ x*L:=by rw [mul_comm]; exact Nat.mul_le_mul_left x hv
 refine ⟨a,b,c,ha,(by unfold a; omega),(by unfold b; omega),?_,(by have :=h b; unfold b L at *; omega),(by have := h c; unfold c L at *; omega),(by unfold c; omega),?_⟩
 · rw [he]; have ht : 10*(R.J+3)*L+1*L ≤ a*L:=by rw [←add_mul]; exact Nat.mul_le_mul_right _ hx
   change _≤ a*L; have hz:a≤L:=by unfold a L; omega
   omega
 change 2*k+L+(b+2)*L ≤ c*L; unfold c; rw [add_mul,add_mul (b+3),add_mul b]; have he:=h (2*k); omega
variable (X:ClockD R d l k) (hg:G.count=R.L)(q:Bool)
include X hg
local notation "Xs"=> shade N i q X.gF
local notation "Ys"=> shade N i q X.pF
local notation "Zs"=> shade N i q X.uF
local notation "Zy"=> Leg.reach G Zs k
lemma trueW (x:Seat N)(u:x∈Xs): Push.GridApprox.window ((ratio G).embed x) (Push.GridApprox.reach R) ⊆ shade P i q X.gF:=by
 rintro y ⟨w,r,rfl⟩; refine moveS i q ((embedW i G q x).2 u) ?_ (by rw [hg]; exact X.trueCare); rw [separation_comm,separation,add_sub_cancel_right]; exact Work.E01.pdist_wrap_le r
lemma fern: Leg.reach G Zs k ⊆ shade P i q X.uF:=by intro x h; obtain ⟨y,v,w⟩:=halo_spec.mp h; obtain ⟨t,u,rfl⟩:= mem_image.mp v; exact moveS i q ((embedW i G q _).2 u) w (hg ▸ X.send)
private lemma parN{z:Seat P}: separation z ((ratio G).embed ((ratio G).parent z)) ≤ R.L.val:=by
 have ht:= Corona.near (ratio G) z; change 2*_ ≤ G.count.val at ht; rw [hg] at ht; omega
lemma ripley : halo 2 ((Leg.reach G Zs k).image (ratio G).parent) ⊆ Ys :=by
 intro t h; obtain ⟨v,A,h⟩:=halo_spec.mp h; obtain ⟨x,hF,rfl⟩:= Finset.mem_image.mp A; obtain ⟨y,a',g⟩:=halo_spec.mp hF; obtain ⟨z,f,rfl⟩:= Finset.mem_image.mp a'
 have hp: separation ((ratio G).embed z) ((ratio G).embed ((ratio G).parent x))≤ 2*k+R.L.val:=(separation_triangle _ x _).trans (Nat.add_le_add g (parN G X hg)); have hx: (ratio G).parent x∈shade N i q (X.pF+2):=(embedW i G q _).1 (moveS i q ((embedW i G q z).2 f) hp (by rw [hg]; exact X.root)); exact moveS i q hx h (by omega)
lemma kids (e:Edge (Seat P))(h:(ratio G).parent e.1 ∈ Ys): ends e ⊆ shade P i q X.pF:=by
 intro x p; let U:=(ratio G).embed ((ratio G).parent e.1); have he:= (embedW i G q _).2 h; have hv : separation U e.1 ≤ R.L.val:= (separation_comm ..).trans_le (parN G X hg); refine moveS i q he (b:=R.L.val+1) ?_ (hg ▸ X.help); simp only [Skye.ends,mem_insert,mem_singleton] at p; apply (separation_triangle U e.1 x).trans; refine Nat.add_le_add hv ?_; rcases p with p|p; rw [p]; simp; rw [p]; exact Work.E01.sep_step_le _ _
end ClockD
lemma mirrorLeg (k:ℕ) (V:Support (More N)) : regionD (Fixed.reflectSweep P i) (Leg.reach G V k)=Leg.reach G (regionD (Fixed.reflectSweep N i) V) k:=by
 let T (n):=Fixed.reflectSweep n i; have he(n:Side) : (boxA (T n)).symm=(boxA (T n)) :=by rw [←sitU, show (T n)⁻¹=T n from Fixed.inv_reflectSweep i]
 unfold Leg.reach regionD; rw [he,he,←paysT]; congr 1; rw [map_eq_image,map_eq_image,image_image,image_image]; refine congr_arg (fun f:_=>V.image f) (funext fun x=>?_); change boxA (T P) _= (ratio G).embed (boxA (T N) x); unfold T; simp only [Fixed.box_reflect,Ratio.signed] -- tune
end YM.CF.BProof.Bide.Half
