import YM.CF.Spire.Eager
set_option autoImplicit false
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Scroll Mir SU Drapes
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {g:E}{b c:Bool}
def polarX (b:Bool)(x:E):E:=dite (b=true) (fun p=>⟨ccU x.val,by
 change Matrix.det (cc (fund x))=1; rw [cc,Matrix.det_transpose, Matrix.star_eq_conjTranspose,Matrix.det_conjTranspose, fund_det,star_one]⟩) fun _=>x
lemma polar_val(b:Bool)(g:E) : fund (polarX b g)= windX b (fund g):=by cases b <;> rfl
lemma fund_inj: Injective fund:=SU.group.mat_injective -- tune
def polarT (b:Bool): E ≃* E where
 toFun:=polarX b
 invFun:= polarX b
 left_inv x :=fund_inj (by rw [polar_val,polar_val]; cases b; rfl; exact cc_cc _)
 right_inv x:= fund_inj (by rw [polar_val,polar_val]; cases b; rfl; exact cc_cc _)
 map_mul' x y:=fund_inj (by rw [polar_val,fund_mul, win_m,fund_mul,polar_val,polar_val])
lemma polar_t (b c:Bool)(x:E): polarT b (polarT c x)=polarT (b.xor c) x:= by apply fund_inj; change fund (polarX b (polarX c x))=fund (polarX _ _); rw [polar_val,polar_val,polar_val]; cases b<;> cases c <;>simp [windX]
lemma dove_sub (x y:Vect)(b:Bool): dove b (x-y)=dove b x-dove b y:=by cases b; rfl; apply PiLp.ext; intro i; change star (x.ofLp i-y.ofLp i) = star (x.ofLp i) - star (y.ofLp i); rw [star_sub]
lemma doveT (b c:Bool)(x:Vect): dove b (dove c x)=dove (b.xor c) x:=by apply PiLp.ext; intro i; cases b<;>cases c <;> simp [dove,cSignX]
lemma doveN(x:Vect)(b: Bool): ‖dove b x‖=‖x‖:=by cases b; rfl; rw [←sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),← inner_self_eq_norm_sq (𝕜:=ℂ),← inner_self_eq_norm_sq (𝕜:=ℂ),dove_dot,inner_self_eq_norm_sq_to_K]; simp [cSignX] -- tune type finite ℂ
lemma bib (z:Ballot): ‖z.val‖=1:=by simpa [Sphere] using z.property
def doveV(b:Bool)(x:Ballot):Ballot:=⟨dove b x.val,by simp [Sphere,doveN,bib] ⟩
lemma dove_v(b c:Bool)(x:Ballot): doveV b (doveV c x) = doveV (b.xor c) x:=Subtype.ext (doveT _ _ _)
def polarV (b:Bool) :Ballot≃ᵢ Ballot where
 toFun:=doveV b
 invFun:=doveV b
 left_inv x:= (dove_v b b x).trans (by simp; rfl)
 right_inv x:= (dove_v b b x).trans (by simp; rfl)
 isometry_toFun:=by refine Isometry.of_dist_eq ?_; intro x y; rw [Subtype.dist_eq,Subtype.dist_eq,dist_eq_norm,dist_eq_norm]; change ‖dove b _-dove b _‖= _; rw [←dove_sub,doveN]
lemma matterX (b:Bool)(x:E):(matter (polarT b x)).val=windX b (matter x).val:=by
 change triple (fund (polarX b x))=_; rw [polar_val,matter_matrix]; unfold triple; cases b; rfl
 change (1:Op _)⊗ₖ each (cc _) =cc _; rw [op_cc_kron,cc_one]; congr 1; ext i j; cases i<;>cases j <;> simp [each,Join.both,ExTwo.wedge_entry] -- tune
lemma full_dove (b:Bool)(x:Ballot): SU.Pair.fullM (doveV b x).val=windX b (Pair.fullM x.val):=by
 cases b; rfl
 let f:=x.val; let z:Vect:=WithLp.toLp 2 Pair.e0
 have hv:dove true z=z:=by apply PiLp.ext; intro i; change star (Pair.e0 i)=_; by_cases h:i=0<;>simp [z,Pair.e0, Pi.single_apply, ExTwo.basisVec,h, Ne.symm]
 have hz:cc (Pair.fullM z)=Pair.fullM z:=by
   unfold Pair.fullM; rw [op_cc_kron,cc_one]; congr 1; change cc (Pair.pairM Pair.e0)=_; ext i j; rw [cc_apply, ←Pair.seed_eq]; simp
 obtain ⟨v,he⟩:=Pair.reachable x.val (bib x)
 have ht: x.val =acts (fund v) z:= (WithLp.ofLp_injective 2) he.symm -- order?
 change Pair.fullM (dove true x.val)= cc (Pair.fullM x.val); rw [ht,dove_acts, hv,← polar_val, Pair.full_cong, Pair.full_cong,cc_mul,cc_mul,hz,show (matter (polarX true v)).val=cc (matter v).val from matterX true v]; rfl

def xtra(b:Bool):ColorT b where
 lens:=polarT b
 V:=1
 X:=polarV b
 trek x z:=Subtype.ext (by change dove b (acts (fund x) _) = acts (fund (polarX b x)) _; rw [dove_acts,polar_val]; rfl)
 shore x:= by rw [singT,one_des]; exact matterX b x
 born x y:=by change ‖fund (polarX b x)- fund (polarX b y)‖=_; rw [polar_val,polar_val,←win_l]; cases b; rfl; exact norm_cc _ -- ambiguous
 facing x:=by simp only [congrC, OneMemClass.coe_one,transpose_one,mul_one,one_mul]; exact full_dove b x
end YM.CF.Spire
