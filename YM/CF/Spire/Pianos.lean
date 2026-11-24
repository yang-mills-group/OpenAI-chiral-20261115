import YM.CF.Spire.Jot
import YM.CF.Spire.Cash
set_option autoImplicit false
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
structure Sweep (N:Side) where
 s:Signed
 b:Site N
 charge: Bool
 deriving Fintype
instance (N:Side): Mul (Sweep N):=⟨fun P Q=>⟨P.s*Q.s,P.b+P.s.act Q.b,P.charge.xor Q.charge⟩⟩
instance (N:Side): Group (Sweep N) where
 one:=⟨1,0,false⟩
 inv P:=⟨P.s⁻¹,-P.s⁻¹.act P.b,P.charge⟩
 mul_assoc a b c:=by change Sweep.mk ((_*_)*_) _ _=Sweep.mk (_*(_*_)) _ _; congr 1; exact mul_assoc ..; change a.b+a.s.act b.b+(a.s*b.s).act c.b=a.b+a.s.act (b.b+b.s.act c.b); rw [Signed.act_mul,Signed.act_add,add_assoc]; exact Bool.xor_assoc .. -- tune
 one_mul a:=by change Sweep.mk (1*a.s) (0 + Signed.act 1 a.b) (false.xor a.charge)=_; simp
 mul_one a:=by change Sweep.mk (a.s*1) (a.b + a.s.act 0) (a.charge.xor false)=_; simp
 inv_mul_cancel a:=by change Sweep.mk (_⁻¹*_) _ _=Sweep.mk 1 0 false; simp
variable {N:Side}
def castX (f:Sweep N): Shape:=⟨f.s,Lattice.lift f.b⟩
lemma stir_wrap(x:Site (More N))(a: Signed)(t u:Cover)(h:wrap N t=wrap N u) : Shape.anon ⟨a,t⟩ N x=Shape.anon ⟨a,u⟩ N x:=by
 unfold Shape.anon; simp only; have hp(T:Cover):wrap (More N) (2 • T)= (assembly N).embed (wrap N T):=(Ratio.embed_wrap (assembly N) T).symm; rw [hp,h,hp]
lemma stir_e(a:Shape)(b:Bool)(U:Bkg (More N)):stir (xtra b) (castX (Sweep.mk a.s (wrap N a.t) b)) U=stir (xtra b) a U:=by
 funext ⟨i,q⟩; have hb: wrap N (Lattice.lift (wrap N a.t))=wrap N a.t:=wrap_lift _; have hp: Shape.anon (castX (Sweep.mk a.s (wrap N a.t) b)) _ i=Shape.anon a _ i:=stir_wrap _ a.s _ _ hb
 change (posDir q).read (stir _ (castX _) U) i=(posDir q).read (stir _ a U) i; rw [veil_x,veil_x,hp]; rfl
lemma fume_e(a:Shape)(b:Bool)(x:Stun N):fume (xtra b) (castX (Sweep.mk a.s (wrap N a.t) b)) x=fume (xtra b) a x:=by
 funext i; have ht:Shape.anon (castX (Sweep.mk a.s (wrap N a.t) b)) N i=Shape.anon a _ i:=stir_wrap i a.s _ _ (wrap_lift _); rw [fume,fume,ht]
lemma stir_l (a:Sweep N)(x:Site (More N)): Shape.anon (castX a) N x=affine a.s ((assembly N).embed a.b) x:=by unfold Shape.anon; rw [show wrap (More N) (2 • (castX a).t)=_ from (Ratio.embed_wrap (assembly N) (Lattice.lift a.b)).symm,wrap_lift]; rfl
lemma stirP(a c:Sweep N)(x: Site (More N)):Shape.anon (castX a) N (Shape.anon (castX c) N x)=Shape.anon (castX (a*c)) N x:=by rw [stir_l,stir_l,stir_l]; change affine _ _ (affine _ _ _) = affine (a.s * c.s) ((assembly N).root (a.b+a.s.act c.b)) x; rw [map_add]; unfold affine; simp only [Ratio.root_embed, Ratio.signed,Signed.act_mul,Signed.act_add]; abel

def flashA(a:Sweep N)(x:Bkg (More N)):=stir (xtra a.charge) (castX a) x
def fireA(a:Sweep N)(x:Stun N):=fume (xtra a.charge) (castX a) x
lemma lights(a c:Sweep N)(x:Bkg (More N)):flashA c (flashA a x)=flashA (a*c) x:=by
 funext ⟨i,q⟩; change (posDir q).read (flashA c (flashA a x)) i= (posDir q).read (flashA (a*c) x) i; simp only [flashA]; rw [veil_x,veil_x,veil_x]; rw [stirP]
 rw [show (castX (a*c)).s=(castX a).s*(castX c).s from rfl,Step.rotate_mul]
 rw [show (xtra (a*c).charge).lens=polarT (c.charge.xor a.charge) from ?_] -- dependent lens? type fixed
 exact polar_t ..
 change polarT (a.charge.xor c.charge)=_; rw [Bool.xor_comm]
lemma firing(a c:Sweep N)(x:Stun N):fireA c (fireA a x)=fireA (a*c) x:=by funext i; unfold fireA; simp only [fume,stirP]; rw [show ∀ (x:Ballot),(xtra c.charge).X ((xtra a.charge).X x)=doveV (c.charge.xor a.charge) x from dove_v _ _, Bool.xor_comm]; rfl -- tune lambda
lemma sign_seq(x:ℂ)(b c:Bool): cSignX b (cSignX c x)=cSignX (b.xor c) x:=by cases b <;> cases c <;> simp [cSignX]
def wageZ(a: Sweep N):Bool:= a.charge.xor (detX a.s)
abbrev payZ(a:Sweep N):ℂ→ℂ:=cSignX (wageZ a)
lemma warX(a c:Sweep N)(x:ℂ):payZ a (payZ c x)=payZ (a*c) x:=by unfold payZ; rw [sign_seq]; change _=cSignX ((a.charge.xor c.charge).xor (detX _)) x; rw [show (a*c).s=a.s*c.s from rfl, det_p]; simp [wageZ, Bool.xor_comm,Bool.xor_left_comm, Bool.xor_assoc]
end YM.CF.Spire
