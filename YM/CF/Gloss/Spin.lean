import YM.CF.Mir.Funds
import YM.CF.Spire.Pianos
import YM.CF.Skye.Can
set_option autoImplicit false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gloss
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire
attribute [local instance] opCStarAlgebra
variable {m B N:Side}
abbrev Era(m:Side):= Sweep (More m)
instance {m:Side}:DecidableEq (Era m):= Classical.decEq _
instance {m:Side}:Nonempty (Era m):=⟨1⟩
local notation "Z"=> CSide m B
abbrev rBar(m B):= Mir.Trip.gaugeR m B
def netB(m B:Side) : Era m→* Sweep (CSide m B) where
 toFun x:=⟨x.s,(rBar m B).embed x.b,x.charge⟩
 map_mul' x y:=by change Sweep.mk (x.s*y.s) ((rBar m B).root (x.b + x.s.act y.b)) _=Sweep.mk _ _ _; rw [map_add]; congr 1; exact congrArg₂ (·+·) rfl (Ratio.signed (rBar m B) y.b x.s)
 map_one' :=by change Sweep.mk _ ((rBar m B).root 0) _= _; rw [map_zero]; rfl
variable (B) (x:Era m)
abbrev ωx:=x.s
abbrev px:=x.charge
abbrev turnV (x:Era m):= flashA (netB m B x)
def ψx:Equiv.Perm (Site (Domain m B)):= Mir.motion x.s ((scaleR m B).root ((assembly (More m)).root x.b))
def ρx:Equiv.Perm (Index m):= Mir.motion x.s ((assembly (More m)).root x.b)
lemma ψX(t: Site (Domain m B)): ψx B x t= Shape.anon (castX (netB m B x)) (CSide m B) t:=by rw [stir_l]; unfold ψx; rw [← Trip.scale_eq]; rfl
lemma μx_p(y:Era m)(t): ψx B (x*y) t= ψx B x (ψx B y t):=by simp_rw [ψX,map_mul,stirP]
lemma tag_h(i: Index m):address m B (ρx x i)= ψx B x (address m B i):=by
 unfold address; change (scaleR _ _).root (Signed.act _ _+_)= Signed.act _ _+_
 rw [map_add]; exact congrArg₂ (·+·) (Ratio.signed (scaleR m B) i x.s) rfl --]
lemma ρXp(y:Era m)(i):ρx (x*y) i=ρx x (ρx y i):=by apply (scaleR m m).embed_injective; change address m m _ = address m m _; rw [tag_h,μx_p,tag_h,tag_h]
@[simp] lemma ρ_o(i:Index m):ρx (1:Era m) i=i:=by change affine 1 ((assembly _).root 0) _= _; rw [map_zero]; simp [affine]
@[simp] lemma ψ_o(i:Site (Domain m B)):ψx B (1:Era m) i=i:=by rw [ψX,stir_l,map_one]; change affine 1 ((assembly _).root 0) _=_; rw [map_zero]; simp [affine]
def sumX(m:Side)(x:Era m)(v:Cue m):Cue m:=fun i=> doveV x.charge (v (ρx x i))
def vest(t: Pack m B):Pack m B:=(turnV B x t.1,sumX m x t.2)
lemma bake(y:Era m)(U) :vest B y (vest B x U)=vest B (x*y) U:=by
 refine Prod.ext ?_ ?_; change flashA _ (flashA _ _)=flashA _ _; rw [lights,map_mul]
 change sumX m y (sumX m x U.2)=sumX _ _ _; funext i; unfold sumX; rw [dove_v]; change _=doveV (x.charge.xor y.charge) _; rw [ρXp, Bool.xor_comm]
lemma ζ_o(t:Pack m B):vest B (1:Era m) t=t:=by
 apply Prod.ext; · unfold vest turnV; rw [map_one]; exact Skye.rev1 t.1
 funext i; change doveV false (t.2 (ρx _ i))=t.2 i; rw [ρ_o]; exact Subtype.ext rfl
lemma squirm (V:Geometry Z)(U:Pack m B):∃ g,vest B x (Lattice.gauge V U.1, Phase.partner m B V U.2)= (Lattice.gauge g (vest B x U).1, Phase.partner m B g (vest B x U).2):=by
 let Y:=netB m B x; refine ⟨fun i=> polarT Y.charge (V (Skye.boxA Y i)), Prod.ext (Skye.revG Y U.1 V) ?_⟩; funext i; change (xtra x.charge).X (scaledV (V _) _)=scaledV _ _; rw [(xtra x.charge).trek]; congr 3; exact (tag_h B x i).trans (ψX B x (address m B i)) -- tune
lemma ζx_o(e:ℝ)(V:Skin m B)(h:Guard V e):Guard (turnV B x V) e:=keepC (N:=CSide m B) _ _ _ _ h
end YM.CF.Gloss
