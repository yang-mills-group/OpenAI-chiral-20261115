import YM.CF.DPress.Chess.Flow.Street
import YM.CF.Nacre.Rail
import YM.CF.Nacre.Tow
import YM.CF.Fixed.OneParticle
/-!
 Wall convention, at *lifted* fermion-lattice height o (hence through gauge
 plane at 2o). The grid requirement for the choice of the transport weight
 will impose a further qualification on the wall. Plane slabs take both endpoints
 when deciding whether to include any link; shrunk interiors used for support propagation.
 -/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess
open Function Lattice Filter Laurent Spire Skye Scroll Lat Rush Wilson MeasureTheory ProbabilityTheory Push.GridApprox
open Cube (More assembly)
open scoped Topology BigOperators NNReal ENNReal Matrix.Norms.L2Operator Classical
structure Wall where
 i: Axis
 o:ℤ
namespace Wall
variable (W:Wall){n m:Side}
abbrev od:= W.o • (Lattice.step W.i : Cover)
abbrev shape : Shape:= ⟨Signed.mirror W.i, 2 • W.od⟩
abbrev joy(n:Side): Sweep n:= ⟨W.shape.s,wrap n W.shape.t,false⟩
abbrev boost (L:Side):Wall:= ⟨W.i,L.val • W.o⟩
lemma broad(K:Ratio n m): (W.boost K.count).shape=W.shape.broad K:=by dsimp [boost,shape,Shape.broad]; congr 1; ext i; simp [od]; ring_nf
lemma rod(K:Ratio n m): reSweep K (W.joy n)=(W.boost K.count).joy m:=by unfold reSweep joy; rw [W.broad,K.embed_wrap]; rfl
lemma anon (x:Seat n): W.shape.anon n x=boxA (W.joy n) x:=by rw [sitA]; unfold joy Shape.anon; rw [(assembly n).embed_wrap]; rfl
abbrev site(n:Side):Equiv.Perm (Seat n) := boxA (W.joy n)
lemma od_i (n:Side): W.od W.i=W.o := by simp [od]
lemma shape_p (x:Seat n): W.site n x W.i=4*(W.o:Per _)-x W.i:=by
 rw [site,← W.anon,Shape.anon]; let z:=W.o; have he:(2 • W.shape.t) W.i=4*z:=by simp [od]; unfold z; ring
 have h: (Signed.mirror W.i).act x W.i= -x W.i:=by simp [Signed.act,Signed.mirror]
 change _ + (((2 • W.shape.t) W.i:ℤ): Per (More n))=_; rw [he,h]; push_cast; unfold z; ring
lemma joins : Nacre.joinX W.shape W.shape=Nacre.lagX 0:=by
 change Shape.mk (Signed.mirror _*_) _=_; rw [Fixed.square_mirror]; congr 1; ext i; by_cases h:W.i=i <;> simp [Signed.act,Signed.mirror,od,h,Ne.symm] -- tune
lemma square (n:Side) : (W.joy n)⁻¹=W.joy n:=by
 change Sweep.mk ((Signed.mirror W.i)⁻¹) _ _=Sweep.mk _ _ _; rw [Signed.mirror_inv,wrap_signed]; simp only [←map_neg]; congr 2; ext i; by_cases h:W.i=i <;> simp [Signed.act,Signed.mirror,od,h,Ne.symm]
lemma itself(n:Side): (W.site n).symm=W.site n := by rw [site,←sitU,W.square]
lemma selves(n:Side): Involutive (W.site n):=fun x=>by nth_rw 1 [←W.itself]; exact Equiv.symm_apply_apply ..
abbrev shine(n:Side):= flashA (W.joy n)
lemma shine_t : W.shine n= stir inert W.shape:=funext (stir_e W.shape false)
lemma twice(n:Side):Involutive (W.shine n):=fun x=>by simpa only [shine,W.square] using (revB (W.joy n) x)
@[fun_prop] lemma iceM(n:Side) : Continuous (W.shine n):= revM ..
abbrev negZ (S:Support (More n)): Support (More n):= S.map (W.site n).toEmbedding
lemma spans {S T: Support (More n)}(p:S⊆ T): W.negZ S⊆ W.negZ T:= Finset.map_subset_map.mpr p
lemma swipe (S:Support (More n))(x:Seat n) : x∈ W.negZ S ↔ W.site n x ∈ S:=by simp [negZ,W.itself]
lemma πsw (S:Support (More n)):W.negZ (W.negZ S)=S:=by ext x; rw [W.swipe,W.swipe,W.selves]
lemma read {A B:Pane n}{S:Support (More n)}(p:Agrees (W.negZ S) A B): Agrees S (W.shine n A) (W.shine n B):= flashD _ _ _ _ p -- tune
lemma trail (n:Side) : MeasurePreserving (W.shine n) (prior SU.group (More n)) (prior SU.group (More n)):=by rw [show W.shine n=Lattice.pull W.shape.s (wrap (More n) (2 • W.shape.t)) from ?_]; exact prior_pull ..; rw [W.shine_t]; rfl
end Wall
end YM.CF.DPress.Chess
