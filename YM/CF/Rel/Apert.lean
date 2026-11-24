import YM.CF.Rel.Ripe
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Affine
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
def spigot (x:Site n)(i:Axis):ℝ:= ((Lattice.lift x i:ℤ) - ((Lattice.lift (-x) i:ℤ):ℝ))/2
lemma slit{v w:Site n}{i:Axis}(hp:v i=w i): spigot v i=spigot w i:=by simp [spigot,lift,hp]
lemma slit_z(v: Site n)(i:Axis): spigot (-v) i= -spigot v i:=by simp [spigot]; ring
lemma sit(x:Site n)(h:10*separation x 0<n.val)(i:Axis): spigot x i=(AnalyticBridge.VerifiedReset.coord 0 x i):=by
 have ht:Lattice.lift (-x)= -Lattice.lift x:=by apply lift_eq_iff.mpr; rw [map_neg,wrap_lift]; refine ⟨rfl,?_⟩; intro j; rw [Pi.neg_apply]; have he:=component_le x j; rw [Lattice.separation,sub_zero] at h; omega
 unfold spigot AnalyticBridge.VerifiedReset.coord; rw [ht,Pi.neg_apply, Int.cast_neg,sub_zero]; ring
def cupB(x:PlaqAxes)(v:G.Color):InputZ G n:=fun a=> if a.2=coord x.val.2 then spigot a.1 x.val.1 • v else 0
lemma pourA(x:PlaqAxes) (y:Site n)(u:Axis) (z:G.Color):cupB x z (y,coord u)= if x.val.2=u then spigot y x.val.1 • z else 0:=by unfold cupB; simp [coord_iff,eq_comm]
lemma pourP (x:PlaqAxes)(r:G.Color)(y:Site n) (u:Axis)(h:10*separation y 0<n.val):cupB x r (y,coord u)=(AnalyticBridge.VerifiedReset.wedge x r).field 0 (y,u):=by rw [pourA,AnalyticBridge.VerifiedReset.wedge_field,sit y h]
lemma cube_b(V:AnalyticBridge.VerifiedReset.LinearJet G)(z:Site n) (h:10*separation z 0 < n.val) (he:n.val≥4) (F:InputZ G n)(q:∀ (i:Site n) a,separation z i≤1→ F (i,coord a)=V.field 0 (i,a))(y:PlaqAxes) : sumH G F (z,plaquette y)= V.positive y:=by
 rcases y with ⟨⟨b,c⟩,hb⟩; ext1 j; change (Matrix.mulVec (Exterior.d 1 n) (parts G 1 F j)) (z,plaquette _) = _; rw [d_plaquettes]; unfold parts; dsimp only; rw [q (z+Lattice.step b) c (by simpa using Font.small z (posDir b)), q _ _ (le_of_eq (separation_self z)|>.trans (by norm_num)), q (z+Lattice.step c) b (by simpa using Font.small z (posDir c)),q _ _ (le_of_eq (separation_self z) |>.trans (by norm_num)),V.field_step h he,V.field_step h he]; unfold AnalyticBridge.VerifiedReset.LinearJet.positive AnalyticBridge.VerifiedReset.LinearJet.curl; rw [WithLp.ofLp_add,WithLp.ofLp_add,WithLp.ofLp_sub]; dsimp; abel -- tune
lemma cobraB (u c:PlaqAxes)(z:Site n)(v:G.Color)(h:10*(separation z 0+1)<n.val):sumH G (cupB u v) (z,plaquette c)= if u=c then v else 0:=by
 rw [cube_b (AnalyticBridge.VerifiedReset.wedge u v) _ (by omega) (by omega),AnalyticBridge.VerifiedReset.curl_wedge]
 intro i a he; apply pourP; have ht:= separation_triangle i z 0; rw [separation_comm i z] at ht; omega
lemma dye_eq(s:Axis)(k j:Axis)(x:Site n)(p:s≠j): spigot ((Signed.mirror s).act x) j=spigot x j:=by apply slit; simp [Signed.mirror, Signed.act,p]
lemma dye_no(s:Axis)(x:Site n): spigot ((Signed.mirror s).act x) s= -spigot x s:=by rw [←slit_z]; apply slit; simp [Signed.mirror,Signed.act]
-- reflection chosen along ramp direction
lemma shave (p:PlaqAxes)(v:G.Color): Bid.pulled (n:=n) (cupB p v) (Signed.mirror p.val.1)= -cupB p v:=by
 funext u; rcases u with ⟨x,j⟩; obtain ⟨j,rfl⟩:=axisEquiv.surjective j; let s:=p.val.1
 have he : (posDir j).rotate (Signed.mirror s)=⟨j,decide (s=j)⟩:=by simp [Lattice.Step.rotate,Signed.mirror,posDir]
 change Bid.pulled _ (Signed.mirror s) _=_; unfold Bid.pulled; dsimp only; rw [axisEquiv.symm_apply_apply, he]; by_cases ht:s=j
 · rw [decide_eq_true ht]; unfold Lattice.Step.used; simp only [Pi.neg_apply, ↓reduceIte,coord_map]; rw [pourA,pourA,if_neg (show p.val.2≠j from ht ▸ p.property.ne'),if_neg (ht ▸ p.property.ne')]
 rw [decide_eq_false ht]; unfold Lattice.Step.used; simp only [Pi.neg_apply,Bool.false_eq_true, ↓reduceIte, coord_map]; rw [pourA,pourA]; split
 next hz=> unfold affine; rw [add_zero,dye_no,neg_smul]
 rw [neg_zero]
lemma spareCi (p:PlaqAxes)(v:G.Color)(i:Axis)(hp:i∉(plaquette p).val): Bid.pulled (n:=n) (cupB p v) (Signed.mirror i)= cupB p v:=by
 have h₁:i≠p.val.1:=fun he=>hp (he ▸ mem_insert_self ..); have h₂:i≠p.val.2:=fun he=>hp (he ▸ mem_insert_of_mem (mem_singleton_self p.val.2))
 funext ⟨x,j⟩; obtain ⟨j,rfl⟩:=axisEquiv.surjective j
 have he : (posDir j).rotate (Signed.mirror i)=⟨j,decide (i=j)⟩:=by simp [Lattice.Step.rotate,Signed.mirror,posDir];
 unfold Bid.pulled; dsimp only; rw [axisEquiv.symm_apply_apply,he]; by_cases h:i=j
 · rw [decide_eq_true h]; unfold Lattice.Step.used; simp only [Pi.neg_apply, ↓reduceIte,coord_map]; rw [pourA,pourA,if_neg (h ▸ h₂.symm),if_neg (h ▸ h₂.symm),neg_zero]
 rw [decide_eq_false h]; unfold Lattice.Step.used; simp only [Bool.false_eq_true,↓reduceIte,coord_map]; rw [pourA,pourA]; split; next he=> unfold affine; rw [add_zero,dye_eq _ j _ _ h₁]
 rfl
end YM.CF.Rel
