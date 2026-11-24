import YM.CF.BProof.Mapping.Reach

/-! B-map: profile extension from both faces needed ONLY deep. Price of full axial coordinates
 from (eq:B-mapcard). Include observations in the tails and express solidity on admitted
 fields. Avoid passing from zero operator extensions (fields built on T). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mapping.Pawn
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox House
open Gauss Release Release.hot
open scoped Topology BigOperators Classical Matrix InnerProductSpace Matrix.Norms.Frobenius
local notation "G"=> SU.group
variable {s c: Side}{Y:Yard s}(g:Ratio c s)(S:Hall s)
variable (x y: Pawn Y)(T:Support s)(z:ℝ)(A:PathData G){R:ℝ}{c':Clip}{M:ℕ}(θ:ℝ)(U:Beam c' R Y.short M z)(h:Charge.Room Y M)
variable {C r:ℕ} (Q:Queue Y g S T C r)(p: Agreed g x y Q.Z)(w:1+U.horizon' ≤ r*g.count.val)
lemma listed {t:Site s}(v:t∈T): Grid.collar ({addr Y g t}:Finset _) r⊆ Q.Z:=Grid.collar_le (singleton_subset_iff.mpr (Grid.to_collar _ _ (mem_image_of_mem _ v))) le_rfl |>.trans Q.lunch -- tune output
include w
lemma licensed (t: Site s)(v:t∈T): Shade g Q.Z (col Y t) U.horizon':= block_read g Q.Z _ r (by omega) fun j _ e=> listed g S T Q v (Grid.collar_mem.mpr ⟨_,mem_singleton_self (addr Y g t), (Grid.dist_symm (addr Y g t) _).symm.trans_le e⟩)

variable {t:Site s} {i:Y.Index}(a:Space s)
include h p
lemma post_read (L:Support s)(u:L∈StackQ Y T i)(k:¬Y.D i)(b:Bool)(q:a∈tilt L):
    sightP S x z A θ U i b a=sightP S y z A θ U i b a ∧ ∀ j:TAxis,inlet (Y.u i) Y.long (issue x z A θ U) b (a,j)=inlet (Y.u i) Y.long (issue y z A θ U) b (a,j):=by
 obtain ⟨V,d⟩:= Q.antenna i L u b; exact ⟨sight_reads g S x y Q.Z z A θ U h p L V k b d w q, fun j=> face_read g S x y Q.Z z A θ U h p L V k b d w a j (V.rises q)⟩
lemma deep_eyes (k:¬Y.D i)(b:Bool)(q:t∈T)(v:Deep.rise Y (2*Deep.D Y) i (time t))(u:Grid.dist a (space t)≤ 1):
    sightP S x z A θ U i b a=sightP S y z A θ U i b a∧ ∀ j:TAxis,inlet (Y.u i) Y.long (issue x z A θ U) b (a,j)=inlet (Y.u i) Y.long (issue y z A θ U) b (a,j):=by
 obtain ⟨L,h,g⟩:= Deep.exists' Y T (Deep.D Y) i t q v; exact post_read _ S x y T z A θ U ‹_› Q p w a L h k b (Grid.collar_mem.mpr ⟨_,mem_image_of_mem _ g,u⟩) -- tune names

private lemma deep_base (k:¬Y.D i)(b:Bond s)(q:b.1∈T)(v:Deep.rise Y (2*Deep.D Y) i (time b.1)):
    Y.baseN i S (issue x z A θ U) (rent S x z A θ U) b=Y.baseN i S (issue y z A θ U) (rent S y z A θ U) b:=by
 let x'(u:Pawn Y):= Y.high i S (issue u z A θ U) (rent S u z A θ U)
 have he(t:Site s)(e:Grid.dist (space t) (space b.1)≤1): x' x t=x' y t := (deep_eyes g S x y T z A θ U h Q p w (space t) k (flag (Y.u i) (time t) Y.long) q v e).1
 have hp: Grid.dist (space (b.1+Lattice.step b.2)) (space b.1)≤1:= Grid.dist_le.mpr (fun j=> Grid.dist_le.mp (Grid.dist_symm _ _ |>.trans_le (Micro.to_step (Step.mk b.2 false) b.1)) j.succ) -- orientation maybe Step true; wrong parenthesization
 let formL(u:Pawn Y):= formal (Y.u i) Y.long S (issue u z A θ U) (rent S u z A θ U i) b
 have hv:formL x=formL y:= by
   rcases whichBond b with ⟨t,p,rfl⟩|⟨t,p',j,rfl⟩; unfold formL; rw [normal_light,normal_light]
   let f(u:Pawn Y):= outlook (Y.u i) Y.long S (issue u z A θ U) (rent S u z A θ U i) -- tune formL rent uses Eye? currently FaceS vs Eyes
   have hx (b:Bool): f x b (p',j)=f y b (p',j):=by
     let v':= deep_eyes g S x y T z A θ U h Q p w p' k b q v (by rw [horiz]; simp) -- tune
     have ht:= deep_eyes g S x y T z A θ U h Q p w (p'+tstep j) k b q v (by rw [horiz]; dsimp only; rw [space_join, Grid.dist_symm,← Face.slide_t]; exact Grid.near_slide _ _)
     unfold f outlook Face.react; change sightP S x z A θ U i b p' *_*_ =_; rw [v'.1,v'.2]; change _*_* (sightP S x z A θ U i b (p'+tstep j))⁻¹=_; rw [ht.1]; exact rfl
   unfold formL; rw [horizontal_light,horizontal_light, light,light]; exact congrArg₂ (Face.link S.K (angle Y.long _)) (hx false) (hx true)
 unfold baseN Lattice.gauge; simp only [Pi.inv_apply, inv_inv]; change (x' x _)⁻¹*formL x*x' x _=(x' y _)⁻¹*formL y*x' y _; rw [he b.1 (by simp),hv,he _ hp]

lemma chapter (b:Bond s)(q:b.1∈T)(hx:Certified S x z A θ U)(hy:Certified S y z A θ U): put S x z A θ U b=put S y z A θ U b:=by
 have hp:=licensed g S T z U Q w b.1 q; have he : addr Y g b.1∈ Q.Z:= shade g Q.Z _ _ hp; by_cases a:b∈Y.rent; swap; · exact granted g S x y Q.Z z A θ U h p b a hp
 obtain ⟨i,k⟩:=Y.rents.mp a; by_cases d:Y.D i; exact readsD g S x y Q.Z z A θ U p b i d k he
 by_cases x': Deep.rise Y (2*Deep.D Y) i (time b.1); swap; · exact reads_safe g S x y Q.Z z A θ U h p b k d x' hp hx hy
 rw [leaser S x z A θ U i b k,leaser S y z A θ U i b k, slot,if_neg d,slot,if_neg d,p.dust b he,deep_base g S x y T z A θ U h Q p w d b q x']
theorem transcript (hx:Certified S x z A θ U)(hy:Certified S y z A θ U): Agrees (↑T) (put S x z A θ U) (put S y z A θ U):= fun i v _=> chapter g S x y T z A θ U h Q p w i v hx hy
end YM.CF.BProof.Mapping.Pawn
