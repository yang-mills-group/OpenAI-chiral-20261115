import YM.CF.BProof.Mapping.Wage

/- interpolation cost at touched records. Use weak term requiring T even though shallow
 need merely its block tangent and Terra investors. Normal cut leases mandatory deep (or D);
 both SmoothSight on both faces of any deep T projection. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mapping.Pawn
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox House
open Gauss Release Release.hot
open scoped Topology BigOperators Classical Matrix InnerProductSpace Matrix.Norms.Frobenius
local notation "G"=> SU.group
variable {s c: Side}{Y:Yard s}(g:Ratio c s)(S:Hall s)
variable (x y: Pawn Y)(Z: Finset (Block Y c))(z:ℝ)(T:PathData G){R:ℝ}{c':Clip}{M:ℕ}(θ:ℝ)(U:Beam c' R Y.short M z)(h:Charge.Room Y M)(u:Agreed g x y Z)
variable {C r:ℕ}
abbrev Certified := ∀ i, ¬Y.D i→∀ b:Bool,Y.Firmly S (issue x z T θ U) (rent S x z T θ U) i b
-- immediate lease formulas
lemma leaser (i:Y.Index)(b:Bond s)(p:b∈ Y.leases i) : put S x z T θ U b=Y.slot i z S (issue x z T θ U) (rent S x z T θ U) b*x.dust b := played Y z S _ _ _ i p
include u
-- payD
lemma readsD (b:Bond s) (i:Y.Index)(k:Y.D i)(v:b∈Y.leases i)(q:addr Y g b.1∈ Z) : put S x z T θ U b=put S y z T θ U b:=by rw [leaser S x _ _ θ _ i b v,slot,if_pos k,leaser S y _ _ θ _ i b v,slot,if_pos k,u.dust _ q]
-- reads in shallow region. Applies only one collar. present also for short step pricing later.
include h
lemma reads_safe {i:Y.Index}(b:Bond s)(p:b∈Y.leases i)(k:¬Y.D i)(w:¬ Deep.rise Y (2*Deep.D Y) i (time b.1))
    (q:Shade g Z (col Y b.1) U.horizon')(hx:Certified S x z T θ U)(hy:Certified S y z T θ U) : put S x z T θ U b=put S y z T θ U b:=by
 let D:= Deep.D Y; let t:=time b.1; have hh : addr Y g b.1∈ Z:= shade g Z _ _ q; rw [leaser S x z _ _ U _ _ p, leaser S y z _ _ U _ _ p, u.dust _ hh,slot,if_neg k,slot,if_neg k]; apply congrArg (·*y.dust b)
 rw [leases,if_neg k] at p; have he: Y.Band i (time b.1):=mem_strip.mp ((mem_watch ..).1 p).1.1; have hp:4*(2*D)< Y.long:=by have u:=Y.long_pos; have :=Deep.D_le Y; unfold D; omega
 rcases whichBond b with ⟨x₁,p₁,rfl⟩|⟨x₁,p₁,r,rfl⟩
 · have hz:along (Y.u i) x₁=Angular.cut Y.long:= (watch_v _ _ _ _ Y.long_pos Y.lL).1 p; apply False.elim (w ⟨he,?_,?_⟩)
   · change 2*(Deep.D Y)≤ along (Y.u i) x₁; have hv:=Deep.D_le Y; unfold Angular.cut at hz; omega
   have hv:=Deep.D_le Y; have ht:= Y.before_u i (show Y.Band i x₁ from he); unfold Angular.cut at hz; change 2*(Deep.D Y)≤ along x₁ (Y.v i); omega
 let l:=Y.long; let t:=Y.u i; let k':=flag t x₁ l; let H(x:Pawn Y) := Y.baseN i S (issue x z T θ U) (rent S x z T θ U)
 have hb: Certified S y z T θ U:=hy; have ht (a:Pawn Y)(v:Certified S a z T θ U): H a (horiz x₁ p₁ r) = inlet t l (issue a z T θ U) k' (p₁,r):=by
    refine congrFun (f:=sheet (H a) x₁) (Y.cushion S (issue a z T θ U) (rent S a z T θ U) x₁ k' (v i k k') rfl ?_) (p₁,r)
    rcases Deep.mist Y (2*D) i (show Y.Band i x₁ from he) w hp with v|v; obtain ⟨p,g⟩:= Y.hot_flag i x₁ hp v; rw [g,show k'=false from p]; exact rfl; obtain ⟨p,g⟩:=Y.cold_flag i x₁ hp v; rw [g,show k'=true from p]; rfl
 change H x _=H y _; rw [ht x hx, ht y hy]; apply face_eq g x y Z z T θ U h u k k' p₁ r; convert q using 1; simp only [House.col,horiz,time_join,space_join, Posts.band Y i x₁ he]; rfl
-- W access for fields and trunks
lemma granted (b:Bond s)(p:b∉Y.rent)(q: Shade g Z (col Y b.1) U.horizon'): put S x z T θ U b=put S y z T θ U b:=by
 by_cases v:b∈ Y.trunks; swap; · have hx:b∈Y.field:=mem_compl.mpr (fun v'=> (not_or.mpr ⟨v,p⟩) (mem_union.mp v')); exact (Y.mix_field _ _ hx).trans ((local_gap g x y Z z T θ U h b hx u q).trans (Y.mix_field _ _ hx).symm)
 exact (Y.squash_flat _ v).trans (Y.squash_flat _ v).symm
-- frame lesson at both. allowance via Queue bound; often use halo r≥2 and Lc≥ horizon. wrap with single hidden.
def sightP (i : Y.Index) (b:Bool):= sight (Y.u i) Y.long S (issue x z T θ U) (rent S x z T θ U i) b
variable {i:Y.Index}(Q: Support s)(L:Lesson S C Q)(k:¬Y.D i)(b: Bool)(p:Grid.collar (aisles Y g L.Z (location Y i b)) r ⊆ Z)(w:1+U.horizon' ≤ r*g.count.val)
include h u p w
lemma shave {a:Space s}(v:a∈ L.Z): Shade g Z (location Y i b,a) (1+U.horizon'):= block_read g Z _ r w fun j _ k'=> p (Grid.collar_mem.mpr ⟨_,mem_image_of_mem _ (mem_image_of_mem _ v),(Grid.dist_symm ..).trans_le k'⟩)
include k
lemma face_read (a:Space s)(t:TAxis)(v:a∈L.Z): inlet (Y.u i) Y.long (issue x z T θ U) b (a,t)=inlet (Y.u i) Y.long (issue y z T θ U) b (a,t) := face_eq g x y Z z T θ U h u k b a t (fun j hp=> shave g S x y Z z U h u Q L b p w v j ((Gauss.base _).mono (by omega) hp)) -- includes tune
lemma sight_reads : Set.EqOn (sightP S x z T θ U i b) (sightP S y z T θ U i b) ↑(tilt Q) := L.solid _ _ _ _ (fun a v=> signs g S x y Z z T θ U h u k b a (shave g S x y Z z U h u Q L b p w v)) (fun a v=> face_read g S x y Z z T θ U h u Q L k b p w a.1 a.2 v.1) -- tune
end YM.CF.BProof.Mapping.Pawn
