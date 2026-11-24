import YM.CF.BPress.Sugar.Stage
import YM.CF.BPress.House.Telescope
/-! Packaging fixed torus B-kernel proof data. Locale. Pose.Crew. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Sugar
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Pressure Next.SectorChange RG
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
variable {N:Side}{B:BandWidth}(A:Bands (More N) B)(R:Hangar (More N))
open Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Stage
structure Crew where
 y: ℝ -- actual β scale.Hoop.
 κ:ℝ
 F:Weave.Fare A
 P: Weave.Budget
 J: ChartRatio SU.group
 T: Sheet.Atlas
 L:ℝ -- Lf purchase parameter
 C:ℝ -- kernel costs
 C':ℝ
 n:ℕ -- grid
 Z: Net (More N) T L y C C' n
 tile : Grid.Tiling (More N) -- Mark tile, not final X tile
 loom : Orbit N → Pane N
namespace Crew
open Wealth Weave
variable {A} (H:Crew A)
abbrev Role (v:mState N A):Prop:= House.Role A H.T H.y H.κ H.F v
abbrev castP := {x:mState N A// Role H x}
-- prefer abbrev.
variable (X:Stage N) (x:mState N A)
-- κ.Region issues ζ.
abbrev layout := flash A x.1.2
def port : Micro (More N):= Hazel.field A H.Z H.F x.1.1 x.2.1 (layout (A:=A) x) x.2.2.1
def tape : Letter A:= ballot A H.Z H.tile (layout (A:=A) x) (H.port x)
abbrev unsea := bawl A R H.y x.1.1 x.2.1.1
abbrev harborT : Orbit N:= (H.port x, x.2.2.2.1)
abbrev utensil : Micro (More N):= H.loom (H.harborT x)
abbrev areaC := specialB X.W A R (unsea R H x)
abbrev fury : ℝ→Paint (More N):= Stage.tower A R X (H.tape x) (unsea R H x) (H.utensil x)
abbrev thread : Stun N:= Stage.way A R X (H.tape x) (unsea R H x) (H.utensil x)
abbrev flag : Support (More N):= RG.flags (temp H.y) (H.port x)
lemma reserves (p:H.Role x) : Reserve A H.F x.1.1 x.2.1 (layout (A:=A) x) x.2.2.1 H.y H.κ H.T:= ⟨p.2.1,p.1.2,p.2.2,p.1.1⟩
structure Stir (e:ℝ)(k:ℕ)(c:ℝ):Prop where
 licence : Licence (R:=R) (H.tape x) X.tile c (H.unsea R x) (H.utensil x) X.W X.q X.qX X.δ
 blaze (a:Site (More N))(h:a∈H.flag x): ∃ i:A.Index,a∈A.gap i∧∃ b:Tri (More N), delta (Fin.tail a) b≤4 ∧ (i,b)∈x.1.1
 flood (a b:Site (More N))(h:a∈ H.flag x)(g:separation a b ≤ k+1): NearBlock A X.W.U b∧ Near A R (H.unsea R x) 1 b
 dangerous(l:Link (More N))(h:¬ Disjoint (RG.flags e (H.port x)) (win k l)): l.1∈ Danger A R X.W (H.unsea R x)∧ endAt l∈Danger A R X.W (H.unsea R x)
variable {Y:Driver N}{e c d:ℝ}{k:ℕ}
structure Rented (d e:ℝ)(k:ℕ)(c:ℝ): Prop where
 roof: Roof N e d k H.loom
 stop : temp H.y ≤ e
 dusk : Dusk B R X.W -- maybe name conflict
 pay(x:mState N A): H.Role x→ H.Stir R X x e k c -- tune binder

lemma fat {D η A0:ℝ}{r r':Side}(f:Record r (More N))(f':Record r' (More N))(W:X.tile=f.key)(q:H.tile=f'.key)(t:Summer A H.F H.P.upper (H.P.low H.y) (H.P.reach H.y) (H.P.chunks H.y))(p:H.P.reach H.y≤ R.L.val)(K:X.W.M≤ R.L.val) (v:Roof N e d k H.loom)(g:temp H.y ≤ e)(J: Booked d k X.W r X.q X.qX)(L:Shields H.T B H.P D H.κ η A0 H.L H.y H.C H.C' r r' X.q X.δ X.W): H.Rented R X d e k (price_p A0 η H.y):=by
 let u:Dusk B R X.W:=⟨L.summer,K⟩; refine ⟨v,g,u,fun x h=>?_⟩; let Y:=reserves H x h; let Q:= L.lost _ _ H.Z A _ _ _ Y.gate Y.u -- inspect; 
 have ht : H.tape x= PortLetter A H.Z H.F x.1.1 x.2.1 (layout (A:=A) x) x.2.2.1 f'.key:= by unfold tape; rw [q]; rfl
 refine ⟨?_, fun a b=>Y.flags_early L.plenty t p Q a b,fun _ _ z l=>Y.stormB L.plenty t p u J.past Q z l,fun i b=>Y.unsafe_re L.plenty t p u g J.past Q i b⟩; rw [W,ht]; exact realized Y J L v t K p g f f' x.2.2.2.1 -- tune type deps
variable {R H X}
lemma Rented.calm (p:Rented R H X d e k c)(v:H.Role x)(l: Link (More N))(q:l∈ inside (safe A R X.W (unsea R H x))): H.utensil x l= H.port x l:=p.roof.lamp _ _ _ (Classical.byContradiction fun h=> (mem_compl.mp ((inside_iff ..).1 q).1) (((p.pay x v).dangerous l h).1)) -- tune safe notation
open Driver
abbrev α (p:Rented R H X Y.d e k c)(q:Stamp A R X Y)(x:mState N A)(t:H.Role x) : Y.Pose := Stage.player q (p.pay x t).licence (p.roof.paid (harborT H x))
end Crew
end YM.CF.BPress.Sugar
