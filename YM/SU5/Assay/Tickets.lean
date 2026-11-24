import SatinFixedContrastNovember4
import YM.SU5.Assay.Bank
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Six Set
variable {P:Spine}{j:Axis}{A:P.Apron}{F G:SampleDose}
/-!
 Wall currency inside the review commitments. Work on *any*
 ordered pair of physical rectangles, also beyond the review
 example. Tick grants can even be **identical** for old and
 narrower inserted measurements consultable on the same host.
-/
namespace Doorway
variable (D:Doorway)
def changeDue (j:Axis):ℝ:=(D.upper j - D.lower j)/6
lemma change_pos (j:Axis):0<D.changeDue j:=div_pos (sub_pos.mpr (D.clearance j)) (by norm_num)
def foyer : Doorway where
 lower j:=D.lower j+D.changeDue j
 upper j:=D.upper j-D.changeDue j
 clearance j:=by unfold changeDue; linarith only [D.clearance j]
lemma stepOut : D.foyer.sealing ⊆ D.invites:=fun _ q i _=>⟨(show D.lower i<D.foyer.lower i from lt_add_of_pos_right _ (D.change_pos i)).trans_le (q.1 i),
 (q.2 i).trans_lt (show D.foyer.upper i<D.upper i from sub_lt_self _ (D.change_pos i))⟩

/-- Enough ages for the specified invitations; they remain **fixed**
    over all stamps, smear & room choices. -/
def Stash (f:Vantage):Prop:=∀i,f i≤D.changeDue i
lemma noBill :D.Stash 0:=fun i=>(D.change_pos i).le
lemma Stash.receive {α:Type*} {f:α→Vantage}{l:Filter α}(p:∀i,Tendsto (fun a=> f a i) l (𝓝 0)):
 ∀ᶠ a in l,D.Stash (f a):=
 eventually_all.mpr fun i=> (p i).eventually (ge_mem_nhds (D.change_pos i))
variable {D}{f:Vantage}
lemma Stash.installs (h:D.Stash f)(p:tsupport F.val ⊆D.spare.invites)(j:Axis): Walled j F (D.foyer.lower j) (D.foyer.upper j) (f j):=by
 intro y u
 have : D.spare.lower j< y j∧y j< D.spare.upper j:=p u j (Set.mem_univ j)
 have w:=h j
 simp only [spare,foyer,changeDue] at w this ⊢
 constructor <;> linarith only [this,w]
lemma Stash.inside (h:D.Stash (A.realWidth P))(p:tsupport F.val⊆ D.spare.invites): P.spacePrice A F ⊆ D.foyer.invites:=by
 intro y v j _; exact (h.installs p j).aperture v

-- midpoint cut axis 3 (not enforcing mirror smears)
def turnCut (D N:Doorway):ℝ:=(D.upper 3+N.lower 3)/2
variable {N: Doorway}{σ:Orders}
lemma Later.split (v:D.Later N σ 0):D.upper 3<D.turnCut N∧D.turnCut N<N.lower 3:=by
 have h:=v (3:Axis);rw [if_pos σ.property] at h
 simp only [Pi.zero_apply,mul_zero,add_zero] at h
 unfold turnCut; constructor <;> linarith only [h]
lemma third (v: D.Stash f)(u:tsupport F.val⊆D.spare.invites):
 Walled 3 F (D.lower 3) (D.upper 3) (f 3):=
 (v.installs u 3).outer (le_add_of_nonneg_right (D.change_pos _).le) (sub_le_self _ (D.change_pos _).le)
lemma first (v:D.Stash f)(u:tsupport F.val ⊆D.spare.invites)(p:D.Later N σ 0):Walled 3 F (D.lower 3) (D.turnCut N) (f 3):=
 (third v u).outer le_rfl p.split.1.le
lemma second (v:N.Stash f)(u:tsupport G.val⊆N.spare.invites)(p:D.Later N σ 0):Walled 3 G (D.turnCut N) (N.upper 3) (f 3):=
 (third v u).outer p.split.2.le le_rfl
end Doorway

variable (P)
structure Curtain (D:Doorway)(j:Axis)(t:ℕ)(k:ℤ)(w:ℕ):Prop where
 width:0<w
 left:D.lower j≤ P.tock t k
 starts:P.tock t k≤D.foyer.lower j
 ends:D.foyer.upper j≤P.tock t (k+w)
 right:P.tock t (k+w)≤D.upper j
-- purchases calipers for all axes
def Tickets (D:Doorway)(t:ℕ):Prop:=∀l,∃k w,P.Curtain D l t k w
variable {P}{D:Doorway}{t w:ℕ}{k:ℤ}
lemma Curtain.on_price (h:P.Curtain D j t k w)(u:D.Stash (A.realWidth P))(q:tsupport F.val⊆D.spare.invites):
 P.FrameFace j t (P.spacePrice A F) (D.lower j) (D.upper j) k w:=by
 refine ⟨h.width,h.left,h.right,?_⟩
 intro y p; obtain ⟨a,b⟩:=u.inside q p j (Set.mem_univ j)
 exact ⟨h.starts.trans a.le,b.le.trans h.ends⟩
lemma Curtain.sales (h:P.macroStep t < D.changeDue j):∃k w,P.Curtain D j t k w:=by
 have p:∀y∈D.foyer.sealing, D.lower j+D.changeDue j ≤ y j∧y j≤D.upper j-D.changeDue j:=fun _ q=> ⟨q.1 j,q.2 j⟩
 obtain ⟨k,w,g⟩:=FrameFace.checkout p (D.foyer.clearance j).le h
 have u: D.foyer.lower≤ D.foyer.upper:=fun i=>(D.foyer.clearance i).le
 exact ⟨k,w,g.width,g.left,(g.buys D.foyer.lower ⟨le_rfl,u⟩).1,(g.buys D.foyer.upper ⟨u,le_rfl⟩).2,g.right⟩
lemma Tickets.late (P:Spine)(D:Doorway):∀ᶠ t in atTop, P.Tickets D t:=
 eventually_all.mpr fun j=> (P.macroStep_zero.eventually (gt_mem_nhds (D.change_pos j))).mono fun _ p=> Curtain.sales p
lemma Fades.shelter {Q:ℕ→P.Apron} (h:P.Fades Q)(D:Doorway):∀ᶠ i in atTop,D.Stash ((Q i).realWidth P):=Doorway.Stash.receive D h

-- Example & sign

def fullWay:Orders:=⟨fun _=>true,rfl⟩
lemma fullSweep :reviewEarlierBox.Later reviewLaterBox fullWay 0:=by intro i;norm_num [reviewEarlierBox,reviewLaterBox,fullWay]
lemma fullCut:reviewEarlierBox.turnCut reviewLaterBox=0:=by norm_num [Doorway.turnCut,reviewEarlierBox,reviewLaterBox]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
