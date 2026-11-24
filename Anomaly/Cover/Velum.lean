import Anomaly.Cover.Verve
import Anomaly.M4
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open CF.Swell Rill CF.Swell.Sonar
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
namespace StageW
-- stencil parts of unscaled Y) plus extraction of current J AT SHIFTED positions and as rooted at center (need translation fitting identities). Fine physical two Seat lengths; actual upper Gram.F near orientation preserved under Guide.Sigma. H pencil arcs qualification. make q.
variable {N:Side}
universe u
inductive Proscenium
| tick -- a
| gauge (s:Signed) -- raw projected weight pre transformation
| core (i:Axis)
| nudge (i:Axis) (b:Bool) -- plus T or minus T
-- add UprTree shifts tests later
 deriving DecidableEq,Fintype
open Proscenium StageQ
local notation "nudgeW" i:max =>More i
abbrev alongM (m:ℕ)(o:Site N)(i:Axis)(b:Bool): Site N:= if b then o+ gapPlus i m else o-gapPlus i m
abbrev gaugeCall(b:BudgetPoint)(K:Scree.Loom N)(X:SOp N)(o:Site N)(s:Signed):Mark N:= fun U=> traceMeter b K o X (flashA (gridTulip s o) U.1) • 1
-- pre: all values at native 0 for this height. no masks on family beyond Mark's own local masks.
def showroom (b:BudgetPoint)(K:Scree.Loom N)(X:SOp N)(F:Axis→SOp N)(m:ℕ)(o:Site N):Proscenium→ Mark N
 | tick=> gaugeMark b K o X
 | .gauge s=> gaugeCall b K X o s
 | core i=> spinMark b K o (F i)
 | nudge i a=> moveMark b K o (alongM m o i a) (F i)
def votingN {N:Side}(F:Proscenium→ Mark N): Mark N:=∑ s:Signed, dollar s • F (.gauge s)
abbrev pairingY {N:Side}(F:Proscenium→ Mark N):= F tick+∑ i:Axis,(F (nudge i true)-F (nudge i false))
variable (b:BudgetPoint)(K:Scree.Loom N)(X:SOp N)(F:Axis→SOp N)(m:ℕ)(o:Site N)
lemma weighP (i:Fields N) : votingN (showroom b K X F m o) i=onStage o (traceMeter b K o X) i.1 • 1:=by unfold votingN onStage; simp only [Finset.sum_apply, Finset.sum_smul, Pi.smul_apply]; exact sum_congr rfl (fun i _=>(smul_assoc ..).symm)
lemma pairingShow: pairingY (showroom b K X F m o)=jointMark b K o m X F:=by unfold pairingY jointMark diffMark; congr 1 -- use rfl ctor
-- covariance of projected probe on Support. inherent.
variable {b K X}
lemma votePiece {r k:ℕ}{t d a v:ℝ} (h: Roof N t d r K)(l:0<d)(g:Trunk (node o) X k a v d)(p:b.threshold ≤ t)(q:k+r+10 ≤ b.B)(ha:0 ≤ a) (s:Signed): WindowTag (gaugeCall b K X o s) o (b.B+12) v:=by
 let W:=gaugeCall b K X o s; let f:=traceMeter b K o X; let V:=gaugeWindow o h l g p q ha; let x0:=gridTulip s o
 have hh:covariant W:=by
    intro g y
    let g':= fun i:Seat N=> polarT x0.charge (g (boxA x0 i))
    let F:Fields N:=(flashA x0 y.1,flashA x0 y.2)
    change f (flashA x0 (Lattice.gauge g _)) • _= twist _ (f F.1 • _); rw [twist_scalar,map_one]
    have he:= V.rolls g' F
    change f _ • _=twist _ (f F.1 • _) at he; rw [twist_scalar,map_one] at he; rw [revG]; exact he
 let S:=offsetMask (b.B+12) o
 refine ⟨⟨?_,fun Z H α y =>?_,fun A=>Reed.Fine.one.scale _⟩,hh,?_,?_⟩
 · let f'(x:Fields N): Fields N:=(flashA x0 x.1,flashA x0 x.2)
   exact Env.along (g:=f') V.ticket.env (((revM x0).measurable.comp measurable_fst).prodMk ((revM x0).measurable.comp measurable_snd))
 · apply V.ticket.dep (flashA x0 Z.1,flashA x0 Z.1) (flashA x0 H.1,flashA x0 H.1) <;> apply flashD <;>rw [offsetMask,screenχ _ _ (?_)] -- args tune
   all_goals first|exact α|rw [←Ione.Clock.nodeA, tieA]
 · exact fun Z=> V.price (flashA x0 Z.1,flashA x0 Z.1)
 exact fun x y h=> congrArg (fun U:Pane N=>f (flashA x0 U) • (1:FC (Single N))) h
section vote
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) (s:ℕ)
variable {I:Type*}(i k:I→ℕ) (m:ℕ)
local notation "N'" j:max=>side Y (i j) s
local notation "Ω" j:max=>More (N' j)
local notation "Xo"=>nodeC (0:Cover)
local notation "wB"=>Y.meter.a s
variable {a b y c:ℝ}
variable {FS:(j:I)→Axis→ SOp (side Y (i j) s)}{X':(j:I)→ SOp (side Y (i j) s)}
local notation "R" j:max=>RootBook Y (i j) (k j) s
local notation "Ka" j:max=>(Y.voyage (i j)).CapeT s
local notation "Υ" j:max=> showroom wB (Ka j) (X' j) (FS j) m 0
local notation "Ξ" j:max=> FC (Single (N' j))
abbrev podium := liner {nodeC (0:Cover)} ((Y.meter.a s).B+12+2*m)
def PinnedW (a b:ℝ)(X:(j:I)→ SOp (side Y (i j) s))(F:(j:I)→ Axis→ SOp (side Y (i j) s)):Prop:=∀ j:I, s<Y.uv (k j)∧ ∃ V f t q, CartPins Y (i j) (k j) s m a b t q (F j) V (X j) f
variable (T:PinnedW Y s i k m a b X' FS) (hp:0<a)(hb:0<b)(t:Proscenium)
include T hp
lemma branchL (j:I): covariant ((Υ j) t)∧ AtSupport false (Satin.region (podium Y s m) (N' j)) ((Υ j) t):=by
 let p:= wB
 let Q:= offsetMask (p.B+12+2*m) (0:Site (N' j)); have he: Q ⊆ Satin.region (podium Y s m) (N' j):=by
    have he:region {Xo} (N' j)={node 0}:=by simp only [region,image_singleton,←node_of,map_zero]; -- tune
    let t:= linen_contains {Xo} (p.B+12+2*m) (N' j); rw [he] at t; exact t
 let T':=offsetMask (p.B+12) (0:Site (N' j)); have hr:T' ⊆ Q:=Corona.halo_mono (Nat.le_add_right ..) le_rfl
 obtain ⟨e,H,K,y,u,v⟩:= T j; let X:= (R j); have hg:X.p= wB := (Papal.prices_plot Y s (i j) (k j) e.le).1
 let A:=v.pulse; let B:=v.ropes.tubes
 rw [←hg]
 cases t
 · let h:= gaugeWindow _ A.roof Λ.dpos B.capX A.reach v.capR hp.le; exact ⟨h.rolls,h.ticket.mono (hg.symm ▸ hr.trans he)⟩
 · next z=> let h:= votePiece _ A.roof Λ.dpos B.capX A.reach v.capR hp.le z; exact ⟨h.rolls,h.ticket.mono (hg.symm ▸ hr.trans he)⟩
 · next i'=> let h:= spinWindow 0 A.roof Λ.dpos (B.hatJ i') A.reach v.capR hp.le; exact ⟨h.rolls,h.ticket.mono (hg.symm ▸ hr.trans he)⟩
 next i' z=>
    let x:= alongM m 0 i' z (N:=N' j); let h:= spinWindow x A.roof Λ.dpos ((B.hatJ i').station x) A.reach v.capR hp.le
    refine ⟨h.rolls,h.ticket.mono ((shift_fits 0 x (X.p.B+12) (p.B+12+2*m) m ?_ (by rw [hg])).trans he)⟩ -- fix
    unfold x alongM; split; exact (stopBeam ..).1; exact (stopBeam ..).2
/-! accredited Panorama -/
include hb
lemma voteMenu (S:Finset Cover)(L:Proscenium): Menu (T:=fun j=> FC (Single (side Y (i j) s))) (fun (j:I) x=> (Υ j) L (replant S _ x)):=by
 rcases isEmpty_or_nonempty I with p|hP; · exact Menu.congr (Menu.zero (T:=fun j=>FC (Single (side Y (i j) s))) (X:=PairsC)) (fun i=>isEmptyElim (i:I))
 choose e V Fs y f w using T
 let W:= (Y.meter.a s); let a':= Λ.J.n; let d:=Λ.J.k; let X0(j:I):Site (N' j):=0; let Cz(j:I):= replant S (N' j); let Z(j:I)(x:PairsC):= (Cz j x).1
 have he(j):(R j).p=W:= (Papal.prices_plot Y s (i j) (k j) (e j).le).1 -- change macro Phi use
 have hv:∀ j:I, Roof (N' j) d Λ.d a' (Ka j) := fun j=> (w j).pulse.roof
 have hz: pageCover Z:= regraft S
 have hZ(i): Measurable (Z i):= measurable_fst.comp (replant_b ..)
 have hq:W.B/10+a'+10 ≤ W.B ∧ W.threshold ≤ d:=by
    let j:=Classical.choice hP; rw [←he j]; exact ⟨(w j).capR,(w j).pulse.reach⟩
 let Iw(j:I)(x:PairsC):FC (Single (N' j)):= 1
 have hI:Menu (T:=fun j=>Ξ j) Iw:= Menu.cnst (fun j=>(1:FC (Single (N' j)))) zero_le_one (fun i=> by simp) -- notation maybe
 let Q:= W.B/10; let O(j:I):Sweep (N' j):=1
 have hE:∀ j:I,Trunk (node (0:Site (N' j))) (X' j) Q a b Λ.d:= fun j=> by unfold Q; rw [← he j]; exact (w j).ropes.tubes.capX
 have ht (F:(j:I)→ Sweep (N' j)): Menu (fun j x=>traceMeter W (Ka j) 0 (X' j) (flashA (F j) (Z j x))) := by
   let V(i):= flashA (F i) ∘ Z i
   exact (verve_t V (visor_gale Z hz F) (fun i=>(revM _).measurable.comp (hZ i)) hv hE hq.2 hq.1 hp.le Λ.dpos hb.le).1
 have ha(i':Axis)(j): Trunk (node (0:Site (N' j))) (FS j i') Q a b Λ.d:= by unfold Q; rw [← he j]; exact ((w j).ropes.tubes.hatJ i')
 cases L
 · have hp:= (verve_t Z hz hZ hv hE hq.2 hq.1 hp.le Λ.dpos hb.le).1 -- remove explicit
   exact Menu.scale hp hI
 · next x=> exact Menu.scale (ht (fun i=> gridTulip x 0)) hI
 · next i'=>
       have hm:= (verve_t Z hz hZ hv (ha i') hq.2 hq.1 hp.le Λ.dpos hb.le).2; exact hm
 next i' z=>
    let x(j:I):= alongM m (X0 j) i' z; let Tu0(j:I):= (ha i' j).station (x j)
    exact (verve_t Z hz hZ hv Tu0 hq.2 hq.1 hp.le Λ.dpos (show 0 ≤ Tenant.quota^2*b from mul_nonneg (sq_nonneg _) hb.le)).2
end vote
end StageW
end YM.CF.Buffered.Afterglow.Tapestry
