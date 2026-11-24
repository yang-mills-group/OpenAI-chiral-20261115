import GaugeFieldConstruction.FancyLightL
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke SelectionAnalysis
open Repertoire 
variable {P:Spine}
namespace Shower
open Complex Mink SignetS YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember YM.GaugeFieldConstruction.Ember.Volumetric NSF.Boundary
variable {n:ℕ}{cost:ℕ→P.Test→ℂ} (C:Porch P cost timeAxis)
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {X F:CloudsL}
open NSF.Work.C22 -- uses Types aliases in YM.Boundary need namespace qualified
local notation "Ξ"=> C.groundHab
local notation "Eχ"=> C.BrightHab.E
local notation "Uₛ"=> C.BrightHab.U
local notation "Bφ" x:max=> Small.bufferF x
variable (A:AllocatedL P) (R:ΧiMars →ₗ[ℂ]ScreensJ P)
open NSF.LD
-- purchase trace exactly across BOTH S & parts. sᵧ≠S support pre-tilt allowed uses only on-image real poses. δ-rate
variable (X) (D:SurfCheckL F)
variable (Cw:∀ j:Axis,Porch P cost j)
variable (g:CalRL Cw X R)(hX: SurfCheckL X)
-- permutation
variable {m:ℕ}
private noncomputable def turn (n m:ℕ):Equiv.Perm (Fin (n+m)):= (finSumFinEquiv.symm.trans (Equiv.sumCongr Fin.revPerm (Equiv.refl (Fin m)))).trans finSumFinEquiv
lemma turnedLeftL (i:Fin n): turn n m (Fin.castAdd m i)= Fin.castAdd m i.rev:=by simp [turn] -- tune
lemma turnedRightL (i:Fin m): turn n m (Fin.natAdd n i)= Fin.natAdd n i:=by simp [turn]
local notation "pHκ"=> SmallRimL (Cw timeAxis) R A X D
open FirstPackMars
include g hX
lemma HullStageηL (W:NSF.Boundary.Waves (SurfRimL F))(v:W.Region (SurfRimL X))(s:(SurfRimL F).RealSpin): OnImage (pHκ) D.AsterBackL W:=by
 intro n m p q hp hq y z x r a b h e
 let V:=place x y; let Y:=place r z
 let d:= CompellL A p y x h hp; let f:= CompellL A q z r e hq
 let T:=NSF.Table.Pairing.closedUp timeAxis V Y
 let A':=stampsEL D a; let B':=stampsEL D b; let Α(i):=R (A' i); let Β(i):=R (B' i); let A2(i):=TurnupMars timeAxis (A' i); let Α'(i):= R (A2 i); let F':=Fin.append A2 B'
 rw [traceVectorL (Cw timeAxis) X A R D p y x a h hp,traceVectorL (Cw timeAxis) X A R D q z r b e hq]
 change inner ℂ (ChargeEntryMars _ d Α) (ChargeEntryMars _ f Β)= _
 have he:=BookingActMars Cw Α Β Α' V Y d f (fun i σ=>g.warmL (A' i) timeAxis σ) (fun i=> g.showL (A2 i)) (fun i=> g.showL _)
 have hv: Fin.append Α' Β=(fun i=>R (F' i)):=by funext i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;> simp [F'] <;> rfl
 have ha:ΦplanR _ T∈ VplaneR _ timeAxis:=char_R ⟨PolesLMars d.L f.L d.pol f.pol,OpenRollR (TerraceOpensMars V Y d f)⟩
 rw [he,hv,←g.salute (n+m) F' T ha]
 let c:=turn n m; let H:=SurfRimL F; let sA(i:Fin n):H.Tag:=⟨(a i.rev).1,H.adj s (a i.rev).1 timeAxis (a i.rev).2⟩; let k:=Fin.append sA b
 let z':=NSF.Bid.bothH y z; let x':=bothSpace x r
 have Q:NSF.Points.rearrange c T=place x' z':=by
    ext1 i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i
    · rw[NSF.Points.rearrange_at,turnedLeftL]; simp only[T,NSF.Table.Pairing.enter,place,bothSpace,NSF.Bid.bothH, Fin.append_left,x',z',points_apply]; exact reflect_position (x i.rev) (y i.rev)
    rw[NSF.Points.rearrange_at,turnedRightL]; simp [T,x',z', place,bothSpace,NSF.Bid.bothH, NSF.Table.Pairing.leave,Y]
 have hV: T∈ conf (n+m):=by intro x y p; exact ha (congrArg (fun z:E4=> z timeAxis) p) -- tune
 rw [← hX.symmetry c F' T hV,Q]
 change _= W.F _ (iz ∘ z') x' _
 have hθ:NSF.Bid.bothT (pinned∘ a) (pinned∘ b) D.AsterBackL=(pinned ∘ k):=by
    funext i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i
    · simp only[k,Function.comp_apply,NSF.Bid.bothT, Fin.append_left]; exact D.AsterLiberL s _ _
    simp only[k,Function.comp_apply, NSF.Bid.bothT,Fin.append_right]
 rw[hθ, show W.F (n+m) (iz ∘ z') x' (pinned ∘ k) = _ from v.roots _ k x' z' (eastBoth h e), D.chartAngleL]
 congr 1; ext1 i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i
 · simp only[F',k,Function.comp_apply,c,turnedLeftL,Fin.append_left] -- use c unfolds
   exact (D.HonAdjL s (a i.rev).1 (a i.rev).2).symm.trans (congrArg (fun x:(SurfRimL F).Tag=> D.HingeL x.1 x.2) (Fin.append_left sA b i).symm)
 simp only [F',k,Function.comp_apply]; rw[turnedRightL]; simp only [Fin.append_right]; exact congrArg (fun x:(SurfRimL F).Tag=>D.HingeL x.1 x.2) (Fin.append_right sA b i).symm
#print axioms HullStageηL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
