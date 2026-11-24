import GaugeFieldConstruction.RovioJ
import GaugeFieldConstruction.Metope
import GaugeFieldConstruction.FrayTideJ
import GaugeFieldConstruction.SteepleJ
import GaugeFieldConstruction.MovingH
import GaugeFieldConstruction.ZagoraJ
import GaugeFieldConstruction.VirenneJ
import GaugeFieldConstruction.TrollopJ
import GaugeFieldConstruction.ZucatoJ
import GaugeFieldConstruction.KronenJ
import GaugeFieldConstruction.MapicoJ
import GaugeFieldConstruction.LongBowJ
import GaugeFieldConstruction.OrigamiJ
import GaugeFieldConstruction.WharfΤJ
import GaugeFieldConstruction.TuristaJ
import GaugeFieldConstruction.WharfΤJ
import GaugeFieldConstruction.MoonθεJ
import GaugeFieldConstruction.LucernaJ
import GaugeFieldConstruction.EmeraldYJ
import GaugeFieldConstruction.Limbra3
import GaugeFieldConstruction.AshtonM
import GaugeFieldConstruction.Accomplished
import GaugeFieldConstruction.Kabul
import GaugeFieldConstruction.Fana
import GaugeFieldConstruction.Garlic
import GaugeFieldConstruction.Ochre
import GaugeFieldConstruction.Coral
import GaugeFieldConstruction.Dales
import GaugeFieldConstruction.Harries
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
variable (P:Spine) {X:Type}[Fintype X][LinearOrder X]
open ProbeθJ Preparation Yoke
-- Pose. Film any from Advent plus f mirrors. only valid Stamps.S.
local notation "KΑ"=>P.calibration
local notation "Kγ"=>P.par
local notation "Lγ"=> P.par.R.L
local notation "ℓν"=>P.par.R.L.val
local notation "HΥ"=> inkΛJ
variable (x:P.VMark) (f s:ℕ) (j:Axis)
-- monetary plur.

section
open Jubilee
open XGarden XGarden.MastTin
lemma LeafPoseNX (i:ℕ)(N:P.run.ir i=P.run.ir i) (A:Mark (side P.run i s))(F:Paper (side P.run i s))(h:AtSupport false univ A)(K:LaurelJ)(x:∀ i:Fields (side P.run i s),A i=marketD F i.1):
 HeadΨJ P.run f s i K A= toMark (marketD (Barber (Levier.ray false (wayZJ P.par f s K)) F)) :=by
 let k:= side P.run i s
 have hP(A:Mark k)(F:Paper k)(p:AtSupport false univ A)(q:A=toMark (marketD F))(j:Axis)(b:ℤ):reflMark j b A=toMark (marketD (Barber (Levier.ray false (plane j b)) F)):= by subst A; exact SweepTurn.same (SweepTurn.refl p j b) ⟨fun v w=> tilt_atom (Levier.ray false (plane j b)) F v⟩ -- tune arg
 have he: A=toMark (marketD F):=funext x
 have hj(X Y:Shape): Levier.ray (N:=k) false (joinX X Y)=(Levier.ray false X)*(Levier.ray false Y):=by
    rw [Levier.ray_join]; rfl -- namespace
 induction K with
 | nil=>
    let W:=plane 3 0; let V:=Levier.ray (N:=k) false W
    change A= toMark (marketD (Barber (Levier.ray false (incX 1)) F)); rw [← gaugeSquare 3 0,hj, ←barber_L]
    exact (h.refl_refl ..).symm.trans (hP (reflMark 3 0 A) _ ((h.refl ..).mono (subset_univ _)) (hP A F h he 3 0) 3 0)
 | cons j l ih=>
    let V:= plane j.1 (globeJ P.par f s j)
    let X:= HeadΨJ P.run f s i l A
    change reflMark j.1 _ _=toMark (marketD (Barber (Levier.ray false (joinX (wayZJ P.par f s l) V)) F)); rw[hj, ← barber_L]; exact (hP X _ (HeadWax _ _ _ _ _ h) ih j.1 _)
lemma ΦHomeNX (i:ℕ)(o:Cover)(n:ℕ)(A: Family P.calibration) (y:AtSupport false (Lattice.halo n {wrap (More (side P.run i s)) o}) (Tapestry.exhibit P.run P.large s i A))(L:LaurelJ):
 AtSupport false (Lattice.halo n {wrap (More (side P.run i s)) ((forgeιJ P.par f s L).motion o)}) (Tapestry.exhibit P.run P.large s i (VivaJ P.par f s P.calibration L A)) :=by
 rw [←OathFest]; let K:=side P.run i s; let U(X:Cover):=(Lattice.halo n {wrap (More K) X})
 induction L with
 | nil=> simpa [forgeιJ,Shape.motion,incX] using y -- tune
 | cons a l ih=>
    let z:= globeJ P.par f s a; let B:= plane a.1 z; let S:=LampsJ P.run i (fun _=>B) false s; let R:= (forgeιJ P.par f s l); let H:= R.motion o;
    have hs (X:Cover): B.motion (B.motion X)=X:= by rw [←palm,show joinX B B= incX 1 from gaugeSquare a.1 z]; simp [incX,Shape.motion]
    have ht (Q:Cover):(Layout.Fren.sh S (wrap (More K) Q))=wrap (More K) (B.motion Q):=by nth_rw 1 [← hs Q]; exact sector_o B false _ -- tune path
    have hp:(U H).image (B.anon K)=U (B.motion H):=by
       have he: B.anon K = (boxA S).symm := funext fun j=>by rw [←wrap_lift j]; rw [Shape.anno]; exact (ht _).symm -- type anon? def map.
       rw[he]; change (U H).image ⇑(boxA S).symm.toEmbedding= _; rw [← map_eq_image]
       change Salt.actY S (Lattice.halo n {wrap (More K) H}) =_; rw[←Salt.walkA]
       unfold Salt.actY; rw [map_singleton]; exact congrArg (fun x=> Lattice.halo n {x}) (ht H)
    rw [show ((forgeιJ P.par f s (a::l)).motion o)= B.motion H from palm ..]; change AtSupport _ (U (B.motion H)) _; rw[←hp]; exact ih.refl ..
#check AtSupport.refl
#check Tilt
#check Levier.ray_join
#check Salt.walkA
end
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
