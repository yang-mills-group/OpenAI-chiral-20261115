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
def SailRoute (x:X→ P.VMark)(u:X→LaurelJ) : Pathsθ X :=fun i s=> (forgeιJ P.par f s (u i)).motion (adventJ P (x i) s) -- section f order
#check SailRoute
lemma FilmRoute (x:X→ P.VMark)(u:X→LaurelJ)(r i:ℕ) :FilmθJ P.run i X (Strideθ P.run i (SailRoute P f x u)) f r :=by
 refine routeParent P.run i r f (fun i=>adventJ P (x i)) u ?_ -- tune arg order
 exact CanonJ P.run i f (fun i=> adventJ P (x i)) r fun i j _ _=> (P.keepsJ (x i)).1 j
lemma S_panJ (x:X→ P.VMark)(u:X→LaurelJ)(R:X→Signed × Bool)(i k:ℕ)(j:X): BoonsθJ.PanB (P:=P) (i:=i) (k:=k) (W:=SailRoute P f x u) (x j) (R j) j false (fun t=>wayZJ P.par f t (u j)) f (fun i=>BoonsθJ.KnitBJ P.par f (u i) (R i)):=by
 refine ⟨fun _ _=> SussexJ _ _ (u j) _, fun a t=>(routeExpandJ P.run i _ f a _).1, ?_⟩ -- tune
 intro s a b; unfold BoonsθJ.KnitBJ; simp; exact (routeScalarJ ..).symm
-- shipping.H qualifier. actual families moved terms.register0
abbrev HaloShip (x:P.VMark)(f t i:ℕ)(L:LaurelJ) :Support (More (side P.run i t)):= (TwineθJ P.run i Unit (Strideθ P.run i (SailRoute P f (fun _:Unit=>x) (fun _=>L))) f) t ()
abbrev ShelterJ (Z:Family P.calibration)(s:ℕ)(i:ℕ):Prop:= ∀ L:LaurelJ, AtSupport false (HaloShip P x f s i L) (Tapestry.exhibit P.run P.large s i (VivaJ P.par f s P.calibration L Z))
lemma NeapJ (v:LaurelJ) (i k:ℕ): Montana P.run i k (TwineθJ P.run i Unit (Strideθ P.run i (SailRoute P f (fun _=>x) (fun _=>v))) f) f := SturdyJ P.run i k f _ (FilmRoute _ _ _ _ _ i) fun i j h=> False.elim (h (Subsingleton.elim i j))
lemma ShelterJ.one (i:ℕ):ShelterJ P x f 1 s i:=by
 intro v; rw [BoonsθJ.VivaOne,Tapestry.actual_one]; exact AtSupport.oneM _
section
variable {P x f s}
lemma ShelterJ.advance (A G:Family P.calibration)(t:ℕ)(h:s≤t)(hp:f≤ s)(i k:ℕ)(p:(P.run.voyage i).kick ≤k)(v:t ≤ P.run.uv k)
 (g:ShelterJ P x f A s i)(b:Tapestry.exhibit P.run P.large t i G= convoy (v:=t) P.run i k h (Tapestry.exhibit P.run P.large s i A)): ShelterJ P x f G t i:=by
 intro W; let K:= Tapestry.exhibit P.run P.large s i A; have ht:AtSupport false univ K:= (g []).mono (subset_univ _)
 rw [← OathFest,b, ← HeadFund P.run i k s f hp W _ ht p h v,OathFest]; exact AbideT_J _ _ _ _ f _ (NeapJ P x f W i k) (fun _=>Tapestry.exhibit P.run P.large s i (VivaJ P.par f s P.calibration W A)) (fun _=> g W) p hp () h v
#check OathFest
#check AbideT_J
-- +/- Supports independent quals for any. union inside even
lemma ShelterJ.minus {X' Φ:Family P.calibration}{i:ℕ}(p:ShelterJ P x f X' s i)(v:ShelterJ P x f Φ s i): ShelterJ P x f (X'-Φ) s i :=by
 intro w; rw[BoonsθJ.VivaSub,map_sub]; obtain h:= (p w).addM ((v w).smulM (-1)); simpa only [sub_eq_add_neg,neg_one_smul] using h
lemma ShelterJ.scale {X':Family P.calibration}{i:ℕ} (p:ShelterJ P x f X' s i)(z:ℂ): ShelterJ P x f (z • X') s i:= by intro w; rw [BoonsθJ.VivaScale,map_smul]; exact (p w).smulM _
end
-- A paste.P physical. k Gate.L even.
open BoonsθJ
lemma HideRoomJ {θ:BandS→ℕ} {i:ℕ}(v:BandS)(μ:f≤ s) (u:SummerJ P.run f)(A:SωJ θ)(K:Signed × Bool) (y:FrameK (Fin (θ v)))(e:s≤ P.run.uv (P.gateCut i))(z:ℂ): ShelterJ P x f (PasteJ P.run (P.gatePeriod i) (P.gateCut i) P.large (r:=s) (adventJ P x s) (ThreadΨ A v K) y z) s (P.gatePeriod i):=by
 intro h; let T':=(forgeιJ P.par f s h).motion (adventJ P x s)
 let N:=Papal.count P.run s (P.gatePeriod i); have hh:300<N.val:=(u s μ).2 _
 rw [StepΩJ, PasteJ,map_sub,paperT_J,map_smul,Tapestry.actual_one]; simp only[sub_eq_add_neg, ←neg_smul]; refine AtSupport.addM ?_ ((AtSupport.oneM _).smulM _)
 refine (SafeTQJ _ _ _ P.large T' _ _ e hh).mono ?_; change (cartO T' 28).image (wrap _)⊆ halo (DuoJ P.par P.width f s-CapLJ P.par P.width) {wrap (More N) T'}; rw [ArtCart.cart_T (show 28< N.val from by omega)]; apply Lattice.Corona.halo_mono ?_ (Subset.refl _); have ht:= DuoM s f P.par P.width; omega
#print axioms HideRoomJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
