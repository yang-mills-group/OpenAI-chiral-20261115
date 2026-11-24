import GaugeFieldConstruction.DresdenJ
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
open Etch
local notation "zA" s:max=> GrowJ P f s
local notation "κs"=> (GrowJ P f s:ℤ)
local notation "W_η"=> WorkWJ P f
local notation "ws"=> GrowJ P f s* WorkWJ P f
local notation "Zγ"=>Mapnest P f x
local notation "ΚΩ"=> XûJ P.par P.width f
noncomputable def HearthJ (P:Spine)(f s:ℕ)(x:P.VMark)(j:Axis):Cover:= fun i=>(GrowJ P f s:ℤ)*pet (Mapnest P f x) j 0 i
local notation "Θζ"=> HearthJ P f s x j
local notation "Vg"=> fShiftJ P f j x
local notation "ΕΦ"=> ruler (KΑ).B
local notation "ZΩ" => pet (Mapnest P f x) j 0
local notation "ℓχ" => P.par.R.L.val
lemma IvoryJ (i:ℕ)(t:f ≤ s): (More (side P.run i s)).val=GrowJ P f s*(More (side P.run i f)).val:=by
 suffices h: (side P.run i s).val= GrowJ P f s*(side P.run i f).val by
    exact (congrArg (·*2) h).trans (mul_assoc ..)
 obtain ⟨u,rfl⟩:= Nat.exists_eq_add_of_le t
 unfold GrowJ; rw [Nat.add_sub_cancel_left,refine_side] -- tune
lemma HearthSceneJ {i r:ℕ}(a:f ≤ s)(p:Proscenium P.calibration.B (GrowJ P f s*WorkWJ P f) (side P.run i s) r): Proscenium P.calibration.B (WorkWJ P f) (side P.run i f) r:=by
 have h: SlabMark.Etch.pitch (KΑ).B (ws) = GrowJ P f s*SlabMark.Etch.pitch (KΑ).B (WorkWJ P f):=by unfold SlabMark.Etch.pitch; ring -- ambiguity
 obtain ⟨y,d,b,v⟩:=p; rw[h,IvoryJ P f s i a] at b v
 have hv:0< GrowJ P f s:= by unfold GrowJ; have ht:=P.par.R.L.property; positivity
 refine ⟨?_, d,Nat.le_of_mul_le_mul_left ?_ hv,Nat.le_of_mul_le_mul_left ?_ hv⟩ -- annotations
 · unfold WorkWJ; have h:=NumberRK P f; omega
 · rw[←mul_assoc]; exact b
 calc
  _ ≤ _:=v
  _ = _:=by ring
lemma BendEra (i:Axis)(u:ℤ): globeJ P.par f s (i,SlabMark.Etch.parting P.calibration (WorkWJ P f:ℕ) (pet (Mapnest P f x) j 0) i u)=SlabMark.Etch.parting P.calibration (GrowJ P f s*WorkWJ P f:ℕ) (HearthJ P f s x j) i u:=by
 unfold SlabMark.Etch.parting globeJ gaugeT HearthJ GrowJ Heat.gaugeShift; dsimp only; push_cast; ring
section MosaicWc
variable {u:Cover}{F G:Family P.calibration}
-- step-by-step Inset moves at f
private lemma goInsets {g:Cover}{W:ℕ}{u σ:Cover}{R:ℕ}(P:Spine)(h:Inset P.calibration W σ u R g)(v:ℤ)(j:Axis): Inset P.calibration W σ (SlabMark.Etch.pushed j v u) R ((plane j (gaugeT P.calibration (W*v))).motion ((plane j 0).motion g)):=by
 intro i; have h:=h i; rw[fling_move]; by_cases a:i=j
 · subst i; rw [if_pos rfl,fling_move,if_pos rfl,ruler_offset]; unfold SlabMark.Etch.pushed; rw [pet_i]; unfold runnel at *; constructor <;> linarith [h.1,h.2]
 · unfold SlabMark.Etch.pushed; rw [if_neg (Ne.symm a),pet_j _ a,fling_move,if_neg (Ne.symm a)]; exact h
private lemma flipInset {g:Cover}{W:ℕ}{u σ:Cover}{R:ℕ}(P:Spine)(h:Inset P.calibration W σ u R g)(v:ℤ)(j:Axis): Inset P.calibration W σ (SlabMark.Etch.bent j v u) R ((plane j (SlabMark.Etch.parting P.calibration W σ j v)).motion g):=by
 intro i; have h:=h i; rw [fling_move]; by_cases a:i=j
 · subst i; unfold SlabMark.Etch.parting; rw[if_pos rfl,ruler_offset]; unfold SlabMark.Etch.bent; rw [pet_i]; unfold runnel at *; constructor <;> linarith [h.1,h.2]
 · unfold SlabMark.Etch.bent; rw [pet_j _ a, if_neg (Ne.symm a)]; exact h
lemma LaurelLocatedJ (p:SlabMark.Etch.Located P.calibration ((GrowJ P f s* WorkWJ P f:ℕ):ℤ) (HearthJ P f s x j) (relocate P.calibration j ((GrowJ P f s:ℤ)* fShiftJ P f j x) F) u G) : ∃ l:LaurelJ,G=VivaJ P.par f s P.calibration l F∧ Inset P.calibration (WorkWJ P f) (pet (Mapnest P f x) j 0) u (10*XûJ P.par P.width f) ((forgeιJ P.par f f l).motion (adventJ P x f)):=by
 induction p with
 | start=>exact ⟨terraceJ P Vg j,(VTerrace P f s Vg j F).symm,Ridge_j P x f j⟩ -- tune
 | @go u G i v z ih=>
    obtain ⟨l,rfl,h⟩:=ih; let k:ℤ:= WorkWJ P f*v; let L:= terraceJ P k i++ l; let b:= VivaJ P.par f s P.calibration l F; let A:= (forgeιJ P.par f f l).motion (adventJ P x f); have he: VivaJ P.par f s P.calibration L F= relocate P.calibration i (κs*k) b:= VTerrace P f s k i b -- defeq? ++
    refine ⟨L,?_, ?_⟩
    · rw [he]; unfold k; push_cast; rw[mul_assoc] -- tune WS
    · have ht:(forgeιJ P.par f f L).motion (adventJ P x f)=(plane i (gaugeT KΑ k)).motion ((plane i 0).motion A):=by
        let x':=adventJ P x f; change (joinX (plane _ (globeJ P.par f f _)) (joinX (plane i (globeJ P.par f f _)) (forgeιJ P.par f f l))).motion x'= _; rw[palm,palm]; simp [globeJ,A,x']
      rw [ht]; exact goInsets P h v i
 | reflect i v z ih=>
    obtain ⟨l,rfl,t⟩:=ih; let a:=SlabMark.Etch.parting KΑ (W_η) (pet Zγ j 0) i v; let H:ProngJ:=(i,a)
    refine ⟨H::l,?_,?_⟩
    · change mirror _ i _ _=mirror _ i (globeJ P.par f s H) _
      rw [show globeJ P.par f s H=_ from BendEra P x f s j i v] -- tune
    · obtain g:= flipInset P t v i; have hr: forgeιJ P.par f f (H::l)=joinX (plane i a) (forgeιJ P.par f f l):=by simp [forgeιJ,globeJ,H]
      rw [hr,palm]; exact g
#print axioms LaurelLocatedJ
end MosaicWc
#check refine_side
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
