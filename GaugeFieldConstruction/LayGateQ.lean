import GaugeFieldConstruction.HitachiQ
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
local notation "Θζ"=> HearthJ P f s x j
local notation "Vg"=> fShiftJ P f j x
local notation "ΕΦ"=> ruler (KΑ).B
local notation "ZΩ" => pet (Mapnest P f x) j 0
local notation "ℓχ" => P.par.R.L.val
open WallsQ
local notation "Ζp"=>P.calibration
variable {o σ B:Cover}{w R:ℕ}{N n:Side}
-- subtract periodic offset using cop.TQ
abbrev PortsideQ (N n:Side)(w:ℕ):Prop:=0<w ∧ N.val=w*n.val
abbrev fWigQ (P:Spine)(f s:ℕ)(o:Cover):Cover:=fun i=> (GrowJ P f s:ℤ)*o i
local notation "σ₀"=>fWigQ P f s
lemma floorqQ(i:ℕ)(u:f ≤ s)(p:PortsideQ (side P.run i s) n (GrowJ P f s*w)) : PortsideQ (side P.run i f) n w:=by
 have h₁:0 < GrowJ P f s:= by unfold GrowJ; have ht:= P.par.R.L.property; positivity
 refine ⟨Nat.pos_of_mul_pos_left p.1,Nat.eq_of_mul_eq_mul_left h₁ ?_⟩ -- lhs?
 apply Nat.eq_of_mul_eq_mul_left two_pos; have hn:= IvoryJ P f s i u; have ht(x: Side): (More x).val =x.val*2:=rfl; rw[ht,ht,p.2] at hn; linarith only [hn]
def InsetQ (w:ℕ)(σ o a:Cover)(d:ℕ):Prop:=∀i,planeQ w σ i (o i)+d≤a i ∧ a i+d≤planeQ w σ i (o i+1)
lemma insetQ_ζ {a:Cover}(h:InsetQ w σ o a R)(j:Axis)(v:ℤ) :InsetQ w σ (bent j (2*v) o) ((plane j (planeQ w σ j v)).motion a) R:=by
 intro i; have h:=h i; rw[fling_move]; by_cases u :i=j
 · subst i; unfold bent; rw[pet_i,if_pos rfl]; unfold planeQ at *; constructor <;> linarith [h.1,h.2]
 unfold bent; rw[if_neg (Ne.symm u),pet_j _ u]; exact h
lemma tariffQP {o' u v:Cover}(a:InsetQ w σ o u R)(b:InsetQ w σ o' v R)(p: PortsideQ N n w)(q:buttonQ n o ≠ buttonQ n o'):
   2*R ≤ separation (wrap (More N) v) (wrap (More N) u) :=by
 obtain ⟨i,hq⟩:=Function.ne_iff.mp q
 let z:ZMod (2*n.val):= buttonQ n o' i-buttonQ n o i
 letI : NeZero (2*n.val):=⟨(mul_pos (by decide) n.property).ne'⟩
 let r:= z.val; have hr': r < 2*n.val:=ZMod.val_lt _; have hr:0<r:=by by_contra! a; exact sub_ne_zero.mpr (Ne.symm hq) (by simpa using (show z.val=0 by omega))
 have he:(↑(o i+r:ℤ):ZMod (2*n.val))= ↑(o' i):=by push_cast; rw[show ↑r=z from ZMod.natCast_zmod_val z]; unfold z buttonQ; ring
 obtain ⟨k,g⟩:= (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp he
 let C:= ((More N).val:ℤ); have hc:C=2*w*(n.val:ℤ):=by change ((↑(N.val*2)):ℤ)=_; rw[p.2]; push_cast; ring
 have ht:o' i- (o i + r)= ↑(2*n.val)*k:=g
 have hp:(w:ℤ)*(o' i)= (w:ℤ)*(o i+r)+C*k:=by rw [hc]; push_cast at *; rw [show o' i= _+_ from eq_add_of_sub_eq ht]; ring
 let W:=v i-C*k-u i
 have h:=b i; have H:=a i
 have hz:(↑(2*R):ℤ) ≤ W:=by
    obtain ⟨t,t'⟩:=H; obtain ⟨e,e'⟩:=h; unfold planeQ at *; push_cast; unfold W; linarith only [hp,t',e,mul_le_mul_of_nonneg_left (show (1:ℤ)≤ ↑r by omega) (Nat.cast_nonneg w)]
 have hy:W ≤ C- ↑(2*R):=by
    obtain ⟨t,t'⟩:=H; obtain ⟨e,e'⟩:=h; unfold planeQ at *; unfold W; push_cast; linarith only [hp,t,e',mul_le_mul_of_nonneg_left (show (r:ℤ)+1≤2*n.val by omega) (Nat.cast_nonneg w),hc]
 set T:=wrap (More N) v-wrap (More N) u; let A:= lift T i
 suffices hc: 2*R ≤ A.natAbs from hc.trans (component_le T i)
 by_contra! t
 have g:C ∣ v i-u i-A:= (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp <| congrFun (show wrap (More N) (lift T)=wrap (More N) (v-u) from by rw[wrap_lift,map_sub]) i
 have he:C∣ W-A:=by unfold W; rw[show v i-C*k-u i-A= (v i-u i-A)-C*k from by ring]; exact dvd_sub g (dvd_mul_right ..)
 have ht:= Int.le_of_dvd (show 0<W-A by omega) he; omega
-- route proof for Positions.S. Package orientation cost with s from f and parent support requirement of TWO anchors in Q1.
inductive BoothQ (σ:Cover)(w:ℕ)(B:Cover) : Cover→LaurelJ→Prop
| root :BoothQ σ w B B []
| fork {x:Cover}{L:LaurelJ}(i:Axis)(v:ℤ)(p:BoothQ σ w B x L): BoothQ σ w B (bent i (2*v) x) ((i,planeQ w σ i v)::L)
lemma micaQ {K K':Family P.calibration}(p:StakeQ P.calibration (GrowJ P f s*w) (fWigQ P f s σ) B K o K') : ∃ L:LaurelJ, K'= VivaJ P.par f s P.calibration L K ∧ BoothQ σ w B o L:=by
 induction p with
 | start=> exact ⟨[],rfl,.root⟩
 | @bends x F i v p ih=>
    obtain ⟨L,rfl,h⟩:= ih; refine ⟨_,?_,h.fork i v⟩
    change mirror _ i _ _=mirror _ i (globeJ P.par f s _) _; rw[show globeJ P.par f s (i,planeQ w σ i v)=planeQ (GrowJ P f s*w) (fWigQ P f s σ) i v from ?_]
    unfold globeJ planeQ fWigQ GrowJ; push_cast; ring -- tune unfold pred
lemma micaLocQ {x a:Cover}{L:LaurelJ}(p:InsetQ w σ B a R)(hp:BoothQ σ w B x L) :InsetQ w σ x ((forgeιJ P.par f f L).motion a) R:=by
 induction hp with
 | root=> simpa [forgeιJ,Shape.motion,incX] using p
 | @fork x l i v q ih=> rw [show forgeιJ P.par f f ((i,planeQ w σ i v)::l)=joinX (plane i (planeQ w σ i v)) (forgeιJ P.par f f l) from (by simp [forgeιJ,globeJ]),palm]; exact insetQ_ζ ih i v -- tune
#print axioms tariffQP
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
