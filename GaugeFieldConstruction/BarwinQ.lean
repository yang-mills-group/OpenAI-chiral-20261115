import GaugeFieldConstruction.BayburtQ
import GaugeFieldConstruction.CarillonQ
import GaugeFieldConstruction.HighlightQ
import GaugeFieldConstruction.PalisadeQ
import GaugeFieldConstruction.StevanjaJ
import GaugeFieldConstruction.SakhaJ
import GaugeFieldConstruction.VoletyJ
import GaugeFieldConstruction.LayGateQ
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
set_option maxHeartbeats 78000
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
open SlabMark.Weir
variable (m:ℕ)
local notation "Z₁"=> AgateQ P
local notation "ιw"=> WailsQ P f m
local notation "wQ"=> WoodQ P f m
local notation "Vκ"=> chordQ P f
local notation "ζp"=> cautionQ P f
local notation "G'^" M:max=> GrowJ P f s*M
local notation "VΘ"=> fWigQ P f s
local notation "Y£"=> P.run
local notation "κς"=> KΑ
local notation "κφ"=> P.par
-- tested ANY f-quilt at s, explicit lifts
-- visits at f. define Panel.Reader rule that yields all $sharp$s. No support included since pair arcs need separations at s'
section
variable (t i k:ℕ)(b:f≤ s)(u:s≤ t)
variable (p:ProngJ)(L:LaurelJ)
abbrev gloryQ (p:ProngJ): ProngJ:= (p.1,globeJ P.par f s p)
def QTapeQ(L:LaurelJ):LaurelJ:=L.map (gloryQ P f s)
include b u
lemma sparkQ : globeJ P.par s t (gloryQ P f s p)= globeJ P.par f t p:=by unfold gloryQ globeJ; dsimp only; rw [← mul_assoc,←pow_add, show t-s+(s-f)=t-f from by omega]
lemma VivaPowerQ (A:Family P.calibration):VivaJ P.par s t P.calibration (QTapeQ P f s L) A= VivaJ P.par f t P.calibration L A:=by
 induction L with
 | nil=>change A=A; rfl
 | cons p L ih=> change Tower.mirror _ p.1 (globeJ P.par s t _) _=Tower.mirror _ p.1 (globeJ P.par f t _) _; rw [sparkQ _ f s t b u]; exact congrArg (Tower.mirror _ _ _) ih -- tune
lemma DealQ : wayZJ P.par s t (QTapeQ P f s L)=wayZJ P.par f t L ∧ forgeιJ P.par s t (QTapeQ P f s L)=forgeιJ P.par f t L:=by
 induction L with
 | nil=>exact ⟨rfl,rfl⟩
 | cons p l ih=>
   have h:= sparkQ P f s t b u p -- u shadow
   exact ⟨congrArg₂ joinX ih.1 (congrArg (plane p.1) h),congrArg₂ joinX (congrArg (plane p.1) h) ih.2⟩
lemma tokenRise (x:P.VMark): let R:=fun f t v=> (forgeιJ P.par f t v).motion (adventJ P x t); R s t (QTapeQ P f s L)= R f t L:=by intro R; unfold R; rw [(DealQ P f s t b u L).2]
end
-- layout lifts.
abbrev ChildQ (X:Type):= Lex (X × Bool)
def labelQ (x:X)(b:Bool):ChildQ X:= toLex (x,b)
def bay_HQ (x:ChildQ X):X:= Prod.fst (ofLex x)
def tip_HQ (x:ChildQ X):Bool:= Prod.snd (ofLex x)
def tagHQ (b:Bool):X↪ ChildQ X where
 toFun x:= labelQ x b
 inj' _ _ h:= congrArg bay_HQ h
def LabelRefQ(x:X): ChildQ Unit ↪ ChildQ X where
 toFun i:= labelQ x (tip_HQ i)
 inj' i j h:= by change toLex _= _; apply toLex.injective; exact Prod.ext (Subsingleton.elim _ _) (congrArg (@tip_HQ X) h)
def BusCQ (x:X):Unit↪X:=⟨fun _=> x,fun _ _ _=>Subsingleton.elim _ _⟩
lemma StrictLabelR (x:X):StrictMono (LabelRefQ x):=by
 intro i j h; change (toLex (_,_):ChildQ X) < toLex (_,_); apply Prod.Lex.right; rcases i with ⟨⟨⟩,a⟩; rcases j with ⟨⟨⟩,b⟩; exact ((Prod.Lex.lt_iff.mp h).resolve_left (lt_irrefl _)).2 -- tune lemma lex type has Order.X.
variable (x y:P.VMark)(u:Bool→ P.VMark)(L:X→ LaurelJ)(t i k:ℕ)
abbrev ChildSlotℓ (p:ChildQ X):P.VMark:= u (tip_HQ p)
#check ChildSlotℓ
def UpperMQ (f s:ℕ)(p:ChildQ X):LaurelJ := QTapeQ P f s (L (bay_HQ p)) -- tune order
#check UpperMQ
open BoonsθJ
abbrev SpadeQ (p:Bool): Seat (side P.run i t):= Strideθ P.run i (short_TRA (u p)) t ()
local notation "Τp" t:max=> (Strideθ P.run i (SailRoute P s (ChildSlotℓ P u) (UpperMQ P L f s)) t)
local notation "Αp" t:max=> (Strideθ P.run i (SailRoute P f (fun _:X=>u false) L) t)
-- compare via movement shape without Sweep.Comp. T fixed scales
lemma DentonQ (r:f≤ s)(z:s ≤ t)(j:X) : (Τp t) (tagHQ false j)= (Αp t) j:=by
 unfold Strideθ LodgeJ; exact congrArg _ (tokenRise P f s t r z (L j) _)
lemma CupSeQ (x:X): separation ((Τp t) (tagHQ false x)) ((Τp t) (tagHQ true x))= separation (SpadeQ P u t i false) (SpadeQ P u t i true):=by
 let N:=side P.run i t; let F:= forgeιJ P.par s t (UpperMQ P L f s (tagHQ false x))
 have h0(b:Bool):(Τp t) (tagHQ b x)= F.anon _ (SpadeQ P u t i b):= (Shape.anno ..).symm
 rw[h0,h0]; unfold Shape.anon; rw [affine,affine,separation_translate,separation_signed] -- tune
-- economy geometric qualification
structure CratonQ (ν:ℕ):Prop where
  stitch: 20*XûJ P.par P.width s≤ separation (SpadeQ P u s i false) (SpadeQ P u s i true)
  price: separation (SpadeQ P u s i false) (SpadeQ P u s i true) ≤ ν
  wage: (Papal.gram P.run s i k).p.B^3≤ν
  space: P.par.R.L.val*(4*(Papal.gram P.run s i k).p.B+2)+ 2*(Papal.gram P.run s i k).p.B < separation (SpadeQ P u s i false) (SpadeQ P u s i true)
  afford: ν+20*XûJ P.par P.width s ≤ DuoJ P.par P.width f s
variable {L} (a:f ≤ s)(v:s ≤ P.run.uv k)
local notation "Ρ"=> SailRoute P s (ChildSlotℓ P u) (UpperMQ P L f s)
local notation "ΤG"=> Strideθ P.run i (Ρ)
local notation "Z"=> SailRoute P f (fun _:X=>u false) L
-- charge cross-groups ascent
variable (ν:ℕ)
include a v
lemma PyxidQ (h:CratonQ P f s u i k ν)(q:ScarJ P.run i X (Strideθ P.run i (SailRoute P f (fun _:X=>u false) L)) f):ScarJ P.run i (ChildQ X) (Strideθ P.run i (SailRoute P s (ChildSlotℓ P u) (UpperMQ P L f s))) s := by
 intro x y w
 let Pq:=Τp s; let τ:= Αp s
 have h0(x:ChildQ X): separation (Pq x) (τ (bay_HQ x))≤ν:=by
    unfold Pq τ; rw [← DentonQ P f s u L s i a le_rfl (bay_HQ x)] -- order
    match x with
    | (x,b)=> cases b
              · exact (separation_self _).trans_le (Nat.zero_le _)
              · rw[separation_comm]; exact (CupSeQ P f s u L s i x).trans_le h.price
 by_cases hy: bay_HQ x=bay_HQ y
 · -- differ bits.
   rcases x with ⟨x,u⟩; rcases y with ⟨y,d⟩; change x=y at hy; subst y; cases u<;>cases d<;>first|exact (w rfl).elim|skip
   · exact h.stitch.trans ((CupSeQ P f s _ L s i x).symm.le)
   rw [separation_comm]; exact h.stitch.trans ((CupSeQ P f s _ L s i x).symm.le)
 have h':= stride_J P.run i k s f (Strideθ P.run i (SailRoute P f (fun _:X=>u false) L)) (FilmRoute P f _ _ _ i) q a v _ _ hy
 have hv: separation (τ (bay_HQ x)) (τ (bay_HQ y)) ≤ ν+(separation (Pq x) (Pq y)+ν):= (separation_triangle _ (Pq x) _).trans (Nat.add_le_add ((separation_comm ..).trans_le (h0 x)) ((separation_triangle _ (Pq y) _).trans (Nat.add_le_add_left (h0 y) _))) -- tune
 have hp:= h'.trans hv; have ht:=h.afford; change _≤ separation (Pq x) (Pq y); omega
#print axioms StrictLabelR
#print axioms CupSeQ
#print axioms PyxidQ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
