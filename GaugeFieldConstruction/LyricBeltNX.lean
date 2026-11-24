import GaugeFieldConstruction.PrismaticRouteNX
import YM.SU5.Assay.Belt
import GaugeFieldConstruction.MountainMedalNX
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
-- actual Coalition: one spine/view/archive, one registration, one path, and APPROVED solicitation of orientation frame and dynamics. Predicate open Badge to allow further needs while preserving same purchases.
open RosterJ BoonsθJ SignetS Patrons ChSigFe
open CF.XGarden.MastTin.ArtCart
open SpaΘ
open Fock.Flux
open Papal
open Yoke SelectionAnalysis
open Oath.BellPrice
open GaugeFieldConstruction.Phys
open Fock
open GaugeFieldConstruction
open Fathom Ember
open Calibration.Floor Calibration -- tune
namespace Glaze
variable {P:Spine}{i:Axis}{s t w:ℕ}
local notation "Ζp" => ruler P.par.block
local notation "χ"=>P.stampPin t
local notation "Nt"=> timeMesh P.par
variable(B:P.Glaze)
abbrev ocSpanNX (v t:ℕ):ℕ:= P.par.R.L.val^(t-v)*B.w
lemma stampPreserveNX(h:s≤t): χ (B.ocSpanNX s t)=P.stampPin s B.w:=by unfold ocSpanNX; push_cast; exact notch_up Nt s t h _
lemma betBoundsNX : P.Marrow i t (↑(-χ (B.w:ℤ)):ℝ) (χ B.w:ℝ) B.S:=by
   rw [← minted_neg]; apply Marrow.at_size B.S |>.mpr; convert B.fits i using 1 <;> ring
lemma betAgesNX(h:s≤t):P.BFits (B.ocSpanNX s t) (volumeAround P.par P.width (t-s) B.S):=by
   intro i; have hp':= (B.betBoundsNX (i:=i) (t:=s)).refine h; rw [← stampPreserveNX B h,← minted_neg] at hp'; convert (Marrow.at_size _).mp hp' using 1 <;> ring
/-- exact growth gives later Glaze as one mark. pose Hart.Books actual. -/
noncomputable def glazeRiseNX(h:s ≤ t): P.Glaze:=
   { w:= B.ocSpanNX s t
     pos:= Nat.mul_pos (pow_pos P.par.R.L.property _) B.pos
     S:= volumeAround P.par P.width (t-s) B.S
     F:= (B.apron s).full P t
     inlet:=(proceeds _ _ P.history.circuit s (t-s) ((Tapestry.locates ..).mp B.inlet)).1
     fits:= B.betAgesNX h
     color:= (B.apron s).fullColor P _ }
-- general ticker pad bills at SAME pedestal height
lemma ownsTokenNX {l r:ℤ}(h:(-(l:ℤ))≤ -(B.w:ℤ))(q:(B.w:ℤ)≤r): P.HabitLevel i B.F t (-χ l) (χ r) (P.grantGapNX i t B.w B.F (χ l:ℝ) (χ r:ℝ)) t:=by
    have hu:= B.betBoundsNX (i:=i) (t:=t)
    let n:=(l+r).toNat; have hv0:0<B.w:=B.pos; have he:(n:ℤ)=l+r:=Int.toNat_of_nonneg (by omega); have hs:-l+(n:ℤ)=r:=by omega
    have hx:= BEntry.mesh_frame B.inlet (s:=t) (j:=i) (a:=-l) (w:=n) (by omega) fun x k=> And.intro (le_trans (by rw [←minted_neg]; exact (minted_le _ _ _ _).mpr h) ((hu x k).1)) ((hu x k).2.trans (by rw [hs]; exact (minted_le _ _ _ _).mpr q))
    have hp:P.HabitLevel i B.F t (-χ l) (χ r) _ t:=⟨le_rfl,-l,n,minted_neg P t l,by rw [←minted_neg,←minted_sub];congr 1; omega,by rw [convey_start]; exact hx,rfl⟩
    have ht: P.tock t B.w ≤ (χ l:ℝ):= (minted_le _ _ _ _).mpr (by omega); have hk:P.tock t B.w ≤ (χ r:ℝ):=(minted_le _ _ _ _).mpr q
    rwa [Habitable.same (show P.Habitable i _ _ _ _ _ from ⟨t,hp⟩) (hearthPayNX i t B.w (B.centers i) ht hk)] at hp
variable {F G:P.Test}{a b d:P.meshPin}{X Y:P.Slabs i}
lemma HabitPairNX(p:P.HabitLevel i F t a d X t)(q:P.HabitLevel i G t d b Y t) : P.HabitLevel i (F*G) t a b (X*Y) t:=by
   obtain ⟨_,l,w',hx,hv,ht,rfl⟩:=p; obtain ⟨_,m,u,g,e,hu,rfl⟩:=q
   have he:l+w'=m:= notch_tight Nt t (by rw [notch_add]; change χ l+χ w'=_; rw[hx,hv,show notch _ t m=d from g]; abel)
   refine ⟨le_rfl,l,w'+u,hx,?_ ,?_⟩
   · rw [Nat.cast_add,show χ ((w':ℤ)+u)=χ w'+χ u from notch_add ..,e,hv]; abel
   rw [convey_start] at ht hu; simp_rw [convey_start]; rw [map_mul,show P.shifts i (-l) G=P.shifts i w' (P.shifts i (-m) G) from by rw[shifts_sum]; congr 2; omega]; exact ⟨ht.concat hu,(HabBox_concat t ht hu).symm⟩ -- tune
#print axioms glazeRiseNX
#print axioms ownsTokenNX
#print axioms HabitPairNX
end Glaze
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
