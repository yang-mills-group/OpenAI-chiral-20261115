import GaugeFieldConstruction.MidasLJ
import GaugeFieldConstruction.OptioJ
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
variable {P:Spine}{X Z:Type}[Fintype X][Fintype Z][LinearOrder X][LinearOrder Z]
variable {θ:BandS→ℕ}{G:ℝ}{f0:ℕ}
variable (p:RosterJ P θ G f0)
-- Bamboo table for all visits.At arrays even torus support, t Mind consumed.

local notation "ΤΓ"=> P.run
variable (B0:SωJ θ)(M:JωL θ)
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke
variable (x:P.VMark)(R:Signed × Bool)(u:BandS)
local notation "Ξu"=> Fin (θ u)
local notation "η"=> FrameK (Fin (θ u))
variable (pu:Adept_T θ B0 M G)
-- Flexible anchor representation. stores assertion on arbitrary Movement Words.May align proofs of R3 via composition. KeyScope.S.
variable (L:finsJ)
local notation "Υs"=> ScaleμJ P.par u.val
-- CASH in force p P through procurement. preservation under Delayed (single.U)
local notation "ΚΡ"=> CalendarJ p B0 M
variable (A: CalendarJ p B0 M)
-- price limits of approximants.Any other heights at same point even with multiple gaps.N.Helper loan.
variable (T:LampHouseJ (θ:=θ) u) (D:P.Heritor)(V:LampΤJ p B0 M x R u A T D.path)
local notation "Zγ"=> FrameK (Fin (θ u))
local notation "ι" i:max=> D.path.subSeq i
local notation "gp" i:max=> P.gatePeriod (D.path.subSeq i)
local notation "gq" i:max=> P.gateCut (D.path.subSeq i)
local notation "βζ"=> FlavorRateJ P u
local notation "Κg"=> ΦWallet p
variable {f s l:ℕ}(g:f0≤ f)(s0:f0 ≤ s)
-- Portrait in all Habitat pads at Slabs.Location.Mar.K.Kernel.
local notation "νP" => RankQJ P.par
local notation "Kρ"=> p.price
local notation "gR" => RStepJ P.par
local notation "βρ" => stepRateJ P.par u.val
variable {r i k:ℕ} (z:Cover)
local notation "φY" s:max z:max=> strideΨJ P f s z
local notation "Wκ"=> Rigχ P f z
local notation "yκ"=> fleetΨJ P f z x
local notation "ΩW"=>ΟGlow (Rigχ P f z f) false P.par
local notation "Κφ" T:max s:max r:max κ:max=>AcJ (T:LampHouseJ u).stairs r s κ -- use explicit.
section
variable (T':LampHouseJ (θ:=θ) u)(H':LampΤJ p B0 M (fleetΨJ P f z x) R u A T' D.path)
include V H' g
lemma PlatoO (q:f≤ r):DownJ T.stairs r f q= DownJ T'.stairs r f q :=by
 have e:= CopalJ p B0 M x R u A T D V g (yκ) R (Wκ) false (fleetBuysJ x R z) T' H' q le_rfl -- binder
 have he(X:FrameK (Fin (θ u))): hoodAJ (ΩW) X=X:=funext fun i=>ΕbrαJ _ rfl _
 apply Prod.ext
 · exact LinearMap.ext fun x=>by have ht:=e.1 x; rw[he,he] at ht; exact ht
 exact LinearMap.ext fun x=>by have ht:=e.2 x; rw [he, ΕbrαJ (P:=P) _ (by rfl)] at ht; exact ht
lemma ΞO (q:f≤ r): ∃ T₀:ThreadJ (E:=Fin (θ u)), ClipOneJ P u f T₀ ∧ SpanPort_J u T'.stairs (↑(ScaleμJ P.par u.val):ℂ) (T.sun L r) (T'.sun L r) T₀ q:=by
 have ht:=PhΘi p B0 M x R u L A T D V g (yκ) R (Wκ) false (fleetBuysJ x R z) T' H' q; let V':= (T.sun L r); let X:= Rigχ P f z f
 have he(i:FrameK (Fin (θ u))) : hoodAJ (ΟGlow X false P.par) i=i:=funext fun i=> ΕbrαJ X rfl _
 have hu:=ΕlassJ X false P.par V'; rw[show CBissJ X false P.par V'=V' from ?_] at ht; exact ht
 refine Prod.ext (LinearMap.ext fun i=>?_) (LinearMap.ext fun i=>?_)
 · have hx:=hu.1 i; rw [he,he] at hx; exact hx.symm
 have hv:=hu.2 i; rw [he,ΕbrαJ X rfl] at hv; exact hv.symm
variable (v:FrameK (Fin (θ u))) (q:f≤ r)
omit H'
lemma WarmStart (q:f≤ r): let R':=(DownJ T.stairs r f q); let A:=(T.rev L r).1 (R'.1 v);
 LoomK A ≤2*((stepRateJ P.par u.val)^(r-f)*LoomK v)∧ LaunchLJ B0 x R u L T D f r q v= PaletteEJ B0 x R u D r A - (R'.2 v+(T.sun L r).2 A) • 1 ∧ BrJ u (T.sun L r).1 A= R'.1 v := by
 intro R' X; let z' := Lens_R p B0 M x R u L A T D.path V r (g.trans q)
 refine ⟨(z'.2.1 (R'.1 v)).trans ?_, rfl, DFunLike.congr_fun z'.2.2 (R'.1 v)⟩
 apply mul_le_mul_of_nonneg_left _ (by norm_num); unfold R'; rw [DownL]; exact (ΞPlc p B0 M x R u A T D V g q).1 _ -- tune
include H' q
local notation "Liftμ"=> (ScaleμJ P.par u.val)
-- express compensated phase picks. useful Off.Norm shift U in L^basis.
lemma FleetBillQ : let R':= DownJ T'.stairs r f q; let C:=T.sun L r; let U:=T'.sun L r; let y:= fleetΨJ P f z x; let X:= (T.rev L r).1 (R'.1 v);
 ∃ E:ThreadJ (E:=Fin (θ u)), ClipOneJ P u f E ∧
      MeshΦ p B0 M y R u pu A T' D H' (g.trans q) (BrJ u (T'.sun L r).1 X)+(U.2 X) • CandΛJ P -(R'.2 v+C.2 X) • CandΛJ P=
      MeshΦ p B0 M y R u pu A T' D H' g v - (Liftμ:ℂ)^(r-f) • (MeshΦ p B0 M y R u pu A T' D H' g (E.1 X) + (E.2 X) • CandΛJ P):=by
 intro R' C M' y X; let d:= r-f; let l:ℂ:= (ScaleμJ P.par u.val:ℂ)^d
 obtain ⟨E,HE,K⟩:= ΞO p B0 M x R u L A T D V g z T' H' q; refine ⟨E,HE,?_⟩; obtain ⟨hk,hκ⟩:= K X; let U:=MeshΦ p B0 M y R u pu A T' D H' (g.trans q)
 let V':=MeshΦ p B0 M y R u pu A T' D H' g; let Tη:= CandΛJ P; change U _ + M'.2 X • Tη- (R'.2 v+C.2 X) • Tη= V' v - l • (V' _+ _)
 let F:=DownJ T.stairs r f q; have hv:F=R':= PlatoO p B0 M x R u A T D V g z T' H' q; let Q:=R'.1; let a:=R'.2; let b:= E.1 X
 have ht:X= (T.rev L r).1 (F.1 v):=congrArg (fun F:ThreadJ (E:=Fin (θ u))=>(T.rev L r).1 (F.1 v)) hv.symm
 have hx:X+C.1 X=Q v:= by rw[ht]; exact (WarmStart p B0 M x R u L A T D V g v q).2.2.trans (DFunLike.congr_fun (congrArg Prod.fst hv) _) -- tune binder. coe
 have hP:C.1 X-M'.1 X= l • Q b:=by unfold Q R'; rw[DownL]; exact hk -- let
 have hA:C.2 X-M'.2 X=l*(E.2 X-a b):=hκ
 have hU(i): V' i=U (Q i)- a i • Tη:=by unfold Q a R'; rw [DownL]; exact gateLeyJ p B0 M y R u pu A T' D H' g i q
 rw [show BrJ u (T'.sun L r).1 X = Q v- l • Q b from (by change X+M'.1 X=_; rw[←hx,←hP]; abel), hU v,hU]
 have aa:U (Q v-l • Q b) = U (Q v)-l • U (Q b):= ( (Φwall p B0 M y R u pu A T' D H' (g.trans q)).map_sub (Q v) (l • Q b)).trans (congrArg (fun m=>U (Q v)-m) ( (Φwall p B0 M y R u pu A T' D H' (g.trans q)).map_smul l (Q b)))
 rw[aa,show M'.2 X=C.2 X-l*(E.2 X-a b) from (by rw[←hA]; abel)]
 funext i S J; simp only [Pi.add_apply,Pi.sub_apply, Pi.smul_apply]; simp only [add_smul,sub_smul,mul_smul,smul_add,smul_sub]; unfold b a Tη; abel
#print axioms FleetBillQ
end
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
