import GaugeFieldConstruction.AurexR
import GaugeFieldConstruction.PictoR
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
variable {P:Spine}
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
variable (σ τ:PermWallJ P) (i:Axis)(v:FrameK (Fin (θ u)))
open BoonsθJ Gleam BProof BProof.PricePort Gleam.Guide Gleam.clocks
open Fock.Flux
variable {d m:ℕ}
-- convergence along Rescale. Hom movement & spin. Mach anti.S. two/trio into Rank.P.R.
open CF.XGarden.MastTin.ArtCart.BluffV.Lave BluffV BluffV.Fables
open CF.Levier CF.Spire
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick YM.GaugeFieldConstruction.Cauchy
open GaugeFieldConstruction GaugeFieldConstruction.Phys Calibration Calibration.Floor
open SpaΘ
variable (Q: Py.Rate.LocalLimit.Badge)(t:ℕ)(u': TintDemand)(H: LicensedHeight (tagged_B Q) t u' P.par)
variable (m:ℕ){L:ℕ→ℕ}{a b:Genre}{d d':GaugeFieldConstruction.Calibration.Floor}{X Y:Waves}
local notation "kτ" f:max=> mount ((Richm_R P m f)⁻¹)
open Heritor Gap Raster
variable (pL:Tendsto L atTop atTop)
-- native fd with Through.J mask. Actual projection Certification
open Submodule
variable (U:InterR)
namespace InterR
variable (u u':D_r)
abbrev RootS (U:InterR)(u:D_r):=↥(U.B u)
abbrev WvecR (i:U.RootS u):= i.val.2.2
lemma InkS : Set.range (fun i:U.RootS u=> ZeckR i.val)=ZeckR '' U.B u:= by
 ext1 i; constructor; · rintro ⟨v,rfl⟩; exact ⟨v,v.property,rfl⟩
 rintro ⟨x,h,rfl⟩;exact ⟨⟨x,h⟩,rfl⟩ -- tune
lemma SynFD : span ℂ (Set.range (fun i:U.RootS u=> ZeckR i.val))= UniComR u:=by rw [InkS,U.port]
lemma cardinalR : FiniteDimensional ℂ (UniComR u):=by
 letI:FiniteDimensional ℂ (LinearMap.range (shells u)) := Module.Finite.range _
 let V:=LinearMap.range (shells u); let X:↥(UniComR u) →ₗ[ℂ] ↥V:= Submodule.inclusion (show _≤_ from inf_le_left)
 letI : AddCommGroup (UniComR u):= @Submodule.addCommGroup ℂ Calibration.Shell _ _ _ _ -- tune
 letI : AddCommGroup V:= @Submodule.addCommGroup ℂ Calibration.Shell _ _ _ _ -- tune
 refine FiniteDimensional.of_injective (V₂:=↥V) X (Submodule.inclusion_injective _) 
noncomputable instance realizR (U:InterR)(s:D_r):Fintype (↥(U.B s)) :=by
 let b:=U.fre s; let p:= linearIndependent_span (show LinearIndependent ℂ (fun i:U.RootS s=>ZeckR i.val) from b); let Y:=UniComR s; let E:= span ℂ (Set.range fun i:U.RootS s=>ZeckR i.val); have h:E= UniComR s:= SynFD _ _
 have e:LinearIndependent ℂ (fun i:U.RootS s=> (⟨ZeckR i.val,(show ZeckR i.val∈ E from subset_span (Set.mem_range_self i))⟩:E)):= p -- tune
 haveI:FiniteDimensional ℂ E:= h.symm ▸ cardinalR s
 letI:= e.finite -- tune
 exact Fintype.ofFinite _ -- need `letI:=e.finite`
def PaddleK (U:InterR)(d:D_r): U.RootS d → Waves:= fun i=>U.WvecR d i
abbrev νChartR (i:U.RootS u): Genre× D_r := (i.val.1,i.val.2.1)
local notation "ΞUt"=>RootS U u
local notation "ΛΓ"=> PaddleK U u
abbrev EmissionR : (U.RootS u →ℂ) →ₗ[ℂ] GaugeFieldConstruction.Calibration.Shell:= ArchBuildJ (fun i:U.RootS u=>ZeckR i.val) -- tune
lemma EmStyle (y:U.RootS u→ℂ): EmissionR U u y= BlendSunR (PaddleK U u) y:=rfl
set_option synthInstance.maxHeartbeats 150000
lemma EmRank : Injective (EmissionR U u):=by
 apply LinearMap.ker_eq_bot.mp; apply LinearMap.ker_eq_bot'.mpr; intro i h; let F:=U.fre u; funext p; exact Fintype.linearIndependent_iff.mp F _ h p -- tune
lemma EmOutreach : LinearMap.range (EmissionR U u)= UniComR u:=by
 rw[←SynFD U u]; let X:=U.B u; let S:=RootS U u; let Y:=fun i:S =>ZeckR i.val
 apply le_antisymm; · intro i h; obtain ⟨v,rfl⟩:=h; exact Submodule.sum_mem _ (fun j _=> Submodule.smul_mem _ (v j) (subset_span (Set.mem_range_self j)))
 apply Submodule.span_le.mpr; rintro i ⟨t,rfl⟩; refine ⟨(Pi.single t 1:ΞUt→ℂ),?_⟩; rw [EmStyle]; unfold BlendSunR; simp; try rfl
lemma finV_R: Module.finrank ℂ (UniComR u) = Fintype.card (RootS U u):=by rw [← EmOutreach U u,LinearMap.finrank_range_of_inj (EmRank ..)]; simp
lemma value1R (i:U.RootS u): HomΓ i.val.1 i.val.2.1 (U.PaddleK u i):=(U.sat u i.property).1
lemma value2R (i:U.RootS u): ΤbandR i.val.2.1 ≤ ΤbandR u:=(U.sat u i.property).2
-- numeric rank of centered Pan ≤ free dimension!
include p pu
local notation "hΩ"=>ΤbandR u
lemma Census_ScopeR: LinearMap.range (SpineM.comp (ArtGateJ B0 R (ΤbandR u))) = UniComR u :=by
 let p':= Tsava p B0 M R (ΤbandR u) pu; let W:= LiPaJ B0 R (ΤbandR u)
 apply le_antisymm
 · intro i h; obtain ⟨v,rfl⟩:=h; apply (uniCR ..).2; change SpineM (W v)∈ Umatrix u; apply harbour; change ΓProj (metK u) (W v)= W v
   unfold W LiPaJ scalB Woof; change ΓProj (metK u) (∑ i:Fin (θ (ΤbandR u)),v i • ThreadΨ B0 (ΤbandR u) R i)= _; rw[map_sum]; simp only [map_smul]; apply sum_congr rfl; intro i _; rw[p'.saturated, if_pos (p'.ray i)] -- tune
 intro i h; obtain ⟨x,yC,rfl⟩:= portPic _ _ ((uniCR u i).1 h); obtain ⟨v,g⟩:=p'.coframe _ yC; exact ⟨v,(congrArg (fun i:Waves=>SpineM i) g).symm⟩ -- tune elaboration spends
include pu p
lemma CensusκP (T:LampHouseJ (θ:=θ) (ΤbandR u))(V: LampΤJ p B0 M x R (ΤbandR u) A T D.path) :Module.finrank ℂ (Utf0P (Panmart p B0 M x R (ΤbandR u) pu A T D V f0 le_rfl)) ≤ Fintype.card (RootS U u):=by
 refine Nat.add_le_add_iff_right.mp (le_trans (rank_ceilingXJ p B0 M x R (ΤbandR u) pu A T D V) ?_)
 let F:=ArtGateJ B0 R (ΤbandR u); let E:=SpineM.comp F
 have h: LinearMap.ker E= ResonanceRankJ B0 R (ΤbandR u):=by rw [ResonanceRankJ,Fables.sonic_K]; rfl
 rw[← finV_R U u,← Census_ScopeR p B0 M R pu u,←h,LinearMap.finrank_range_add_finrank_ker]; exact le_of_eq (Module.finrank_fin_fun ..).symm
#print axioms CensusκP
end InterR
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
