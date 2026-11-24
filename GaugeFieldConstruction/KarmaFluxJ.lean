import GaugeFieldConstruction.VerveΘJ
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
variable (U H:PermWallJ P) (j:Axis)(v y:FrameK (Fin (θ u)))
local notation "ηG" s0:max=> MeshΦ p B0 M x R u pu A T D V s0
local notation "ΚQ" => LaunchLJ B0 x R u L T D
-- unit in screens mesh
abbrev CandΛJ (P:Spine): ScreensJ P:= fun i U V=> P.Eucl i ((StallJ P U)+(StallJ P V)).toNNReal
local notation "γS"=>CandΛJ P
lemma UnitWallJ (e:ℕ) : CallBoxJ x U H j 1 (CandΛJ P j U H) e :=by
 let a:=StallJ P U; let b:= StallJ P H; have he:((x j-U.val:P.meshPin):ℝ)<( (x j+H.val:P.meshPin):ℝ):=lt_trans (sub_lt_self _ U.property) (lt_add_of_pos_right (x j:ℝ) H.property)
 have ht:= Habitable.one P (A:=x j-U.val) (B:=x j+H.val) j he e; rw [show (((x j+H.val):P.meshPin):ℝ)-((x j-U.val:P.meshPin):ℝ)= a+b from (by change (x j:ℝ)+b-((x j:ℝ)-a)=a+b; ring)] at ht; exact ht
variable {r t a:ℕ}
lemma ACP_S (F:StaE (E:=Fin (θ u)))(h:s≤r)(q:r≤t): PlcJ t s F (h.trans q) = (PlcJ t r F q).comp (PlcJ r s F h) ∧ AcJ F t s (h.trans q)=AcJ F r s h + (AcJ F t r q).comp (PlcJ r s F h):=by
 induction q with
 | refl=> rw[Plc_self,Ac_self]; simp -- tune
 | @step n h' ih=> rw [Ac_step _ _ _ (h.trans h'),Ac_step _ _ _ h',Plc_succ _ _ _ (h.trans h'), Plc_succ _ _ _ h',ih.1,ih.2]; simp [LinearMap.add_comp,LinearMap.comp_assoc,add_assoc]
lemma RampantJ (v:FrameK (Fin (θ u)))(h:s≤r)(e:r≤t): LaunchLJ B0 x R u L T D s t (h.trans e) v=LaunchLJ B0 x R u L T D r t e (PlcJ r s T.stairs h v) -AcJ T.stairs r s h v • 1:=by
 let Z:=T.stairs; let A':=T.sun L t; let G:=(T.rev L t).1; let F:= AcJ Z r s h; let B:= PaletteEJ B0 x R u D t; let q:=h.trans e; let χ:=PlcJ r s Z h v
 have he(y:ℕ)(d:y≤t)(w): LaunchLJ B0 x R u L T D y t d w=B (G (PlcJ t y Z d w))-(AcJ Z t y d w+A'.2 (G (PlcJ t y Z d w))) • 1:=by
    unfold LaunchLJ LampsteadJ FlatBaskJ -- order
    simp only [LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.smulRight_apply,LinearMap.add_apply]; rw [DownL] -- tune
 rw[he s q,he r e]; obtain ⟨ht,hv⟩:= ACP_S (u:=u) Z h e; rw[ht,hv]; simp only [LinearMap.comp_apply,LinearMap.add_apply]
 simp only [add_smul]; unfold Z; abel
local notation "θX"=> Φwall p B0 M x R u pu A T D V
local notation "Αχ"=> T.stairs
include s0
lemma gateLeyJ (h:s≤r): MeshΦ p B0 M x R u pu A T D V s0 v= MeshΦ p B0 M x R u pu A T D V (s0.trans h) (PlcJ r s T.stairs h v)-(AcJ T.stairs r s h v) • CandΛJ P:=by
 funext i U H; obtain ⟨f,g,z⟩:= ((eventually_ge_atTop f0).and (farWallJ U H)).exists; let P':= AcJ T.stairs r s h v; let Y:= PlcJ r s T.stairs h v; let X:= CandΛJ P i U H
 apply tendsto_nhds_unique_of_eventuallyEq (ΦGateJ p B0 M x R u pu 0 A T D V s0 U H i v) ((ΦGateJ p B0 M x R u pu 0 A T D V (s0.trans h) U H i Y).sub (tendsto_const_nhds (x:=P' • X)))
 filter_upwards [eventually_ge_atTop r,eventually_ge_atTop f] with t d e
 have p':= (SeroxJ p B0 M x R u pu 0 A T D V g s0 U H i t v (h.trans d) e z).1; apply p'.same; rw [RampantJ _ _ _ _ _ _ _ _ h d]; exact ((SeroxJ p B0 M x R u pu 0 A T D V g (s0.trans h) U H i t Y d e z).1).minus ((UnitWallJ x U H i t).scale _)
omit s0
include V
abbrev ΤTrekJ (P:Preparation)(u:BandS) (T:StaE (E:=Fin (θ u)))(s t:ℕ):Prop:= TrekJ (RankQJ P) (stepRateJ P u.val) (stepInvJ P) (chipJ P) s t T
lemma billEraJ : ΤTrekJ P.par u T.stairs f0 r :=⟨fun s u' _ => price_sail p B0 M x R u A T D.path V _ u'⟩
include s0
lemma ΞPlc (a:s≤r):let S:=PlcJ r s T.stairs a; SkillJ S (stepRateJ P.par u.val^(r-s)) ∧ Function.Bijective S∧(∀ i,LoomK i≤ stepInvJ P.par^(r-s)*LoomK (S i))∧ RankQJ P.par r≤2^(r-s)*RankQJ P.par s ∧ SkillA (AcJ T.stairs r s a) (RankQJ P.par s*(RStepJ P.par u.val)^(r-s)):= by
 intro S; exact ζAccum _ T.stairs _ _ _ _ (billEraJ p B0 M x R u A T D V) (p.price f0 le_rfl u r) s0 a le_rfl -- tune arguments.
omit s0
section comp
variable (s':f0 ≤ s)
include s'
local notation "ℬR"=> BrJ u (T.sun L s).1
lemma weighΘ (v:FrameK (Fin (θ u))): LoomK (BrJ u (T.sun L s).1 v)≤2*LoomK v:=by
 let P':=(T.sun L s).1; let v':=LoomK v; change LoomK (v+P' v)≤ _; have hx:= ((Lens_R p B0 M x R u L A T D.path V s s').1.1 v)
 apply (loomer_T ..).trans -- name tune
 linarith only [hx,noLoom v]
local notation "ωP"=>PaletteEJ B0 x R u D
lemma αArtJ : PaletteEJ B0 x R u D s v=LaunchLJ B0 x R u L T D s s le_rfl (BrJ u (T.sun L s).1 v)+(T.sun L s).2 v • 1:=by
 let F:=T.sun L s; let G:=(T.rev L s).1; let E:=BrJ u F.1; have he:E.comp G=LinearMap.id:=(Lens_R p B0 M x R u L A T D.path V s s').2.2; have h(z):E (G z)=z:= DFunLike.congr_fun he z
 have ht:Function.Bijective E:=by have hu:Function.Surjective E:=fun i=> ⟨_, h i⟩; exact ⟨LinearMap.injective_iff_surjective.mpr hu,hu⟩ -- tune
 have hz:G (E v)=v:= ht.1 (h _)
 unfold LaunchLJ LampsteadJ FlatBaskJ DownJ; simp only [climbing_refl]; change _= PaletteEJ B0 x R u D s (G (E v))-(0+F.2 (G (E v))) • 1+F.2 v • 1; rw [hz,zero_add]; abel
include pu g
lemma LawΦsJ (w:f≤ s)(q:BelowWallJ P U H f):∃ X:P.Slabs j,
 CallBoxJ x U H j (PaletteEJ B0 x R u D s v) X s ∧ ‖X-(MeshΦ p B0 M x R u pu A T D V s' (BrJ u (T.sun L s).1 v) j U H+(T.sun L s).2 v • CandΛJ P j U H)‖ ≤ ΦWallet p * FlavorRateJ P u f s s (2* LoomK v):=by
 let Y:= (BrJ u (T.sun L s).1 v); have he:=(SeroxJ p B0 M x R u pu L A T D V g s' U H j s Y le_rfl w q).1; let H':=(T.sun L s).2 v; rw [αArtJ p B0 M x R u L A T D V v s']; refine ⟨_,he.plus ((UnitWallJ x U H j _).scale H'),?_⟩
 let Z:=MeshΦ p B0 M x R u pu A T D V s' Y j U H; let b:=FareΔJ B0 x R u L T D s s Y j U H; change ‖b+H' • _-(Z+H' • _)‖≤ _; rw [add_sub_add_right_eq_sub]; have he:=ΘChargeJ p B0 M x R u pu L A T D V g s' U H j s Y le_rfl w q
 rw[dist_eq_norm] at he; refine he.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ ?_) (WalletB _).le)
 · exact weighΘ p B0 M x R u L A T D V s' v
 have hv:=p.price f g u s; exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hv.small _)) (hv.hot le_rfl w).le) (pow_nonneg (zero_le_one.trans hv.bound) _)
#print axioms gateLeyJ
#print axioms LawΦsJ
#print axioms ΞPlc
end comp
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
