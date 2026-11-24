import GaugeFieldConstruction.AuldΘJ
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
variable (σ τ:PermWallJ P) (i:Axis)(v:FrameK (Fin (θ u)))
abbrev Sehya (P:Spine):PermWallJ P:=⟨P.stampPin 0 (WorkWJ P 0),PledgeJ P 0⟩
variable {cost:ℕ→P.Test→ℂ}  -- continuity & singleton
section
variable (R':∀ i:Axis, Porch P cost i)
abbrev EarthLawJ (P:Spine)(cost: ℕ→P.Test→ℂ):Prop:=forall (F:P.Test)(s t:ℕ),s ≤ t→cost t (P.conveying s (t-s) F)=cost s F
-- immediate E & χ instantiation
lemma MeanBylawsJ (P:Spine) : EarthLawJ P P.publicBill :=by
 intro F s t p; obtain ⟨t,rfl⟩:=Nat.exists_eq_add_of_le p; rw[Nat.add_sub_cancel_left]
 induction t with
 | zero=> rfl
 | succ n ih=>
    obtain ⟨S,h⟩:= (P.conveying s n F).property.paid; exact (P.history.circuit.supports (s+n) h).2.trans (ih (by omega)) -- tune induction order ℕ add.
lemma χBylawsJ (P:Spine)(x:P.Spectrum0 3): EarthLawJ P (P.soloBill x):=by
 intro F s t p; obtain ⟨t,rfl⟩:=Nat.exists_eq_add_of_le p; rw[Nat.add_sub_cancel_left]; change P.chi 3 x (P.reading 3 (s+t) (P.conveying s t F))= _; rw[P.carryReads]; rfl -- tune
variable (Law:EarthLawJ P cost)
abbrev VirtueJ (i:Axis)(A:P.Slabs i):ℂ:= (inner ℂ (R' i).Ω ((R' i).ρ A (R' i).Ω))
lemma livingJ(j:Axis) :Continuous (VirtueJ R' j):=by
 let Z:=R' j; refine continuous_const.inner ?_; exact (((show LipschitzWith 1 Z.ρ from LipschitzWith.of_dist_le_mul fun i j=> by rw[dist_eq_norm,dist_eq_norm,NNReal.coe_one,one_mul,←map_sub]; exact Z.watch_le _).continuous).clm_apply (continuous_const (y:=Z.Ω))) -- tune
abbrev HeapΨ (S:ScreensJ P): ℂ:= VirtueJ R' 3 (S 3 (Sehya P) (Sehya P))
include Law
lemma CallΨJ {t:ℕ}{i:Axis}{A B:P.meshPin}{F:P.Test}{X:P.Slabs i} (p:P.Habitable i F t A B X): VirtueJ R' i X= cost t F:=by
 obtain ⟨v,m,b,w,g,h,u,rfl⟩:=p; exact ((R' i).expense u).trans (((R' i).axSym v (-b) _).trans (Law F _ _ m))
include s0
lemma ΨglyphJ : Tendsto (fun r:ℕ=> if h:s≤r then cost r (LaunchLJ B0 x R u L T D s r h v) else 0) atTop (𝓝 (VirtueJ R' i (MeshΦ p B0 M x R u pu A T D V s0 v i σ τ))):=by
 obtain ⟨f,h,v'⟩:=((farWallJ σ τ).and (eventually_ge_atTop s)).exists; let G:=ΦGateJ p B0 M x R u pu L A T D V s0 σ τ i v; apply ((livingJ R' i).continuousAt.tendsto.comp G).congr'; filter_upwards[eventually_ge_atTop f] with r e
 let h':=v'.trans e; rw[dif_pos h']; exact CallΨJ R' Law (SeroxJ p B0 M x R u pu L A T D V (s0.trans v') s0 σ τ i r v h' e h).1
lemma ΦSkyJ : VirtueJ R' i (MeshΦ p B0 M x R u pu A T D V s0 v i σ τ)= HeapΨ R' (MeshΦ p B0 M x R u pu A T D V s0 v):=tendsto_nhds_unique (ΨglyphJ p B0 M x R u pu 0 A T D V s0 σ τ i v R' Law) (ΨglyphJ p B0 M x R u pu 0 A T D V s0 _ _ _ _ R' Law) -- arguments tune
omit s0 Law
lemma Virtue1J : VirtueJ R' i (CandΛJ P i σ τ)=1:=by unfold VirtueJ CandΛJ; rw [(R' i).still]; rw [inner_self_eq_norm_sq_to_K,(R' i).normΩ]; simp
-- linear and estimate.SLabs.r.
lemma Vbudget (X:P.Slabs i): ‖VirtueJ R' i X‖≤ ‖X‖:=by
 let Z:=R' i; have ht:= norm_inner_le_norm (𝕜:=ℂ) Z.Ω (Z.ρ X Z.Ω); rw [Z.normΩ,one_mul] at ht; have hz:=(Z.ρ X).le_opNorm Z.Ω; rw[Z.normΩ,mul_one] at hz; exact ht.trans (hz.trans (Z.watch_le X)) -- name tune
lemma Vfoot (z:ℂ)(X Y:P.Slabs i) : VirtueJ R' i (z • X+Y)=z*VirtueJ R' i X+VirtueJ R' i Y:=by unfold VirtueJ; rw[map_add,map_smul]; rw [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,inner_add_right,inner_smul_right] -- tune
include Law
include s0
lemma PanΨ (S:ScreensJ P)(h:S∈ Panmart p B0 M x R u pu A T D V s s0): VirtueJ R' i (S i σ τ)=HeapΨ R' S:=by
 obtain ⟨⟨v,z⟩,rfl⟩:=h; rw[kickΔ,add_comm]; unfold HeapΨ; simp only [Pi.add_apply,Pi.smul_apply,Vfoot i R',Vfoot (i:=3) R',Virtue1J]; rw [ΦSkyJ p B0 M x R u pu A T D V s0 σ τ i v R' Law] -- names tune
omit Law s0
abbrev Heapψ (P:Spine) (S:ScreensJ P):ℂ:= HeapΨ (P.publicH) S
lemma SpikeJ (P:Spine): Heapψ P (CandΛJ P)=1:=Virtue1J (Sehya P) _ _ _
lemma Hpv (z:ℂ)(X Y:ScreensJ P): Heapψ P (z • X+Y)=z* Heapψ P X+ Heapψ P Y:= Vfoot 3 P.publicH z _ _
lemma hAσ (X Y:ScreensJ P): Heapψ P (X+Y)= Heapψ P X+ Heapψ P Y:=by
 have ht:=Hpv 1 X Y; rw [show (1:ℂ) • X=X from (by funext i σ τ; simp only [Pi.smul_apply]; rw [one_smul]),one_mul] at ht; exact ht
lemma hΛz (P:Spine) : Heapψ P 0=0:=by unfold Heapψ HeapΨ VirtueJ; change inner ℂ _ ((P.publicH 3).ρ 0 _)=_; rw[map_zero]; simp
lemma hχν (z:ℂ)(X: ScreensJ P): Heapψ P (z • X)= z*Heapψ P X:= by simpa only [add_zero,hΛz] using Hpv z X (0:ScreensJ P)
def Focusβ (P:Spine) : ScreensJ P →ₗ[ℂ] ℂ where
 toFun:= Heapψ P
 map_add':= hAσ
 map_smul' z v:=hχν z v
abbrev Utf0P (X:Submodule ℂ (ScreensJ P)) := X ⊓ LinearMap.ker (Focusβ P)
def RenewΛJ (P:Spine): ScreensJ P→ₗ[ℂ] ScreensJ P where
 toFun z:= z- (Heapψ P z) • CandΛJ P
 map_add' z v:= by
    change z+v- (Heapψ P (z+v)) • _=_; rw [hAσ]; funext i j x; simp only [Pi.sub_apply,Pi.smul_apply,Pi.add_apply]; rw[add_smul]; abel
 map_smul' z v:= by
    change z • v- Heapψ P (z • v) • _=z • (v-Heapψ P v • _); rw[hχν]; funext i a b; simp only [Pi.sub_apply,Pi.smul_apply]; rw[smul_sub, mul_smul]
abbrev SnpΦ (P:Spine)(A:ScreensJ P):= RenewΛJ P A
lemma PoseNullJ (P:Spine)(X:ScreensJ P): Heapψ P (SnpΦ P X)=0:=by
 let W:=Focusβ P; change W (X- Heapψ P X • _)=_; rw[W.map_sub,W.map_smul]; change Heapψ P X- _* Heapψ P (CandΛJ P)=_; rw [SpikeJ,mul_one,sub_self]
lemma pose_skipJ (P:Spine): SnpΦ P (CandΛJ P)=0:=by unfold SnpΦ; change CandΛJ P-Heapψ P (CandΛJ P) • CandΛJ P=_; rw[SpikeJ]; funext i a b; simp only [Pi.smul_apply,Pi.sub_apply]; rw[one_smul,sub_self]; rfl
include V s0 p pu
abbrev ΦCentered (s0:f0≤ s):FrameK (Fin (θ u))→ₗ[ℂ] ScreensJ P := (RenewΛJ P).comp (Φwall p B0 M x R u pu A T D V s0)
lemma PanZeroJ : LinearMap.range (ΦCentered p B0 M x R u pu A T D V s0)= Utf0P (Panmart p B0 M x R u pu A T D V s s0):=by
 let W:=CandΛJ P; apply le_antisymm
 · intro j ⟨a,p'⟩; subst j; let J':=MeshΦ p B0 M x R u pu A T D V s0 a; unfold Utf0P; refine ⟨⟨(a,-Heapψ P J'),?_⟩,PoseNullJ P J'⟩; change J' + (- Heapψ P J') • W=J'- _ • W; funext i u v; simp only [Pi.add_apply,Pi.smul_apply,Pi.sub_apply]; rw[neg_smul,sub_eq_add_neg]; rfl
 intro F p'; obtain ⟨⟨⟨w,v⟩,rfl⟩,y⟩:=p'; rw [kickΔ] at y ⊢; let J:=MeshΦ p B0 M x R u pu A T D V s0 w; let X:= RenewΛJ P; have h: SnpΦ P (J+ v • W)=J+v • W:=by change (J+ v • W)- _= _; rw [show Heapψ P (J+ v • W)= 0 from y]; funext i a b; simp only [Pi.smul_apply,Pi.sub_apply]; rw[zero_smul,sub_zero]
 refine ⟨w,?_⟩; rw[show ΦCentered p B0 M x R u pu A T D V s0 w= X (J+ v • W) from ?_]; exact h
 rw[X.map_add,X.map_smul, show X W=0 from pose_skipJ P]; change X J=X J+ _; funext i a b; simp only [Pi.add_apply,Pi.smul_apply,Pi.zero_apply]; rw[smul_zero,add_zero]
#print axioms PanZeroJ
#print axioms PanΨ
#print axioms MeanBylawsJ
end
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
