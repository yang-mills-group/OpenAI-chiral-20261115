import GaugeFieldConstruction.ChalupaR
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
variable (u Ev2:D_r)
local notation "ΞUt"=>RootS U u
abbrev WeBasisR(U:InterR)(d:D_r):= FrameK (U.RootS d)
def ScanTicketR (P:Spine){I:Type}[Fintype I](F:I→ScreensJ P): FrameK I→ₗ[ℂ] ScreensJ P where
 toFun v:= ArmScreenR P F v
 map_add' i j:=by funext k a b; unfold ArmScreenR ArmBlendR; simp only[Pi.add_apply,add_smul,sum_add_distrib]
 map_smul' z i:=by funext k a b; unfold ArmScreenR ArmBlendR; simp only[Pi.smul_apply, Finset.smul_sum,smul_eq_mul]; change _=∑ j: I,z • (i j • _); simp_rw[mul_smul] -- tune implicit θ
lemma MapCelR {E:Type}[Fintype E](F:E→ScreensJ P)(j:Axis)(a b:PermWallJ P)(i:FrameK E): ScanTicketR P F i j a b= ArmBlendR P F i j a b:=rfl
-- rank convergence simultaneous. generic convert
private lemma AmberPondR {E F S:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E]
    [NormedAddCommGroup F][NormedSpace ℂ F][Nonempty S](X:ℕ→ S→E→ₗ[ℂ] F)(C:E→ℝ)
    (G:∀ (L:ℕ→ℕ)(y:ℕ→S)(T:ℕ→ E) (z:E), Tendsto L atTop atTop→ Tendsto T atTop (𝓝 z)→ Tendsto (fun i=> ‖X (L i) (y i) (T i)‖^2) atTop (𝓝 (C z))) : ∃ k>0,∀ᶠ i:ℕ in atTop,∀ t:S,∀ x:E, ‖X i t x‖≤k*‖x‖:=by
 haveI: ProperSpace E:=FiniteDimensional.proper ℂ _
 suffices H: ∃ k>0,∀ᶠ i in atTop,∀ t:S,∀ x:E, ‖x‖=1 → ‖X i t x‖≤k by
    obtain ⟨k,v,p⟩:=H; refine ⟨k,v,p.mono fun i h y v=>?_⟩; by_cases q:v=0
    · subst v; simp
    have hz:0< ‖v‖:=norm_pos_iff.mpr q; let z:ℂ:= ‖v‖; have hr:‖z‖=‖v‖:= Complex.norm_of_nonneg (norm_nonneg _) -- tune
    have ht:‖z⁻¹ • v‖=1:=by rw[norm_smul, norm_inv,hr, inv_mul_cancel₀ hz.ne']
    have h':=h y _ ht; rw[map_smul, norm_smul,norm_inv,hr, mul_comm,← div_eq_mul_inv] at h'; exact (div_le_iff₀ hz).mp h'
 by_contra! h
 have he(k:ℕ): ∃ i ≥ k,∃ y:S,∃ x:E,‖x‖=1 ∧ ((k:ℝ)+1)<‖X i y x‖:= frequently_atTop.mp (h _ (by positivity)) k -- tune bundling
 choose i d y x t r using he
 obtain ⟨a,c,R,p',F⟩:= (isCompact_sphere (0:E) 1).tendsto_subseq (fun i=> show x i∈Metric.sphere (0:E) 1 from by rw [Metric.mem_sphere,dist_zero_right]; exact t i)
 let V:= G (fun j=> i (R j)) (y∘R) (x∘R) a ((tendsto_atTop_mono d tendsto_id).comp p'.tendsto_atTop) F; have hy:Tendsto (fun j=>(R j:ℝ)+1) atTop atTop:= ((Filter.tendsto_atTop_add_const_right _ (1:ℝ) tendsto_natCast_atTop_atTop).comp p'.tendsto_atTop)
 obtain ⟨j,g,h⟩:= (((tendsto_pow_atTop (by decide: (2:ℕ)≠0)).comp hy|>.eventually_gt_atTop (C a+1)).and (V.eventually (ge_mem_nhds (show C a<C a+1 by linarith)))).exists -- wrong le left; tune
 have hx:= pow_le_pow_left₀ (show 0 ≤(R j:ℝ)+1 from by positivity) ((r (R j)).le) 2; exact (not_le.mpr g) (hx.trans h)
private lemma CrichtonR {E F S:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E]
    [NormedAddCommGroup F][NormedSpace ℂ F][Nonempty S](X:ℕ→ S→E→ₗ[ℂ] F)(C:E→ℝ)
    (p:∀ x:E,x≠0→0<C x)(G:∀ (L:ℕ→ℕ)(y:ℕ→S)(T:ℕ→ E) (z:E), Tendsto L atTop atTop→ Tendsto T atTop (𝓝 z)→ Tendsto (fun i=> ‖X (L i) (y i) (T i)‖^2) atTop (𝓝 (C z))) : ∃ k>0,∀ᶠ i:ℕ in atTop,∀ t:S,∀ x:E, k*‖x‖≤‖X i t x‖:=by
 haveI: ProperSpace E:=FiniteDimensional.proper ℂ _
 suffices H: ∃ k>0,∀ᶠ i in atTop,∀ t:S,∀ x:E, ‖x‖=1 → k≤‖X i t x‖ by
    obtain ⟨k,v,p⟩:=H; refine ⟨k,v,p.mono fun i h y v=>?_⟩; by_cases q:v=0
    · subst v; simp
    have hz:0< ‖v‖:=norm_pos_iff.mpr q; let z:ℂ:= ‖v‖; have hr:‖z‖=‖v‖:= Complex.norm_of_nonneg (norm_nonneg _) -- tune
    have ht:‖z⁻¹ • v‖=1:=by rw[norm_smul, norm_inv,hr, inv_mul_cancel₀ hz.ne']
    have h':=h y _ ht; rw[map_smul, norm_smul,norm_inv,hr, mul_comm,← div_eq_mul_inv] at h'; exact (le_div_iff₀ hz).mp h'
 by_contra! h
 have he(k:ℕ): ∃ i ≥ k,∃ y:S,∃ x:E,‖x‖=1 ∧ ‖X i y x‖< ((k:ℝ)+1)⁻¹:= frequently_atTop.mp (h _ (by positivity)) k -- tune
 choose i d y x t r using he
 obtain ⟨a,c,R,p',F⟩:= (isCompact_sphere (0:E) 1).tendsto_subseq (fun i=> show x i∈Metric.sphere (0:E) 1 from by rw [Metric.mem_sphere,dist_zero_right]; exact t i)
 have H:0<C a:= p _ (by intro w; rw[Metric.mem_sphere,w,dist_self] at c; norm_num at c)
 let V:= G (fun j=> i (R j)) (y∘R) (x∘R) a ((tendsto_atTop_mono d tendsto_id).comp p'.tendsto_atTop) F; have hy:Tendsto (fun j=>(R j:ℝ)+1) atTop atTop:= ((Filter.tendsto_atTop_add_const_right _ (1:ℝ) tendsto_natCast_atTop_atTop).comp p'.tendsto_atTop)
 obtain ⟨j,g,h⟩:= ((((tendsto_inv_atTop_zero.comp hy).pow 2).eventually (ge_mem_nhds (show (0:ℝ)^2<C a/2 by rw [zero_pow (by decide : (2:ℕ)≠0)]; linarith))).and (V.eventually (Ioi_mem_nhds (half_lt_self H)))).exists
 have hx:= pow_le_pow_left₀ (norm_nonneg _) ((r (R j)).le) 2; exact (not_le.mpr h) (hx.trans g)
variable {S:Type}[Nonempty S](ιs:ℕ→ S → P.VMark)
variable (W:ℕ→ S→ U.RootS u → ScreensJ P)
variable (heat:26 ≤ m)
variable (πW:∀ i:U.RootS u,∃ (r:ℝ)(u':BandS),0≤r∧aptC i.val.2.1 ≤3+u'.val∧∀ᶠ k in atTop,∀ y:S,∃ g:f0 ≤ k,∃ R T t, TakesR p B0 M (ιs k y) pu A (W k y i) r (U.PaddleK u i) i.val.2.1 u' i.val.1 D g m R T t)
-- using shelf NormR. Uniform valuation at every root.
include pu D Q t u' H πW heat
abbrev GapHeightR (P: Spine)(j:ℕ)(X:ScreensJ P):= DotM_R P 3 (X 3 (RootApR P j) (RootApR P j))
private def GapTaxR (P:Spine)(j:ℕ):ScreensJ P→ₗ[ℂ] P.Hil 3 where
 toFun x:= GapHeightR P j x
 map_add' x y:=rfl
 map_smul' a b:=rfl
lemma MetricR_Lim : let G(w:ΞUt→ℂ):= EmissionR U u w -- tune local ΞUt from earlier not header
 ∀ (L:ℕ→ℕ)(y:ℕ→S)(T:ℕ→(RootS U u→ℂ))(z:RootS U u→ℂ), Tendsto L atTop atTop → Tendsto T atTop (𝓝 z) → Tendsto (fun i=> ‖GapHeightR P (L i) (ScanTicketR P (W (L i) (y i)) (T i))‖^2) atTop (𝓝 (Wick.stare (couples (Mirror.night (G z)) (G z))).re):=by
 intro G L y T' z s h
 let R:=RootApR P ∘ L
 refine ΓAuroraR p B0 M pu A D Q t u' H m s R (fun i=>ιs (L i) (y i)) (Filter.Tendsto.comp (RootAling P) s) (fun i:U.RootS u=>i.val.2.1) (fun i:U.RootS u=>i.val.1) (PaddleK U u) (fun j k=>W (L k) (y k) j) heat (fun i=>U.value1R u i) ?_ T' z h R -- tune comp
 intro i; obtain ⟨r,u,e,k,v⟩:=πW i; exact ⟨r,u,e,k,(s.eventually v).mono fun i p=>p (y i)⟩
lemma MintPeak : ∃ (c t:ℝ),0<c∧0<t∧∀ᶠ f in atTop,∀ (i:S)(z: U.RootS u→ℂ),c*‖z‖ ≤ ‖GapHeightR P f (ScanTicketR P (W f i) z)‖ ∧ ‖GapHeightR P f (ScanTicketR P (W f i) z)‖ ≤ t*‖z‖:=by
 let X(k:ℕ)(i:S):= (GapTaxR P k).comp (ScanTicketR P (W k i)); let C (v:U.RootS u→ℂ):= (Wick.stare (couples (Mirror.night (EmissionR U u v)) (EmissionR U u v))).re; have he(v:U.RootS u→ℂ)(p:v≠0):0<C v:=by
    have hz: EmissionR U u v≠0:=fun e=> p ((EmRank U u) (e.trans (map_zero _).symm))
    obtain ⟨a,k⟩:= (show EmissionR U u v∈ LinearMap.range (shells u) from (show _∈UniComR u from (EmOutreach ..) ▸ (show EmissionR U u v∈LinearMap.range _ from LinearMap.mem_range_self _ _)).1)
    unfold C; rw [←k, Mirror.price]; exact Invoice.mirror_positive _ a (by rintro s; rw [s,map_zero] at k; exact hz k.symm)
 let h:=MetricR_Lim p B0 M pu A D Q t u' H m U u ιs W heat πW; obtain ⟨c,v,t⟩:= CrichtonR X C he h; obtain ⟨C,u,z⟩:= AmberPondR X C h
 exact ⟨c,C,v,u,(t.and z).mono fun i h s x=>⟨h.1 s x,h.2 s x⟩⟩
#print axioms MintPeak
end InterR
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
