import GaugeFieldConstruction.AmberGaugeVU
set_option autoImplicit false
set_option maxHeartbeats 280000
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden.MastTin.ArtCart
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
open Buffered Lifted Girt Skye Window Vale
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {G H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick.Yacht.Vesper Violets
-- Epoch hull as quadratures. standard cost coupons
open scoped Kronecker
open YM.GaugeFieldConstruction
variable (x:Cover)(w:300<n.val)
namespace BluffV
open Cauchy
-- plen capital: anchor unweighted.White v
local instance QuartzGammaUniqueVU38Cerise : AddCommGroup ↥P14:= PackP.G.toAddCommGroup
local instance QuartzGammaUniqueVU39Cerise : AddCommGroup ↥P25:= PackM.G.toAddCommGroup
local instance QuartzGammaUniqueVU40Cerise : Module ℂ ↥P14:= PackP.S.toModule
local instance QuartzGammaUniqueVU41Cerise : Module ℂ ↥P25:= PackM.S.toModule
local instance QuartzGammaUniqueVU42Cerise : AddCommGroup ↥G15:= PackS.G.toAddCommGroup
local instance QuartzGammaUniqueVU43Cerise : Module ℂ ↥G15:= PackS.S.toModule
local instance QuartzGammaUniqueVU44Cerise : AddCommGroup ↥G3:= PackG.G.toAddCommGroup
local instance QuartzGammaUniqueVU45Cerise : Module ℂ ↥G3:= PackG.S.toModule
open Phys Row TableF.Lenten.Loden
open Matter (FlavorIndex)
open Raw Calibration
local instance QuartzGammaUniqueVU49Cerise : AddCommGroup Gκ:= PackH.G.toAddCommGroup
local instance QuartzGammaUniqueVU50Cerise : Module ℂ Gκ:= PackH.S.toModule
namespace Fables
open Conj
variable (R:Signed)(b:Bool)(d:Floor)

-- PROPER FRAME average to seek the clover. Off-shell generator steering exact at every Height
open Calibration.Floor U1 Row.Record LabelAction
noncomputable abbrev CastJetVU(a:Wed): G4:= ⟨(a,a),le_rfl⟩
noncomputable def EphJetVU(a:Wed): UG four:= ⟨evalTg (CastJetVU a),by unfold SG gFour Record.space; rw [Fintype.range_linearCombination]; exact Submodule.subset_span ⟨_,rfl⟩⟩ -- tune
local instance gA (i:Floor):AddCommGroup (UG i):=Submodule.addCommGroup _
local instance fA (i: Floor): AddCommGroup (UF i):=Submodule.addCommGroup _
local instance xA(i:Floor):AddCommGroup (UX i):=Submodule.addCommGroup _
local instance uA(i:Floor): AddCommGroup (UV i):=inferInstanceAs (AddCommGroup (Prod _ _))
local instance uM(i:Floor): Module ℂ (UV i):= inferInstanceAs (Module ℂ (Prod _ _))
noncomputable abbrev BathJetVU(a:Wed):UV four:=(0,EphJetVU a,0,0)
lemma φPassTurnVU (R:Signed)(a:Wed): spinFrame four R (BathJetVU a)=BathJetVU (wedAct.move R a):=by
 have ht: g4Act.move R (CastJetVU a)= CastJetVU (wedAct.move R a):=by apply Subtype.ext; rw [g4Act,Labels.sym_mv]; simp [ordered] -- tune
 have hp:=Carries.move_basis g4Act evalTg readingTg (gauge four).toCarries (CastJetVU a) (EphJetVU a) rfl R; rw [ht, show g4Act.cost R (CastJetVU a)=false from Bool.xor_self _,pay_false] at hp -- tune
 refine Prod.ext rfl (Prod.ext (Subtype.ext hp) (Prod.ext ?_ ?_)); · ext1 i; exact map_zero ((Calibration.matter four).moves R)
 ext1 i; exact map_zero ((mixed four).moves R)
abbrev Wg01VU:= Wed.mk 0 1 (by decide)
abbrev Wg23VU:= Wed.mk 2 3 (by decide)
abbrev Wg02VU:= Wed.mk 0 2 (by decide)
abbrev Wg13VU:= Wed.mk 1 3 (by decide)
abbrev ΩPureVU: UV four:= BathJetVU Wg01VU+BathJetVU Wg23VU-(BathJetVU Wg02VU+BathJetVU Wg13VU)
lemma vFieldFeatVU: FeatGaugeVU (fun b=>spinFrame four b.val) ΩPureVU =64 • ΩPureVU:=by
 apply SightWordVU
 · intro B v; simp only [List.mem_cons,List.not_mem_nil, or_false] at v
   rcases v with v|v|v|v|v
   · subst B; unfold ΩPureVU; rw [map_sub,map_add, map_add,φPassTurnVU,φPassTurnVU,φPassTurnVU,φPassTurnVU, show wedAct.move Hm1VU.val Wg01VU=Wg23VU by decide,show wedAct.move Hm1VU.val Wg23VU=Wg01VU by decide,show wedAct.move Hm1VU.val Wg02VU=Wg02VU by decide,show wedAct.move Hm1VU.val Wg13VU=Wg13VU by decide]; abel
   · subst B; unfold ΩPureVU; rw [map_sub,map_add, map_add,φPassTurnVU,φPassTurnVU,φPassTurnVU,φPassTurnVU, show wedAct.move Hm0VU.val Wg01VU=Wg01VU by decide,show wedAct.move Hm0VU.val Wg23VU=Wg23VU by decide,show wedAct.move Hm0VU.val Wg02VU=Wg13VU by decide,show wedAct.move Hm0VU.val Wg13VU=Wg02VU by decide]; abel
   · subst B; unfold ΩPureVU; rw [map_sub,map_add, map_add,φPassTurnVU,φPassTurnVU,φPassTurnVU,φPassTurnVU, show wedAct.move Hf0VU.val Wg01VU=Wg01VU by decide,show wedAct.move Hf0VU.val Wg23VU=Wg23VU by decide,show wedAct.move Hf0VU.val Wg02VU=Wg02VU by decide,show wedAct.move Hf0VU.val Wg13VU=Wg13VU by decide]
   · subst B; unfold ΩPureVU; rw [map_sub,map_add, map_add,φPassTurnVU,φPassTurnVU,φPassTurnVU,φPassTurnVU, show wedAct.move Hf1VU.val Wg01VU=Wg01VU by decide,show wedAct.move Hf1VU.val Wg23VU=Wg23VU by decide,show wedAct.move Hf1VU.val Wg02VU=Wg02VU by decide,show wedAct.move Hf1VU.val Wg13VU=Wg13VU by decide]
   · subst B; unfold ΩPureVU; rw [map_sub,map_add, map_add,φPassTurnVU,φPassTurnVU,φPassTurnVU,φPassTurnVU, show wedAct.move Hf2VU.val Wg01VU=Wg01VU by decide,show wedAct.move Hf2VU.val Wg23VU=Wg23VU by decide,show wedAct.move Hf2VU.val Wg02VU=Wg02VU by decide,show wedAct.move Hf2VU.val Wg13VU=Wg13VU by decide]
 unfold ΩPureVU; rw [map_sub,map_add, map_add,φPassTurnVU,φPassTurnVU,φPassTurnVU,φPassTurnVU, show wedAct.move HlVU.val Wg01VU=Wg02VU by decide,show wedAct.move HlVU.val Wg23VU=Wg13VU by decide,show wedAct.move HlVU.val Wg02VU=Wg01VU by decide,show wedAct.move HlVU.val Wg13VU=Wg23VU by decide]; abel
#print axioms vFieldFeatVU
-- picks the F01 B(2) coordinate
private abbrev M01κ : GIndex:= (true,⟨(2,0),fun _=>rfl⟩)
private abbrev M_epoch (k:S3)(b:Bool):GIndex:= (b,⟨(k,0),fun _=>rfl⟩)

lemma ΩFloatsVU:ΩPureVU≠0:=by
 have hA:Row.arc Wg01VU=ket M01κ:=by
    change Cauchy.F (Fin.castSucc (0:S3)) ((1:S3).castSucc)=ket _; unfold Cauchy.F; rw[Fin.lastCases_castSucc,Fin.lastCases_castSucc,if_neg (by decide), if_pos (by decide)]; exact picked_G M01κ -- check G
 have hB:Row.arc Wg23VU= -ket (M_epoch 2 false):=by
    change Cauchy.F ((2:S3).castSucc) (Fin.last 3)= -ket _; unfold Cauchy.F; rw [Fin.lastCases_castSucc,Fin.lastCases_last]; exact congrArg Neg.neg (picked_G (M_epoch 2 false)) -- tune inferred
 have hC:Row.arc Wg02VU= -ket (M_epoch 1 true):=by
    change Cauchy.F ((0:S3).castSucc) ((2:S3).castSucc) =_; unfold Cauchy.F; rw[Fin.lastCases_castSucc,Fin.lastCases_castSucc,if_neg (by decide),if_neg (by decide)]; exact congrArg Neg.neg (picked_G (M_epoch 1 true))
 have hD:Row.arc Wg13VU= -ket (M_epoch 1 false):=by
    change Cauchy.F ((1:S3).castSucc) (Fin.last 3) =_; unfold Cauchy.F; rw[Fin.lastCases_castSucc,Fin.lastCases_last]; exact congrArg Neg.neg (picked_G (M_epoch 1 false))
 intro h; have g:=congrArg (fun y:UV four=> y.2.1.val) h
 let K:=fun a:Wed=> evalTg (CastJetVU a); change K Wg01VU+ K Wg23VU-(K Wg02VU+K Wg13VU)=0 at g; have hp(a):K a=Bose (Row.arc a) (Row.arc a):= rfl
 rw [hp,hp,hp,hp,hA,hB,hC,hD] at g; unfold Bose at g; simp only [map_neg,LinearMap.neg_apply,neg_neg,times',on_ket] at g
 have z:=DFunLike.congr_fun g (M01κ,M01κ); norm_num [ket, Finsupp.single_apply, show (M_epoch 2 false) ≠ M01κ by decide, show (M_epoch 1 true) ≠ M01κ by decide, show (M_epoch 1 false) ≠ M01κ by decide] at z
#print axioms ΩFloatsVU
end Fables
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
