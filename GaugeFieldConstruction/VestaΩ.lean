import GaugeFieldConstruction.PaidReading
import GaugeFieldConstruction.KolM
import GaugeFieldConstruction.Virago
import GaugeFieldConstruction.Postmark
import GaugeFieldConstruction.Harries
set_option autoImplicit false
set_option maxHeartbeats 460000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open BProof.PricePort Gleam.clocks

namespace Papal
open scoped YM.CF.Mew
open Fock.Flux Girt TableF TableF.Lenten.Layout Gleam.Guide CF.XGarden CF.XGarden.MastTin ArtCart Zpress ScopeU Buffered
open FrameP
variable (s i k:ℕ)
namespace FrameP
open Window Thera
open scoped Matrix
local notation "N'"=> count Y s i
local notation "K'"=>P.K.j
local notation "Ω"=> ØFlat Y s i k
local notation "F'"=>boardC N' P.K.j (gram Y s i k).J.M
local notation "E"=>tickA N'
local notation "Π"=>mateK N'
local notation "U"=> Ωturn Y s i k
set_option maxHeartbeats 270000 in
lemma normalized_Ω (Z:Kea.Pad P.K.j (count Y s i)) : inner ℂ Π Ω≠0 ∧ ∀ T:FC (Single N'),
    U T= inner ℂ Π (acts T Ω)/ inner ℂ Π Ω:=by
 let P':= F'; let M:= (gram Y s i k).J.M; let A:= pinShift N' P.K.j M; let B:=pinBack N' P.K.j M
 have hF:IsStarProjection P':=baseP Z _; have h:IsStarProjection E:=touchP _ ▸ cutM_idp _; have hx:Sea P' Ω:= actual_f Y s i k
 have ht:Sea E Π:=tickB _
 have V:Valve P' E A B:=token_V Z (by rw [P.kJ]; decide) _
 have kζ:=shore_valve V hF h (board_rank Z _) _ _ hx ht
 have v: star (quant A)*star (quant B)=1:=by rw [←star_mul,←quant_mul,V.rest,quant_one,star_one]
 have e: acts (star (quant A)) ((inner ℂ Ω Π) • Ω)=Π:=by rw [← kζ,←act_mul,v,act_one]
 have he: inner ℂ Π Ω≠0:=by
    intro x; have hh:inner ℂ Ω Π=0:= (inner_conj_symm _ _).symm.trans (by rw [x]; simp -- tune
      ); rw [hh,zero_smul,map_zero] at e
    exact zero_ne_one' _ ((show (0:ℝ)=‖Π‖ from (show ‖(0:Wave (Single N'))‖=(0:ℝ) from norm_zero).symm.trans (congrArg Norm.norm e)).trans ht.2) -- tune
 constructor; exact he
 intro T; let B':= translateW P' A B 1 0 T
 have hU:U T=quotation Ω (quant A*T*quant B):=by
    change quotation Ω (translateW P' A B (tradew _ 1) 0 T)= _
    rw [trade_p]; unfold translateW Flux.seek Flux.wall; rw[show (quantU (1:UNI _)).val=1 from quant_one,star_one,neg_zero,knight_start,one_mul,one_mul,mul_one,mul_one] -- tune
 rw [hU]; apply (eq_div_iff he).mpr
 have hv:acts (quant B) Ω= Ω:=by nth_rw 1 [←quant_pure hF Ω hx]; rw [←act_mul,←quant_mul,V.bring,quant_pure hF Ω hx]
 unfold quotation; rw [act_mul,act_mul,hv]
 rw [mul_comm,show inner ℂ Π Ω * inner ℂ Ω _ = inner ℂ ((inner ℂ Ω Π) • Ω) (acts (quant A) (acts T Ω)) from ?_]; swap; · rw [inner_smul_left,inner_conj_symm]
 rw [←act_inner,e] -- orientation tune

set_option maxHeartbeats 210000 in
lemma θφV (Z:Kea.Pad P.K.j (count Y s i)) (j:Axis)(b:ℤ)(T:FC (Single N')):
    U (theta (carR j b N') T)=star (U T):=by
 obtain ⟨h,v⟩:=normalized_Ω Y s i k Z
 let L:= plane j b; let V:=carR j b N'; let A':= arum V false true Π; let x:= (1:Bkg (More N')); let M₁:=P.K.j
 let M:=(gram Y s i k).J.M
 have ht: sings false V F' = swapX true F':=by
    have he:=P.J.gran.trans ((Y.voyage i).ownership s).size
    have h:=funde_f L inert (pinLift j) (mirrorX j) x M₁ (by unfold M₁; rw[P.kJ]; decide) M _ (P.V.note.fields_one _ (P.U.needed.trans he)) ((guard0 P.dpos.le).shrink P.U.gem)
    have hx: stir inert L x=x:=by change pull _ _ x=x; unfold x; funext i; simp [Lattice.pull,Lattice.Step.read] -- tune
    rw [hx] at h; exact h
 let r:=tickR L inert (pinLift j) (mirrorX j) N'
 have hp: IsStarProjection F':= baseP Z _
 have he: Sea (cutM (Tset N')) Π:= touchP N' ▸ tickB N'
 have hv: Sea F' Ω:=actual_f _ _ _ _
 have ha:A' Π=Π:= arum_self V false true (Tset N') he r
 have H(c d:Wave (Single N')): inner ℂ (A' c) (A' d)=star (inner ℂ c d):=arum_globe V false true (Tset N') he r c d
 have HX(z:Wave (Single N')): A' (acts T z)=acts (theta (carR j b N') T) (A' z):= arum_act V false true z Π T -- orientation arg?
 let w:=inner ℂ Ω (A' Ω)
 have g:A' Ω=w • Ω:=by
    have c:acts (lineOp F') (A' Ω)=A' Ω:=by
       rw [←tour_line V false true F' F' hp ht]; unfold A'; rw [←arum_act,hv.1]
    exact c.symm.trans (Fock.Sea.scalar hp hv _)
 have g₁:=H Π Ω; rw [ha,g,inner_smul_right] at g₁
 have g₂:=H Π (acts T Ω); rw [ha,HX,g,map_smul,inner_smul_right] at g₂
 rw [v,v,star_div₀,←g₁,←g₂]
 have p:w≠0:=fun t=>h ((star_injective) (g₁.symm.trans (by rw [t]; simp)))
 field_simp
#print axioms θφV
end FrameP
end Papal
end LocalLimit
end Rate
end YM.CF.Py
end
