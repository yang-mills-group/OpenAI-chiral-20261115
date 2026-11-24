import Verses.Culinary
import Verses.Shade
import Verses.Sensor
import YM.CF.Muse.Sail
import Verses.Staging
import Verses.Sensor
import Verses.Billing
import Verses.Fusing
import LusterS.Husk
import YM.SU5.Velvet.Hemline
import Refrain.Seismic
import YM.SU5.Velvet.Viper
import YM.SU5.Velvet.Fronds
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask
set_option maxHeartbeats 550000
lemma heavy_integrable (s i k:ℕ)(t:s≤Y.uv k) : Integrable (fun x:Pane (count Y s i)=>Real.exp (((-((gram Y s i k).path.inChannels (gram Y s i k).funds (gram Y s i k).p (gram Y s i k).beta x))+
 greyFee Y 1 s i k x ))) (prior SU.group (More (count Y s i))):=by
 let A:=gram Y s i k; let x:=ℶ s
 have hp:=prices_plot Y s i k t
 change Integrable (regenerate A.path _ _ _ (flagCup A.p _ _) (1*((walls pio x:ℕ):ℝ)^4) (sax x)) _
 have he:A.path=P.V.L.path (Y.uv k-s):=hp.2.1
 have hx:A.funds=P.K.top.clip:=hp.2.2.1
 rw [he,hx]; exact (env_reg (P.V.L.mood _)).integrable _
-- E weave Mark with perturbed Gram, no integrability hypotheses required beyond actual. abs conditional. Use on numerator integral directly, but hUp asks no proof integrability, `∫ ‖ ‖` maybe not genuine L1! can request in Petals where needed. In Arc_r likely measurable. Keep L∞ as regulation. 
abbrev rental (s i k:ℕ)(G:GramM (count Y s i))(F:Mark (count Y s i))(x: Orbit (count Y s i)) : ℂ := letterRead (F (x.1,Papal.room Y s i x)) (Graph.recX P.U G (room Y s i) x)
def WeightedMark (s i k:ℕ)(G:GramM (count Y s i))(F:Mark (count Y s i))(m:ℝ):ℝ:=let A:=gram Y s i k; let t:= m; let T:=count Y s i
        (∫ x:Orbit T, Real.exp (t*flakes A.p.threshold x.1)*‖rental Y s i k G F x‖∂city T)/ ‖vac0 P.U A (room Y s i)‖
lemma hull_pressure (s i k:ℕ)(h:s≤Y.uv k)(q n:ℕ)(b a C δ:ℝ)(g:Gust Y s q b a C δ n)(u:n ≤ i)(w:pressureLean Y 1 s i k)(hm:VLine Y s i k ( (ℶ s) ^ (-(8:ℝ)⁻¹))) {α μ γ D:ℝ}(R:GramM (count Y s i))(G:Arc_r R P.h α μ γ)(e:ProperT (gram Y s i k) R)(F:Mark (count Y s i))(hP:0≤D)(p:∀ y:Orbit (count Y s i),let S:= spar 4 R.J.M (1:Pane (count Y s i));∀ p:IsStarProjection S, upPrice _ S p q (F (y.1,room Y s i y)) D)(he:1≤ ℶ s):
    let B:=gram Y s i k; WeightedMark Y s i k R F (flagCup B.p P.K.top.clip B.beta/2) ≤ D*Real.exp ((α+μ+γ+6*parcelF (ℶ s))* sites (count Y s i)):=by
 intro B; let N:= count Y s i; let v:=flakes B.p.threshold (N:=N); let U:=room Y s i; let Q:= sites N; let x:= ℶ s; let d:=parcelF x; let Δ:=flagCup B.p P.K.top.clip B.beta/2; let M:=angleFin B.J.M N P.K.j; let l:= α+μ+γ
 let Z(V:Pane N):=Real.exp (-B.path.inChannels B.funds B.p B.beta V+greyFee Y 1 s i k V); let L:=D*Real.exp (M+(l+4*d)*Q); have hi:Integrable Z (prior SU.group (More N)):=heavy_integrable Y s i k h; have hu: MeasurePreserving Prod.fst (city N) (prior SU.group (More N)):=measurePreserving_fst
 unfold WeightedMark; dsimp only; let W:=vac0 P.U B U
 let J:=Fineness.gaugedBase P.L B.beta (More N) (P.V.L.H (Y.uv k-s))
 let D':=Real.exp ((J+M)-d*Q); have hB:D'≤ ‖W‖:=by
    apply le_trans _ hm
    unfold D'; change Real.exp _ ≤ Real.exp (J+M - _*_); apply Real.exp_monotone; apply sub_le_sub_left; gcongr; exact Real.rpow_le_rpow_of_exponent_le he (by norm_num [claimV,ratioV,tauA]) -- direction d=d^-ε > x^-1/8. 
 have hL:0 ≤ L:=mul_nonneg hP (Real.exp_pos _).le
 let S(y:Orbit N):= Z y.1 * L
 have hF :Integrable S (city N):=(hu.integrable_comp_of_integrable hi).mul_const _
 change (∫ y:Orbit N,Real.exp (Δ*v y.1)*‖rental Y s i k R F y‖∂city N)/‖W‖≤_
 apply (div_le_iff₀ ((Real.exp_pos _).trans_le hB)).mpr
 apply le_trans (b:= ∫ y,S y∂city N)
 · apply integral_mono_of_nonneg (Eventually.of_forall (fun y=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))) hF; refine Eventually.of_forall fun y=> ?_; let A:= R.path.inChannels R.funds R.p R.beta y.1
   have hp:= g.bill h u α μ γ R G e F D y (p y); let e':= Δ*v y.1
   unfold rental; dsimp only; rw [Graph.porch (P:=P.U) (V:=R) (S:=room Y s i) y,(letterRead _).map_smul_of_tower,norm_smul,Real.norm_of_nonneg (r:=Graph.past R _) (Real.exp_pos _|>.le), ←mul_assoc]
   apply (mul_le_mul_of_nonneg_left hp (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le).trans
   change Real.exp e'*Real.exp (-A)*(D*Real.exp ((M+(l+4*d)*Q)+greyFee Y 1 s i k y.1-e')) ≤ S y
   obtain ⟨t1,t2,t3,t4,h⟩:= e; have ht:A=B.path.inChannels B.funds B.p B.beta y.1:=by unfold A B; rw [←t1,←t2,←t3,←t4]
   apply le_of_eq; unfold S Z L; rw [ht, show ((M+(l+4*d)*Q)+_)-e'= M+(l+4*d)*Q+(greyFee Y 1 s i k y.1-e') by ring,Real.exp_add (x:=(-(B.path.inChannels ..))), Real.exp_add (M+(l+4*d)*Q),Real.exp_sub]; field_simp
 unfold S; rw [integral_mul_const,CF.Window.usesPrior _ hi]; refine (mul_le_mul_of_nonneg_right w hL).trans ((mul_le_mul_of_nonneg_left hB (mul_nonneg hP (Real.exp_pos _).le)).trans' ?_)
 change Real.exp (J+x^(-yieldA)*Q)*(D * Real.exp (M+(l+4*d)*Q))≤ (D*Real.exp ((l+6*d)*Q))*D'
 rw [mul_left_comm,mul_assoc D]; apply mul_le_mul_of_nonneg_left _ hP; unfold D'; rw [← Real.exp_add,←Real.exp_add]; apply Real.exp_monotone
 have he': x^(-yieldA) ≤ d:= Real.rpow_le_rpow_of_exponent_le he (by norm_num [yieldA,claimV,ratioV,tauA]); nlinarith only [mul_le_mul_of_nonneg_right he' (show 0≤ Q from (zero_le_one.trans (sites_pos _)))]

end Papal
end LocalLimit
end Rate
end YM.CF.Py
