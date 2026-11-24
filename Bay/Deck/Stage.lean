/- Compatibility lift, near-exact baseline YM/SU5/Thin/Cascade/Stage.lean with narrower imports omitting Vellum. No proof changes. -/
import Bay.Deck.Outpost
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
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open clocks
variable {L':Side}
namespace Papal
open CF.Rapids CF.Pannier.Damask CF.Pannier.Damask.VelvetC CF.Pannier.Chancel
open Graph Pannier
local notation "Ψ"=> P.R.L

open clocks Sleigh Paddled
variable (s i k:ℕ)
local notation "M"=> count Y s i
local notation "θA"=>levelQ P.W.C
local notation "θB"=>cashU P.W.C
local notation "X"=>hat Ψ P.x
local notation "μ" x:max=> radiusB x

variable {ε a C D:ℝ}{v b:ℕ}(W:Convent P ε a C D v b)

lemma rink_free (t:0 < X s)(U:Pane (count Y s i)):0≤ rink Y s i k U:= by unfold rink stipd; have h:= (shinyH (X s) t).2.2.1; unfold clocks.grain; positivity
include W
lemma shine_land (A:ℝ)(q:0≤A): ∀ᶠ s in atTop,∀ i k,s≤Y.uv k→∀ (R:GramM (count Y s i))(E:ℝ), HillSeal Y s i k R E →∀ {n:Side}(r:Ratio n (More (count Y s i))), Portal r (X s) P.R.L →∀ (F:Pane (count Y s i)→ℝ)(t b C:ℝ), VisiblePolar Y s i k A t b r F →
 ∀ (G:Orbit (count Y s i)→ℂ), (∀ᵐ x∂(city (count Y s i)), ‖G x‖ ≤ Real.exp (t*F x.1 + C + rink Y s i k x.1/2) * ‖sealMark Y s i R x‖) →
 (∫ x, ‖G x‖ ∂city (count Y s i)) ≤ Real.exp ((b+C)+(sod Y k s i+(3*E+2*oar (X s))*sites (count Y s i))):=by
 filter_upwards [financed Y A q, seal_budget Y W] with s p h i k v' R E e; intro n r f F t b C q G g
 let N:=count Y s i; let a:= angleFin (gram Y s i k).J.M N P.K.j; let Z:= sites N; let u(U:Pane N):= winterBill Y s i k U * Real.exp (t*F U); let K:= a+(3*E+oar ((hat Ψ P.x) s))*Z; let I:= Real.exp (K+C); let f₀(x:Orbit N):=u x.1* I
 have hp: RG.Envelope u:= ((polar_env (P.V.L.mood (Y.uv k-s))).mul (expEnv q.1 t)); let U:=prior SU.group (More N); let S:=city N; have h0:Integrable u U:=hp.integrable U
 have hf:MeasurePreserving Prod.fst S U:= measurePreserving_fst ..; have hg:= (show Integrable f₀ S from (hf.integrable_comp_of_integrable h0).mul_const I)
 by_cases H:Integrable (fun x=> ‖G x‖) S; swap; · rw [integral_undef H]; exact (Real.exp_pos _).le
 refine (integral_mono_ae H hg ?_).trans ?_
 · filter_upwards [g] with x u₀; specialize h i k v' R E e x; apply u₀.trans; rw [Real.exp_add (t* F x.1 + C), mul_assoc]; exact (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans_eq (by unfold f₀ u I; rw [Real.exp_add K, Real.exp_add (t*F _)]; unfold K a Z N; ring)
 unfold f₀; rw [integral_mul_const,show (∫ x : Orbit N,u x.1 ∂city N)=∫ x,u x∂U from CF.Window.usesPrior u h0]; refine (mul_le_mul_of_nonneg_right (p i k v' r f F t b q) (Real.exp_pos _).le).trans_eq ?_;  unfold K; rw [←Real.exp_add]; unfold winterRent sod; unfold a Z N gram; dsimp only; congr 1; unfold entryFin; ring -- remove change
lemma relative_shine (p:Cistern P.J Chi.canonical P.h P.P P.N0) (A:ℝ)(q:0≤A): ∀ᶠ s in atTop,∀ i k,(Y.voyage i).kick≤k → s≤Y.uv k→∀ (R:GramM (count Y s i))(E:ℝ), HillSeal Y s i k R E →∀ {n:Side}(r:Ratio n (More (count Y s i))), Portal r (X s) P.R.L →∀ (F:Pane (count Y s i)→ℝ)(t b C:ℝ), VisiblePolar Y s i k A t b r F →
 ∀ (G:Orbit (count Y s i)→ℂ), (∀ᵐ x∂(city (count Y s i)), ‖G x‖ ≤ Real.exp (t*F x.1 + C + rink Y s i k x.1/2) * ‖sealMark Y s i R x‖) →
 (∫ x, ‖G x‖ ∂city (count Y s i)) / ‖compensated P.U (gram Y s i k) (room Y s i)‖ ≤ Real.exp ((b+C)+(3*E+3*oar (X s))*sites (count Y s i)):=by
 filter_upwards [(stage_slope P.V P.x).eventually_ge_atTop 1,benchmarks_power Y 1 one_pos p,shine_land Y W A q] with s hs u q i k j v R E e; intro n r f X' t b C q' G h
 let N:= count Y s i; let d:=sites N; let K:= sod Y k s i; let y:= oar (hat P.R.L P.x s); let U:= compensated P.U (gram Y s i k) (room Y s i); have hx:Real.exp (K-y*d) ≤ ‖U‖:=by apply le_trans _ (u i k j v); apply Real.exp_monotone; apply sub_le_sub_left; rw [one_mul]; exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hs (by norm_num)) (zero_le_one.trans (sites_pos _))
 refine (div_le_iff₀ (lt_of_lt_of_le (Real.exp_pos _) hx)).mpr ((q i k v R E e r f X' t b C q' G h).trans ((mul_le_mul_of_nonneg_left hx (Real.exp_pos _|>.le)).trans' ?_)); apply le_of_eq; rw [←Real.exp_add]; change Real.exp ((b+C)+(K+(3*E+2*y)*d))=Real.exp ((b+C)+(3*E+3*y)*d+(K-y*d)); congr 1; ring
end Papal
end LocalLimit
end Rate
end YM.CF.Py
