import YM.SU5.Relativistic.Meridian
import YM.SU5.Relativistic.Roscoe
import YM.SU5.Relativistic.Bailout
set_option autoImplicit false

set_option autoImplicit false
set_option maxHeartbeats 1050000
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
open Pannier
local notation "G🌸"=> SU.group
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
local notation "Dx" i:max => hat P.R.L P.x i
local notation "Dx₀" s i => count Y s i
local notation "ρ" s:max => P.V.L.path s
local notation "U" s i => room Y s i
local notation "M" s i k => gram Y s i k
open CF.Pannier.Damask
open Buffered
open Papyrus.GaugeFlux
-- new estimate for ACTUAL slate response. Orbit pays for flake affine. Reports supplied same course.
variable {h κ A:ℝ}
def BreachP (s i k:ℕ) (h d κ:ℝ) (F:Mark (count Y s i)):Prop:=
 let G:=gram Y s i k; let L:=room Y s i
 ∀ x:Orbit (count Y s i), Yep h (acts (star (F (x.1,L x))) (mateK _)) (changeM P.U (L x) G.J.M) (Real.exp (seaPrec P.K.j (count Y s i) G.J.M+d+κ*flakes G.p.threshold x.1))
-- Old `Backlog` had kite d required large pressure.
private lemma baseSlope {n:Side} (t:ℝ)(x: Pane n) : flakes t x ≤ (6:ℝ)*(RG.flags t x).card:=by
 have h: roughness t x⊆ (RG.flags t x) ×ˢ (univ: Finset PlaqAxes):=by
    intro i p; exact mem_product.mpr ⟨(flags_spec ..).2 ⟨i,WilsonStartup.anchor_visit _, (mem_filter.mp p).2⟩,mem_univ _⟩
 unfold flakes; apply (Nat.cast_le.mpr (card_le_card h)).trans; rw [card_product,card_univ,show Fintype.card PlaqAxes=6 from by decide]; push_cast; rw [mul_comm]
variable (g: FairRoute P.P P.J P.h P.N0 Chi.canonical)
include g
lemma scales_h (p:0≤h)(u:h≤ P.h)(s_ : Inflation A P)(ε K:ℝ)(w:0<ε)(hz:0≤K):∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,(Y.voyage i).kick ≤ k → s≤Y.uv k→∀ F:Mark (count Y s i),∀ d:ℝ,Envelope F → BreachP Y s i k h d K F→
 ‖Buffered.Afterglow.Journey.compass Y i k s F‖ ≤ Real.exp (d+ ε*sites (count Y s i)):=by
 let x:=hat P.R.L P.x; let q:= ε/3; have he:0<q:= div_pos w (by norm_num)
 obtain ⟨κ,hK,qT⟩:= lantern (t:=P.d) (r:=P.J.n) p (cash_v P.W.C) P.J.ht (level_p P.W.C) q he -- tune params
 let κ':=6*(κ+K)
 filter_upwards [pressed Y g s_ q he, ration Y q κ' (by unfold κ'; positivity) he, (turnover P).eventually qT,(turnover P).eventually (((dev_R P.R).1.low (k:=1) (by omega)).spine.eventually (ge_mem_nhds (show 0<q/6 by positivity)))] with s u1 u2 u3 u4
 obtain ⟨n,r⟩:= u3
 filter_upwards [(count_grows Y s).eventually_ge_atTop n] with i u5 k hi hk F d E S
 let I:= count Y s i; let N:= sites I; let V:=gram Y s i k; let L:= room Y s i
 obtain ⟨a,b,c,z,H⟩:=prices_plot Y s i k hk
 have ht: V.p.threshold=temp (x s):= (congrArg BudgetPoint.threshold a).trans (Y.meter.boot s).1
 let P_:= Papyrus.Mosaic.grain (N:=More I) G🌸 V.path V.funds V.p V.beta κ'
 obtain ⟨pI,pm⟩:=u2 i k hk
 let Z:= preGa P.V (More I) (Y.uv k-s) V.beta; change (∫ i,P_ i∂prior G🌸 (More I)) ≤ Real.exp (q*N+Z) at pm
 let z:= seaPrec P.K.j I V.J.M
 let cc:= Real.exp (q*N+z+d); let T:= fun y: Orbit I=> letterRead (F (y.1,L y)) (Graph.recX P.U V L y)
 have hm(y:Orbit I): ‖T y‖ ≤ cc*P_ y.1:=by
    let v:= r (roofage Y i s) P.h _ _ P.K.j H u u5 u4 u4 y (safety Y s i k y).1
    let pZ:= Real.exp (z+d+K*flakes V.p.threshold y.1); let U':= Graph.beam V P.U L y; let B:= Real.exp (q*N+κ*flakes (temp (x s)) y.1); let A:= F (y.1,L y); let O:= mateK I; unfold T; rw [Graph.porch,(letterRead _).map_smul_of_tower]; let J:= Graph.past V y.1; rw [norm_smul,Real.norm_of_nonneg (r:=J) (Real.exp_pos _).le]; change J*‖inner ℂ O (acts A U')‖≤ _; rw [←act_inner]; apply le_trans (mul_le_mul_of_nonneg_left (Yep.val (show Yep h _ U' (B*pZ) from v.2 _ _ _ (Real.exp_pos _).le (S y))) (Real.exp_pos _).le); unfold B pZ cc P_ Papyrus.Mosaic.grain; rw [←Real.exp_add,← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone
    rw [← ht]; unfold κ' Papyrus.Mosaic.solar; nlinarith only [mul_le_mul_of_nonneg_left (baseSlope V.p.threshold y.1) (show 0≤κ+K by positivity)] -- tune _ implicit
 have hg: Integrable T (city I):=mark_integrable (roofage Y i s).bill E ((Marks.can_read _ _ _ _ (Y.each_level i k s hi hk)).smul (Complex.exp (-V.v)))
 let U':=prior G🌸 (More I); have hx:MeasurePreserving Prod.fst (city I) U':=measurePreserving_fst; have ha:= hx.integrable_comp_of_integrable pI
 have hh: ‖num0 P.U V L F‖≤ cc*Real.exp (q*N+Z):=by
    change ‖∫ i,T i∂city I‖ ≤_; apply (norm_integral_le_integral_norm ..).trans; apply le_trans (integral_mono hg.norm (ha.const_mul cc) hm); change (∫ i:Orbit I,cc*P_ i.1∂city I)≤_; rw [integral_const_mul,CF.Window.usesPrior _ pI]; exact mul_le_mul_of_nonneg_left pm (Real.exp_pos _).le
 let H_:= Real.exp (chase Y i k s-q*N); have he:H_≤ ‖vac0 P.U V L‖:= u1 i k hi hk; rw [Buffered.Afterglow.Journey.compass, ← same_ratio,norm_div]; apply (div_le_iff₀ (Real.exp_pos _|>.trans_le he)).mpr; refine hh.trans ((mul_le_mul_of_nonneg_left he (Real.exp_pos _).le).trans' ?_)
 unfold H_ cc; rw [←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone; change _≤ _+(Z+z-q*N); unfold q; ring_nf; change ε*N*(2/3)+_+_+_≤ ε*N*(-1/3)+ε*N+z+d+Z; linarith
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.scales_h
