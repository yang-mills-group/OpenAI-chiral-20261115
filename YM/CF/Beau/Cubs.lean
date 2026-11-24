import YM.CF.Mica.Glint
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Beau
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
open Ione Larch
open Taxi Geo RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
variable {X':Scree.Hub n}{F:Config E' (More n) → ℝ}
lemma mold_l (x:ℝ) : pot (n:=n) ∅ (moldV n x)=Complex.ofRealCLM x:=by rw [mon_v]; exact hullB _ -- tune
lemma spark_H(p: P.Regular X'.val.2 F)(hp:F 1=0)(t:∀ x y:DN,IsAffineDirection X'.val.1 x→IsAffineDirection X'.val.1 y→ logHessian F x y=0): spark X'.val.1 (moldV n∘ F):=by
 constructor; · change pot ∅ (moldV n (F 1))=0; rw [hp,map_zero,map_zero]
 intro x y hx hy; rw [show pot ∅ ∘ (moldV n ∘ F) ∘ increment 1=Complex.ofRealCLM ∘ (F ∘ increment 1) from funext fun i=>mold_l _]
 have hk:= p.smooth 1 (flat_ok P X'.val.2); have hp: ContDiffAt ℝ (↑P.order:WithTop ℕ∞) (F ∘ increment 1) 0:= hk
 rw [Complex.ofRealCLM.iteratedFDeriv_comp_left (i:=2) hp (by exact Nat.cast_le.mpr ((show (2:ℕ)≤6 from by norm_num).trans P.order_ge))]; change Complex.ofRealCLM (logHessian F x y)=_; rw [t x y hx hy,map_zero]
-- generic scalar blindness
variable (H:ℕ→ Scree.Hub n)(Q:ℕ→InkD n)(L:ℕ→ℝ)
lemma heads0(p:∀ i:ℕ,PressB P (H i) (Q i) h (L i))(u:∀ x:Skye.Seat n, SumBudget (fun i=>if (H i).val.1=x then P.mass (H i).val.2 (L i) else 0) b)(hv:1≤h)(v:∀ i x, cut_V (Q i x)=0) : head_L (pool_F H Q P)=0:=by
 apply funext; intro i; apply funext; intro V; change cut_V (pool_F H Q P i V)=0; unfold pool_F; by_cases z: visible P i.val.2 ∅ V; · rw [pale_p V z]; let G:= pile_q (pea_Y H Q L p u hv i) hv (budget_Y H Q L p u hv i) V z; have he:= cut_V.hasSum G.hasSum; rw [←he.tsum_eq]; refine (tsum_congr (g:=fun _=>0) fun j=>?_).trans tsum_zero; unfold sZ; split; exact v _ _; exact map_zero cut_V
 rw [show caj P _ _ V=0 from if_neg z,map_zero]
local notation "Nl"=> numbering (Lane n)
local notation "Nh"=> numbering (Reign n)
variable(P:BudgetPoint)(R:PathData SU.group){q:Clip}{σ C Λ:ℝ}(p:R.Bounds q σ C Λ)(v δ:ℝ)(D': OriK P.order v)(hc:0≤v)(hw:Decent q P)(hp:Geo.Width P q σ)(hn:60 <(More n).val)
include p hc D' hw hp
abbrev lite_b (n:Side)(P:BudgetPoint)(R:PathData SU.group)(q:Clip)(δ:ℝ):RegBudget n:= Beau.pool_F (fun i=>Bra (numbering (Lane n) i) P R) (fun i=>ham (numbering (Lane n) i) P q R δ) P
abbrev lit_P (n:Side)(P:BudgetPoint)(R:PathData SU.group)(q:Clip)(δ:ℝ):RegBudget n:= Beau.pool_F (fun i=>Epi (numbering (Reign n) i) P R) (fun i=>gustH (numbering (Reign n) i) P q R δ) P
abbrev rate_b(P:BudgetPoint)(q:Clip)(σ C v δ:ℝ):ℝ:=v*Collection.turnFee P*|AnalyticBridge.VerifiedReset.factor*δ| * P.threshold^2 * Quotes.lowBase SU.group q P σ C
abbrev rate_h(P:BudgetPoint)(q:Clip)(σ C v δ:ℝ):ℝ:=v*Collection.turnFee P*|0+AnalyticBridge.VerifiedReset.factor*δ| * P.threshold^3 * Quotes.highBase SU.group P σ C
local notation "Rb"=>rate_b P q σ C v δ
local notation "Rh"=>rate_h P q σ C v δ
local notation "Yb"=>lite_b n P R q δ
local notation "Yh"=>lit_P n P R q δ
include hn
lemma thirst (ht: 1≤ h)(k:ℕ) : IncX (fun _=>False) Yb P h Rb ∧ Ionic P k Yb ∧ head_L Yb=0 ∧∀ V:Orbit n, HasSum (fun i:Lane n=>Vow.march P (χx P R i) (oV (ham i P q R δ)) V) (exponentL P Yb V.1):=by
 let H(i:ℕ):= Bra (Nl i) P R; let Q(i:ℕ):= ham (Nl i) P q R δ; let L(i:ℕ):= Taxi.p0 (Nl i) P q R δ v
 have hP(i):PressB P (H i) (Q i) h (L i):=wantV P R hw v D' _ δ _; have hx:= (reg_p (n:=n) R P p hw hp δ v hc).1; have hk(y:Xo): SumBudget (fun i=> if (H i).val.1=y then P.mass (H i).val.2 (L i) else 0) Rb:= Cost.equiv Nl (hx y)
 have hW(i : ℕ)(t:Nonwrapping (H i).val.2 (H i).val.1) : spark (H i).val.1 (Q i):=by
    have hz:= hotLow P R p hw δ hn (Nl i) t; let b:= AnalyticBridge.VerifiedReset.wedge Averaging.axes01 (spike SU.group); let o:=(H i).val.1; let U:=b.field o; have hu:IsAffineDirection o U:= (LinearJet.isAffine ..).mpr ⟨b,rfl⟩
    exact spark_H (X':=H i) (bust P R hw v D' _ δ).1 (hz U U hu hu).2 fun x y p v=>(hz x y p v).1
 refine ⟨stride_E H Q L hP hk ht,wish_E H Q L hP hk (fun i h p=>hW i h) ht,heads0 H Q L hP hk ht (fun i x=>?_ ),fun V=>?_ ⟩
 · change blind_E (moldV n _)=0; rw [mon_v,oqua]
 exact (Nl).hasSum_iff.mp (profit_E H Q L hP hk ht V)
lemma crown_V (ht: 1≤ h)(k:ℕ) : IncX (fun _=>False) Yh P h Rh ∧ Ionic P k Yh ∧ head_L Yh=0 ∧∀ V:Orbit n, HasSum (fun i:Reign n=>Vow.march P (ωx P R i) (oV (gustH i P q R δ)) V) (exponentL P Yh V.1):=by
 let H(i:ℕ):= Epi (Nh i) P R; let Q(i:ℕ):= gustH (Nh i) P q R δ; let L(i:ℕ):= p2 (Nh i) P q R δ v
 have hP(i):PressB P (H i) (Q i) h (L i):=capZ P R p hw v D' _ δ _; have hx:= (reg_p (n:=n) R P p hw hp δ v hc).2; have hk(y:Xo): SumBudget (fun i=> if (H i).val.1=y then P.mass (H i).val.2 (L i) else 0) Rh:= Cost.equiv Nh (hx y)
 have hW(i : ℕ)(t:Nonwrapping (H i).val.2 (H i).val.1) : spark (H i).val.1 (Q i):=by
    have hz:= hotMax P R p hw δ hn (Nh i) t; let b:= AnalyticBridge.VerifiedReset.wedge Averaging.axes01 (spike SU.group); let o:=(H i).val.1; let U:=b.field o; have hu:IsAffineDirection o U:= (LinearJet.isAffine ..).mpr ⟨b,rfl⟩
    exact spark_H (X':=H i) (Taxi.boomV P R p hw v D' _ δ).1 (hz U U hu hu).2 fun x y p v=>(hz x y p v).1
 refine ⟨stride_E H Q L hP hk ht,wish_E H Q L hP hk (fun i h p=>hW i h) ht,heads0 H Q L hP hk ht (fun i x=>?_ ),fun V=>?_ ⟩
 · change blind_E (moldV n _)=0; rw [mon_v,oqua]
 exact (Nh).hasSum_iff.mp (profit_E H Q L hP hk ht V)
end YM.CF.Beau
