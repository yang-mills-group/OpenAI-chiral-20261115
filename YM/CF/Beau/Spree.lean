import YM.CF.Beau.Cubs
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
local notation "Nl"=> numbering (Lane n)
variable(P:BudgetPoint)(R:PathData SU.group){q:Clip}{σ C Λ:ℝ}(p:R.Bounds q σ C Λ)(v δ:ℝ)(D': DayT P.order v)(hc:0≤v)(hw:Decent q P)(hp:Geo.Width P q σ)(hn:60 <(More n).val)
local notation "Rd"=> (P.supportExponent+1+1)
variable (T:Ids n)(hv:1 ≤ h)(hL:(P.supportExponent+1+1)/(P.B:ℝ)≤σ/8)
abbrev Yp(P:BudgetPoint)(R:PathData SU.group)(i:ℕ):= χx P R (numbering (Lane n) i)
abbrev argsQ (P:BudgetPoint)(R:PathData SU.group)(q:Clip)(δ:ℝ)(i:ℕ): Support (More n)→ Copy n:=regV T P R q δ (Nl i) (Yp (n:=n) P R i)
abbrev ΘK(T:Ids n)(P:BudgetPoint)(R:PathData SU.group)(q:Clip)(δ:ℝ):Cusp n:= ΘS (Yp P R) (argsQ T P R q δ) P
abbrev rate_μ(P:BudgetPoint)(q:Clip)(σ C v δ:ℝ):= |δ| * Footprint.payment 1 P.B 0 (σ/8) 1 (Fintype.card Signed * cap_cost q P σ C v) (P.supportExponent+1+1) Geo.lowCount
private lemma born_c(i:ℕ)(l:Clip): regV T P R l δ (Nl i)=chasmR (Yp P R i) (argsQ T P R l δ i):=by unfold argsQ regV chasmR; rw [Pi.single_eq_same]
private lemma blind_l(X:Aura n)(V:Orbit n)(i:ℕ)(c:Clip) : cut_V (μV (Yp P R) (argsQ T P R c δ) X D i V)=0:=by
 unfold μV; split; swap; exact map_zero cut_V
 rename_i v; change cut_V ((regV T P R c δ _ (Yp (n:=n) P R _) _) V)=0; unfold regV chasmR; rw [Pi.single_eq_same,Pi.smul_apply,map_smul]; suffices he: cut_V ((oV (herV T R c P (Nl i).1 (Nl i).2 D)) V)=0 from by rw [he,smul_zero]
 change cut_V (loanW R c P (0:Site (More n)) _ _ _)=0; unfold loanW; rw [map_sub]; unfold warmK; rw [show cut_V (Pastry.hollow _)=_ from oqua _]; split; simp; rw [show cut_V (Pastry.hollow _)=_ from oqua _,sub_zero]
include p D' hc hw hp hv hL
lemma Λro :∃ Z:Aura n→ℝ, Thr (ΘK T P R q δ) Z P h ∧ (∀ x:Skye.Seat n,tallB Z P.B Rd x ≤ rate_μ P q σ C v δ) ∧ veil_M (ΘK T P R q δ)=0∧∀ V:Orbit n,FleetS P.threshold V.1→ HasSum (fun i:Lane n=>fuelV P (regV T P R q δ i) V) (fuelV P (ΘK T P R q δ) V):=by
 let Y:=Yp (n:=n) P R; let F:=argsQ T P R q δ
 let G(i):= |δ| * bill_l R (Nl i).2 q v P
 have he(i:ℕ)(D':Support (More n)): Vow.Medal P (Y i).val D' (F i D') h (G i):= giftD P R T hc (by assumption) hw _ δ D' (zero_le_one.trans hv) -- check
 have hg:= Quotes.hit_scale (abs_nonneg δ) (stunL (n:=n) v P R p hc Rd (by have hx:=P.exponent_pos; positivity) hL)
 have ht: Ac.Hit (fun i:ℕ=> (Y i).val) P.B G Rd (rate_μ P q σ C v δ):=fun i=>Cost.equiv Nl (hg i)
 obtain ⟨hp0,t⟩:= sail_F Y F G he hv ht
 refine ⟨vis Y G,hp0,t,?_,fun V u=>?_ ⟩
 · funext X D V; change cut_V (ΘS Y F P X D V)=0; unfold ΘS lasting zenS; split; swap; exact map_zero cut_V
   rename_i q1; let M(i:ℕ):= μV Y F X D i
   have hp:=cut_V.hasSum ((Vow.lend (F:=M) (fun i=> mail_k Y F G he hv X i D) (milk_P Y F G he hv ht X) hv V q1).hasSum)
   exact hp.tsum_eq.symm.trans ((tsum_congr (g:=fun _=>0) fun j=>blind_l P R δ T X V j q).trans tsum_zero)
 have ht':=keen_Q Y F G he hv ht V u
 simp_rw [←show ∀ i:ℕ, _=chasmR (Y i) (F i) from fun i=>born_c P R δ T i q] at ht'
 exact (Nl).hasSum_iff.mp ht'
end YM.CF.Beau
