import Palm.Chain
import Palm.Ready
import Palm.Starting
import YM.CF.Swell.Vote
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L} {d h x : ℝ}
  {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} (J : Robes N V W) (q : Chi) (h : ℝ) (D C R0 : ℝ→ℝ) {N0 : ℕ} (T : Month x 1 6 2 N0 V W) (ht : T.q ≤ m.val)
  (S : Cape m B R.L) (ρ : ℕ→ℝ) (f : ℕ→ℝ) (k i : ℕ)
namespace Parcel
open Branch
open Pitching Pitching.Focus
variable {J q h D C R0 T S ρ f i}
variable (s:Parcel J q h D C R0 T ht S ρ f k)
variable {delay:ℝ}{P:Prescription R B}(H:Service V U W J q h D C R0 P N0 delay)(t:s.Prepared P delay)
variable (G:Morn K)(Q:Diary)(sk:G.After R)(Lq:ShelfTh G Q R0 D C J q h P N0 delay)
local notation "Yc"=> (hat R.L x i)
local notation "Ar"=> G.armor
local notation "w0"=> ((Actual T ht S f k).toSpine.address i)
local notation "fϕ"=> thinAllot G.Mult R Yc
local notation "fZ"=> (3*dleaf R.L Yc)

open Tune Roots Oath Bake Neon
attribute [-instance] instDecidableEqLex
variable {I:Type}[Fintype I][LinearOrder I]{Aρ qv ε:ℝ}(CA:Καlendar R G.armor qv Aρ G.Mult ε)
local notation "Nc" j:max=> cell m B R.L j
variable (xs:Site (cell m B R.L i)) -- unused
-- ABI
local notation "Mk"=> Mew.Key (LabelΩ I)
local notation "YΩ"=> hat R.L x i
local notation "ηκ" j:max=> (allotΨ R.L (hat R.L x j))
local notation "fi" i:max=> (mesh m R.L i)
local notation "St_" i:max=> (V.L.op (k-1-i) (kint m B R.L i))
variable (Ω:I→Site (cell m B R.L i))(v:Very_Ψ (N:=mesh m R.L i) (B:=B) Ω (s.gram i).p.B)
open scoped Mew
local notation "wrk" j:max=> ((Actual T ht S f k).toSpine.address j).step V
variable (d0 top:ℕ)(Ωs:∀ j:ℕ,I→Site (cell m B R.L j))
variable (Eξ:Mew.Key (LabelΩ I) → RegBudget (cell m B R.L top))(Kϕ:Mew.Key (LabelΩ I) → ForceBudget (cell m B R.L top))

open Swell
-- arithmetic engine. Seeds .
lemma φYeq (v:BudgetPoint)(pv:v.order=G.coinP.order)(pu:v.power=G.coinP.power)(hE:v.supportExponent=G.coinP.supportExponent)(a:ℝ): Yρ v G.φ a=Yρ G.coinP G.φ a:=by unfold Yρ κplant Moto.trotΦ Taxi.tollV AnalyticBridge.VerifiedReset.pairBill; rw [pv,pu,hE]

local notation "PM"=> (s.gram top).p
local notation "Et"=> (ηκ top)
local notation "Si"=> cell m B R.L top
local notation "Aot" i:max=> cue_Φ (ηκ top) h (tiν (i:LabelΩ I))
local notation "Ao" i:max=> Aot i
local notation "Kr" i:max=> seedsY (P:=PM) (Ao i) (xΞ (Ωs top) i)
include t CA
lemma plantTop (hk:top≤k)(hi:1≤top)(h0:1≤h)(hs:Very_Ψ (N:=mesh m R.L top) (B:=B) (Ωs top) (s.gram top).p.B)
   (u:Ready_K R.L (hat R.L x top) ∧ 0<allotΨ R.L (hat R.L x top)∧ Oath.Gala 2 6 100 (hat R.L x top) 3)
   (hf:Yρ G.coinP G.φ Hπ ≤ Aρ): Leaf_R (s.gram top) (Ωs top) (dry_C (shootX (fun i=> Kr i))) 0 h G.Mult Aρ (Et) R.L:=by
 have hp:PM=T.a top:=by obtain ⟨_,_,_,jt⟩:=t; rw [jt.gramZ]
 have hb: (PM).order=6:=hp ▸ (T.boot top).2.2.2.2
 have he: (PM).power=2:=hp ▸ (T.boot top).2.2.2.1
 have hT: (PM).threshold=temp (hat R.L x top):=hp ▸ (T.boot top).1
 have pe: (PM).supportExponent=1:=hp ▸ (T.boot top).2.2.1
 have hB: 10 ≤ (PM).B:=by rw [hp,(T.boot top).2.1]; exact u.1.hint _ le_rfl
 have hL:1<R.L.val:=by have h:=CA.side; omega
 have hHb:1≤ radiusB (hat R.L x top):= Nat.le_trans (by norm_num:(1:ℕ)≤10) (u.1.hint _ le_rfl)
 have hY:20 ≤ (cell m B R.L top).val:=by
    have hq(i:ℕ):2 ≤ (cell m B R.L i).val:=by change 2 ≤ (mesh m R.L i).val *2*B.val; exact ((show 2 ≤ (mesh m R.L i).val*2 by have h:1≤(mesh m R.L i).val:=Subtype.property _; omega)).trans (Nat.le_mul_of_pos_right _ B.property)
    obtain ⟨t,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega:top ≠ 0); rw [grows]; exact Nat.mul_le_mul (hq t) CA.side
 have h':=zero_lt_one.trans_le h0
 apply launch_LeafTh (Ωs top) (s.gram top) CA hs _ h0 u.2.1.le
 intro i
 let j:=tiν (i:LabelΩ I); let U:= Ao i; let pS:=Et
 have eF: InΦ U:= sCap _ j
 have hG:h^2*‖U.2‖≤pS*Hπ∧‖U.1‖≤pS*Hπ:=by
    obtain ⟨a,b,c⟩:=norms_t (Gior j) pS h u.2.1 h'; have hb(w:ℝ)(p:w ≤ ‖Gior j‖):pS*w≤ pS*Hπ:=mul_le_mul_of_nonneg_left (p.trans (basis_D _)) u.2.1.le; have hv:‖(U.2)‖=max ‖(U.2.1)‖ ‖(U.2.2)‖:=rfl; rw [mul_comm _ ‖U.2‖,hv]; refine ⟨?_, c.trans_le (hb _ ((norm_fst_le _).trans (norm_snd_le _)))⟩; rcases le_total ‖U.2.1‖ ‖U.2.2‖ with x|x; · rw [max_eq_right x]; exact b.trans_le (hb _ ((norm_snd_le _).trans (norm_snd_le _)))
    rw [max_eq_left x]; exact a.trans_le (hb _ (norm_fst_le _))
 have hr:=(plantsY (P:=PM) (L:=R.L) U h (pS*Hπ) G.φ eF (xΞ (Ωs top) i) (hb ▸ G.hD) G.hΦ hB (show Oath.Gala (PM).power (PM).order 100 (hat R.L x top) 3 by rw [he,hb]; exact u.2.2) hHb hT (by change 20 < (Si).val*2; omega) (show 3≤ (Si).val by omega) hL h0 hG.1 hG.2).1
 have eh: Yρ PM G.φ (pS*Hπ) ≤ Aρ*pS:=by
    rw [φYeq G PM (hb.trans G.order.symm) (he.trans G.power.symm) (pe.trans G.ge.symm), Yρ,bond_Q, mul_left_comm, mul_comm Aρ]; exact mul_le_mul_of_nonneg_left hf u.2.1.le
 refine ⟨Provides.liftE h (s.gram top) _ _ hr.vest eh,hr.site,hr.flair⟩
#check plantsY
#check launch_LeafTh
end Parcel
end YM.CF.Py.Rate
