import Sparkle.Ascent
import Sparkle.Seed
set_option autoImplicit false
set_option maxHeartbeats 2200000
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
-- earnings profiles quant issued b through \ell. Accept permit Rent
open Larch Vow Bake Mew Roots Rive Neon
local notation "BN"=> mid N B
local notation "Η"=> Scree.Hub (mid N B)
local notation "Θ"=> X.p.supportExponent
variable {J:Type}[LinearOrder J][Fintype J]
variable (σ:J → Site (mid N B))(K_ E0:Key J →  RegBudget (mid N B))(F_:Key J →  ForceBudget (mid N B))
variable (Xo Yo:Key J →  RegBudget (mid P B))(Zo:Key J →  ForceBudget (mid P B)) {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)} (Xi:Op SU.Slot){q:Chi}{h:ℝ}
local notation "Tz"=> Cube.node ∘ σ
local notation "P_"=> X.p
variable (Q:J → ℝ)(qE:J → ArcΦ)(qΨ:J →  ArcΦ)(s:J → ℂ)
variable {Vp Va Bk Cμ Wη Eμ Cx ZΨ QΦ ξQ:ℝ} -- remove
variable (Fκ:Cause_P V U G S G₀ G₁ X Y Xo Yo Zo Xi q kL h Vp Va σ Q qE K_ F_ qΨ s Bk Cμ Wη Eμ Cx ZΨ QΦ)
open Roots Mew Rive Oise
variable {α:Type}[DecidableEq α]
open scoped YM.CF.Mew
local notation "Ω"=> mid N B
local notation "qμ"=> (Cube.node ∘σ)
local notation "Ωk"=> MixT σ
open Drift Oise
attribute [-instance] instDecidableEqLex
open Compass
namespace Dyad
open Swell Compass Taxi Ione Tune Grain
-- indexing universe. B fixed. 
namespace Keeping
variable (A: SiteLedger V U kL q)
#check SiteLedger
local notation "Sc" i:max=>mid (A.side i) B
variable {I:Type}[LinearOrder I][Fintype I]
#check geo
local notation "LogA" i:max=> heir V A I i
local notation "Geo" i:max=> geo (I:=I) V A i
variable (v0 f:ℕ)(hzT κ Vq:ℝ)
local notation "τ" k:max=> A.money k
local notation "bT" k:max=> (A.gram k).p.B
local notation "Spr" i:max=> sap (N:=A.side i) (B:=B) (A.gram i).p (A.money i)
local notation "Cure" i:max=> TraceS (mid (A.side i) B)
-- IR Scope. Makers indexed $C common regardless r, D per-r. n0. i=r store only weak Lawn. Good when pressure-turning (order1 estimate at most Aρ, Uc, use sparse)
variable {C Dσ:ℕ → ℝ}{D:ℕ → ℕ → ℝ}(i0:ℕ)(e0:i0<v0)
variable (hx:∀ (i:ℕ),f ≤  i → i ≤ v0 →  ∀ (I:Type)[LinearOrder I][Fintype I](o:I → Site (mid (A.side i) B)),Very_Ψ o (A.gram i).p.B →  Chew hzT (A.money i) κ Vq R.L (A.gram i) (sap (A.gram i).p (A.money i) false) (sap (A.gram i).p (A.money i) true) o (leafER o (A.gram i).p (A.money i)))
  (kE:∀ i:ℕ,f ≤  i → i<v0 →  KnollStep V U kL hzT (A.gram i) (A.gram (i+1)) (A.job i) (A.ratio i) (A.plant i) (A.plant (i+1)) (A.opT i) q (A.money (i+1)) (A.money i) κ Vq)
  (liftV:∀ i,f ≤  i → i<v0 → ∀ (I:Type)[LinearOrder I][Fintype I](o:I → Site (mid (A.side i) B)), Very_Ψ o (A.gram i).p.B →  Very_Ψ (adapt V A i o) (A.gram (i+1)).p.B)
variable (hH:1 ≤ hzT)(hp:0 ≤ κ)(hb:0 ≤  Vq)(p_:∀ i,f ≤  i → i ≤ v0 → 0 ≤ A.money i)
namespace Office
variable (hx0:f ≤  i0)(hv0:i0 ≤ v0)
variable (M Mp:TraceS (mid (A.side i0) B))(Lh:ℕ →  TraceS (mid (A.side i0) B))
include hx hx0 p_ hH hp hb
local notation "Ofs"=>Office V A v0 hzT κ Vq
-- forward records priced lower. congruence under update
omit hx hx0 p_ hH hp hb
variable (hρ:Office V A v0 hzT κ Vq C D i0 M Mp Lh)(C':ℕ→ℝ)(D':ℕ→ℕ→ℝ)
include hρ
lemma onward (t:∀ j, i0 ≤ j  → C j=C' j)(u:∀ k j,i0 ≤ j → D k j=D' k j):Accounts V A v0 hzT κ Vq C' D' i0:=by
 refine ⟨M,Mp,Lh,⟨fun j h x=>?_,fun k j h x y=>?_,?_,?_⟩⟩
 · rw [←t _ h]; exact hρ.assets j h x
 · rw [←t _ h,←u _ _ h]; exact hρ.pays k j h x y
 · intro I _ _ o v; obtain ⟨L,p,q⟩:=hρ.blank I o v; exact ⟨L,p,q.raiseP V A o L t⟩
 intro r p k I _ _ o h; obtain ⟨T,x,q⟩:=hρ.grant r p k I o h; exact ⟨T,x,q.raiseZ V A o T t (u r)⟩
omit hρ
include hH p_ hp hb hx0 hx
lemma primary (x:f≤v0):Accounts V A v0 hzT κ Vq 0 0 v0:=by
 let a:=Spr v0; have h:= p_ v0 x le_rfl; let θ:=A.money v0
 apply found V A v0 f hzT κ Vq v0 hx hH hp hb p_ x le_rfl (a false) (a true) (fun _=>a false)
 · intro I _ _ o t; let L:=leafER o (A.gram v0).p θ; have e:=hx v0 x le_rfl I o t
   exact ⟨L,e,.cane o (chew_risk V A hzT κ Vq v0 _ _ o L e (mul_nonneg hp h) (mul_nonneg hb h)).1⟩
 · intro v h t; omega
 · intro k i j t v; omega
 intro i h t; omega
include kE liftV e0
-- index r>=i0+1 as r+1. Seat 0 fallback. include r outside via collapsing to Np.
lemma film (M Mp:TraceS (Sc (i0+1)))(Lh:ℕ→TraceS (Sc (i0+1)))(pT:Office V A v0 hzT κ Vq C D (i0+1) M Mp Lh):
  ∃ (C':ℕ→ℝ)(D':ℕ→ℕ→ℝ),Accounts V A v0 hzT κ Vq C' D' i0 ∧(∀ j,i0 < j  → C j=C' j)∧(∀ k j,i0 < j → D k j=D' k j):=by
 let Areq(i:ℕ):Prop:= 0< i ∧ i0+1 ≤ i-1 ∧ i-1 ≤ v0
 let Pa(i:ℕ):= if Areq i then Lh (i-1) else Mp
 have hxR:f ≤ i0+1:=hx0.trans (Nat.le_succ _)
 have hq0:= p_ (i0+1) hxR e0
 have he(i:ℕ)(I:Type)[LinearOrder I][Fintype I](o:I→Site (Sc i0))(v:Very_Ψ o (bT i0)):∃ L:Log I (Sc (i0+1)), Lawn hzT (A.money (i0+1)) κ Vq R.L (A.gram (i0+1)) M (Pa i) (adapt V A i0 o) L∧
    -- branching.Witness Exact!
    (if h:Areq i then Charge V A C (D (i-1)) hzT κ Vq (i-1) v0 (i0+1) (adapt V A i0 o) L else Proto V A C hzT κ Vq v0 (i0+1) (adapt V A i0 o) L):=by
      have h:=liftV i0 hx0 e0 I o v
      unfold Pa
      split
      next x=>exact pT.grant _ x.2.1 x.2.2 I _ h
      next x=>obtain ⟨L,e,p⟩:= pT.blank I _ h; exact ⟨L,chew_risk V A hzT κ Vq (i0+1) _ _ _ L e (mul_nonneg hp hq0) (mul_nonneg hb hq0),p⟩
 choose Bq e using fun (r:ℕ)(o:Site (Sc i0))=> he r (Fin 1) (uniO (Fin 1) o) (veryOne ..)
 obtain ⟨u,w,Pη,Wη,p,c⟩:=(kE i0 hx0 e0).register ℕ (0:ℕ) M Pa Bq (fun r o=>(e r o).1)
 let C':= update C i0 u; let D'(k):= update (D k) i0 (w (k+1))
 have h1(i:ℕ)(v:i0< i): C i=C' i:=(update_of_ne v.ne' _ _).symm; have h2(k i:ℕ)(v:i0< i): D k i=D' k i:=(update_of_ne v.ne' _ _).symm
 have hy:C' i0=u:=update_self ..; have hz(k:ℕ):D' k i0=w (k+1):=update_self ..
 have hν:=p 0
 have hpV(j:ℕ)(q:i0 ≤ j)(v:j<v0): Niche R.L (C' j) 0:=by
    rcases eq_or_lt_of_le q with h|h; · rw [←h,hy]; exact ⟨hν.non,hν.amp,(by rw [abs_zero]; norm_num),hν.back⟩
    rw [←h1 _ h]; exact pT.assets j h v
 have hU(k j:ℕ)(q:i0 ≤ j)(r:j<k)(z:k ≤v0):Niche R.L (C' j) (D' k j):=by
    rcases eq_or_lt_of_le q with h|h; · rw [←h,hz,hy]; exact p _
    rw [←h1 _ h,←h2 _ _ h]; exact pT.pays k j h r z
 let Lo(r):Cure i0:=Wη (r+1)
 refine ⟨C',D',found V A v0 f hzT κ Vq i0 hx hH hp hb p_ hx0 e0.le Pη (Wη 0) Lo ?_ hpV hU ?_,h1,h2⟩
 · intro I _ _ o v; obtain ⟨T,p,e0T⟩:=he 0 I o v; rw [dif_neg (show ¬Areq 0 by simp [Areq])] at e0T
   obtain ⟨T0,tv,rv⟩:=c 0 I o v T p; rw [←hy] at rv; exact ⟨T0,tv,.reel i0 e0 o T0 T (w 0) (e0T.raiseP V A _ T h1) (chew_risk V A hzT κ Vq i0 _ _ o T0 tv (mul_nonneg hp (p_ i0 hx0 e0.le)) (mul_nonneg hb (p_ i0 hx0 e0.le))).1 rv⟩
 intro r v q I _ _ o hu; obtain ⟨Tv,pr,h⟩:=he (r+1) I o hu
 obtain ⟨gv,L,u⟩:=c (r+1) I o hu Tv pr
 have he_:Areq (r+1):=by unfold Areq; omega
 rw [dif_pos he_,Nat.add_sub_cancel] at h; rw [←hy,←hz] at u
 exact ⟨gv,L,.reel i0 v o gv Tv (h.raiseZ V A _ Tv h1 (h2 r)) (chew_risk V A hzT κ Vq i0 _ _ o gv L (mul_nonneg hp (p_ _ hx0 e0.le)) (mul_nonneg hb (p_ _ hx0 e0.le))).1 u⟩
#print axioms YM.CF.Py.Dyad.Keeping.Office.film
end Office
end Keeping
end Dyad
end YM.CF.Py
end
