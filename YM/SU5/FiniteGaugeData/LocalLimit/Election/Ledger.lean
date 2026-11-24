import YM.CF.Vp929.RATE
import YM.SU5.FiniteGaugeData.LocalLimit.Election.Chosen
import YM.SU5.FiniteGaugeData.LocalLimit.Heat.Responsive

/-! Election on the final prepared FiniteGaugeData prescription. The stored Shop witness supplies
real-path responsiveness of the very same physical step. -/
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
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
variable {F' G' Q₀ C:ℝ→ℝ}{F:(s:Side)→Scree.Loom s→Prop}{N0:ℕ}{W:GivenX V U}{M:Side}{J:Robes M V W}(q:Chi)(b:ℕ)(h a τ :ℝ)(F0:Scrolls B)
namespace LocalLimit
private theorem calibrated (a:ℕ) {F:ℕ→(s:Side)→Scree.Loom s→Prop} (hF:AvailableΛ F) :
  ∃ (K:Teller SU.group)(L:ChartRatio SU.group),K.j=4 ∧ LocalRatio L ∧ K.top.clip.direct ≤1 ∧∃ (C:ℝ) (P:Patch), P.J = 4 ∧ a ≤ P.L.val ∧
  ∃ (V:Grace K P L)(T:Acorn.Repair K.j)(b₁:ℕ),1 ≤ b₁ ∧
  ∃ d:ℝ,0<d ∧∃ (U:Grasp V.U (P.L^b₁) d)(W:GivenX V U)(M:Side)(J:Robes M V W),U.baseline ≤ T.d ∧ J.k ≤ J.roomX ∧∃ (K0 Gv sℝ:ℝ),0<K0 ∧ 0<Gv ∧ 0<sℝ∧ Budget (P.L^b₁) d sℝ ∧ ∃ (F0:Scrolls (P.L^b₁))(lΛ:ℕ), (∀ m, ScaleK K0 Gv (F0 m)) ∧ RackedΛ (F lΛ) J ∧∃ (KX b vL c l b₀ DD E C0 h1 r:ℝ)(kT d':ℕ) (P_: Pic.Span W.pearl KX b vL c l b₀ kT), Roe.Port P_ DD E C0 h1 r d' ∧∀ᶠ h:ℝ in atTop, C0≤ h ∧ ∀ᶠ N0:ℕ in atTop, IntervalPS V Chi.canonical b₁ h F0 (F lΛ) C J N0:=by
 obtain ⟨K,L,p,v,f,C,N',H⟩:= rate_ledger_0 hF; let b:Side:= ⟨2*(a+N'+1)+1,by omega⟩; let P:Patch:=⟨b,4,by decide,by change 3≤2*(a+N'+1)+1; omega,by exact ⟨a+N'+1,rfl⟩⟩
 obtain ⟨V,T,b₁,vH,F⟩:=H P (show N'≤2*(a+N'+1)+1 by omega) rfl; obtain ⟨e,t,u⟩:=F b₁ le_rfl; obtain ⟨U,W,M,J,uR,tR,A,D,aS,h1,h2,h3,hB,Fp,l,hV,δ,pV⟩:=u Chi.canonical e t le_rfl
 exact ⟨K,L,p,v,f,C,P,rfl,(show a≤ 2*(a+N'+1)+1 by omega),V,T,b₁,vH,e,t,U,W,M,J,uR,tR,A,D,aS,h1,h2,h3,hB,Fp,l,hV,δ,pV⟩
structure Preparation where
  K : Teller SU.group
  kJ : K.j = 4
  direct : K.top.clip.direct ≤ 1
  R : Patch
  rJ : R.J = 4
  L : ChartRatio SU.group
  chart : LocalRatio L
  V : Grace K R L
  b : ℕ
  bp : 1 ≤ b
  d : ℝ
  dpos : 0 < d
  U : Grasp V.U (R.L^b) d
  W : GivenX V U
  M : Side
  J : Robes M V W
  hires : J.k ≤ J.roomX
  N0 : ℕ
  h : ℝ
  height : 1 ≤ h
  δ : ℝ → ℝ
  C : ℝ → ℝ
  R0 : ℝ → ℝ
  app : Appointed J Chi.canonical R0 δ C h N0
  P : Prescription R (R.L^b)
  delay : ℝ
  H : Service V U W J Chi.canonical h δ C R0 P N0 delay
  response : ResponsiveService J Chi.canonical N0 h delay P
  x : ℝ
  K0 : ℝ
  Gv : ℝ
  sμ : ℝ
  budget : Budget (R.L^b) d sμ
  F0 : Scrolls (R.L^b)
  scale : ∀ m, ScaleK K0 Gv (F0 m)
  calendarScale : ℝ
  genesis : ℝ
  early : genesis ≤ x
  sculpture : Sculpture V Chi.canonical b h F0 R0 δ calendarScale N0 J genesis

namespace Preparation
abbrev block (P : Preparation) := P.R.L^P.b
abbrev nominated (P : Preparation) (F : (s:Side)→Scree.Loom s→Prop) :=
  DActual P.V P.W P.J Chi.canonical P.h P.δ P.C P.R0 P.b P.N0 P.P P.delay P.x F

theorem elect (ε : ℝ) {F : ℕ→(s:Side)→Scree.Loom s→Prop} (hF : AvailableΛ F) :
    ∃ P : Preparation, ∃ l : ℕ, ε < P.x ∧ P.nominated (F l) := by
  obtain ⟨K,L,p,v,f,C,R,d,Pg,V,T,b,v',e,x,U,W,M',J,t,H,Rh,G,s,p1,p2,p3,p4,F0,lΛ,hP,rW,
    KX,b',vL,c,l,b₀,DD,E,C0,h1,r,kT,d',P_,wp,g⟩ := calibrated 0 hF
  obtain ⟨h,hX,vH⟩ := g.exists
  obtain ⟨n,w⟩ := vH.exists
  obtain ⟨δ,Q,cost,app,pres,delay,start,service,retag,cut,sculpt,_,buyers⟩ := w.pays
  let a := max (ε+1) start
  let Good (y : ℝ) := DActual V W J Chi.canonical h δ cost Q b n pres delay y (F lΛ)
  obtain ⟨y,ay,hy⟩ := select_one (Y:=fun y => start≤y ∧ Good y)
    ⟨_,buyers.mono fun y h₁ h₂ => ⟨h₂,h₁ h₂⟩⟩ a
  have response : ResponsiveService J Chi.canonical n h delay pres := by
    intro m n' location level p' q' threshold request
    obtain ⟨cap,rad,hpos,hbound,hr,shops⟩ := cut.ships m n' location level p' q' threshold request
    letI := hr
    obtain ⟨shop,ready,same⟩ := shops
    rw [same]
    exact realStep_receipt shop request ready cap
  let prep : Preparation := ⟨K,p,f,R,d,L,v,V,b,v',e,x,U,W,M',J,H,n,h,w.permit.step,
    δ,cost,Q,app,pres,delay,service,response,y,Rh,G,s,p4,F0,hP,C,start,hy.1,sculpt⟩
  exact ⟨prep,lΛ,(lt_of_lt_of_le (lt_add_one ε) (le_max_left ..)).trans ay,hy.2⟩

theorem main_election (ε : ℝ) : ∃ P : Preparation, ε < P.x ∧ P.nominated optionalLaw := by
  obtain ⟨P,_,h,hP⟩ := elect ε trueAvailable
  exact ⟨P,h,hP⟩
end Preparation
end LocalLimit
end Rate
end YM.CF.Py
