import YM.CF.Vp929.EveryLevel
import YM.CF.Vp929.Roof.Fit
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

variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
theorem law_available: AvailableΛ VolumeCape.Dream.Nimbus :=by
   intro b d t z; obtain ⟨M,l,k,u,p,q,G⟩:= VolumeCape.Dream.arch t z
   refine ⟨M,fun B u' => ⟨k,u,l,p,q, fun m v=>?_⟩⟩
   exact G (CSide m B) (u'.trans (show B.val ≤ m.val*2*B.val from Nat.le_mul_of_pos_left _ (Nat.mul_pos m.property two_pos)))
/-- Co-compatible with the finite-range-in-law strengthening. -/
theorem ratevol (a:ℕ) :
  ∃ (K:Teller SU.group)(L:ChartRatio SU.group),K.j=4 ∧ LocalRatio L ∧ K.top.clip.direct ≤1 ∧∃ (C:ℝ) (P:Patch), P.J = 4 ∧ a ≤ P.L.val ∧
  ∃ (V:Grace K P L)(T:Acorn.Repair K.j)(b₁:ℕ),1 ≤ b₁ ∧
  ∃ d:ℝ,0<d ∧∃ (U:Grasp V.U (P.L^b₁) d)(W:GivenX V U)(M:Side)(J:Robes M V W),U.baseline ≤ T.d ∧ J.k ≤ J.roomX ∧∃ (K0 Gv sℝ:ℝ),0<K0 ∧ 0<Gv ∧ 0<sℝ∧ Budget (P.L^b₁) d sℝ ∧ ∃ (F0:Scrolls (P.L^b₁))(lΛ:ℕ), (∀ m, ScaleK K0 Gv (F0 m)) ∧ RackedΛ (VolumeCape.Dream.Nimbus lΛ) J ∧∃ (KX b vL c l b₀ DD E C0 h1 r:ℝ)(kT d':ℕ) (P_: Pic.Span W.pearl KX b vL c l b₀ kT), Roe.Port P_ DD E C0 h1 r d' ∧∀ᶠ h:ℝ in atTop, C0≤ h ∧ ∀ᶠ N0:ℕ in atTop, IntervalPS V Chi.canonical b₁ h F0 (VolumeCape.Dream.Nimbus lΛ) C J N0:=by
 obtain ⟨K,L,p,v,f,C,N',H⟩:= rate_ledger_0 law_available; let b:Side:= ⟨2*(a+N'+1)+1,by omega⟩; let P:Patch:=⟨b,4,by decide,by change 3≤2*(a+N'+1)+1; omega,by exact ⟨a+N'+1,rfl⟩⟩
 obtain ⟨V,T,b₁,vH,F⟩:=H P (show N'≤2*(a+N'+1)+1 by omega) rfl; obtain ⟨e,t,u⟩:=F b₁ le_rfl; obtain ⟨U,W,M,J,uR,tR,A,D,aS,h1,h2,h3,hB,Fp,l,hV,δ,pV⟩:=u Chi.canonical e t le_rfl
 exact ⟨K,L,p,v,f,C,P,rfl,(show a≤ 2*(a+N'+1)+1 by omega),V,T,b₁,vH,e,t,U,W,M,J,uR,tR,A,D,aS,h1,h2,h3,hB,Fp,l,hV,δ,pV⟩
/-- The actual signed-denominator estimate (level zero). This version chooses one fixed x and states also that a.e. pivot in a tail pays the estimate. All step and Cape purchases in `ratevol` can be made together with it (see proof). -/
theorem denominator (ε:ℝ) : ∃ (K:Teller SU.group)(R:Patch)(L:ChartRatio SU.group), K.j=4∧R.J=4∧Odd R.L.val∧LocalRatio L∧K.top.clip.direct≤1 ∧∃ (V:Grace K R L)(b₁:ℕ) (d:ℝ), 1 ≤ b₁ ∧ 0 < d ∧∃ (U:Grasp V.U (R.L^b₁) d)(W:GivenX V U)(M:Side)(J:Robes M V W), J.k ≤ J.roomX ∧∃ (N0:ℕ)(h:ℝ)(F C Q:ℝ→ℝ),1 ≤ h ∧ Pitching.Focus.Appointed J Chi.canonical Q F C h N0 ∧
       ∃ (Y:Prescription R (R.L^b₁)) (d₀ z:ℝ), Service V U W J Chi.canonical h F C Q Y N0 d₀ ∧ Retag V U W J h N0 d₀ ∧ CutFrom Q F C J Chi.canonical h Y N0 d₀ ∧ ε < z ∧ 1 ≤ Real.log z ∧ 0<z ∧ ∃ (c:ℝ)(F0:Scrolls (R.L^b₁)) (z':ℝ)(lΛ:ℕ), RackedΛ (VolumeCape.Dream.Nimbus lΛ) J ∧ Sculpture V Chi.canonical b₁ h F0 Q F c N0 J z' ∧ z'≤z ∧
       (∀ᵐ x ∂ volume, z ≤ x → DActual V W J Chi.canonical h F C Q b₁ N0 Y d₀ x (VolumeCape.Dream.Nimbus lΛ)) ∧
       ∃ x:ℝ,z ≤ x ∧ DActual V W J Chi.canonical h F C Q b₁ N0 Y d₀ x (VolumeCape.Dream.Nimbus lΛ) := by
 obtain ⟨K,L,p,v,f,C,P,d,Pg,V,T,b,v',e,x,U,W,M',J,t,H,Rh,G,s,p1,p2,p3,p4,F0,lΛ,hP,rW,KX,b',vL,c,l,b₀,DD,E,C0,h1,r,kT,d',P_,wp,g⟩:= ratevol 0
 obtain ⟨h,hX,v⟩:=g.exists; obtain ⟨n,w⟩:=v.exists
 obtain ⟨F,Q,c,z,Pκ,y₁,d₀,Pζ,vG,Tκ,D,t,e'⟩:=w.pays
 let a:= max (max (ε+1) (Real.exp 1)) d₀; have hx:d₀ ≤ a := le_max_right ..; have hl:Real.exp 1 ≤ a:= le_trans (le_max_right ..) (le_max_left ..); have he:ε<a:= lt_of_lt_of_le (lt_add_one _) ((le_max_left ..).trans (le_max_left ..))
 let Y(x):=DActual V W J Chi.canonical h F c Q b n Pκ y₁ x (VolumeCape.Dream.Nimbus lΛ); obtain ⟨y,u,hy⟩ := select_one (Y:=fun x=> d₀≤ x ∧ Y x) ⟨_,e'.mono fun x p u=>⟨u,p u⟩⟩ a
 refine ⟨K,P,L,p,d,P.odd_side,(by assumption),f,V,b,e,v',x,U,W,M',J,H,n,h,F,c,Q,w.permit.step,z,Pκ,y₁,a,Pζ,vG,Tκ,he,?_, (Real.exp_pos _).trans_le hl,C,F0,d₀,lΛ,rW,D,hx, e'.mono (fun x p r=> p (hx.trans r)),y,u.le,hy.2⟩
 exact (Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le hl)).2 hl

end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.ratevol
#print axioms YM.CF.Py.Rate.denominator
#print axioms YM.CF.Py.Rate.DActual.ratevol
