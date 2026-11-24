import GaugeFieldConstruction.Dockets
import GaugeFieldConstruction.JointConsult
import YM.SU5.Exchange.Visa.Fort
import YM.CF.Atala.Zork

/-!
# Joint pre-election funding for the two field franchises. Adapted from GaugeFieldConstruction/Tutelage, Dockets and LocalFieldBounds PF/Fountain.
-/
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
open Preparation
-- Custom local name for exactly the same data in PF.Fountain
structure FountainSt (P:Preparation): Prop where
 flow:∃ (K c a:ℝ), 1≤K ∧ 0<c ∧ 0<a ∧ ∀ᶠ n:ℕ in atTop,∀ m:Side,n≤ (CSide m P.block).val → ∀ J: Cascade.Interest (CSide m P.block), InterestX P.W.C _ J →∀ u:ℝ,1≤u→ ∃ (V:∀ S:Seal (Skye.Seat (CSide m P.block)), Lend m P.block P.d S), Hive.Vista P.U J.M J.P V 8 K ((Fintype.card Play:ℝ)*u) c a
theorem jointLatchSt {Q:Badge}(p: Marketable Q)(X:TintDemand)(TintRq: TintDemand)(NLeaf Tleaf:ℕ): CommissionVector (fun P=> LicensedHeight Q NLeaf X P ∧ (TintRateCommercial Tleaf TintRq P ∧ (Solstitial P ∧ FountainSt P)) ∧ Hallway P.J Chi.canonical P.h P.P P.N0 ∧ 8∣P.M.val):=by
  constructor; intro e' ε he Hq
  obtain ⟨K,L,pK,v,f,C,Pay,kC,Γ,Tξ,hPay,hKc,hΓ,Dg,A,C',N₀,hC,hA,hg,i1,i2,i3,H⟩:= jointCulmen YM.CF.Py.Rate.Audit1102.available NLeaf Tleaf
  obtain ⟨N'',Z⟩:= p.extra K L pK v f hC A C' Pay kC Γ hPay hKc hΓ hA hg Tξ Dg
  let N':= N₀+X K L Pay kC Γ Tξ  + N''+TintRq K L Pay kC Γ Tξ
  let t:Side:=⟨240 * N'+ 225, by omega⟩
  let R:Patch:= ⟨t,4,by decide,by change 3 ≤ 240*N'+225; omega, by refine ⟨120*N'+112,?_⟩; unfold t; simp; omega⟩ -- odd
  have hr:R.L.val=240*N'+225:=rfl
  have hv:15 ∣ R.L.val:=by omega
  have hw:R.L.val%16=1:=by omega
  obtain ⟨fee,V,T,b0,hB,Y⟩:=H R (show N₀ ≤ _ from by omega) rfl
  obtain ⟨b,LQ,υ⟩:= ((eventually_ge_atTop b0).and (Z R rfl hv hw (by omega) V T)).exists
  obtain ⟨q₃,h₃,μ⟩:=υ; obtain ⟨e0,t0,u⟩:=Y b LQ
  obtain ⟨A2,C1,dS,hA2,hC1,hdS,aS,pS⟩:= Tulip.funde_s K.j (by omega)
  obtain ⟨A3,C2,dT,hZ,hC2,hdT,aT,pT,hT⟩:= BProof.Spin.wallet V.width1 V.width2 V.pos1 V.pos2
  obtain ⟨cA,z₁,Q₁,q₁,mA,Qw⟩:= Atala.auric (R:=V.U) 8 2 (by norm_num) V.gate (by omega : 1≤K.j) (V.pos1.le) V.pos2.le V.width1 V.width2 V.note T
  let e:= min (min e' (min dS dT)) (min cA (min e0 q₃))
  have hd₁:e ≤ dS:=by unfold e; simp
  have hd₂:e ≤ dT:=by unfold e; simp
  have hd':e ≤ e':=by unfold e; simp
  have x:0 < e:=lt_min (lt_min he (lt_min hdS hdT)) (lt_min z₁ (lt_min t0 h₃))
  have ep:e≤ min e0 q₃:= by unfold e; simp
  obtain ⟨U,W,F,I,mo,hS,tP,hI,j⟩:=u Chi.canonical e x (ep.trans (min_le_left ..))
  obtain ⟨z_v,hb,wr,wh,seek⟩:=μ e x (ep.trans (min_le_right ..)) U W tP F I mo hS hI
  obtain ⟨M',J,Dp,K',Γp,hwR,h8,H,Rh,G,s,p1,p2,p3,p4,F0,lΛ,hP,rW,V₀,H₀,W₀⟩:=j z_v hb wr wh
  obtain ⟨KX,b',vL,c,l,b₀,kT,⟨P'⟩⟩:= Pic.crop0 W.pearl V.note (by omega) W.health; obtain ⟨DD,E,C0,h1,r,d',H'⟩:= Roe.portH P'
  have g: ∀ᶠ h:ℝ in atTop,C0≤ h ∧ ∀ᶠ n:ℕ in atTop, CoPayPS V Chi.canonical b h F0 (VolumeCape.Dream.Nimbus lΛ) C V₀ J n (fun Pβ=> Tutelage V J F I Chi.canonical h n A C' Pay kC Γ Tξ NLeaf Pβ ∧ RateCover J Chi.canonical h n Pay kC Γ Tξ Tleaf Pβ) ∧ WheelExact J Chi.canonical h n ∧ WheelX J Chi.canonical h n ∧ MeritWheel J Chi.canonical h n ∧ Q K L R V (R.L^b) e U W M' J F I A C' Pay kC Γ z_v K' Dp Tξ h n:=by
     filter_upwards [W₀,eventually_ge_atTop C0,seek M' J hwR H Dp K' Γp] with h p φ t'
     exact ⟨φ,((financeVector V Chi.canonical b h C F0 p.1 rW P' H' φ fee).and (p.2.and t')).mono fun n ⟨e,⟨a,b,c⟩,p⟩=> ⟨e,a,b,c,p⟩⟩
  obtain ⟨h,⟨hX,vH⟩,τ⟩:= (g.and (eventually_ge_atTop (Hq K R L V _ e U W M' J lΛ V₀))).exists
  obtain ⟨n,w,Lπ,HΨ,hΩ,ha⟩ := vH.exists
  obtain ⟨δ,Q,cost,app,hβ,pres,delay,start,service,retag,cut,sculpt,_,color,buyers⟩ := w.pays
  let a := max (ε+1) start
  let Good (y : ℝ) := DActual V W J Chi.canonical h δ cost Q b n pres delay y (VolumeCape.Dream.Nimbus lΛ)
  obtain ⟨y,ay,hy⟩ := select_one (Y:=fun y => start≤y ∧ Good y)
    ⟨_,buyers.mono fun y h₁ h₂ => ⟨h₂,h₁ h₂⟩⟩ a
  have response : ResponsiveService J Chi.canonical n h delay pres := by
    intro m n' location level p' q' threshold request
    obtain ⟨cap,rad,hpos,hbound,hr,shops⟩ := cut.ships m n' location level p' q' threshold request
    letI := hr
    obtain ⟨shop,ready,same⟩ := shops
    rw [same]
    exact realStep_receipt shop request ready cap
  let prep : Preparation := ⟨K,pK,f,R,rfl,L,v,V,b,(hB.trans LQ),e,x,U,W,M',J,H,n,h,w.permit.step,
    δ,cost,Q,app.hide,pres,delay,service,response,y,Rh,G,s,p4,F0,hP,C,start,hy.1,sculpt⟩
  have hvz: Solstitial prep:=by
    refine ⟨min A2 A3,max C1 C2,lt_min hA2 hZ,hC1.trans_le (le_max_left ..),?_⟩
    filter_upwards [eventually_ge_atTop (max aS aT)] with k hk n l
    constructor
    · intro M; exact ((Tulip.axis_down _ _ (pS M n (by omega)) e x hd₁).drop (min_le_left ..)).books (le_max_left ..)
    intro J p; have hz:J.P.toll V.f V.g V.F1 V.F2:=by rw [←W.h1,←W.h2,←W.h3,←W.h4]; exact p.leanJ.1
    exact ((Tulip.axis_down _ _ (pT (by omega:aT ≤ n.val) (⟨J.P,hz⟩:BProof.Spin.Buyer V.f V.g V.F1 V.F2 n)) e x hd₂).drop (min_le_right ..)).books (le_max_right ..)
  have hzr : FountainSt prep:=by
    obtain ⟨α',t1,tY,t2,σp⟩:= Qw U W.pearl x ((min_le_right ..).trans (min_le_left ..)) tP
    refine ⟨Q₁,t1,α',(by linarith only [q₁]),t2,tY,?_⟩
    filter_upwards [eventually_ge_atTop (max mA U.roundZ)] with n hz m h J p' u ℓ
    have hp : J.P.toll V.f V.g V.F1 V.F2:=by rw [←W.h1,←W.h2,←W.h3,←W.h4]; exact p'.leanJ.1
    obtain ⟨Y,hY,_⟩:= σp (m:=m) (hz.trans h) J.P J.M hp u ℓ
    exact ⟨Y,hY⟩
  obtain ⟨Y,usable,parcels⟩:= Preparation.enroll_prepared (P:=prep) hy.2
  have αAttic : Attic prep:=by
     refine ⟨cut,fun x=>?_⟩
     obtain ⟨h₁,⟨eN,pN⟩,h₈⟩:= (g.and (eventually_ge_atTop x)).exists
     obtain ⟨n₁,Q,_⟩:= pN.exists
     obtain ⟨δz,c₁,L',Y,_,T',u,Z',Srv,_,K',_⟩:= Q.pays
     exact ⟨h₁,n₁,_,_,_,T',u,h₈,Q.permit.step,Srv,K'⟩
  refine ⟨prep,lΛ,V₀,Y,τ,(lt_of_lt_of_le (lt_add_one ε) (le_max_left ..)).trans ay,hd',⟨H₀,hβ⟩, (show Geometry prep from on_wheels Lπ (zero_le_one.trans w.permit.step) cut), αAttic,⟨⟨on_wheels Lπ (zero_le_one.trans w.permit.step) cut,on_spiced HΨ (zero_le_one.trans w.permit.step) cut,hv,hw,hC,Pay,kC,Γ,Tξ,hPay,hKc,hΓ,Dg,by change X K L Pay kC Γ Tξ ≤ R.L.val; omega,by change _<R.L.val; omega,by change _<R.L.val; omega,by change _≤R.L.val; omega,T,F,I,mo,A,C',z_v,K',Dp,hg,hA,hb,Γp,hS,tP,hI,color.1,ha⟩,
    ⟨⟨Pay,kC,Γ,Tξ,hPay,hKc,hΓ,Dg,by change TintRq K L Pay kC Γ Tξ ≤ R.L.val; omega,by change _<R.L.val; omega,by change _<R.L.val; omega,by change _≤R.L.val; omega,color.2⟩,hvz,hzr⟩,on_merits hΩ (zero_le_one.trans w.permit.step) cut,h8⟩,hy.2,usable,parcels,?_,?_⟩
  · intro i j
    apply YM.SU5.FiniteGaugeData.Audit1102.nimbusLaw lΛ _ ((Y.voyage i).craft j)
    intro V
    exact ((Y.voyage i).ownership j).paid.bill.comp (measurable_const.prodMk measurable_id)
  exact Y.corners id id strictMono_id strictMono_id
#print axioms jointLatchSt
end LocalLimit
end Rate
end YM.CF.Py
end
