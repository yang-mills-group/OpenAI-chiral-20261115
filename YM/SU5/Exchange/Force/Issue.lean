-- Adapt from SatinThinConsult
import YM.SU5.Exchange.Force.Jets
import YM.SU5.Exchange.Force.Pivot
import SatinThinMonarch
import SatinThinVow
import SatinThinPayload
import SatinThinImpact
import SatinThinMap
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
variable (F:Pilot)(Z:Pluck R)(I:Stake.Isle){σ v₀ v' hκ:ℝ}(Q:Pig.Tun I Z F σ){H:Muster G S x d T}{W:GivenX V U}{G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}{q q':Chi}
variable (b:StatV V G T U W X Y a γ w x p i)(M:Sheep V U W G Y.J X.J (i+2) p A) (τ:Fend V H M Z F q Y.p X.p γ a j l (r*radiusB x))(s:Sheet.isle M=I)(H0: StageP V H Y X U)(K':Girt.BaseL U G Y G₀ G₁ q' kL)
variable (N0 N1:ℕ)(A₀:Roof _ vS dS N0 G₀)(A₁:Roof _ vS dS N1 G₁)(he:N0+N1≤radiusB x)(hx:Stake.PondP V F x vS kL j l (i+2))(hu:kL<firstRadius SU.group)(w0:0< vS)(wv:vS ≤ dS)(wq:dS<d)
variable (htA:0 < A)
variable {b0:ℝ}(P_:∀ D:Support (Domain P B), Lend P B d D) (T':ℝ)(ht:Vista U Y.J.M Y.J.P P_ (i+2) M.q ((Fintype.card Play:ℝ)*T') M.lot M.tone)(zP: Oise.BoldB (T:=T) (k:=i) (H:=H) b0)
variable(D_: Corset d q' kL (i+2) p)
-- take common constants. Pee.B+= output p+4.Match after.Same stage calendar.K.No SO.
variable (h m0 mC C C' w' SC oμ ε δ Dμ kW:ℝ)(Xc:SkyC i C)(hM:1 ≤ m0)(ha:1 ≤ mC)(uS:ε>0)(Xp₀:SuitP i C')(Wol:0≤w')
variable {κ0:ℝ}(Jp:PactH d kL (Xp₀.C*(R.L.val:ℝ)⁻¹^2) κ0 q' (i+2) p D_)
variable {J_:ℕ}{zv:ℝ}
variable(hp:1≤h)(ph:1 < I.fine)(wK:5*Y.p.B+4≤10*radiusB x)(e':LocalRatio L)(jK:l ≤18)(βU:0< Y.beta)(rP:(j+110)*radiusB x+14≤r*radiusB x)(rQ: 2*((j+5)*radiusB x) ≤ r*radiusB x)
open Lilt Plume Vow Bake
open Prism Haro Oath
open Larch
variable (κ':Roc (mid P B)→ℝ)(Pp:∀ iκ:Roc (mid P B),PressB Y.p iκ.1 (actionZ Y iκ) h (κ' iκ)) (GG: Gala p i 100 x 3)
open Vow Bake Rue Larch
variable (pW:WindV K.j p)(pα:Tact G S Y h δ κ')(Nπ: BeaconP K.j Y S)
local notation "Λm"=> ((2:ℝ)^p*(16*δ)/h^2)
variable (ζ0:ℝ)(hvZ:0 < ζ0)(hZ:3*ζ0 ≤ M.r0)(uZ:ζ0 ≤1)
local notation "Cπ"=> (population*(A*followV [] R.L))
local notation "ρθ"=>way_Q R i p x δ Cπ ζ0 pW.C h
variable (Ωs HS Hf Df Lv Lp LK:ℝ)(Ap:Corona_Q (zv:=zv) V F Z M τ K' P_ T' ht D_ h C' δ Xp₀ Jp HS Hf Df Lv Lp LK)
local notation "XΨ"=> (pace_Z R Hf δ Df)
local notation "YP"=> pay_Z p (radiusB x) l i x h zv (XΨ) w
local notation "Kα"=> (rainX R 2 x)
open Ione
open Oise Sour Haro BondL Salt Nacre Nor
variable (Yt:Monk SU.group S)
local notation "Pv"=> (↑(Next.Fluctuations.Sector.prefactor S SU.group Y.beta):ℂ) * (↑((shotM L (F.hat R x) Y.beta)^Fintype.card Yt.park.Free):ℂ) * pulseZ (T:=T) (x:=x) (U:=U) (H₀:=Y) (G:=G) (H₁:=X) Yt

open Neon Mew Vow Tap Rive Bake
open scoped YM.CF.Mew
local notation "BN"=> mid N B
local notation "BP"=> mid P B
local notation "AΨ"=> Aura BN
local notation "sA"=> (X.p.supportExponent+1+1)
local notation "ζK"=> X.p.supportExponent+(1:ℝ)/2
variable {pψ:Hh=1}{zP' z0 z1 D γ0 Γ Dη μ b₃ kC:ℝ}{zΨ:ℝ}
variable {J:Type}[LinearOrder J][Fintype J]
variable (Xo Yo:Key J→ RegBudget (mid P B))(Zo:Key J→ForceBudget (mid P B)) (σ:J→ Site (Domain P B))
variable (Tx:Scree.Loom (mid N B))
local notation "Yq" v:max=> color_b Y Y.beta (Xo v) (Yo v) (Zo v) Y.v
variable (Q₁ Q₂ Q₃ Vℓ:ℝ) {cQ vL uK hℓ vB Hf':ℝ}{dM M0 κ v1 kF WΨ :ℝ} (HcP: Call_H (Y:=Y) h Xo Yo Zo σ Q₁ Q₂ Q₃)(ΑΨ:Span_H_cap (X:=X) (Y:=Y) (G₀:=G₀) (G₁:=G₁) (J_:=J_) (cQ:=cQ) (vL:=vL) (zv:=zv) V h M τ P_ T' ht D_ C' Xp₀ Jp δ Hf Df uK hℓ kC vB Vℓ Q₁ Q₂ Q₃)
variable {bb ba bc d₃:ℝ}(uΓ:κPass X.p ba bb bc d₃ (rainX R 1 x) zv (rainX R 2 x) h Γ μ Dη D)(uL:κLast X.p Γ κ M0 v1 (rainX R 2 x) ((rainX R 2 x)⁻¹* μ) kF)
local notation "PX"=> X.p
local notation "ζν"=> (rainX R 1 x)
variable {r_:ℝ} (ij:Haro.ΘS r_) [Nonempty (ΘS r_)] (Tq:QuotaH V.f V.g V.F1 V.F2) (AA:Sour.BondL (tatE V Tq (mid N B)) (tagE V Tq (mid N B)) (body_Q (N:=mid N B) r_) bb bc ba dS)
variable(QΔ:TagT (tatE V Tq (mid N B)) (tagE V Tq (mid N B)) (body_Q (N:=mid N B) r_) dS)(hTc:Tq.2=X.J.M)(ptc:(Tq.1 _).val=X.J.P)
variable(h0:0< ba)(hzG: HopeT dS z0 z1 X.p.order)(huG:X.p.threshold≤ z1)(hv':X.p.threshold ≤ vS)(r1:N0+10≤ X.p.B)(w1:cipherK N0≤ 5*X.p.B)(s1:3 ≤ X.p.B)(hΨ:1≤rainX R 1 x)(hφ:rainX R 1 x≤rainX R 2 x)
variable (R':RegBudget (mid N B))(Kν:ForceBudget (mid N B))(Lt:ℝ)(eW:ℂ)
variable (KΦ:Cusp (mid N B))(u0: κBend_n (X:=X) (Y:=Y) V F Z M τ K' N0 A₀ w0 wv P_ T' ht h hp Yt ij Tq ba bb bc AA hzG huG hv' r1 w1 s1 R' Kν M0 Lt eW zv KΦ)
local notation "ΛR"=> (Haro.riseV ij)
variable (Fz:Key J→ Troupe S (r*radiusB x) (Words S)→ Aura (mid N B)→ Copy (mid N B))
open Moto Prism Hove Taxi
variable(Pc:BudgetPoint)(D_φ:ℝ)(DG:DayT i D_φ)(hφv:0≤D_φ)(uφ:Even K.j)(vφ:4≤ K.j)
variable (qP:2≤p)(Zt Kc:ℝ)(Tρ:Hove.Grant K.j p){cΦ:ℝ}(ωh:Warm_K R.L i p l K.j Tρ ζ0 (population*(A*followV [] R.L)) Pc cΦ x D_φ)(pΦ:TimΞ R.L i p l x hℓ uK Pc)(gΦ: Pc.supportExponent=w) (g':Pc.order=i)(Wφv:Pc.power=p)(Wκ Fχ:ℝ)(uc:0 ≤ Wκ)(q0:0 ≤Fχ)(qs: Hf ≤ Fχ*(R.L.val:ℝ)⁻¹^5)(vC:0≤Hf)(hΨv:0 ≤ kC)(δQ: Df≤Wκ)(pQ0:100*(1+radiusB x)≤(Domain N B).val)(h_μ: vB≤Wκ) (PA:Tune.OakenP R K S T)
variable (hpμ:10≤X.p.B)(lvμ:10≤ Y.p.B)(pv:(Neon.KX l)^3< R.L.val)(sK:(PKard l)^3< R.L.val)(Lpκ:1<R.L.val)(htδ:2*(R.L.val^2)<(mid N B).val)(h0':20<(Domain P B).val)(r0':20<(Domain N B).val)(v0': 3≤ (mid N B).val) -- period
variable(Kx:∀ z:Key J,Girt.BaseL U G (color_b Y Y.beta (Xo z) (Yo z) (Zo z) Y.v) G₀ G₁ q' kL)(Ωp:Key J→ Troupe S (r*radiusB x) (Words S)→ Aura (mid N B)→ Raid (LeanV (Single (mid N B))))(Mp:∀ z∈hill J,Jade.GroV V F Z (X:=X) (Y:=color_b Y Y.beta (Xo z) (Yo z) (Zo z) Y.v) M P_ ht τ (Kx z) (Ωp z) (Fz z) h zv 1)
variable (Yb:Key J→ Pax (mid N B))(Wξ:Op SU.Slot)(Wy:WakeS (X:=X) (Y:=Y) (G₀:=G₀) (G₁:=G₁) (U:=U) (G:=G) (kL:=kL) (q':=q') (x:=x) V h Xo Yo Zo σ R' Kν Lt eW Fz Yb Wξ v1 kF Dη (D+Dη))
variable(P0:IncX primeU Y.F Y.p h 1)
open Lattice Siete PhysicalNext.JointLoad Heir Tap Tune Rue
-- use script.Stat.Area exp global as local cost bound. Output estimator summaries.BeforeYear.
local notation "TT" t:max=> κprobe t R.L
local notation "sKΦ"=> (tintW Pc Pc i p l K.j Tρ Fχ kC D_φ)
local notation "uXΦ"=> uXv Pc Pc i p K.j Tρ Fχ D_φ
local notation "uYΦ"=> uYv Pc Pc p K.j Tρ Fχ D_φ
local notation "uZΦ"=> loon (Fχ*Sauce Pc D_φ)
local notation "Ltz"=> R.L.val
variable (σP:J→ Site (mid N B))
variable (Sx:σ=Cube.node ∘ Hove.heel G ∘ σP)
local notation "T'σ"=> Hove.heel G ∘ σP
variable (Q:J→ℝ)(LΩ:J→ ArcΦ)
local notation "Kφ"=> fundK p i l zv h w x (Hf*((R.L.val:ℝ)^4)*δ+Df)
-- measured sigma budgets, actual first derivatives. E1 canonical. λΨ,χ. SEAM.Path rank support.
local notation "Wπ"=> nun_ω Y.F
variable (pΘ:∀ j:J,Axon R.L.val (Hove.heel G (σP j)) Y.p (νTip Xo j) h (Q j) (LΩ j))
variable (eΘ:∀ j:J,νTip Yo j=0)(uΘ:∀ j:J,Q j≤cΦ)(p_:Sauce Pc D_φ * cΦ ≤ δ)(he1:Sauce Pc D_φ*cΦ ≤ Q₁)(he2:0≤Q₂)(he3:0≤ Q₃)(heL:reserveT X.p.power X.p.order X.p.B 2 *Dη ≤Wκ)(Tp: Ids (mid N B))
local notation "Tv"=> theory_e R.L Pc D_φ sKΦ cΦ Wκ Kφ
local notation "Wφ"=> (nun_ω Y.F)
variable {Ys:GramM (mid N B)}
-- Projection Core: internal.Wx and Cox drift. Assumes normalized Grams. Need polynomial CalB later.W.Shape. VQ all root Board. Outputs paid Stamp Envelopes with exponent excess and attainable cutoff energies.
local notation "νo"=> R.L.val
variable (nν:ℕ)(Fv: Neon.GapN σP X.p.B R.L.val nν) -- use fully qualified
variable (μFa: ↑nν * theory_e R.L Pc D_φ (tintW Pc Pc i p l K.j Tρ Fχ kC D_φ) cΦ Wκ (fundK p i l zv h w x (Hf*((R.L.val:ℝ)^4)*δ+Df))≤ v1)
variable (ρQ:∀ j,Sized_J (Q j) cΦ (nun_ω Y.F (Hove.heel G (σP j))) h (LΩ j))
local notation "QO"=> (reserveT X.p.power X.p.order X.p.B 1*(D+Dη))
-- state Agency. step.None sym-critical.Center chart. all receipts per accepted parameter family. quantitative basis. V1 mask. Can strengthen for NONnurturing boot.Cap.Weight.QP.Motion.
variable {κΦ f_ a_ g_ :ℝ}(fc:f_ ≤ Q₁)(gc:f_ ≤ Q₂)(kc:f_ ≤ Q₃)
variable (ηp:Ann_S X.p Pc R nν p i l x cΦ D_φ Hf h (tintW Pc Pc i p l K.j Tρ Fχ kC D_φ) ba bb bc zv Df δ kF v1 M0 κΦ Wκ)(Lk: vB= Df)
open QuadClock
section
local notation "setStep" E:max F:max => color_b Y Y.beta E 0 F Y.v
include he A₁ wq wv w0 hx K'
noncomputable def launchpad : QuadClock.Observatory G X.p where
 source := trueBeat (S:=S) (G₀:=G₀) (G₁:=G₁) (Y:=Y) (X:=X) (q':=q') (zv:=zv) (kL:=kL) V F Z M τ N0 A₀ w0 wv P_ T' ht h hp ij Tq AA hzG huG hv' r1 w1 s1 -- tune zv missing, kL hidden in K' binder implicit. check
 flies s E0 E1 K0 K1 v w A B' t u:=by
    obtain ⟨a,B0,W,Z0,z,m,rfl⟩:=A; obtain ⟨a',B1,W',Z1,z',m',rfl⟩:=B'
    apply Matures.paid _ m m' hp
    let Δt:=reSweep G s; have hh: RelativePant Δt (setStep E0 K0) (setStep E1 K1):= ⟨t,fun _ _=> (map_zero _).symm,fun i t V p=>u i (V,t) p⟩
    exact fun i V' c D q=>rel_cone (Y:=setStep E0 K0) V F Z M τ a B0 N0 N1 A₀ A₁ he hx w0 wv wq P_ T' ht h z s V' i E1 0 K1 B1 a' Z1 W' z' hh D c

end
include fc gc kc Lk ηp PA hΨv pΦ hpμ lvμ pQ0 h0' r0' v0' htδ p_ he1 he2 he3 K' ωh ΑΨ u0 QΔ hTc ptc P0 hp htA b wq w0 wv H0 hx h0 A₀ A₁ he vC hvZ hZ uZ pv sK Lpκ qs q0 qP DG hφv gΦ g' Wφv uφ vφ hΨ hφ
open QuadClock
lemma classroom (Vh:HavenL (mid N B) X.p R.L.val) (Ha:ZealQ KΦ) (HhY: ∀ s∈cycleSweep (mid P B),passingR (mid P B) s Y.F Y.F) (HHF:∀ s∈cycleSweep (mid P B),passingF (mid P B) s Y.K Y.K)(nc:ℕ)(hc: (nc:ℝ)*strive_E X.p.order ≤ (nν:ℝ)) : ∃ (Be:Observatory G (spark_B X R' Kν Lt eW).p)(Ca:ArcΦ→ℝ→ℝ), OrbitJet V U G S G₀ G₁ (spark_B X R' Kν Lt eW) Y (Haro.riseV ij) q' kL h v1 kF Wκ (Δv Pc D_φ*sKΦ) (tintW Pc Pc i p l K.j Tρ Fχ kC D_φ) uZΦ uXΦ uYΦ f_ cΦ κΦ Be KΦ Ca (cipherK N0) nc:=by
 obtain ⟨κ₀,ακ,bκ⟩:=vow_life Y h P0 hp HhY
 -- Core registry for this Shop
 obtain ⟨Φ,qk,μ,Uq,Dη,kp,KP,KL,hd,u,p_l,y,Γv⟩:=ηp.core
 let Be:= launchpad (X:=X) (Y:=Y) (zv:=zv) (G:=G) (q':=q') V F Z M τ N0 N1 A₀ A₁ he hx w0 wv wq P_ T' ht h hp ij Tq AA hzG huG hv' r1 w1 s1
 let D:= fun a u=> Extr_h R.L.val Pc D_φ*(sKΦ*κprobe mintR R.L h u Wκ (κ₀:ℂ) a)+Kφ
 have wQ: Odd G.count.val:= b.hunt.bill.symm ▸ R.odd_side
 refine ⟨Be,D,?_⟩
 constructor; exact Ha
 intro J _ _ σP Fp Zp vG Qv Hw
 let Ψ:=vG; let gp:=Hw.quorum; let Hv:=Hw.buy; let σp:= (Cube.node ∘ Hove.heel G ∘ σP); let pS:=Hw.talk; have et(i:J): νTip (0: Mew.Key J→RegBudget (mid P B)) i=0:= funext₂ fun x y=> Mew.tip_0 [i] -- tune
 let Fv:=Call_H.raiseK _ _ _ _ _ _ _ _ fc gc kc Hv
 obtain ⟨Fz,Yb,Kx,Ω,Mp,PX',s',t',Lx,Bw,Wy⟩:= wax_residence V F Z b M τ H0 K' N0 N1 A₀ A₁ he hx w0 wv wq P_ T' ht D_ h C' δ Xp₀ Jp hp Hf Df Yt Fp (0:Key J→RegBudget (mid P B)) Zp σp Q₁ Q₂ Q₃ Vℓ Fv ΑΨ KP KL ij Tq AA QΔ hTc ptc h0 hzG huG hv' r1 w1 s1 hΨ hφ R' Kν Lt eW KΦ u0 rfl
 let V0 := fun z:Key J=> Sour.BondL.pivotS AA A₀ (w0.trans_le wv) h (cone_f (Fz z)) hp huG hv' r1 w1 s1 hzG ij
 change Yb=heat_P X.p V0 at s'; subst Yb; let Yb:=heat_P X.p V0
 rw [←b.down.hK,←b.down.order] at p_l y; rw [gΦ] at Γv
 let Yp:=fun j=>(Hw.cost j).pay.2; refine ⟨V0,fun z l=>?_,Wy.crop,fun j=>?_ ,?_⟩
 · exact ⟨Lx z l,Kx z,Fz z,Ω z,Mp z l,t' z l,rfl⟩
 · intro k Rq; let Tp: Ids (mid N B):= Classical.arbitrary _
   obtain ⟨G',Kζ,p,l,w,v⟩:=Wz_E_cap V F Z b M τ K' N0 N1 A₀ A₁ he hx w0 wv wq htA P_ T' ht D_ h C' δ Xp₀ Jp hp ζ0 hvZ hZ uZ Hf Df Fp (0:Key J→RegBudget (mid P B)) Zp σp Q₁ Q₂ Q₃ Vℓ Fv ΑΨ R' Kν Lt eW Fz Pc D_φ DG hφv uφ vφ qP Tρ ωh pΦ gΦ g' Wφv Wκ Fχ u q0 qs vC hΨv hd pQ0 (Lk.trans_le hd) PA hpμ lvμ pv sK Lpκ htδ h0' r0' v0' Kx Ω Mp Yb _ Wy P0 σP rfl Qv Ψ pS et Yp p_ he1 he2 he3 p_l Tp rfl j
   have hv:nun_ω Y.F (Hove.heel G (σP j))=k:=rfl
   unfold D; rw [←ακ (Hove.heel G (σP j)), mul_assoc (Δv Pc D_φ)]; exact ⟨G',Kζ,p,l,w,v⟩
 have uv:(nc:ℝ)*(strive_E X.p.order*Tv)≤v1:=(by rw [← mul_assoc]; exact (mul_le_mul_of_nonneg_right hc (yφ_age ..)).trans Γv) -- Tv uses notation dims captured include?
 intro E_ Gk Κ δX A2 K_ν; rw [← y]; obtain ⟨Q,ξP,κB⟩ := mora_billet V F Z b M τ K' N0 N1 A₀ A₁ he hx w0 wv wq htA P_ T' ht D_ h C' δ Xp₀ Jp hp ζ0 hvZ hZ uZ Hf Df Fp (0:Key J→RegBudget (mid P B)) Zp σp Q₁ Q₂ Q₃ Vℓ Fv ΑΨ R' Kν Lt eW Fz Pc D_φ DG hφv uφ vφ qP Tρ ωh pΦ gΦ g' Wφv Wκ Fχ u q0 qs vC hΨv hd pQ0 (Lk.trans_le hd) PA hpμ lvμ pv sK Lpκ htδ h0' r0' v0' Kx Ω Mp Yb _ Wy P0 σP rfl Qv Ψ pS et p_ he1 he2 he3 p_l (Classical.arbitrary _) nc Hw.quorum uv Hw.cost rfl KΦ V0 Bw E_ Gk Κ δX (fun b' => by
    intro Wt TΩ
    specialize A2 b'; dsimp only at A2; unfold D at A2; rw [←ακ (Hove.heel G (σP b')), mul_assoc (Δv Pc D_φ)] at A2; exact A2)
 refine ⟨Q,ξP,fun z p=> ?_,κB⟩
 · change FlagWidth X.p _ (cipherK N0); apply glowWidth _ (V0 z) _; exact PX' _ p -- tune
end YM.CF.Py
