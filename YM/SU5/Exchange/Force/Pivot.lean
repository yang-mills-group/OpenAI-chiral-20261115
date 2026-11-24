-- Extend SatinThinPayload.wax_mature with Amber.Lives (proof adapted from there)
import YM.SU5.Exchange.Force.Amber
import SatinThinAccrual
import SatinThinImpulse
import SatinThinKappa
import SatinThinBorn
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
include u0 HcP uΓ uL h0 hTc ptc QΔ b H0 he A₁ hx wq ΑΨ hΨ hφ
lemma wax_residence (Gs:Yo=0) : ∃ (Fz:Key J→Troupe S (r*radiusB x) (Words S)→ Aura (mid N B)→ Copy (mid N B))(Yb:Key J→ Pax (mid N B))(Kx:∀ z:Key J,Girt.BaseL U G (Yq z) G₀ G₁ q' kL)(Ωp:Key J→ Troupe S (r*radiusB x) (Words S)→ Aura (mid N B)→ Raid (LeanV (Single (mid N B)))), (∀ z∈hill J,Jade.GroV V F Z (X:=X) (Y:=Yq z) M P_ ht τ (Kx z) (Ωp z) (Fz z) h zv 1) ∧  let U0:=fun F:Cusp (mid N B)=> Sour.BondL.pivotS AA A₀ (w0.trans_le wv) h F hp huG hv' r1 w1 s1 hzG ij; let V0:=fun z:Mew.Key J=> U0 (cone_f (Fz z)); (∀ z∈hill J, ∀ Y:Aura (mid N B),∀ D⊆Y.val,Stax.Lives X.p (cipherK N0) Y D (V0 z Y D)) ∧ Yb=(fun z=>QuadClock.rust_P X.p (V0 z)- QuadClock.rust_P X.p (V0 0)) ∧ (∀ z∈hill J,QuadClock.Matures (mid N B) X.p U0 h (cone_f (Fz z))) ∧ (∀ z∈hill J, StageP V H (Yq z) X U) ∧ BornW (X:=X) (Y:=Y) (G₀:=G₀) (G₁:=G₁) (U:=U) (G:=G) (kL:=kL) (q':=q') (x:=x) V h Xo Yo Zo σ R' Kν Lt eW  KΦ V0 Fz Yb (Haro.riseV ij) v1 kF Dη (D+Dη) ∧ WakeS (X:=X) (Y:=Y) (G₀:=G₀) (G₁:=G₁) (U:=U) (G:=G) (kL:=kL) (q':=q') (x:=x) V h Xo Yo Zo σ R' Kν Lt eW Fz Yb (Haro.riseV ij) v1 kF Dη (D+Dη):=by
 have hv:=b.fee; have hk(t) := HcP.stem t; have hxφ:X.J.M=upMale R.L R.odd_side Y.J.M:=b.dose.grown
 have hV(T:Orbit (mid N B)):IsStarProjection (spar K.j X.J.M (G₀ T)):= (U.broadness _ K'.size _).projection _ ((A₀.paid T).shrink wq.le)
 obtain ⟨F_κ,Yφ,κ_Φ,KΓ⟩:= u0.owns
 obtain ⟨Kx,KX⟩:= Karma_H V F Z M τ K' P_ T' ht h Xo Yo Zo σ HcP F_κ Yφ κ_Φ -- order
 obtain ⟨Ω,Fz,QX,h0'⟩:= heroes_cap V h M τ P_ T' ht Xo Yo Zo Kx δ Hf Df uK hℓ kC vB D_ C' Xp₀ Jp Q₁ Q₂ Q₃ Vℓ ΑΨ (fun z _=> HcP.power z) Gs -- inspect
 let Fv(z):= Sour.BondL.pivotS AA A₀ (w0.trans_le wv) h (cone_f (Fz z)) hp huG hv' r1 w1 s1 hzG ij; let Yc(z):=FeeD X.p (nixV (Fv z)); let Yb(z):= Yc z-Yc 0
 rw [h0' _ _ KX] at KΓ; obtain ⟨Vx,Lρ,pN,pQ,pp,CΩ,Ts_⟩:= KΓ.body
 have pL(i)(u:i∈hill J):= (QX i u).2.1
 have hz:=fun i p=>(QX i p).2.2.1; have hZ:=fun i p=>(QX i p).2.2.2; have pA:=uL.worth
 have heR:=uΓ.ip; obtain ⟨E0,Hκ,Qw,hc,Pκ⟩:= primal_u_cap V Xo Yo Zo (fun i x=>(HcP.stem i|>.2.2 x).1) (fun i x=>(HcP.stem i|>.2.2 x).2) (fun i x=>(HcP.ear i).2 x) M Kx τ P_ ht Fz Ω pL hz hΨ hφ hZ hv (zero_le_one.trans hp) N0 N1 vS dS A₀ A₁ he wv wq w0 hx (fun i t=>(QX i t).1) σ (fun i=>(HcP.stem i).1) (fun i=>(HcP.stem i).2.1) (fun i=>(HcP.ear i).1) Yt Tq AA ij QΔ hzG huG hv' r1 w1 hp s1 h0 uΓ.pole uΓ.pin uΓ.note (hΨ.trans hφ) uΓ.carry heR.1 uΓ.cost.1 uΓ.cost.2.1 uΓ.cost.2.2 heR.2.1 heR.2.2 eW M0 KΦ R' Vx pN pA.1 pA.2 (by norm_num : 1/2<(1:ℝ)) uL.high.1 uL.high.2 pQ hxφ pp Ts_ hV hTc ptc uΓ.pay -- `he` shadow!!! check primal parameter unused Mum!!
 refine ⟨Fz,Yb,Kx,Ω,hz,?_⟩ -- let reduction
 dsimp only
 refine ⟨amber_radius V Xo Yo Zo (fun i x=>(HcP.stem i|>.2.2 x).1) (fun i x=>(HcP.stem i|>.2.2 x).2) (fun i x=>(HcP.ear i).2 x) M Kx τ P_ ht Fz Ω pL hz hΨ hφ hZ hv (zero_le_one.trans hp) N0 N1 vS dS A₀ A₁ he wv wq w0 hx (fun i t=>(QX i t).1) σ (fun i=>(HcP.stem i).1) (fun i=>(HcP.stem i).2.1) (fun i=>(HcP.ear i).1) Tq AA ij QΔ hzG huG hv' r1 w1 hp s1 h0 uΓ.pole uΓ.pin uΓ.note (hΨ.trans hφ) uΓ.carry heR.1 uΓ.cost.1 uΓ.cost.2.1 uΓ.cost.2.2 heR.2.1 heR.2.2 uΓ.pay,rfl,amber_mature V Xo Yo Zo (fun i x=>(HcP.stem i|>.2.2 x).1) (fun i x=>(HcP.stem i|>.2.2 x).2) (fun i x=>(HcP.ear i).2 x) M Kx τ P_ ht Fz Ω pL hz hΨ hφ hZ hv (zero_le_one.trans hp) N0 N1 vS dS A₀ A₁ he wv wq w0 hx (fun i t=>(QX i t).1) σ (fun i=>(HcP.stem i).1) (fun i=>(HcP.stem i).2.1) (fun i=>(HcP.ear i).1) Tq AA ij QΔ hzG huG hv' r1 w1 hp s1 h0 uΓ.pole uΓ.pin uΓ.note (hΨ.trans hφ) uΓ.carry heR.1 uΓ.cost.1 uΓ.cost.2.1 uΓ.cost.2.2 heR.2.1 heR.2.2 uΓ.pay,pL,?_,?_,E0,Qw,Hκ,?_,?_,?_⟩ -- order structures
 · constructor
   intro Q C u k pU pV v0 V' t q
   intro Ωk
   obtain ⟨s,w,r⟩:= Pκ Q C u k pU pV V' t q
   refine ⟨s,w,by unfold Ωk; rw [v0,add_zero]; exact CΩ.symm,fun i u=>⟨uL.gain ▸ (r i u).1,(r i u).2⟩⟩
 · unfold Yb; simp only [sub_self]
 · intro z u; obtain ⟨a,hU,p⟩:=hc z u; exact ⟨a,hU,fun v=> (p v).trans_eq uΓ.karma.1⟩
 · intro z u; obtain ⟨a,hU,p⟩:= hc z u; let A:=old_Q (Fz z)-old_Q (Fz 0); obtain ⟨p1,bk,q1,v,ηw,q₂,Λw⟩:= leaf_X_cap V Xo Yo Zo M Kx τ P_ ht Fz Ω pL hz hΨ hφ hZ hv (zero_le_one.trans hp) _ _ _ _ A₀ A₁ he wv wq w0 hx z u -- shadow
   have ht'(i):0 ≤ q1 i := (q₂ i).wage (zero_le_one.trans hp)
   exact ⟨q1+a,fun i=>by
       have h:Yb z i = A i+(Yb z i-A i):=(add_sub_cancel ..).symm
       rw [h]; exact (q₂ i).plus (hU i),fun i=>by rw [Larch.tall_add]; exact add_le_add ((tall_m q1 ht' (le_add_of_nonneg_right zero_le_one) i).trans ((Λw i).trans_eq uΓ.karma.2)) ((p i).trans_eq uΓ.karma.1)⟩ -- q0 synt
 intro Q C u k pU pV v0 V' t q
 obtain ⟨s,w,r⟩:= Pκ Q C u k pU pV V' t q
 refine ⟨fun z=> budgetR (roomV X.p (nixV (Fv z)) (Fv z) (KΦ+Q z)),s,w,by dsimp only; rw [v0,add_zero]; exact CΩ.symm,fun i u=>⟨uL.gain ▸ (r i u).1,(r i u).2⟩⟩
end YM.CF.Py
