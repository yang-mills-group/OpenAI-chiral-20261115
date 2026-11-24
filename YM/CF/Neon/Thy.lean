import YM.CF.Neon.Price
import YM.CF.Neon.World
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Neon
open Py
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
open Moto
open Vow Lilt Larch Bake Rue
open Prism Hove Oise
-- primary picture: rank 0 pressure (global scalar extracted separately), 3 PH weight and 4 derivatives, 4 radial. representation.H.
local notation "Yκ"=> mid P B
local notation "Xκ"=> mid N B
local notation "Ωp"=> RegBudget (mid P B)
local notation "θp"=> (Y.p)
local notation "HF"=> Scree.Hub (mid P B)
local notation "Пρ"=> S.patch.L.val
local notation "Pr"=> Roc (mid P B)
open Taxi Hope
variable (o: Site (mid P B))(E1:RegBudget (mid P B))(OG:RegBudget (mid P B))(X0:Dome)(Aζ:Skate)(Q:ℝ)(h:ℝ)
local notation "Δo"=> Cube.node o
local notation "ZK"=> Φrap Yκ o 10
local notation "C_"=> (ZK)
local notation "κr"=> ((ZK,true):Roc Yκ)
local notation "Vζ"=> G_κ θp o OG E1
local notation "EΛ"=> θG (Y:=Y) o OG Aζ
local notation "ZΛ"=> vRΦ (Y:=Y) o OG Aζ
local notation "ZΩ"=> vRψ (Y:=Y) o E1 OG Aζ
local notation "νv"=> ωX (OG ZK)
local notation "V_o"=> ((↑Y.p.order:ℝ)+1)
local notation "PhZ" z:max=> (Moto.hrζ θp z 1)
local notation "PhA:" z:max=> (Moto.trotΦ θp z A)
local notation "Φp" x:max=> (Moto.rotζ θp x)
variable (A) (hu:A≥0) (wQ:Taxi.DayT Y.p.order A)
variable (Fκ Gκ: Scree.Hub (mid P B)→ℝ)
local notation "Ων"=> Ψy o θp · Fκ A
local notation "fκ" x:max=> (Ψy o θp x Fκ A)
variable (hx:∀ i,PressB Y.p i (E1 i) h (Fκ i)) (h0:1 ≤ h)(hv: IncX primeU OG Y.p h 1)(hK:∀ i,CapZ Y.p (Fκ i) A)(zP:20 < (More (mid P B)).val) (u0:Short S Y.p (Φrap (mid P B) o 10).val.2)
variable (Vq:Axon S.patch.L.val o Y.p E1 h Q (Aζ,X0))
local notation "Pu"=> (Sauce θp A)
variable (pZ:∀ v:Site (Domain P B),(∑ i:Scree.Hub (mid P B), if v=i.val.1 then Y.p.mass i.val.2 (Fκ i) else 0)≤ Q)
local notation "TT"=> (Pu*Q)
local notation "PE" i:max=> (eno_b Y i)
local notation "cΨr"=> (PE ZΩ)
local notation "cΦr"=> (PE ZΛ)
open Mew Rive
variable{Hp:ℕ}{q q':Chi}{R0 a0 cQ vL zv:ℝ}{F:Pilot}{Z:Pluck R}{H:Muster G S x d T}{J_:ℕ}{W:GivenX V U}
variable (M:Sheep V U W G Y.J X.J (k+2) p R0)
variable (τ:Fend V H M Z F q Y.p X.p γ a0 j l (r*radiusB x))(P_:∀ D:Support (Domain P B), Lend P B d D)(K₀:ℝ)(w_:Vista U Y.J.M Y.J.P P_ (k+2) M.q ((Fintype.card Play:ℝ)*K₀) M.lot M.tone)
variable {Λ:Type}[LinearOrder Λ][Fintype Λ]
variable (Fp Gp:Mew.Key Λ→ RegBudget (mid P B))(Zp:Mew.Key Λ→ ForceBudget (mid P B))
local notation "ξ"=> Key Λ
variable(hX:∀ i w,River (fun z:Key Λ=>Fp z i w))(hY:∀ i w,River (fun z:Key Λ=>Gp z i w))(hZ:∀ i w,River (fun z:Key Λ=>Zp z i w))
variable (pL:Fp 0=OG)(j0:Λ)(vT:∀ i w, tipI (fun z:Key Λ=> Fp z i w) [j0]= E1 i w)(oT:∀ i w, tipI (fun z:Key Λ=> Gp z i w) [j0]=0)
variable {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}
variable (Kx:∀ z:Key Λ,Girt.BaseL U G (Oise.color_b Y Y.beta (Fp z) (Gp z) (Zp z) Y.v) G₀ G₁ q' kL)(KL:Girt.BaseL U G (eno_b Y (vRΦ (Y:=Y) o OG Aζ)) G₀ G₁ q' kL)(Ks:Girt.BaseL U G (eno_b Y (vRψ (Y:=Y) o E1 OG Aζ)) G₀ G₁ q' kL)
local notation "Ωq" z:max=> Oise.color_b Y Y.beta (Fp z) (Gp z) (Zp z) Y.v
local notation "φp"=> Stilo.beamH
local notation "Ωτ"=> Troupe S (r*radiusB x) (Words S)
variable (F_κ:Key Λ→Troupe S (r*radiusB x) (Words S)→ Aura (mid N B)→ Copy (mid N B))(F_l:Troupe S (r*radiusB x) (Words S)→ Aura (mid N B)→ Copy (mid N B))(F_k:Troupe S (r*radiusB x) (Words S)→ Aura (mid N B)→ Copy (mid N B))
variable (Mp: Key Λ→ Troupe S (r*radiusB x) (Words S)→ Palot.leaf (Site (Domain N B))→ Raid (LeanV (Single (mid N B))))(Vs:(Troupe S (r*radiusB x) (Words S)→ Palot.leaf (Site (Domain N B))→ Raid (LeanV (Single (mid N B)))))(Vl:(Troupe S (r*radiusB x) (Words S)→ Palot.leaf (Site (Domain N B))→ Raid (LeanV (Single (mid N B)))))
variable (hfκ:∀ z∈hill Λ,Jade.GroV (X:=X) (Y:=Oise.color_b Y Y.beta (Fp z) (Gp z) (Zp z) Y.v) V F Z M P_ w_ τ (Kx z) (Mp z) (F_κ z) h zv 1)(hfφ:Jade.GroV V F Z (X:=X) (Y:=eno_b Y (vRΦ (Y:=Y) o OG Aζ)) M P_ w_ τ KL Vl F_l h zv 1)(hfk:Jade.GroV V F Z (X:=X) (Y:=eno_b Y (vRψ (Y:=Y) o E1 OG Aζ)) M P_ w_ τ Ks Vs F_k h zv 1)
variable (Hx:∀ i∈hill Λ,LookZ V (Xm:=X) (Xu:=Oise.color_b Y Y.beta (Fp i) (Gp i) (Zp i) Y.v) M τ (Kx i) P_ w_ J_ cQ vL)(HΦ:LookZ V (Xm:=X) (Xu:=eno_b Y (vRΦ (Y:=Y) o OG Aζ)) M τ KL P_ w_ J_ cQ vL)(Hψ:LookZ V (Xm:=X) (Xu:=eno_b Y (vRψ (Y:=Y) o E1 OG Aζ)) M τ Ks P_ w_ J_ cQ vL)
local notation "μp"=> (subtK (r:=r*radiusB x) S κr)
local notation "Lψ"=> (old_Q F_k)
local notation "T'l"=> Trough
variable (X_:Aura (mid N B))(Vz: Orbit (mid N B))
local notation "Kρ"=> (subtK (r:=r*radiusB x) S)
variable (N0 N1:ℕ)(A₀:Roof _ vS dS N0 G₀)(A₁:Roof _ vS dS N1 G₁)(he:N0+N1≤radiusB x)(htP:Stake.PondP V F x vS kL j l (k+2))(wp:0<vS)(wu:vS ≤ dS)(wq:dS<d)
variable (D_:Corset d q' kL (k+2) p)(C':ℝ)(Xp₀:SuitP k C'){κ₀:ℝ}(Jp:PactH d kL (Xp₀.C*(R.L.val:ℝ)⁻¹^2) κ₀ q' (k+2) p D_)
variable (Q_:Rill.Arch G d)(hp:Q_.val=1)
local notation "OpQ"=> (OPx (x:=x) (S:=S) (X:=X) (Y:=eno_b Y ZΩ) V M D_ Q_ C' Xp₀ Jp)
local notation "KT"=> FaceP (Y:=Y) A o Fκ
variable (b:StatV V G T U W X (eno_b Y (vRψ (Y:=Y) o E1 OG Aζ)) a0 γ w x p k)(Q0:StageP V H (eno_b Y (vRψ (Y:=Y) o E1 OG Aζ)) X U)(V0:ℝ)
variable (o':Site (mid N B))(to_:heel G o'=o)
local notation "Lν"=> PactH
variable (Φs:Hove.Grant K.j p)(ζ0:ℝ)(uζ:0 < ζ0)(hpζ:3*ζ0≤ M.r0)(hxζ:ζ0 ≤1)(p0:Even K.j)(hk':4≤ K.j)(pA:2≤ p)(n0:ℕ)(hδ: 2*n0 < (mid N B).val)(w0:0< R0)
local notation "Cm"=> (population*(R0*followV [] R.L))
open Tap
local notation "Yν"=> (StackL (clan_X true (PE ZΩ)) (dawn_D S Y.p))
local notation "Ψw"=> (ωX (OG (Φrap Yκ o 10)))
local notation "ϕx"=> (‖Ψw‖*‖X0.1‖)
local notation "ϕy"=> (‖Ψw‖*‖X0.2‖+ δK0 *ϕx)
local notation "Tu"=> (1+(n0:ℝ))
local notation "TkΨ"=> (paid_M o (Yν) p)
local notation "Пc"=> (pace_Z R)
local notation "Δpκ"=> (2*((2:ℝ)^p*mintY p (a:=ζ0) (C:=Cm) (radiusB x)*mintY p (a:=ζ0) (C:=Cm) 0)+ Φs.A/(R.L.val:ℝ)^5)
local notation "ζl"=> (lace 0 R.L)
local notation "ζp"=> (lace 1 R.L)
local notation "Jψ"=> (Φs.F*(ζl^2*ϕx + 8*(ζl*ζp)*ϕy))
local notation "Gz"=> (Φs.C+‖baseF false‖+‖baseF true‖+1)
local notation "K₀'"=> (Gz^2*(ζl^2 *ϕx))
local notation "H₀'"=> (Gz^2*(ζl*ζp*ϕy)/Tu)
local notation "E₀'"=> (κP p*Δpκ*TkΨ)
local notation "PΨ"=> (Hove.jetsL o' (OpQ true))
local notation "ζν"=> ((ζl:ℂ)*(ζp:ℂ))
-- Galaxy B.alignP.Exp. already Archer. emission Φ separately.
local notation "Л"=> (hostX (l:=((H.post+90)*radiusB x)) S κr)
variable (Vκ:ℝ)(Ψ: DayT X.p.order Vκ)(uc:0 ≤ Vκ)
variable (Υ:Gala p k 100 x 3)(Υ':Gala p k (16*(l+300)) x 3)(hμ:10 ≤ X.p.B)(he':1 ≤ radiusB x)(hN:20 < (More (mid N B)).val)(hP:3 ≤ (mid N B).val)
variable (Hf Fd:ℝ)(Tp:Ids (mid N B))(hQ0:Sauce Y.p A*Q ≤ V0)(pQ0:100*(1+radiusB x)≤(Domain N B).val)
variable (Λk:KnotX (Xs:=X) (Y:=eno_b Y (vRψ (Y:=Y) o E1 OG Aζ)) H Tp h V0 (FaceP (Y:=Y) A o Fκ) (fun i B=> F_k (subtK S i) B) (fun i v O=> vanX (Xs:=X) (Y:=eno_b Y (vRψ (Y:=Y) o E1 OG Aζ)) (M:=M) V D_ U W H i Jp Q_ v O) Hf Fd)
local notation "Lκ"=> (S.patch.L.val)
local notation "Dκ"=> (Hf*(S.patch.L.val:ℝ)^4*V0+Fd)
local notation "П"=> (∑ i:Roc (mid P B) with S.ratio.parent i.1.val.1=node o', Y.p.mass i.1.val.2 (KT i))
local notation "DF"=> (Hf*П+Fd)
local notation "WC"=> (miteV X.p.B X.p.order X.p.power 1 zv)
local notation "Λy"=> (Real.exp (X.p.supportExponent*(PKard l:ℝ))*(deck_K k p (10*(l+300))*(Oath.stakeH k*h^2*Hove.paid_M o' (OpQ true) p)))
local notation "Kψ"=> (GvC k h WC Dκ (Larch.ball_v (cirQ x):ℝ))
local notation "KP"=> (Real.exp ((X.p.supportExponent+1+1)*(PKard l:ℝ))*Kψ)
local notation "ΚρK"=> Extr_h Lκ X.p Vκ
local notation "AY"=> ((DF)+(Λy))
open Tune
variable (uK hℓ kC vB:ℝ)(GA: Blush_X V F Z (X:=X) (Y:=eno_b Y (vRΦ (Y:=Y) o OG Aζ)) M τ KL P_ K₀ w_ h kC hℓ uK vB)(PA:OakenP R K S T)(Bg: StageP V H (eno_b Y (vRΦ (Y:=Y) o OG Aζ)) X U)
local notation "ΦAg"=> (Ψw • Aζ)
local notation "wG"=> (‖Ψw • Aζ‖)
local notation "zM"=> ((qCorset X.p.threshold Y.p.threshold (R.L.val:ℝ)))
local notation "Ppκ"=> (F_l μp)
local notation "ζΦ"=> (kC*((R.L.val:ℝ)⁻¹)^4 * Moto.trotΦ Y.p wG A)
local notation "Ωz"=> (l_fee (Fintype.card (PlaqAxes×PlaqAxes)) Y.p X.p hℓ wG + uK*KX l * (‖(↑(zM):ℂ)‖*wG))
local notation "ΛZ"=> (Real.exp (X.p.supportExponent*(KX l:ℝ))*ζΦ+vB)
variable (S_P:Λ→Site (Domain P B)) (Lp:∀ i:Scree.Hub (mid P B),Hush S_P i.val.2 fun z=>Fp z i)(Lv:∀ i:Scree.Hub (mid P B),Hush S_P i.val.2 fun z=>Gp z i)(LZ:∀ i:Force (mid P B),Hush S_P i.val.1.val.2 fun z=>Zp z i)
variable (L0:∀ i∈hill Λ, StageP V H (Oise.color_b Y Y.beta (Fp i) (Gp i) (Zp i) Y.v) X U)
local notation "PP"=> X.p
local notation "Lτ"=> S.ratio.parent ∘ S_P
variable (Yb:Key Λ→ Pax (mid N B))(hpY:∀ z∈hill Λ,Turf (Yb z))(uY: ∀ i:Aura (mid N B),∀ v:Orbit (mid N B),River fun z=>Yb z i v)(eY:∀ i:Aura (mid N B),Hush (S.ratio.parent ∘ S_P) i.val (fun z=>Yb z i))
variable (dP:ℝ)(ρF:∀ z∈hill Λ,∃ C:Aura (mid N B)→ℝ,(∀ i:Aura (mid N B),Medal X.p i.val ∅ (εS F_κ Yb z i) h (C i))∧∀ i:Seat (mid N B), tallB C X.p.B (X.p.supportExponent+1+1) i ≤ dP)
local notation "Pμ"=> (reserveT X.p.power X.p.order X.p.B 2*dP)
local notation "Tσ"=> (εS F_κ Yb)
local notation "Pc_"=> (Yp) -- junk
local notation "Ωκ_t"=> (ΛZ+(AY)+Pμ)
local notation "Ωω"=> (κP p)
local notation "Φt"=> ((↑(zM):ℂ) • ΦAg)
local notation "Tκ'"=> (2*peka_H X.p.power *(vB+DF+Pμ))
local notation "Zη"=> (↑(ζl):ℂ)^2 • (Ψw • X0.1)
local notation "Ζτ"=> ζν • (Ψw • X0.2)
local notation "Ετ"=> (E₀'+(2*K₀'/Tu+8*H₀'))
local notation "Εp"=> (pruneQ*(E₀'+(K₀'+12*H₀')))
local notation "Hκ"=> coldE PP (τι Yb [j0])
variable (hk:0 ≤ kC)(pv:(KX l)^3< S.patch.L.val)(sK:(PKard l)^3 < S.patch.L.val)(pU:S.ratio.parent (S_P j0) = Cube.node o')
variable (Wκ Fχ Kp:ℝ)(wM:0≤Wκ)(wqL:0≤ Fχ)(wKc:Hf ≤ Fχ*(R.L.val:ℝ)⁻¹^5)(hF:0 ≤ Hf)(htD:2*((2:ℝ)^p*Haro.mintY p (a:=ζ0) (C:=population*(R0*followV [] R.L)) (radiusB x)*Haro.mintY p (a:=ζ0) (C:=population*(R0*followV [] R.L)) 0)+ Φs.A/(R.L.val:ℝ)^5 ≤ (Φs.A+2)*((R.L.val:ℝ)⁻¹)^5)(hmZ:vB≤ Wκ)(hDf:Fd≤ Wκ)(hpρ:Nor.reserveT X.p.power X.p.order X.p.B 2*dP ≤ Wκ)(hmΨ:mNv X.p Y.p l hℓ uK R.L ≤ 2*((R.L.val:ℝ)⁻¹)^5) (hv0:(1+(n0:ℝ))⁻¹≤ (R.L.val:ℝ)⁻¹^2)
abbrev tintW (Xp Yp:BudgetPoint)(k p l j:ℕ)(F0:Hove.Grant j p)(Fχ kC A:ℝ) := lush (gyro_S Xp Yp l kC A) (ψC Xp k p l) (Fχ*Sauce Yp A) F0.F (ΩZad (Sauce Yp A) F0.A) δK0
abbrev uXv (Xp Yp:BudgetPoint)(k p j:ℕ)(F0:Hove.Grant j p)(Fχ A:ℝ) := coil_T (Fχ*Sauce Yp A) (ΩZad (Sauce Yp A) F0.A) δK0 (ume F0.C) (κP p) (mC0 Xp)
abbrev uYv (Xp Yp:BudgetPoint)(p j:ℕ)(F0:Hove.Grant j p)(Fχ A:ℝ) := coin_T (Fχ*Sauce Yp A) (ΩZad (Sauce Yp A) F0.A) δK0 (ume F0.C) (κP p) pruneQ (mC0 Xp)
local notation "Lo"=> ((R.L.val:ℝ)⁻¹)
local notation "ζa"=> (‖Ψw‖*‖Aζ‖)
local notation "ζb"=> (‖Ψw‖*‖X0.1‖)
local notation "ζc"=> (‖Ψw‖*‖X0.2‖)
local notation "ζB"=> (ζb*h^2)
local notation "ζC"=> (ζc*h^2)
local notation "μe"=> mintR Lo ζa ζB ζC Q Wκ
local notation "Ξf"=> naxR Lo ζa ζB ζC Q Wκ
local notation "ΞK"=> nagR Lo ζa ζB ζC Q Wκ
local notation "BV"=> (tintW X.p Y.p k p l K.j Φs Fχ kC A* μe)
include hμ he' hN hP Ks Υ Υ' Ψ uc wp wu wq he htP Λk b Q0 hfk hp to_ hu wQ hx h0 hv hK zP u0 Vq pZ hQ0 pQ0 A₀ A₁
include Lp Lv LZ L0 Tp hpY eY ρF PA GA Hψ HΦ Hx hfκ hfφ hX hY hZ vT oT uY pL Bg pv sK pU hk
include Φs uζ hpζ hxζ p0 hk' pA hδ w0
include wM wqL wKc hF htD hmZ hDf hpρ hmΨ hv0
lemma lance_X : ∃ G K' t GΦ GΨ, Ice Lκ o' X.p h (Δv X.p Vκ*BV) (Extr_h Lκ X.p Vκ*BV+KP) BV Hκ G K' t (GΦ,GΨ) ∧ ‖GΦ-Φt‖ ≤ loon (Fχ*Sauce Y.p A)*Ξf ∧ ‖GΨ.1-(Zη)‖*h^2 ≤ uXv X.p Y.p k p K.j Φs Fχ A * Ξf ∧ ‖GΨ.2-(Ζτ)‖*h^2 ≤ uYv X.p Y.p p K.j Φs Fχ A * ΞK:=by
 obtain ⟨ha,hb,hc,Uv,Ft,t,FΦ,FΨ,pv0,ζt,ζv,ζv'⟩:= faith_P A V o E1 OG X0 Aζ Q h hu wQ Fκ hx h0 hv hK zP u0 Vq pZ M τ P_ K₀ w_ Fp Gp Zp hX hY hZ pL j0 vT oT Kx KL Ks F_κ F_l F_k Mp Vs Vl hfκ hfφ hfk Hx HΦ Hψ N0 N1 A₀ A₁ he htP wp wu wq D_ C' Xp₀ Jp Q_ hp b Q0 V0 o' to_ Φs ζ0 uζ hpζ hxζ p0 hk' pA n0 hδ w0 Vκ Ψ uc Υ Υ' hμ he' hN hP Hf Fd Tp hQ0 pQ0 Λk uK hℓ kC vB GA PA Bg S_P Lp Lv LZ L0 Yb hpY uY eY dP ρF hk pv sK pU -- tune args
 -- Nv.point p. after-L forecast.Price.Frame.Beat. root mass nonneg
 have hQ:0 ≤ Q:= (Taxi.eraF _ _ (hx (Φrap (mid P B) o 10)) (zero_le_one.trans h0) _ (ping_f θp _)).grade.trans (Neon.power_r (Y:=Y) _ _ _ _ hx (zero_le_one.trans h0) pZ _)
 obtain ⟨hℓ,uℓ,kℓ,uρ⟩:= peak_T X.p Y.p R.L k p l K.j Φs A Fχ kC wqL hk hu n0 hv0 Q wG ζb ζc П h dP Δpκ (Hove.paid_M o' (OpQ true) p) TkΨ Wκ Hf Fd hℓ uK vB (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hQ wM wKc hF htD hmZ hDf hpρ hmΨ ha hc hb (paidp_p ..) -- tune
 let xℓ:= BV; have ht:wG=ζa:=norm_smul ..
 have hu:Ωκ_t ≤ xℓ := hℓ.trans_eq (by unfold xℓ tintW; rw [ht]); have hk0:0 ≤ Δv X.p Vκ:= by unfold Δv; positivity
 have hK:0 ≤ ΚρK:=by unfold Extr_h; positivity
 refine ⟨Uv,Ft,t,FΦ,FΨ,Ice.gain_μ o' X.p h Lκ pv0 _ _ _ (mul_le_mul_of_nonneg_left hu hk0) (add_le_add (mul_le_mul_of_nonneg_left hu hK) le_rfl) hu,?_,?_,?_⟩ -- tune `ht` treated substitution in proof concessions only RHS no need rewrite everywhere?
 · exact (ζt.trans uℓ).trans_eq (by rw [ht])
 · exact (ζv.trans kℓ).trans_eq (by unfold uXv; rw [ht])
 exact (ζv'.trans uρ).trans_eq (by unfold uYv; rw [ht])
end YM.CF.Neon
#print axioms YM.CF.Neon.lance_X
