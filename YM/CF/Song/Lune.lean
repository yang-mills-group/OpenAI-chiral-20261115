import YM.CF.Song.Bingo
import YM.CF.Song.Loom
import YM.CF.Tuft.Veil
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
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
-- earnings profiles quant issued b through \ell. Accept permit Rent
variable (F:Pilot)(Z:Pluck R)(I:Stake.Isle){σ v₀ v' hκ:ℝ}(Q:Pig.Tun I Z F σ){H:Muster G S x d T}{W:GivenX V U}{G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}{q q':Chi}
variable (b:StatV V G T U W X Y a γ w x p i)(M:Sheep V U W G Y.J X.J (i+2) p A) (τ:Fend V H M Z F q Y.p X.p γ a j l (r*radiusB x))(s:Sheet.isle M=I)(H0: StageP V H Y X U)(K':Girt.BaseL U G Y G₀ G₁ q' kL)
variable (N0 N1:ℕ)(A₀:Roof _ vS dS N0 G₀)(A₁:Roof _ vS dS N1 G₁)(he:N0+N1≤radiusB x)(hx:Stake.PondP V F x vS kL j l (i+2))(hu:kL<firstRadius SU.group)(w0:0< vS)(wv:vS ≤ dS)(wq:dS<d)
variable (htA:0 < A)
variable {b0:ℝ}(P_:∀ D:Support (Domain P B), Lend P B d D) (T':ℝ)(ht:Vista U Y.J.M Y.J.P P_ (i+2) M.q ((Fintype.card Play:ℝ)*T') M.lot M.tone)(zP: Oise.BoldB (T:=T) (k:=i) (H:=H) b0)
variable(D_: Corset d q' kL (i+2) p)(N₀:ℕ)(Q_:Rill.Arch G d)(pX:Q_.val=1) (Qx:TailB→Support (Domain P B)→Toll (Iota G))(Qv: Grave→Support (Domain P B)→Toll (Iota G))(hk:RoofT V (M_:=M) Qx Qv)
-- take common constants. Pee.B+= output p+4.Match after.Same stage calendar.K.No SO.
variable (h m0 mC C C' w' SC oμ ε δ Dμ kW:ℝ)(Xc:SkyC i C)(hM:1 ≤ m0)(ha:1 ≤ mC)(uS:ε>0)(Xp₀:SuitP i C')(Wol:0≤w')
local notation "g₁"=> ((R.L.val:ℝ)⁻¹^2)
local notation "Zr"=> keyS SC A 1 Xp₀.C l p i
local notation "bq"=> sliceK R.L (l+90) (i+2) SC A ((4:ℝ)^p*1)
variable (T_:HeatS V F U W I q q' l i p 1 m0 mC C C' w' SC ε 0 0 (sliceK R.L (l+90) (i+2) SC A ((4:ℝ)^p*1)) 1 Xc Xp₀ Dμ 1 kL D_ N₀ δ A h oμ (keyS SC A 1 Xp₀.C l p i*gritY R.L.val) x) {κ0:ℝ}(Jp:PactH d kL (Xp₀.C*(R.L.val:ℝ)⁻¹^2) κ0 q' (i+2) p D_)
variable (j':l≤18)(pF:fiery SU.group x R.L < vS)(hv1:1 ≤ F.hat R x)(h0:SC =w+2+2)(hK:Footprint.reserve Y.p.supportExponent SC (Footprint.conversion S.ratio (l+90+5)) ε)(hQ:Xp₀.C*(R.L.val:ℝ)⁻¹^2≤1) -- expand g₁
local notation "Zp"=> (fun p: Roc (mid P B)=> (subtK (r:=r*radiusB x) S p))
variable {J_:ℕ}{zv:ℝ}
variable(ve:∀ (F:Forest (ratio G)) (W: Pane (mid P B))(U:Orbit (mid N B)), JointB G (seine G F q' kL W (G₀ U), G₀ U) dS)
variable(blips:ℕ)
variable (yb:∃ A0 B₀ V₀ F0, Yields V I Z F H Q U Y.J X.J q q' kL vS i j blips A0 B₀ V₀ F0)
variable(hp:1≤h)(ph:1 < I.fine)(wK:5*Y.p.B+4≤10*radiusB x)(e':LocalRatio L)(jK:l ≤18)(βU:0< Y.beta)(rP:(j+110)*radiusB x+14≤r*radiusB x)(rQ: 2*((j+5)*radiusB x) ≤ r*radiusB x)
open Lilt Plume Vow Bake
local notation "mQ"=> (zv*(degreePrice (radiusB x) zv 1)^0*(1-degreePrice (radiusB x) zv 1)⁻¹)
local notation "Aƙ"=> (oμ*(backX 2 *reserveT p i (radiusB x) 2))
local notation "Pδ"=> thermV SC m0 mC ε Dμ Zr 2 Xc p l
local notation "ΣC"=> Troupe S (r*radiusB x) (Words S)
variable (hv_:1 ≤ rainX R 1 x)(uR:rainX R 1 x≤ rainX R 2 x)
local notation "σn"=> Aura (mid N B)
local notation "Φn"=> Aura (mid P B)
local notation "Kz"=> (mid N B)
local notation "rQv"=> r*radiusB x
local notation "Θr"=> Y.p
variable {Yφ:Troupe S (r*radiusB x) (Words S) → Palot.leaf (Site (Domain N B)) → Raid (LeanV (Single (mid N B)))} {Uφ:Troupe S (r*radiusB x) (Words S) → Palot.leaf (Site (Domain N B)) → Orbit (mid N B) → Cipher (mid N B)}
variable (Mν:Jade.GroV V F Z M P_ ht τ K' Yφ Uφ h zv 1)(Wν:Angost V F Z M τ K' P_ T' ht)
open Prism Haro Oath
variable (iκ:Roc (mid P B))(O:Ride S) -- trim
local notation "Ωv"=> ((H.post+90)*radiusB x)
local notation "Pm"=> (hostX (l:=Ωv) S iκ).val
local notation "YO"=> (Stilo.beamH (hostX (l:=Ωv) S iκ).val)
local notation "Hc"=> actionZ Y iκ
local notation "V'Z"=> vanX (M:=M) V D_ U W H iκ Jp Q_
local notation "qT"=> (Prism.Rock (mid N B))
local notation "Wp'"=> (taxV X.p Yφ h)
-- authorization.L.Revenue.Spectral.Shape.Sun. HOIST from X Loom.F
local notation "ΘC"=> (beam_C (H:=H) V M D_ Q_ C' Xp₀ Jp)
local notation "Υ"=> (glasp (H:=H) V M D_ Q_ C' Xp₀ Jp)
local notation "Vt"=> forge_P (H:=H) V M D_ Q_ C' Xp₀ Jp
local notation "Hq" t:max=> hostX (l:=Ωv) S t
local notation "tη"=> (Youth N P B)
open Larch
variable (κ':Roc (mid P B)→ℝ)(Pp:∀ iκ:Roc (mid P B),PressB Y.p iκ.1 (actionZ Y iκ) h (κ' iκ)) (GG: Gala p i 100 x 3)
variable{ad:ℝ}(Tp:Ids (mid N B))(BB1 BB2:Roc (mid P B)→ Aura (mid N B)→ℝ)(Vh:∀ iκ:Roc (mid P B),ReconB (Xs:=X) H Tp iκ h (fun B=> Uφ (subtK S iκ) B) (BB1 iκ) (BB2 iκ) (vanX (M:=M) V D_ U W H iκ Jp Q_) (ad* Y.p.mass iκ.1.val.2 (κ' iκ)))
local notation "Tz"=> (fun t:tη=> grain_V i h (Wp' t.2.1 (Zp t.1)+ chi_f X.p.order*((BB1 t.1 t.2.1)+(BB2 t.1 t.2.1))))
variable (DF:ℝ)(u2:∀ oRh:Site (Domain N B),(∑ i:Roc (mid P B) with S.ratio.parent i.1.val.1=oRh,∑ j:Palot.leaf (Site (Domain N B)) with (hostX (l:=((H.post+90)*radiusB x)) S i).val⊆j.val, X.p.mass j.val (BB1 i j + BB2 i j)) ≤ DF)
local notation "σQ"=> (loft_X (S:=S) ((H.post+90)*radiusB x))
local notation "RΛ"=> Roc (mid P B)
local notation "UΨ"=> ΘC iκ (Stilo.beamH O) -- remove
local notation "o₁"=> spot_v (S:=S)
local notation "WC"=> (miteV X.p.B X.p.order X.p.power 1 zv)
open Vow Bake Rue Larch
-- purchase van transfers T^. program.X.Up.Ph.N rho. threshold^Room.CALL SCC.Ph.Ch.b. any Board.S Term.Φ.cost waivers. n=6 supports.
local notation "StF"=> (Vt)
local notation "σP"=> X.p
local notation "δΦ"=> grain_V i h 1
local notation "Kv"=> GvC i h WC DF (Larch.ball_v (cirQ x):ℝ)
local notation "Qδ"=> (X.p.supportExponent+1+1)
local notation "Kw"=> shine_C (l+300) (X.p.supportExponent+1+1)*(tet_B (l+300) X.p.B * GvC i h WC DF (ball_v (cirQ x):ℝ))
variable (pW:WindV K.j p)(pα:Tact G S Y h δ κ')(Nπ: BeaconP K.j Y S)
local notation "Λm"=> ((2:ℝ)^p*(16*δ)/h^2)
variable (ζ0:ℝ)(hvZ:0 < ζ0)(hZ:3*ζ0 ≤ M.r0)(uZ:ζ0 ≤1)
local notation "Cπ"=> (population*(A*followV [] R.L))
local notation "ρθ"=>way_Q R i p x δ Cπ ζ0 pW.C h
variable (Ωs HS Hf Df Lv Lp LK:ℝ)(Ap:Corona_Q (zv:=zv) V F Z M τ K' P_ T' ht D_ h C' δ Xp₀ Jp HS Hf Df Lv Lp LK)
local notation "XΨ"=> (pace_Z R Hf δ Df)
local notation "YP"=> pay_Z p (radiusB x) l i x h zv (XΨ) w
local notation "Kα"=> (rainX R 2 x)
variable (qv:degreePrice (radiusB x) Ωs 1 < 1)(hQ0:0 < Ωs)(hS:1 ≤ rainX R 2 x)(qHK:pay_Z p (radiusB x) l i x h zv (pace_Z R Hf δ Df) w+Lv+ (HS*degreePrice (radiusB x) HS 1 ^0*(1-degreePrice (radiusB x) HS 1)⁻¹) ≤1) (μσ:rainX R 2 x*LK+ Real.exp 1*((HS*degreePrice (radiusB x) HS 1^0*(1-degreePrice (radiusB x) HS 1)⁻¹)+(pay_Z p (radiusB x) l i x h zv (pace_Z R Hf δ Df) w+Lv)) ≤ Ωs)
include Ap b τ K' hvZ hZ uZ pα Nπ GG pW htA hp H0 A₀ A₁ he hx w0 wv wq e' βU qv hQ0 hS qHK μσ
local notation "σY"=> (shine_C (l+300) (X.p.supportExponent+1+1))
omit qv hQ0 hS qHK μσ
open Ione
variable (qT_:Pant_W (N:=P) Y)
include qT_

lemma baudU:∃ Yφ Uφ,Jade.GroV V F Z M P_ ht τ K' Yφ Uφ h zv 1 ∧ GaussW X.p (nixV (cone_f Uφ)) (cone_f Uφ) h (pack_Q i*pay_Z p (radiusB x) l i x h zv (pace_Z R Hf δ Df) w+Lv) LK (wren_K i p*(pace_Z R Hf δ Df+rise_K i p w* |way_Q R i p x δ Cπ ζ0 pW.C h|) +reserveT p i (radiusB x) 1*(3*Lp)) HS∧ ArmsK X.p (cone_f Uφ) (pence_v X.p Yφ h) h ∧ ∀ o:Seat (mid N B),tallB (Vow.hymn (pence_v X.p Yφ h)) X.p.B (X.p.supportExponent+1+1+1) o≤ LK:=by
 obtain ⟨Yφ,Uφ,Mν,xQ,K1,lk0,Qw,hxU,uK⟩:= Ap.title; let Tp:= Classical.arbitrary (Ids (mid N B)); obtain ⟨B1,B2,Tκ,qh,Lw⟩:= (uK κ' pα Tp).yield
 obtain ⟨Qx,Qv,Fq⟩:= Pig.sail_t V (M_:=M); let D:= XΨ; have pW0:S.patch.L= R.L:=congrArg RG.Patch.L τ.head.cert.got
 let D':= Hf*(S.patch.L.val:ℝ)^4*δ+Df; have hw:D'=D:=by unfold D'; rw [pW0]
 obtain ⟨Fv,A0,C0,ρ,pV,uρ,hU,vV,pL⟩:= lunar_Q V F Z b M τ H0 K' N0 N1 A₀ A₁ he hx w0 wv wq htA P_ T' ht D_ Qw hxU Qx Qv Fq h C' δ Xp₀ Jp hp Mν κ' GG Tp B1 B2 Tκ D' Lw pW pα Nπ ζ0 hvZ hZ uZ qT_ -- tune
 let K'B:= σY*(tet_B (l+300) X.p.B * GvC i h WC D' (ball_v (cirQ x):ℝ)); have hB: K'B=YP:=by unfold K'B pay_Z; rw [b.fee,b.down.order,b.down.hK,b.bill,hw]
 have hk(O:Seat (mid N B)): tallB C0 X.p.B (X.p.supportExponent+1+1) O ≤ YP:= (uρ O).trans_eq hB
 let E:= old_Q Uφ; let K:= cone_f Uφ; let X':=nixV K
 have hY:= Ione.zeal_P X.p E X' K xQ K1 Fv pL hp hU vV (musk_Q V F Z b M τ H0 K' N0 N1 A₀ A₁ he hx w0 wv wq P_ T' ht h Mν qT_) (fun i V0 p i' D b' c=> cone_Y V F Z b M τ H0 K' N0 N1 A₀ A₁ he hx w0 wv wq P_ T' ht h Mν i V0 i' qT_ D p) (phant_E V F Z b M τ H0 K' N0 N1 A₀ A₁ he hx w0 wv wq P_ T' ht h Mν qT_) pV hk lk0 ρ
 rw [hw,b.fee,b.down.order,b.down.hK,b.bill] at hY; exact ⟨Yφ,Uφ,Mν,hY,K1,lk0⟩

open Sour Stax Haro Nacre Scroll Salt
local notation "Zκ"=> pence_v X.p Yφ h
local notation "Gκ"=> cone_f Uφ
local notation "Υt"=> (pack_Q i*pay_Z p (radiusB x) l i x h zv (pace_Z R Hf δ Df) w+Lv)
local notation "Μc"=> (wren_K i p*(pace_Z R Hf δ Df+rise_K i p w* |way_Q R i p x δ Cπ ζ0 pW.C h|) +reserveT p i (radiusB x) 1*(3*Lp))
include Mν
omit Ap hvZ hZ uZ pα Nπ GG pW htA hp e' βU qT_
private lemma soul_v (Xq:Aura (mid N B))(δq:ℕ)(hp':δq≤10*radiusB x)(W0:Support (Domain N B)): Stax.Lives X.p δq Xq W0 (Gκ Xq W0):=by
 intro i p; unfold cone_f at p; rw [Finset.sum_apply] at p; obtain ⟨j,v,t'⟩:= exists_ne_zero_of_sum_ne_zero p; obtain ⟨k,g⟩:= Salt.permit K' τ P_ ht j (beamH Xq.val) (Uφ j Xq) (Mν.quiet _ _).toLullT _ t'; have hx:= Salt.hostB K' τ P_ ht j (beamH Xq.val) δq hp' k; have hv: W0=(penn S j).flags:= (mem_filter.mp v).2.symm; rw [hv]; exact ⟨by simpa only [bay_beam] using hx,g⟩ -- scope
omit Mν
variable {δK θ b₀ b₁ b₂ b₃ γ' n₃ r₀ v₃ v₄ z e₃:ℝ}{n₂:ℕ}(q2:1 ≤ X.p.power)(zqt:0 < r₀)(l₃:MotD V b₀ b₁ b₂ b₃ n₂)(h8:n₂ ≤ (mid N B).val)(xB:dS≤ b₃)(s₃:1 ≤ K.j) -- remove
local notation "b'"=> (Tenant.quota^2*(b₁*r₀))
local notation "c'"=> (Tenant.quota^2*(b₂*r₀))
local notation "ρv"=> Dq X.p b₀ b' c' Μc θ z h γ' δK r₀
local notation "Τ'"=> riseV
abbrev ThemeS (E:Cusp (mid N B))(p:ℝ):=E
variable (Tσ:Finset (Scree.Hub (mid N B)))(hc0:liveB Tσ)(hz:∀ i:Scree.Hub (mid N B),coverNumber X.p.B i.val.2≤1 → i∈Tσ)
include Ap hvZ hZ uZ pα Nπ GG pW htA hp e' βU qT_ zqt l₃ h8 xB q2 s₃ hc0 hz
local notation "Γδ"=> QuotaH V.f V.g V.F1 V.F2
local notation "KX"=> mid N B
lemma lumen (Wk:Lens v₃)(eZ: Pace X.p b₀ b' c' h r₀ γ' δK HS LK Μc θ z Kα v₃)(wz: 1 ≤ Kα)(hz':0 < z)(t₃:X.p.threshold≤vS)(r1: N0+10≤ X.p.B)(h1:cipherK N0≤5* X.p.B)(s1:3 ≤ X.p.B)(hE:0<b₀)(pE:b₀≤1)(hzG:HopeT dS e₃ v₄ X.p.order)(hl:X.p.threshold ≤ v₄): -- Note HopeT uses v₃ => need separate λ
 ∃ Yφ Uφ,Jade.GroV V F Z M P_ ht τ K' Yφ Uφ h zv 1 ∧∃ (iv:ΘS r₀)(E C: Cusp (mid N B))(T':RegBudget (mid N B))(m:ℝ)(Z':Aura (mid N B)→ℝ), Anuk C Z' X.p h∧ (∀ i:Seat (mid N B),tallB Z' X.p.B (X.p.supportExponent+1+1) i ≤ Υt) ∧ ZealQ C ∧ BondL.Picket X.p E T' C Tσ X.J.M K.j m h Υt ρv ((rainX R 2 x)⁻¹*γ') θ wΨ∧∃ j: Γδ, j.2=X.J.M∧ (j.1 _).val=X.J.P∧ EdgeC X.p A₀ (w0.trans_le wv) (tatE V j KX) (tagE V j KX) (cone_f Uφ) E (Haro.riseV iv):=by
 obtain ⟨Yφ,Uφ,Mν,Y',K₀,t⟩:=baudU V F Z b M τ H0 K' N0 N1 A₀ A₁ he hx w0 wv wq htA P_ T' ht D_ h C' δ Xp₀ Jp hp e' βU κ' GG pW pα Nπ ζ0 hvZ hZ uZ HS Hf Df Lv Lp LK Ap qT_; obtain ⟨U0,Bk,m,U',Z0,C',pK,u0,h₂,ℓ,heB,vA,qF,hR,Tk,hpP,fV⟩:= Y'.render -- C' shadow
 let G0:= cone_f Uφ; let Ci:=pence_v X.p Yφ h; let I (X:Aura KX)(D:Support (More KX)) := if D.Nonempty then Ci X D else U' X -- syntax
 have hv(Xq:Aura KX)(D)(v:D⊆ Xq.val):Fray X.p h (cipherK N0) Xq D (G0 Xq D) (I Xq D):=by
    refine ⟨?_,soul_v V F Z b M τ H0 K' _ _ A₀ A₁ he hx w0 wv wq P_ T' ht h Mν Xq _ (by rw [b.fee] at h1; omega) D⟩; unfold I; split; next s=> exact K₀.price _ _ s v
    next s=> rw [Finset.not_nonempty_iff_eq_empty.mp s]; exact u0 _
 have hd:= K'.legal.1; have hr:Bake.Turf (fun i=>G0 i ∅):= Jade.pep_f V F Z M P_ ht h τ K' H0 N0 N1 dS A₀ A₁ he wv wq Yφ Uφ Mν (half_lt_self w0) (half_pos hd) (half_lt_self hd) (fun y v p=> (hx τ y v p).1)
 have py(i:Seat KX):tallB (Vow.hymn I) X.p.B (wu X.p) i≤ LK:=by have hu: Vow.hymn I=Vow.hymn Ci:=funext (fun X=> sum_congr rfl (fun i v=> if_pos (mem_filter.mp v).2.1)); rw [hu]; exact t i
 have hxT(i:Seat KX):tallB (urnL I) X.p.B (wu X.p) i ≤ HS:=by rw [show urnL I=U' from (funext (fun i=> if_neg Finset.not_nonempty_empty))]; exact dutyK pK i -- δ def 
 have hg:=b.dose.courage; have he':= hg.leanJ.1; rw [W.h2,W.h4,W.h1,W.h3] at he'; obtain ⟨j',u,v⟩:= demand _ V.pos1.le V.pos2.le _ he' X.J.M; let heZ:= l₃.earn j' KX _ _ zqt h8 (w0.trans_le wv) xB; have hpQ:= rise_F V s₃ U W X hg K'.size j' r₀ u v wq.le -- order K'.size maybe coarse requirement fine.X side.N
 obtain ⟨i,E',C'',hT,e⟩:= goX hp G0 X.p A₀ (w0.trans_le wv) hE pE zqt hzG hl t₃ r1 h1 s1 q2 I hv hr (fun s i' Ψ p a c=>cone_Y V F Z b M τ H0 K' N0 N1 A₀ A₁ he hx w0 wv wq P_ T' ht h Mν s Ψ i' qT_ a p) vA s₃ v₃ Wk U0 Bk (show PreR X.p G0 U0 Bk m h Υt Μc from ⟨hpP,fV⟩) Tσ hc0 hz wz hz' hpQ heZ (mul_le_mul_of_nonneg_right l₃.fresh zqt.le) hxT py (M:=X.J.M) eZ -- order
 exact ⟨Yφ,Uφ,Mν,i,C'',Bk,E',m,Z0,h₂,ℓ,heB,hT,j',v,u,e⟩
end YM.CF.Py
