import YM.CF.Muse.Plate
import GaugeFieldConstruction.Webb
import GaugeFieldConstruction.Tremolo
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
local notation "B_"=> (More N)
local notation "S₁"=> (Domain N B)
local notation "dN"=> Directions SU.group (More N)
local notation "tL"=> mid P B
local notation "sL"=> mid N B
variable {r d':ℕ}
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
variable (F:Pilot)
-- S0 pre-L security.
variable {s u:ℝ}{q q':Chi}
local notation "tfx"=> (radiusB x)
open Feu Feu.Corset Haro
variable (D:Corset d q' u (k+2) k')(pV:BudgetPoint)
variable {σ:ℝ}(Z:Pluck R)(U:Grasp V.U B d)(W:GivenX V U){Xs: GramM (mid N B)}{Y: GramM (mid P B)}{M:Sheep V U W G Y.J Xs.J (k+2) n A}(P_:∀ X: Support (Domain P B),Lend P B d X)(H:Muster G S x d T)
variable {γ α:ℝ} (uF:Fend V H M Z F q Y.p Xs.p γ α j l r)
local notation "LQ"=> ((H.post+90)*radiusB x)
-- CURRENT rods. step purchased.F.Shape representative static
local notation "H_X"=> F.hat R x
local notation "V'"=> (stilK tfx)^k'
local notation "Y'"=> Y.p
variable {q'' q0 : ℝ}(w':Hive.Vista U Y.J.M Y.J.P P_ (k+2) M.q ((Fintype.card Play:ℝ)*q'') M.lot M.tone)
open Jet Plume Eire.Dress

variable (Fκ:FerryP H F K R D) (φ: Xs.p.power=k')
variable{G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}(D_: Girt.BaseL U G Y G₀ G₁ q' u)(L0: StageP V H Y Xs U)
local notation "Φ"=> F.hat R x
local notation "tV"=> (temp x)
variable (Cp: Plume.Cord S)(K_:Fairy S (F.hat R x) Cp)(Tp:Ids (mid N B))(U':Pane (mid N B))(i:Roc (mid P B))(O:Ride S)(y:pingS (temp x) (Stilo.bay O) U')
local notation "N_"=> mid N B
local notation "vT"=> (Vmove x U')
local notation "WΗ"=> (Stilo.bay O)
local notation "sX"=> ArchL D_ uF.head.scaleP H
local notation "I_"=> lineP Xs.p (S.ratio.parent i.1.val.1) (Stilo.bay O) (radiusB x)
local notation "pp"=> subtK (r:=r) S i
local notation "G'"=> (fun U:Pane (mid N B)=> Stake.Grit D_ uF P_ w' (U,Tp) Cp)
local notation "Yx"=> (fun U' : Pane (mid N B)=> (G' U').heatT pp)
local notation "Ω"=> (fun i:Directions SU.group (Domain N B)=> (G' (vT (I_ i))).coats pp) -- notation `i` captures!? hygiene danger. test
local notation "MK" U:max=> (Plume.cort (S:=S) U Cp)
local notation "T_'"=> Cp.2.2
local notation "S2"=> (Eire.trot S (Plume.cort U' Cp) (kop S r))
variable (χ:x=x)
local notation "SB"=> (BranchX (r:=r) S (vast (k:=Z.N1*radiusB x) H) LQ)
variable {a a' s0:ℝ}(hx:a < s)(hu:0<a')(hu':a' < u)
variable (Qp: Palot.fits (BranchX (r:=r) S (vast (k:=Z.N1*radiusB x) H) ((H.post+90)*radiusB x)) (subtK (r:=r) S i) O)
variable (k₀ k₁:ℕ)(A_: Roof (mid N B) s s0 k₀ G₀)(A₁: Roof (mid P B) s s0 k₁ G₁)(heV:k₀+k₁ ≤ radiusB x)(η':l≤18)(ss:s ≤ s0)(tK:s0 < d)(hU:u< firstRadius SU.group) (hpZ:fiery SU.group x R.L < s)
variable (hv:∀ (Q: Monk SU.group S), Chir Q x → ‖Q.z‖≤ F.hat R x → Bell S Q x T H.trot H.room H.post H.beta a a')
local notation "ΛX"=> (erosion ((H.post+70)*radiusB x) (Stilo.bay O))
local notation "Jc"=> school (MK U') r H
local notation "Ξ"=> (subtK (r:=r) S i)
local notation "KT"=> (kop S r)
variable (M₀ a0 C C' v w t:ℝ)(R0:PlanS k Xs.p Y.p i O (cort U' Cp) (school (cort U' Cp) r H) T R M₀ a0 C C' v w r l x)
local notation "o"=> S.ratio.parent i.1.val.1
local notation "x0"=> (i.1.val.2)
local notation "pe"=> (Y.p)
local notation "𝔛"=> (Xs.p)
local notation "Hv"=> (Jc ∘ (vT∘ I_))
local notation "n₀"=> Directions SU.group (Domain N B)
-- use simple local E spectral energy with tags.V Caps. Coarse near V only. No derivative of Key prints.S exact on patch.H true regardless Sort. 
-- curvature & closeness. rail payment μ angles—η post only. LamQ buy. use V.tender.
section
local notation "Tρ"=> (Support (Domain P B))
local notation "cΩ"=> (Scree.mid N B)
local notation "uΦ"=> (actionZ Y i ∘ Jc)
variable {vK Kρ K₁ ε Bz:ℝ}
variable (oθ:Find Xs.p Y.p k n x R.L)(Jp:PactH d u ε Bz q' (k+2) k' D)
variable (F':Raid (Dwell (mid P B)))(Q CC:ℝ)(Xf:PressB Y.p i.1 (actionZ Y i) Q CC)(fF:∀ U,BedP Y.p U (actionZ Y i) i.1 F')(fP:∀ i,0≤ F' i)
local notation "Λ"=> Heir.reach x
local notation "£V"=> vT ∘ I_
variable (W_X: Rill.Arch G d)(tW:W_X.val=1)
open Trees Footprint
variable (Qx:TailB→Support (Domain P B)→Toll (Iota G))(Qv: Grave→Support (Domain P B)→Toll (Iota G)) (v0:RoofT V (M_:=M) Qx Qv)
variable (Xc:SkyC k C) (hM:1 ≤ M₀)(ha:1 ≤ a0)
variable (Xp₀:SuitP k C')(vh':v=(R.L.val:ℝ)⁻¹^2)(Wol:0≤w)(heV': ε ≤ 1)(hρ:Xp₀.C*(R.L.val:ℝ)⁻¹^2 ≤ ε)(hlimP:w*Xs.p.threshold*(1+(Heir.reach x:ℝ))<u)(vP:TubeP k k' w ε 1 x)
variable (b' ε' τ:ℝ)(SC SC':ℝ)(δ:ℝ)
variable (hpre_b:SC*2*Yaw.χ (l+90) ≤ radiusB x*(M.r0/2))(po:0≤SC)(pe':0≤ε)(vt:0≤ SC')(hx':0<Q)(T_:∑ i':Finset (Dwell (mid P B)), Scree.tariff Y.p i.1.val.1 Q i'*F' i'≤CC)
variable (hr₀:Push.AbsoluteSums.Footprint.reserve Y.p.supportExponent SC (Push.AbsoluteSums.Footprint.conversion S.ratio (H.post+90+5)) ε')
local notation "PU"=> puls (Y:=Y) H i M₀ a0 C F' Qx Xc Qv ε
local notation "Lφ"=> meritT C Xc Y.p (i.1.val.2) H.post M₀ a0
local notation "HY"=> (population*M.r1)
local notation "HX"=> (population*(A*followV [] G.count))
local notation "Ω₀"=> (hostX (l:=LQ) S i).val
local notation "B'_"=> Y.p.mass i.1.val.2 CC
local notation "H4"=> (Real.exp (SC*Yaw.χ (l+90))*(lip (k+2)*HY))
local notation "Hc"=> lorp SC (l+90) Xs.p.power HX
local notation "WZ"=> ((H4 + Real.exp (-(M.r0/2)*(radiusB x:ℝ))*Hc*(SC'^2*lip (k+2)^2) + Hc*(SC'^2 * levyC k 1 ε))/Q^2)
local notation "Bz"=> Coin_ ((4:ℝ)^n*SC') (population*(A*followV [] G.count)) (population*M.r1) SC (l+90) (k+2)
variable (hh:0 ≤ b')(hb:b' ≤1)(vY:0 ≤ Coin_ ((4:ℝ)^n*SC') (population*(A*followV [] G.count)) (population*M.r1) SC (l+90) (k+2))(hp:Coin_ ((4:ℝ)^n*SC') (population*(A*followV [] G.count)) (population*M.r1) SC (l+90) (k+2)≤ b'*Q)
local notation "graI"=> Real.exp (-ε'*(coverNumber Y.p.B x0:ℝ))
local notation "Bill"=> (Real.exp (SC*Footprint.preCost (l+90+5))* ledgerP k n ε' * harp C Xc n l M₀ a0)
local notation "Sp"=> sparkK C Xc R
local notation "H8"=> (Real.exp (Bill*δ)*(Bill*δ))
local notation "Xo4"=> (graI*(Bill * (b'^4+ H8 +Sp))*B'_)
local notation "Xo0"=> (graI*(Bill*(1+ H8))*B'_)
local notation "S'u"=> Strung Ω₀
local notation "Zq" x:max=> rateT (Scree.tariff Xs.p o SC') x
local notation "gT"=> gateQ (M:=M) V D U W H i Jp W_X
-- separate want pulse from new.L Budget. Provisional leftover. Enact on tail via assumptions later. Pay all angular.R.Shocks.Old. 
variable (Bv: Short S Y.p i.1.val.2→ Siete.Acceptance Y.p i.1.val.2 i.1.val.1 (fun Vß=> crumb (actionZ Y i Vß).val ∅) (F' ∅))(hP:Y.p.mass i.1.val.2 CC ≤ δ)
open Lilt Jade
local notation "GZ"=> (gateQ (M:=M) V D U W H i Jp W_X)
local notation "PX"=> Palot.leaf (Site (Domain N B))
local notation "YP"=> (Xs.p)
local notation "W_"=> (vanX (M:=M) V D U W H i Jp W_X)
local notation "hO"=> Stilo.beamH Ω₀
variable (kR:1 ≤ radiusB x)(hRs:S.ratio=Rush.ratio G)
variable {ζμ Zκ:ℝ}
local notation "Tq"=> (Track (Ride S) (Raid (Dwell (mid N B))))
variable (S0 S1:Track (Ride S) (Raid (Dwell (mid N B))))(Q0:VoiceZ V F D Z U W P_ H uF w' D_ i M₀ a0 C Jp CC W_X Xc b' ε' SC SC' δ ζμ S1 S0 Zκ)
local notation "Zz"=> (Jade.tour (S:=S) (F.hat R x))
variable (oκ:Palot.leaf (Site (Domain N B)))
local notation "OΦ"=> Stilo.beamH oκ.val
local notation "YΦ"=> Pane (mid N B)
local notation "ZΦ"=> Cipher (mid N B)
local notation "Mx"=> Xs.p
variable (D0 d0:ℝ)(J_:ℕ)(Bq: ↥(Sil S r)→Roc (mid P B)→↥(tale S (((H.loft+H.post+200)*radiusB x)) (luceL R J_ x))→Track (Ride S) (Raid (LeanV (Single (mid N B)))))(Gq:↥(Sil S r)→Roc (mid P B)→Track (Ride S) ℝ)(Ag:∀ t':↥(Sil S r), RopeX (c:=d0) V F Z M P_ w' J_ SC' uF D_ t' (Bq t') (Gq t') D0)
variable (pρ:0 ≤ ζμ)
local notation "oG"=> (S.ratio.parent i.1.val.1)
variable (hΦ:Roc (mid P B))
-- static
local instance textW_S0 :MeasurableSpace (Finset (Sat S)):= ⊤
local instance textW_S1 :MeasurableSingletonClass (Finset (Sat S)):=⟨fun _=>trivial⟩
local instance textW_S2 :MeasurableSpace (List (Hos S r)):= ⊤
local instance textW_S3 :MeasurableSingletonClass (List (Hos S r)):=⟨fun _=>trivial⟩
local instance textW_S4 :Finite ↥(Sil S r):=Set.Finite.to_subtype Jade.sill_p
local notation "WQ"=> ((H.loft+H.post+200)*radiusB x)
local notation "Hc"=> (J_) -- collision
local notation "Z₂"=> (luceL R J_ x)
local notation "ΨK"=> (Jade.loam V F Z M P_ w' uF D_ (subtK (r:=r) S i) OΦ)
variable (KΩ:Oath.Shrine (mid N B) (Stilo.bay (Stilo.beamH oκ.val)) (fun v=>vanX (M:=M) V D U W H i Jp W_X v (Stilo.beamH oκ.val)))
local notation "WT"=> wrap_B (fun z=> (W_ z OΦ)) (Stilo.bay OΦ) KΩ
variable (I':Orbit (mid N B)→Cipher (mid N B))(vtB: LullT V F Z M P_ w' uF D_ (subtK (r:=r) S i) (Stilo.beamH oκ.val) I')
local notation "Hi"=> (pulseZ) -- dummy
variable (Y'Φ:(hostX (l:=((H.post+90)*radiusB x)) S i).val ⊆ oκ.val) -- tune required
variable (Ky:Stake.PondP V F x s u j l (k+2))(hT:0 < s)(pT:0<u)
local notation "HG"=> Finset (Dwell (mid N B))
local notation "qX"=> (fun z:Pane (mid N B)=> I' (z,Tp) - WT z)
local notation "QΞ"=> (text_r S Ω₀ ζμ (F.hat R x))
local notation "Xμ"=> (Zz).real (QΞ)
local notation "σG"=> (earnX Xs.p Ω₀ ζμ (F.hat R x) x Z₂ WQ (fun z=> Bq z i) oκ)
local notation "Yβ"=> raiseP Xs.p S1 (radiusB x) OΦ
local notation "Zβ"=> raiseP Xs.p S0 (radiusB x) OΦ
variable{Zp:ℝ}(Q0r:Oise.BoldB (T:=T) (k:=k) (H:=H) Zp)
local notation "pQ"=> ↥(Robe S Φ)
local notation "zP"=> ((Mx))
local notation "Tr"=> (Tg) -- collision!
local notation "Hug"=> (Rue.litres Xs.p.threshold (Stilo.bay OΦ) ∅)
open Py
local notation "sΚ"=> tonK (H:=H) i oκ Y'Φ
local notation "WΣ"=> (birth_v (H:=H) (X:=Xs) F J_ ζμ Bq i oκ)
local notation "WΣ₃"=> ((1+(Hope.reel (radiusB x) oκ.val:ℝ))^Xs.p.order • WΣ)
abbrev Scant(ζμ:ℝ)(nn:Bool)(G:YΦ) : Cipher (mid N B):=∫ j:pQ in (if nn then (text_r S Ω₀ ζμ (F.hat R x))ᶜ else text_r S Ω₀ ζμ (F.hat R x)), ΨK (G,Tp) j.val ∂Zz
local notation "Vx"=> Scant V F Z U W P_ H uF w' D_ Tp i oκ -- check parameters (# print)
-- support-local on chamber (not globally!)
include uF A_ A₁ hT pT heV L0 Ky Tp tK ss
lemma tunicOn (ζμ:ℝ)(n:Bool)(G Gζ:YΦ)(ht:pingS Xs.p.threshold oκ.val G)(hu:pingS Xs.p.threshold oκ.val Gζ)(hh:Agrees oκ.val G Gζ) : Vx ζμ n G= Vx ζμ n Gζ:=by
 have hT':(cook S (subtK (r:=r) S i).toLeft).flags=∅:=by rw [Feu.hu_p]; exact Feu.kflags _
 unfold Scant; exact setIntegral_congr_fun (by split <;> first | exact (textR_m ..).compl | exact textR_m ..) (fun z h=> songT V F Z M P_ w' uF D_ L0 _ _ _ A_ A₁ heV ss tK hT pT Ky (subtK (r:=r) S i) OΦ _ z.property Tp Tp _ _ (by rw [bay_beam,hT']; constructor; simpa using ht; simp) (by rw [bay_beam,hT']; constructor; simpa using hu; simp) (by rw [bay_beam]; exact hh) (fun _ _=>rfl) (by rw [hT']; simp))
local notation "Dvh"=> unrest (∅:Support (Domain N B)) Xs.p.B
include Q0r Ag Y'Φ η'
lemma tuntegral (G:YΦ)(ht:pingS Xs.p.threshold oκ.val G): Integrable (fun x' : pQ => ΨK (G,Tp) x'.val) Zz:=by
 let y:= enough_r uF; haveI:=tour_p (S:=S) y
 let Pκ:= fun i:pQ=>stamp i.val WQ Z₂ r; have he:Measurable Pκ:= stamp_m.comp measurable_subtype_coe
 let Vxe(i:pQ)(z:YΦ):ZΦ:= ΨK (z,Tp) i.val
 let S'₀:=↥(Sil S r)× ↥(tale S WQ Z₂); let Y_(t:S'₀):= Bq t.1 i t.2 OΦ; have hb:0 ≤ Y_:= fun z=> (Ag _).hand _ _ _
 have hh(j:pQ):Sym_ Xs.p (radiusB x) (Vxe j) (Stilo.bay OΦ) ∅ (Y_ (Pκ j)):= (Ag _).ticket i j.val Tp OΦ rfl j.property
 have hw : G∈ Hug:=by rw [bay_beam]; constructor; simpa using ht; simp
 have hu(j:YΦ):StronglyMeasurable (fun x' :pQ=>Vxe x' j):= (all_m V F Z M P_ w' uF D_ L0 k₀ k₁ _ A_ A₁ heV η' ss tK hT pT Ky (subtK (r:=r) S i) (Stilo.beamH oκ.val) Q0r (fun i:pQ=> i) measurable_id (fun _=>(j,Tp)) measurable_const).stronglyMeasurable
 have ha:oG∈ Stilo.bay OΦ:=by rw [bay_beam]; exact Y'Φ (hail_o S i)
 exact digJ Xs.p (Stilo.bay OΦ) ∅ Vxe Y_ hb Zz Pκ he hh _ ha (empty_subset _) (fun z _=>hu z) _ hw
lemma tunprice (G:YΦ)(ht:pingS Xs.p.threshold oκ.val G)(p:Xs.p.power=2):BedP (KeyUp Xs.p) G (Vx ζμ false) sΚ WΣ₃:=by
 let y:= enough_r uF; haveI:=tour_p (S:=S) y
 let Pκ:= fun i:pQ=>stamp i.val WQ Z₂ r; have he:Measurable Pκ:= stamp_m.comp measurable_subtype_coe
 let Vxe(i:pQ)(z:YΦ):ZΦ:= ΨK (z,Tp) i.val
 let S'₀:=↥(Sil S r)× ↥(tale S WQ Z₂); let Y_(t:S'₀):= Bq t.1 i t.2 OΦ; have hb:0 ≤ Y_:= fun z=> (Ag _).hand _ _ _
 have hh(j:pQ):Sym_ Xs.p (radiusB x) (Vxe j) (Stilo.bay OΦ) ∅ (Y_ (Pκ j)):= (Ag _).ticket i j.val Tp OΦ rfl j.property
 have hw : G∈ Hug:=by rw [bay_beam]; constructor; simpa using ht; simp
 have hu(j:YΦ):StronglyMeasurable (fun x' :pQ=>Vxe x' j):= (all_m V F Z M P_ w' uF D_ L0 k₀ k₁ _ A_ A₁ heV η' ss tK hT pT Ky (subtK (r:=r) S i) (Stilo.beamH oκ.val) Q0r (fun i:pQ=> i) measurable_id (fun _=>(j,Tp)) measurable_const).stronglyMeasurable
 have ha:oG∈ Stilo.bay OΦ:=by rw [bay_beam]; exact Y'Φ (hail_o S i)
 let μ:= (Zz).restrict QΞ
 intro _ j
 let Bh:= thrive Xs.p (Stilo.bay OΦ) ∅ Vxe Y_ hb μ Pκ he hh _ ha (empty_subset _) (fun z _=>hu z) _ hw j
 have he(tx:YΦ): (Vx ζμ false tx)=∫ i,Vxe i tx ∂μ:= rfl -- test if false if proof
 apply Hope.signs3 (P:=Xs.p) (X₀:=sΚ) (M:=radiusB x) (p:=p)
 · have hx: WΣ j= ∫ v,Nor.linkY Xs.p (Stilo.bay OΦ) (Y_ (Pκ v)) (radiusB x) j∂μ:=by unfold birth_v; rw [if_pos Y'Φ]; unfold Jade.earnX; rw [bay_beam, integral_indicator (textR_m ..)]
   have hy:Nor.linkY Xs.p (Stilo.bay OΦ) (fun j=> ∫ t,Y_ (Pκ t) j∂μ) (radiusB x) j= (∫ t,Nor.linkY Xs.p (Stilo.bay OΦ) (Y_ (Pκ t)) (radiusB x) j∂μ):=by
       have hp(a:Raid (Dwell (mid N B))): Nor.liftR Xs.p (Stilo.bay OΦ) (radiusB x) (a j)= (Nor.liftR Xs.p (Stilo.bay OΦ) (radiusB x) 1)*a j:=by unfold Nor.liftR Jet.composeCost; ring
       by_cases ht:j∈Wheat (camp (Stilo.bay OΦ)); · unfold Nor.linkY; simp_rw [if_pos ht,hp]; exact (hp (fun j=> ∫ t,Y_ (Pκ t) j∂μ)).trans (MeasureTheory.integral_const_mul (μ:=μ) (Nor.liftR Xs.p (Stilo.bay OΦ) (radiusB x) 1) (fun t=>Y_ (Pκ t) j)).symm
       unfold Nor.linkY; simp_rw [if_neg ht]; rw [integral_zero]
   change Signs Xs.p oG _ (WΣ j); rw [hx,←hy]; apply Prism.mint Bh; exact Eventually.of_forall (fun x=> by rw [Function.comp_apply, Feu.non_r]; exact congrArg (fun z:Cipher (mid N B)=>crumb z.val j) (he _).symm)
 · let A':= Mom.screen (G:=SU.group) oκ.val
   have hy:Tendsto A' (𝓝 0) (𝓝 0):=by simpa only [map_zero] using A'.continuous.tendsto 0
   have hk:∀ᶠ x in 𝓝 0,pingS Xs.p.threshold oκ.val (increment G x):=by
       have ht:∀ᶠ x in 𝓝 0,Forge.gyrate Dvh G x ∈ Hug:= (stickU ..).continuousAt.eventually ((Rue.open_l ..).mem_nhds ((Forge.born Dvh G).symm ▸ hw))
       filter_upwards [ht] with y hz; simpa [Feu.non_r,bay_beam] using hz.1
   filter_upwards [hy.eventually hk,hk] with v h1 h2; exact congrArg (fun z:Cipher (mid N B)=>crumb z.val j) (tunicOn V F Z U W P_ H uF w' D_ L0 Tp i k₀ k₁ A_ A₁ heV ss tK oκ Ky hT pT ζμ false _ _ h1 h2 (by intro i a b; unfold RG.increment; rw [Mom.screen_at,if_pos (show Mom.needed oκ.val i from ⟨a,b⟩)]))
include vtB
lemma turbid (G:YΦ)(ht:pingS Xs.p.threshold oκ.val G)(ζμ:ℝ) : I' (G,Tp)=Vx ζμ false G+Vx ζμ true G:=by
 have hT':(cook S (subtK (r:=r) S i).toLeft).flags=∅:=by rw [Feu.hu_p]; exact Feu.kflags _
 have hw : G∈ Hug:=by rw [bay_beam]; constructor; simpa using ht; simp
 let Bh:= tuntegral V F Z U W P_ H uF w' D_ L0 Tp i k₀ k₁ A_ A₁ heV η' ss tK SC' oκ D0 d0 J_ Bq Gq Ag Y'Φ Ky hT pT Q0r G ht
 have hp:= vtB.visor (G,Tp) (hT'.symm ▸ hw)
 exact ((integral_add_compl (textR_m (S:=S) Ω₀ ζμ Φ) Bh).trans ((phraseT (enough_r uF) _).trans hp)).symm
section
-- takes YPh through credentials
include vt
open Py.Riant
lemma tunworth (p:Xs.p.power=2)(t:Xs.p.order=6)(hb:Xs.p.B=radiusB x)(u:Xs.p.supportExponent=1): 0≤ WΣ₃ ∧ Trees.currency (radiusB x) 2 oκ.val * (∑ j:Finset (Dwell (mid N B)), Scree.tariff (KeyUp Xs.p) oG SC' j * WΣ₃ j) ≤ ZPay x*(Trees.currency (radiusB x) 3 oκ.val*(∑ j:Finset (Dwell (mid N B)), Scree.tariff Xs.p oG SC' j * WΣ j)):=by
 let K:=radiusB x; let D:=(1+(Hope.reel K oκ.val:ℝ)); have hz:0 ≤ D:=by unfold D; positivity
 have hf:= bondY V F Z M P_ w' J_ SC' uF D_ ζμ Bq Gq Ag i oκ -- tune shadow
 have hZ:0 ≤ ZPay x:=by unfold ZPay; have ht:=pos_C; positivity
 let B'':=(∑ j:Finset (Dwell (mid N B)), Scree.tariff Xs.p oG SC' j * WΣ j)
 have hp:0 ≤ B'':=sum_nonneg (fun i _=> mul_nonneg (by unfold Scree.tariff; positivity) (hf _))
 have hm:(∑ j:Finset (Dwell (mid N B)), Scree.tariff (KeyUp Xs.p) oG SC' j* WΣ₃ j) ≤ Stick Xs.p sΚ B'':=by
    unfold Stick; rw [hb]; change _≤ D^7* _; rw [show D^7=D*D^Xs.p.order from (by rw [t]; ring)]; unfold B''; rw [Finset.mul_sum]; apply sum_le_sum; intro j w
    by_cases he:j∈ Wheat (camp oκ.val)
    · exact (mul_le_mul_of_nonneg_right (Hope.bill3 (X₀:=sΚ) p K j he vt) (mul_nonneg (pow_nonneg hz _) (hf j))).trans_eq (by change (D*_)*(D^Xs.p.order*_)=_; ring)
    change _*(D^_*(WΣ j))≤ _; rw [show WΣ j=0 from ?_,mul_zero,mul_zero,mul_zero,mul_zero]; unfold birth_v; rw [if_pos Y'Φ]; unfold Jade.earnX
    apply MeasureTheory.integral_eq_zero_of_ae
    filter_upwards with v₀; by_cases hx:v₀∈QΞ; · rw [Set.indicator_of_mem hx]; exact if_neg he
    exact Set.indicator_of_notMem hx _

 have h1: Tollup (1/2) Xs.p sΚ ≤ Trees.currency K 1 oκ.val:=by unfold Tollup Trees.currency; rw [hb]; apply Real.exp_le_exp.mpr; exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
 have hx:= (growth_z _ (p0:=Xs.p) (by omega : Xs.p.B≤2*radiusB x) sΚ hp).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hZ) hp)
 refine ⟨fun i=> mul_nonneg (pow_nonneg hz _) (hf _), (mul_le_mul_of_nonneg_left (hm.trans hx) (Real.exp_pos _).le).trans_eq ?_⟩
 rw [show Trees.currency K 3 oκ.val=Trees.currency K 1 oκ.val * Trees.currency K 2 oκ.val from (by unfold Trees.currency; rw [←Real.exp_add]; congr 1; ring)]; change Trees.currency K 2 _*(ZPay x* Trees.currency K 1 _* B'') = ZPay x*(Trees.currency K 1 _*Trees.currency K 2 _* B''); ring
end

end
end YM.CF.Oath
end
