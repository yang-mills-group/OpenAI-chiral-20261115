import YM.CF.Tune.Earn
import YM.CF.Muse.Torus
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Tune
open Oath Moto
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
local instance textKK_P0 :MeasurableSpace (Finset (Sat S)):= ⊤
local instance textKK_P1 :MeasurableSingletonClass (Finset (Sat S)):=⟨fun _=>trivial⟩
local instance textKK_P2 :MeasurableSpace (List (Hos S r)):= ⊤
local instance textKK_P3 :MeasurableSingletonClass (List (Hos S r)):=⟨fun _=>trivial⟩
local instance textKK_P4 :Finite ↥(Sil S r):=Set.Finite.to_subtype Jade.sill_p
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
include A_ A₁ hT pT L0 Ky oθ Ag Q0r hRs uF ss tK η' pρ heV Tp Y'Φ vtB
local notation "pQ"=> ↥(Robe S Φ)
local notation "zP"=> ((Mx))
local notation "Tr"=> (Tg) -- collision!
local notation "Hug"=> (Rue.litres Xs.p.threshold (Stilo.bay OΦ) ∅)
variable (Aζ:Skate)(zW:∀ U':Pane (mid P B),pingS Y.p.threshold i.1.val.2 U'→ exp (actionZ Y i U')-1=Moto.plateZ i.1.val.1 Y.p Aζ U')(Kc Vq κA:ℝ)(St:Stance k C Kc)(dκ:0 ≤ κA)(uζ:Verc Aζ)(hζ:∀ i j,‖Aζ i j‖≤κA)(pK:S.ratio.embed (S.ratio.parent i.1.val.1)=i.1.val.1)(hK:Lattice.halo 2 {i.1.val.1}⊆ i.1.val.2)(hn_:20 < (Domain P B).val)(ζ_:Short S Y.p i.1.val.2)(Qκ: Taxi.DayT Y.p.order Vq)(hQ:0 ≤ Vq)
variable (Λρ:∀ (Cp:Cord S)(υ:Pane (mid N B)), Fairy S (F.hat R x) Cp→pingS (temp x) (Stilo.bay (Stilo.beamH oκ.val)) υ→Lilt.textP (hostX (l:=((H.post+90)*radiusB x)) S i).val Cp ζμ→ PlanS k Xs.p Y.p i (Stilo.beamH oκ.val) (cort υ Cp) (school (cort υ Cp) r H) T R M₀ a0 C C' v w r l x)
local notation "ζP"=> Kc*((R.L.val:ℝ)⁻¹)^4 * Moto.trotΦ Y.p κA Vq
local notation "KΨ"=> (if OΦ=(hO) then (Pi.single (∅:Finset (Dwell (mid N B))) (ζP):Raid (Dwell (mid N B))) else 0)
local notation "F0"=> (fun z:Pane (mid N B)=> I' (z,Tp))
omit A_ A₁ hT pT L0 Ky oθ Ag Q0r hRs uF ss tK η' pρ heV Tp Y'Φ vtB
include St dκ hQ
include A_ A₁ hT pT L0 Ky oθ Ag Q0r hRs uF ss tK η' pρ heV Tp Y'Φ vtB uζ hζ pK hK ζ_ Qκ hn_ Λρ zW φ Fκ
variable (Zr:ℝ)(zq:0≤ Zr)(Ξρ:∀ Cp:Cord S,Lilt.textP (hostX (l:=((H.post+90)*radiusB x)) S i).val Cp ζμ→ Fairy S (F.hat R x) Cp→ Tale.Wyth T i.1.val.2 (school (cort 1 Cp) r H) (S.ratio.parent i.1.val.1) Xs.p R.L Zr)
local notation "Fz"=> l_fee (Fintype.card (PlaqAxes×PlaqAxes)) Y.p Xs.p Zr κA
local notation "Xz"=> (qCorset Xs.p.threshold Y.p.threshold (R.L.val:ℝ))
local notation "Kz" I:max J:max=> ((↑(qCorset Xs.p.threshold Y.p.threshold (R.L.val:ℝ)):ℂ)*Aζ I J)
local notation "WΣ"=> (birth_v (H:=H) (X:=Xs) F J_ ζμ Bq i oκ)
local notation "HT"=> Scree.tariff Xs.p oG SC'
local notation "ZpK"=> (KΨ+ WΣ)
local notation "sσ"=> tonK (H:=H) i oκ Y'Φ
include hx hu hu' hv vt
omit Λρ vtB Y'Φ
variable (Xρ:ℝ)(wκ:0 ≤ Xρ)(dQ:ℝ)(he:0< dQ)(hk:Xs.p.B=radiusB x)(eK:Xs.p.supportExponent+dQ+dQ=D0)(hZX:∀ i:Roc (mid P B),(Jade.tour (S:=S) (F.hat R x)).real (text_r S (hostX (l:=((H.post+90)*radiusB x)) S i).val ζμ (F.hat R x)) ≤ Xρ* (coverNumber (radiusB x) (hostX (l:=((H.post+90)*radiusB x)) S i).val:ℝ))
local notation "dC"=> (backX dQ*reserveT Xs.p.power Xs.p.order (radiusB x) dQ)
local notation "mC"=> (d0*(degreePrice (radiusB x) d0 1)^0*(1-degreePrice (radiusB x) d0 1)⁻¹)
local notation "μC"=> Xρ*dC*mC
variable (o':Site (mid N B))(tO:S.ratio.parent i.1.val.1=Cube.node o')
local notation "TK" y:max=> ∑ j:HG,HT j * (birth_v (H:=H) (X:=Xs) F J_ ζμ Bq i y) j
local notation "ΛΨ"=> (hostX (l:=LQ) S i) -- notation ΛΨ dup.
variable (Wt:Palot.leaf (Site (Domain N B))→ Copy (mid N B))(Z0V:∀ j':Palot.leaf (Site (Domain N B)),LullT V F Z M P_ w' uF D_ (subtK (r:=r) S i) (Stilo.beamH j'.val) (Wt j'))
variable (U2:∀ (Yq:Monk SU.group S),∀ O:Ride S,(hostX (l:=(H.post+90)*radiusB x) S i).val⊆Stilo.bay O→ tight_p Yq i ζμ ((H.post+90)*radiusB x)→pingS (temp x) (Stilo.bay O) Yq.V→ PlanS k Xs.p Y.p i O Yq (school Yq r H) T R M₀ a0 C C' v w r l x)
structure Yearn (Wt:Palot.leaf (Site (Domain N B))→ Copy (mid N B))(b v0 X_:ℝ)(ρΘ:ℂ)(A:Skate): Prop where
 wave:∃ Bx:Palot.leaf (Site (Domain N B))→ℝ,0≤Bx ∧ (∀ y:Palot.leaf (Site (Domain N B)),∀ u: (hostX (l:=((H.post+90)*radiusB x)) S i).val⊆ y.val, PressB Xs.p (tonK (H:=H) i y u) (fun z=>Wt y (z,Tp)) SC' ((if y= (hostX (l:=((H.post+90)*radiusB x)) S i) then b else 0)+Bx y) ∧ (Hove.paid_M o' (Haro.orbitPH (Wt y (1,Tp))) Xs.p.power)*SC'^2≤ 2*Bx y) ∧(∀ I J:PlaqAxes, ‖Moto.tooth (S.ratio.parent i.1.val.1) Xs.p (fun z:Pane (mid N B)=> Wt (hostX (l:=((H.post+90)*radiusB x)) S i) (z,Tp)) I J - ρΘ*A I J‖ ≤ v0 + Bx (hostX (l:=((H.post+90)*radiusB x)) S i)) ∧ (∑ j:Palot.leaf (Site (Domain N B)) with (hostX (l:=((H.post+90)*radiusB x)) S i).val⊆ j.val,Xs.p.mass j.val (Bx j)) ≤ X_
 quiet (j: Palot.leaf (Site (Domain N B))): ¬(hostX (l:=((H.post+90)*radiusB x)) S i).val⊆ j.val→ Wt j=0
include hZX wκ he hk eK Z0V U2 Ξρ zq tO
lemma κ_pose: Yearn (Xs:=Xs) H Tp i SC' o' Wt (ζP) ((Fz)+ (Jade.tour (S:=S) (F.hat R x)).real (QΞ) * (‖((↑(Xz)):ℂ)‖*κA)) (μC) ((↑(Xz)):ℂ) Aζ:=by
 let B₁(y:Palot.leaf (Site (Domain N B)))(u: (ΛΨ).val⊆ y.val)(Cp:Cord S)(υ:Pane (mid N B))(_p: Fairy S (F.hat R x) Cp)(v:pingS (temp x) (Stilo.bay (Stilo.beamH y.val)) υ)(t:Lilt.textP ((ΛΨ).val) Cp ζμ):= U2 (cort υ Cp) (Stilo.beamH y.val) (by rw [bay_beam]; exact u) t v
 let Gc(j:Roc (mid P B))(p:Palot.leaf (Site (Domain N B))):= birth_v (H:=H) (X:=Xs) F J_ ζμ Bq j p; have hG:= bondY V F Z M P_ w' J_ SC' uF D_ ζμ Bq Gq Ag
 let Wς(p:Palot.leaf (Site (Domain N B))):ℝ:= ∑ j:Finset (Dwell (mid N B)),Scree.tariff Xs.p oG SC' j* Gc i p j -- Wς shadows GivenX
 let Qp(j:Roc (mid P B))(p:Palot.leaf (Site (Domain N B))) := ∑ u: Finset (Dwell (mid N B)),Scree.tariff Xs.p oG SC' u*Gc j p u
 have hX(i j g):0 ≤ HT g *Gc i j g:= mul_nonneg (by unfold Scree.tariff; positivity) (hG _ _ _)
 have Ht :0≤Wς := fun p=> sum_nonneg (fun i _=>hX _ _ _)
 refine ⟨⟨Wς,Ht,fun iκ y=>?_ ,fun I J=>?_ ,?_ ⟩,fun ℓ=>beam_blank V F Z U W P_ H uF w' D_ i ℓ _ (Z0V ℓ)⟩ -- W replace
 · obtain ⟨p1,p2⟩:= tot_W V F D Z U W P_ H uF w' Fκ φ D_ L0 Tp i hx hu hu' k₀ k₁ A_ A₁ heV η' ss tK hv M₀ a0 C C' v w oθ SC' vt hRs iκ D0 d0 J_ Bq Gq Ag pρ (Wt iκ) (Z0V iκ) y Ky hT pT Q0r Aζ zW Kc Vq κA St dκ uζ hζ pK hK hn_ ζ_ Qκ hQ (B₁ iκ y)
   let Mκ:= (earnX Xs.p Ω₀ ζμ (F.hat R x) x Z₂ WQ (fun z=> Bq z i) iκ); let Vκ:= (if Stilo.beamH iκ.val= (hO) then (Pi.single (∅:Finset (Dwell (mid N B))) (ζP): Raid (Dwell (mid N B))) else 0)
   have hp: Gc i iκ=Mκ:=if_pos y; constructor
   · let X0:=(if iκ= ΛΨ then ζP else 0); change PressB _ _ _ _ (X0+Wς iκ); apply Hope.hi_p p1; rw [pay_K V F D Z U W P_ H uF w' Fκ φ D_ L0 Tp i hx hu hu' k₀ k₁ A_ A₁ heV η' ss tK hv M₀ a0 C C' v w oθ SC' vt hRs iκ D0 d0 J_ Bq Gq Ag pρ (Wt iκ) (Z0V iκ) y Ky hT pT Q0r Aζ zW Kc Vq κA St dκ uζ hζ pK hK hn_ ζ_ Qκ hQ (B₁ iκ y)]; unfold Wς; rw [hp]; apply add_le_add _ le_rfl; unfold X0; split <;> rename_i hv -- fix
     · rw [if_pos (Subtype.ext ((bay_beam iκ.val).symm.trans ((congrArg Stilo.bay hv).trans (bay_beam _))))]
     split; rename_i v; exact lust_p (Y:=Y) (R:=R) C Kc Vq κA St dκ hQ; exact le_rfl
   have he(s r:Single (mid N B)): ‖orbitPH (Wt iκ (1,Tp)) s r‖≤ Gc i iκ (Haro.tray s r):=by -- tune WΣd replace
      have he:= Haro.ortho_l (tonK (H:=H) i iκ y) (fun z=>Wt iκ (z,Tp)) (Vκ+ Mκ) (p2 _) s r; rw [hp]; refine he.trans_eq ?_; rw [Pi.add_apply,show Vκ _=0 from ?_,zero_add]; unfold Vκ; split; exact Pi.single_eq_of_ne (by simp [Haro.tray]) _; exact rfl
   exact pinM o' _ (fun z:Pane (mid N B)=>Wt iκ (z,Tp)) (Gc i iκ) (hG _ _) (show (tonK (H:=H) i iκ y).val.1=node o' from tO) he vt (Wς iκ) le_rfl
 · let K0:= hostX (l:=((H.post+90)*radiusB x)) S i; have he:= earn_Φ V F D Z U W P_ H uF w' Fκ φ D_ L0 Tp i k₀ k₁ A_ A₁ heV η' ss tK M₀ a0 C C' v w oθ SC' hRs K0 D0 d0 J_ Bq Gq Ag pρ (Wt K0) (Z0V K0) (Subset.refl _) Ky hT pT Q0r Aζ zW Kc Vq κA St dκ uζ hζ pK hK hn_ ζ_ Qκ hQ (B₁ K0 (Subset.refl _)) Zr zq Ξρ I J rfl; apply he.trans; refine add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)) ?_
   · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hζ I J) (norm_nonneg _)
   apply le_trans _ (single_le_sum (f:=fun j:HG=> HT j*Gc i K0 j) (fun j _=>hX _ _ _) (mem_univ ∅)); rw [show HT ∅= 1 from (by simp [Scree.tariff,endL]), one_mul,show Gc _ K0=_ from if_pos (Finset.Subset.refl K0.val)]; -- tune
 · let D':= univ.filter (fun j:Roc (mid P B)=> S.ratio.parent j.1.val.1=oG); let Uo(j:Roc (mid P B)):= univ.filter (fun p:Palot.leaf (Site (Domain N B))=> (hostX (l:=LQ) S j).val⊆ p.val)
   refine (single_le_sum (f:=fun j:Roc (mid P B)=>∑ p∈Uo j, Xs.p.mass p.val (Qp j p)) (fun j _=> sum_nonneg fun i _=> mul_nonneg (Real.exp_pos _).le (sum_nonneg fun s _=> hX _ _ _)) (show i∈D' from (mem_filter.mpr ⟨mem_univ _,rfl⟩))).trans ?_
   exact Jade.hello_b V F Z M P_ w' J_ SC' uF D_ vt ζμ Xρ Bq Gq Ag dQ he hk eK wκ (fun i j h=> (hZX i).trans (by rw [mul_comm Xρ]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Corona.cover_mono h _)) wκ)) o -- tune
end
end YM.CF.Tune
