import GaugeFieldConstruction.Bisley
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Feu
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
variable (D:Corset d q' u (k+2) k')(pV:BudgetPoint)
variable {σ:ℝ}(Z:Pluck R)(U:Grasp V.U B d)(W:GivenX V U){Xs: GramM (mid N B)}{Y: GramM (mid P B)}{M:Sheep V U W G Y.J Xs.J (k+2) n A}(P_:∀ X: Support (Domain P B),Lend P B d X)(H:Muster G S x d T)
variable {γ α:ℝ} (uF:Fend V H M Z F q Y.p Xs.p γ α j l r)
local notation "LQ"=> ((H.post+90)*radiusB x)
-- CURRENT rods. step purchased.F.Shape representative static
local notation "H_X"=> F.hat R x
local notation "Y'"=> Y.p
variable {q'' q0 : ℝ}(w':Hive.Vista U Y.J.M Y.J.P P_ (k+2) M.q ((Fintype.card Play:ℝ)*q'') M.lot M.tone)
open Jet Plume Eire.Dress
namespace Corset
variable (Fκ:FerryP H F K R D) (φ: Xs.p.power=k')
variable{G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}(D_: Girt.BaseL U G Y G₀ G₁ q' u)(L0: StageP V H Y Xs U)
local notation "Φ"=> F.hat R x
local notation "tV"=> (temp x)
variable (Cp: Plume.Cord S)(K_:Fairy S (F.hat R x) Cp)(Tp:Ids (mid N B))(U':Pane (mid N B))(i:Roc (mid P B))(O:Ride S)(y:pingS (temp x) (Stilo.bay O) U')
local notation "N_"=> mid N B
local notation "vT"=> (Vmove x U')
local notation "W'"=> (Stilo.bay O)
local notation "sX"=> ArchL D_ uF.head.scaleP H
variable (Roδ :Support (Domain N B))(Roα :S.ratio.parent i.1.val.1 ∈ Roδ)
local notation "I_"=> lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x)
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
variable (h:ℝ)(C1:ℝ)(F':Finset (Dwell (mid P B))→ℝ) (Xf:PressB Y.p i.1 (actionZ Y i) h C1)(fF:∀ U,BedP Y.p U (actionZ Y i) i.1 F')(fP:∀ i,0 ≤ F' i)(γ1:∑ i':Finset (Dwell (mid P B)), Scree.tariff Y.p i.1.val.1 h i' * F' i' ≤ C1)
variable (oθ:Find Xs.p Y.p k n x R.L) (Xc:SkyC k C) (hM:1 ≤ M₀)(ha:1 ≤ a0)
local notation "Lφ"=> meritT C Xc Y.p (i.1.val.2) H.post M₀ a0
open Eire.Dress
variable (Qx:TailB→Support (Domain P B)→Toll (Iota G))(Qv: Grave→Support (Domain P B)→Toll (Iota G)) (v0:RoofT V (M_:=M) Qx Qv)
local notation "θ"=> (Wheat (camp i.1.val.2))
local notation "K_X"=> (Finset (Dwell (mid P B)))
local notation "αL"=> (actionZ Y i ∘ Hv)
local notation "Ξo"=> Jade.loam V F Z M P_ w' uF D_ Ξ O
local notation "Yo"=> (hostX (l:=LQ) S i).val
local notation "£"=> (vT ∘ I_)
local notation "pR"=> (Xf)
-- TECH parent. ℓ splits isolate φ ALL match.M.Tram
local notation "TL"=> (LeanV (Single (mid P B)))
local notation "LA"=> (fun z:n₀=>lump θ (fun i=>crumb (αL z).val i) (Yx (£ z)) O Yo)
local notation "LD"=> (fun z:n₀=>lump θ (fun i=>Pastry.crumb (exp (αL z) -1-αL z).val i) (Yx (£ z)) O Yo) -- αL precedence
variable (sQ tQ:ℝ)
local notation "C'P"=> population*(A*followV [] G.count)
local notation "P₁"=> population*M.r1
local notation "Bz"=> Coin_ ((4:ℝ)^n*tQ) (population*(A*followV [] G.count)) (population*M.r1) sQ (l+90) (k+2)
open Trees
local notation "Xv'"=> Scree.tariff Xs.p o tQ
variable (pT:0 ≤ tQ)(pa:0 ≤ sQ)(p: sQ*2*Yaw.χ (l+90) ≤ (radiusB x)* M.r0)
local notation "PF"=> (Scree.tariff Y.p i.1.val.1 h)
local notation "ir"=> (0:n₀)
local notation "Fvz"=> (Lφ • F' : Raid (Dwell (mid P B)))
local notation "S2'"=> Rue.saber (Lφ • F') 2
variable (g' :0 ≤ h) (b':ℝ) (hh:0 ≤ b')(hb:b' ≤1)(vY:0 ≤ Coin_ ((4:ℝ)^n*tQ) (population*(A*followV [] G.count)) (population*M.r1) sQ (l+90) (k+2))(hp:Coin_ ((4:ℝ)^n*tQ) (population*(A*followV [] G.count)) (population*M.r1) sQ (l+90) (k+2)≤ b'*h)
local notation "tA"=> (Lφ*C1)
local notation "tB"=> Real.exp tA*tA^2
local notation "SV"=> Track (Ride S) (Raid (Dwell (Scree.mid N B)))
-- exclude hM and X dependencies when not needed. Quant FY
local notation "Yc"=> Xc.zip
include pT pa p uF oθ v0
include hh hb vY hp hM ha fP g' γ1 w'
open Plume
variable (Yw:Finset (Finset (LeanV (Single (mid P B))))) (XK:Yw⊆ Wheat (camp i.1.val.2))
local notation "Fpe"=> (sign_l G S LQ (k+2) Qx)
local notation "Fsa"=> (sign_z G S LQ (k+2) Qv)
local notation "Sc_"=> (fun y I=> fun v : SV=> ScoreU k y I v Fpe Fsa Yo)
local notation "tQ'"=> (Scree.tariff Xs.p o tQ)
local notation "EA" y:max=> Strung Yo (rateT tQ' y) (radiusB x) sQ
local notation "CW"=> currency (radiusB x) sQ Yo
-- provisional principal output leftover. unflagged lite inherited.S.Status. PAY through all Werk.Health and Rank stamp. NF aperture (remove any later AFF). 
local notation "Pvp"=> (Short S Y.p i.1.val.2)
local notation "DHI"=> (kperm (Wheat (camp i.1.val.2)))
local notation "DIH"=> (perm_p (Wheat (camp i.1.val.2)))
local notation "LF"=> (fun y:n₀=>(Ξo ((£ y),Tp) Cp).val)
local notation "L1"=> (fun y:n₀=>lump DHI (fun i=>crumb (αL y).val i) (Yx (£ y)) O Yo)
local notation "Ø" => (∅:Finset (Dwell (mid P B)))
local notation "L0X"=> (fun y:n₀=>lump {Ø} (fun i=>crumb (αL y).val i) (Yx (£ y)) O Yo)
local notation "LX"=> (fun y:n₀=>lump DIH (fun i=>crumb (αL y).val i) (Yx (£ y)) O Yo)
local notation "£T"=> (fun y:n₀=> LF y- LX y)
local notation "Sc1"=> ScoreU k θ S2'
local notation "Sc2"=> sparkK C Xc R
omit hh hb vY hp γ1 pT pa p -- no fiscal proof yet Demand
variable (X0K X1K X2K X3K:Track (Ride S) (Raid (Dwell (mid N B)))) -- syntax
variable (R1:ScoreU k (kperm (Wheat (camp i.1.val.2))) (meritT C Xc Y.p i.1.val.2 H.post M₀ a0• F') X1K (sign_l G S ((H.post+90)*radiusB x) (k+2) Qx) (sign_z G S ((H.post+90)*radiusB x) (k+2) Qv) (hostX (l:=((H.post+90)*radiusB x)) S i).val)
variable (R2:ScoreU k (Wheat (camp i.1.val.2)) (meritT C Xc Y.p i.1.val.2 H.post M₀ a0• F') X2K (sign_l G S ((H.post+90)*radiusB x) (k+2) Qx) (sign_z G S ((H.post+90)*radiusB x) (k+2) Qv) (hostX (l:=((H.post+90)*radiusB x)) S i).val)
variable (RS:ScoreU k (Wheat (camp i.1.val.2)) (Rue.saber (meritT C Xc Y.p i.1.val.2 H.post M₀ a0 • F') 2) X3K (sign_l G S ((H.post+90)*radiusB x) (k+2) Qx) (sign_z G S ((H.post+90)*radiusB x) (k+2) Qv) (hostX (l:=((H.post+90)*radiusB x)) S i).val)
variable (Φp:ScoreU k ({∅}:Finset (Finset (Dwell (mid P B)))) (sparkK C Xc R • F') X0K (sign_l G S ((H.post+90)*radiusB x) (k+2) Qx) (sign_z G S ((H.post+90)*radiusB x) (k+2) Qv) (hostX (l:=((H.post+90)*radiusB x)) S i).val) (AAp:PhysicalNext.JointLoad.Heir.Short S Y.p i.1.val.2→ Siete.Acceptance Y.p i.1.val.2 i.1.val.1 (fun V'=> crumb (actionZ Y i V').val ∅) (F' ∅))
section
include Roα φ Fκ K_ y oθ ha hM Xf fF K_ Yw v0 hu hu' heV η' hU hpZ hv hx Qp D_ L0 R0 RS A_ A₁
omit Yw
lemma lampTₛ: Woody k LD 0 (X3K O) :=by
 let hp:= ready_tₛ V F D Z U W P_ H uF w' Fκ φ D_ L0 Cp K_ U' i O y Roδ Roα Qp M₀ a0 C C' v w R0 h C1 F' Xf fF oθ Xc hM ha -- tune
 exact RS O _ _ (monetₛ V F D Z U W P_ H uF w' Fκ φ D_ Cp K_ Tp U' i O y Roδ Roα hx hu hu' Qp k₀ k₁ A_ A₁ heV η' hU hpZ hv Qx Qv v0) (fun i _=> (Rue.waxen hp).haveP i)
include R2
lemma jetQtyₛ: Woody k LF 0 (X2K O+X3K O):=by
 let hp:= ready_tₛ V F D Z U W P_ H uF w' Fκ φ D_ L0 Cp K_ U' i O y Roδ Roα Qp M₀ a0 C C' v w R0 h C1 F' Xf fF oθ Xc hM ha; have he: Woody k LA 0 (X2K O):= R2 O _ _ (monetₛ V F D Z U W P_ H uF w' Fκ φ D_ Cp K_ Tp U' i O y Roδ Roα hx hu hu' Qp k₀ k₁ A_ A₁ heV η' hU hpZ hv Qx Qv v0) (fun i v=> hp.haveP i)
 have hz:= lampTₛ V F D Z U W P_ H uF w' Fκ φ D_ L0 Cp K_ Tp U' i O y Roδ Roα hx hu hu' Qp k₀ k₁ A_ A₁ heV η' hU hpZ hv M₀ a0 C C' v w R0 h C1 F' Xf fF fP oθ Xc hM ha Qx Qv v0 g' X3K RS; refine (he.addP hz).germ ?_; filter_upwards [beam_vₛ V F D Z U W P_ H uF w' Fκ φ D_ L0 Cp K_ Tp U' i O y Roδ Qp M₀ a0 C C' v w R0 h C1 Xf] with x p using p.symm
omit R2
include R1
lemma noLXₛ: Woody k (fun y:n₀=> LF y-LX y-L0X y) 0 (X1K O+X3K O):=by
 let hp:= ready_tₛ V F D Z U W P_ H uF w' Fκ φ D_ L0 Cp K_ U' i O y Roδ Roα Qp M₀ a0 C C' v w R0 h C1 F' Xf fF oθ Xc hM ha; have hu₃: Woody k L1 0 (X1K O):= R1 O _ _ (monetₛ V F D Z U W P_ H uF w' Fκ φ D_ Cp K_ Tp U' i O y Roδ Roα hx hu hu' Qp k₀ k₁ A_ A₁ heV η' hU hpZ hv Qx Qv v0) (fun i v=> hp.haveP i)
 have hz:= lampTₛ V F D Z U W P_ H uF w' Fκ φ D_ L0 Cp K_ Tp U' i O y Roδ Roα hx hu hu' Qp k₀ k₁ A_ A₁ heV η' hU hpZ hv M₀ a0 C C' v w R0 h C1 F' Xf fF fP oθ Xc hM ha Qx Qv v0 g' X3K RS
 refine (hu₃.addP hz).germ ?_
 filter_upwards [beam_vₛ V F D Z U W P_ H uF w' Fκ φ D_ L0 Cp K_ Tp U' i O y Roδ Qp M₀ a0 C C' v w R0 h C1 Xf] with t hvv
 change L1 t + LD t=LF t-LX t-L0X t
 rw [show LF t=LA t+LD t from hvv, show LA t=L0X t+(LX t+L1 t) from ?_]; swap
 · dsimp only; unfold lump
   conv_lhs=> rw [← bredP i.1.val.2, sum_union (sealed i.1.val.2),sum_insert (sole i.1.val.2)]
   rw [add_assoc, Finset.sum_singleton]
 abel
end
open Stilo
local notation "s_"=> (Scree.mid N B)
local notation "Y'Q"=> (CW)
variable (ε δ:ℝ)(hs: Push.AbsoluteSums.Footprint.reserve Y.p.supportExponent sQ (Footprint.conversion S.ratio (H.post+90+5)) ε) (hP:Y.p.mass i.1.val.2 C1≤ δ)
include γ1 fF fP p pa pT g' oθ w' v0 uF hM ha Fκ hP hs hh hb hp vY L0 φ A_ A₁ η' hU hpZ hv hx hu hu' heV Xf
local notation "PE1"=> (Real.exp (sQ*Footprint.preCost (l+90+5))*ledgerP k n ε * (harp C Xc n l M₀ a0))
local notation "PXi"=> (Real.exp (-ε*coverNumber Y.p.B x0))
local notation "Xo4"=> (PXi*(PE1*(b'^4+Real.exp (PE1*δ)*(PE1*δ))) *Y.p.mass i.1.val.2 C1)
local notation "Xo0"=> (PXi*(PE1*(1+ Real.exp (PE1*δ)*(PE1*δ)))*Y.p.mass i.1.val.2 C1)
-- Quant existential receipt. From high and short.Core.Integral after Palm.Axis.Output Packs header momentum CLL! input Kn width Distances. Ranger.
abbrev vesselₛ(Tp:Ids (mid N B))(Cp:Cord S)(U':Pane (mid N B))(O:Ride S)(i:Roc (mid P B))(Roδ:Support (Domain N B))(p:n₀):= (Jade.loam V F Z M P_ w' uF D_ (subtK (r:=r) S i) O ((Vmove x U' (lineP Xs.p (S.ratio.parent i.1.val.1)  Roδ (radiusB x) p)),Tp) Cp).val
-- coordinate p: ∆ actual minus unresolved PH. threshold call retains $
abbrev residualₛ (A_:Ids (mid N B))(C_: Cord S)(U':Pane (mid N B))(O:Ride S)(i:Roc (mid P B))(Roδ:Support (Domain N B))(p:n₀): FC (LeanV (Single (mid N B))):=
 let U0:= Vmove x U' (lineP Xs.p (S.ratio.parent i.1.val.1)  Roδ (radiusB x) p); (Jade.loam V F Z M P_ w' uF D_ (subtK (r:=r) S i) O (U0,A_) C_).val-lump (perm_p (Wheat (camp i.1.val.2))) (fun i' => crumb (actionZ Y i (school (cort U' C_) r H U0)).val i') ((Stake.Grit D_ uF P_ w' (U0,A_) C_).heatT (subtK (r:=r) S i)) O (hostX (l:=((H.post+90)*radiusB x)) S i).val-lump {∅} (fun i' => crumb (actionZ Y i (school (cort U' C_) r H U0)).val i') ((Stake.Grit D_ uF P_ w' (U0,A_) C_).heatT (subtK (r:=r) S i)) O (hostX (l:=((H.post+90)*radiusB x)) S i).val
lemma rocketₛ(Kt:ℝ) : (∃ S0 S1: Track (Ride S) (Raid (Dwell (mid N B))),0 ≤ S0∧0 ≤ S1 ∧ Strung (hostX (l:=LQ) S i).val (rateT (Scree.tariff Xs.p o tQ) S0) (radiusB x) sQ Xo0 ∧ Strung (hostX (l:=LQ) S i).val (rateT (Scree.tariff Xs.p o tQ) S1) (radiusB x) sQ Xo4 ∧∀ (Cp:Cord S), Fairy S (F.hat R x) Cp→∀ (Tp:Ids (mid N B))(U':Pane (mid N B))(O:Ride S),pingS (temp x) (Stilo.bay O) U' → Palot.fits (BranchX S (vast (k:=(Z.N1*radiusB x)) H) ((H.post+90)*radiusB x)) (subtK (r:=r) S i) O → PlanS k Xs.p Y.p i O (cort U' Cp) (school (cort U' Cp) r H) T R M₀ a0 C C' v w r l x →∀ Roδ,S.ratio.parent i.1.val.1∈ Roδ→ Woody k (vesselₛ V F Z U W P_ H uF w' D_ Tp Cp U' O i Roδ) 0 (S0 O) ∧ (Woody k (residualₛ V F Z U W P_ H uF w' D_ Tp Cp U' O i Roδ) 0 (S1 O))) := by
 have vh:0 ≤ C1:=(sum_nonneg (fun j _=>mul_nonneg ((verge_l _ h g' Y.p).fee j) (fP _))).trans γ1
 obtain ⟨Gp_,h2,p2,r2⟩:= tallyIX V F Z U W P_ H uF w' i M₀ a0 C h C1 F' fP γ1 oθ Xc hM ha Qx Qv v0 sQ tQ pT pa p g' b' hh hb vY hp θ (Subset.refl _) 0 (fun i _=> Nat.zero_le _)
 obtain ⟨S1',h1,p1,r1⟩:= tallyIX V F Z U W P_ H uF w' i M₀ a0 C h C1 F' fP γ1 oθ Xc hM ha Qx Qv v0 sQ tQ pT pa p g' b' hh hb vY hp DHI (filter_subset ..) 4 (fun i p=> (mem_filter.mp p).2)
 obtain ⟨S3',h3,p3,r3⟩:= tallyN V F Z U W P_ H uF w' i M₀ a0 C h C1 F' fP γ1 oθ Xc hM ha Qx Qv v0 sQ tQ pT pa p g' b' hh hb vY hp
 refine ⟨Gp_+S3',S1'+S3',add_nonneg h2 h3,add_nonneg h1 h3,?_ ,?_,fun Cp K_ Tp U' O y Qp R0 Roδ Roα=>?_⟩
 · rw [tFit]; have hh:= p2.plus_l p3; refine ⟨hh.hand,hh.spear,hh.pay.trans ?_⟩; rw [←mul_add]; simp only [pow_zero,one_mul]; have h:=tribune V F Z U W H uF i M₀ a0 C C1 oθ Xc hM ha sQ ε hs vh δ hP 1 zero_le_one; simpa only [one_mul] using h
 · rw [tFit]; have hhP:= p1.plus_l p3; refine ⟨hhP.hand,hhP.spear,hhP.pay.trans ?_⟩; rw [←mul_add]; exact tribune V F Z U W H uF i M₀ a0 C C1 oθ Xc hM ha sQ ε hs vh δ hP (b'^4) (by positivity)
 exact ⟨jetQtyₛ V F D Z U W P_ H uF w' Fκ φ D_ L0 Cp K_ Tp U' i O y Roδ Roα hx hu hu' Qp k₀ k₁ A_ A₁ heV η' hU hpZ hv M₀ a0 C C' v w R0 h C1 F' Xf fF fP oθ Xc hM ha Qx Qv v0 g' Gp_ S3' r2 r3, noLXₛ V F D Z U W P_ H uF w' Fκ φ D_ L0 Cp K_ Tp U' i O y Roδ Roα hx hu hu' Qp k₀ k₁ A_ A₁ heV η' hU hpZ hv M₀ a0 C C' v w R0 h C1 F' Xf fF fP oθ Xc hM ha Qx Qv v0 g' S1' S3' r1 r3⟩
end Corset
end YM.CF.Feu

end
