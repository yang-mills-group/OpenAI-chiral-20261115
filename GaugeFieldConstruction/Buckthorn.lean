import YM.CF.Oath.Suit
import YM.CF.Oath.Gloria
import GaugeFieldConstruction.Bisley
set_option autoImplicit false
set_option maxHeartbeats 400000
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
section
variable
  {N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
  {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
  (V:Grace K R L)
  {x y0 β:ℝ}
  {r d':ℕ}
  (F:Pilot)
  {s u:ℝ}{q q':Chi}
  (D:Corset d q' u (k+2) k')(pV:BudgetPoint)
  {σ:ℝ}(Z:Pluck R)(U:Grasp V.U B d)(W:GivenX V U){Xs: GramM (mid N B)}{Y: GramM (mid P B)}{M:Sheep V U W G Y.J Xs.J (k+2) n A}(P_:∀ X: Support (Domain P B),Lend P B d X)(H:Muster G S x d T)
  {γ α:ℝ} (uF:Fend V H M Z F q Y.p Xs.p γ α j l r)
  {q'' q0 : ℝ}(w':Hive.Vista U Y.J.M Y.J.P P_ (k+2) M.q ((Fintype.card Play:ℝ)*q'') M.lot M.tone)
  (Fκ:FerryP H F K R D) (φ: Xs.p.power=k')
  {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}(D_: Girt.BaseL U G Y G₀ G₁ q' u)(L0: StageP V H Y Xs U)
  (Cp: Plume.Cord S)(K_:Fairy S (F.hat R x) Cp)(Tp:Ids (mid N B))(U':Pane (mid N B))(i:Roc (mid P B))(O:Ride S)(y:pingS (temp x) (Stilo.bay O) U')
  (Roδ :Support (Domain N B))(Roα :S.ratio.parent i.1.val.1 ∈ Roδ)
  {a a' s0:ℝ}(hx:a < s)(hu:0<a')(hu':a' < u)
  (Qp: Palot.fits (BranchX (r:=r) S (vast (k:=Z.N1*radiusB x) H) ((H.post+90)*radiusB x)) (subtK (r:=r) S i) O)
  (k₀ k₁:ℕ)(A_: Roof (mid N B) s s0 k₀ G₀)(A₁: Roof (mid P B) s s0 k₁ G₁)(heV:k₀+k₁ ≤ radiusB x)(η':l≤18)(ss:s ≤ s0)(tK:s0 < d)(hU:u< firstRadius SU.group) (hpZ:fiery SU.group x R.L < s)
  (hv:∀ (Q: Monk SU.group S), Chir Q x → ‖Q.z‖≤ F.hat R x → Bell S Q x T H.trot H.room H.post H.beta a a')
  (M₀ a0 C C' v w:ℝ)(R0:PlanS k Xs.p Y.p i O (cort U' Cp) (school (cort U' Cp) r H) T R M₀ a0 C C' v w r l x)
  {vK Kρ K₁ ε Bz:ℝ}
  (oθ:Find Xs.p Y.p k n x R.L)(Jp:PactH d u ε Bz q' (k+2) k' D)
  (F':Raid (Dwell (mid P B)))(Q CC:ℝ)(Xf:PressB Y.p i.1 (actionZ Y i) Q CC)(fF:∀ U,BedP Y.p U (actionZ Y i) i.1 F')(fP:∀ i,0≤ F' i)
  (r₂ r₃:Prism.Rock (mid P B))(p₂ p₃:Prism.Rock (mid N B))(zU:r₂∈ hue_I i.1.val.2)(zV:r₃∈ hue_I i.1.val.2)(hlim:Kρ*Xs.p.threshold*(1+(Heir.reach x:ℝ))<u)
  (X' Y₀:Support (Domain P B))
  (Qx:TailB→Support (Domain P B)→Toll (Iota G))(X00:∀ i x, Suite (badge _) (pinH G d true) (pinH G d false) x (Qx i x) (M.X i x))
  (hf:insideS X' x)(uX:mark_l S ((H.post+90)*radiusB x) X'≤ O)(sh: Short S Y.p i.1.val.2)(hK:0≤ Kρ)
  (J:Finset ((Support (Domain P B))×Support (Domain P B))) (h':J⊆ γl x (Domain P B))
  (Xc:SkyC k C) (hM:1 ≤ M₀)(ha:1≤ a0)


























section
include Roα uF oθ Jp φ D_ Fκ w' hU hx hu hu' heV A_ A₁ hv η' hpZ y Qp sh K_
include R0 L0 Xf fF hM ha X00
lemma coatVₛ : Woody k (fun y:( Directions SU.group (Domain N B))=> ( (ancient (G:=G) (S:=S) J ( (actionZ Y i)) M.X Jp.ink r₂ r₃ ( ((H.post+90)*radiusB x)) ( Stilo.beamH ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val)))) (( (fun iι:Directions SU.group (Domain N B)=> (( (fun U:Pane (mid N B)=> Stake.Grit D_ uF P_ w' (U,Tp) Cp)) (( (Vmove x U')) (( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x)) iι))).coats ( subtK (r:=r) S i))) y) (( (( school (Plume.cort (S:=S) U' Cp) r H) ∘ (( (Vmove x U'))∘ ( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x))))) y) O) 0 (( (mapK (S:=S) ( ((H.post+90)*radiusB x)) Qx r₂ r₃ ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val) (lip (k+2)^2*Prism.crack ( (( meritT C Xc Y.p (i.1.val.2) H.post M₀ a0)• F' :Raid (Dwell (mid P B)))) r₂ r₃) J)) O):=by
 have H0:= ready_tₛ V F D Z U W P_ H uF w' Fκ φ D_ L0 Cp K_ U' i O y Roδ Roα Qp M₀ a0 C C' v w R0 Q CC F' Xf fF oθ Xc hM ha
 have Hy:=order_hₛ V F D Z U W P_ H uF w' Fκ φ D_ Cp K_ Tp U' i O y Roδ Roα hx hu hu' Qp k₀ k₁ A_ A₁ heV η' hU hpZ hv
 let F_'(iZ jZ:( (Support (Domain P B))))(z:( Directions SU.group (Domain N B)))(p q:Rock (mid N B)):= lyric G Jp.ink M.X ( (actionZ Y i)) iZ jZ r₂ r₃ p q (( (( school (Plume.cort (S:=S) U' Cp) r H) ∘ (( (Vmove x U'))∘ ( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x))))) z) (( (fun iι:Directions SU.group (Domain N B)=> (( (fun U:Pane (mid N B)=> Stake.Grit D_ uF P_ w' (U,Tp) Cp)) (( (Vmove x U')) (( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x)) iι))).coats ( subtK (r:=r) S i))) z)
 exact begets (k:=k) O r₂ r₃ Qx J F_' _ ( ((H.post+90)*radiusB x)) ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val) (fun xν h v p q=>prism_r M.X Jp.ink Qx X00 (k+2) r₂ r₃ ( (fun iι:Directions SU.group (Domain N B)=> (( (fun U:Pane (mid N B)=> Stake.Grit D_ uF P_ w' (U,Tp) Cp)) (( (Vmove x U')) (( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x)) iι))).coats ( subtK (r:=r) S i))) ( (actionZ Y i)) ( (( school (Plume.cort (S:=S) U' Cp) r H) ∘ (( (Vmove x U'))∘ ( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x))))) ( (( meritT C Xc Y.p (i.1.val.2) H.post M₀ a0)• F' :Raid (Dwell (mid P B)))) 0 p q xν.1 xν.2 (by omega) D.can (Hy _ (v.symm ▸ le_trans le_sup_right le_sup_left)) (Hy _ (v.symm ▸ le_sup_right)) H0) -- tune
variable (Qv: Grave→Support (Domain P B)→Toll (Iota G))(Y00:∀ i x, Suite (badge _) (pinH G d true) (pinH G d true) x (Qv i x) (heal G d M.Y i x))

include Y00
lemma per_lₛ (p q:Single (mid P B)): Woody k (fun v=> frostM p q (( (fun iι:Directions SU.group (Domain N B)=> (( (fun U:Pane (mid N B)=> Stake.Grit D_ uF P_ w' (U,Tp) Cp)) (( (Vmove x U')) (( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x)) iι))).coats ( subtK (r:=r) S i))) v) M.Y Jp.ink ( ((H.post+90)*radiusB x)) ( Stilo.beamH ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val)) (orbitPH (( ((actionZ Y i) ∘ ( (( school (Plume.cort (S:=S) U' Cp) r H) ∘ (( (Vmove x U'))∘ ( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x))))))) v) p q) O) 0 ((( (doleK (S:=S) (G:=G))) p q ( ((H.post+90)*radiusB x)) Qv ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val) (k+2) (Worm p q ( (( meritT C Xc Y.p (i.1.val.2) H.post M₀ a0)• F' :Raid (Dwell (mid P B)))))) O) :=by
 have H0:= ready_tₛ V F D Z U W P_ H uF w' Fκ φ D_ L0 Cp K_ U' i O y Roδ Roα Qp M₀ a0 C C' v w R0 Q CC F' Xf fF oθ Xc hM ha
 have Hy:=order_hₛ V F D Z U W P_ H uF w' Fκ φ D_ Cp K_ Tp U' i O y Roδ Roα hx hu hu' Qp k₀ k₁ A_ A₁ heV η' hU hpZ hv
 have ht:=april p q _ k (0:( Directions SU.group (Domain N B))) ( (( meritT C Xc Y.p (i.1.val.2) H.post M₀ a0)• F' :Raid (Dwell (mid P B)))) H0
 exact master_p (p:=p) (q:=q) M.Y _ ( ((H.post+90)*radiusB x)) Qv Y00 ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val) (k+2) ( (fun iι:Directions SU.group (Domain N B)=> (( (fun U:Pane (mid N B)=> Stake.Grit D_ uF P_ w' (U,Tp) Cp)) (( (Vmove x U')) (( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x)) iι))).coats ( subtK (r:=r) S i))) _ D.can (by omega : k ≤ k+2) 0 O ht Hy -- tune
end

variable (Qv: Grave→Support (Domain P B)→Toll (Iota G))(Y00:∀ i x, Suite (badge _) (pinH G d true) (pinH G d true) x (Qv i x) (heal G d M.Y i x))







variable {Uq uT hκ oΦ : ℝ}(X00': RoofT V (M_:=M) Qx Qv)





variable (hpre_b:Uq*2*Yaw.χ (l+90) ≤ radiusB x*(M.r0/2))(po:0≤Uq)(pe':0≤ε)(vt:0≤ hκ)(hx':0<Q)(T_:∑ i':Finset (Dwell (mid P B)), Scree.tariff Y.p i.1.val.1 Q i'*F' i'≤CC)
open Trees








variable (q₃ ε':ℝ)(hr₀:Push.AbsoluteSums.Footprint.reserve Y.p.supportExponent Uq (Push.AbsoluteSums.Footprint.conversion S.ratio (H.post+90+5)) ε')






private lemma arithPi (t z y a q x r h p:ℝ) (u:0<p) : t*(r*(z*y))+z*q*x*(t*h^2*(a*y))≤ ((r+q*x*(h^2*a))/p^2)*z*(t*p^2*y):= le_of_eq (by field_simp <;> ring)

section
include X00' uF vt hpre_b po hM ha oθ fP pe'
include hr₀ T_ hx'
lemma wageDₛ : 0 ≤ ( (∑ s∈ hue_I ( (i.1.val.2)),∑ t∈ hue_I ( (i.1.val.2)),(( money_s (Y:=Y) H i M₀ a0 C F' Xc Qv) s t+ ( money (Y:=Y) H i M₀ a0 C F' Qx Xc) s t))) ∧ Strung ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val) (rateT ( Scree.tariff Xs.p ( S.ratio.parent i.1.val.1) hκ) ( (∑ s∈ hue_I ( (i.1.val.2)),∑ t∈ hue_I ( (i.1.val.2)),(( money_s (Y:=Y) H i M₀ a0 C F' Xc Qv) s t+ ( money (Y:=Y) H i M₀ a0 C F' Qx Xc) s t)))) (radiusB x) Uq ((( (( (( (Real.exp (Uq*Yaw.χ ( l+90))))*(lip (k+2)*( (population*M.r1))))) + ( (Real.exp (-( (( M.r0)/2))*(radiusB x:ℝ)))) * ( (lorp Uq ( l+90) Xs.p.power ( (population*(A*followV [] G.count)))))*(hκ^2*( (lip (k+2)^2)))))/Q^2)*(( currency (radiusB x) Uq ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val))*(( meritT C Xc Y.p (i.1.val.2) H.post M₀ a0)*CC))):=by
 let S':= hue_I ( (i.1.val.2)); let WR(s t:Rock (mid P B)):= ( money_s (Y:=Y) H i M₀ a0 C F' Xc Qv) s t+ ( money (Y:=Y) H i M₀ a0 C F' Qx Xc) s t
 have he:= oθ.hK.trans oθ.hL.symm; let A₀(iZ jZ:Rock (mid P B)):ℝ:=Haro.amt Y.p.power i.1.val.1 iZ jZ; -- shadow i lex! rename
 let Hbe(iμ j:Rock (mid P B)) :ℝ:= A₀ iμ j * ( Q^2)*( crack ( (( meritT C Xc Y.p (i.1.val.2) H.post M₀ a0)• F' :Raid (Dwell (mid P B))))) iμ j
 let g:= ( (( (( (( (Real.exp (Uq*Yaw.χ ( l+90))))*(lip (k+2)*( (population*M.r1))))) + ( (Real.exp (-( (( M.r0)/2))*(radiusB x:ℝ)))) * ( (lorp Uq ( l+90) Xs.p.power ( (population*(A*followV [] G.count)))))*(hκ^2*( (lip (k+2)^2)))))/Q^2))*( currency (radiusB x) Uq ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val))
 have hA(i j:Rock (mid P B)) : 1 ≤ A₀ i j := one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))
 have hT:= (sharp_m (l:=l) H i M₀ a0 C oθ Xc hM ha).1
 have ht:0 ≤ ( (( meritT C Xc Y.p (i.1.val.2) H.post M₀ a0)• F' :Raid (Dwell (mid P B)))):= smul_nonneg (zero_le_one.trans hT) fP
 have hp(i j:Rock (mid P B)):0 ≤ Hbe i j:=mul_nonneg (mul_nonneg (zero_le_one.trans (hA i j)) (by positivity)) (sum_nonneg fun i _=>sum_nonneg fun j _=>ht _)
 have hx:0 ≤ ( (lorp Uq ( l+90) Xs.p.power ( (population*(A*followV [] G.count))))):=by unfold lorp; rw [mul_assoc _ (flavor*_) _,←sq]; unfold flavor; positivity
 have hv:0≤( (( (Real.exp (Uq*Yaw.χ ( l+90))))*(lip (k+2)*( (population*M.r1))))):=by apply mul_nonneg (Real.exp_pos _).le (mul_nonneg (richP _) _); have hV:= M.mare; unfold population; positivity -- f'M
 have hu:0 ≤ levyC k 1 ε:=by have ht:=wheels_p (n:=k); have hz:= p0; have hp:=p1; unfold levyC θ_I; positivity
 have hc:0 ≤ ( currency (radiusB x) Uq ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val)):=(Real.exp_pos _).le; have hh: 0≤ g:=by unfold g; positivity
 have p₁(s₀ t₀)(h:s₀∈ S')(u:t₀∈ S'):0≤ WR s₀ t₀ ∧ Strung ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val) (rateT ( Scree.tariff Xs.p ( S.ratio.parent i.1.val.1) hκ) (WR s₀ t₀)) (radiusB x) Uq (g*Hbe s₀ t₀):=by
    obtain ⟨f,pP⟩:=purseV V F Z U W H uF i M₀ a0 C oθ F' fP s₀ t₀ h u Qx Xc hM ha Qv X00' hpre_b po pe' vt -- tune
    obtain ⟨bf,bq,vv,vQ⟩:=currencyP V F Z U W H uF i M₀ a0 C oθ F' fP s₀ t₀ h u Qx Xc hM ha Qv X00' hpre_b po pe' vt
    let I:=vQ; unfold WR; simp_rw [tFit]; have p:=pP.plus_l bq
    refine ⟨add_nonneg f bf,p.hand,p.spear,p.pay.trans ?_⟩
    let t:= A₀ s₀ t₀; rw [←show t=Haro.amt Xs.p.power i.1.val.1 s₀ t₀ from he ▸ rfl]; have hΔ: 0≤ (( crack ( (( meritT C Xc Y.p (i.1.val.2) H.post M₀ a0)• F' :Raid (Dwell (mid P B)))))) s₀ t₀:= sum_nonneg fun i _=> sum_nonneg fun j _=> ht _ -- tune ht name
    refine le_trans (add_le_add_left (le_mul_of_one_le_left (mul_nonneg hv (mul_nonneg hc hΔ)) (show 1 ≤ t from hA _ _)) _) ?_
    unfold g Hbe; change t*(( (( (Real.exp (Uq*Yaw.χ ( l+90))))*(lip (k+2)*( (population*M.r1)))))*(( currency (radiusB x) Uq ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val))*((( crack ( (( meritT C Xc Y.p (i.1.val.2) H.post M₀ a0)• F' :Raid (Dwell (mid P B)))))) s₀ t₀)))+( currency (radiusB x) Uq ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val))*( (Real.exp (-( (( M.r0)/2))*(radiusB x:ℝ))))*( (lorp Uq ( l+90) Xs.p.power ( (population*(A*followV [] G.count)))))*(t*hκ^2*(( (lip (k+2)^2))*((( crack ( (( meritT C Xc Y.p (i.1.val.2) H.post M₀ a0)• F' :Raid (Dwell (mid P B)))))) s₀ t₀)))≤ (( (( (( (Real.exp (Uq*Yaw.χ ( l+90))))*(lip (k+2)*( (population*M.r1))))) + ( (Real.exp (-( (( M.r0)/2))*(radiusB x:ℝ)))) * ( (lorp Uq ( l+90) Xs.p.power ( (population*(A*followV [] G.count)))))*(hκ^2*( (lip (k+2)^2)))))/Q^2)*( currency (radiusB x) Uq ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val))*(t*( Q^2)*((( crack ( (( meritT C Xc Y.p (i.1.val.2) H.post M₀ a0)• F' :Raid (Dwell (mid P B)))))) s₀ t₀))
    exact arithPi _ _ _ _ _ _ _ _ Q hx'

 have hh'(iμ)(v:iμ∈ S'):= sumsQ ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val) (radiusB x) S' (WR iμ) ( Scree.tariff Xs.p ( S.ratio.parent i.1.val.1) hκ) (fun j=> g*Hbe iμ j) (fun j p=> (p₁ iμ j v p).1) (fun j p=> (p₁ iμ j v p).2)
 have hy:= sumsQ ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val) (radiusB x) S' (fun i=>∑ j∈ S', WR i j) ( Scree.tariff Xs.p ( S.ratio.parent i.1.val.1) hκ) (fun i=>∑ j∈S',g*Hbe i j) (fun i p=>(hh' i p).1) (fun i p=>(hh' i p).2)
 refine ⟨hy.1,hy.2.hand,hy.2.spear,hy.2.pay.trans ?_⟩
 have hg :∑ i:Rock (mid P B),∑ j:Rock (mid P B), Hbe i j ≤ ( meritT C Xc Y.p (i.1.val.2) H.post M₀ a0)*CC:=by
    refine le_trans (pay_j _ _ _ ht hx'.le) ?_; apply le_trans _ (mul_le_mul_of_nonneg_left T_ (zero_le_one.trans hT)); rw [Finset.mul_sum]; exact sum_le_sum fun _ _=> Eq.le (mul_left_comm ..)
 calc
    _ ≤ ∑ i:Rock (mid P B),∑ j:Rock (mid P B), g*Hbe i j:= by apply le_trans _ (sum_le_sum_of_subset_of_nonneg (subset_univ S') fun i _ _=> sum_nonneg fun j _=> mul_nonneg hh (hp i j)); exact sum_le_sum fun i _=>sum_le_sum_of_subset_of_nonneg (subset_univ S') fun j _ _=> mul_nonneg hh (hp i j)
    _ ≤ _:=by simp_rw [← Finset.mul_sum]; exact (mul_le_mul_of_nonneg_left hg hh).trans_eq (mul_assoc ..)
end


private lemma XpCH {A I:Type*}[AddCommGroup A](S:Finset I)(F X P:I→I→A) :(∑ i∈S, ∑ j∈S,(F i j+X i j))=(∑ i∈S,∑ j∈S,F i j)+(∑ i∈S,∑ j∈S,X i j)+(∑ i∈S,∑ j∈S,P i j)-(∑ i∈S,∑ j∈S,P i j):= by simp_rw [Finset.sum_add_distrib]; simp
include Roα uF oθ Jp φ D_ Fκ w' hU hx hu hu' heV A_ A₁ hv η' hpZ y Qp sh K_ R0 L0 Xf fF hM ha X00 Y00 fP
lemma celtXₛ : Woody k (( (fun y:( Directions SU.group (Domain N B))=>Feu.Corset.lump (perm_p ( Wheat (camp ( (i.1.val.2))))) (fun i'=>crumb (( ((actionZ Y i) ∘ ( (( school (Plume.cort (S:=S) U' Cp) r H) ∘ (( (Vmove x U'))∘ ( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x))))))) y).val i') (( (fun U' : Pane (mid N B)=> (( (fun U:Pane (mid N B)=> Stake.Grit D_ uF P_ w' (U,Tp) Cp)) U').heatT ( subtK (r:=r) S i))) (( ( (Vmove x U')) ∘ ( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x))) y)) O ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val)))-( (fun y:( Directions SU.group (Domain N B))=> ∑ s∈ hue_I ( (i.1.val.2)),∑ t∈ hue_I ( (i.1.val.2)),ancient (S:=S) ( γl x (Domain P B)) ( (actionZ Y i)) M.X Jp.ink s t ( ((H.post+90)*radiusB x)) ( Stilo.beamH ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val)) (( (fun iι:Directions SU.group (Domain N B)=> (( (fun U:Pane (mid N B)=> Stake.Grit D_ uF P_ w' (U,Tp) Cp)) (( (Vmove x U')) (( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x)) iι))).coats ( subtK (r:=r) S i))) y) (( (( school (Plume.cort (S:=S) U' Cp) r H) ∘ (( (Vmove x U'))∘ ( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x))))) y) O))) 0 (( (∑ s∈ hue_I ( (i.1.val.2)),∑ t∈ hue_I ( (i.1.val.2)),(( money_s (Y:=Y) H i M₀ a0 C F' Xc Qv) s t+ ( money (Y:=Y) H i M₀ a0 C F' Qx Xc) s t))) O):=by
 let S':= hue_I ( (i.1.val.2)); let Fx(s t:Rock (mid P B))(xx:( Directions SU.group (Domain N B))):= crownM (S:=S) (( (fun iι:Directions SU.group (Domain N B)=> (( (fun U:Pane (mid N B)=> Stake.Grit D_ uF P_ w' (U,Tp) Cp)) (( (Vmove x U')) (( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x)) iι))).coats ( subtK (r:=r) S i))) xx) M.Y Jp.ink ( ((H.post+90)*radiusB x)) ( (actionZ Y i)) (( (( school (Plume.cort (S:=S) U' Cp) r H) ∘ (( (Vmove x U'))∘ ( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x))))) xx) ( Stilo.beamH ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val)) s t O; -- shadows x.Kinematics! rename
 let L(s t:Rock (mid P B))(xx:( Directions SU.group (Domain N B))):= ancient (S:=S) (univ\( γl x (Domain P B))) ( (actionZ Y i)) M.X Jp.ink s t ( ((H.post+90)*radiusB x)) ( Stilo.beamH ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val)) (( (fun iι:Directions SU.group (Domain N B)=> (( (fun U:Pane (mid N B)=> Stake.Grit D_ uF P_ w' (U,Tp) Cp)) (( (Vmove x U')) (( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x)) iι))).coats ( subtK (r:=r) S i))) xx) (( (( school (Plume.cort (S:=S) U' Cp) r H) ∘ (( (Vmove x U'))∘ ( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x))))) xx) O
 have hy(p q:Single (mid P B)):= per_lₛ V F D Z U W P_ H uF w' Fκ φ D_ L0 Cp K_ Tp U' i O y Roδ Roα hx hu hu' Qp k₀ k₁ A_ A₁ heV η' hU hpZ hv M₀ a0 C C' v w R0 oθ Jp F' Q CC Xf fF Qx X00 sh Xc hM ha Qv Y00 p q -- shadow F
 have hp(s t:Rock (mid P B))(kh:s∈S')(u:t∈S'): Woody k (Fx s t+ L s t) 0 ((( money_s (Y:=Y) H i M₀ a0 C F' Xc Qv) s t+ ( money (Y:=Y) H i M₀ a0 C F' Qx Xc) s t) O):=by
    have h': Woody k (Fx s t) 0 (( money_s (Y:=Y) H i M₀ a0 C F' Xc Qv) s t O):=by
       let W(iμ j:SU.Slot):= ( (doleK (S:=S) (G:=G))) (s,iμ) (t,j) ( ((H.post+90)*radiusB x)) Qv ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val) (k+2) (Worm (s,iμ) (t,j) ( (( meritT C Xc Y.p (i.1.val.2) H.post M₀ a0)• F' :Raid (Dwell (mid P B))))); let U(iμ j:SU.Slot)(xx:( Directions SU.group (Domain N B))):=frostM (S:=S) (s,iμ) (t,j) (( (fun iι:Directions SU.group (Domain N B)=> (( (fun U:Pane (mid N B)=> Stake.Grit D_ uF P_ w' (U,Tp) Cp)) (( (Vmove x U')) (( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x)) iι))).coats ( subtK (r:=r) S i))) xx) M.Y Jp.ink ( ((H.post+90)*radiusB x)) ( Stilo.beamH ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val)) (orbitPH (( ((actionZ Y i) ∘ ( (( school (Plume.cort (S:=S) U' Cp) r H) ∘ (( (Vmove x U'))∘ ( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x))))))) xx) (s,iμ) (t,j)) O
       have he(j:SU.Slot):= sum_W univ (W j) O (U j) 0 (fun i _=> hy (s,j) (t,i)); let Z(i)(v:( Directions SU.group (Domain N B))):=∑ j:SU.Slot,U i j v
       refine (sum_W univ (fun i:SU.Slot=>∑ j:SU.Slot,W i j) O Z 0 (fun i _=> he i)).germ ?_; filter_upwards with v; unfold Fx crownM; exact (doble O univ _).symm -- over‐simp RHS. tune
    have hx₀:= coatVₛ V F D Z U W P_ H uF w' Fκ φ D_ L0 Cp K_ Tp U' i O y Roδ Roα hx hu hu' Qp k₀ k₁ A_ A₁ heV η' hU hpZ hv M₀ a0 C C' v w R0 oθ Jp F' Q CC Xf fF s t Qx X00 sh (univ\( γl x (Domain P B))) Xc hM ha
    exact h'.addP hx₀
 let W_(s t:Rock (mid P B)):= (( money_s (Y:=Y) H i M₀ a0 C F' Xc Qv) s t+ ( money (Y:=Y) H i M₀ a0 C F' Qx Xc) s t); let U_(s t:Rock (mid P B)):= Fx s t+L s t
 have hh(i)(v:i∈ S'):= sum_W S' (W_ i) O (U_ i) 0 (fun j p=> hp i j v p); let X_(i:Rock (mid P B))(z:( Directions SU.group (Domain N B))):=∑ j∈S', U_ i j z
 refine (sum_W S' (fun i=>∑ j∈S',W_ i j) O X_ 0 hh).germ ?_
 filter_upwards with v; -- algebra. use Eq.LO.
 let f':= winH (S:=S) (( (fun iι:Directions SU.group (Domain N B)=> (( (fun U:Pane (mid N B)=> Stake.Grit D_ uF P_ w' (U,Tp) Cp)) (( (Vmove x U')) (( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x)) iι))).coats ( subtK (r:=r) S i))) v) M.X M.Y M.oddP Jp.ink ( ((H.post+90)*radiusB x)) ( (actionZ Y i)) i.1 (( (( school (Plume.cort (S:=S) U' Cp) r H) ∘ (( (Vmove x U'))∘ ( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x))))) v) ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val) Y.p Xf ( γl x (Domain P B)) O
 change _= ( (fun y:( Directions SU.group (Domain N B))=>Feu.Corset.lump (perm_p ( Wheat (camp ( (i.1.val.2))))) (fun i'=>crumb (( ((actionZ Y i) ∘ ( (( school (Plume.cort (S:=S) U' Cp) r H) ∘ (( (Vmove x U'))∘ ( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x))))))) y).val i') (( (fun U' : Pane (mid N B)=> (( (fun U:Pane (mid N B)=> Stake.Grit D_ uF P_ w' (U,Tp) Cp)) U').heatT ( subtK (r:=r) S i))) (( ( (Vmove x U')) ∘ ( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x))) y)) O ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val))) v-_ ; rw [show ( (fun y:( Directions SU.group (Domain N B))=>Feu.Corset.lump (perm_p ( Wheat (camp ( (i.1.val.2))))) (fun i'=>crumb (( ((actionZ Y i) ∘ ( (( school (Plume.cort (S:=S) U' Cp) r H) ∘ (( (Vmove x U'))∘ ( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x))))))) y).val i') (( (fun U' : Pane (mid N B)=> (( (fun U:Pane (mid N B)=> Stake.Grit D_ uF P_ w' (U,Tp) Cp)) U').heatT ( subtK (r:=r) S i))) (( ( (Vmove x U')) ∘ ( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x))) y)) O ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val))) v = _ from f']
 unfold current; rw [doble,doble,doble];
 change (∑ i∈ S',∑ j∈S', (Fx i j v+L i j v))= (_+_+_)-_
 let U(s t):= ancient (S:=S) ( γl x (Domain P B)) ( (actionZ Y i)) M.X Jp.ink s t ( ((H.post+90)*radiusB x)) ( Stilo.beamH ( (hostX (l:=( ((H.post+90)*radiusB x))) S i).val)) (( (fun iι:Directions SU.group (Domain N B)=> (( (fun U:Pane (mid N B)=> Stake.Grit D_ uF P_ w' (U,Tp) Cp)) (( (Vmove x U')) (( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x)) iι))).coats ( subtK (r:=r) S i))) v) (( (( school (Plume.cort (S:=S) U' Cp) r H) ∘ (( (Vmove x U'))∘ ( lineP Xs.p (S.ratio.parent i.1.val.1) Roδ (radiusB x))))) v) O
 exact XpCH S' (fun i j=> Fx i j v) (fun i j=> L i j v) U

end
end YM.CF.Oath
end
