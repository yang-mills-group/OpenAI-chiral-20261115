import YM.CF.Oath.Gloria
import GaugeFieldConstruction.Hollow
import GaugeFieldConstruction.Vuoto
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
include X00
private lemma Merν {b:Bool}(Z:Rill.Arch G d)(f: paintL G r₂ p₂ (Qx (true,b) X')=0): fyL G b M.X (bring Jp.ink Z) X' r₂ p₂=0:=by
 ext i j; let V:= Qx (true,b) X'; let I:= (switchG G).symm; let W(a b:SU.Slot):= V (I (r₂,a)) (patchQ G (p₂,b))
 have hp(a b):0 ≤ W a b:=(X00 ..).nonn _ _; have hw(i j): W i j ≤ 0:=by rw [←f]; exact (single_le_sum (fun l (_:l∈(univ:Finset SU.Slot))=>hp i l) (mem_univ j)).trans (single_le_sum (fun j (_:j∈(univ:Finset SU.Slot))=>sum_nonneg (fun l (_:l∈(univ:Finset SU.Slot))=>hp j l)) (mem_univ i))
 change _=0; apply norm_le_zero_iff.mp; exact (((X00 ..).expo ..).bounded (bring Jp.ink Z)).trans (hw i j)
-- area bound to hitG
include uF zU sh hf oθ
lemma buyTruth (O':Support (Domain N B))(ht: O'=halo (1000*radiusB x) {S.ratio.parent i.1.val.1})(hp:H.post ≤18) (τ:Bool)(u: paintL G r₂ p₂ (Qx (true,τ) X')≠0): mark_l S ((H.post+90)*radiusB x) X' ≤ Stilo.beamH O':=by
 have vh:=uF.head.scaleP; obtain ⟨z,t,v⟩:= truthG M.X M.oddP (Qx (true,τ)) r₂ p₂ τ (X00 _) vh X' u
 let r:=S.ratio.parent i.1.val.1; have he(a: Site (Domain P B))(v':a∈X'): separation r (S.ratio.parent a)≤cirQ x:=by
    have g': separation (posG r₂) a < X'.card := v.lim _ z _ v'; refine (separation_triangle r (S.ratio.parent (posG r₂)) (S.ratio.parent a)).trans ?_
    rw [separation_comm r]; have h:=short_patch (B:=Y.p) sh oθ.hU i.1.property (mem_union_left _ (show posG r₂∈ i.1.val.2 from (mem_filter.mp zU).2)); unfold cirQ; have hx:= Work.E04.parent_separation S.ratio (posG r₂) a; unfold insideS at hf; unfold r; omega
 rw [ht]; unfold mark_l; apply (Stilo.beam_l _ _).2 -- tune
 intro i b; obtain ⟨y,k,d⟩:=halo_spec.mp b; obtain ⟨p,l,rfl⟩:=mem_image.mp k; refine halo_spec.mpr ⟨r, mem_singleton_self _, (separation_triangle ..).trans (le_trans (add_le_add (he _ l) d) ?_)⟩
 unfold cirQ; have hp': H.post*radiusB x≤18*radiusB x:= Nat.mul_le_mul_right _ hp; have he:=uF.fireK.blade; rw [Nat.add_mul]; omega
variable (W_X:Rill.Arch G d)(tW:W_X.val=1)(g':Seat (mid N B)→SU.E)(hh:Canvas Xs.p (S.ratio.parent i.1.val.1) (Heir.reach x) U' g' k Kρ)
abbrev windowK(z:tangD (mid N B)):= Vmove x U' (lineP Xs.p (S.ratio.parent i.1.val.1) (Stilo.bay O) (radiusB x) z)
abbrev sailV(z:tangD (mid N B)):= school (cort U' Cp) r H (windowK (Xs:=Xs) (S:=S) (x:=x) U' i O z)
abbrev isleΛ(z:tangD (mid N B)):= (Stake.Grit D_ uF P_ w' (windowK (Xs:=Xs) (S:=S) (x:=x) U' i O z,Tp) Cp).coats (subtK S i)
omit X00 uF zU sh hf oθ
abbrev Nexus₁(k:ℕ)(V:ℝ):ℝ:= (k+1:ℝ)*(7*wheel_l k^2*Haro.pole*Haro.horn^2*V)
include uF X00 zU sh hf oθ zV hK tW hh hlim
include K_ Qp D_ Fκ hx hu hu' heV η' hU hpZ hv A_ A₁ φ Xf y
lemma stampπ (Tq:tangD (mid N B)→ Op SU.Slot)(C₄:ℝ) (qA:Allows k Tq 0 C₄) (gY:Allows k ( (fun t=>Haro.CharM (actionZ Y i) r₂ r₃ (gauge (g' ∘ (ratio G).parent) (sailV (r:=r) (Xs:=Xs) H Cp U' i O t))) - Tq) 0 (C₄*ε)) (ht:ε ≤ 1) (hq:insideS Y₀ x)(h:O=Stilo.beamH (halo (1000*radiusB x) {S.ratio.parent i.1.val.1}))(l m:SU.Slot): Pence k (fun z=> ((lyric G Jp.ink M.X (actionZ Y i) X' Y₀ r₂ r₃ p₂ p₃ (sailV (r:=r) (Xs:=Xs) H Cp U' i O z) (isleΛ V F Z U W P_ H uF w' D_ Cp Tp U' i O z))- litho G Jp.ink M.X X' Y₀ r₂ r₃ p₂ p₃ W_X g' (Tq z)) l m) 0 (paintL G r₂ p₂ (Qx (true,true) X')*(paintL G r₃ p₃ (Qx (true,false) Y₀)*(Nexus₁ k C₄*ε))) := by
 by_cases f:paintL G r₂ p₂ (Qx (true,true) X')=0
 · have h0(P_): fyL G true M.X (bring Jp.ink P_) X' r₂ p₂=0:=Merν V D U W Jp r₂ p₂ X' Qx X00 P_ f -- tune order
   simpa only [lyric,litho,h0, star_zero,zero_mul,mul_zero,sub_zero,Matrix.zero_apply,f,norm_zero] using (show Pence k (fun _:Directions SU.group (Domain N B)=> 0) 0 ‖(0:ℂ)‖ from Pence.const ..)
 by_cases g:paintL G r₃ p₃ (Qx (true,false) Y₀)=0
 · have h0(P_): fyL G false M.X (bring Jp.ink P_) Y₀ r₃ p₃=0:=Merν V D U W Jp r₃ p₃ Y₀ Qx X00 P_ g
   simpa only [lyric,litho,h0, mul_zero,zero_mul,sub_zero,Matrix.zero_apply,g,norm_zero] using (show Pence k (fun _:Directions SU.group (Domain N B)=> 0) 0 ‖(0:ℂ)‖ from Pence.const ..)
 have ha:=uF.pal.page.trans_le η'
 have h1:= (hitG V F D Z U W P_ H uF w' Fκ φ D_ Cp K_ Tp U' i O y hx hu hu' Qp k₀ k₁ A_ A₁ heV η' hU hpZ hv oθ Jp W_X tW g' hh r₂ p₂ zU hlim X' Qx X00 hf (h.symm ▸ buyTruth V F Z U W H uF i oθ r₂ p₂ zU X' Qx X00 hf sh _ rfl ha true f) sh hK true f).2
 have h2:= (hitG V F D Z U W P_ H uF w' Fκ φ D_ Cp K_ Tp U' i O y hx hu hu' Qp k₀ k₁ A_ A₁ heV η' hU hpZ hv oθ Jp W_X tW g' hh r₃ p₃ zV hlim Y₀ Qx X00 hq (h.symm ▸ buyTruth V F Z U W H uF i oθ r₃ p₃ zV Y₀ Qx X00 hq sh _ rfl ha false g) sh hK false g).2
 have he:= (Rue.bare_p _ _ (glowπ G Jp.ink M.X i.1 (actionZ Y i) Xf (sailV (r:=r) (Xs:=Xs) H Cp U' i O) X' Y₀ r₂ r₃ p₂ p₃ (isleΛ V F Z U W P_ H uF w' D_ Cp Tp U' i O) W_X _ _ (X00 ..) (X00 ..) g' Tq h1 h2 qA gY ht l m))
 exact ⟨he.smooth,he.earned.trans (le_of_eq (by unfold Nexus₁; ring))⟩
end
end YM.CF.Oath
end
