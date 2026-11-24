import GaugeFieldConstruction.Montos
import GaugeFieldConstruction.Miscal
import GaugeFieldConstruction.Vraze
import GaugeFieldConstruction.Nocta
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
variable (W_X:Rill.Arch G d)(tW:W_X.val=1)(g':Seat (mid N B)→SU.E)(hh:Canvas Xs.p (S.ratio.parent i.1.val.1) (Heir.reach x) U' g' k Kρ)
lemma lineΔπ(r s:Rock (mid N B))(D E:Op SU.Slot) : lineY r s (D-E)=lineY r s D-lineY r s E:=by unfold lineY; simp only [Matrix.sub_apply,sub_smul, Finset.sum_sub_distrib]
abbrev Boot (C₄:ℝ) := (k+1:ℝ)*(wheel_l k * wheel_l k * Haro.horn^2 * C₄)
include uF X00 sh oθ zU zV hK tW hh hlim K_ Qp D_ Fκ hx hu hu' heV η' hU hpZ hv A_ A₁ φ Xf y
lemma spritzπ (Bb:Support (Domain N B))(Tq:tangD (mid N B)→ Op SU.Slot)(C₄:ℝ) (qA:Allows k Tq 0 (C₄*crack F' r₂ r₃)) (gY:Allows k ( (fun t=>Haro.CharM (actionZ Y i) r₂ r₃ (gauge (g' ∘ (ratio G).parent) (sailV (r:=r) (Xs:=Xs) H Cp U' i O t))) - Tq) 0 ((C₄*crack F' r₂ r₃)*ε)) (ht:ε ≤ 1)(h:O=Stilo.beamH (halo (1000*radiusB x) {S.ratio.parent i.1.val.1})): let Pπ:= fun X Yv z p q=> lyric G Jp.ink M.X (actionZ Y i) X Yv r₂ r₃ p q (sailV (r:=r) (Xs:=Xs) H Cp U' i O z) (isleΛ V F Z U W P_ H uF w' D_ Cp Tp U' i O z); let U:= fun X Y z p q=> litho G Jp.ink M.X X Y r₂ r₃ p q W_X g' (Tq z); let Vρ:= (crack F' r₂ r₃); let I:=γl x (Domain P B); Woody k (Brush Pπ I - Brush U univ) 0 (broomK (S:=S) Qx (Nexus₁ k C₄*ε*Vρ) I Bb ((H.post+90)*radiusB x) r₂ r₃ + broomK (S:=S) Qx (Boot (k:=k) C₄*Vρ) (univ\ I) Bb ((H.post+90)*radiusB x) r₂ r₃):=by -- tune shadow
 intro Vp Uμ Csp I
 let m:=(H.post+90)*radiusB x
 let Aq:= broomK (S:=S) Qx (Nexus₁ k C₄*ε*Csp) I Bb m r₂ r₃; let Vq:= broomK (S:=S) Qx (Boot (k:=k) C₄*Csp) (univ\I) Bb m r₂ r₃
 have hp:Woody k (Brush (Vp-Uμ) I) 0 Aq:=by
    refine brushMoney (Vp-Uμ) Qx I r₂ r₃ Bb (Nexus₁ k C₄*ε*Csp) m k (fun z₀ t p q l m =>?_) -- tune expected m shadow
    have hk:=stampπ V F D Z U W P_ H uF w' Fκ φ D_ Cp K_ Tp U' i O y hx hu hu' Qp k₀ k₁ A_ A₁ heV η' hU hpZ hv oθ Jp Q CC Xf r₂ r₃ p q zU zV hlim z₀.1 z₀.2 Qx X00 ((mem_filter.mp (mem_product.mp t).1).2) sh hK W_X tW g' hh Tq _ qA gY ht ((mem_filter.mp (mem_product.mp t).2).2) h l m
    rw [show Nexus₁ k C₄*ε*Csp=Nexus₁ k (C₄*Prism.crack F' r₂ r₃)*ε from (by unfold Csp Nexus₁; ring)]; exact hk
 have hu:Woody k (Brush Uμ (univ\I)) 0 Vq:=by
    refine brushMoney Uμ Qx _ r₂ r₃ Bb (Boot (k:=k) C₄*Csp) m k (fun a h x y i j=>?_)
    have hk:= Haro.LithAge G Jp.ink M.X a.1 a.2 r₂ r₃ x y W_X _ _ (X00 ..) (X00 ..) g' Tq qA; have he:= Rue.bare_p _ _ (cape_l _ hk i j)
    exact ⟨he.smooth,he.earned.trans (le_of_eq (by unfold Boot Csp; ring))⟩
 have he:= hu.ride (-1) (by simp); rw [neg_smul, one_smul] at he
 rw [show Brush Vp I-Brush Uμ univ=Brush (Vp-Uμ) I+-Brush Uμ (univ\I) from ?_]; exact hp.addP he
 ext1 y; change Brush Vp I y - Brush Uμ univ y= Brush (Vp-Uμ) I y+-Brush Uμ _ y
 let Y:= @univ (Support (Domain P B)×Support (Domain P B)) _; have hh: I ∪ (Y\I)=Y:= union_sdiff_of_subset (subset_univ _)
 have hz: Disjoint I (Y\I):= disjoint_sdiff; rw [show Brush Uμ univ y= Brush Uμ I y+Brush Uμ (Y\I) y from (by conv_lhs=> rw [show univ=(Y:Finset (Support (Domain P B)×Support (Domain P B))) from rfl,←hh,Brush,sum_union hz]; rfl)]
 rw [show Brush (Vp-Uμ) I y=Brush Vp I y-Brush Uμ I y from ?_]; abel
 unfold Brush; simp only [Pi.sub_apply,lineΔπ,sum_sub_distrib]
-- uniform κ from broomK on any p,q (cost aggregated, weights known via broom joinVsum); specialization MB. Common O derivatives/all Tp/f across purchases.
omit zU zV
abbrev Mβ (X:Support (Domain N B))(Vp:tangD (mid N B)→ Pane (mid P B))(U:tangD (mid N B)→ Rill.Arch G d) (J:Finset ((Support (Domain P B))×Support (Domain P B))) (O':Ride S)(z:tangD (mid N B)):=∑ s ∈ hue_I i.1.val.2,∑ t∈ hue_I i.1.val.2, ancient (G:=G) (S:=S) J (actionZ Y i) M.X Jp.ink s t ((H.post+90)*radiusB x) (Stilo.beamH X) (U z) (Vp z) O'
abbrev CoatScore (F':Raid (Dwell (mid P B)))(i:Roc (mid P B))(X:Support (Domain N B))(K:ℝ)(ε:ℝ) :Raid (Dwell (mid N B)):= let I:= γl x (Domain P B); let A:=(H.post+90)*radiusB x; ∑ p∈ hue_I i.1.val.2,∑ q∈ hue_I i.1.val.2,(broomK (S:=S) Qx (Nexus₁ k K*ε*crack F' p q) I X A p q + broomK (S:=S) Qx (Boot (k:=k) K*crack F' p q) (univ\I) X A p q)
-- check signature.Expensive unif; annotation
omit uF X00 sh oθ hK tW hh hlim K_ Qp D_ Fκ hx hu hu' heV η' hU hpZ hv A_ A₁ φ Xf y
section
-- include X00 separately later (no omit Id references)
include uF X00 sh oθ hK tW hh hlim K_ Qp D_ Fκ hx hu hu' heV η' hU hpZ hv A_ A₁ φ Xf y
lemma molten (Hp:Support (Domain N B))(Zt:Support (Domain N B))(hHp:Hp=Lattice.halo (1000*radiusB x) {S.ratio.parent i.1.val.1})(hOc:O=Stilo.beamH Hp)(ht:l=5)(hpZ':Zt=(hostX (l:= (H.post+90)*radiusB x) S i).val) (g:InkD (mid P B))(Vp:tangD (mid N B)→ Pane (mid P B))(hX:∀ z', Flour (camp i.1.val.2) (g (Vp z')).val)(C₄:ℝ) (hA:∀ a∈hue_I i.1.val.2,∀ b∈ hue_I i.1.val.2, let Tq:=fun z=>Haro.CharM g a b (Vp z); Allows k Tq 0 (C₄*crack F' a b) ∧ Allows k ( (fun t=>Haro.CharM (actionZ Y i) a b (gauge (g' ∘ (ratio G).parent) (sailV (r:=r) (Xs:=Xs) H Cp U' i O t))) - Tq) 0 ((C₄*crack F' a b)*ε)) (uQ:ε ≤ 1) : let LB:= Area (N:=N) (B:=B) Zt Hp; let L_:=γl x (Domain P B); let Qy:=Mβ (M:=M) (Xs:=Xs) (Y:=Y) V D U W H i Jp Zt (sailV (r:=r) (Xs:=Xs) H Cp U' i O) (isleΛ V F Z U W P_ H uF w' D_ Cp Tp U' i O) L_; Woody k ((∑ j∈LB,Qy (Stilo.beamH j.val))- fun z=> InjectPH g' (pulled G (bring Jp.ink W_X) M.X (orbitPH (g (Vp z))) univ)) 0 (CoatScore (k:=k) H Qx F' i Zt C₄ ε)∧∀ j':Palot.leaf (Site (Domain N B)), j'∉LB→ ∀ (X:tangD (mid N B)→ Pane (mid P B))(Yι:tangD (mid N B)→ Rill.Arch G d),Mβ (M:=M) (Xs:=Xs) (Y:=Y) V D U W H i Jp Zt X Yι L_ (Stilo.beamH j'.val)=0:=by -- tune M arg
 intro LB L_ Qy
 let I:=hue_I i.1.val.2; let J(a b:Rock (mid P B)):=fun z=>Haro.CharM g a b (Vp z)
 let S' (s t:Rock (mid P B))(X Yv z p q):= lyric G Jp.ink M.X (actionZ Y i) X Yv s t p q (sailV (r:=r) (Xs:=Xs) H Cp U' i O z) (isleΛ V F Z U W P_ H uF w' D_ Cp Tp U' i O z); let T' (s t:Rock (mid P B))(X Y z p q):= litho G Jp.ink M.X X Y s t p q W_X g' (J s t z); let Pk:= ((H.post+90)*radiusB x)
 have hs(a)(f:a∈I)(b)(z:b∈I):= spritzπ V F D Z U W P_ H uF w' Fκ φ D_ Cp K_ Tp U' i O y hx hu hu' Qp k₀ k₁ A_ A₁ heV η' hU hpZ hv oθ Jp F' Q CC Xf a b f z hlim Qx X00 sh hK W_X tW g' hh Zt (J a b) C₄ (hA a f b z).1 (hA a f b z).2 uQ (by rw [←hHp]; exact hOc)
 let Vq(a b:Rock (mid P B)):=Brush (S' a b) L_-Brush (T' a b) univ
 let A(a b:Rock (mid P B)) :Raid (Dwell (mid N B)):= (broomK (S:=S) Qx (Nexus₁ k C₄*ε*crack F' a b) L_ Zt ((H.post+90)*radiusB x) a b + broomK (S:=S) Qx (Boot (k:=k) C₄*crack F' a b) (univ\L_) Zt ((H.post+90)*radiusB x) a b)
 have he(P_:Rill.Arch G d)(Vx:Pane (mid P B))(a)(ha:a∈I)(b)(hb:b∈I):= hoard P_ M.X M.oddP Jp.ink ((H.post+90)*radiusB x) i.1 a b Qx X00 uF.head.scaleP (mem_filter.mp ha).2 (mem_filter.mp hb).2 Y.p sh oθ.hU (by have ht:=uF.fireK.blade; omega) (by rw [uF.pal.page,ht]) Hp hHp (actionZ Y i) Vx Zt hpZ'
 refine ⟨(Woody.sumV (B:=fun p=>∑ l∈I,A p l) (G:=fun p=>∑ l∈I,Vq p l) (S:=I) (fun s r=> Woody.sumV fun t k=> hs s r t k)).germ ?_, fun J W V X=>?_⟩
 · filter_upwards with q; let a' := Hp
   let U₁:= (isleΛ V F Z U W P_ H uF w' D_ Cp Tp U' i O q); let V₁:= (sailV (r:=r) (Xs:=Xs) H Cp U' i O q)
   have hx: (InjectPH g' (pulled G (bring Jp.ink W_X) M.X (orbitPH (g (Vp q))) univ))= ∑ p∈ I,∑ r∈I, Brush (T' p r) univ q:=by
       have hh:= moons (G:=G) Qx i.1 g' Jp.ink M.X W_X (Vp q) g (hX q) univ; rw [univ_product_univ] at hh -- tune
       exact hh
   have hf(j): Qy (Stilo.beamH (Subtype.val j)) q= ∑ a ∈ I,∑ b∈I, ancient (G:=G) (S:=S) L_ (actionZ Y i) M.X Jp.ink a b ((H.post+90)*radiusB x) (Stilo.beamH Zt) U₁ V₁ (Stilo.beamH (Subtype.val (j:Palot.leaf (Site (Domain N B))))) :=rfl
   change _=(∑ j∈ LB, Qy (Stilo.beamH j.val)) q -InjectPH g' (pulled G (bring Jp.ink W_X) M.X (orbitPH (g (Vp q))) univ); rw [hx]; simp_rw [Finset.sum_apply,Vq,Pi.sub_apply,sum_sub_distrib,hf]
   apply congrArg₂ (·-·) _ rfl; rw [sum_comm (s:=LB)]; apply sum_congr rfl; intro i' l; rw [sum_comm (s:=LB)]; apply sum_congr rfl; intro j v; exact ((he U₁ V₁ _ l _ v).1).symm
 funext y; unfold Mβ; apply sum_eq_zero; intro i p; apply sum_eq_zero; intro j v; exact (he _ _ _ p _ v).2 _ W -- shadow i
end

end
end YM.CF.Oath
end
