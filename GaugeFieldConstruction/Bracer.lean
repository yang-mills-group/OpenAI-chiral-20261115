import GaugeFieldConstruction.Kasol
import GaugeFieldConstruction.Garl
import GaugeFieldConstruction.Savio
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
  {d e η t z g b c A B':ℝ} {j k' m n l:ℕ}
  (V:Grace K R L)
  {x y0 β:ℝ}
  {r d':ℕ}
  (F:Pilot)
  {s u:ℝ}{q q':Chi}
  (D:Corset d q' u (6+2) k')(pV:BudgetPoint)
  {σ:ℝ}(Z:Pluck R)(U:Grasp V.U B d)(W:GivenX V U){Xs: GramM (mid N B)}{Y: GramM (mid P B)}{M:Sheep V U W G Y.J Xs.J (6+2) n A}(P_:∀ X: Support (Domain P B),Lend P B d X)(H:Muster G S x d T)
  {γ α:ℝ} (uF:Fend V H M Z F q Y.p Xs.p γ α j l r)
  {q'' q0 : ℝ}(w':Hive.Vista U Y.J.M Y.J.P P_ (6+2) M.q ((Fintype.card Play:ℝ)*q'') M.lot M.tone)
  (Fκ:FerryP H F K R D) (φ: Xs.p.power=k')
  {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}(D_: Girt.BaseL U G Y G₀ G₁ q' u)(L0: StageP V H Y Xs U)
  (Cp: Plume.Cord S)(K_:Fairy S (F.hat R x) Cp)(Tp:Ids (mid N B))(U':Pane (mid N B))(i:Roc (mid P B))(O:Ride S)(y:pingS (temp x) (Stilo.bay O) U')
  (Roδ :Support (Domain N B))(Roα :S.ratio.parent i.1.val.1 ∈ Roδ)
  {a a' s0:ℝ}(hx:a < s)(hu:0<a')(hu':a' < u)
  (Qp: Palot.fits (BranchX (r:=r) S (vast (k:=Z.N1*radiusB x) H) ((H.post+90)*radiusB x)) (subtK (r:=r) S i) O)
  (k₀ k₁:ℕ)(A_: Roof (mid N B) s s0 k₀ G₀)(A₁: Roof (mid P B) s s0 k₁ G₁)(heV:k₀+k₁ ≤ radiusB x)(η':l≤18)(ss:s ≤ s0)(tK:s0 < d)(hU:u< firstRadius SU.group) (hpZ:fiery SU.group x R.L < s)
  (hv:∀ (Q: Monk SU.group S), Chir Q x → ‖Q.z‖≤ F.hat R x → Bell S Q x T H.trot H.room H.post H.beta a a')
  (M₀ a0 C C' v w:ℝ)(R0:PlanS 6 Xs.p Y.p i O (cort U' Cp) (school (cort U' Cp) r H) T R M₀ a0 C C' v w r l x)
  {vK Kρ K₁ ε Bz:ℝ}
  (oθ:Find Xs.p Y.p 6 n x R.L)(Jp:PactH d u ε Bz q' (6+2) k' D)
  (F':Raid (Dwell (mid P B)))(Q CC:ℝ)(Xf:PressB Y.p i.1 (actionZ Y i) Q CC)(fF:∀ U,BedP Y.p U (actionZ Y i) i.1 F')(fP:∀ i,0≤ F' i)
  (r₂ r₃:Prism.Rock (mid P B))(p₂ p₃:Prism.Rock (mid N B))(zU:r₂∈ hue_I i.1.val.2)(zV:r₃∈ hue_I i.1.val.2)(hlim:Kρ*Xs.p.threshold*(1+(Heir.reach x:ℝ))<u)
  (X' Y₀:Support (Domain P B))
  (Qx:TailB→Support (Domain P B)→Toll (Iota G))(X00:∀ i x, Suite (badge _) (pinH G d true) (pinH G d false) x (Qx i x) (M.X i x))
  (hf:insideS X' x)(uX:mark_l S ((H.post+90)*radiusB x) X'≤ O)(sh: Short S Y.p i.1.val.2)(hK:0≤ Kρ)
open Py Stilo
open Trees Hake
open Lilt Jade
variable (Wm κ B'':ℝ)(J_:ℕ)(Bq: ↥(Sil S r)→Roc (mid P B)→↥(Jade.tale S (((H.loft+H.post+200)*radiusB x)) (luceL R J_ x))→Track (Ride S) (Raid (LeanV (Single (mid N B)))))(Gq:↥(Sil S r)→Roc (mid P B)→Track (Ride S) ℝ)(Ag:∀ i:↥(Sil S r), Jade.RopeX (c:=Wm) V F Z M P_ w' J_ B'' uF D_ i (Bq i) (Gq i) κ)
variable (pB:Stake.PondP V F x s u j l (6+2))(hT:0 < s)(pT:0<u)
variable{Zp:ℝ}(Q0r:Oise.BoldB (T:=T) (k:=6) (H:=H) Zp)
open Jade
variable (hz:SharpHerd M 3)(vr:Fend V (Muster3 H) (Sheep3 V (X:=Xs) (Y:=Y) M hz) Z F q (KeyUp Y.p) (KeyUp Xs.p) γ α j l r)(Dv:Girt.BaseL U G (Gram3 Y) G₀ G₁ q' u)
-- individual Stalk price
variable (A0: Palot.leaf (Site (Domain N B)))(Hp:A0.val=Lattice.halo (1000*radiusB x) {S.ratio.parent i.1.val.1})(δ:ℝ)(D0 D1 h:ℝ)
variable (hkC:CurrentWork V F Z U W P_ (Muster3 H) (Y:= Gram3 Y) (Xs:=Gram3 Xs) (M:=Sheep3 V (X:=Xs) (Y:=Y) M hz) vr w' Dv i A0 δ h D0 D1 5) (hq:0≤ h)
open Vow
variable (Ext: Pax (mid N B))(HX:∀ j, LullT V F Z M P_ w' uF D_ (subtK (r:=r) S i) (beamH j.val) (Ext j))(hΦ:∀ j, ¬(hostX (l:=(H.post+90)*radiusB x) S i).val⊆ j.val→ Ext j=0)
-- A0 Currency anchor post.L.
variable (hbK:Xs.p.B=radiusB x)(pμ:Xs.p.power=2)(hy:Xs.p.supportExponent=1)
include hkC HX hΦ Hp hq uF
include A_ A₁ hT pT L0 pB Ag Q0r ss tK η' heV oθ
include Tp pμ hy hbK
open Riant Vow
abbrev Paring := univ.filter fun j:Palot.leaf (Site (Domain N B))=> (hostX (l:= (H.post+90)*radiusB x) S i).val⊆ j.val
abbrev Porin :=∑ j∈Paring H i, Trees.currency (radiusB x) 3 j.val * joinV (Scree.tariff Xs.p (S.ratio.parent i.1.val.1) h) (birth_v F (H:=H) (X:=Xs) J_ δ Bq i j)
abbrev GCost:= Real.exp (2*(fortK:ℝ))
lemma cotStore (hB:B''=h) : TarKen (KeyUp Xs.p) (S.ratio.parent i.1.val.1) A0 h 2 (LodgeCost D0+ GCost* (ZPay x*Porin (R:=R) (Xs:=Xs) F H i J_ Bq δ h)) (leaps 6 3 3 * D1 + ZPay x*Porin (R:=R) (Xs:=Xs) F H i J_ Bq δ h) Ext:=by
 subst B''
 obtain ⟨C',g,tC,w,T,y,T',ph⟩:= tippling V F Z U W P_ H uF w' D_ L0 i k₀ k₁ A_ A₁ heV η' ss tK oθ Wm κ h J_ Bq Gq Ag pB hT pT Q0r hz vr Dv A0 Hp δ D0 D1 h hkC hq -- tune order
 let I:= S.ratio.parent i.1.val.1; let Yp:= KeyUp Xs.p; let Yg:= birth_v (H:=H) (X:=Xs) F J_ δ Bq i; let B₀(j:Palot.leaf (Site (Domain N B))):Raid (Dwell (mid N B)):= (1+(Hope.reel (radiusB x) j.val:ℝ))^Xs.p.order • Yg j
 let X:= (hostX (l:= (H.post+90)*radiusB x) S i).val
 let Tρ:=Scree.tariff Yp I h; let L₀:=Porin (R:=R) (Xs:=Xs) F H i J_ Bq δ h; let Z₀:=ZPay x
 have ha:I ∈ A0.val:= Hp.symm ▸ halo_subset _ _ (mem_singleton_self _)
 let H_b:= Paring H i; have hx(i')(g:i'∈ H_b):= tunworth (ζμ:=δ) V F Z U W P_ H uF w' D_ L0 Tp i k₀ k₁ A_ A₁ heV η' ss tK h hq i' κ Wm J_ Bq Gq Ag _ (HX i') (mem_filter.mp g).2 pB hT pT Q0r pμ oθ.order hbK hy -- tune args
 have hy:0 ≤ B₀:=fun j k=> mul_nonneg (by positivity) (bondY V F Z M P_ w' J_ h uF D_ δ Bq Gq Ag i j k)
 let Yx:= Yg;
 have hu:0≤Z₀:=by unfold Z₀ ZPay; have hp:=pos_C; positivity
 have hpay (P: Finset (Palot.leaf (Site (Domain N B))))(g:P ⊆H_b): (∑ j∈P, Esk Yp h 2 I j (B₀ j)) ≤ Z₀ * L₀:=by
    have he:= (sum_le_sum_of_subset_of_nonneg (f:=fun i=>Esk Yp h 2 I i (B₀ i)) g fun i v p=> mul_nonneg ((Real.exp_pos _).le) (sum_nonneg (fun j _=>mul_nonneg (show 0 ≤ Scree.tariff Yp I h j from by unfold Scree.tariff; positivity) (hy _ _))))
    apply he.trans; unfold L₀ Porin; rw [mul_sum]; apply sum_le_sum; intro i u
    have h':= (hx _ u).2; change Trees.currency Xs.p.B 2 _ *joinV _ _ ≤ _; rw [hbK]; exact h'
 let K0:= Ambush I A0; let g0:= steakK H i A0; let E0:= Exurbs I A0; let gE:= elk H i A0
 let TE:Vow.Aura (mid N B)→ Raid (Dwell (mid N B)):= fun t=> if t∈gE then T t+ B₀ t else 0
 have hf:g0 ⊆ H_b:= fun j p=> mem_filter.mpr ⟨mem_univ _,(mem_filter.mp p).2.1⟩
 have hh(g:Pane (mid N B))(UvQ:Ids (mid N B))(j)(p:j∈H_b)(u:pingS Xs.p.threshold j.val g) (t':Finset (Dwell (mid N B))): Signs Yp I (fun v=>crumb (Scant V F Z U W P_ H uF w' D_ UvQ i j δ false (increment g v)).val t') (B₀ j t') := tunprice V F Z U W P_ H uF w' D_ L0 UvQ i k₀ k₁ A_ A₁ heV η' ss tK h j κ Wm J_ Bq Gq Ag (mem_filter.mp p).2 pB hT pT Q0r g u pμ u t' -- tune order
 have hp(x:Pane (mid N B))(T:Ids (mid N B))(j)(p:j∈H_b)(w:pingS Xs.p.threshold j.val x): Ext j (x,T)=Scant V F Z U W P_ H uF w' D_ T i j δ true x+ Scant V F Z U W P_ H uF w' D_ T i j δ false x:= (turbid V F Z U W P_ H uF w' D_ L0 T i k₀ k₁ A_ A₁ heV η' ss tK h j κ Wm J_ Bq Gq Ag _ (HX j) (mem_filter.mp p).2 pB hT pT Q0r x w δ).trans (add_comm ..)
 let Ψ (v:Bool) (Tp:Ids (mid N B))(j:Palot.leaf (Site (Domain N B))):= Scant V F Z U W P_ H uF w' D_ Tp i j δ v
 have he_Z(i:Hos S r):True:= trivial -- unnecessary
 let H':=hostX (l:=(H.post+90)*radiusB x) S i
 have hT' : 0≤ Z₀ * L₀:= le_trans (le_of_eq (show 0=(∑ i ∈ (∅:Finset (Aura (mid N B))), Esk Yp h 2 I i (B₀ i)) from (by rw [Finset.sum_empty]))) (hpay _ (empty_subset _))
 have hb: Esk Yp h 2 I A0 C' ≤ LodgeCost D0:=by unfold Esk; rw [show Yp.B=radiusB x from hbK]; exact tC
 have he: ∑ i ∈ elk H i A0, Esk Yp h 2 I i (T i)≤ leaps 6 3 3 * D1:=by unfold Esk; rw [show Yp.B=radiusB x from hbK]; exact T'
 have hg:= TarKen.palace (P:=Yp) (h:=h) (B:=B₀) (W:=T) (X1:=H') (F:=Ext) (X':=Ψ false) (K:=Ψ true) ha (hail_o S i) g0 gE rfl rfl hΦ (fun j v=> fun Tp U u=> hp _ _ j (mem_filter.mpr ⟨mem_univ _,v⟩) u) hy hb g (fun Tp U=>w Tp U) y he (fun i p _ u V=>ph _ p V u) (fun i p=> hpay i fun t v=>mem_filter.mpr ⟨mem_univ _,p t v⟩) (fun j g Tp U v=> hh U Tp j (mem_filter.mpr ⟨mem_univ _,g⟩) v) hq
 apply hg.shift _ le_rfl; apply add_le_add_right; refine mul_le_mul_of_nonneg_right ?_ hT';
 have ht:coverNumber (radiusB x) A0.val ≤ fortK:=by rw [Hp]; exact Corona.tile _ _ _ (by have he:=uF.fireK.blade; omega)
 unfold Trees.currency GCost; change Real.exp (2*(coverNumber Xs.p.B A0.val:ℝ))≤ _; rw [hbK]; apply Real.exp_monotone; exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ht) (by norm_num)
omit hkC Hp HX hΦ
variable (Vo:Site (Domain N B))(hr:A0.val=Lattice.halo (1000*radiusB x) {Vo})
-- subset paying. β uniform. Parent.Seat.Solar. Parameter κ=5. Uses ν accounting from P13.
variable (Q0 Q1:Roc (mid P B)→ℝ)(Kf:Roc (mid P B)→Pax (mid N B))(I:Finset (Roc (mid P B)))(sH:∀ x∈I,S.ratio.parent x.1.val.1=Vo)(hs:∀ x∈I,∀ i,LullT V F Z M P_ w' uF D_ (subtK (r:=r) S x) (beamH i.val) (Kf x i))(vFS:∀ i∈I,∀ j, ¬(hostX (l:=(H.post+90)*radiusB x) S i).val⊆ j.val→ Kf i j=0)(KQ:∀ i∈I, CurrentWork V F Z U W P_ (Muster3 H) (Y:= Gram3 Y) (Xs:=Gram3 Xs) (M:=Sheep3 V (X:=Xs) (Y:=Y) M hz) vr w' Dv i A0 δ h (Q0 i) (Q1 i) 5)
-- variable x shadow in vFS uses no local `x`; only sH.OK
variable (wK v₀:ℝ)(e₀:0<v₀)(hnQ:0≤wK)(hν:∀ (i:Roc (mid P B))(Y0:Palot.leaf (Site (Domain N B))), (hostX (l:=((H.post+90)*radiusB x)) S i).val⊆Y0.val→(tour (S:=S) (F.hat R x)).real (text_r S (hostX (l:=((H.post+90)*radiusB x)) S i).val δ (F.hat R x)) ≤ coverNumber (radiusB x) Y0.val * wK) -- warmth constraint
include hν e₀ hnQ hs vFS hr KQ sH
abbrev Ivory (x hY W a:ℝ)(p k:ℕ):ℝ:= (wK*(backX a *reserveT p k (radiusB x) a))*W*(1-degreePrice (radiusB x) W 1)⁻¹
lemma gloved (hB:B''=h)(p:Xs.p.supportExponent+v₀+v₀+2=κ) :TarKen (KeyUp Xs.p) Vo A0 h 2 (LodgeCost (∑ i∈I,Q0 i) + GCost*(ZPay x*Ivory wK x h Wm v₀ Xs.p.power Xs.p.order)) (leaps 6 3 3 * (∑ i∈I,Q1 i) + ZPay x*Ivory wK x h Wm v₀ Xs.p.power Xs.p.order) (∑ i∈I,Kf i):=by
 subst B''
 have ht:= aurum_E V F Z M P_ w' J_ h uF D_ hq δ wK Bq Gq Ag v₀ e₀ hbK p hnQ hν Vo -- tune params
 let Uι(i):=Porin (Xs:=Xs) F H i J_ Bq δ h
 have hx:(∑ i∈I,Uι i)≤ Ivory wK x h Wm v₀ Xs.p.power Xs.p.order:=by
    let J:= Finset.univ.filter fun i:Roc (mid P B)=> S.ratio.parent i.1.val.1=Vo
    apply le_trans (b:=∑ j∈J,Uι j); -- use calc
    · refine sum_le_sum_of_subset_of_nonneg (fun i p=> mem_filter.mpr ⟨mem_univ _,sH _ p⟩) (fun i _ _=> sum_nonneg fun j v=>mul_nonneg (Real.exp_pos _).le ?_); refine sum_nonneg fun j _=> mul_nonneg ?_ ?_; · unfold Scree.tariff; positivity
      exact bondY V F Z M P_ w' J_ h uF D_ δ Bq Gq Ag _ _ _
    refine (le_trans (b:=∑ i:Roc (mid P B) with S.ratio.parent i.1.val.1=Vo,∑ j∈Paring H i,Real.exp (2*(coverNumber (radiusB x) j.val:ℝ))*Xs.p.mass j.val (joinV (Scree.tariff Xs.p Vo h) (birth_v F (H:=H) (X:=Xs) J_ δ Bq i j))) ?_ (ht.trans_eq ?_))
    · apply le_of_eq; apply sum_congr rfl; intro i p; unfold Uι Porin; refine sum_congr rfl fun j _=>?_; rw [(mem_filter.mp p).2,BudgetPoint.mass,hbK,hy]; rw [←mul_assoc,←Real.exp_add]; congr 2; unfold Trees.currency; ring_nf -- tune rw
    unfold Ivory; ring -- pow_zero category
 let H'(i):= GCost*(ZPay x*Uι i); let T0 i:=LodgeCost (Q0 i)+ H' i; let T1 i:=leaps 6 3 3 *Q1 i+ ZPay x*Uι i
 have hh:= TarKen.run Kf I T0 T1 (P:=KeyUp Xs.p) (o:=Vo) (QX:=A0) (h:=h) (a:=2) (hr.symm ▸ halo_subset _ _ (mem_singleton_self _)) (fun i g=> (sH _ g) ▸ cotStore V F Z U W P_ H uF w' D_ L0 Tp i k₀ k₁ A_ A₁ heV η' ss tK oθ Wm κ h J_ Bq Gq Ag pB hT pT Q0r hz vr Dv A0 (by rw [sH _ g]; exact hr) δ _ _ h (KQ i g) hq (Kf i) (hs i g) (vFS i g) hbK pμ hy rfl) -- transport cast
 have hc:0≤ ZPay x:=by unfold ZPay; have hp:= pos_C; positivity
 apply hh.shift; · unfold T0 LodgeCost H'; rw [sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,←Finset.mul_sum]; exact add_le_add_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx hc) (Real.exp_pos _).le) _
 unfold T1; rw [sum_add_distrib,←Finset.mul_sum, ← Finset.mul_sum]; exact add_le_add_right (mul_le_mul_of_nonneg_left hx hc) _

end
end YM.CF.Oath
end
