import GaugeFieldConstruction.Herd
import GaugeFieldConstruction.VolumeShade
import SatinThinTrough

-- keep Flora from both primary inputs to the same Trough step
set_option autoImplicit false
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (Scree.mid N B) (Scree.mid P B)}{R:Patch}{L:ChartRatio SU.group}
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

variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (Scree.mid N B)}{Y: GramM (Scree.mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Nor
variable (U:Grasp V.U B d)(W:GivenX V U)(s0:ℕ)(I:Stake.Isle)(v_:SharpSheep V U W I A k p 3 s0)(e_:LocalRatio L) (t':1 < I.fine)
variable (q q':Chi)(u w' a h kL:ℝ)(h_:0 < A)(hw:0<a)(wS:scope_v a l R)(j_:l+100 ≤ j)(hL:6 ≤ k)(pL:2 ≤ p)(l0:5 ≤ l)(l1:l ≤18)
variable (hu:0 < kL)(wv:2*kL < firstRadius SU.group)(hx:h<d)(p0':0<u)(pv:u≤h)(M₀:ℕ)
variable (D_:Corset d q' kL (k+2) p)(Dμ m0 mC C C' wτ:ℝ)(Xc:SkyC k C)(hM:1 ≤ m0)(ha:1 ≤ mC)(Xp₀:SuitP k C')(Wol:0 ≤ wτ){κ0:ℝ}(Jp:PactH d kL (Xp₀.C*(R.L.val:ℝ)⁻¹^2) κ0 q' (k+2) p D_)
local notation "Sκ"=> a+2+2
local notation "Lφ"=> (a/4)
local notation "Zr"=> keyS (a+2+2) A 1 Xp₀.C l p k
local notation "Pδ"=> thermV (Sκ) m0 mC (a/4) Dμ Zr 2 Xc p l

open Neon
structure Fiords (F:Pilot)(Z:Pluck R)(q:Chi)(E₀:Tun I Z F ((tollE a)*100000))(k₀ M₀ n:ℕ)(vS dS u H PΨ ρ kC:ℝ)(Nheat:ℕ)(fog:ℝ→ℝ) :Prop where
 block(f g f' δ:ℝ→ℝ):sizeK R.L 2 f → sizeK R.L 2 g → sizeK R.L 2 f' → sizeK R.L 1 δ→ ∀ τ:ℝ→ℝ, sizeK R.L 1 τ → ∀ ag Cg:ℝ,0<ag → 0<Cg → ∀ J0:ℕ,∃ J₁:ℕ,J0≤ J₁ ∧ ∃ F' S' Dκ P₁:ℝ→ℝ,sizeK R.L 1 F'∧sizeK R.L k₀ S' ∧ Litt R 2 Dκ ∧ sizeK R.L 1 P₁ ∧∃ Qht hℓ:ℝ,∃ D_μ:ℝ→ℝ,0<hℓ ∧ sizeK R.L (k₀+1) D_μ ∧∃ Yζ:BudgetPoint,Yζ.supportExponent=a∧ Yζ.order=k ∧ Yζ.power=p∧∀ᶠ x:ℝ in atTop, TimΞ R.L k p l x hℓ (D_μ x) Yζ ∧ Stake.PondP V F x vS kL j l (k+2) ∧ 0< F' x∧degreePrice (radiusB x) (F' x) 1 ≤ 1/2∧∀ {N P:Side}(S:StepData (Domain N B) (Domain P B))(G:Ratio (Scree.mid N B) (Scree.mid P B))(T:Tube SU.group S)(A0:Scree.Loom (Scree.mid N B))(E:Scree.Loom (Scree.mid P B))(X:GramM (Scree.mid N B))(Y: GramM (Scree.mid P B)), Roof _ vS dS M₀ A0→ Roof _ vS dS M₀ E →(∀ F' U' V', JointB G (seine G F' q' kL U' (A0 V'), A0 V') dS) →∀ P0:Girt.BaseL U G Y A0 E q' kL,∀ {Z' γ:ℝ}, StatV V G T U W X Y Z' γ a x p k → n*radiusB x ≤ (Domain N B).val → ∃ (M:Sheep V U W G Y.J X.J (k+2) p A)(Hm:Muster G S x d T)(PP:∀ D:Lattice.Support (Domain P B), Lend P B d D) (t':ℝ)(ht:Vista U Y.J.M Y.J.P PP (k+2) M.q ((Fintype.card Play:ℝ)*t') M.lot M.tone), ρ=M.r0 ∧ M.height=Qht ∧ Sheet.isle M=I ∧ SharpHerd M 3 ∧ 1≤ t' ∧ ∃ Jz:ℕ,∀ (s:ℝ)(F0 F1:RegBudget (Scree.mid P B))(Q:ForceBudget (Scree.mid P B))(Wu:ℂ), let X':= Oise.color_b X (s+(Hm.ang+Hm.fee)) 0 0 0 0; let Uv:= Oise.color_b Y s F0 F1 Q Wu; Hm.ang=Z' ∧ Hm.fee=γ∧(StatV V G T U W X' Uv Z' γ a x p k → ∀ P_:Girt.BaseL U G Uv A0 E q' kL, StageP V (tint_z Hm s) Uv X' U ∧ ∃ τ':Fend V (tint_z Hm s) M Z F q Uv.p X'.p γ Z' j l (coming Z j l*radiusB x), SiteCost (j:=j) (l:=l) (X:=X') (Y:=Uv) V U W I q' a kL F Z q (tint_z Hm s) E₀ vS t' H ag Cg (τ x) (P₁ x) J₁ M PP ∧ (Arc_r Uv H (f x) (g x) (f' x) → (Oise.LookZ V (Xm:=X') (Xu:=Uv) M τ' P_ PP ht Jz (F' x) ((tolQ X.p).supportExponent+1) ∧ FluxShade (X:=X') (Y:=Uv) (zv:=F' x) V F Z M τ' P_ PP t' ht H Jz (a/4) a M₀ M₀ Nheat (fog x) vS dS) ∧ Clover (zv:=F' x) V F Z (X:=X') (Y:=Uv) M τ' P_ PP t' ht D_ H C' (δ x) Xp₀ Jp (PΨ*gritY R.L.val) (S' x) (Dκ x) ∧ Blush_X (X:=X') (Y:=Uv) V F Z M τ' P_ PP t' ht H kC hℓ (D_μ x) (S' x)))
variable (F:Pilot)(hQ:∀ᶠ x in atTop, FireK L q F R K l (k+2) j x)
variable (Hp:ℝ)(tH:1≤Hp)(uT:tollL R I Hp A (tollE a) k l ≤ Hp)(Wκ:ℝ→ℝ)(Kz N₀:ℕ)(uκ:sizeK R.L (Kz+1) Wκ)(Bv:Xp₀.C*(R.L.val:ℝ)⁻¹^2 ≤1)
variable (Wp:∀ (f:ℝ→ℝ),sizeK R.L 1 f→∀ᶠ x in atTop,HeatS V F U W I q q' l k p 1 m0 mC C C' wτ (a+2+2) (a/4) 0 0 (sliceK R.L (l+90) (k+2) (a+2+2) A ((4:ℝ)^p*1)) 1 Xc Xp₀ Dμ 1 kL D_ N₀ (f x) A Hp (Wκ x) (keyS (a+2+2) A 1 Xp₀.C l p k*gritY R.L.val) x)
include v_ hQ e_ h_ hw wS hL pL l0 l1 j_
include hu wv t' hx p0' pv V U W Wp hM ha Wol uκ tH uT Jp Bv
variable (kc:ℝ)(hKc:Tune.Stance k C kc)(pJ:4≤ K.j)(hkL:5 ≤ R.L.val)
include hKc pJ hkL
lemma totem_flux : ∃ M:ℕ,∃ Z:Pluck R,∃ Q:Tun I Z F ((tollE a)*100000), Fiords (j:=j) (l:=l) (A:=A) V U W I q' a kL D_ C' Xp₀ Jp F Z q Q Kz M₀ M u h kL Hp (Pδ) I.r0 kc N₀ Wκ:=by
 let hp:= model_b V U W (SharpSheep.terms V U W (p:=3) @v_) t'
 obtain ⟨y,N',Z,ε⟩:= plan_Θ V U W F I s0 3 v_ t' hL l0 l1 j_ q e_ p a hQ
 let Q:= F; let Wg:=tollE a; let P:=Wg*100000; let t':=tollL R I Hp A Wg k l; have hg:0 < Wg:= by unfold Wg tollE; linarith
 let X:=hQ.exists.choose_spec
 obtain ⟨K₀,N₁,H⟩:= Pig.earnWide V W.C.P P K.η K.C d u kL j k p p l I N' F p0' W.health hu wv hp.hs hp.g4 hp.g2 hp.g1 hp.g5 hp.g3 e_ X.gain l1 l0 j_ (by omega) pL Z q q' W.C.posP.le (by unfold P; positivity) V.applyK K.width (zero_le_one.trans V.up)
 obtain ⟨x,tQ⟩:=Oise.thirst V l j k l1 (by omega) F q
 let n0:=y+N₁+(j+j+102); have he:= riseV R I hp Hp A Wg k l (zero_le_one.trans tH) h_
 refine ⟨n0,N',K₀,⟨fun f g f' δ hf hg₁ hf' hδ τ hr a_g Cg hag hcG J0=>?_⟩⟩
 let w1:=a+1+1+1+1; let fnu:= fun x=>f x+g x+f' x
 let Y:= coming N' j l; obtain ⟨N'',pN⟩:= Wray.scaleDebt V F N' I K₀ Hp Hp t' Wg 0 w1 1 (a/4) fnu k j p (coming N' j l) l hp.g6 hp.g9 hp.g7 hp.p0 hp.g5 hp.g8 (zero_le_one.trans tH) (zero_le_one.trans he) le_rfl hg.le (by unfold Wg w1 tollE; linarith) (by unfold w1; linarith) zero_lt_one uT rfl ((hf.accrue hg₁).accrue hf')
 obtain ⟨E,w,q1⟩:= pN _ le_rfl
 obtain ⟨pc,Qv,c0,cq,Γ⟩:=Wray.sapI
 obtain ⟨Kμ,Φ⟩:=spirit_t F N' I K₀ Hp (a+1+1+1) Qv pc c0 k j p
 let FX(x):= LuneP N'.N1 (radiusB x) (Lilt.costC N'.N1 (radiusB x) k j p (a+1+1+1) (Lilt.roseP F N' I K₀ x (luceL R Kμ x) k Hp pc Qv))
 obtain ⟨Jq,hJ⟩:= volumeCredits V F N' I K₀ Hp Hp t' Wg 0 (a+1+1+1+1) 1 (a/4) τ k j p Y l hp.g6 hp.g9 hp.g7 hp.p0 hp.g5 hp.g8 (zero_le_one.trans tH) (zero_le_one.trans he) le_rfl hg.le (by unfold Wg tollE; linarith) (by positivity) zero_lt_one uT rfl hr (a_g/32) Cg (by positivity) hcG
 let Qq:= max J0 Jq; obtain ⟨Pc,Vc,rC⟩:= hJ Qq (le_max_right ..)
 let ΦX:=Py.pond_X k p a hL pL hw -- may need import.
 obtain ⟨vT,Hv,φb⟩:= ray_p R.L k p l Wκ ((uκ.low (show 1 ≤ _ by omega)).spine) ΦX -- spine.sizeK atLeast1.Now.
 refine ⟨Qq,le_max_left ..,E,fun x=>migrate (Wκ x) (E x) k p (radiusB x),FX,Pc,w,migrate_p _ _ _ w uκ _ _ (q1.mono fun x v=>⟨v.1,v.2.1⟩),Φ _ le_rfl,Vc,I.pay,vT,Wκ,Hv,uκ,ΦX,rfl,rfl,rfl,?_⟩
 filter_upwards [ε,hQ,q1,H N'',tQ,speedK (billX R.L), Work.E01.radiusB_tendsto.eventually_ge_atTop (M₀+M₀), evolve V F j l (k+2) p0' hu, (year SU.group R.L).eventually_gt_atTop 0, Wp δ hδ,(sizeK.fierce (R.L)).spine.eventually (gt_mem_nhds p0'), broadB (R:=R) F, fire_l F N' I K₀ Kμ pc Qv Γ k, H Qq,rC,φb, Tune.burn_ω (N₀:=N₀) (p:=p) (q:=q) V F l1 vT Hv (by omega:(2:ℕ)≤ k) pJ hkL] with i pη Fv c Cv v Rv hZ hy hX piH pUi U₀ Tw Vq Rq TK pVa
 refine ⟨TK,fun x=>hy x,c.1,c.2.1,?_⟩
 intro Ck B' S G T A0 E0 R0 X0 A₁ E₁ Xv D' a' γ b hB
 obtain ⟨M,tin,U',z,h0,r,Xxy⟩:= pη.earns b (le_trans (Nat.mul_le_mul_right _ (show y≤n0 by unfold n0; omega)) hB)
 obtain ⟨P_,wt⟩:= M.paint t' he; refine ⟨M,z,P_,t',wt,Eq.symm (congr_arg Stake.Isle.r0 U'),congrArg Stake.Isle.pay U',U',tin,he,N'',?_⟩
 intro Vt Q' H' X'' φ X2 Vu
 refine ⟨h0,r,?_⟩; intro b D'
 have hxo:X2=Oise.color_b R0 (Vt+(a'+γ)) 0 0 0 0:=by unfold X2; rw [h0,r];
 obtain ⟨H0,r⟩:= Xxy Vt Q' H' X'' φ (hxo ▸ b); rw [←hxo] at H0 r
 have hg:= b.hunt.scaleP; have hK:= Fv.blade; have hs:j+110<Y:=by unfold Y coming; omega
 let Y₂:= v M r ((Nat.mul_le_mul_right (radiusB i) (show j+j+102≤n0 from by unfold n0; omega)).trans hB); have p0:=Cv r ((Nat.mul_le_mul_right (radiusB i) (show N₁≤n0 from by unfold n0; omega)).trans hB) U' b.dose le_rfl b.down b.foot
 have hp0:= wS _ _ (ratio G) b.hunt.bill
 have hh: Footprint.reserve Vu.p.supportExponent (a+2+2) (Footprint.conversion S.ratio (l+90+5)) (a/4):=by
    rw [b.cult,hg]; refine ⟨by positivity,by positivity,(le_trans (add_le_add ?_ le_rfl) hp0.2.2)⟩
    apply mul_le_mul_of_nonneg_right (show a+2+2 ≤ tollE a from by unfold tollE; linarith); unfold Footprint.conversion Footprint.preCost; positivity
 obtain ⟨τt,θv,θu,Tk,Ω',h0P,hKκ⟩:=Tw
 have hE:FX i =LuneP N'.N1 (radiusB i) (Lilt.costC N'.N1 (radiusB i) k j X2.p.power (tolQ X2.p).supportExponent (Lilt.roseP F N' I K₀ i (luceL R Kμ i) k Hp pc Qv)):=by unfold FX tolQ; simp only [b.bill,b.down.hK]
 refine ⟨H0,r,⟨⟨_,Y₂⟩,Vq r ((Nat.mul_le_mul_right (radiusB i) (show N₁≤n0 from by unfold n0; omega)).trans hB) U' b.dose le_rfl b.down b.foot,?_⟩,fun t=>And.symm ?_⟩
 · intro Vg Vx B_v B_ e T₁ Y₁ Z' t Bη Wη g Qx Qv f m
   apply Rq S M P_ U' wt b.down.hU _ (Y:=Vu) (X:=X2) r Vg Vx B_v B_ e T₁ Y₁ Z' t Bη Wη g Qx Qv f m
   rw [b.cult,hg]; exact hp0

 apply and_assoc.mpr; rw [hE]; apply kind_shade V F N' I K₀ b M r U' H0 D' _ _ A₁ E₁ hZ (fun gX=> hy gX) (by linarith only [wv,hu]) p0' pv hx h_ P_ t' wt Y₂ D_ N₀ Hp m0 mC C C' wτ (a+2+2) _ _ _ Dμ Xc hM ha (by positivity) Xp₀ Wol piH Jp pUi U₀ rfl hh Bv Xv N'' p0 tH hp.hs (b.fee' ▸ Rv) e_ l1 (lt_of_lt_of_le (show 0 < SectorNext.Remainder.Scales.y SU.group R.L i/2 by exact half_pos hX) b.rest.1) (le_trans ?_ (Nat.mul_le_mul_right _ (show j+111 ≤ coming N' j l by omega))) ?_ t _ h0P hKκ pc Qv (luceL R Kμ i) c0 cq τt θv θu Tk Ω' vT Hv kc hKc pVa
 · simp_rw [Nat.add_mul]; omega
 · rw [←Nat.mul_assoc]; apply Nat.mul_le_mul_right; unfold coming; omega
 intro A B C D u' τ Y Z pξ Bη Wη e vC vW k'
 rw [show (tolQ X2.p).supportExponent=a+1+1+1 from by unfold tolQ; simp only [b.bill]]
 apply c.2.2 S (X:=X2) (Y:=Vu) M P_ U' wt b.down.hU _ r _ _ _ _ u' _ _ _ pξ _ _ e vC vW k'
 rw [b.cult,hg]; exact hp0
end YM.CF.Py

end
