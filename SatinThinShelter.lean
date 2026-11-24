import SatinThinSpanPH
import YM.CF.Brood.Tips
import YM.CF.Neon.Ten
import YM.CF.Neon.Hick
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
variable {N n B: Side} {P:BudgetPoint}{h Q A B₀ C:ℝ}{L:ℕ}
-- Geometry maturity V (on coarse side); pack for P1 eventual demands later.
structure HavenL (n:Side)(P:BudgetPoint)(L:ℕ) : Prop where
 period:4 ≤ (More n).val
 door:1<L
 pay:10 ≤ P.B
 rooms: ∀ i:Scree.Hub n,chose L P i→ Nonwrapping i.val.2 i.val.1
lemma regularRooms (p:4 ≤ (More n).val)(h:1<L)(g:10≤P.B)(v:10*(L*(4*P.B+2)+2*P.B)< (More n).val) : HavenL n P L:=by
 refine ⟨p,h,g,fun i t x u=>?_⟩
 apply lt_of_le_of_lt (Nat.mul_le_mul_left _ ((Corona.extent _ P.B u i.property).trans ?_)) v
 let k:= coverNumber P.B i.val.2; have hx:k≤ L:= by
    rcases Nat.eq_zero_or_pos k with hu|hu; rw [hu]; exact Nat.zero_le _
    change k^3<L at t; have hp:= Nat.pow_le_pow_left hu 2; nlinarith only [t,hp,Nat.mul_le_mul_right k hp]
 change k*_+_≤ _; gcongr
lemma atRim (v:HavenL n P L)(x:Site n): chose L P (Φrap n x 10):=by
 have hP:= v.pay; have hp:coverNumber P.B (Φrap n x 10).val.2 ≤ 1:= (Corona.cover_mono (Corona.halo_mono hP (Subset.refl _)) _).trans (AnalyticBridge.CouplingShape.ballPaid ..); exact (Nat.pow_le_pow_left hp 3).trans_lt (by rw [one_pow]; exact v.door)
section
variable {s:Sweep n}(r:s∈cycleSweep n){x y:Site n}(g:Earlier s x y)
include g
lemma shift_ref : (boxA s).symm (node x)=node y:= (boxA s).symm_apply_eq.mpr g.symm
lemma root_in (S:Finset (Seat n)): node x∈ S ↔ node y∈ actY s S := by unfold actY; rw [mem_map_equiv]; change _ ↔ boxA s (node y)∈ S; rw [g]
lemma root_is (i:Scree.Hub n): (moveHub s i).val.1=node y ↔ i.val.1=node x:= by change (boxA s).symm _=_↔_; rw [←shift_ref g,(boxA s).symm.injective.eq_iff]
lemma move_bill (l:ℕ): moveHub s (Φrap n x l)=Φrap n y l:=Subtype.ext (Prod.ext (shift_ref g) (by change (actY s (halo l {node x}))=_; unfold actY; rw [← sitU,←paysT,map_singleton]; rw [show (boxA s⁻¹).toEmbedding _= _ from (shift_ref g)]))
omit g
lemma chose_pull (i:Scree.Hub n): chose L P (moveHub s i) ↔ chose L P i:=by unfold chose; rw [show coverNumber _ (moveHub s i).val.2=_ from glow_q s P.B i.val.2]
open scoped YM.CF.Mew
lemma suit_scar (c:ℂ)(s:Sweep n)(A:Cipher n): suit_Y s (c • A)=(Spire.payZ s c) • (suit_Y s A):=by
 apply Subtype.ext; let V:= Levier.siteU (castX s) s.charge (spinU s.charge s.s) n; change sauce s.charge (detX s.s) V (c • A.val)= (cSignX _ c) • sauce _ _ _ A.val; rw [sauce,singT,win_c,twist_scalar]; rfl
abbrev turnD (s:Sweep n)(X:ArcΦ):ArcΦ:= (costSkate s X.1,costDome s X.2)
lemma turn_Zero (s:Sweep n): turnD s 0=0:= Prod.ext (cost_zero s) (dome_zero s)

end
local notation "mQ"=> mid N B
variable (s:Sweep (mid N B))(r:s∈cycleSweep (mid N B))(x y: Site (mid N B))(g:Earlier s x y)(hp:0≤h)
variable (v:HavenL (mid N B) P L)
open scoped YM.CF.Mew
include g r hp v
lemma wheelD {u:RegBudget (mid N B)}{X:ArcΦ}(p:Axon L y P u h Q X): Axon L x P (base_Q s u) h (duty_Q P.order P.power*Q) (turnD s X):=by
 have ht(i:Scree.Hub (mid N B))(t:i.val.1≠node x):base_Q s u i=0:=by unfold base_Q; rw [p.site _ (mt (root_is g i).mp t)]; exact funext (fun i=>map_zero _)
 refine ⟨earth_Q P s r p.vest hp,ht,fun i t=>?_⟩
 by_cases he:i.val.1=node x; swap; · rw [ht i he,if_neg (fun (p:i= Φrap (mid N B) x 10)=>he (p ▸ rfl)),Pill_0]; exact ⟨rfl,rfl⟩
 obtain ⟨a,W⟩:=p.flair _ ((chose_pull i).mpr t : chose L P (moveHub s i)); have hw:(moveHub s i).val.1=node y:= (root_is g i).2 he; let F:= u (moveHub s i)
 obtain ⟨w,q,z⟩:= p.vest.weight; have u':= v.rooms (moveHub s i) ((chose_pull i).mpr t); unfold base_Q; rw [life_step]; simp only [Function.comp_apply,Facet.glacial,a,map_zero,true_and]
 simp only [←move_bill g 10,show moveHub s i=moveHub s (Φrap (mid N B) x 10) ↔ i=Φrap (mid N B) x 10 from (scope_q s).injective.eq_iff] at W; -- tune
 rw [show pillar x (step_F s F) P=turnD s (pillar y F P) from Prod.ext (by change tooth (node x) _ _=costSkate _ (tooth (node y) _ _); rw [←he,←hw]; exact tooth_cost s r i _ (q _) hp v.period u') (cost_Dome s i _ _ g he F (q _) u')]; rw [show F= u (moveHub s i) from rfl,W]; split; rfl; exact turn_Zero _

lemma restore {u:RegBudget (mid N B)}{V:Cusp (mid N B)}{z:ℂ}{F:Copy (mid N B)}{X:ArcΦ}(p:Ice L y P h A B₀ C F u V z X) : Ice L x P h (duty_Q P.order P.power*A) (strive_E P.order*B₀) C (turn_V s F) (base_Q s u) (force_V s V) (phaseB s z) (turnD s X):=by
 refine ⟨wheelD s r x y g hp v p.axle,le_trans ?_ p.phase,fun i h=>?_ ,?_,fun i w=>?_⟩
 · rw [phaseB,castT]; unfold cSignX; split; rw [norm_star]; rfl -- le_rfl syntax? `rw` closes.
 · unfold force_V; refine funext fun D=>funext fun v=>?_ ; unfold turn_V; simp only [Function.comp_apply]; rw [p.stout _ (mt (root_in g _).mpr h)]; exact map_zero _
 · obtain ⟨Z,qk,u,t⟩:=p.grant; let a:=strive_E P.order; have ha:0 ≤ a:=by unfold a strive_E composeCost; positivity
   refine ⟨a • zeal_F s Z,⟨fun i=>mul_nonneg ha (qk.1 _),fun i D p t=>?_⟩,fun i=>?_ ,fun i t'=>?_⟩
   · let X:=moldA s i; exact medal_all P i.val D s r (qk.2 X (actY s D) (map_nonempty.mpr p) (Finset.map_subset_map.mpr t)) hp
   · rw [tall_s]; let A:=(boxA s).symm i; have he i:=call_Q (k:=P.B) (a:=P.supportExponent+1+1) s Z i; specialize he A; rw [show boxA s A=i from (boxA s).apply_symm_apply i] at he; rw [he]; exact mul_le_mul_of_nonneg_left (u _) ha
   · have ht:= t (moldA s i) (right_ne_zero_of_mul (show a*Z (moldA s i)≠0 from t')); exact ⟨glow_q s P.B i.val ▸ ht.1,(root_in g _).mpr ht.2⟩
 · unfold turn_V; simp only [Function.comp_apply]; rw [p.wear (yellA s i) (skew_V s i.1 _ w),map_add,map_add]; -- tune
   let u':=suit_Y s; have hl(x:Cipher mQ): suit_Y s⁻¹ (u' x)=x:=by unfold u'; rw [moon_Y,mul_inv_cancel,toon_Q]
   rw [ show exponentL _ _ (yellA s i).1= u' (exponentL P (base_Q s u) i.1) from (force_r P s u i).symm,← bean_H P s V i]; -- direction
   change _= _; rw [hl,hl]; suffices he:suit_Y s⁻¹ (z • 1)=(phaseB s z) • 1 by rw [he]
   rw [phaseB,castT,suit_scar,map_one]
end YM.CF.QuadClock
