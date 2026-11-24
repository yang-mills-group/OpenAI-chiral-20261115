import SatinThinHomage
import YM.CF.Fans.Cause
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
open scoped YM.CF.Mew

open Waxy
variable {N n B:Side}{P:BudgetPoint}{h A B' C a:ℝ}{L:ℕ}
def PointSk (a:ℝ):ArcΦ:=(a • mainSlot,0)
lemma point_zero : PointSk 0=0:=by simp [PointSk]
lemma embark (V:HavenL (mid N B) P L)(o:Site (mid N B))(h0:0≤h)(F:Copy (mid N B))(E:RegBudget (mid N B))(K:Cusp (mid N B))(t:ℂ)(Y:ArcΦ)(p:Ice L o P h A B' C F E K t Y)(z e:ℝ)(v: ‖Y.1-z • mainSlot‖≤e) : ∃ a:ℝ, ‖(PointSk a).1 - z • mainSlot‖ ≤ e ∧
  ∀ x:Site (mid N B), Ice L x P h (duty_Q P.order P.power*A) (strive_E P.order*B') C (hailQ Fρ o F x) (hailQ Eρ o E x) (hailQ Kρ o K x) 0 (PointSk a):=by
 let A':= duty_Q P.order P.power*A; let B0:=strive_E P.order*B'; let Y_:=avenue o (fun t=>turnD t) Y
 have ha(s:Sweep (mid N B)): |bandSign s|=1:=by rcases tax_cases s.s with p|p<;> unfold bandSign <;> rw [p] <;> norm_num
 have hT(x:Site (mid N B)): Ice L x P h A' B0 C (hailQ Fρ o F x) (hailQ Eρ o E x) (hailQ Kρ o K x) 0 (Y_ x):= by
    let S:= fromHere x o
    have hp(s:Sweep (mid N B))(u:s∈S): Ice L x P h A' B0 C (bandSign s • Fρ s F) (bandSign s • Eρ s E) (bandSign s • Kρ s K) (bandSign s • tρ s t) (bandSign s • turnD s Y):=by
       obtain ⟨s',x'⟩:=(fromHere_iff ..).1 u; have w:= realV x (bandSign s) (restore s s' x o x' h0 V p) h0; rw [ha,one_mul,one_mul,one_mul] at w; exact w
    have he : Ice L x P h A' B0 C (hailQ Fρ o F x) (hailQ Eρ o E x) (hailQ Kρ o K x) (hailQ tρ o t x) (Y_ x):=by
       let T:= refund x o; have hu:=realV x T (ice_sum x S _ _ _ _ _ _ _ _ hp h0) h0; rw [abs_of_pos (refund_pos ..)] at hu; simpa only [sum_const,nsmul_eq_mul,T,A',B0,S,refund_pr] using hu -- notation unfolds A in statement, tune
    rw [nobody_t] at he; exact he
 have hx(x:Site (mid N B))(y:Site (mid N B))(s:Sweep (mid N B))(hq:s∈cycleSweep (mid N B))(h:Earlier s x y) : turnD s (Y_ y)=bandSign s • Y_ x:=by
    have hp:= wheelD s hq x y h h0 V (hT y).axle; have hv:= real_E x (bandSign s) (hT x).axle h0; have hu: base_Q s (hailQ Eρ o E y) = bandSign s • hailQ Eρ o E x:= hail_E o E s hq x y h; rw [hu] at hp
    have hh:chose L P (Φrap (mid N B) x 10):=atRim V x; let W:= (Φrap (mid N B) x 10); have u:=(hp.flair W hh).2; rw [if_pos rfl] at u; have f:=(hv.flair W hh).2; rw [if_pos rfl] at f; exact u.symm.trans f
 obtain ⟨a,η⟩:=sign_forces (Y_ o).1 o (fun s q v=>congrArg Prod.fst (hx o o s q v))
 have hm(i:Site (mid N B)): Y_ i= PointSk a:= by
    have hd(i:Site (mid N B)):(Y_ i).2=0:=by
       have h:=(hT i).axle.flair _ (atRim V i)|>.2; rw [if_pos rfl] at h; exact scareDome i _ (h ▸ (show seedsP (pillar (B:=B) i (hailQ Eρ o E i (Φrap (mid N B) i 10)) P).2 from true_P ..)) (fun s q v=>congrArg Prod.snd (hx i i s q v)) -- h uses RegBudget and pillar. tune
    let s₀:= Sweep.mk 1 (i-o) false; have hg:s₀∈cycleSweep (mid N B):= quad_id
    have hp:costSkate s₀ (Y_ o).1=tax 1 • (Y_ i).1:= congrArg Prod.fst (hx i o s₀ hg (earlier_translate i o)); rw [η,cost_scale,scarLine s₀ hg,show bandSign s₀= _ from tax_o,tax_o,one_smul,one_smul] at hp; exact Prod.ext hp.symm (hd i)
 refine ⟨a, ?_,fun i=> hm i ▸ hT i⟩
 rw [←hm o]; let S:= fromHere o o; let x:= refund o o; let F:= fun s:Sweep (mid N B) => bandSign s • costSkate s Y.1; have hp:(Y_ o).1 = x • ∑ s∈S,F s:=by simp only [Y_,avenue,Prod.smul_fst, Prod.fst_sum] ; rfl -- find Prod lemma tune
 have he:0<x:=refund_pos ..; let K:= z • mainSlot; rw [hp]; change ‖x • (∑ s∈S,F s)-K‖≤_; have ht(s:Sweep (mid N B))(w:s∈S): ‖F s-K‖≤e:=by
    have hw:=scarLine s ((fromHere_iff ..).1 w).1; have hk: K= bandSign s • costSkate s K:=by unfold K; rw [cost_scale,hw, smul_comm (bandSign _),smul_smul,smul_smul,mul_assoc,tax_sq,mul_one] -- order smul_comm first occurrence
    unfold F; let L:=costSkate s; nth_rw 1 [hk]; rw [←smul_sub,←cost_sub,norm_smul, Real.norm_eq_abs,ha,one_mul]; exact (cost_contract ..).trans v
 rw [show x • _ - K= x • (∑ s∈S,(F s-K)) from ?_,norm_smul,Real.norm_of_nonneg he.le]; refine le_trans (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum ht)) he.le) ?_; rw [sum_const,nsmul_eq_mul]; exact (refund_pr o o e).le; rw [Finset.sum_sub_distrib,smul_sub,sum_const,← Nat.cast_smul_eq_nsmul ℝ]; congr 1; exact (inv_smul_smul₀ (by exact_mod_cast (card_pos.mpr (anyFrom o o)).ne') K).symm

variable (L:Side)(Y:BudgetPoint)(Q W VZ VX VY u A':ℝ)
-- inequality α. Keep exact λ real (prev purchase)
local notation "mQ"=> mid N B
lemma cleared (v:HavenL (mid N B) P L.val)(o:Site (mid N B))(h0:0≤h)(F:Site (mid N B) → Copy (mid N B))(t:Bent Fρ F)(E:RegBudget (mid N B))(K:Cusp (mid N B))(z:ℂ)(X:ArcΦ)(p: Ice L.val o P h A B' C (F o) E K z X)(Wf:αPrice L h Q W VZ VX VY (PointSk u) X P Y (a:ℂ)) : ∃ b:ℝ, αPrice L h Q W VZ VX VY (PointSk u) (PointSk b) P Y (a:ℂ) ∧∀ x:Site (mid N B),Ice L.val x P h (duty_Q P.order P.power*A) (strive_E P.order*B') C (F x) (hailQ Eρ o E x) (hailQ Kρ o K x) 0 (PointSk b):=by
 let r:= Tune.qCorset P.threshold Y.threshold (L.val:ℝ); have hz: ζtap L P Y (a:ℂ) (PointSk u)=(r*a*u) • mainSlot:=by unfold ζtap PointSk; rw [Complex.coe_smul,Complex.coe_smul,smul_smul]; exact (mul_smul (r * a) u _).symm -- tune likely symmetry with a
 obtain ⟨b,v,p⟩:=embark v o h0 (F o) E K z X p _ _ (hz ▸ Wf.red); refine ⟨b,⟨hz.symm ▸ v,le_trans ?_ Wf.violet,le_trans ?_ Wf.verd⟩,fun x=> ?_⟩
 · refine le_trans (Eq.le ?_) (mul_nonneg (norm_nonneg _) (sq_nonneg h)); simp [PointSk,ζVtap]
 · refine le_trans (Eq.le ?_) (mul_nonneg (norm_nonneg _) (sq_nonneg h)); simp [PointSk,ξtap]
 have hv:=p x; rw [hail_owned Fρ _ _ t] at hv; -- actually proposition p uses hailQ Fρ? p obtained from embark has `F o`. exactly
 exact hv
end YM.CF.QuadClock
