import YM.SU5.Silk.Clock.Stater
import YM.CF.Brood.Tips
import YM.CF.Ione.Tape
import YM.CF.Hype.Ace
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione.Clock
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
open Vow Salt
open Bake Lilt Rue Trees Taxi Moto Neon Haro Tap Py
open Hove
variable (s:Sweep n)
lemma cold_orbT(F:Cipher n)(q:Flour (camp X) F.val) : cutM (pitchMask X)*orbitPH F*cutM (pitchMask X)=orbitPH F:=by
 have ht(i j:Tulip.Single n)(h:orbitPH F i j≠0):i∈pitchMask X ∧ j∈pitchMask X:=by
    unfold orbitPH at h; rw [Matrix.of_apply,Prism.port_eq] at h; split at h; contradiction
    have he: { (true,i),(false,j)}∈ Wheat (camp X):= Classical.byContradiction fun w=> h (by rw [q.door w,mul_zero])
    have hj: {(true,i),(false,j)}⊆camp X:=mem_powerset.mp (mem_filter.mp he).1; exact ⟨(mem_filter.mpr (by obtain ⟨_,v⟩:=mem_filter.mp (hj (show (true,i)∈_ from mem_insert_self ..)); exact ⟨mem_univ _,v⟩)), mem_filter.mpr (by have p:= (mem_filter.mp (hj (mem_insert_of_mem (mem_singleton_self (false,j))))).2; exact ⟨mem_univ _,p⟩)⟩
 ext i j; rw [Fock.cutM,Matrix.mul_diagonal,Matrix.diagonal_mul]; by_cases h:orbitPH F i j=0; rw [h,mul_zero,zero_mul]
 obtain ⟨a,b⟩:=ht i j h; rw [if_pos b, if_pos a,mul_one,one_mul]

variable {N B:Side}{o:Site (mid N B)} (bq:Sweep (mid N B))
-- column oriented as a forward pull s: values from the source at mPath s o, to o. No alignment by Gauge-only translations.
abbrev dashF(s:Sweep n)(R:RegBudget n):RegBudget n:= base_Q s⁻¹ R
abbrev Price_R(s:Sweep n):ℝ:= Price s.s
lemma dash_eq(s:Sweep n)(R:RegBudget n)(i:Scree.Hub n)(U:Pane n):dashF s R (moveHub s i) (flashA s U)=suit_Y s (R i U):=by
 unfold dashF base_Q step_F; simp only [Function.comp_apply,inv_inv,revB]; rw [show moveHub s⁻¹ (moveHub s i)=i from (scope_q s).left_inv i]
lemma dash_orb(s:Sweep n)(p:s∈Whirl n)(R:RegBudget n)(U:UNI SpinIdx)(w:JetS s.s false (detX s.s) U)(i:Scree.Hub n): orbitPH (dashF s R (moveHub s i) 1)=Thera.jazz (detX s.s) (twist (siteU (castX s) false U n) (orbitPH (R i 1))):=by
 have ht:=dash_eq s R i 1; rw [Facet.glacial] at ht; rw [ht]; have h:JetS s.s s.charge (detX s.s) U:= ((whirl s).1 p).1.symm ▸ w; rw [←tama s U h]; unfold FrameR; rw [Haro.paral]; rw [((whirl s).1 p).1]; rfl

local notation "mH"=>mid N B
abbrev arc_s(s:Signed)(U:UNI SpinIdx)(X:ArcΦ):ArcΦ:= (localFace s⁻¹ X.1,zoomL s U X.2)
lemma arc_s0(s:Signed)(U:UNI SpinIdx):arc_s s U 0=0:= Prod.ext (locale_zero s⁻¹) (zoom_zero U s)
-- general pillar. Proof anchored where it's bought.
lemma gains(s:Sweep mH)(p:s∈Whirl mH)(q:Site mH)(Wz:RegBudget mH)(j:Scree.Hub mH)(t:PressB P j (Wz j) h c)(u:0≤ h)(v:j.val.1=node (mPath s q))(y:Nonwrapping j.val.2 j.val.1)(N4:4 ≤ (More mH).val)(U:UNI SpinIdx)(w:JetS s.s false (detX s.s) U):
 pillar q (dashF s Wz (moveHub s j)) P=arc_s s.s U (pillar (mPath s q) (Wz j) P):=by
 refine Prod.ext ?_ ?_
 · have he: moveHub s⁻¹ (moveHub s j)=j:= (scope_q s).left_inv _
   unfold Neon.pillar; dsimp only [arc_s]; have hp:= boost_face s⁻¹ (inv_mem p) (moveHub s j) (he.symm ▸ (show PressB P j (Wz j) h c from t)) N4 u (he.symm ▸ y)
   unfold dashF base_Q; rw [he]; rw [he,v] at hp
   have hk:(moveHub s j).val.1=node q:= by change (boxA s).symm j.val.1= _; rw [v,nodeA,Equiv.symm_apply_apply]
   rw [hk] at hp; exact hp
 change jetsL q (orbitPH (dashF s Wz (moveHub s j) 1))= _; rw [dash_orb s p Wz U w]; have hj:= (cold_orbT _ (t.fitted 1)); exact tQuantum s j.val.2 q U (v ▸ y) w _ (pitch_Q s _ U _ hj)

lemma motion_admits(s:Sweep n)(p:s∈Whirl n)(F:RegBudget n)(V:BudgetPoint)(x:ℝ)(v:IncX primeU F V h x)(z:0≤h): IncX primeU (dashF s F) V h (duty_Q V.order V.power*x):=by
 obtain ⟨B,v,t⟩:=v.weight; let Q:= duty_Q V.order V.power; have he:0≤ Q:=by unfold Q duty_Q composeCost; positivity; --
 refine ⟨⟨fun i=>Q*B (moveHub s⁻¹ i),fun i=>pay_all_F V s⁻¹ i _ (inv_mem p) (v _) z,fun i=>?_⟩,fun _ w=>False.elim w⟩
 apply le_trans (Eq.le ?_) (mul_le_mul_of_nonneg_left (t ((boxA s⁻¹).symm i)) he); rw [mul_sum]; conv_rhs=>rw [←Equiv.sum_comp (scope_q s⁻¹)]
 apply sum_congr rfl; intro j _; split_ifs with v p h
 · unfold BudgetPoint.mass; rw [show coverNumber _ (scope_q s⁻¹ j).val.2= _ from glow_q s⁻¹ V.B j.val.2]; change (Trees.currency V.B V.supportExponent j.val.2)*(Q*B _)= Q*(Trees.currency _ _ _* B (moveHub s⁻¹ j)); ring
 · exact False.elim (p (congrArg (boxA s⁻¹).symm v))
 · exact False.elim (v ((boxA s⁻¹).symm.injective h))
 rw [mul_zero]
lemma facetAx(s:Sweep mH)(p:s∈Whirl mH)(R:RegBudget mH)(X:ArcΦ)(o:Site (mid N B))(u:Axon m (mPath s o) P R h a X)(z:0≤h)(hn:∀ i:Scree.Hub mH,chose m P i→Nonwrapping i.val.2 i.val.1)(pN:4≤ (More mH).val)(U:UNI SpinIdx)(t:JetS s.s false (detX s.s) U) : Axon m o P (dashF s R) h (duty_Q P.order P.power*a) (arc_s s.s U X):=by
 let W:= Whirl mH
 have hs(i:Scree.Hub mH)(v:i.val.1≠node o): dashF s R i=0:=by
    unfold dashF base_Q; rw [u.site,show step_F s⁻¹ (0:InkD mH)=0 from funext fun x=> map_zero _]; unfold moveHub; dsimp only; rw [nodeA]; intro q; change (boxA s⁻¹).symm _= _ at q; rw [sitU] at q; exact v ((boxA s).injective q)
 refine ⟨motion_admits s p R P a u.vest z, hs, fun i ht=>?_⟩
 let J:= Φrap mH o 10; by_cases hv:i.val.1=node o; swap
 · rw [hs i hv]; simp_rw [if_neg (fun x:i=Φrap mH o 10=> hv (congrArg (fun k:Scree.Hub mH=> k.val.1) x))]; exact ⟨rfl,Pill_0 o P⟩
 obtain ⟨j,rfl⟩:=(scope_q s).surjective i; let i:=moveHub s j; change i.val.1=node o at hv; have hb:j.val.1=node (mPath s o):=by rw [nodeA,←hv]; exact ((boxA s).apply_symm_apply _).symm
 have hd:chose m P j:=by unfold chose; unfold chose at ht; rw [show coverNumber _ (scope_q s j).val.2= _ from glow_q s P.B j.val.2] at ht; exact ht
 obtain ⟨B',pB,v⟩:=u.vest.weight; let T':= gains s p o R j (pB j) z hb (hn j hd) pN U t; obtain ⟨u,r⟩:=u.flair j hd; rw [r] at T'
 have ha:= dash_eq s R j 1; rw [Facet.glacial] at ha; refine ⟨?_,?_⟩
 · change Beau.pot ∅ (dashF s R (moveHub s j) 1)=0; rw [ha,Beau.pot_Z]; rw [show Beau.pot ∅ (R j 1) = 0 from u,map_zero]
 by_cases he:j= Φrap mH (mPath s o) 10; · refine T'.trans ?_; rw [if_pos he,if_pos (show (scope_q s) j=J from he.symm ▸ pass_hrap s o 10)] -- he ▸ tune
 refine T'.trans ?_; rw [if_neg he,arc_s0,if_neg (fun h=>he ((scope_q s).injective (h.trans (pass_hrap s o 10).symm)))]
end YM.CF.Ione.Clock
