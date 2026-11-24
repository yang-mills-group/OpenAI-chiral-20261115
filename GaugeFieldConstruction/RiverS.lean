import GaugeFieldConstruction.HarborM
import GaugeFieldConstruction.Corbie
import YM.CF.Salt.Felt
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
-- sweep weight.TIO. openc slice.S.inverse. erosion
open Levier Thera Urn Nacre Salt

namespace SliceRoof
-- PPE of operating Loom (A2)
open Vow Rue Rill CreekX Pressure CF.Forge
variable {P:BudgetPoint}{k:ℕ}{H:Scree.Loom n}{t d c a:ℝ}{F:Elm n Unit d a c}{A S:Support (More n)}{D Y:Support (More n)}{U W: Orbit n}
def uplift (F:Elm n Unit d a c) (H:Loom n)(k:ℕ)(D S:Support (More n))(t:ℝ)(U:Orbit n):Op (Single n):= if nozzle k S D t U.1 then releaseQ F S (H U) else 0
local notation "Xρ"=> uplift F H k D S t
lemma nozzle_axis (s:Sweep n): nozzle k (actY s S) (actY s D) t (flashA s U.1) ↔ nozzle k S D t U.1:=by
 unfold nozzle; rw [flagsA, sandQ,sandQ,walkA,walkA,show _∪actY s (Lattice.halo (2*k+20) D) = actY s (sandQ k S D) from (Finset.map_union ..).symm]
 change _ ↔ sandQ k S D ∩ _ ⊆ _
 unfold actY; simp only [←sitU,← Finset.map_inter,Finset.map_subset_map]
variable (u:Roof n t d k H)(p:P.threshold≤t)(hp:Lattice.halo (cipherK k) D⊆ A)(hg:Lattice.halo (k+22) S⊆ A)(w:0<d)
include u w
lemma release_agree {U W:Pane n}(g:Lattice.Agrees S U W)(a:Guard U d)(e:Guard W d): releaseQ F S U=releaseQ F S W:=by
 rw[re_L F _ _ a w,re_L F _ _ e w];ext i j; apply sub_eq_zero.mp; apply norm_le_zero_iff.mp
 apply ((F.coat S|>.1 ()).expo i j|>.variation (light _ U w a) (light _ W w e)).trans_eq
 rw [show (forum _ _).eval S (light _ U w a) (light _ W w e)=0 from ?_,mul_zero]; change Tulip.fare S _ _ / _=_; rw [show Tulip.fare S (Tulip.profile U) (Tulip.profile W)=0 from ?_,zero_div]
 unfold Tulip.fare; apply sum_eq_zero; intro i p; have h:=g i (mem_filter.mp p).2.1 (mem_filter.mp p).2.2; rw [show Tulip.profile U i=Tulip.profile W i from funext (fun t=> by unfold Tulip.profile; rw [h]),sub_self,norm_zero]
include hp hg
lemma lift_eq (h:Lattice.Agrees A U.1 W.1)(t:Set.EqOn U.2 W.2 A): Xρ U=Xρ W:=by
 unfold uplift
 -- t shadow
 split_ifs with p q q
 · apply release_agree u w _ (u.paid _) (u.paid _); exact sailsZ u hp hg p q h t
 · exact False.elim (q (trench_f hp hg h|>.1 p))
 · exact False.elim (p (trench_f hp hg h|>.2 q))
 rfl
omit hp hg
lemma lift_meter : Measurable Xρ:=by
 let f(x:Orbit n): ↥(Openc (More n) d):=light d (H x) w (u.paid _)
 have ht:Measurable f:= (((Dial.profile_c).measurable.comp u.bill).subtype_mk)
 apply Measurable.ite (@nozzle_meter n _ _ _ _) _ _
 · -- repro release equals ivory
   have he(i):releaseQ F S (H i)=F.F S () (f i):=re_L F S _ (u.paid _) w
   simp_rw[he]; refine (show Continuous (F.F S ()) from ?_).measurable.comp ht; exact continuous_matrix fun i j=>(F.coat S|>.1 ()).expo i j|>.connected
 exact measurable_zero
lemma lift_gZ (g:Seat n→ SU.E): Xρ (Lattice.gauge g U.1,threadG g U.2)= twist (tradew n g) (Xρ U):=by
 unfold uplift; simp only [gz (U:=U)]; split
 · rw [u.rev]; exact norm_enter _ _ (u.paid _) w g
 exact (map_zero _).symm
lemma lift_move (s:Sweep n)(r:Injective (priorP U.2))(q:groupShape F):uplift F H k (actY s D) (actY s S) t (flashA s U.1,bun s U.2) = realR s true (Xρ U):=by
 unfold uplift; simp only [nozzle_axis (U:=U)]; split; · rw [u.move _ _ _ r]; exact backG q s S _ (u.paid _) w
 cases ht:s.charge <;> cases hf:detX s.s <;> simp [realR,bolt,hitL,Thera.jazz,windX,ht,hf]
lemma lift_empty {T:Ids n}: uplift F H k ∅ S t U = uplift F H k ∅ S t (U.1,T):=by
 unfold uplift; simp only []; split
 · rename_i v; refine release_agree u w (fun i x y=> ?_) (u.paid _) (u.paid _); exact (sailsEmpty u v i x y).trans (sailsEmpty u (U:=(U.1,T)) (show nozzle k S ∅ t (U.1,T).1 from v) _ x y).symm
 rfl
lemma lift_real (i j:Single n): ‖Xρ U i j‖≤ F.W S i j:=by
 unfold uplift; split
 · rw [re_L F _ _ (u.paid _) w]; exact (F.coat S|>.1 ()).expo i j|>.bounded _
 rw [Matrix.zero_apply,norm_zero]; exact (F.coat S|>.1 ()).nonn i j
include p hp hg
open XGarden Jet Broc
local notation "Sz"=> fun i:tangD n=> ((pressQ P Y U.1 i,U.2):Orbit n)
variable (vZ:D⊆ Y)(pZ:cipherK k ≤5*P.B)(ht:3 ≤ P.B)
variable {c0 K' C x q T':ℝ}
def γCreek (F:Elm n Unit d a c)(H:Loom n)(S:Support (More n))(i j:Single n)(U:Orbit n) (x:tangD n):ℂ:= equalizer (fun y=> F.F S () y i j) (Tulip.profile (increment (H U) x))
lemma gamma_S (h:hud_T 7 K')(t:coinH K' c0)(g:0≤c0)(i j:Single n): Allows 7 (γCreek F H S i j U) 0 (DeskK c0 d* F.W S i j) :=by
 let L:tangD n→_:= Tulip.profile ∘ increment (H U)
 have he:=t (tangD n) _ _ _ (h _ (H U) 0 (by simp))
 let f(x):= F.F S () x i j; let K:= F.W S i j
 let G:=F.coat S|>.1 (); have hx:= G.expo i j
 have hb: ball (L 0) d⊆ Openc (More n) d:=by
    intro y h; refine ⟨H U,u.paid _,mem_ball_iff_norm.mp ?_⟩
    unfold L at h; simp only [Function.comp_apply,Next.SectorChange.Motion.increment_zero] at h; exact h
 have h':Allows 7 (equalizer f) (L 0) (K * ((1+2^7/d)^7)):= allows_looks (G.fuel i j) hx.connected hb w 7 hx.bounded
 exact (h'.comp he).mono (le_of_eq (by unfold K DeskK composeCost; ring))
-- Stronger than Holds grant in focused Loom.Pane Z frozen. agreement on profile only.
include vZ pZ ht
lemma bloom_Ψ (h:hud_T 7 K')(i j:Single n)(g:pingS P.threshold (A\D) U.1):
 (fun y=> uplift F H k D S t (Sz y) i j)=ᶠ[𝓝 0] fun y=>γCreek F H S i j U (P.threshold • (wakeB (unrest Y P.B) y)):=by
 let L:=unrest Y P.B; let T:tangD n→L[ℝ] tangD n:=P.threshold • wakeB L
 let B(y:tangD n):Orbit n:= Sz y
 let C:=fun y:tangD n=> increment (H U) (T y)
 have ht':ContinuousAt (fun y:tangD n=>Tulip.profile (C y)) 0:= Dial.profile_c.continuousAt.comp ((show ContinuousAt (increment (H U)) (T 0) from cliff_n (h n _ _ (by rw [map_zero,norm_zero]; norm_num))).comp T.continuous.continuousAt)
 have hx(i:Pressure.Bond (More n))(pz:i.1∈S):∀ᶠ y in 𝓝 (0:tangD n),H (B y) i=C y i:=by
    have h:= nozzle_port u p hp hg vZ pZ ht pz g; refine h.mono ?_; intro y h; refine h.trans ?_; change increment _ (wakeB L (P.threshold • y)) i = _; rw [map_smul]; rfl
 have hv:∀ᶠ y in 𝓝 (0:tangD n),∀ i:Pressure.Bond (More n),i.1∈S→ H (B y) i=C y i:=by
    apply eventually_all.mpr; intro y; by_cases p:y.1∈S; exact (hx y p).mono (fun i p _=>p); exact Eventually.of_forall (fun i h=> (p h).elim)
 have hz: Tulip.profile (C 0) ∈ Openc (More n) d:=by
    change Tulip.profile (increment _ (T 0))∈_; rw [map_zero]; simp; exact lantern _ (u.paid _) w
 filter_upwards [hv,Vow.tick (Y:=Y) g, ht'.eventually ((openc _ _).mem_nhds hz)] with x q h t
 change uplift F H k D S _ (B x) i j=γCreek F H S i j U (T x)
 unfold uplift; rw[if_pos (payz p hp hg (U:=B x) h), re_L F _ _ (u.paid _) w]; unfold γCreek; rw [equalizer,dif_pos (show Tulip.profile _∈ _ from t)]
 let X:=light d _ w (u.paid (B x)); let Y':↥(Openc (More n) d):=⟨Tulip.profile (C x),t⟩
 apply sub_eq_zero.mp; apply norm_le_zero_iff.mp; apply (((F.coat S).1 ()).expo i j|>.variation X Y').trans_eq
 rw[show (forum _ _).eval S X Y'=0 from ?_,mul_zero]; change Tulip.fare S (Tulip.profile (H (B x))) (Tulip.profile (C x))/_=_
 have hF:Tulip.fare S (Tulip.profile (H (B x))) (Tulip.profile (C x))=0:=by
    unfold Tulip.fare; apply sum_eq_zero; intro i p; rw [show Tulip.profile (H (B x)) i=Tulip.profile (C x) i from funext (fun j=>by unfold Tulip.profile; rw [q i (mem_filter.mp p).2.1]),sub_self,norm_zero]
 rw[hF,zero_div]
end SliceRoof
end YM.CF.Sour
end
