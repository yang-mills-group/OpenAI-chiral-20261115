import YM.CF.Taxi.Bar
import YM.CF.Taxi.Dig
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Vow
variable {p:Clip}(R: PathData SU.group)(o:Site (More n))(U:Pane n)
local notation "G"=> SU.group
-- chart general Z, universal. supporting p.Mask external generation carries D. Live loan derivative from *unclipped source* with masks; keystone Booleans only move through reached positions. No continuity of root.U when kept/displaced Vk on ANY neighborhood required. only at strict + local.
variable (b: AnalyticBridge.VerifiedReset.Low)
local notation "B_"=> Low.home R b P o
local notation "kP"=> P.threshold
lemma wakeV (t:Y⊆D) (v:tangD n): Agrees (halo (5*P.B) Y) U (pressQ P D U v):=by
 intro i g l;  unfold pressQ gyrate Function.comp RG.increment; rw [steadyB,if_neg]; simp; exact fun y=> Finset.disjoint_left.mp (mem_filter.mp y).2 (mem_insert_self ..) (Corona.halo_mono le_rfl t g)
private lemma keel_b (h:Decent p P)(z:pingS P.threshold (B_\Y) U)(q:Y⊆D): ∀ᶠ x: tangD n in 𝓝 0, kept p kP o (pressQ P D U x)↔kept p kP o U:=by
 let F(x):=pressQ P D U x
 let A(i:Face (Per (More n))):= P.threshold * Real.exp ((separation o i.1:ℝ)/p.relaxation)
 have ht:=h.radius
 have hx:∀ i:Face (Per (More n)),∀ᶠ x:tangD n in 𝓝 0,SU.group.chord (faceValue (F x) i)≤A i↔ SU.group.chord (faceValue U i)≤A i:=by
   intro i; by_cases g:P.B-2 ≤ separation o i.1
   · exact Eventually.of_forall fun x=> ⟨fun _=>too_far _ _ h U i _ g,fun _=>too_far _ _ h (F x) i _ g⟩
   have hp:i.1∈ B_:= Low.halo_home _ _ _ _ (halo_spec.mpr ⟨_,mem_singleton_self _,by omega⟩); by_cases H:i.1∈ Y
   · have hb:touched i⊆ Lattice.halo (5*P.B) Y:=fun j v=>halo_spec.mpr ⟨i.1,H, ((separation_comm ..).trans_le (visit_near i v)).trans (by omega)⟩
     exact Eventually.of_forall fun x=>by rw [show faceValue (F x) i= faceValue U i from (face_local i U (F x) (agrees_mono (wakeV U q x) (Finset.coe_subset.mpr hb))).symm]
   have hh:¬ Disjoint (B_ \Y) (touched i):= fun s=> Finset.disjoint_left.mp s (mem_sdiff.mpr ⟨hp,H⟩) (anchor_visit _)
   have hv:kP ≤ A i:=by refine le_mul_of_one_le_right P.threshold_pos.le (Real.one_le_exp (div_nonneg ?_ p.radius_pos.le)); positivity
   filter_upwards [Vow.tick (Y:=D) z] with x p; exact ⟨fun _=> (z i hh).le.trans hv,fun _=> (p i hh).le.trans hv⟩
 refine (eventually_all.mpr hx).mono fun x p=>?_ ; exact ⟨fun g i=> (p i).1 (g i), fun g i=> (p i).2 (g i)⟩
lemma datum (s:RG.Slot)(S:ℕ)(u:s.length ≤S): 0 ≤ Wages.slotCost G P.power P.order S:= zero_le_one.trans (Wages.slot_ge ..)
private lemma body_c(j:ℕ×ℕ)(p:b.2=.inr j) : AnalyticBridge.VerifiedReset.Bill P o (fun _=>True) (4*rowCost SU.group P (Low.length R b)) (Low.plain R b o):=by
 let t(v:RG.Slot):=Wages.slotCost G P.power P.order (Low.length R b)
 let v:=Low.left R b j; let w:=Low.right R b j; let C:=t v
 have ht:v.length ≤ Low.length R b:=by simp [Low.length,p,v]; -- tune
 have hp:w.length ≤ Low.length R b:=by simp [Low.length,p,w];
 let Y(v:RG.Slot):=(fun U:Pane n=>v.atSite U o); have hu(v:RG.Slot)(u:v.length ≤ Low.length R b): AnalyticBridge.VerifiedReset.Bill P o (fun _=>True) (2*C) (Y v):=Wages.pane_R v _ u o P
 have h:= Bill.mul_left (2:ℝ)⁻¹ (Bill.pair (hu v ht) (hu w hp)); have hU:(Low.plain R b o)=(fun U=> (2:ℝ)⁻¹* inner ℝ (Y v U) (Y w U)):=by
    funext U; unfold Low.plain; rw [p]; change inner ℝ _ _ /2=_; rw [div_eq_inv_mul]
 rw [hU]; apply AnalyticBridge.VerifiedReset.Bill.le h; rw [abs_of_nonneg (by positivity)]; unfold rowCost C t; exact le_of_eq (by ring)
-- price clipped inl unconditionally at all U even huge.Cost |alpha| const. $pow λ etc available
def liteV (P:BudgetPoint)(u:ℝ):= composeCost P.order (u*‖Complex.ofRealCLM‖) 1
lemma mintK {f:Pane n→ℝ}(c:ℝ)(i:Site (More n))(S: Signs P i (f ∘ increment U) c):Allows P.order ((Complex.ofRealCLM ∘ f) ∘ pressQ P D U) 0 (liteV P c):=by
 let L:=Complex.ofRealCLM; unfold liteV; rw [mul_comm c]; apply Vow.debt_m (Y:=D) (o:=i); exact Prism.skills ((Prism.skin S).linear _ le_rfl)
lemma scaleV (p:BudgetPoint)(u v:ℝ):liteV p (u*v) = u*liteV p v:=by unfold liteV composeCost; ring
lemma mint_p (p:BudgetPoint)(v:ℝ)(he:0 ≤v):0≤liteV p v:=by unfold liteV composeCost; positivity
variable(Γ:ℝ)
def stampV (R:PathData SU.group)(c:Clip)(P:BudgetPoint)(b:Low)(Γ:ℝ):ℝ:= |b.mark R c| *(2*P.threshold+liteV P (Γ*(faceCost SU.group P*P.threshold^2))+liteV P (Γ*(4*rowCost SU.group P (b.length R)))) -- typo k_b should P.threshold
lemma pulse_k (q:Y ⊆ D)(d:Decent p P)(g:DayT P.order Γ)(x:0≤Γ) (z:pingS P.threshold (B_\Y) U):Allows P.order (fun i: tangD n=> Complex.ofRealCLM (b.live R p P o (pressQ P D U i))) 0 (stampV R p P b Γ):=by
 let F:=pressQ P D U; have hx:= keel_b R o U b d z q; let t:= P.threshold; let a:= Γ; let G':=SU.group; have h0: 0 ≤ 2*kP:=by have hp:=P.threshold_pos; positivity
 let wℝ:= liteV P (Γ*(faceCost SU.group P*P.threshold^2)); let vu:= liteV P (Γ*(4*rowCost SU.group P (b.length R))); have hw:0 ≤ wℝ:=mint_p _ _ (mul_nonneg x (mul_nonneg (faceCost_nonneg ..) (sq_nonneg _))); have hv:0 ≤ vu:=mint_p _ _ (mul_nonneg x (mul_nonneg (by norm_num) (row_nonneg ..))); let L:=b.live R p P o; let M(t):ℂ:=(L t:ℝ)
 have hq:0 ≤ stampV R p P b Γ:=mul_nonneg (abs_nonneg _) ((add_nonneg (add_nonneg h0 hw) hv))
 change Allows P.order (M ∘ F) 0 _
 cases k:b.2
 next u=>
    by_cases v:o∈Y
    · have hp(i:tangD n):faceValue U (o,b.1)=faceValue (F i) (o,b.1):=face_local _ _ _ (agrees_mono (wakeV U q i) (Finset.coe_subset.mpr (fun y w=> halo_spec.mpr ⟨o,v, ((separation_comm ..).trans_le (visit_near (o,b.1) w)).trans (by have ht:=d.radius; omega)⟩)))
      have he:M ∘ F=fun _=>M U:=by funext x; unfold M L; simp only [Function.comp_apply,Low.live,k,Sum.elim_inl,←hp]
      rw [he]; apply allows_const; unfold M; rw [Complex.norm_real]; apply (Low.shapeBound R p b o U).trans; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); simp_rw [Low.length,k,Sum.elim_inl,Nat.cast_zero,zero_div,Real.exp_zero,mul_one]; unfold vu Low.length at hv; simp only [k,Sum.elim_inl] at hv; exact le_trans (le_add_of_nonneg_right hw) (le_add_of_nonneg_right hv)
    let YP(W: Pane n):Prop:= SU.group.chord (faceValue W (o,b.1)) ≤ kP
    have hT:¬ Disjoint (B_ \ Y) (touched (o,b.1)):= fun h=> Finset.disjoint_left.mp h (mem_sdiff.mpr ⟨b.small_home R P o, v⟩) (anchor_visit _)
    let C (V:Pane n):= SU.group.price (faceValue V (o,b.1)); have he:AnalyticBridge.VerifiedReset.Bill P o YP (faceCost SU.group P * P.threshold^2) C:= face_price _ b.1 _ (fun _ e=>e)
    let V(W: Pane n):=p.direct*C W; have hp:=Bill.mul_left p.direct he; have hu := g _ _ YP _ _ _ hp rfl U (z _ hT).le; have hv':=mintK (D:=D) U _ o hu; change Allows P.order (fun i=>Complex.ofRealCLM (V (F i))) 0 (liteV P (Γ*(|p.direct| * (faceCost SU.group P *P.threshold^2)))) at hv'
    apply (hv'.germ ?_).mono ?_
    · filter_upwards [Vow.tick (Y:=D) z] with i pq; have ht:= (pq _ hT).le; unfold M L V Low.live; rw [Function.comp_apply,k, Sum.elim_inl,PathData.clipped,if_pos ht, SU.group.chord_price]; unfold C; change ((_ :ℝ) :ℂ)= ((_ :ℝ):ℂ); ring_nf <;> rfl
    unfold stampV; rw [show b.mark R p=p.direct from (by unfold Low.mark; rw [k]; rfl),mul_left_comm Γ |p.direct|,scaleV]; exact mul_le_mul_of_nonneg_left (le_trans (le_add_of_nonneg_left h0) (le_add_of_nonneg_right hv)) (abs_nonneg _) -- tune desired w ≤ sum
 next j=>
    by_cases pV: PathData.kept p t o U
    · let H:= body_c R o b j k (P:=P); have hp:=Bill.mul_left (b.mark R p) H; have hu:= g _ _ _ _ _ _ hp rfl U trivial
      apply ((mintK (D:=D) U _ _ hu).germ ?_).mono ?_
      · filter_upwards [hx] with i v; unfold M L Low.live; simp only [F,Function.comp_apply,k,Sum.elim_inr,if_pos (v.2 pV)]; rfl
      unfold stampV; rw [mul_left_comm Γ |b.mark R p|,scaleV]; exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (add_nonneg h0 hw)) (abs_nonneg _)
    refine (allows_const 0 ((show ‖(0:ℂ)‖= _ from norm_zero).le.trans hq)).germ ?_; filter_upwards [hx] with i w; change (0:ℂ)=↑(b.live R p P o (F i)); rw [Low.live,k,Sum.elim_inr,if_neg fun h=>pV (w.mp h),Complex.ofReal_zero]
end YM.CF.Taxi
