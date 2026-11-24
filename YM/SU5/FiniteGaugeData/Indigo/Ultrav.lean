import YM.SU5.FiniteGaugeData.Indigo.Refugio
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
local notation "W₀" => GridStep Λ l S

namespace Navy
open VolumeCape.Dream
open Satin
open Fief Steam
-- uniform step budget: at fixed S, any high s & Q from that s's actuated phases, even all unit ball. Ink order. WP Sigma not assumed operator continuity in β, W Width.
abbrev Sizing (Λ:Preparation)(s:ℕ):Prop:=Λ.R0 (hat Λ.R.L Λ.x s)≤1
include Y
lemma stable : ∀ᶠ s in atTop,Sizing Λ s:= ((Λ.app.fiscal.low (k:=1) (by omega)).spine.comp (horizons Λ.x (V:=Λ.V))).eventually ( ge_mem_nhds (by norm_num:(0:ℝ)<1))
omit Y
section
variable {I:Type*} (u:I→ℕ)(P:(i:I)→ PaidPt Y S (u i))(p:∀ i,Sizing Λ (u i))
local notation "n" i:max=>side Y (P i).val.1 (u i)
local notation "m" i:max=>side Y (P i).val.1 (u i+1)
local notation "Q" i:max => ingress Y (u i) (P i).val.1 (P i).val.2
-- deployment. mechan helper bounds gathered of knot.
private lemma from_pane{N P:Side}(A:StepData (More N) (More P))(C:ℝ)(M:Ratio N P){b: Odd M.count.val}(j:ℕ)(G:Op SU.Slot)(V:Male)(χ:Chi)(d β:ℝ)(l:Loom N)(x:Mark N)(W:Fields P) (B:A.patch.Branches A.kernel SU.group)(s:∀ v,‖gathered M j G V b χ d x W v‖≤C): ‖pushMark M A j G V b χ d β l x W‖ ≤ C:=by
 let f:=assembled M j G V b χ d l x W; let A':=A.density β W.1; have he:= A.isKernel B β; unfold pushMark linkLaw
 apply (norm_integral_le_of_norm_le ((he.integrable W.1).mul_const C) (Eventually.of_forall fun i=>?_)).trans; · rw [integral_mul_const,he.total,one_mul];
 rw [norm_smul,Real.norm_of_nonneg (he.positive ..)]; exact mul_le_mul_of_nonneg_left ((norm_integral_le_of_norm_le_const (C:=C) (Eventually.of_forall fun k=>s _)).trans (by simp)) (he.positive ..)
include p Y
private lemma onu(D:Key S)(A:I→Catalog S)(e:∀i,‖A i‖≤1)(W:(i:I)→Fields (side Y (P i).val.1 (u i+1))): ∃ c:ℝ,0≤c∧∀ i, ‖(Q i) (Satin.knot (n i) (Typeset S D) (source S (A i) D)) (W i)‖≤c:=by
 let N(i:I):= side Y (P i).val.1 (u i); let T (i:I):=side Y (P i).val.1 (u i+1)
 rcases isEmpty_or_nonempty I with v|v; · exact ⟨0,le_rfl,fun i=> isEmptyElim (i:I)⟩
 let t(i:I):=(P i).val.1; let k(i:I):=(P i).val.2; let G(i:I):= bead _ Λ.R.L _ (sized Y (u i)) (t i); let c:= Classical.choice v
 have hz(i:I):= (crease Y (u i) _ _ (P i).property.calendar (P i).property.age)
 let A'(i):= rayCost Y (u i) (t i) (k i)
 let M(i):= (Tᵣ (t i) (k i) (u i+1)).J.M; let V:= Σ i:I,Fields (N i); let y(i:V):I:=i.1; have he:Deal (T:=fun _:(Σ i:V,Edge (Seat (T (y i)))) => SU.E) (fun a (_ : PUnit.{1})=> (W (y a.1)).2 a.2):= Deal.pure (X:=PUnit.{1}) _
 obtain ⟨Z,b,r⟩:= (Fiber.gather (X:=PUnit.{1}) (I:=V) (fun i=> N (y i)) Λ.R.L (fun i=> T (y i)) (fun i=> sized Y (u (y i)) (t (y i))) Λ.K.j (aliasLaw Λ) (Journey.legal Λ) Λ.R.odd_side (fun i=>M (y i)) (fun i=> A' (y i)) (fun i=> (( ((Y.voyage (t (y i))).X (Y.uv (k (y i)))).pull.tip (u (y i)) (P (y i)).property.age)).trans (p (y i))) Chi.canonical Λ.J.d (hz c).1 (hz c).2 (Typeset S D) (fun i _=> W (y i)) Sigma.snd he).budget
 refine ⟨Z,b,fun i=>?_⟩; rw [reel]; let f:= source S (A i) D; let w:=Typeset S D; let l:= (Y.voyage (t i)).CapeT (u i); apply from_pane _ _ _ _ _ _ _ _ _ _ _ _ (show Λ.R.Branches Λ.K.bind SU.group from Λ.V.L.cloth)
 intro a; let V:= gathered (G i) Λ.K.j (A' i) (M i) Λ.R.odd_side Chi.canonical Λ.J.d (wholeZ (N i) w) (W i) a
 let x:=Prod.map (onC (N i)) (onC _) a; have hu:‖f x‖≤1:= (price_letter S (A i) D x).trans (e i); let t:=Satin.knot (N i) w f; rw [show gathered (G i) _ _ _ _ _ _ t (W i) a=f x • V from ?_]; swap; · -- may type infer via RW? ambiguous
    unfold V t gathered before avgF Satin.knot wholeZ; simp_rw [map_smul,←Finset.smul_sum]; exact smul_comm .. |>.symm
 rw [norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) hu).trans (r (show (Σ i:I,Fields (N i)) from ⟨i,a⟩) PUnit.unit)
include h
open scoped Classical
lemma rateable : ∃ c:ℝ,0≤c ∧∀ i:I,∀ x:Catalog S, ‖x‖≤1→ ‖transitionQ Y h S (u i) (P i) x‖≤ c:=by
 let T:= GridStep Λ l S; let N(i):=side Y (P i).val.1 (u i+1); let J:= Σ i:I, {x: Catalog S // ‖x‖≤1} × Fields (N i); let t:= Sigma.fst (β:=fun i:I=> {x:Catalog S // ‖x‖≤1} × Fields (N i)); choose c e H using fun a:Key S=> onu (I:=J) Y S (fun i=> u (t i)) (fun i=> P (t i)) (fun i=>p (t i)) a (fun i=> i.2.1.val) (fun i=>i.2.1.2) (fun i=>i.2.2)
 let V:ℝ:=∑ i:Key S,c i; have hp:0≤V:= sum_nonneg (fun i _=>e i)
 refine ⟨V,hp,fun i x v=>?_⟩; let ξ:=transitionQ Y h S (u i) (P i) x; apply Quest.Chaperone.signage Y h (P i).val.1 (u i+1) T ξ hp (roomy_hosp _ (P i).property.bill.upper); intro y; unfold T ξ; rw [sold_ticket, ingress_compose_sum Y h S (u i) (P i).property,Finset.sum_apply]; exact (norm_sum_le ..).trans (sum_le_sum (fun a _=> H a ⟨i,⟨x,v⟩,y⟩))
end
open scoped Classical
include Y h
lemma ultramare : ∃ C:ℝ,0≤C∧∀ᶠ s in atTop,forall i k:ℕ, ‖snag Y h S s i k‖ ≤ C:=by
 let V:= stable Y; let A:= Σ s:{s:ℕ // Sizing Λ s},PaidPt Y S s.val; let u(a:A):=a.1.val; obtain ⟨C,v,c⟩:= rateable (I:=A) Y h S u (fun a=>a.2) (fun a=>a.1.2); refine ⟨C,v,?_⟩; filter_upwards [V] with s p i k
 by_cases w:Offered Y S s i k
 · rw [snag_pay Y h S s i k w]; apply ContinuousLinearMap.opNorm_le_bound _ v; intro x; by_cases b:x=0; · rw [b,map_zero,norm_zero,norm_zero,mul_zero]
   have he:= norm_pos_iff.mpr b; let z:= ((‖x‖⁻¹:ℝ):ℂ); have hp:‖z‖=‖x‖⁻¹:= by unfold z; rw [Complex.norm_real,norm_inv, norm_norm]
   have h₁:‖z • x‖=1:=by rw [norm_smul,hp,inv_mul_cancel₀ he.ne']
   let B:= transitionQ Y h S s ⟨(i,k),w⟩; have hv:‖B (z•x)‖≤ C:= c (show A from ⟨⟨s,p⟩,⟨(i,k),w⟩⟩) (z•x) h₁.le; rw [map_smul,norm_smul,hp, ← div_eq_inv_mul] at hv; exact (div_le_iff₀ he).mp hv
 rw [snag,dif_neg w]; exact (norm_zero (E:=Slip Λ l S)) ▸ v
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}
variable {P:Call Λ l}{J:Wicket Λ l}
variable (K:Universal Y h u v I E)(R:Rolled Y h u v J P)
include K R
omit Y h K R in
private lemma twoBound {X: Type} [PseudoMetricSpace X] (u v:ℕ→ℕ)(G:ℕ→ℕ→X)(η:ℕ→ X) (z:X) {p:(ℕ→ℕ)→Prop} (H: Couplet u v G η z p) (s:Set X)(t:IsClosed s)(h:∀ i k,G i k∈s) : z∈s∧∀ i,η i∈s:=by
 have he(i:ℕ):η i∈s:= t.mem_of_tendsto (H.inner i) (Eventually.of_forall fun k=> h i (v k))
 exact ⟨t.mem_of_tendsto H.periods (Eventually.of_forall fun i=> he (u i)),he⟩
lemma stamina : ∃ C:ℝ,0≤C∧∀ᶠ s in atTop,‖P S s‖≤ C∧∀ i,‖J S s i‖≤ C:=by
 obtain ⟨c,p,w⟩:= ultramare Y h S; refine ⟨c,p,?_⟩; filter_upwards [w] with s t
 exact twoBound u v _ _ _ (R.evening S s) {x| ‖x‖≤c} (isClosed_le (show Continuous (fun f:Slip Λ l S=> ‖f‖) from (continuous_norm (E:=Slip Λ l S))) continuous_const) t
#print axioms stamina
#print axioms ultramare
end Navy
end YM.CF.Buffered.Afterglow.Hierarchy
