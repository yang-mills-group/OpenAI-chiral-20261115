-- adaptation of LoomForce.FrameTaylor/FinePoly to sector
import YM.SU5.LoomForce.FinePoly
import YM.SU5.SatinWard.Resolution.Spark
import YM.SU5.WindTorque.Docket
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.LitCurrent.Surplus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{P T:SOp N}{a b d v g t u:ℝ}{r k:ℕ}
open Next.Rank Next.Rank.Spindle
open CF.Pannier.Chancel.Rous
variable (B:ℕ)(h: 2*(B+1)<(More N).val)(V:Rules SU.group)
local notation "A"=> tangD N
open Urn Salt
variable {p:BudgetPoint}{K:Scree.Loom N}{e:ℝ}{q:ℕ} (bI:Chamber.Division)(x:Site N)(z:Checked p K e d a k q)(E:Pattern P T r d a v)
variable (bP: p.B=B)
local notation "Τ" => p.threshold
local notation "ℓ" => occupancy a v g
local notation "Λ" => HopeT d b g 3
local notation "τ" => (Surplus.btax K p bI x k E)
local notation "S" => (offsetMask p.B x)
local notation "ξ" => node x
local notation "λp" => 4* (B:ℝ)
-- canonical aperture even when no tag licensed -- give zero output on failure.
local notation "TX" => btaxpayer bI x E (k:=k)
include z E h
variable (W:TankSpot d u)(Q: HopeT d b g 3)
variable (A':Mantle V B p.threshold u) (U: Pane N)
local notation "J"=>install B (node x) ∘L collectF B (node x) h
local notation "Φ"=> install B (node x) (wired 1 (node x) B U)
local notation "doll"=> untouched (Chamber.grantA bI E x)
include bP V W A'
lemma bpermit_trace (f:pingS Τ S U) : Healthy Τ (Spindle.patch B ξ) U ∧ ‖Φ‖≤2*(4*B*Τ) ∧ τ U=doll k (increment 1 Φ) ∧ ‖Φ-J (paintedMark B ξ U 1)‖≤ (V.C+SU.group.colorScale)*(4*B*Τ)^2:= by
  let X:=install B ξ (wired 1 ξ B U)
  have hx:S=Spindle.patch B ξ:= by unfold offsetMask; rw [bP]; rfl
  have ht: Healthy Τ (Spindle.patch B ξ) U:= hx ▸ ping_le f
  obtain ⟨c,y,g⟩:= frame_exact B ξ h V U ht p.threshold_pos A'.snow
  let P':= increment (1:Pane N) X; have hu:= W.paid N X (le_trans y A'.door)
  refine ⟨ht,y,?_,g⟩
  rw [← btax_invariant bI x z E (fingers U ξ)]
  have h': k≤ B:= by have ht:=z.extra; omega
  refine btax_degree bI x z E (spine U ξ) _ ((pingB ..).2 f) ?_ (agrees_mono c (Corona.halo_mono h' (Subset.refl _)))
  exact ⟨fun s i j g=>(hu.1 s i j g).trans (half_le_self z.angle.le), fun s i j g=>(hu.2 s i j g).trans (half_le_self z.angle.le)⟩

-- before making the Paint claim, have this sup at every actual depth including beyond gates
include Q
lemma binBasket : ‖τ U‖ ≤ broadCash ℓ (λp * Τ) := by
  have ht:=p.threshold_pos
  let t:=4*(B:ℝ)*Τ; have hv:0≤t:=by unfold t; positivity
  have hp:= stencil_cost z E x Q
  by_cases f:pingS Τ S U; swap
  · change ‖(live K p k x (Chamber.grantA bI E x) U).trace‖≤_; rw [live, Set.indicator_of_notMem f,Matrix.trace_zero, norm_zero]; unfold broadCash; positivity
  obtain ⟨-,y,g0,-⟩:= bpermit_trace B h V bI x z E bP W A' U f
  let X:= install B ξ (wired 1 ξ B U)
  have he:= baperture_taylor bI x z E W Q X (le_trans y A'.door); have hx:= baperture_cost bI x z E Q X X
  rw [g0]; refine le_trans (by let D:=doll k (increment 1 X); have hp:= norm_add_le (D - TX X X) (TX X X); rw [sub_add_cancel] at hp; exact hp) (?_ : ‖doll k (increment 1 X) - TX X X‖+ ‖TX X X‖ ≤ _)
  refine add_le_add (le_trans he ?_) ((by rw [pow_two]; exact hx : ‖TX X X‖ ≤ (2:ℝ)⁻¹*ℓ*‖X‖^2).trans ?_) <;> gcongr

-- final Broom-birth estimate: unlike path-global projector expense
-- this makes the approximation on WellDrawn at both tiny and ordinary lease.
def blapAsset (bI:Chamber.Division) (x:Site N) (k B:ℕ)(h: 2*(B+1)< (More N).val)(E:Pattern P T r d a v)(q:FrameA B):ℂ:=
    btaxpayer bI x E (k:=k) ((install B (node x) ∘L collectF B (node x) h) q) ((install B (node x) ∘L collectF B (node x) h) q)
lemma bpaint_it {α:ℝ}(hα:0≤α)(f:pingS Τ S U) (s:Tiny (Spindle.patch B ξ) U α): ‖τ U - blapAsset bI x k B h E (receiveMark B ξ U 1)‖ ≤ broadError ℓ (λp * Τ) (rawError V (λp * Τ) B Τ α):= by
  obtain ⟨fX,hx,fη,hμ⟩:= bpermit_trace B h V bI x z E bP W A' U f
  let X:= Φ; let Y:=paintedMark B ξ U 1; let F:=receiveMark B ξ U 1; let c:=ℓ
  let G:=J; let F':=G F; let L:= λp * Τ
  let δ:= 2*group.colorScale*(4*B*α)*Τ; let w:= rawError V L B Τ α
  have hl(i:Turn B):= receive_cost B ξ h U fX s hα (x:=i)
  have hp:=p.threshold_pos; have hw:=group.colorScale_pos; have hD:=V.positive
  have hδ: 0≤ δ:=by unfold δ; positivity
  have hY:‖Y-F‖≤δ:= (pi_norm_le_iff_of_nonneg hδ).mpr fun i=>(hl i).1
  have ht: ‖F‖≤ Τ:=(pi_norm_le_iff_of_nonneg hp.le).mpr fun i=>(hl i).2.2
  have hF (y:FrameA B){v:ℝ}(p:‖y‖≤v): ‖G y‖≤ λp * v:= (install_price ..).trans ((collect_price B ξ h y).trans (mul_le_mul_of_nonneg_left p (by positivity)))
  have hf : ‖F'‖ ≤ L:= hF _ ht
  have hK : ‖X-F'‖ ≤ w:= by
    have hc := hF _ hY; rw [map_sub] at hc
    exact (norm_sub_le_norm_sub_add_norm_sub X (G Y) F').trans (add_le_add hμ hc)
  have ha:0≤ℓ:= stencil_cost z E x Q
  have hu: ‖TX X X-TX F' F'‖≤ (2:ℝ)⁻¹*ℓ*w*(2*L+L):= by
    have hr:TX X X-TX F' F'= TX (X-F') X+ TX F' (X-F'):=by simp only [map_sub,_root_.sub_apply]; abel
    rw [hr]; apply (norm_add_le ..).trans; rw [mul_add]
    have ho(U V:A)(u v:ℝ)(hu:‖U‖≤u)(hv:‖V‖≤v): ‖TX U V‖ ≤ (2:ℝ)⁻¹*ℓ*(u*v):=(baperture_cost bI x z E Q U V).trans (by have hg:=(norm_nonneg _).trans hu; gcongr)
    exact add_le_add ((ho (X-F') X w (2*L) hK hx).trans_eq (by ring)) ((ho F' (X-F') L w hf hK).trans_eq (by ring))
  rw [fη]; apply (norm_sub_le_norm_sub_add_norm_sub _ (TX X X) _).trans; refine add_le_add ((baperture_taylor bI x z E W Q X (le_trans hx A'.door)).trans ?_) hu
  gcongr
#print axioms binBasket
#print axioms bpaint_it
section poly
omit z bP V W A' Q
open Buffered Pannier.Chancel.Rous Next.Rank Spindle
local notation "I"=> Sheds B
local notation "AV"=> FrameA B
variable (k:ℕ)
def bcoins (i j:Sheds B) := stepValue B (node x) h (untouched (Chamber.grantA bI E x) k) i j
-- sym average since Ward quadratic gauge. Using star for physical reflection and later estimator
noncomputable def bcashY (i j:Sheds B) := (bcoins B h bI x E k i j+bcoins B h bI x E k j i) /2
local notation "c"=> bcashY B h bI x E k
lemma bcashYaw(i j:Sheds B): c i j=c j i:=by unfold bcashY; rw [add_comm (bcoins ..)]

def bfineY (U : Sheds B→ℝ): ℂ:= ∑ u:Sheds B,∑ v:Sheds B,bcashY B h bI x E k u v*(U u:ℝ)*(U v:ℝ)

lemma bpolynomial (X:FrameA B): blapAsset bI x k B h E X=bfineY B h bI x E k (snapFace B X):= by
 let V:=snapFace B X; let t(i:I):= J (Stern i); let Z:=btaxpayer (k:=k) bI x E
 let M:= J X; let U:=bcoins B h bI x E k
 have ht:M=∑ i:I,V i • t i:=by rw [←Finset.sum_congr rfl (show ∀ i:I,i∈univ→ J (V i • Stern i)=V i • t i from fun i _=>map_smul ..),← map_sum]; exact congrArg (fun P:AV=> J P) (snapAll B X).symm
 have hf: Z M M=∑ i:I,∑ j:I,(U i j)*(V i:ℝ)*(V j:ℝ):= by
    rw [ht,map_sum Z,_root_.sum_apply]; refine sum_congr rfl fun i _=>?_ ; rw [map_sum]; apply sum_congr rfl; intro j _; rw [map_smul,map_smul Z]; change (V j) • (V i) • (U i j)= _; simp [Complex.real_smul]; ring
 let b(i j:I):=U i j * (V i:ℝ)*(V j:ℝ); let Q(i j:I):=U j i * (V i:ℝ)*(V j:ℝ)
 unfold bfineY; change Z M M= _; rw [hf]
 have he(i j:I):c i j*(snapFace B X i:ℝ)*(snapFace B X j:ℝ)=(b i j+Q i j)/2:=by unfold bcashY b Q V U; ring
 simp_rw [he]; rw [show Q=fun i j=> b j i from funext₂ (fun i j=>by unfold Q b; ring)]
 simp_rw [←sum_div,sum_add_distrib]; rw [sum_comm (f:=fun i j:I=> b j i)] -- maybe syntax
 change _=_; ring

lemma bcharge_lease : ∑ i:I,∑ j:I, ‖c i j‖ ≤ charges B (node x) h (untouched (Chamber.grantA bI E x) k):= by
 let f(i j:I):= ‖bcoins B h bI x E k i j‖; let V:=∑ i:I,∑ j:I,f i j; change _ ≤ V
 have he(i j:I): ‖c i j‖ ≤ (f i j+f j i)/2:=by unfold bcashY; rw [norm_div,Complex.norm_ofNat]; exact div_le_div_of_nonneg_right (norm_add_le ..) (by norm_num)
 refine le_trans (sum_le_sum (fun i _=> sum_le_sum (fun j _=> he i j))) (Eq.le ?_); simp_rw [←sum_div,sum_add_distrib]; rw [sum_comm (f:=fun i j:I=> f j i)]; change (V+V)/2=V; ring

lemma bevaluator_roll (ρ:ℝ)(X:I→ℝ): bfineY B h bI x E k (ρ • X)=(ρ:ℂ)^2 * bfineY B h bI x E k X:=by
 unfold bfineY; simp_rw [mul_sum, Pi.smul_apply, smul_eq_mul,Complex.ofReal_mul]; refine sum_congr rfl fun i _=>sum_congr rfl (fun j _=>?_); ring
end poly
end YM.CF.LitCurrent.Surplus
