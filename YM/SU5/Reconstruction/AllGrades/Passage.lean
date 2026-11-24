import YM.SU5.Reconstruction.AllGrades.Caption
import YM.SU5.Reconstruction.UVPrice.PayLow
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section
namespace YM.ConePrice.Session
open Function Set Filter MeasureTheory Spectral Analysis InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real Picket Roy
variable {H W:Hilbert} {a: Axis} {Γ: AddSubgroup ℝ} (K: OS.Semigroup H a)(T:Germ.Alliance (CF.Buffered.Afterglow.Tower.Trans a) Γ H)(S:OS.Semigroup W a)
local notation "U" j:max v:max=> (T.crew j).play v
/-! Re-localize the spectrum on THIS REAL gravity, from old vs new, no fake spatial momenta. -/
variable {γ : AddSubgroup ℝ} (P:γ →+ Γ)
noncomputable def earnCrew (i:CF.Buffered.Afterglow.Tower.Trans a): Players γ H where
 play u:= U i (P u)
 pulls u x:= (T.crew i).pulls ..
 play_zero:= by rw [map_zero]; exact (T.crew i).play_zero
 piles u w:=by rw [map_add]; exact (T.crew i).piles ..
noncomputable def pull : Germ.Alliance (CF.Buffered.Afterglow.Tower.Trans a) γ H := ⟨earnCrew T P,fun i j u v=> T.cCom ..⟩
local notation "Y"=>pull T P
private lemma knows (s:List (CF.Buffered.Afterglow.Tower.Trans a))(Z:CF.Buffered.Afterglow.Tower.Trans a→γ): (Y).raw s Z=T.raw s (P ∘ Z):=by
 induction s with
 | nil=>rfl
 | cons j s ih=> rw [Alliance.raw_step,ih, Alliance.raw_step]; rfl
variable (Q:∀ v:γ,(P v:ℝ)=v)
local notation "r₁"=> Coupon a γ
local notation "r₂"=> Coupon a Γ
include Q
noncomputable def port (f: r₁): Coupon a Γ:=⟨fun i=>P (f.stamp i),by rw [Q]; exact f.ground⟩
local notation "P₀" f:max=> port P Q f
lemma _root_.YM.ConePrice.Session.time_port (f:r₁): (P₀ f).dt=f.dt:=by unfold Coupon.dt; rw [show (port P Q f).stamp a=P (f.stamp a) from rfl,Q]
lemma x_port (f:r₁): (P₀ f).displacement = f.displacement:=by apply congrArg (diameter); funext i; exact Q _
lemma financed (x: H): Lore K T x ∘ port (a:=a) P Q= Lore K (Y) x:=by funext f; unfold Lore Live Function.comp; dsimp only; rw [time_port]; exact congrArg (fun S0:H.Op=> inner ℂ x ((K.E f.dt*S0) x)) ((knows T P (look a) (fun i=>f.stamp i.val)).symm)
lemma pleasure {f:Coupon a Γ→ℂ}(p:f∈Coupon.Population S Γ) : f ∘ port (a:=a) P Q∈ Coupon.Population S γ:=by
 apply closure_minimal (t:={f|f ∘ port (a:=a) P Q∈ Coupon.Population S γ}) ?_ (isClosed_closure.preimage (show Continuous (fun k: r₂→ℂ=> k ∘ port (a:=a) P Q) from continuous_pi (fun i': r₁=>continuous_apply _))) p
 rintro v ⟨x,rfl⟩; refine subset_closure (Set.mem_range.mpr ⟨x,?_⟩); funext p; dsimp only [Function.comp_apply]; unfold Coupon.tagT Coupon.cash; rw [time_port,x_port]
-- from square receipts to forward. γ dense. Need apply for old coupons. positivity WIN.
omit Q
variable {J: Hilbert}(V:OS.Semigroup J a) (d:Dense (γ:Set ℝ))(e: Backs S) (p:Forward S) (g:∀ x:J,(Coupon.tagT (Γ:=γ) V x)^2∈Coupon.Population S γ)
include d e p g
lemma covers_forward : Forward V:=by
 have ht:Shelf S⊆ front a:=closure_minimal (iUnion_subset fun x=> MeasureTheory.Measure.support_subset_of_isClosed (t:=front a) (closed_front a) (ConePrice.forward_ae S x p)) (closed_front _)
 have hz:Shelf V⊆ front a:=by
    intro x v; have hx:0 ≤ x a:=shelf_ePays V x v
    let f:= Coupon.receipt x (Γ:=γ) (a:=a)
    have hv : f^2∈ Coupon.Population S γ:= by
       apply closure_minimal (t:={f:r₁→ℂ|f^2∈Coupon.Population S γ}) ?_ (isClosed_closure.preimage (f:=fun f:r₁→ℂ=>f^2) (continuous_id.pow 2)) (Coupon.climb V x v); exact Set.range_subset_iff.mpr g
    have h₂:f^2= Coupon.receipt (Γ:=γ) (x+x):= by funext u; rw [Coupon.receipts_add u x x hx hx, Pi.pow_apply, pow_two]
    rw [h₂] at hv; have h:=ht (Coupon.in_price S d e _ (add_nonneg hx hx) hv); change ‖SEP a _‖≤ _ at h; rw [←two_smul ℝ x,map_smul,norm_smul] at h; change ‖(2:ℝ)‖*_≤ (2:ℝ)*x a at h; change ‖_‖≤ _; rw [Real.norm_eq_abs, abs_of_pos (by norm_num)] at h; linarith
 ext1 v; apply (V.ℚmeasure.null_pair (closed_front a).isOpen_compl.measurableSet v).mp; refine measure_mono_null (compl_subset_compl.mpr (Set.Subset.trans ?_ hz)) Measure.measure_compl_support; exact Set.Subset.trans (subset_iUnion (fun x : J => Measure.support (V.ℚmeasure.diagonal x)) v) subset_closure
end YM.ConePrice.Session
#print axioms YM.ConePrice.Session.covers_forward
#print axioms YM.ConePrice.Session.pleasure
