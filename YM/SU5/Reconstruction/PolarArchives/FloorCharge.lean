import YM.SU5.Reconstruction.Trap.Nerve
/-! simultaneous contraction systems on Reach.Pricing the joint floor. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CrossedFrame.MotorPool
open Function Set Filter MeasureTheory InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace Classical
variable {H:Hilbert}{X I:Type}[AddCommGroup X][Module ℂ X](l r:X →ₗ[ℂ] H)
local notation "℘" => WithLp 2 (H.space × H.space)
local notation "M"=>Crew l r
local notation "L"=> pinl l r
local notation "R"=> pinr l r
lemma spend(q:M): ‖q‖^2=‖L q‖^2+‖R q‖^2:= WithLp.prod_norm_sq_eq_of_L2 (q:graph l r).val
lemma pins_action {A B:H.Op} (h:∀ p:X,∃ z:X,A (l p) = l z ∧ B (r p)= r z) (q:M): ∃ z:M, L z=A (L q) ∧ R z=B (R q):=by
 let g(u:M):= WithLp.toLp 2 (A (L u),B (R u))
 have hv: Continuous g:= ?_; swap; · exact (WithLp.prod_continuous_toLp 2 H H).comp (((A.comp L).continuous).prodMk ((B.comp R).continuous))
 have H': g q ∈ graph l r := closure_minimal (s:=range (buildGraph l r)) (t:=g ⁻¹' graph l r) (by
       rintro _ ⟨x,rfl⟩; obtain ⟨z,h,v⟩:=h x; rw [mem_preimage]; change WithLp.toLp 2 (A (l x),B (r x))∈ _; rw [h,v]; exact (buildGraph l r z: graph l r).property)
      ((completeSpace_coe_iff_isComplete.mp (show CompleteSpace (graph l r:Set ℘) from inferInstanceAs (CompleteSpace (graph l r)))).isClosed.preimage hv) (lens_dense l r q)
 exact ⟨(⟨g q,H'⟩:graph l r),rfl,rfl⟩
structure Driver (π:H.Op)(A B:I→ H.Op): Prop where
 press(i:I)(p:X) : ∃ z:X,A i (l p) = l z ∧ B i (r p)=r z
 cost(i:I)(p:H): ‖A i p‖ ≤ ‖p‖ ∧ ‖B i p‖ ≤ ‖p‖
 ok(i:I)(p:H): π (A i p)=π p ∧ π (B i p)=π p
 grant(p:H)(u:∀ i,A i p=p): π p=p
 right(p:H)(u:∀ i,B i p=p): π p=p
variable {π:H.Op} {A B:I→ H.Op}(G:Driver l r π A B)
namespace Driver
include G
private lemma contract_step(i:I){p v:M}(h:L v=A i (L p))(q:R v= B i (R p)): ‖v‖≤‖p‖:= (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by rw [spend,spend,h,q]; exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) ((G.cost i (L p)).1) _) (pow_le_pow_left₀ (norm_nonneg _) ((G.cost i (R p)).2) _))
/-- Both projected costs still in the Crew, with a ONE correlated purchase. -/
lemma gains (p:M):∃ v:M, L v=π (L p) ∧ R v=π (R p) :=by
 let P:= (π.comp L).prod (π.comp R); let K:= P.ker
 haveI : CompleteSpace K:= P.isClosed_ker.completeSpace_coe
 let v:= p-K.starProjection p; have u : P v=P p:= by
    unfold v; rw [map_sub, show P (K.starProjection p)=0 from (K.starProjection_apply_mem p), sub_zero]
 have he: v ∈ Kᗮ:= K.sub_starProjection_mem_orthogonal p -- hidden notation tune
 have h:∀ i, A i (L v)=L v ∧ B i (R v)= R v:=by
    intro i; obtain ⟨w,x,y⟩:=pins_action l r (G.press i) v; have hh: w=v:=by
       have z:w-v ∈ K:=by
          change P _=0; rw [map_sub]; apply sub_eq_zero.mpr; change (π (L w),π (R w))= (π (L v),π (R v)); rw [x,y,(G.ok i _).1,(G.ok i _).2]
       have t:= norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (w-v) v ((K.mem_orthogonal v).1 he (w-v) z)
       have hz : ‖w‖^2≤‖v‖^2:= pow_le_pow_left₀ (norm_nonneg _) (contract_step l r G i x y) 2
       rw [sub_add_cancel] at t
       apply sub_eq_zero.mp <| norm_eq_zero.mp ?_; nlinarith
    subst w; exact ⟨x.symm,y.symm⟩
 rw [show P v= (π (L v),π (R v)) from rfl, G.grant (L v) (fun i=> (h i).1), G.right (R v) (fun i=>(h i).2)] at u
 exact ⟨v,congrArg Prod.fst u,congrArg Prod.snd u⟩
/-- Get the synchronized registers over ONE sequence. -/
lemma ledger (p:X) : ∃ v:ℕ→X,Tendsto (fun n=> l (v n)) atTop (𝓝 (π (l p)))∧ Tendsto (fun n=> r (v n)) atTop (𝓝 (π (r p))) := by
 obtain ⟨v,h,t⟩:=gains l r G (buildGraph l r p); obtain ⟨f,b,e⟩:=mem_closure_iff_seq_limit.mp (lens_dense l r v); choose x hx using b
 rw [←(tap_build l r p).1,←(tap_build l r p).2,←h,←t] ; change ∀ i, buildGraph l r (x i)=f i at hx; rw [← funext hx] at e
 exact ⟨x,((L).continuous.tendsto v).comp e, ((R).continuous.tendsto v).comp e⟩
end Driver
end YM.CrossedFrame.MotorPool
