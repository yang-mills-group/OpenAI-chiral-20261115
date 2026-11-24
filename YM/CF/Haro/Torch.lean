import YM.CF.Haro.Celtic
import YM.CF.Haro.Walk
import YM.CF.Prism.Rock
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
variable {c f:Side}(j m:ℕ)(e:Even j)(h:2 ≤ j)
variable (G:Ratio c f)(ho:Odd G.count.val)
open Branch Laic
variable {t:ℝ}(Y: cro G t)(W: Meter TailB G t)(V: Meter Grave G t)
open Skye Precision
open Jet
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{z:E}
-- value at rotated ALL. Fine fields read near stock literal. 
abbrev mater(g:SU.E):= (matter g).val
lemma lucent:∃ H:ℝ,1 ≤ H∧∀ x: SU.group.Color,‖x‖ ≤ 1→ ‖mater (SU.group.lieExp x)-1‖ ≤ H*‖x‖:=by
 let F(x:SU.group.Color):=mater (SU.group.lieExp x); have hp: ContDiff ℝ (1:ℕ) F:=matt fun i j=>(Prism.curr true i j).of_le le_top
 obtain ⟨C,hC,K⟩:= Jet.payment_for 1 (isCompact_closedBall (0:SU.group.Color) 1) F (fun _ _=>hp.contDiffAt)
 refine ⟨max 1 C, le_max_left ..,fun x hx=>?_⟩; have hv:F 0=1:=by unfold F mater; rw [show SU.group.lieExp 0=1 from (by simp), map_one]; rfl -- tune
 have he:= (convex_closedBall (0:SU.group.Color) 1).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (f:=F) (fun i _=>hp.differentiable (by norm_cast) i) (fun i hi=>(norm_iteratedFDeriv_one F).symm.trans_le ((K i hi).norm_le 1 le_rfl)) (mem_closedBall_self (by norm_num)) (mem_closedBall_zero_iff.mpr hx); rw [hv,sub_zero] at he; exact he.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _))
variable {k n:ℕ}{K d b ε v:ℝ}
lemma cereal (U:E→SU.E)(k:ℕ)(v:ℝ)(b:ℝ)(z:E)(p:Rill.Tender U z b k)(e:∀ x:E→SU.E, Rill.Tender x z b k→ Shake (fun i=>brand (x i)) z (v*b) k)(h:‖mater (U z)-1‖≤ d): Allows k (fun i=>mater (U i)-1) z (max (v*b) d):=by
 have hv:= shakesH (fun i=>mater (U i)) z _ k (show Shake (fun i=>mater (U i)) z (v*b) k from ((shakeL _ _ (e U p) (ContinuousLinearMap.fst ℝ _ _)).bag (mul_le_of_le_one_left (e U p|>.price) (ContinuousLinearMap.norm_fst_le ..)))) (1:Op Slot)
 exact hv.paid h
-- path near
lemma baton(W:Pane c)(x:Seat c)(U:Lattice.Walk)(p:∀ i:Pressure.Bond (More c), Skye.ends i⊆ reelQ x U→ ‖mater (W i)-1‖≤ K): ‖mater (travel W x U)-1‖ ≤ U.length*K:=by
 have he(u v:SU.E): ‖mater (u*v)-1‖ ≤ ‖mater u-1‖+ ‖mater v-1‖:=by
    let A:=mater u; let B:=mater v; rw [show mater (u*v)=A*B from congr_arg Subtype.val (map_mul ..),show A*B-1=(A-1)+A*(B-1) by rw [mul_sub,mul_one]; abel]; rw [←show ‖A * (B-1)‖=‖mater v-1‖ from CStarRing.norm_coe_unitary_mul (matter u) (B-1)]; exact norm_add_le ..
 induction U generalizing x with
 | nil=> simp only [travel,List.length_nil,mater,map_one]; simp
 | cons s l ih=>
   let Y:= reelQ x (s::l); let Z:=reelQ (x+s.vec) l; have ht: Y= insert x Z:=List.toFinset_cons ..; have hz: Z⊆ Y:=ht ▸ subset_insert _ _; have hv: ends (s.used x) ⊆ Y:=by
      have hx:x∈Y:= List.mem_toFinset.mpr (List.mem_cons_self ..); have hy:x+s.vec∈Y:=hz (List.mem_toFinset.mpr (by cases l <;> simp [visits]))
      unfold Skye.ends; rcases s with ⟨t,b⟩; cases b; · exact insert_subset hx (singleton_subset_iff.mpr hy)
      have h:x+ Lattice.Step.vec ⟨t,true⟩= x-step t:=Eq.symm (sub_eq_add_neg ..); exact insert_subset (show x-step t ∈ _ from h ▸ hy) (singleton_subset_iff.mpr (show x-step t+step t∈ _ from (sub_add_cancel x (step t)).symm ▸ hx))
   have hh: ‖mater (s.read W x)-1‖≤ K:=by
      unfold Step.read; let u:=s.used x; split; swap; · exact p u hv
      let A:=mater (W u); rw [show mater _ =star A from congr_arg Subtype.val (map_inv matter _)]; rw [← star_one (R:=Op Slot),←star_sub,norm_star]; exact p u hv
   rw [travel,List.length_cons,Nat.cast_add,Nat.cast_one,add_mul]; exact (he ..).trans ((add_le_add hh (ih _ (fun b k=> p b (k.trans hz)))).trans_eq (by ring))
open PhysicalNext.JointLoad RG Pressure
lemma matchL (x:Seat c)(W:Lattice.Walk)(V:E→ Pane c)(z:E)(K L:ℝ)(k n m:ℕ)(r:ℝ)(B:ℕ)(g:Seat c→ SU.E)(o:Seat c)(P:BudgetPoint)(hp:Heir.Canvas P o m (V z) g n K)(hK:0 ≤ K)(p:W.length ≤ 2^k)(b:W.length ≤ B)(h:reelQ x W⊆halo m {o})(hx:K*P.threshold*(1+(m:ℝ))≤1)(hg:1 ≤ L)(ht:∀ x: SU.group.Color,‖x‖ ≤ 1→ ‖mater (SU.group.lieExp x)-1‖ ≤ L*‖x‖)(hk:Rill.Wind d (·*·) n r)(hv:Rill.Wind d (fun i _=>i⁻¹) n r)(hw:1≤r)(hq:0 ≤ ε)(he:Cash (k+5) ε r ≤ d)(hF:∀ i:Bond (More c),ends i⊆reelQ x W→ Rill.Tender (fun y=>V y i) z ε n)(u:∀ F:E→SU.E, Rill.Tender F z (Cash (k+5) ε r) n→ Shake (fun i=>brand (F i)) z (v*Cash (k+5) ε r) n): Allows n (fun v=>mater (travel (Lattice.gauge g (V v)) x W)-1) z (max (v*Cash (k+5) ε r) ((B:ℝ)*(L*(K*P.threshold*(1+(m:ℝ)))))):=by
 let D:= L*(K*P.threshold*(1+(m:ℝ))); have hp0 : 0 ≤ D:= by unfold D; have hz:=P.threshold_pos; positivity
 apply cereal _ n v (Cash (k+5) ε r) z _ u
 · refine (baton _ _ _ ?_).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr b) hp0); intro i w
   obtain ⟨x,h1,hp'⟩:=halo_spec.mp (h (w (mem_insert_self ..))); rw [mem_singleton.mp h1] at hp'
   have hh:‖Heir.crop o m g (V z) i‖≤ K*P.threshold*(1+(m:ℝ)) := (hp.size i hp').trans (by have :=P.threshold_pos; gcongr)
   rw [show Lattice.gauge g (V z) i= _ from Siete.lift_q hp i hp']; exact (ht _ (hh.trans hx)).trans (mul_le_mul_of_nonneg_left hh (zero_le_one.trans hg)) -- tune bullet
 have hc:k+5=k+3+2:=Nat.add_assoc k 3 2|>.symm
 rw [show Cash (k+5) ε r=Cash (k+3) (r^2*ε) r from (by unfold Cash; rw [hc,pow_add r (k+3),mul_assoc])]; change Rill.Tender _ _ (r^(k+3)*(r^2*ε)) n; refine wand hk hv hw (by positivity) (fun v=> Lattice.gauge g (V v)) _ _ k p ?_ ?_
 · unfold Cash; rw [←mul_assoc,←pow_add]; exact he
 intro i s; rw [pow_succ r 1,pow_one,mul_assoc]; apply tapG hk hw _ g i (hF i s); refine le_trans ?_ he; unfold Cash; gcongr; exact (pow_one r).symm.le.trans (pow_le_pow_right₀ hw (by omega))
end YM.CF.Haro
