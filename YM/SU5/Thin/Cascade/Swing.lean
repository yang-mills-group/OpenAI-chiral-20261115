import YM.SU5.Thin.Cascade.Beauty
import YM.SU5.FiniteGaugeData.Signal.OceanPort
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Rapids
open Function Filter NormedSpace Fock Thera Finset Lattice Fir Lat Laurent Kea Tulip Rush Jill Cube Ember SU Dial Peaks Cascade Flare Scroll Spire Gall
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder Classical ContDiff
attribute [local instance] opCStarAlgebra
-- AT actor basis, issuing shear covering every flat Slot, on the actual odd spin orientation. Do not infer a uniform operator norm bound from fare here.
def LiftMark (C:ℝ)(j:ℕ)(N: Side): Prop:=∀ M:Jill.Male, ∃ U: Op (Single N), Clad (tickA N) (spar j M (1: Bkg (More N))) 1 1 U ∧ SnowCone (laneP (spar j M 1) 1 U) C
lemma assemblesAt (j:ℕ)(hj:1≤j): ∃ C≥(0:ℝ),∃ k:ℕ,∀ N:Side,Even N.val→ k≤ N.val→ LiftMark C j N:=by
 obtain ⟨m,C,hM,hC,z⟩:=Jill.zip hj; -- could choose tiny R such that no risks AND π bound r π²<=1/8 for all.
 let r:= min (m/2) (1/(8*Real.pi^2)); have hm:0<r:= lt_min (half_pos hM) (by have hp:=Real.pi_pos; positivity); let s:= heave r
 obtain ⟨c,h,D⟩:=rod j s le_rfl hm; let A:= c^2*Real.pi; obtain ⟨x,xP,g⟩:= fame hj hm (show 0<A from (by unfold A; positivity)); obtain ⟨v,H⟩:=gave j hj
 refine ⟨x+2,by linarith,v,fun N p u=>?_⟩
 intro M; let S:=too N; let t:=Ember.pinch N; have hh: Pad j N:= H N p u; have he:0<t:= pinch_pos N; have ht:r*t^2 ≤ 1/8:=by
    have hx:t ≤ Real.pi:= div_le_self Real.pi_pos.le (by exact_mod_cast N.property); have hr:r≤1/(8*Real.pi^2):= min_le_right ..; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he.le hx 2) hm.le); have hp:0<Real.pi^2:=by positivity
    rw [le_div_iff₀ (by positivity : 0<8*Real.pi^2)] at hr; linarith only [hr]
 obtain ⟨U,Q,T,V,Z⟩:=D N p ht emptyC S M s (Set.mem_Icc.mpr ⟨le_rfl,le_rfl⟩); let W:=risky S j M r; let F:= portT S M j r s; let E:=mateV W (s*t)
 have hx(i:Stag N): i∉W:=by
    intro e; have he': high_d M S i j ≤ r*t^2:= (mem_filter.mp e).2; let P:=Kea.angle S i; have hte:t≤ ‖P‖:=by unfold P S; rw [too_u]; exact (cohere (i.1 0)).trans (norm_le_pi_norm (Lat.pm i.1) 0)
    have hv:= (z M P (up_p S p i)).1; unfold high_d at he'; change disk j M P ≤ _ at he'; nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he.le hte 2) hM.le,hv,he',mul_lt_mul_of_pos_right (show r < m from (min_le_left ..).trans_lt (half_lt_self hM)) (show (0:ℝ)<t^2 from pow_pos (pinch_pos _) _)] -- normalization uses t; repetitive
 have hm': shake W=0:=funext fun i=>by unfold shake; rw [if_neg (hx i)]; rfl
 have hz: portT S M j r s=1:=by unfold portT openW; change 1 + (s* _ ) • shake W=_; rw [hm',smul_zero,add_zero]
 have hy:E=1:=by unfold E mateV openW; rw [hm',smul_zero,add_zero,star_one]
 let A₀:= tickA N; let B:= spar j M (1:Bkg (More N)); let B':= field S j M; have heq: B=Dofu N B':=by unfold B; rw [← Signal.Sparkle.LocalPlane.free1]; exact hh.2 emptyC S M
 let e:= Dofu N U; have hu: Clad B A₀ 1 1 e:=by
    have h:= torn S p j M U F E Q; rw [show F=1 from hz,hy,map_one] at h; exact heq.symm ▸ h
 refine ⟨star e,dual hu,liftCore hu ?_⟩
 have hp(i:Single N):‖acts (laneP A₀ 1 e) (basisKet i)‖≤ x ∧ ‖acts (star (laneP A₀ 1 e)) (basisKet i)‖≤ x:=by
    have he' := g (M:=M) (Emu.tilt F U) S p (Emu.attire Q p hm h T Z) i; rw [Emu.tall_s,show F=1 from hz,map_one] at he'; exact he'
 exact ⟨fun i=>(hp i).1,fun i=>(hp i).2⟩
end YM.CF.Rapids
