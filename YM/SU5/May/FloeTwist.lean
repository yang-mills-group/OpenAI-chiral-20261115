import YM.SU5.FiniteGaugeData.Marked.Variation.Vitrine
import YM.SU5.Reconstruction.Hygrometry.Landing
import YM.SU5.May.FloeWeight
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Floe
open Function Filter Finset Fir Lattice Laurent Next.Free Bloch Lat Ember Jill Rush
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Onyx Fock SU Flare Kea Sods Emu Dial Cube Tulip Spire Scroll Thera
open Fock Reflect
open Hygrometry Personality PriceCliff
open Stationary (Gaia)
open Buffered.Lifted Buffered.Afterglow.Tower.Tilted
variable {N:Side} (u: Odd N.val)(P:Ramp)
local notation "N+"=>N.val
noncomputable def reverseF (P:Ramp)(k:Flap N)(i:Axis):Fin N.val:= if i=P.a then Fin.rev (k P.b) else if i=P.b then Fin.rev (k P.a) else k i
lemma reverse_e(k:Flap N) : reverseF P (reverseF P k) =k:=by funext i; by_cases h:i=P.a<;>by_cases e:i=P.b<;> simp [reverseF, * ,P.cross]
noncomputable def reflected(P:Ramp)(j:ℕ): Trace j N ≃ Trace j N:= ⟨fun k i=> reverseF P (k i),fun k i=>reverseF P (k i),fun x=>funext fun i=>reverse_e P _,fun x=>funext fun i=>reverse_e P _⟩
private lemma rev_mid (p:Fin N.val): ((Fin.rev p).val:ℤ)+p.val=N.val-1:=by have ht:=p.isLt; change (↑((_ -(_ + 1)):ℕ):ℤ)+_= _; omega
include u
lemma trem_a (c:Flap N): trem N (reverseF P c) P.a= - trem N c P.b:=by simp only [trem,reverseF,if_true]; linarith only [rev_mid (c P.b),mid_double N u]
lemma trem_b (c:Flap N): trem N (reverseF P c) P.b= - trem N c P.a:=by simp only [trem,reverseF,P.cross,if_false,if_true]; linarith only [rev_mid (c P.a),mid_double N u]
lemma trem_transform (c:Flap N): trem N (reverseF P c)=P.s.act (trem N c):=by
 funext i; by_cases h:i=P.a; · rw [h,P.move_a,trem_a u]
 by_cases e:i=P.b; · rw [e,P.move_b,trem_b u]; -- semicolon
 rw [P.move_h _ h e]; simp [trem, reverseF, h, e]
variable (j:ℕ)
local notation "W"=> whisper P
lemma trace_deck (c:Trace j N): traces N j (reflected P j c)=P.s.act (traces N j c):=by
 change traces N j _=(P.s.actEquiv (R:=ℤ)) _; unfold traces; rw [map_sum]; exact sum_congr rfl fun i _=> trem_transform u P _
omit u in
lemma branch_clock (x:Cover) : nodeC ((whisper P).cell x)=P.s.act (nodeC x):=(P.mode_motion (nodeC x)) ▸ (Shape.mote P.plan x).symm
private lemma node_at_point (x v:Cover) : nodeC (point N x v) = N.val • nodeC x + 2 • v:=by funext i; have he:=point_cost N u x v i; unfold nodeC; simp only [nsmul_eq_mul, Pi.add_apply, Pi.mul_apply, Pi.natCast_apply, Pi.one_apply, Nat.cast_ofNat,Pi.ofNat_apply]; linarith only [he]
lemma reflect_chart (x:Cover)(c:Trace j N) : (whisper P).cell (point N x (traces N j c))= point N ((whisper P).cell x) (traces N j (reflected P j c)):=by
 apply Buffered.Afterglow.Satin.nodeC_inj; -- tune
 rw [branch_clock,node_at_point u, node_at_point u,branch_clock,trace_deck u]; change (P.s.actEquiv (R:=ℤ)) (N.val • _+ 2 • _)=N.val • (P.s.actEquiv (R:=ℤ)) _+2 • (P.s.actEquiv (R:=ℤ)) _; rw [map_add,map_nsmul,map_nsmul]
end YM.CF.May.Floe
#print axioms YM.CF.May.Floe.reflect_chart
