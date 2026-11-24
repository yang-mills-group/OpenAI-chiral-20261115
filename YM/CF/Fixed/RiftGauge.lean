import YM.CF.Fixed.TimeTransform
import YM.CF.Graph.Sage

/-! Abelian seam discrepancy in flight. Actual cap. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Fixed.Rift
open Function NormedSpace Matrix Lattice Finset Filter Fock BZ Mir Lat Scroll SU Bulk
open Reed.Bare Cube
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side} {c b d:ℝ} {p : Side}
variable (α β : ℝ)
abbrev phase_b(x:ℝ)(y:Slot):ℝ:=2 * infla y (x/2)
abbrev αZ (α β:ℝ)(x:Per (More N)) : ℝ:= if x=1 then α else if x= -1 then β else 0
def airy (N:Side)(α β:ℝ) : Bkg (More N) := fun p=> if p.2=1 then cue ((αZ α β (p.1 0))/2) else 1
def θ_issue (N:Side)(u v:ℝ): AxisA N := fun x t i=> if i=0 then ages (phase_b u x) (phase_b v x) t else 0
lemma freq_spread (x: Ion N): freqZ (θ_issue N α β) x= spread N (phase_b α x.2) (phase_b β x.2) (zmom x.1):=by funext i j; unfold freqZ θ_issue spread; by_cases g:j=0 <;> simp [g,update_of_ne]
lemma far_one (h:1<N.val) : (1:Per N).val=1:=by rw [←Nat.cast_one,ZMod.val_natCast_of_lt h]
lemma near_one (N:Side) : ((-1:Per N).val)+1=N.val:=by have hp:=N.property; rw [peal, ZMod.val_natCast_of_lt (show N.val-1<N.val from Nat.sub_lt hp (by decide))]; exact Nat.sub_add_cancel hp
lemma meet_node (i:Site N)(h:2<N.val) : node i 0=1 ↔ i 0=0:=by rw [← (ZMod.val_injective (More N).val).eq_iff, far_one (show 1<(More N).val from by unfold More; simp; omega), ← ZMod.val_eq_zero, RP.val_node]; omega
lemma meat_node (i:Site N) : node i 0= -1 ↔ i 0= -1:=by rw [← (ZMod.val_injective (More N).val).eq_iff, ←(ZMod.val_injective N.val).eq_iff (a:=i 0), RP.val_node]; have h:=near_one (More N); have hp:=near_one N; have he : (More N).val=N.val*2:=rfl; omega -- parameter
lemma fee_zero(x:Slot):phase_b 0 x=0:=by unfold phase_b; unfold infla; split <;> simp [fortune]
lemma phase_ok (i: Fin 3) (u:ℝ): phase_b u (ply i)=u:=by unfold phase_b ply; unfold infla; simp [fortune]; ring
lemma blank (N:Side)(u v:ℝ)(p:2 < N.val): BlankN (θ_issue N u v) (Cube.links (airy N u v)):=by
  constructor
  · intro i; unfold links airy; simp
  intro i j; by_cases h:j=0
  · subst j; let x:=airy N u v; unfold links airy; simp only [Fin.succ_zero_eq_one, if_true,Pi.add_apply,step_apply,show ¬(0:Axis)=1 from by decide,ite_false,add_zero]; rw [map_mul]; change (matter (cue _)).val*(matter (cue _)).val=_; rw [clothes, diagonal_mul_diagonal]; apply congrArg; funext t; unfold θ_issue; rw [if_pos rfl]; simp_rw [←phase_ext,αZ,ages, meet_node i p,meat_node]; split_ifs <;> first | exact congrArg phase ((two_mul ..).symm) | rw [←two_mul, show 2*infla t (0/2)=(0:ℝ) from fee_zero t]
  unfold links airy; have he:j.succ ≠ 1:= fun z=> h (Fin.succ_inj.mp z)
  simp only [if_neg he,mul_one, map_one, θ_issue, if_neg h, phase,Complex.ofReal_zero,zero_mul, Complex.exp_zero]; simp -- tune

lemma chord_cost(x:ℝ) : SU.group.chord (cue x) ≤ |x|:=by
  let y:=SU.group.chord (cue x); have he:= Gauge.chord_price SU.group (cue x); have hp:Gauge.price SU.group (cue x)=1-(3+2*Real.cos x)/5:=by
    change 1-(Matrix.trace (diagonal (guide x))).re / _ = _; -- precedence
    rw [trace_diagonal,Complex.re_sum]; simp [guide,phase_eval,F,Fin.sum_univ_succ,Gauge.repDim,SU.group]; rw [← Complex.ofReal_cos]; rw [Complex.ofReal_re]; ring
  rw [hp] at he; nlinarith [Real.one_sub_sq_div_two_le_cos (x:=x),sq_abs x, abs_nonneg x]
lemma stone_air (h:|α|≤c)(t:|β|≤c): airy N α β∈Graph.stone SU.group _ (c/2):=by
  have ht:0≤c:=(abs_nonneg α).trans h; have hs(x:ℝ)(t:|x|≤c): SU.group.chord (cue (x/2))≤ c/2:= by apply (chord_cost (x/2)).trans; rw [abs_div,abs_of_pos (by norm_num:0<(2:ℝ))]; linarith only [t]
  intro i _; change SU.group.chord _ ≤ _; unfold airy; by_cases e:i.2=(1:Axis)
  · rw [if_pos e]; apply hs; unfold αZ; split_ifs; exact h; exact t; simpa using ht
  rw [if_neg e, SU.group.chord_one]; exact div_nonneg ht (by norm_num)
lemma motion_cap (h:|α|≤c)(t:|β|≤c)(P:RG.BudgetPoint)(p: 2*c ≤ P.threshold): RG.flags P.threshold (airy N α β)=∅:= Graph.rife P _ (stone_air α β h t) (by linarith)
lemma airy_p (h:2<N.val) : Fixed.reflConfig N 0 (airy N α β)= airy N β α:=by
  let i:= (0:Axis); let q:Site (More N):=0; ext1 ⟨x,a⟩; change Step.read _ (airy _ _ _) _ = _
  by_cases g:a=0; · subst a; simp [Step.read,Signed.mirror,Step.rotate,posDir,airy, Step.used]
  have hx : (Signed.mirror 0).act x 0= -(x 0):= by simp [Signed.mirror,Signed.act];
  simp only [Step.read,Step.rotate,Signed.mirror,posDir,Ne.symm g, decide_false,Bool.false_xor,Bool.false_eq_true,ite_false, Equiv.refl_apply]; unfold airy; by_cases u:a=1; swap; · simp [u,Step.used]
  have he : (1: Per (More N)) ≠ -1:= (away_W (N:=More N) (by change 2<N.val*2; omega)).2
  simp only [Step.used,Bool.false_eq_true,ite_false,affine,add_zero,u, if_true]; -- beta hx unfolded shape
  rw [show ( ({perm:=Equiv.refl Axis, flip:=fun j=> decide ((0:Axis)=j)}:Signed).act x) 0= _ from hx]; unfold αZ
  by_cases p: x 0=1; · simp [p, Ne.symm he]
  by_cases g: x 0= -1; · simp [g, Ne.symm he]
  rw [if_neg (show ¬(-(x 0))=1 from fun v=>g (by rw [←v,neg_neg])),if_neg ((not_congr neg_inj).mpr p),if_neg p,if_neg g]
lemma share_north (h:2<N.val)(p:ℝ): Agrees (RP.north N 0) (airy N α β) (airy N α p):= by
  intro i t u; have ht: (i.1 0).val ≤ N.val:= (RP.north_mem i.1 0).mp t; have hv: i.1 0≠ -1:=by intro b; rw [b] at ht; have h:=near_one (More N); change (-(1:Per (More N))).val+1=N.val*2 at h; omega
  unfold airy αZ; simp only [if_neg hv]
end YM.CF.Fixed.Rift
