import YM.CF.BPress.Lute.Station
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Lute.Kite
open Function Finset Filter NormedSpace Metric SU SU.Pair Mesa Fort Spin Spin.Paint Music Lattice Fock
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
section paths
variable {I:Type}[DecidableEq I][Fintype I][Nonempty I]
structure CurveX (A:Type)(P:A→Prop)(u v:A)[NormedAddCommGroup A][NormedSpace ℝ A](f:ℝ→A):Prop where
 head:f 0=u
 tail:f 1=v
 special(x:ℝ):P (f x)
 south(x:ℝ)(p:x≤1/8): f x=u
 north(x:ℝ)(p:1-1/8≤x):f x=v
 smooth: ContDiff ℝ ∞ f
lemma poses (U V:Op I)(p:trueS U)(q:trueS V):∃ f:ℝ→Op I,CurveX _ trueS U V f:=by
 obtain ⟨f,T,r,s,e⟩:=Lodge.key_path U V p q; refine ⟨f∘bound,⟨?_,?_ ,fun x=> e _ (mid_bound _),?_,?_,?_⟩⟩; simp [r,bounds01.1]; simp [s,bounds01.2]; intro x u; rw [comp_apply,bound_lo u,r]; intro x u; rw [comp_apply,bound_hi u,s]; exact contDiff_iff_contDiffAt.mpr (fun x=> (T _ (mid_bound x)).comp x bound_smooth.contDiffAt)
lemma Sym.plan {U: Op Slot}(p:Spin.Sym U): trueS U:= ⟨p.gate,p.traceX⟩
lemma center_lift : ∃ B:Op Slot,trueS B∧ cap B= Music.basis:= lift_sym _ (Sym.plan basis_acts) basis_acts.triangle basis_flip
abbrev embed : Ket SU.F:= basisKet 0
lemma embed_norm: ‖embed‖=1:=by simp [embed]
lemma embed_star : IsSelfAdjoint (fullM embed):= by rw [fullM,isSelfAdjoint_iff,op_star_kron,star_one,show embed.ofLp=e0 from rfl, northStar]
lemma root_lift : ∃ B:Op Slot,trueS B∧ cap B= fullM embed:=by have he:= Spin.Sym.full _ embed_norm; exact lift_sym _ (Sym.plan he) he.triangle embed_star
abbrev S := center_lift.choose
abbrev St: trueS S∧cap S= Music.basis:=center_lift.choose_spec
abbrev Y := root_lift.choose
abbrev Yt:trueS Y∧cap Y=fullM embed:= root_lift.choose_spec
def shapeL := (poses Y S Yt.1 St.1).choose
lemma sheetL : CurveX _ trueS Y S shapeL := (poses _ _ Yt.1 St.1).choose_spec
lemma cap_s : ContDiff ℝ ∞ (cap (J:=I)):=by
 unfold cap; exact ContDiff.mul contDiff_id (contDiff_iff_contDiffAt.mpr (fun x=>Lute.mat_smooth _ _ fun i j=>(key_entry j i).contDiffAt))
-- B(u) in text
abbrev B_theme(x:ℝ):Op Slot:=cap (shapeL x)
lemma shape_cost: CurveX _ Spin.Sym (fullM embed) Music.basis B_theme:= {
 head:= by rw [B_theme,sheetL.head,Yt.2]
 tail:= by rw [B_theme,sheetL.tail,St.2]
 north x p:= by rw [B_theme,sheetL.north x p,St.2]
 south x p:= by rw [B_theme,sheetL.south x p,Yt.2]
 special x:=capgate _ (sheetL.special _)
 smooth:=cap_s.comp sheetL.smooth
}

-- SU route g inverse chosen constant for zero
variable (k:Fin 5)
abbrev orb(k:Fin 5):= (Mag.center k)⁻¹
lemma twined : trueS (fund (orb k)):=⟨fund_U _,fund_det _⟩
def anchor:ℝ→Op SU.F:= if k=0 then fun _=>1 else (poses _ _ suit_one (twined k)).choose
lemma anchor_s: CurveX _ trueS 1 (fund (orb k)) (anchor k):=by
 unfold anchor; split; next h=> subst k; rw [orb,Mag.center_zero, inv_one,fund_one]; exact ⟨rfl,rfl,fun _=>suit_one,fun _ _=>rfl,fun _ _=>rfl,contDiff_const⟩
 next h=> exact (poses _ _ suit_one (twined k)).choose_spec
abbrev μ (A:Op SU.F)(h:trueS A):SU.E:=⟨⟨A,h.1⟩,h.2⟩
def walking(x:ℝ): E:=μ (anchor k x) ((anchor_s k).special x)
def starPath(x:ℝ) := triple (anchor k x)
lemma walking_occ(x:ℝ): starPath k x=(matter (walking k x)).val:= by simp only [matter_matrix]; rfl
lemma star_gate(x:ℝ): trueS (starPath k x):=⟨triple_mem (walking k x),triple_det (walking k x)⟩ -- tune
lemma t_smooth : ContDiff ℝ ∞ triple:= contDiff_iff_contDiffAt.mpr (fun x=> Lute.mat_smooth _ _ (fun i j=>by
 rcases i with ⟨x,a|a⟩; all_goals rcases j with ⟨y,b|b⟩; all_goals simp only [triple, each,Join.both,Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂, Matrix.kroneckerMap_apply, cc_apply,ExTwo.wedge_entry]; all_goals refine ContDiffAt.mul contDiffAt_const ?_; all_goals first| exact ContDiffAt.sub ((key_entry _ _).contDiffAt.mul (key_entry _ _).contDiffAt) ((key_entry _ _).contDiffAt.mul (key_entry _ _).contDiffAt)| exact Complex.conjCLE.toContinuousLinearMap.contDiff.contDiffAt.comp _ (key_entry _ _).contDiffAt| exact contDiffAt_const))
lemma smooth_p : ContDiff ℝ ∞ (starPath k):= t_smooth.comp (anchor_s k).smooth

-- X_z actual
abbrev light(x:ℝ):= acts (anchor k x) embed
lemma light_cost : CurveX _ (fun a=>‖a‖=1) embed (acts (fund (orb k)) embed) (light k):=by
 have he(A:Op SU.F)(p:trueS A):‖acts A embed‖=1:=(act_unit_norm ⟨A,p.1⟩ _).trans embed_norm
 refine ⟨?_,?_,fun x=> he _ ((anchor_s k).special _),?_,?_,?_⟩; · rw [light,(anchor_s k).head,act_one]
 · rw [light,(anchor_s k).tail]; -- indent
 · intro x p; rw [light,(anchor_s k).south x p,act_one]
 · intro x p; rw [light,(anchor_s k).north x p]
 exact contDiff_iff_contDiffAt.mpr (fun x=> by
    have ht(A:Op SU.F): acts A embed=shaft 0 A:=rfl
    unfold light; simp_rw [ht]; exact (s_smooth _ _).comp x (anchor_s k).smooth.contDiffAt)
lemma shape_light (t:ℝ):cap (starPath k t*Y)=fullM (light k t):=by rw [cap_side,Yt.2, walking_occ]; exact (full_cong (walking k t) embed).symm
lemma mix_shift (k:Fin 5)(t u:ℝ): hopper k (t/2)*tap k u*(hopper k (t/2))ᵀ=tap k (t+u):=by rw [tap,tap, mul_assoc,mul_assoc (hopper k u),← cong_basis,←mul_assoc (hopper k u),←mul_assoc]; unfold hopper; rw [←rot_add,←rot_add, show t/2+(u+t/2)=t+u from by ring]; -- tune assoc
end paths
end YM.CF.BPress.Lute.Kite
