import YM.SU5.May.LunarBeam
import YM.SU5.May.FloePeople
import YM.SU5.Reconstruction.Oblique.Bows
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Lunar
open Function Filter Finset Lattice Laurent Next.Free Bloch Fir Real Complex MeasureTheory WithLp
open scoped Topology BigOperators ContDiff Matrix InnerProductSpace ENNReal ComplexOrder Classical Matrix.Norms.L2Operator
open Onyx Fock Buffered.Afterglow.Tower Buffered.Afterglow.Tower.Tilted Window.ArchiveK Window.Largo
attribute [local instance] opCStarAlgebra
variable (N:Side)(P:Ramp)(p:E4)
local notation "a₀"=> P.a
local notation "b₀"=> P.b
abbrev Title (P:Ramp):= {v:Cover // v P.a=0}
variable (t:Title P)
noncomputable def planus (P:Ramp)(t:Title P)(n:ℤ):Cover:= fun i=> if i=P.a ∨ i=P.b then t.val i+n else t.val i
private def disc(v:Cover):Title P:= ⟨(fun i=> if i=P.a ∨ i=P.b then v i-v P.a else v i),by simp⟩
def tumbles : (Title P × ℤ)≃ Cover where
 toFun i:=planus P i.1 i.2
 invFun v:= (disc P v,v P.a)
 left_inv i:=by obtain ⟨v,n⟩:= i; have he:planus P v n P.a=n:= (by simp [planus,v.property]); with_reducible apply Prod.ext; apply Subtype.ext; ext1 k; change (disc P (planus P v n)).val k=v.val k; dsimp only [disc]; rw [he]; unfold planus; split_ifs <;> simp
                exact he
 right_inv x:=by ext1 k; unfold planus disc; dsimp only; split_ifs <;> simp
-- Pin unit
noncomputable def halfer :ℝ:= (Real.sqrt 2)⁻¹
lemma halfSquare : halfer^2=1/2:= by unfold halfer; rw [inv_pow, Real.sq_sqrt (by norm_num)]; ring
lemma halfLegal : 0 < halfer:=by unfold halfer; positivity
noncomputable def tilted (P:Ramp):E4:=halfer • (YM.basis P.a+YM.basis P.b)
abbrev lengthT:= inner ℝ (tilted P) p
lemma chopped : lengthT P p= halfer*(p P.a + p P.b):=by unfold lengthT tilted; rw [real_inner_smul_left,inner_add_left,YM.basis_inner,YM.basis_inner]
lemma tilted_at(i:Axis): tilted P i=if i=P.a∨i=P.b then halfer else 0:=by
 unfold tilted; simp only [PiLp.smul_apply,PiLp.add_apply, YM.basis_eq,smul_eq_mul]; have he:=P.cross; by_cases v:i=P.a; · subst i; simp [he.symm]
 by_cases p:i=P.b; · subst i; simp [he]
 simp [p,v]
lemma rulerL : ‖tilted P‖=1:=by
 have hp:= (sq_eq_sq₀ (norm_nonneg (tilted P)) zero_le_one); rw [←hp]; rw [← real_inner_self_eq_norm_sq]; rw [show inner ℝ (tilted P) (tilted P)=_ from chopped P _]; simp [tilted_at]; nlinarith only [halfSquare]
def canon (P:Ramp)(t:Title P): E4:= toLp 2 fun i=> if i=P.a then -(t.val P.b:ℝ)/2 else if i=P.b then (t.val P.b:ℝ)/2 else (t.val i:ℝ)+1/2
noncomputable def chord (N:Side)(P:Ramp)(t:Title P): E4:=tune N • canon P t
local notation "qₜ"=> chord N P t
@[simp] lemma a_loc : canon P t a₀= -(t.val P.b:ℝ)/2:= by simp [canon]
@[simp] lemma b_loc : canon P t b₀=(t.val P.b:ℝ)/2:= by simp [canon,P.cross]
@[simp] lemma z_loc (i:Axis)(x:i≠a₀)(y:i≠b₀): canon P t i=(t.val i:ℝ)+1/2:= by simp [canon,x,y]
lemma canon_orbit : inner ℝ (tilted P) (canon P t)=0:=by rw [show inner ℝ _ _= _ from chopped P (canon P t),a_loc,b_loc]; ring
lemma duet : inner ℝ (tilted P) (qₜ)=0:=by unfold chord; rw [real_inner_smul_right, canon_orbit]; ring
private lemma outside (P:Ramp):∃ i:Axis,i≠P.a ∧ i≠P.b:=by
  have hp(i j:Axis):∃ k:Axis,k≠i∧k≠j:=by revert i j; decide
  exact hp ..
lemma salaried : 1/2 ≤ ‖canon P t‖:=by
 obtain ⟨i,x,y⟩:=outside P; apply le_trans _ (arm_abs _ i); rw [z_loc P _ i x y]; rcases le_or_gt (0:ℤ) (t.val i) with h|h
 · have h':(0:ℝ)≤t.val i:= (by exact_mod_cast h); linarith [le_abs_self ((↑(t.val i):ℝ)+1/2)]
 have hl:t.val i≤ -1:= (by omega); have ht: (↑(t.val i):ℝ) ≤ -1:= (by exact_mod_cast hl); linarith [neg_le_abs ((↑(t.val i):ℝ)+1/2)]
lemma hired : (qₜ)≠0:=by apply smul_ne_zero (tune_p N).ne'; exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (salaried P t))
noncomputable def rimB(N:Side):ℝ:= N.val* halfer
def powert (P:Ramp)(t:Title P):ℝ:= (1+(t.val P.b:ℝ))/2
noncomputable def tagE(P:Ramp)(t:Title P):ℝ:= if Even (t.val P.b+1) then 1 else -1
lemma tagguard : tagE P t*tagE P t=1 ∧ tagE P t ≤ 1 ∧ -(1:ℝ)≤tagE P t :=by unfold tagE; split <;> norm_num
local notation "𝕀"=>Complex.I
lemma tagcoast: coastE (powert P t*(2*Real.pi))=(tagE P t:ℂ):=by
 unfold tagE; split
 next h=> obtain ⟨k,H⟩:= h; have hv: powert P t=k:= by have he: (t.val P.b:ℝ)+1=(k:ℝ)+k:= (by exact_mod_cast H); unfold powert; linarith
          rw [hv]; unfold coastE; push_cast; rw [show 𝕀 * _ = ↑k*(2*π*𝕀) from (by ring), Complex.exp_int_mul_two_pi_mul_I]; -- notation remove
 next h=> obtain ⟨k,H⟩:= (Int.not_even_iff_odd).mp h; have hv: powert P t=(k:ℝ)+1/2:= by have he: (t.val P.b:ℝ)+1=2*(k:ℝ)+1:= (by exact_mod_cast H); unfold powert; linarith
          rw [hv]; unfold coastE; push_cast; rw [show 𝕀 * _ = ↑k*(2*π*𝕀)+π*𝕀 from (by ring),Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]
lemma rimH:0<rimB N:=by unfold rimB; have h:= halfLegal; positivity
private lemma node_fee(n:ℤ): nodeR (rimB N) (powert P t) n * halfer=tune N*(n+powert P t):= by unfold nodeR rimB tune; have h:=halfLegal; field_simp
lemma duty (n:ℤ) : apAt N (tumbles P (t,n))=(qₜ)+nodeR (rimB N) (powert P t) n • tilted P:=by
 apply PiLp.ext; intro i; rw [ap_fee,chord]; simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,tilted_at]; by_cases b:i=P.a; · subst i; simp only [a_loc, true_or,if_true,node_fee]; rw [show tumbles P (t,n) P.a=n from (by change planus P t n P.a = _; simp [planus,t.property])]; unfold powert; ring
 by_cases c:i=P.b; · subst i; simp only [b_loc,or_true,if_true,node_fee]; rw [show tumbles P (t,n) P.b = t.val P.b+n from (by change planus P t n P.b = _; simp [planus])]; unfold powert; push_cast; ring
 rw [z_loc _ _ _ b c]; simp only [b,c, false_or, ite_false,mul_zero,add_zero]; rw [show tumbles P (t,n) i= t.val i from (by change planus P t n i= _; simp [planus,b,c])]
local notation "U"=> rimB N
local notation "X" n:max=> nodeR (rimB N) (powert P t) n
noncomputable def campaign (P:Ramp)(t:Title P)(v:E4)(N:Side):Momentum := rays (rimB N) (tagE P t) (chord N P t) (tilted P) v
lemma interrupt (r:Cover)(x:-rimB N+20 < lengthT P (emitX r))(y:lengthT P (emitX r)< -20): HasSum (fun t:Title P=>campaign P t (emitX r) N) (poll N r):=by
 let f(i:Title P × ℤ):= spectral (apAt N (tumbles P i)) (emitX r); let he:= (tumbles P).hasSum_iff.mpr (voter_sum N r).hasSum; apply HasSum.prod_fiberwise (f:=f) he; intro i; unfold f; simp_rw [duty]; let M:= tagE P i; let X':= powert P i; let u:=tagguard P i; exact opportunity (rimH N) X' u.2.1 u.1 (tagcoast P i) (chord N P i) (tilted P) (rulerL P) (duet ..) (hired N P i) _ x y
#print axioms interrupt
end YM.CF.May.Lunar
