import YM.CF.BProof.Bias.Rice
import YM.CF.BProof.Fig.Mire
/-! Using antiperiodic basis parity at translated boxes. Do not assume cancellation
point estimate over the support terms of a particular translation-covariant choice
of seat prices; Tape.levy bounds real-part trace without this. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint Wick Hearth
open Fir Laurent Rush Bloch Next.Free BZ Real
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}(i:Axis)
lemma drum_tr (A: Stamp): Commute (axisShift N i) (drum N A):= by
 let V:=axisShift N i; have ht: Spin.tile N =relic (fun _=>spinJ):=congrArg liftA (pilesV (N:=N) spinJ).symm; apply Commute.mul_right (b:=Spin.tile N) (c:=curtain N A); rw [ht]; exact relic_comm ..; rw [relic_shift i]; exact (curtain_relic ..).symm
lemma hop_cre : cc (axisShift N i)=axisShift N i:=by
 ext x y; change star (axisShift N i x y)=_; rw [axis_shift]; dsimp only; split; next t=> simp [seam,Matrix.one_apply,apply_ite (fun z:ℂ=>star z)] -- tune
 simp
lemma hop_basis (x: Single N): acts (axisShift N i) (basisKet (addK (step i) x))= (seam (anticut N) (fsite x) i) • basisKet x:=by
 apply PiLp.ext; intro j; rw [actAxis]; simp only [basis_apply,Equiv.apply_eq_iff_eq, WithLp.ofLp_smul,Pi.smul_apply]; by_cases h:j=x<;> simp [h,fsite] -- tune
lemma hop_comm_star (Z:Op (Single N))(h: Commute (axisShift N i) Z) : Commute (axisShift N i) (star Z):=by
 let U:=hopV N i; have hp:=U.property; have he: star U.val*Z=Z*star U.val:=by
    rw [← mul_one (star U.val*Z),←hp.2,← mul_assoc, mul_assoc (star U.val) Z U.val,show Z*U.val=U.val*Z from h.symm,← mul_assoc (star U.val) U.val, hp.1,one_mul]
 have ht:=congrArg star he; rw [star_mul,star_mul,star_star] at ht; exact ht.symm
lemma norm_sail {Z:Op (Single N)}(h: Commute (axisShift N i) Z)(x:Single N): ‖acts Z (basisKet x)‖ = ‖acts Z (basisKet (addK (step i) x))‖:=by
 rw [← act_unit_norm (hopV N i) (acts Z (basisKet (addK (step i) x))),← act_mul]; unfold hopV; dsimp only; rw [h.eq, act_mul,hop_basis,map_smul,norm_smul]; simp
variable {A B:Stamp}{R J X:Finset (Per N)}{j:ℕ}{d:ℝ}{C:Quilt N}
lemma shore {i:Axis}(M:Male)(p:i≠0)(h:1 ≤ j)(b:Free d j M R)(c:Call R J A B C) : Commute (axisShift N i) (Plus j M R C):=by
 let S:=axisShift N i; let T:=Seat R; let D:=pair C; let L:=Polar j M R; have he : Commute S (tickA N):=by rw [sky_t]; exact relic_comm ..
 have hg(V:Finset (Per N)): Commute S (Seat V):=((axis_t i p).comm _).symm; have hT:Commute S (1-T):=(Commute.one_right _).sub_right (hg R)
 have hf:Commute S L:=by apply commEntry b; rw [redP_eq M h]; exact relic_comm ..; rw [PP_eq]; exact hT.mul_right he; rw [QQ_eq]; exact hT.mul_right ((Commute.one_right _).sub_right he)
 have hv: T*D= T*(Seat J * drum N (A-B)) + T*drum N B:=eq_add_of_sub_eq ((mul_sub ..).symm.trans (styleL c)) -- tune
 apply Commute.mul_right (c:=1-cc L); rw [show Polar j M R * pair C=L*(T*D) from (by rw [←mul_assoc,(entryBoth M b).2]),hv]; apply hf.mul_right; exact ((hg R).mul_right ((hg J).mul_right (drum_tr ..))).add_right ((hg R).mul_right (drum_tr ..))
 apply (Commute.one_right _).sub_right; have hp : cc S= S:=hop_cre i; unfold Commute SemiconjBy; change S*_= _*S; nth_rw 1 2 [← hp]; rw [←cc_mul,←cc_mul,hf.eq]
abbrev guy(x : Site N)(m:SpinIdx)(g:Slot):Single N:=((x,m),g)
def swing (Z: Op (Single N))(p:Site N)(m:SpinIdx)(g:Slot):= ‖acts Z (basisKet (guy p m g))‖
variable {Z:Op (Single N)}
lemma swing_inc (v:Site N)(m u)(k:Commute (axisShift N i) Z)(j:ℕ): swing Z (v+j • step i) m u=swing Z v m u:=by
 induction j with
 | zero=> simp -- tune
 | succ j ih=> rw [add_smul,one_smul,←add_assoc]; exact (norm_sail i k (guy (v + j • step i) m u)).symm.trans ih
lemma bump (v:Site N)(m u)(k:Commute (axisShift N i) Z)(x:Per N) : swing Z (update v i x) m u=swing Z v m u:=by
 rw [show update v i x=v+along (v i) x • step i from ?_]; exact swing_inc i v m u k _; funext j; by_cases p:j=i<;> simp [p,nsmul_eq_mul]
lemma stepShow {A:Op (Single N)}(h:∀ i:Axis,i≠0→ Commute (axisShift N i) A) (x y:Site N)(p:x 0=y 0)(m:SpinIdx)(w:Slot): swing A x m w=swing A y m w:=by
 let F:=update (update (update x 1 (y 1)) 2 (y 2)) 3 (y 3)
 have hf(t:Axis)(q:t≠0): ∀ v, swing A (update v t (y t)) m w=swing A v m w:=fun v=>bump t v _ _ (h t q) _
 suffices F=y by
   calc
     _ = swing A F m w := by unfold F; rw [hf 3 (by decide),hf 2 (by decide),hf 1 (by decide)]
     _ = _:=congrArg (fun p=>swing A p m w) this
 funext i; fin_cases i <;> simp [F,update_apply,p]
end YM.CF.BProof.Bias
