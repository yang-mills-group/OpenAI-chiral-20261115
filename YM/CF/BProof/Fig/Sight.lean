import YM.CF.BProof.Fig.Layout

/-! free-symbol ≥ discrete Difference†Difference on all plus/minus. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Fig
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Align Stint
open Fir Laurent Rush Bloch Next.Free BZ
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side} {t:Bool}
def paint (f: Site N→Op SpinIdx): Op (Page N):= twist (overU N SpinIdx) (jump (Equiv.refl (Site N)) f)
lemma cookHop (i:Axis) : Fig.hop N i=paint (fun z:Site N=> phase (pm z i) • 1):=by
 unfold paint; rw [twist_formula]; let F:= overU N SpinIdx; let J:=Fig.hop N i; let g(z:Site N): Op SpinIdx:=phase (pm z i) • 1
 suffices hx: J*F.val=F.val*jump (Equiv.refl _) g by change J=_; rw [←hx,mul_assoc,F.property.2,mul_one]
 ext ⟨x,a⟩ ⟨y,b⟩; simp only [Matrix.mul_apply,Fintype.sum_prod_type (α₁:=Site N), J,hop_formula]; rw [sum_eq_single (Lat.advance i x),sum_eq_single y]; swap; · intro d _ h; simp [g,jump_apply,h]
 swap; · simp; -- address differently
 simp only [F,overU,Matrix.kronecker_apply,jump_apply,g,Equiv.refl_apply,ite_true,Matrix.smul_apply]; by_cases h:a=b <;> simp [Matrix.one_apply,h, HF, mul_ite,ite_mul]
 intro w _ e; simp [Ne.symm e]
 simp
lemma paint_mul (f g: Site N→Op SpinIdx) : paint f *paint g=paint (fun x=> f x*g x):=by rw [paint,paint,← map_mul]; exact congrArg _ (jump_mul ..)
lemma paint_sub (f g: Site N→Op SpinIdx) : paint f -paint g=paint (fun x=> f x-g x):=by rw [paint,paint,← map_sub,← jump_sub ..]; rfl
lemma paint_ast (f: Site N→Op SpinIdx) : star (paint f)=paint (fun x=> star (f x)):=by rw [paint,← map_star,jump_star]; rfl
lemma paint_smr (c:ℝ)(f: Site N→Op SpinIdx): c • paint f=paint (fun z=> c • f z):=by
 unfold paint; rw [← map_smul]; apply congrArg; ext ⟨x,a⟩ ⟨y,b⟩; by_cases g:x=y<;>simp [jump_apply,g]
@[simp] lemma paint_one : paint (N:=N) (fun _=>1)=1:=by rw [paint,jump_id,map_one]
lemma paint_pill(u:Bool) : paint (N:=N) (fun _=>pill u)=cutSpin N u:=pilesV ..
lemma paint_real(j:ℕ)(h:1≤j)(M:Male): liftA (paint (fun z:Site N=> bar j M.val (mel z)))= spar j M (1:Bkg (More N)):= by rw [spar,profile_trivial,funde_flat j h M N,cart_traded (A:=bar j M.val) (f:=tub (bar j M.val)) (cBar j M.val true h M.property) N]; rfl
lemma paint_mono {f g:Site N→ Op SpinIdx}(h:∀ i,f i≤g i): paint f ≤ paint g:=by
 apply twist_mono; rw [← sub_nonneg,← jump_sub]; have he(i): ∃ A:Op SpinIdx,(g-f) i=star A*A:= CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr (h i)); choose F h using he
 let X:=jump (Equiv.refl _) F; rw [show jump (Equiv.refl _) (g-f)=star X*X from ?_]; exact star_mul_self_nonneg _; unfold X; rw [jump_star,jump_mul]; exact congrArg _ (funext h)
lemma hop_square (i:Axis): star (Fig.hop N i-1)*(Fig.hop N i-1)=paint (fun z=> (‖phase (pm z i)-1‖^2 : ℝ) • (1:Op SpinIdx)):=by
 let f(z:Site N):ℂ:=phase (pm z i)-1; rw [cookHop,←paint_one,paint_sub,paint_ast,paint_mul]; apply congrArg; funext z; rw [show phase (pm z i) • (1:Op SpinIdx)-1=f z •1 from (by simp [f, sub_smul]),star_smul,star_one,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,mul_one,←Complex.coe_smul,smul_smul]; congr 1; rw [mul_comm,Complex.ofReal_pow]; exact inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (f z)
lemma frame_low {c:ℝ}(u:Bool)(i:Axis)(j:ℕ)(M:Male)(g:∀ x:Site N,c* ‖phase (pm x i)-1‖^2≤Jill.disk j M (pm x)): let F:= fun z:Site N=> if u then bar j M.val (mel z) else 1-bar j M.val (mel z); let S:=cutSpin N u; c •(S*(star (Fig.hop N i-1)*(Fig.hop N i-1))*S) ≤ S*paint F*S:=by
 intro B S; unfold S; rw [hop_square,←paint_pill,paint_mul,paint_mul,paint_mul,paint_mul,paint_smr]; apply paint_mono; intro i'; let T:=pill u; change c •(T*_ *T)≤ _; rw [show pill u*B i'*pill u=_ from lowFull (j:=j) M (pm i') (mel_h i') u,Algebra.mul_smul_comm,T |> (fun _=> mul_one T),Algebra.smul_mul_assoc,show T*T=T from (cutM_idp _).1,smul_smul]; exact smul_le_smul_of_nonneg_right (g i') (cutM_idp _).nonneg -- tune
lemma sweep {j:ℕ}(h:1≤j): ∃ c:ℝ,0<c∧∀ (N:Side)(i:Axis)(u:Bool)(M:Male), let T:=axisShift N i-1; let H:=bandCut (univ:Support N) u; let P:=spar j M (1: Bkg (More N)); c • (H*(star T*T)*H) ≤ H*(if u then P else 1-P)*H:=by
 obtain ⟨c,C,hp,-,Q⟩:= feed h; refine ⟨c,hp,?_⟩; intro N i u M T H P; let S:= Fig.hop N i -1; have hf:T=liftA S:=by unfold S T axisShift; rw [liftA.sub,liftA.one]
 have hl:=liftA.mono (frame_low (N:=N) u i j M (fun i'=> (Q i' M).1 i)); let Z:= paint (fun z:Site N=>bar j M.val (mel z)); let W:=paint (fun z:Site N=> if u then bar j M.val (mel z) else 1-bar j M.val (mel z)); have hg:liftA Z=P:= paint_real j h M; have he:liftA W=(if u then P else 1-P):=by
   cases u
   · change liftA (paint (fun z=>1-_))= _; rw [←paint_sub (fun _=>1),paint_one,liftA.sub,liftA.one]; exact congrArg _ hg
   exact hg
 change liftA (c • (cutSpin N u*(star S*S)*cutSpin N u)) ≤ liftA (cutSpin N u* W*cutSpin N u) at hl; simp only [liftA.prod,liftA.smr,he,lift_spin,liftA.ast,←hf] at hl; exact hl
end YM.CF.BProof.Fig
