import YM.CF.BPress.Bias.Fence
/- Signed Fourier wagon. Preserve translation (including ones that cross the anti cuts!), don't require tangential origin to lie in the momentum period box. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Bias
open Function Finset Filter NormedSpace Metric Lattice Fock Cube Laurent Bloch Next.Free Fir Lat Spin Paint Rush Blank Nacre SU Tulip Spin.Cellar Spin.Cellar.Pass Spin.Hole Spin.Trans Spin.Pledge Spin.Stride Dial Eye Pf
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {N: Side} {j:ℕ} {M:Jill.Male} {F C:Op (Single N)} (Z:Paint (More N)) {t:Finset (Per N)} {z : ℝ}
-- mass of a diagonal fiber slice
namespace Sails
variable (f: Cover)(u:f 0=0)
variable (N)
abbrev takeX(f:Cover)(x:Site N):= x+wrap N f
def through : Equiv.Perm (Single N):= Equiv.prodCongr (Equiv.prodCongr (Equiv.addRight (wrap N f)) (Equiv.refl _)) (Equiv.refl _)
def ride : Op (Single N):= scalarP (wagon N (fun _=>1) f)
include u
lemma coastM(x:Site N): takeX N f x 0=x 0:=by simp [takeX,u,wrap]
-- Turn anti commutes Lens
omit u in
lemma ride_lens : ride N f=Blank.lens (fun p => mode p f • 1) N:=by
 let d(p:Momentum):Op SpinIdx:=mode p f • 1; let F:= wagon N (fun _=> (1: Op SpinIdx)) f; let A:=overU N SpinIdx; apply congrArg scalarP (show F=plates N d from ?_); suffices F*A.val=A.val*Rush.mark N d by rw [plates,twist_formula, ←this, mul_assoc]; change F=F*(A.val*star A.val); rw [A.property.2,mul_one]
 ext ⟨x,b⟩ ⟨k,i⟩
 change (F*A.val) _ _=(A.val*Rush.mark N d) _ _
 let P:=mel k; let F'(y:HopK N):ℂ:=mode P (natural y.1)*((1:Op SpinIdx) y.2 i/normF N)
 have he(y:HopK N): A.val y (k,i)=F' y:= four_id ..
 have ht(x y:SpinIdx): (1:Op SpinIdx) x y=if x=y then 1 else 0:= Matrix.one_apply ..
 rw [Matrix.mul_apply]; simp_rw [he]; rw [show ∑ k:HopK N,F (x,b) k*F' k= (F*ᵥ F') (x,b) from rfl, single_load (mode_fee k) b (fun y:SpinIdx=> (1:Op SpinIdx) y i/normF N) (fun _=>1) f x]; unfold A; simp only [Matrix.mul_apply,Matrix.one_mulVec,Fintype.sum_prod_type,four_id,Rush.mark,jump_apply,Equiv.refl_apply]
 simp [Matrix.one_apply,ite_div,mul_ite,ite_mul,d]; split <;> ring
omit u in
lemma commute_lens (f: Cover)(F: Momentum→Op SpinIdx): Commute (ride N f) (lens F N) := by unfold Commute SemiconjBy; rw [ride_lens,l_mul,l_mul]; simp only [Matrix.mul_smul, Matrix.smul_mul, one_mul, mul_one]
local notation "Y0"=>ride N f
omit u
lemma hop(i j: Single N): Y0 i j= if through N f i=j then wind (penX i) f else 0:=by
 rcases i with ⟨⟨i,x⟩,v⟩; rcases j with ⟨⟨j,b⟩,t⟩; by_cases h:i+wrap N f=j<;> by_cases s:x=b<;> by_cases g:v=t<;> simp [ride,scalarP, through, h,s,g,wagon_app]
lemma hop_left (A:Op (Single N))(i j : Single N) : (Y0*A) i j =wind (penX i) f*A (through N f i) j:=by rw [Matrix.mul_apply]; simp [hop,ite_mul]
lemma hop_right (A:Op (Single N))(i j : Single N) : (A*Y0) i (through N f j)= A i j*wind (penX j) f:=by rw [Matrix.mul_apply]; simp [hop,mul_ite]
lemma forth :Y0∈unitary (Op (Single N)):=by
 apply Matrix.mem_unitaryGroup_iff.mpr; ext i j; rw [hop_left, Matrix.star_apply,hop]; by_cases h:i=j; · subst j; simp [ wind, fee_real,fee_one];
 simp [Ne.symm h,h]
lemma comm_beam {E A :Op (Single N)} (r:Trans.Ready z E A)(h:Commute Y0 A)(b:Commute Y0 E): Commute Y0 (Trans.beam E A):= (twist_C ⟨_,forth N f⟩).mp (by let U:UNI (Single N):= ⟨_,forth N f⟩; change twist U _=_; rw [←r.shine U, (twist_C U).mpr h.symm,(twist_C U).mpr b.symm]) |>.symm
lemma diag (A:Op (Single N))(p:Commute (ride N f) A)(i:Single N) : A (through N f i) (through N f i)= A i i:=by
 let z:= wind (penX i) f; have he:= Matrix.ext_iff.mpr p.eq i (through N f i); rw [hop_left,hop_right,mul_comm (A i i)] at he; exact mul_left_cancel₀ (show z≠ 0 from left_ne_zero_of_mul_eq_one (fee_one _)) he
include u
lemma comm_shutter (t:Finset (Per N)):Commute (shutter t) Y0:=by
 refine neComm (shutters t) _ ?_; intro i j h; rw [hop] at h; split at h
 next s=> simp only [← s,shutters,mem_filter,mem_univ,true_and]; rw [show fog (through N f i)=fog i from coastM N f u _]
 next s=> exact False.elim (h rfl)
-- blanks
lemma market (v:ℝ)(t:Finset (Per N)) (p:Pass (pos (Lower t)) (Hole.neg (Lower t)) (loose (Lower t)) (nativeX j M N) v): Commute Y0 (screen j M t):=by
 let C:=nativeX j M N; have hx:Commute Y0 (shutter t):=(comm_shutter N f u t).symm; have ht:Commute Y0 C:=commute_lens N f _; have hp : Commute Y0 (pos (Lower t)):=by rw [← shutter_plus,t_lamp]; exact (commute_lens ..).mul_right hx
 have hg:= ht.sub_right (comm_beam N f p.gate1 (ht.mul_right hp) hp); apply comm_beam N f p.gate0 _ hg; rw [shutter_empty]; exact (comm_shutter N f u _).symm.mul_right hg
variable {N}
def Plane (Z:Paint (More N)):Prop:=∀ x y:Site N,x 0=y 0 → Z (node x)=Z (node y)
lemma swivel_ride (b:Plane Z): Commute (ride N f) (coupling Z):=by
 unfold Commute SemiconjBy; ext i k; obtain ⟨j,rfl⟩:= (through N f).surjective k; rw [hop_left,hop_right, atX,atX];
 rcases i with ⟨⟨x,i⟩,w⟩; rcases j with ⟨⟨y,j⟩,v⟩; have he(x: Site N)(i:SpinIdx)(b:Slot): through N f ((x,i),b)=((x+wrap N f,i),b):=rfl; rw [he, he]; dsimp only [home,penX]; by_cases h:x=y; swap
 · simp only [add_left_inj,h,ite_false,mul_zero,zero_mul] -- tune
 subst y; simp only [↓reduceIte]; rw [b (x+_) x (coastM N f u x)]; change _ = _*wind x f; ring
omit u in
lemma cc_zero : cc (ride N f)=ride N f:=by ext i j; rw [cc_apply,hop]; split<;>simp [wind,fee_real]
lemma ash_shift (x:Site N) (m:ℝ) (p:Pass (pos (Lower t)) (Hole.neg (Lower t)) (loose (Lower t)) (nativeX j M N) m)(b:Plane Z)(U:Bore (screen j M t) (coupling Z) z):let A:= lost (screen j M t) (coupling Z); ash (takeX N f x) A=ash x A:=by
 intro A; let C:=(screen j M t); have h:= swivel_ride Z f u b; have hx:= market N f u m t p; have hf:Commute (ride N f) A:=by
    have he:Commute (ride N f) (cc C):= by nth_rw 1 [← cc_zero (N:=N) f]; unfold Commute SemiconjBy; rw [←cc_mul,←cc_mul, hx.eq]
    have hu:Commute (ride N f) (cc (coupling Z)):= by nth_rw 1 [← cc_zero (N:=N) f]; unfold Commute SemiconjBy; rw [←cc_mul,←cc_mul,h.eq]; -- left repeated occurrences?
    rw [show A=C*coupling Z*(1-cc C)* (-cc (coupling Z))*C by unfold A lost; rw [gapStar U.sk]]; exact (((((hx.mul_right h).mul_right ((Commute.one_right _).sub_right he)).mul_right (hu.neg_right)).mul_right hx))
 unfold ash Matrix.trace; simp only [Complex.re_sum,Matrix.diag_apply, book, Matrix.of_apply]; refine sum_congr rfl (fun i _=>?_); exact congrArg Complex.re (diag N f A hf ((x,i.1),i.2)) -- x'
omit u in
lemma ash_orientation (x y:Site N)(t':x 0=y 0) (m:ℝ) (p:Pass (pos (Lower t)) (Hole.neg (Lower t)) (loose (Lower t)) (nativeX j M N) m)(b:Plane Z)(U:Bore (screen j M t) (coupling Z) z):let A:= lost (screen j M t) (coupling Z); ash y A=ash x A:=by
 let f:=natural (y-x); have he:f 0=0:=by simp [f,natural,t']
 have ht := ash_shift Z f he x m p b U; rw [show takeX N f x=y from by unfold f takeX; rw [nat_true]; abel] at ht; exact ht
end Sails
end YM.CF.BPress.Bias
