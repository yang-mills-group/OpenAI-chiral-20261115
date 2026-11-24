import YM.CF.Vault.Limb
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vault
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip Scroll Branch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8000
variable {N P:Side}(G:Ratio N P)
lemma debit(k j:Bool)(x:Sew N P) : (dotB k G x).val*cc (lobe G j)=lobe G j*(dotB k G x).val:=by
 have he(v:Site P→Vect) : cutM (upperP P)*Cfield v=Cfield v *cc (cutM (upperP P)):=by rw [same_s]; exact onsite_ref v |>.eq
 obtain ⟨v,h,p⟩:=square_t G k x; change squareD G k (post x)*_= _*squareD G k (post x); rw [p]; have hX : foot G (spotC v)*cc (lobe G true)= lobe G true*foot G (spotC v):=by
    rw [lobe_t,cc_foot,←foot_mul,← foot_mul]; congr 1; rw [tickA,spotC]; apply Eq.symm
    simp only [portW]; rw [show cc ((cutM (upperP P)).submatrix (helix P).symm.symm (helix P).symm.symm)=(cc (cutM (upperP P))).submatrix (helix P).symm.symm (helix P).symm.symm from rfl]; rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,he] -- tune
 cases j; rw [lobe_plus,cc_sub,cc_one,sub_mul,mul_sub,hX,one_mul,mul_one]; exact hX
lemma det_bill(x:Sew N P): (dotB true G x).val.det=(dotB false G x).val.det:=by
 change Matrix.det (squareD _ _ _)=Matrix.det (squareD _ _ _)
 obtain ⟨v,h,q⟩:=square_t G true x; obtain ⟨w,p,r⟩:= square_t G false x; rw [q,r]; unfold foot spotC portW
 have ht (x): (foot G (spotC x)).det=(Cfield x).det:=by change (Matrix.reindex (switchG G).symm (switchG G).symm (Matrix.reindex (helix P).symm (helix P).symm (Cfield x))).det=_; rw [Matrix.det_reindex_self,Matrix.det_reindex_self]
 change det (foot G (spotC v))=det (foot G (spotC w)); rw [ht,ht]
 exact Mir.field_det_match h p
variable (j:ℕ)(L:Side)(ho:Odd L.val)
abbrev Duel:=Male × TickZ
def dustX(j:ℕ) : Chop Duel := twinX (mateF (@Peaks.cloth j)) (rentD true) (rentD false)
def lendX (b:Bool){ι: Type*}: Chop ι := fun _ N P G x=> lobe G b
def wireX (A:Chop Duel)(b:Bool): Chop Duel:=fun i _ _ G x=> (A i G x)⁻¹*lobe G b+star (A i G (chargeB x))*(1-lobe G b)
def fade (j:ℕ)(b:Bool): Chop Duel:= wireX (dustX j) b
lemma dusk(M:Duel)(x:Sew N P): dustX j M G (post x)=ment M.2 (Peaks.cloth j M.1 G (post x).1) (dotB true G x) (dotB false G x):=by unfold dustX twinX; rw [charge_p]; rfl
lemma wireL(A)(x:Sew N P)(i b):wireX A b i G (post x)=fort (lobe G b) (A i G (post x)):=by unfold wireX; rw [charge_p]; rfl
lemma duskF(M:Duel)(x:Sew N P)(b:Bool):fade j b M G (post x)=fort (lobe G b) (dustX j M G (post x)):=wireL ..
variable (M:Duel)(x:Sew N P)
lemma spinning_m (ho: Odd G.count.val):Commute (lobe G true) (dustX j M G (post x)):=by
 let C:= (lobe_sq G true).2; exact dusk G j M x ▸ revSpin _ _ C _ _ (debit G true true x) (debit G false true x) ((canUse j G.count ho).orients _ _ _) _ -- tune
lemma motion_z (ho:Odd G.count.val): twist (tooth G) (dustX j M G (post x))=dustX j M G (post x):=by rw [dusk]; exact revZen (tooth G) (dotB true G x) (dotB false G x) (Peaks.cloth j M.1 G (unionP x.1)) (bolt_spin G x true) (bolt_spin G x false) (bolt_else G ho j M.1 x.1) _
lemma dusk_eq (M:Male)(x:Sew N P): dustX j (M,noneL) G (post x)=Peaks.cloth j M G (unionP x.1):=by rw [dusk, show (M,noneL).2=noneL from rfl,funds_n]; rfl
lemma fadesZero (M:Male)(x:Sew N P)(b:Bool):fade j b (M,noneL) G (post x)=ticketT (Peaks.cloth j) b M G (unionP x.1):=by rw [duskF,dusk_eq,fort,ticketT, revI]
private lemma plus_a(X:Op (Iota G))(h:Commute (lobe G true) X)(p:Bool):Commute (lobe G p) X:=by cases p; rw [lobe_plus]; exact (Commute.one_left _).sub_left h; exact h
lemma motionX (ho:Odd G.count.val)(a:Bool)(h:IsUnit (dustX j M G (post x))): Commute (lobe G a) (fade j a M G (post x)) ∧ star (fade j (!a) M G (post x))*fade j a M G (post x)=1 ∧ twist (tooth G) (fade j a M G (post x))=fade j (!a) M G (post x):=by rw [duskF, duskF]; have ht:= fort_r _ (lobe_sq ..) _ h (plus_a G _ (spinning_m G j M x ho) a); exact ⟨ht.1,(by rw [circ]; exact ht.2), Vault.steam _ _ _ _ h (bolt_one ..) (motion_z G j M x ho)⟩
lemma revertX (M:Male)(b:Bool)(h:IsUnit (dustX j (M,oneL) G (post x))): (dotB false G x).val *cc (fade j b (M,oneL) G (post x))=fade j b (M,oneL) G (post x)*(dotB true G x).val:=by rw [duskF]; exact invert_the _ _ _ _ h (by rw [dusk]; exact roofs _ _ (skew_square G true x) (skew_square G false x) _) (debit G true b x) (debit G false b x)
end YM.CF.Vault
