import YM.CF.Scroll.Pith
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scroll
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8000
variable {N P:Side}(G:Ratio N P)(ho:Odd G.count.val)(u:UNI SpinIdx)
def inert : ColorT false:=⟨MulEquiv.refl _,1,IsometryEquiv.refl _,fun _ _=>rfl,fun i=>(one_des _).symm,fun _ _=> rfl,fun i=>by unfold congrC; simp; rfl⟩ -- tune
abbrev restJ : Shape:=⟨1,0⟩

def revBolt : UNI SpinIdx:= ⟨Mir.pin 0,Mir.pin_U _⟩
def tooth: UNI (Iota G):=pflux restJ G revBolt inert
private lemma free : restJ.flee 0=0:=by
 apply nsmul_right_injective (M:=Cover) (show (2:ℕ)≠0 by decide); change 2 • _=2 • _; have h:=Shape.mote restJ (0:Cover); simp only [Shape.motion, show restJ.s=1 from rfl, show restJ.t=0 from rfl, Signed.act_one, smul_zero, zero_add, add_zero] at h; rw [smul_zero]; exact add_right_cancel ((zero_add _).trans h).symm
private lemma erf :restJ.mills N=id:=by
 funext x; unfold Shape.mills; rw [free,map_zero]; simp [restJ,affine]
private lemma free_t (x:Cover):restJ.flee x=x := by nth_rw 1 [←zero_add x]; rw [Shape.flee_p,free, show restJ.s=1 from rfl]; simp
private lemma free_e (x:Site N):restJ.rent x=0:=by have h:= Shape.vibes restJ x; rw [erf,id_eq, free_t] at h; apply nsmul_right_injective (M:=Cover) N.property.ne'; change N.val • _=N.val • _; rw [smul_zero]; linear_combination (norm := abel) h
private lemma carB(x:Nom N P): stanza G restJ inert x=x:=by
 have he {N:Side}(X:Bkg (More N)): stir inert restJ X=X:=by unfold stir inert restJ; dsimp only; change id ∘ Lattice.pull 1 _ X = X; simp
 unfold stanza; rw [he, show Shape.broad G restJ=restJ by simp [Shape.broad,restJ],he]
private lemma mat_t (k:Bool): lobe G k=readK G fun _ => angle k ⊗ₖ (1:Op Slot):=by
 unfold lobe; rw [pilesV]
 ext ⟨⟨x,r,a⟩,l⟩ ⟨⟨y,t,b⟩,m⟩
 change jump (Equiv.refl (Site N)) (fun _=>sA k _) (x,r,a) (y,t,b)*(1:Op Slot) l m=(jump (Equiv.refl (Hand G)) (fun _=>angle k ⊗ₖ (1:Op Slot))) ((x,r),a,l) ((y,t),b,m)
 by_cases hx:x=y<;>by_cases h:r=t<;>simp [jump_apply,sA,slashA,Fir.s_app,h,hx]
private lemma idle : (tooth G).val=readK G (fun _=>(spinQ revBolt inert).val):=by
 unfold tooth pflux readK fros portX; simp only [milU,Shape.payA,free_e,Rush.fee,Pi.zero_apply,zpow_zero,prod_const_one,one_smul]; rw [show paceU restJ G=Equiv.refl _ from ?_]
 ext1 x; change (restJ.mills N x.1,restJ.s.act x.2)=x; rw [erf,show restJ.s=1 from rfl, Signed.act_one]; rfl
lemma bolt_one (k:Bool) : twist (tooth G) (lobe G k)=lobe G (!k):=by
 rw [twist_formula,idle,mat_t,mat_t, readK_star,readK_mul,readK_mul]
 congr 1; funext i
 let W:= (spinQ revBolt inert).val; change W*((angle k) ⊗ₖ 1)*star W= _
 have hS:sings false (spinQ revBolt inert) ((angle k) ⊗ₖ 1)= _ := wingK revBolt inert _ (1:Op Slot)
 rw [singT,windX,if_neg Bool.false_ne_true, twist_formula] at hS; rw [hS] -- tune
 have hv:=angleX (mirrorX 0) k; change sings false revBolt _=_ at hv; rw [hv]; cases k <;>simp [inert,singT,win_i]
lemma bolt_spin (x:Sew N P)(k:Bool) : congrC (tooth G) (squareD G k (post x))=squareD G k (post x):=by
 let V:=tooth G
 rw [congr_form]; change (tooth G).val*squareD G _ _*star (cc (tooth G).val)=_; rw [idle,squareD,readK_cc,readK_star,readK_mul,readK_mul]; congr 1; funext i
 have he(Y:Vect): congrC (spinQ revBolt inert) (localPair Y)=localPair Y:=by
    have hg:=spinJ_grading
    unfold congrC spinQ; change (revBolt.val ⊗ₖ (1:Op Slot))*(spinJ⊗ₖ Pair.fullM Y)*_ᵀ=_
    simp only [op_kron_mul,←Matrix.kroneckerMap_transpose, show inert.V.val=(1:Op Slot) from rfl,Matrix.transpose_one,one_mul,mul_one]; unfold localPair
    congr 1; rw [show revBolt.val*spinJ=spinJ*cc revBolt.val from (mirrorX 0).justice,mul_assoc,show cc revBolt.val* revBolt.valᵀ=1 by rw [show revBolt.valᵀ=star (ccU revBolt).val by ext; simp [ccU]]; exact (ccU revBolt).property.2,mul_one]
 cases k
 · have h:=he (hook x.2.2 (node i.1)); rw [congr_form] at h; exact h
 have h:=he (hook x.2.1 (node (isle G i))); rw [congr_form] at h; exact h
include ho in
lemma bolt_else (j:ℕ)(M:Male)(x: Nom N P): twist (tooth G) (Peaks.cloth j M G (unionP x)) = Peaks.cloth j M G (unionP x):=by
 let F:= tub (brix j G.count); have hp:= mosaicS G ho restJ inert revBolt true false F x (BV restJ.s G.count ho j false revBolt) (cBrix j G.count ho).sumK
 rw [carB] at hp; let A:=mosaic G true false F (unionP x);
 unfold Peaks.cloth; dsimp only; change twist _ (lobe G true*A*lobe G true+lobe G false*A*lobe G false) = _
 simp only [map_mul,map_add,bolt_one, show twist (tooth G) A=A from hp]; exact add_comm ..
end YM.CF.Scroll
