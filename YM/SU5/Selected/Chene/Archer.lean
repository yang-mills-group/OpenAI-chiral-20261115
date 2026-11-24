import YM.SU5.Selected.Chene.Quill
import YM.PREC.FrameResponse
set_option autoImplicit false
noncomputable section
namespace YM.Chene.Trunk
open Function Filter Matrix Lattice Tree SectorNext.Vacuum.FlatTree Finset Next.Rank.Axial Pad Precision Exterior RG
open scoped Topology BigOperators Matrix
variable {c f : Side} (S:StepData c f)

open YM.Precision in def camp := (probe S).submatrix (wheel c) (wheel f)
lemma pantheon(v: Reed f→ ℝ) (x:Reed c) : (camp S *ᵥ v) x= (probe S*ᵥ (v ∘ (wheel f).symm)) (wheel c x):=by rw [camp,submatrix_mulVec_equiv]; rfl

def limb (v:Site c→ℝ): form 0 c:= fun x=> -(v x.1)
lemma palm (v:Site c→ℝ)(x:Reed c): (d 0 c *ᵥ limb v) (wheel c x)= climb v x:=by rw [wheel_app,d_sites]; unfold climb limb; abel
lemma pillars(v:Site f→ℝ): camp S *ᵥ climb v= climb (v∘S.ratio.embed):=by
 have ht:climb v ∘ (wheel f).symm=d 0 f*ᵥ limb v:= by funext i; obtain ⟨p,rfl⟩:=(wheel f).surjective i; rw [palm,Function.comp_apply,Equiv.symm_apply_apply]
 funext x; rw [pantheon,ht,root_gradient]; exact palm (v∘S.ratio.embed) x
lemma heading: camp S*realM (sky f)= realM (press S.ratio.embed):=by apply Matrix.ext_iff_mulVec.mpr; intro i; rw [←mulVec_mulVec,liftPress (p:= (@id (Site f))), liftPress S.ratio.embed,speedZ,speedZ,pillars]; rfl -- first RW named parameter issue
lemma loft(X:Matrix (Body 2 f) (Body 2 f) ℝ) (p:ℝ): bolt (pasture X) (camp S) p * realM (arena S.ratio)=0:=by
 let V:= realM (sky f); let W:=realM (press S.ratio.embed); rw [show realM (arena _)=stance V W from by ext (i|i) j<;> rfl]; exact Pad.reach _ p _ _ _ (pasture_g X) (heading S)
lemma rebates : seat (pin ℝ f) (0:Matrix Axis (Reed c) ℝ)* realM (arena S.ratio)=0 ∧
    seat (0:Matrix Axis (Reed f) ℝ) (pin ℝ c)* realM (arena S.ratio)=0:=by
 let V:= realM (sky f); let W:=realM (press S.ratio.embed); rw [show realM (arena _)=stance V W from by ext (i|i) j<;> rfl]; constructor <;> rw [stake,Matrix.zero_mul,pin_angle] <;> abel
lemma footSlab (x:Reed c) : (wheel c).symm (x.1,coord x.2)=x:= (wheel c).symm_apply_apply x
private lemma arcBill {f:Side}{U:form 1 f}{i:Axis}{c:ℝ}(p:∀ x:Site f,U (x,coord i)=c)(x:Site f)(k:ℕ): integralLink x (List.replicate k (posDir i)) U=k*c:=by
 change linkSum (fun i=> U (i.1,coord i.2)) _ _= _
 induction k generalizing x with
 | zero=>simp [linkSum]
 | succ k ih=> rw [List.replicate_succ,linkSum,ih]; change U (x,coord i)+_=_; rw [p]; push_cast; ring
lemma tonal (v:Axis→ℝ)(x:Reed c) : (mean S *ᵥ ((wind f *ᵥ v) ∘ (wheel f).symm)) (wheel c x)=(wind c *ᵥ v) x:=by
 let r:= (f.val:ℝ)⁻¹*v x.2; let i:=x.2; let y:= (wind f*ᵥ v) ∘ (wheel f).symm;
 have hx(a:Site f): y (a,coord x.2)=r:=by simp_rw [y,r,Function.comp_apply,pinchK,wind_emit]
 rw [wheel_app,mean,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,wind_emit]; let P:= S.patch; have hp: axisEquiv.symm (coord x.2)=x.2:= axisEquiv.symm_apply_apply _; simp only [hp,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,StepData.repath]
 have hi(u:S.patch.Points): integralLink (atPoint S x.1 u) (List.replicate S.patch.L.val (posDir x.2)) ((wind f *ᵥ v) ∘ (wheel f).symm)=(S.patch.L.val:ℝ)*r:= arcBill hx _ _
 simp_rw [hi,←Finset.sum_mul, S.patch.weight_sum,_root_.one_mul]
 unfold r; have hf:f.val=c.val*S.patch.L.val:=S.sizes; rw [hf,Nat.cast_mul,(by ring : ↑c.val*(S.patch.L.val:ℝ)=(S.patch.L.val:ℝ)*(c.val:ℝ)), _root_.mul_inv_rev]; have hh:= hard_positive S.patch.L; have ht:=hard_positive c; field_simp -- tune order
lemma moves : pin ℝ c * (camp S * wind f) = 1:=by
 apply Matrix.ext_iff_mulVec.mpr; intro x; let v:= wind f *ᵥ x; let b:= fixRoot S *ᵥ (v ∘ (wheel f).symm)
 let w(i:Site c) := -(b (i,vac)); have h: camp S*ᵥ v= wind c*ᵥ x+climb w:=by -- type maybe incl
    funext i; rw [pantheon,probe,Matrix.add_mulVec,← Matrix.mulVec_mulVec,Pi.add_apply,Pi.add_apply,tonal S x i, wheel_app,d_sites]; unfold w climb b; exact congrArg₂ (·+·) rfl (by ring)
 rw [←mulVec_mulVec,←mulVec_mulVec]; change pin ℝ c *ᵥ (camp S*ᵥ v)=_; rw [h,Matrix.mulVec_add,rail,mulVec_mulVec,pin_wind,add_zero]
end YM.Chene.Trunk
#print axioms YM.Chene.Trunk.moves
