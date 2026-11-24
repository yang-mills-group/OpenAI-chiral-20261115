import YM.CF.Scroll.Bene
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scroll
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker
attribute [local instance] opCStarAlgebra
variable {b r:Bool}{N P:Side}(a:Shape)(U:UNI SpinIdx)(t:ColorT b)(H: JetS a.s b r U)
variable (x:Bkg (More N)) (f g:Cover→Op SpinIdx)(o:Lattice.Order)
private lemma slider_app (i j z v w k l i' v'):
 slider N z o i j (f z i j) (profile x) ((v,k),i') ((w,l),v')=if k=i ∧ w=v+wrap N z∧ l=j then wind v z*f z i j*(matter (travel x (node v) (leap z o))).val i' v' else 0:=by
 simp only [slider, Matrix.sum_apply]; rw [Finset.sum_eq_single v]; swap; intro h _ hp; simp [panel,Ne.symm hp]; swap; simp
 by_cases h:k=i <;> by_cases p:w=v+wrap N z<;> simp [panel,h,p,track_pr,brand]
private def layerX(z:Cover): Op (Model N):=jump (Equiv.addRight (wrap N z)) fun i=>wind i z • ((f z) ⊗ₖ (matter (travel x (node i) (leap z o))).val)
private lemma layer_p(z): love N (layerX x f o z)= ∑ i:SpinIdx,∑ j:SpinIdx,slider N z o i j (f z i j) (profile x):=by
 ext ⟨⟨x,i⟩,p⟩ ⟨⟨y,j⟩,q⟩; simp only [loveAt,unityP, Matrix.submatrix_apply,layerX,jump_apply, Matrix.sum_apply,slider_app]; rw [sum_eq_single i]; swap; intro b _ h; simp [Ne.symm h]; swap; simp
 rw [sum_eq_single j]; swap; intro b _ h; simp [Ne.symm h]; swap; simp
 simp [helix, ← eq_comm (a:=y),mul_assoc] -- tune
variable (E:∀ i j,Summable fun x=> ‖f x i j‖)
include E
lemma summ_l(i j):Summable fun z:Cover=> slider N z o i j (f z i j) (profile x):=by
 apply u_all; intro ⟨⟨v,k⟩,a⟩ ⟨⟨y,l⟩,b⟩; apply Summable.of_norm; refine (E i j).of_nonneg_of_le (fun _=>norm_nonneg _) ?_; intro z; rw [slider_app]; split; swap; simp
 simp only [norm_mul,wind,fee_norm,one_mul]; apply mul_le_of_le_one_right (norm_nonneg _); apply (norm_entry ..).trans; exact (CStarRing.norm_of_mem_unitary (matter _).property).le
lemma report : Summable (fun z=>love N (layerX x f o z)) ∧ tourP N f o (profile x)=∑' z,love N (layerX x f o z):=by
 have he(i j:SpinIdx):= summ_l x f o E i j; simp_rw [layer_p]; refine ⟨summable_sum fun i _=>summable_sum fun j _=> he i j,?_⟩
 rw [Summable.tsum_finsetSum]; swap; intro i _; exact summable_sum fun j _=> he i j
 unfold tourP; apply sum_congr rfl; intro i _; rw [Summable.tsum_finsetSum]; swap; intro j _; exact he i j
 exact sum_congr rfl fun j _=> names.tsum_eq (fun z:Cover=>slider N z o i j (f z i j) (profile x))
omit E
def rollX (s: Signed): Equiv.Perm Lattice.Order:= orderEquiv s
lemma ortX (s:Signed)(i:Cover): List.map (·.rotate s) (leap i o)=leap (s.act i) (rollX s o):=by rw [leap, leap,send_route _ _ _ s 0]; simp only [affine,add_zero,Signed.act_zero]; rw [two_smul, two_smul, Signed.act_add]; rfl
variable (k:∀ x,sings b U (f (a.s.act x))=g x)
include k
private lemma layer_s(z:Cover): sings b (prepU a U t N) (love N (layerX x f (rollX a.s o) (a.s.act z)))=love N (layerX (stir t a x) g o z):=by
 set s':=a.s; rw [wingX]; congr 1
 let W:= layerX x f (rollX a.s o) (a.s.act z); let P:=layerX (stir t a x) g o z
 suffices u:∀ i j:Site N,tap (sings b (mealU a U t N) W) i j=tap P i j from by ext ⟨i,I⟩ ⟨j,J⟩; exact congr_fun (congr_fun (u i j) I) J
 intro i j; have ht (x:Bkg (More N))(X:Cover→Op SpinIdx) (o z u v):tap (layerX x X o z) u v= if u+wrap N z=v then wind u z • ((X z) ⊗ₖ (matter (travel x (node u) (leap z o))).val) else 0 :=by ext; by_cases h:u+wrap N z=v <;> simp [layerX,tap,jump_apply,h]
 unfold mealU W P; rw [tap_sg,ht,ht]; have hx: (Tofu a N) i+wrap N (a.s.act z) = (Tofu a N) (i+wrap N z):= Shape.tow .. |>.symm; rw [hx]
 by_cases h:i+wrap N z=j; swap; rw [if_neg h,if_neg ((Tofu a N).injective.ne h),win_z,mul_zero,zero_mul]
 rw [if_pos h,if_pos (congr_arg (Tofu a N) h),←h]; change (milU a U t i).val*windX b (wind (a.mills N i) (a.s.act z) • _)*star _=_; rw [lane_x, wingK, k]
 change wind i z • ((g z) ⊗ₖ sings b t.V (matter (travel _ (node (a.mills N i)) _)).val)=_
 rw [levity,a.nodex,ortX,t.shore]
include E
lemma dial_r (v:∀ i j,Summable fun x=> ‖g x i j‖): sings b (prepU a U t N) (dialW N f (profile x))= dialW N g (profile (stir t a x)):=by
 unfold dialW; rw [singT,win_r,win_sum,map_smul,map_sum,←Equiv.sum_comp (rollX a.s)]; congr 1; apply sum_congr rfl; intro i _
 obtain ⟨hg,he⟩:= report x f (rollX a.s i) E; rw [←singT, he,sings_sumts _ _ _ hg, (report (stir t a x) g i v).2]; rw [← a.s.actEquiv.toEquiv.tsum_eq] -- maybe wrong
 refine tsum_congr fun z=> ?_; exact layer_s a U t x f g i k z -- tune
end YM.CF.Scroll
