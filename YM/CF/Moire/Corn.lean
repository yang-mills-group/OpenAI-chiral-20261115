import YM.CF.Moire.Yoke
/-! Extensive *nonperturbative* analytically tilted Weyl sea. Projection complexification with gauge for sector extensions. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Moire
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire Branch Nacre
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m:ℕ}{n:Side}
variable {e b:ℝ}{S: Seal (Site (More n))}{J: Chin n→ℂ}
def armC(a:Shape)(P:Toy m n)(x y:HopK n)(j:Trip m n)(X:Chin n): Op (Single n):= Matrix.of (fun i k=> if i.1=x ∧ k.1=y then spark P a x y j X i.2 k.2 else 0)
lemma arm_g(a:Shape)(P:Toy m n)(h:handy P)(x y j)(X:Chin n)(g): armC a P x y j (relayg g X)=twist (tradew n (g ∘ a.anon n)) (armC a P x y j X):=by
 ext ⟨u,i⟩ ⟨v,k⟩; let G:=g ∘ a.anon n; change Nacre.ni u v (armC a P x y j (relayg g X)) i k=ni u v (twist (tradew n (g ∘ a.anon n)) (armC a P x y j X)) i k; rw [twistW]; let D:=armC a P x y j X; have hp(W): ni u v (armC a P x y j W)= if u=x∧ v=y then spark P a x y j W else (0:Op Slot):=by by_cases p:u=x∧ v=y<;>ext i k<;> simp [ni,armC,p]
 rw [hp,hp]; split_ifs with he; · rw [he.1,he.2,spark_g _ h]; rfl
 simp
lemma anteD (s:Signed)(u:Site (More n)): (incX s⁻¹).anon n ((incX s).anon n u)=u:=by
 rw [←nat_true u, Shape.anno,Shape.anno,← palm,wink,inv_mul_cancel,Shape.motion]; simp [incX]
lemma tofu_ax (s:Signed)(x:Site n):(Tofu (incX s⁻¹) n) (Tofu (incX s) n x)=x:=by
 change (incX s⁻¹).mills n ((incX s).mills n x)=x; rw [← yen,wink,inv_mul_cancel, show incX 1= lagX 0 from rfl,lag_i]; simp
lemma hornC(a:Signed)(x:HopK n):east (incX a⁻¹) x=node ((Tofu (incX a) n).symm x.1):=by
 rw [show (Tofu (incX a) n).symm = Tofu (incX a⁻¹) n from Equiv.ext (fun u=>by obtain ⟨v,rfl⟩:= (Tofu (incX a) n).surjective u; rw [Equiv.symm_apply_apply,tofu_ax])]; exact (Shape.nodex ..).symm

def mulC(s:Signed)(P:Toy m n)(x y:HopK n)(j:Trip m n)(X:Chin n): Op (Single n):= ape n (incX s) (armC (incX s⁻¹) P x y j X)
lemma mulCg(s:Signed)(P:Toy m n)(h:handy P)(x y j)(X: Chin n)(g): mulC s P x y j (relayg g X) = twist (tradew n g) (mulC s P x y j X):=by
 unfold mulC ape; rw [arm_g _ _ h, ← twin, envoy, show (g ∘ (incX s⁻¹).anon n) ∘ (incX s).anon n=g from funext fun v=>by unfold comp; rw [anteD], twin]

def guardK(s:Signed)(n:Side):=prepU (incX s) (spinX s) inert n
lemma fence(s:Signed)(i j:Single n)(h:(Tofu (incX s) n) i.1.1≠ j.1.1): (guardK s n).val i j=0:=by
 rcases i with ⟨⟨x,i⟩,k⟩; rcases j with ⟨⟨y,j⟩,l⟩
 change jump (Tofu (incX s) n) (fun i=> (milU (incX s) (spinX s) inert i).val) (x,(i,k)) (y,(j,l))=_; rw [jump_apply, if_neg h]
lemma rayC(s:Signed)(P:Toy m n)(x y:HopK n)(l:Trip m n)(i j:Single n)(X:Chin n): mulC s P x y l X i j=∑ b:Slot,∑ d:Slot,(guardK s n).val i (x,b)* spark P (incX s⁻¹) x y l X b d*star ((guardK s n).val j (y,d)) :=by
 unfold mulC ape; rw [twist_formula,Matrix.mul_apply]; let Q:=guardK s n; let A:=armC (incX s⁻¹) P x y l X
 change ∑ k,(Q.val*A) i k * (star Q.val) k j= _; simp_rw [Matrix.mul_apply, Finset.sum_mul] -- tune
 rw [sum_comm]; unfold Single; simp_rw [Fintype.sum_prod_type (α₁:=HopK n)]; simp only [A,armC,Matrix.of_apply,ite_and,mul_ite,ite_mul, mul_zero,zero_mul,sum_ite_irrel,sum_const_zero,sum_ite_eq',mem_univ,ite_true, Matrix.star_apply]; rfl -- tune
lemma Had.chi(c:ℂ)(h:Had b e S J): Had (‖c‖*b) e S (fun x=> c* J x):=by
 refine ⟨fun x=>by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (h.base _) (norm_nonneg _),fun x y=>?_⟩; rw [←mul_sub,norm_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left (h.high ..) (norm_nonneg _)
lemma grit(s:Signed)(P:Toy m n)(x y: HopK n)(j:Trip m n)(i k:Single n):Differentiable ℂ (fun X=> mulC s P x y j X i k) :=by
 simp_rw [rayC]
 apply Differentiable.fun_sum; intro u _; apply Differentiable.fun_sum; intro v _; refine Differentiable.mul ?_ (differentiable_const _); refine Differentiable.mul (differentiable_const _) ?_; let L:=LinearMap.toContinuousLinearMap (show Op Slot→ₗ[ℂ]ℂ from { toFun:=fun x=>x u v,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }); exact L.differentiable.comp (spark_d P _ x y j)
lemma frostC(s:Signed)(i j: Single n)(P:Toy m n)(x y:HopK n)(k:Trip m n)(X:Chin n)(h:¬((Tofu (incX s) n) i.1.1=x.1∧(Tofu (incX s) n) j.1.1=y.1)): mulC s P x y k X i j=0:=by
 rw [rayC]; apply sum_eq_zero; intro a _; apply sum_eq_zero; intro b _; by_cases f:(Tofu (incX s) n) i.1.1=x.1
 · rw [fence s j _ (fun q=> h ⟨f,q⟩),star_zero,mul_zero]
 rw [fence s i _ f,zero_mul,zero_mul]

def Owes(s:Signed)(P:Toy m n)(x y:HopK n)(k:Trip m n)(e U W:ℝ)(i j: Single n):ℝ:= if ((Tofu (incX s) n) i.1.1=x.1∧(Tofu (incX s) n) j.1.1=y.1) then (↑(Fintype.card Slot):ℝ)*ruby m U W (titanic e (pays x y k))*(∑ b:Slot,netP P x y k b) else 0
lemma grit_pay(s:Signed)(P:Toy m n)(p:handy P)(x y:HopK n)(j:Trip m n)(U W:ℝ)(l:0<e)(g:0≤U)(f:0≤W)(v:∀ t:Cin,‖spurY t‖≤U)(k:∀ t:Cin,‖sol t‖≤W): Suite (badge _) (bail n e) (bail n e) (Ferry (incX s⁻¹) x y j) (Owes s P x y j e U W) (fun X=>mulC s P x y j X.val):=by
 let S:= Ferry (incX s⁻¹) x y j
 refine ⟨⟨fun d X=> ?_,fun i z=>?_⟩,fun i z=> honors _ _ (grit s P x y j i z|>.differentiableOn)⟩ -- tune
 · change mulC s P x y j (relayg d X.val)*(tradew n d).val= _; rw [mulCg _ _ p]; exact twist_product ..
 unfold Owes; split
 · rename_i h
   let V:= guardK s n; let Z:= ruby m U W (titanic e (pays x y j)); let Y:=(↑(Fintype.card Slot):ℝ)*Z*(∑ b:Slot,netP P x y j b); have hx(q r): ‖V.val q r‖≤1:= (norm_entry ..).trans_eq (CStarRing.norm_of_mem_unitary V.property)
   have hp(b d:Slot): Had (Z * netP P x y j b) e S (fun X=> V.val i (x,b) * spark P (incX s⁻¹) x y j X b d * star (V.val z (y,d))) :=by
      let A:=V.val i (x,b); let B:=star (V.val z (y,d)); let Q(X):= spark P (incX s⁻¹) x y j X b d
      change Had _ _ _ (fun x=> A*Q x*B); simp_rw [mul_right_comm A (Q _)]; apply (Had.chi (A*B) (star_F _ l _ _ _ _ _ _ k v g f b d)).spill; refine mul_le_of_le_one_left (by unfold netP ruby titanic; positivity) ?_; rw [norm_mul,norm_star]; exact mul_le_one₀ (hx ..) (norm_nonneg _) (hx ..)
   have hv:Had Y e S (fun X=>mulC s P x y j X i z):=by simp_rw [rayC]; apply (Had.sumT _ _ _ (fun b=>Had.sumT _ _ _ (hp b))).spill; unfold Y; rw [Finset.mul_sum]; apply sum_le_sum; intro b _; simp only [sum_const,nsmul_eq_mul,card_univ]; exact le_of_eq (mul_assoc ..).symm
   refine ⟨by unfold ruby titanic netP; positivity,fun _=>⟨(bent_G ..).2.2,?_,?_⟩,hv.base,hv.high,(grit s P x y j i z).continuous.comp continuous_subtype_val⟩
   · rw [show (forum n e).home i=east (incX s⁻¹) x by rw [hornC,←h.1,Equiv.symm_apply_apply]; rfl]; exact (bent_G ..).1
   rw [show (forum n e).home z=east (incX s⁻¹) y by rw [hornC,←h.2,Equiv.symm_apply_apply]; rfl]; exact (bent_G ..).2.1
 rename_i h; simp_rw [fun X=> frostC s i z P x y j X h]; exact nothing ..
end YM.CF.Moire
