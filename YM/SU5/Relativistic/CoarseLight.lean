import YM.SU5.Relativistic.TriFlux
import YM.PREC.Derivative
/-! # predictor root gauge derivative on integer and real flats. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.GaugeFlux
open Function Finset Filter MeasureTheory Lattice Wilson
open RG Precision Exterior
open scoped Matrix BigOperators
variable {N: Side} {C:Side}(S:StepData C N)
def coding (N:Side) := Equiv.prodCongr (Equiv.refl (Site N)) axisEquiv -- order dims
lemma coded (e:Bond N): coding N e=(e.1,coord e.2):=rfl
def contour (f:Bond N→ℝ) : form 1 N := f ∘ (coding N).symm
lemma contours (f: Bond N→ℝ)(e:Bond N): contour f (e.1,coord e.2)=f e:=congrArg f ((coding N).symm_apply_apply _)
-- scalar cochain P

def pressB: (Bond N→ℝ)→ₗ[ℝ] (Bond C→ℝ):= (LinearMap.pi (fun i:Bond C=> LinearMap.proj (coding C i))).comp ((probe S).mulVecLin.comp (LinearMap.pi fun i:Body 1 N=>LinearMap.proj ( (coding N).symm i)))
lemma press_r (f:Bond N→ℝ) (x:Bond C): pressB S f x=((probe S)*ᵥ contour f) (x.1,coord x.2):=rfl
lemma exact_block (v:Site N→ℝ) : pressB S (differ v)=differ (v∘ S.ratio.embed):=by
 let V:form 0 N:= fun i=> v i.1
 have he: contour (differ v)=d 0 N *ᵥ V := by
    funext i; obtain ⟨e,rfl⟩:= (coding N).surjective i; rw [coded e -- argimplicit
      , contours, d_sites]; rfl
 funext i; rw [press_r,he,root_gradient,d_sites]; rfl

-- constants and winding
private def conF (N:Side)(v:Axis→ℝ)(x:Bond N):ℝ:= v x.2
private lemma con_path (v:Axis→ℝ)(x y:Site N)(p:Walk): integralLink x p (contour (conF N v))= integralLink y p (contour (conF N v)):=by
 induction p generalizing x y with
 | nil=>rfl
 | cons a p ih=>
    let H:= fun e:Edge (Site N)=> contour (conF N v) (e.1,coord e.2);
    change linkSum H _ (a::p)=linkSum H _ (a::p)
    have he : linkSum H (x+a.vec) p=linkSum H (y+a.vec) p:= ih _ _
    rw [linkSum,linkSum,he]
    cases a with| mk i b=>cases b <;> simp [H,contour,conF,coding,Step.used] -- dependent issues
private lemma site_dc (v:Axis→ℝ)(a b:Body 0 C): (fixRoot S *ᵥ contour (conF N v)) a=(fixRoot S *ᵥ contour (conF N v)) b:=by
 have he(i:S.patch.Points):tau S a.1 i (contour (conF N v))=tau S b.1 i (contour (conF N v)):=by
    simp only [tau,LinearMap.neg_apply,LinearMap.sum_apply,LinearMap.smul_apply,con_path v (atPoint S a.1 i) (atPoint S b.1 i)]
 simp only [fixRoot,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,adjusted,LinearMap.sub_apply,LinearMap.sum_apply,LinearMap.smul_apply,he]
lemma con_block (v:Axis→ℝ) : pressB S (conF N v)=conF C (S.patch.L.val • v):=by
 funext i; have he(k : S.patch.Points): integralLink (atPoint S i.1 k) (S.repath i.2) (contour (conF N v))=(S.patch.L.val:ℝ)*v i.2:= by
   suffices H:∀ n (x:Site N), integralLink x (List.replicate n (posDir i.2)) (contour (conF N v))= (n:ℝ)*v i.2 by exact H S.patch.L.val _
   intro n; induction n with
   | zero=> intro x; simp [integralLink,linkSum]
   | succ n ih=> intro x; let a:= (List.replicate n (posDir i.2)); let Q:= fun e:Edge (Site N)=> contour (conF N v) (e.1,coord e.2); rw [List.replicate_succ]; change linkSum Q x (_::a)=_; rw [linkSum,show linkSum Q (x+_) a= (n:ℝ)*v i.2 from (show linkSum Q (x+(posDir i.2).vec) a=_ from ih (x+step i.2))]; simp only [posDir,Step.used,Bool.false_eq_true,↓reduceIte]; rw [show Q (x,i.2)=v i.2 from contours _ (x,i.2)]; push_cast; ring
 rw [press_r,probe,Matrix.add_mulVec,Pi.add_apply,←Matrix.mulVec_mulVec,d_sites]; rw [site_dc S v ((i.1+step i.2),vac) (i.1,vac),sub_self,add_zero]; unfold Precision.mean; rw [LinearMap.toMatrix'_mulVec,LinearMap.pi_apply]; simp only [LinearMap.sum_apply,LinearMap.smul_apply,show axisEquiv.symm (coord i.2)=i.2 from axisEquiv.symm_apply_apply _,he, ← Finset.sum_smul,S.patch.weight_sum,one_smul,conF,Pi.smul_apply,nsmul_eq_mul]

def positionB (t:Axis→ℝ)(x:Site N):ℝ:= (∑ i:Axis,(x i).val*t i)/N.val
lemma val_embed(g: Ratio C N)(v:Site C)(i:Axis): (g.embed v i).val=g.count.val * (v i).val :=by
 let F:Cover:= fun i=> (v i).val
 have he:wrap C F=v:= funext fun i=> by change ((↑((v i).val:ℤ)):Per C)=_; simp
 nth_rw 1 [←he]; rw [g.embed_wrap]
 have hp: g.count.val*(v i).val<N.val:=by rw [g.exact_size,Nat.mul_comm C.val]; exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) (g.count.property)
 have hu: ((g.count.val • F:Cover) i)= (g.count.val*(v i).val : ℕ):=by simp [F]
 change ZMod.val ((↑((g.count.val • F:Cover) i)):Per N)=_
 rw [hu,Int.cast_natCast, ZMod.val_natCast_of_lt hp]
lemma real_coarse (t:Axis→ℝ): positionB (N:=N) t ∘ S.ratio.embed=positionB (N:=C) t:=by
 funext i; unfold Function.comp positionB; simp_rw [val_embed, Nat.cast_mul,_root_.mul_assoc] -- tune loop
 rw [←Finset.mul_sum, S.sizes]; push_cast; change S.patch.L.val*_ / ((C.val:ℝ)* S.patch.L.val)=_; have h: (S.patch.L.val:ℝ)≠0:=Nat.cast_ne_zero.mpr S.patch.L.property.ne'; field
private lemma at_wrap (t:Axis→ℝ) (e:Bond N): positionB t (e.1+step e.2)-positionB t e.1+extra t e=t e.2/N.val:= by
 rcases e with ⟨x,i⟩; change positionB t (x+step i)- _+_= t i/N.val
 let W(x:Site N):=∑ i,(x i).val * t i
 have hx(y:Site N):positionB t y=W y/N.val:=rfl
 let J:= (x i).val; let f:= (N.val:ℝ); let k:= t i; let z:=x+step i
 have he: W z - W x=((z i).val:ℝ)*k-(J:ℝ)*k:=by
    unfold W; rw [←Finset.sum_sub_distrib,sum_eq_single i]
    · intro j u v; simp [z,v]
    exact fun h=>False.elim (h (mem_univ _))
 have ht: (z i).val=if J+1=N.val then 0 else J+1:=by
    unfold z; simp only [Pi.add_apply,step_apply,↓reduceIte]; rw [ZMod.val_add,ZMod.val_one_eq_one_mod,Nat.add_mod_mod]; split_ifs with h
    · rw [show (x i).val+1=N.val from h,Nat.mod_self]
    exact Nat.mod_eq_of_lt (by unfold J at *; have hp:= ZMod.val_lt (x i); omega)
 rw [hx,hx, ← sub_div, he,ht]; unfold extra; dsimp only; by_cases h:J+1=N.val
 · rw [if_pos h,if_pos (show (x i).val+1=N.val from h)]; push_cast; change (0*k-J*k)/f+k=k/f -- tune
   have hp': (J:ℝ)+1=f:= by unfold f; exact_mod_cast h
   have hz:f≠0:=Nat.cast_ne_zero.mpr N.property.ne'; field_simp; rw [←hp']; ring
 rw [if_neg h,if_neg (show (x i).val+1≠N.val from h)]; push_cast; unfold k; ring
lemma seamB (t:Axis→ℝ) : extra (N:=N) t= conF N (fun i=>t i / N.val) - differ (positionB t):=by
 funext i; change _=t i.2/N.val-differ _ i; exact eq_sub_of_add_eq ( (add_comm ..).trans (at_wrap _ i)) -- tune
lemma seam_block (t:Axis→ℝ): pressB S (extra t)=extra t:=by
 rw [seamB,map_sub, exact_block,real_coarse, con_block,seamB]; congr 2; funext i; simp only [Pi.smul_apply,nsmul_eq_mul,S.sizes,Nat.cast_mul]; have h: (S.patch.L.val:ℝ)≠0:=Nat.cast_ne_zero.mpr S.patch.L.property.ne'; field
-- Beautiful. charge itself not merely gauge equiv.
lemma fl_block (v:Site N→ℝ)(t:Axis→ℝ): pressB S (Fl v t)=Fl (v ∘ S.ratio.embed) t:=by
 rw [show Fl v t=differ v+extra t from rfl,map_add,seam_block, exact_block]; rfl
end YM.CF.Papyrus.GaugeFlux
#print axioms YM.CF.Papyrus.GaugeFlux.fl_block
