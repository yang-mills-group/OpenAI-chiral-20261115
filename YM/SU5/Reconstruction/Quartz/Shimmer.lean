import YM.SU5.Reconstruction.Quartz.Split
import Mathlib.Analysis.Complex.Hadamard
set_option autoImplicit false
noncomputable section
namespace YM.Quartz
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal Complex ComplexOrder InnerProductSpace
open Multiplier CrossedFrame Clasp Complex HadamardThreeLines
variable {K H D:Hilbert}(C:Clasp K H D)(n:ℕ)
local notation "A"=> C.angle
local notation "P"=> C.motion
local notation "f"=> C.realF
local notation "S"=> spectrum ℂ C.angle
local notation "Q"=> glacier C n
local notation "R"=> Quartz.rise C n
local notation "W"=> peel C.l
local notation "V"=> peel C.r
local notation "L" i:max=> C.Left.symm.conjStarAlgEquiv i
local notation "B" i:max=> C.Right.symm.conjStarAlgEquiv i
variable (X:H.Op)(Y:D.Op)
lemma stained (h:C.Pass X Y) : let z:=C.bring X Y
    (L X)*peel C.l=peel C.l*z ∧ (B Y)*peel C.r=peel C.r*z:= by
 intro z; obtain ⟨r,a⟩:= (C.sustain ..).1 h
 refine ⟨?_,?_⟩<;> ext1 x
 · simp only [mul_apply_eq_comp,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_symm, C.left_done]; apply C.Left.injective; rw [LinearIsometryEquiv.apply_symm_apply,C.left_done]; exact DFunLike.congr_fun r.symm x
 simp only [mul_apply_eq_comp,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_symm, C.right_done]; apply C.Right.injective; rw [LinearIsometryEquiv.apply_symm_apply,C.right_done]; exact DFunLike.congr_fun a.symm x
lemma rise_one_tag (x:S)(p:f x∈ Ioo (0:ℝ) 1)(e:x∈slopeZone C n): rise_tag C n 1 x* glaze (C.realF x)= glaze (1-C.realF x):= by
 let t:= C.crystal x; let r:= f x; obtain ⟨pr,pt⟩:= p; unfold rise_tag glaze; rw [face_ready C n x e,show (1:ℂ)/2 = ((↑(1/2:ℝ)):ℂ) from by push_cast; rfl, ← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul] -- ofReal_one tune
 apply congrArg; let v:=(1:ℝ)/2*t; have hh: v+v=t:=by unfold v; ring
 have hp:0< 1-r:=sub_pos.mpr pt; have hm:Real.exp t=(1-r)/r:= Real.exp_log (div_pos hp pr)
 have z: Real.exp v*Real.exp v=(1-r)/r:= by rw[←Real.exp_add,hh]; exact hm
 have hw:(Real.exp v*Real.sqrt r)^2=1-r:= by rw[mul_pow,Real.sq_sqrt pr.le,pow_two,z,div_mul_cancel₀ _ pr.ne']
 change Real.exp v*Real.sqrt r= Real.sqrt _; nth_rw 1 [← Real.sqrt_sq (show 0≤Real.exp v*Real.sqrt r from by positivity),hw]
lemma reach_exact : (glacier C n)*Quartz.rise C n 1*peel C.l=(glacier C n)*peel C.r:=by
 let x:= ((earth C n).times (rising C n 1)).times (peelL C); refine x.single (((earth C n).times (peelR C)).agrees x.price (fun v=>(C.inOpen v).mono ?_))
 intro t ht; by_cases k:t∈ slopeZone C n<;> simp only [Pi.mul_apply,comp_apply]; · simpa [k] using (rise_one_tag C n t ht k).symm
 simp [k]
lemma glacier_walk (z:ℂ): Commute (glacier C n) (Quartz.rise C n z):= (earth C n).jointly (rising C n z)
lemma base_walk (e:ℝ): Q * R ((e:ℂ)*I)= Q * C.Cabin (e/2) := by
 apply ((earth C n).times (rising C n ((e:ℂ)*I))).single; convert (earth C n).times (C.Cabin_reads (e/2)) using 1; ext1 x; by_cases h:x∈ slopeZone C n
 · simp only[h,indicator_of_mem,Pi.one_apply, Pi.mul_apply,one_mul,comp_apply,river, Chirp.sing, rise_tag,face_ready C n x h]; unfold crystal; congr 1; push_cast; ring
 simp [h]
lemma stand (h:C.Pass X Y): (R 1*Q*(L X)*Q)*(R (-1))= Q*(B Y)*Q := by
 let a:= C.bring X Y; let W1:= peel C.l; let V1:=peel C.r; obtain ⟨b,v⟩:=stained C X Y h
 have hs: (Q*B Y*Q)*R 1 = (R 1*Q*L X*Q):= by
   apply dense_cancel W1 (peel_dense C.l C.j); change _*W1= _*W1; let z:= R 1*Q
   have he: Q*R 1*W1=Q*V1:=reach_exact ..; have hw: Q*W1=W1*Q:=((earth C n).jointly (peelL C)).eq; have hv: Q*V1=V1*Q:=((earth C n).jointly (peelR C)).eq
   calc
     Q*B Y*Q*R 1*W1 = Q*B Y*(Q*R 1*W1):= by simp only[mul_assoc]
     _ = Q*(B Y*V1)*Q := by rw [he]; nth_rw 1 [hv]; simp only[mul_assoc]
     _ = Q*R 1*W1*(a*Q):= by rw [he]; unfold V1 a; rw [v]; simp only[mul_assoc]
     _ = R 1*Q*(L X*W1)*Q:= by rw [(glacier_walk C n 1).eq]; unfold W1 a; rw [b]; simp only [mul_assoc]
     _ = R 1*Q*L X*Q * W1:= by rw [mul_assoc (R 1*Q*_) Q W1,hw]; simp only[mul_assoc]
 rw [←hs,mul_assoc (Q*_ *Q),←rise_add]; simp
noncomputable def twinkle (i:K.Op)(z:ℂ):K.Op:= (Quartz.rise C n z*glacier C n*i*glacier C n)*Quartz.rise C n (-z)
local notation "T"=>twinkle C n (L X)
lemma spark (u:ℝ): T ((u:ℂ)*I)= Q*(C.Cabin (u/2)*L X*star (C.Cabin (u/2)))*Q:= by
 let J:= (u:ℂ)*I; let F:=R J; let B1:=R (-J); let G:=C.Cabin (u/2)
 have h₁:F*Q=Q*G:= by unfold F; rw[←(glacier_walk ..).eq]; exact base_walk ..
 have h₂:Q*B1= star G*Q:= by unfold G B1 J; rw[show -((u:ℂ)*I)= (((-u:ℝ):ℂ)*I) from by push_cast; ring,base_walk,C.Cabin_cross,( (earth C n).jointly (C.Cabin_reads _)).eq]; rw[neg_div]
 unfold twinkle; change F*Q*_*Q*B1=_; rw [mul_assoc (F*Q*_),h₁,h₂]; simp only[mul_assoc,G]
lemma summit (u:ℝ)(h:C.Pass X Y): T (1+(u:ℂ)*I)= Q*(C.Cabin (u/2)*B Y*star (C.Cabin (u/2)))*Q := by
 let k:= (u:ℂ)*I
 have p:= stand C n X Y h
 unfold twinkle; change R (1+k)*Q*(L X)*Q* R (-(1+k))=_; rw [add_comm 1 k,neg_add_rev,rise_add,rise_add]; rw [show R k*R 1*Q*(L X)*Q*_= R k*(R 1*Q*(L X)*Q* R (-1))*R (-k) from by simp only [mul_assoc]]; rw[p]
 obtain ⟨x,hx⟩:= C.Left.symm.conjStarAlgEquiv.surjective (B Y); change L x= B Y at hx; rw[← hx,← spark C n x u]; unfold twinkle k; simp only[mul_assoc]
end YM.Quartz
