import GaugeFieldConstruction.TeamEffort
/-
 K1 triangular estimate without determinant. ℓ1 norms. usable with euclidean bases via constant equivalence.
-/
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Frugal
open Function Finset
open scoped Classical BigOperators Topology
variable {I E:Type*}[Fintype I] [NormedAddCommGroup E][NormedSpace ℂ E]
-- grade from 3. 
abbrev FrameK (I:Type*) := I→ℂ
abbrev LoomK (x:FrameK I): ℝ:=∑ i, ‖x i‖
abbrev Woof (w:FrameK I)(p:I→E):E:=∑ i, w i • p i
abbrev scalB (p:I→E):FrameK I→ₗ[ℂ]E:=
 { toFun:=fun w=>Woof w p
   map_add':=fun v w=> by simp [Woof,add_smul,sum_add_distrib] -- tune
   map_smul':=fun a v=>by simp [Woof, Finset.smul_sum,mul_smul] }
lemma noLoom (w:FrameK I):0≤LoomK w:=sum_nonneg fun _ _=> norm_nonneg _
lemma woof_cost (w:FrameK I){p:I→E}{e:ℝ}(h:∀ i,‖p i‖≤e) : ‖Woof w p‖≤ LoomK w *e:= le_trans (norm_sum_le ..) (by unfold LoomK; rw [sum_mul]; exact sum_le_sum fun i _=> (norm_smul_le ..).trans (mul_le_mul_of_nonneg_left (h i) (norm_nonneg _)))
lemma single_k (w:FrameK I)(i:I):‖w i‖≤LoomK w:= single_le_sum (fun _ _=> norm_nonneg _) (mem_univ i)
abbrev GradeV (γ:I→ℕ)(w:FrameK I)(p:ℕ→Prop): FrameK I:= fun i=> if p (γ i) then w i else 0 -- classical prop uses Classical.choice; rewriting instance issues.
lemma grade_cost (γ:I→ℕ) (w:FrameK I) (p:ℕ→Prop) : LoomK (GradeV γ w p)≤ LoomK w:= sum_le_sum (fun i _=>by unfold GradeV; split_ifs; rfl; exact (norm_zero.le.trans (norm_nonneg _))) -- tune rfl
-- generic Inverse
variable (grade:I→ℕ){basisP:I→E}(Λ:ℕ→E→ₗ[ℂ]E) (cap:E→ₗ[ℂ]E) (Dim:ℕ) {W:I→E}{τ X φ:ℝ}
structure Planaris (basis:I→E)(τ:ℝ):Prop where
 ray (i:I): grade i≤Dim
 bounded (i:I): ‖basis i‖≤τ
 coframe(x:E)(p:Λ Dim x=x):∃ w:FrameK I,x=Woof w basis
 saturated(i:I)(j:ℕ): Λ j (basis i)= if grade i≤j then basis i else 0
 brake(w:FrameK I): LoomK w≤ τ*‖Woof w basis‖
structure EclipseS (τ:ℝ):Prop where
 home(x:E):‖x‖ ≤τ*‖cap x‖
 span(j:ℕ):∀ x:E,cap (Λ j x)=Λ j (cap x)
 calm (i:ℕ)(x:E): ‖Λ i x‖≤‖x‖
 latch {i j:ℕ}(p:i ≤ j)(x:E): Λ i (Λ j x)=Λ i x
structure Facies (basis W:I→E) (X φ:ℝ):Prop where
  sane (i:I):‖W i‖ ≤ X
  ne (i:I): ‖Λ (grade i) (W i)-cap (basis i)‖≤φ
  high(i:I):Λ Dim (W i)=W i
variable (hp:Planaris grade Λ Dim basisP τ)(hv:EclipseS Λ cap τ)(hP:Facies grade Λ cap Dim basisP W X φ)(wt:0≤ τ)(pX:0≤ X)(pt:0≤φ)
include hp hv hP wt pt pX
abbrev Tickle (γ:I→ℕ)(n:ℕ)(w:FrameK I):= GradeV γ w (·< n)
abbrev VeinB (w:FrameK I)(W:I→E)(φ:ℝ):= ‖Woof w W‖ + φ*LoomK w
-- cumulative next using exact collection of errors on all remaining. allow expensive lower.
lemma goods (w:FrameK I)(r:ℕ) : let ν:=LoomK (GradeV grade w (·=r)); let t:=τ*τ
 ν ≤ t*(VeinB w W φ+X * LoomK (Tickle grade r w)):=by
 intro ν t; let x:=Tickle grade r w; let y:=GradeV grade w (·=r)
 let T:= Woof y basisP
 have Hk: Woof y basisP=T:=rfl
 let F:= fun i=>w i • Λ r (W i)- x i • Λ r (W i)- y i • cap (basisP i)
 have He: ‖Λ r (Woof w W) - Λ r (Woof x W) -cap T‖≤ φ*LoomK w:= by
    unfold Woof LoomK; rw [show T=Woof y basisP from rfl]; unfold Woof; rw [map_sum,map_sum,map_sum]
    simp only [map_smul]; rw [← sum_sub_distrib,←sum_sub_distrib, mul_sum]; apply (norm_sum_le ..).trans
    apply sum_le_sum; intro i _; change ‖F i‖ ≤ _; unfold F; rcases lt_trichotomy (grade i) r with h|h|h
    · dsimp only [x,y,Tickle,GradeV]; rw [if_pos h,if_neg (ne_of_lt h),sub_self,zero_smul,sub_zero,norm_zero]; positivity
    · dsimp only [x,y,Tickle,GradeV]; rw [if_pos h,if_neg (show ¬ grade i < r from by omega),zero_smul,sub_zero, ← smul_sub, norm_smul,mul_comm φ]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _); rw [←h]; exact hP.ne i
    dsimp only [x,y,Tickle,GradeV]; rw [if_neg (Ne.symm (ne_of_lt h)),if_neg (show ¬ grade i < r from by omega),zero_smul,zero_smul,sub_zero,sub_zero,norm_smul,mul_comm φ]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _); have Ha:= (hv.calm r (Λ (grade i) (W i)-cap (basisP i))).trans (hP.ne i)
    rw [map_sub,hv.latch h.le,←hv.span,hp.saturated,if_neg (not_le_of_gt h),map_zero,sub_zero] at Ha; exact Ha
 have Hw: ‖cap T‖≤VeinB w W φ+X * LoomK x:=by
    have Hv : ‖Λ r (Woof w W)-Λ r (Woof x W)‖ ≤‖Woof w W‖ + LoomK x*X:= le_trans (norm_sub_le ..) (add_le_add (hv.calm ..) ((hv.calm ..).trans (woof_cost x hP.sane)))
    have Hp := norm_sub_le (Λ r (Woof w W)-Λ r (Woof x W)) ((Λ r (Woof w W)-Λ r (Woof x W))-cap T); rw [sub_sub_cancel] at Hp; unfold VeinB; rw [mul_comm X]; linarith only [He,Hp,Hv]
 have Hu : ν ≤τ* ‖T‖:= hp.brake y
 exact le_trans Hu ((mul_le_mul_of_nonneg_left (le_trans (hv.home T) (mul_le_mul_of_nonneg_left Hw wt)) wt).trans_eq (mul_assoc ..).symm)
abbrev TowerX (τ X:ℝ):ℕ→ℝ
 | 0 => 0
 | n+1=> TowerX τ X n+τ*τ*(1+X*TowerX τ X n)
omit hp hv hP wt pt pX
lemma Tower_nn (t x:ℝ)(h:0≤t)(p:0≤x)(n:ℕ):0 ≤ TowerX t x n:=by induction n with
 | zero=>rfl
 | succ n ih=>rw [TowerX]; positivity
include hp hv hP wt pt pX
lemma encompass (w:FrameK I)(r:ℕ) : LoomK (Tickle grade r w) ≤ TowerX τ X r * VeinB w W φ:=by
 induction r with
 | zero=>have hz:Tickle grade 0 w=0:=by funext i; unfold Tickle GradeV; rw [if_neg (by omega)]; rfl
         rw [hz]; simp [LoomK,TowerX]
 | succ r hr=>
    have He:= goods grade Λ cap Dim hp hv hP wt pX pt w r; dsimp only at He -- tune unfolds lets only
    have Hs:LoomK (Tickle grade (r+1) w) = LoomK (Tickle grade r w)+ LoomK (GradeV grade w (·=r)):=by
       unfold LoomK; rw [←sum_add_distrib]; apply sum_congr rfl; intro i _; unfold Tickle GradeV; split_ifs <;> (first | solve | omega | simp_all only [norm_zero,add_zero,zero_add]) -- tune precedence
    rw [Hs,TowerX]; calc
       _ ≤ TowerX τ X r*VeinB w W φ + τ*τ*(VeinB w W φ+X*(TowerX τ X r*VeinB w W φ)) := add_le_add hr (le_trans He (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hr pX) _) (by positivity)))
       _ = _:= by ring
lemma downward (w:FrameK I)(y:TowerX τ X (Dim+1)*φ ≤1/2) : LoomK w ≤ (2*TowerX τ X (Dim+1))* ‖Woof w W‖:=by
 have He:= encompass grade Λ cap Dim hp hv hP wt pX pt w (Dim+1); rw [show Tickle grade (Dim+1) w=w from funext fun i=> if_pos (Nat.lt_add_one_iff.mpr (hp.ray i))] at He; unfold VeinB at He; rw [mul_add,←mul_assoc _ φ] at He
 have Hp:= mul_le_mul_of_nonneg_right y (noLoom w); linarith only [He,Hp] -- products regroup
omit hp hv hP wt pt pX
private lemma fdim_self {F H:Type*}[AddCommGroup F][Module ℂ F][FiniteDimensional ℂ F][AddCommGroup H][Module ℂ H](X Y:F →ₗ[ℂ] H)(p:Surjective X)(t:Injective X)(u:Injective Y):Surjective Y:=by
 let E:=LinearEquiv.ofBijective X ⟨t,p⟩; let K:=E.symm.toLinearMap ∘ₗ Y; have h:Surjective K :=(LinearMap.injective_iff_surjective).mp (E.symm.injective.comp u); intro z; obtain ⟨x,e⟩:=h (E.symm z); exact ⟨x,E.symm.injective e⟩ -- section include! omit
include hp hv hP wt pt pX
lemma onward (y:TowerX τ X (Dim+1)*φ ≤1/2) : Injective (scalB W) ∧ ∀ x:E,Λ Dim x=x→∃ w:FrameK I, scalB W w=x:=by
 let Y:= LinearMap.ker (Λ Dim-LinearMap.id)
 have H(i:E):i∈Y↔Λ Dim i=i:=by rw [LinearMap.mem_ker]; exact sub_eq_zero
 let p(w:FrameK I):scalB W w∈Y:=by rw [H]; change Λ Dim (Woof _ W)=Woof _ W; unfold Woof; simp only [map_sum,map_smul,hP.high]
 let q(w:FrameK I):scalB basisP w∈Y:=by
    have hh(i:I):Λ Dim (basisP i)=basisP i:=by rw [hp.saturated, if_pos (hp.ray i)]
    rw [H]; change Λ Dim (Woof _ basisP)=Woof _ basisP; unfold Woof; simp only [map_sum,map_smul,hh]
 let A:FrameK I→ₗ[ℂ]Y:=(scalB basisP).codRestrict Y q
 let B:FrameK I→ₗ[ℂ]Y:=(scalB W).codRestrict Y p
 have hx : Surjective A:=by rintro ⟨x,e⟩; obtain ⟨w,h⟩:= hp.coframe x ((H _).mp e); exact ⟨w,Subtype.ext h.symm⟩
 have hu(w:FrameK I)(y:LoomK w ≤0): w=0:=funext fun i=> norm_le_zero_iff.mp ((single_k w i).trans y)
 have Hy: Injective A:= LinearMap.ker_eq_bot.mp (by
    rw [LinearMap.ker_eq_bot']; intro w t; have He:Woof w basisP=0:=congrArg Subtype.val t; have h:=hp.brake w; rw [He,norm_zero,mul_zero] at h; exact hu w h)
 have ht: Injective (scalB W):= LinearMap.ker_eq_bot.mp (by
    rw [LinearMap.ker_eq_bot']; intro w t; change Woof w W=0 at t; have e:= downward grade Λ cap Dim hp hv hP wt pX pt w y; rw [t,norm_zero,mul_zero] at e; exact hu w e)
 have hf:= fdim_self A B hx Hy (fun _ _ h=> ht (congrArg Subtype.val h))
 refine ⟨ht, fun x p' =>?_⟩; obtain ⟨w,v⟩:=hf ⟨x,(H x).mpr p'⟩; exact ⟨w,congrArg Subtype.val v⟩
end YM.Frugal
end
