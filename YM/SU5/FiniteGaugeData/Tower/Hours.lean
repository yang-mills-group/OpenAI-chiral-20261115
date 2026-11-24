import YM.SU5.FiniteGaugeData.Tower.TimeKeeper
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Spatial moves -- across-time forms, commutation on lattice and continuations
-/
open scoped InnerProductSpace
open Fock
section plane
variable {Z:Calibration}(a j:Axis)(g:a≠j)(x z:ℤ)
local notation "n" m:max=> (Z.c m)

include g
private lemma cross_lag : joinX (plane j z) (lagX (x • step a))=joinX (lagX (x • step a)) (plane j z):=by
 simp only [joinX,plane,lagX,Signed.act_one,mul_one,one_mul]
 have h:(Signed.mirror j).act (x • step a : Cover)=x • step a:=by
    funext b; by_cases k:j=b
    · subst b; simp [Signed.mirror,Signed.act,g,Ne.symm g]
    simp_all [Signed.mirror,Signed.act,eq_comm (a:=j) (b:=b)]
 rw [h,add_comm]
omit g
variable {S:Finset Cover}{w b:Bool}{F:Family Z}(p:InTest Z w S b F)
local notation "U" x:max y:max m:max=> prepU (lagX (x • step y)) 1 inert (Z.c m)
local notation "N" x:max y:max R:max=> Yg (lagX (x • step y)) R
include p
private lemma raw_slide(m:Side)(R):chime Z a x F m R= twist (quantU (U (-x) a m)) (F m (N x a R.1, N x a R.2)):=by
 change theta (carR a x (Z.c m)) (theta (carR a 0 _) (F m (fling a 0 _ (fling a x (Z.c m) R.1),fling a 0 _ (fling a x _ R.2))))=_
 unfold fling; rw [← kor,← kor,Heat.plane_join,sub_zero]; rw [Heat.theta_theta _ _ _ (Heat.firm_join a 0 x) ((p.support m).allV _|>.sector), zero_sub]
include g
lemma straddle: chime Z a x (mirror Z j z F)=mirror Z j z (chime Z a x F):=by
 funext m W
 rw [raw_slide a x (axial Z j z p)]; change twist (quantU (U (-x) a m)) (theta (carR j z _) (F m (fling j z _ _, fling j z _ _)))=theta (carR j z _) (chime Z a x F m (fling j z _ W.1,fling j z _ W.2)); rw [raw_slide a x p]
 unfold fling; rw [← kor,← kor,← kor,← kor,cross_lag a j g]
 let v:=Z.c m
 have he:(carR j z v).val*(U (-x) a m).val=(U (-x) a m).val*(carR j z v).val:=by
    change (carR j z _ * _).val = (_ * carR j z _).val; unfold carR; rw [kio,kio,cross_lag a j g,mul_one,one_mul]
 exact (theta_twist_right _ _ _ he ((p.support m).allV _|>.sector)).symm
omit g
omit p
lemma twin_slide (p : InTest Z true S false F) : chime Z a x (chime Z j z F)= chime Z j z (chime Z a x F):=by
 by_cases h:a=j
 · subst a
   -- bumps requires w=true b=false; so restrict or generalize
   rw [Tower.bumps _ _ x z p,Tower.bumps _ _ z x p,add_comm]
 unfold chime
 -- reveals chime a too, reconstruct
 change chime Z a x (mirror Z j z (mirror Z j 0 F))=mirror Z j z (mirror Z j 0 (chime Z a x F))
 rw [straddle a j h x z (axial Z j 0 p),straddle a j h x 0 p]
end plane
section raw
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}(Q:Resolution (E:=E) Y H D)
variable (j:Axis)(z:ℤ)(strict:Bool)
variable (a: Axis) (σ : a ≠ j)
variable (C:Arena Y H Q j z strict)
local notation "T" s:max=> Tower.Field Y H s j z strict
local notation "κ" s:max=>actor Y H s Q j z strict C
local notation "A"=> Ark.Ht Y H Q j z strict C
local notation "ρ" s:max i:max=>ripple Y H V s Q j z strict C i
local notation "J" x:max=> Heat.gaugeShift Λ.block x
local notation "m"=> meshface (Λ:=Λ) z s
lemma field_test (f:T s): TestFamily K true f.val:= (exam j _ K ((purpose_ok ..).1 f.property).1).1

local notation "Φ" k:max f:max=> chime K a (J k) f
include σ
lemma side_box {u:ℤ}{S:Finset Cover}(p:region j m (K).ℓ S):region j m (K).ℓ (address a (J u) S):=by
 intro i h; obtain ⟨x,g,rfl⟩:= mem_image.mp h; simpa [Ne.symm σ] using p x g
private lemma beside (x:ℤ)(t:T s): Φ x t.val∈purpose K m j strict:=by
 obtain ⟨v,h⟩:= (purpose_ok ..).1 t.property; obtain ⟨c,hx,v⟩:= (v:∃ S:Finset Cover,InTest (tent Y H) true S false _ ∧ region j m (K).ℓ S)
 exact (purpose_ok ..).2 ⟨⟨address a _ c,flow_port _ _ _ hx,side_box Y H s j z a σ v⟩,fun g=> chime_cov _ _ _ hx (h g)⟩
noncomputable def sail (x:ℤ): (Tower.Field Y H s j z strict)→ₗ[ℂ] Tower.Field Y H s j z strict where
 toFun t:=⟨chime K a _ t.val,beside Y H s j z strict a σ x t⟩
 map_add' _ _:=Subtype.ext (chime_plus ..)
 map_smul' c _:=Subtype.ext (chime_scale ..)
local notation "Δ" a:max σ:max x:max=>sail Y H s j z strict a σ x
lemma sails(x y:ℤ)(t:T s): (Δ a σ x) ((Δ a σ y) t)=(Δ a σ (x+y)) t:=by
 apply Subtype.ext; change Φ x (Φ y t.val) = Φ (x+y) t.val
 rw [Tower.bumps _ _ _ _ (field_test Y H s j z strict t).paid.choose_spec]; unfold Heat.gaugeShift; congr 1; ring
lemma sail_seed (t:T s): (Δ a σ 0) t=t:=by apply Subtype.ext; change Φ 0 t.val = t.val; rw [show (J (0:ℤ))=0 from by unfold Heat.gaugeShift; ring,wake _ _ (field_test Y H s j z strict t).paid.choose_spec]
lemma sail_vacuum (x:ℤ):(Δ a σ x) (unity Y H j z strict s)=unity Y H j z strict s:=Subtype.ext (chime_unit K _ _)
lemma crossover(x:ℤ)(q:ℕ)(t:T s): (Δ a σ x) (tick Y H s j z strict q t)=tick Y H s j z strict q ((Δ a σ x) t):=Subtype.ext (twin_slide a j _ _ (field_test Y H s j z strict t).paid.choose_spec)
lemma acrossover(k:Axis)(σ': k ≠ j)(x y:ℤ)(t:T s): (Δ a σ x) ((Δ k σ' y) t)=(Δ k σ' y) ((Δ a σ x) t):=Subtype.ext (twin_slide a k _ _ (field_test Y H s j z strict t).paid.choose_spec)
include V Q
lemma sail_up (r:ℕ)(p:s≤r)(t:T s)(x:ℤ):sail Y H r j z strict a σ (Λ.R.L.val^(r-s)*x) (Raise Y H Q j z strict s r p t)=Raise Y H Q j z strict s r p ((Δ a σ x) t):=by
 apply Subtype.ext; change chime K a _ (stream Y H D s _ _) = stream Y H D s (r-s) (Φ x t.val)
 rw [chime_X Y H V s a x Q (field_test Y H s j z strict t)]
include C
lemma sail_preserves(x:ℤ)(t u:T s):inner ℂ ((κ s) ((Δ a σ x) t)) ((κ s) ((Δ a σ x) u))= inner ℂ ((κ s) t) ((κ s) u):= by
 rw [stems Y H V,stems Y H V]
 change E s (mirror K j m (Φ x t.val) * Φ x u.val)=_
 have v (b:T s):=field_test Y H s j z strict b
 rw [←straddle a j σ _ _ (v t).paid.choose_spec, ←chime_product]
 exact SWay Y H V s a x ((exam j _ K ((purpose_ok ..).1 t.property).1).2.mul (v _))
lemma sail_isometry(x:ℤ)(t:T s):‖(κ s) ((Δ a σ x) t)‖=‖(κ s) t‖:= by nth_rw 1 [@norm_eq_sqrt_re_inner ℂ]; rw [sail_preserves Y H V,←@norm_eq_sqrt_re_inner ℂ]
/-- Lift an arbitrary compatible late family (supported vectors at all
levels r above s). Keeps same Hilbert at all tiers, abbreviate replication of
Pool. No pretense moving vectors have well behaved Fock norm. -/
structure Lamination where
 go (r:ℕ)(p:s≤r): Tower.Field Y H r j z strict →ₗ[ℂ] Tower.Field Y H r j z strict
 same (t r:ℕ)(p:s≤t)(v:t≤ r)(x:T t): Raise Y H Q j z strict t r v (go t p x)=go r (p.trans v) (Raise Y H Q j z strict t r v x)
 weak (r:ℕ)(p:s≤ r)(x:T r): ‖actor Y H r Q j z strict C (go r p x)‖≤ ‖actor Y H r Q j z strict C x‖
omit σ
variable (L₀:Lamination Y H s Q j z strict C)
local notation "χ"=> Choir Y H j z strict
local notation "R"=> Raise Y H Q j z strict
local notation "κ'" s:max=>arrows Y H V Q j z strict C s
noncomputable def excursion(x:χ):A:= (κ (max s x.1)) (L₀.go (max s x.1) (le_max_left ..) (R x.1 (max s x.1) (le_max_right ..) x.2))
local notation "ω"=>excursion Y H s Q j z strict C L₀
lemma path_eq {u r:ℕ}(p:s≤r)(v:u≤ r)(x:T u): ω (show χ from ⟨u,x⟩)=(κ r) (L₀.go r p (R u r v x)):=by
 unfold excursion; simp only
 set t:=max s u; have a:s≤t:=le_max_left ..; have b:u≤t:=le_max_right ..; let e:=max_le p v
 rw [←join_actor Y H V Q j z strict C t r e,L₀.same]; congr 2; apply Subtype.ext; have eee:=congrArg Subtype.val (linking_diagram Y H Q j z b (show t≤r from e) (freeze Y H u j z strict x)); exact eee
lemma shipboat: ∃ G:A→L[ℂ] A,‖G‖≤1 ∧ ∀r (x:T r), G ((κ r) x)=ω (show χ from ⟨r,x⟩):=by
 suffices h:∃ G:A→L[ℂ] A,‖G‖≤1 ∧ ∀x:χ,G ((κ x.1) x.2)=ω x by obtain ⟨v,t,e⟩:=h; exact ⟨v,t,fun r x=>e (show χ from ⟨r,x⟩)⟩
 apply _root_.YM.Kernel.Gram.by_bound C (fun x=>ω x) 1 zero_le_one
 intro f
 let r:=max s (f.support.sup (fun i:χ=>i.1)); let w:=le_max_left s (f.support.sup (fun i:χ=>i.1))
 have hp:s≤ r:=w; have he(i:χ)(t:i∈f.support):i.1 ≤r:= (le_sup (f:=fun i:χ=>i.1) t).trans (le_max_right ..)
 let y(i:χ):T r:=if t:i∈f.support then R i.1 r (he i t) i.2 else 0
 let x:T r:= f.sum fun i v=>v• y i
 have a: (κ' r) x=(show _root_.YM.Kernel.Gram _ from C).stems f:=by
    simp only [_root_.YM.Kernel.Gram.stems,Finsupp.linearCombination_apply,x,map_finsuppSum,map_smul]
    unfold Finsupp.sum; refine sum_congr rfl fun i v=> ?_; dsimp only; unfold y; rw [dif_pos v]; exact congrArg (fun u:A=> f i • u) (join_actor Y H V Q j z strict C i.1 r (he i v) i.2)
 let g:=L₀.go r hp
 have b: (κ' r) (g x)=Finsupp.linearCombination ℂ (fun x=>ω x) f:=by
    simp only [Finsupp.linearCombination_apply,x,map_finsuppSum,map_smul]
    unfold Finsupp.sum; refine sum_congr rfl fun i v=> ?_; dsimp only; unfold y; rw [dif_pos v]; exact congrArg (fun u:A=> f i • u) (path_eq Y H V s Q j z strict C L₀ hp (he i v) i.2).symm
 rw [one_mul,←a,←b]; exact L₀.weak ..
noncomputable def onship:A→L[ℂ] A:= (shipboat Y H V s Q j z strict C L₀).choose
local notation "S₀"=>onship Y H V s Q j z strict C L₀
lemma nearship: ‖S₀‖≤1:= (shipboat Y H V s Q j z strict C L₀).choose_spec.1
lemma offship {r t:ℕ}(p:s≤ r)(v:t≤ r)(x:T t): (S₀) ((κ t) x)=(κ r) (L₀.go r p (R t r v x)):= (shipboat Y H V s Q j z strict C L₀).choose_spec.2 t x |>.trans (path_eq Y H V s Q j z strict C L₀ p v x)
lemma todeck {t:ℕ}(p:s≤t)(x:T t): (S₀) ((κ t) x)=(κ t) (L₀.go t p x):=by
 have h:R t t (le_refl _) x=x:=Subtype.ext (by change stream Y H D t _ _=x.val; rw [Nat.sub_self]; rfl)
 exact (offship Y H V s Q j z strict C L₀ p le_rfl x).trans (by rw [h])

private lemma high_test (tG tH:A→L[ℂ] A)(P:∀ r:ℕ, s≤r → ∀ x:T r,tG ((κ r) x)=tH ((κ r) x)): tG=tH:=by
 apply _root_.YM.Kernel.Gram.by_bud C; intro i
 let r:=max s i.1; have e:s≤r:=le_max_left ..; have v:i.1≤r:=le_max_right ..
 have h:=P r e (R i.1 r v i.2); rwa [join_actor Y H V] at h

-- signed amount at integer scale
noncomputable def smill (Λ:Preparation)(s r:ℕ)(i:ℤ):ℤ:=(Λ.R.L.val:ℤ)^(r-s)*i
omit V C Q
lemma smill_id (Λ:Preparation)(s:ℕ)(i:ℤ):smill Λ s s i=i:=by simp [smill]
lemma smill_add (Λ:Preparation)(s r:ℕ)(i k:ℤ):smill Λ s r (i+k)=smill Λ s r i+smill Λ s r k:=by simp [smill,mul_add]
private lemma smill_count (Λ:Preparation)(s r t:ℕ)(p:s≤r)(q:r≤t)(i:ℤ):smill Λ r t (smill Λ s r i)=smill Λ s t i:= by unfold smill; rw [←mul_assoc,←pow_add,show t-r+(r-s)=t-s by omega]
include V Q C σ
noncomputable def sailboat (x:ℤ):Lamination Y H s Q j z strict C where
 go r _:=sail Y H r j z strict a σ (smill Λ s r x)
 weak r _ y:=(sail_isometry Y H V r Q j z strict a σ C _ y).le
 same t r p v y:=by
   rw [←sail_up Y H V t Q j z strict a σ r v y]
   exact congrArg (fun x=>sail Y H r j z strict a σ x _) (smill_count Λ s t r p v x)
noncomputable def sailV (x:ℤ):A→L[ℂ] A:=onship Y H V s Q j z strict C (sailboat Y H V s Q j z strict a σ C x)
local notation "V₀" s:max a:max σ:max x:max=>sailV Y H V s Q j z strict a σ C x
lemma sailV_at (x:ℤ)(t:ℕ)(v:s≤ t)(y:T t):(V₀ s a σ x) ((κ t) y)=(κ t) (sail Y H t j z strict a σ (smill Λ s t x) y):=todeck Y H V s Q j z strict C (sailboat Y H V s Q j z strict a σ C x) v y
lemma sailV_source:(V₀ s a σ 0)=ContinuousLinearMap.id ℂ A:=by
 apply high_test Y H V s Q j z strict C; intro r p x
 change (V₀ s a σ 0) _=(κ r) x
 rw [sailV_at Y H V s Q j z strict a σ C 0 r p x,smill,mul_zero,sail_seed]
lemma sailV_sum(x y:ℤ): (V₀ s a σ x).comp (V₀ s a σ y)=V₀ s a σ (x+y):=by
 apply high_test Y H V s Q j z strict C; intro r p f
 rw [ContinuousLinearMap.comp_apply,sailV_at Y H V s Q j z strict a σ C y r p,sailV_at Y H V s Q j z strict a σ C x r p,sailV_at Y H V s Q j z strict a σ C (x+y) r p,smill_add,sails]
lemma sailV_high (x:ℤ)(t:ℕ)(p:s≤ t):(V₀ s a σ x)=V₀ t a σ (smill Λ s t x):=by
 apply high_test Y H V t Q j z strict C; intro r q f
 rw [sailV_at Y H V _ Q j z strict a σ C _ r (p.trans q), sailV_at Y H V _ Q j z strict a σ C _ r q,smill_count Λ s t r p q x]
lemma sailV_small(x:ℤ): ‖V₀ s a σ x‖≤1:=nearship Y H V s Q j z strict C (sailboat Y H V s Q j z strict a σ C x)
lemma sailV_commutes(b:Axis)(σ':b≠j)(x y:ℤ):(V₀ s a σ x).comp (V₀ s b σ' y)=(V₀ s b σ' y).comp (V₀ s a σ x):=by
 apply high_test Y H V s Q j z strict C; intro r q f
 rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply]
 simp only [sailV_at Y H V s Q j z strict a σ C x r q,sailV_at Y H V s Q j z strict b σ' C y r q]; rw [acrossover]
lemma sailV_tide(x:ℤ)(k:ℕ):(V₀ s a σ x).comp (ρ s k)=(ρ s k).comp (V₀ s a σ x):=by
 apply high_test Y H V s Q j z strict C; intro r q f
 simp only [ContinuousLinearMap.comp_apply,sailV_at Y H V s Q j z strict a σ C x r q,limited_time Y H V s Q j z strict C k q]; rw [crossover]
lemma sailV_vac(x:ℤ):(V₀ s a σ x) (floorV Y H Q j z strict C)=floorV Y H Q j z strict C:=by
 rw [vacua Y H V Q j z strict C s,sailV_at Y H V s Q j z strict a σ C _ s (le_refl s),sail_vacuum]
lemma sailV_time(x:ℤ)(t:ℝ≥0): (V₀ s a σ x).comp (advance Y H V Q j z strict C t)=(advance Y H V Q j z strict C t).comp (V₀ s a σ x):=by
 ext1 f
 change (V₀ s a σ x) (advance _ _ _ _ _ _ _ _ t f)=advance _ _ _ _ _ _ _ _ t ((V₀ s a σ x) f) -- careful ambig
 let S0:=V₀ s a σ x
 suffices h:(fun u:ℝ≥0=>S0 (advance Y H V Q j z strict C u f))=(fun u:ℝ≥0=>advance Y H V Q j z strict C u (S0 f)) by exact congrFun h t
 apply (MeshClock.fills (timeMesh Λ)).denseRange_val.equalizer
 · exact S0.continuous.comp (advance_strong Y H V Q j z strict C f).continuous
 · exact (advance_strong Y H V Q j z strict C _).continuous
 funext u; dsimp only [Function.comp_apply]
 obtain ⟨r,i,h⟩:=MeshClock.split _ u.property
 rw [← h,advance_at]
 let mm:=max r s; have hp:r ≤ mm:=le_max_left ..; have ht:s ≤ mm:=le_max_right ..
 unfold S0
 rw [← consistent_τ Y H V r Q j z strict C (2*i) mm hp,sailV_high _ _ V s _ _ _ _ a _ C x mm ht,←ContinuousLinearMap.comp_apply, sailV_tide]; rfl
end raw
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.sailV_commutes
#print axioms YM.CF.Buffered.Afterglow.Tower.sailV_sum
#print axioms YM.CF.Buffered.Afterglow.Tower.sailV_time
