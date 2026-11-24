import SatinThinJetsAnalytic
import SatinPP.Brackets
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six MacroGrid

section
open OS.Semigroup
variable {G:Hilbert}{j:Axis}(S:OS.Semigroup G j)
-- range Re≥b>0
lemma soften (b:ℝ) (p:0<b) {z:ℂ}(h:b ≤ z.re): ‖deriv S.F z‖ ≤ 2/b:= by
 have hw(w:ℂ)(r:w∈closedBall z (b/2)) :0<w.re:= by
    have g:= (Complex.abs_re_le_norm (w-z)).trans (dist_eq_norm w z ▸ mem_closedBall.mp r) -- ▸ direction
    rw [Complex.sub_re] at g
    linarith only [abs_le.mp g,p,h]
 have t:DifferentiableOn ℂ S.F (closedBall z (b/2)):=fun w r=>(S.localHeat w (hw w r)).differentiableAt.differentiableWithinAt
 refine (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (C:=1) (half_pos p) (t.diffContOnCl_ball (Set.Subset.refl _)) (fun w r=>S.norm_row (hw w (sphere_subset_closedBall r)))).trans_eq (by ring)

lemma soften_le {u v b:ℝ}(p:0<b)(h:b≤u)(q:b≤v):
 ‖S.E u.toNNReal - S.E v.toNNReal‖ ≤ (2/b)*|u-v|:= by
 let M: Set ℂ:= {w | b≤w.re}
 have g:Convex ℝ M:= (convex_halfSpace_ge Complex.reLm.isLinear _)
 rw [←SatinJets.branch_eq_heat S u (p.trans_le h),← SatinJets.branch_eq_heat S v (p.trans_le q),← Real.norm_eq_abs,← Complex.norm_real,Complex.ofReal_sub]
 exact g.norm_image_sub_le_of_norm_deriv_le (f:=S.F) (fun z e=>(S.localHeat _ (p.trans_le e)).differentiableAt) (fun _=>soften S b p) (x:= (v:ℂ)) (y:=(u:ℂ)) q h
end
variable (P:Spine)(x:P.Spectrum0 3)(j:Axis)
local notation "ξ"=> P.advocate 3 x j
local notation "G"=> P.ManyF j ξ
local notation "Γ"=> P.cartage j ξ
local notation "Θ"=> P.seasons j ξ
local notation "E"=> (Θ).E
local notation "κ"=> P.wealth j ξ
local notation "D" s:max=>P.lengthP s
local notation "Xρ" s:max=> P.basePlay x (P.pointEra s) s

local notation "Lk" s:max l:max=>P.lightKet x j s l

variable (J:P.Ellis 3 x){b:ℝ}(s:ℕ)(l g: List Axis)
lemma beam_join {H:Hilbert}{k:Axis}(S:OS.Semigroup H k)(a v:ℝ≥0)(X Y:H):
 inner ℂ (S.E a X) (S.E v Y)=inner ℂ X (S.E (a+v) Y):=by rw [S.swing,S.time]; rfl
lemma joined (v:Vantage)(a:ℝ≥0)(A B:G):
 inner ℂ (E a A) (Γ v (E a B))=inner ℂ A (E (a+a) (Γ v B)):= by rw [← P.warm_drive,beam_join] -- args
include J
lemma sparkle_up (p:Vantage)(h:P.faceWidth s < b)(t:b ≤ p j/2):
 P.sparkle x s l g p=
   inner ℂ ((Lk s (j::l)) b) (E ((D s)*(p j-2*b)).toNNReal (Γ ((D s) • p) ((Lk s g) b))):= by
 rw [P.sparkle_plus x j J s l g p (h.trans_le t),P.lamplight x j s _ h.le t, P.lamplight x j s g h.le t,P.joined]

 let a:=(D s)*(p j/2-b)
 rw [show (D s)*(p j-2*b)=a+a from (by unfold a;ring), Real.toNNReal_add (show 0 ≤ a from mul_nonneg (P.lengthP_pos _|>.le) (sub_nonneg.mpr t)) (show 0≤a from mul_nonneg (P.lengthP_pos _|>.le) (sub_nonneg.mpr t))]
omit J in
lemma cart_j (p q:Vantage)(h:∀k,k≠j→p k=q k): Γ p=Γ q:= by
 unfold cartage; congr 1; exact funext fun k:Trans j=>h _ k.property

lemma sparkle_lip (p q:Vantage)(h:P.faceWidth s < b)(t:3*b < p j)(v:3*b < q j)(d:∀k,k≠j→p k=q k)(e:0<b):
 dist (P.sparkle x s l g p) (P.sparkle x s l g q) ≤
   (‖(Lk s (j::l)) b‖*(2/b)*‖(Lk s g) b‖)*|p j - q j|:= by
 rw [dist_eq_norm,P.sparkle_up x j J s l g p h (by linarith), P.sparkle_up x j J s l g q h (by linarith)]
 have hg:(Γ) ((D s) • q)=(Γ) ((D s) • p):= Eq.symm (P.cart_j x j _ _ (fun k n=> by simp only [Pi.smul_apply,d k n]))
 rw [hg,← inner_sub_right,←ContinuousLinearMap.sub_apply]
 refine (norm_inner_le_norm ..).trans ?_
 let y:= D s; have w:0<y:=P.lengthP_pos s; let X:=Lk s (j::l); let Y:= Lk s g
 have ht: ‖(Θ).E (y*(p j-2*b)).toNNReal - (Θ).E (y*(q j-2*b)).toNNReal‖ ≤ (2/b)*|p j - q j|:= by
    refine (soften_le Θ (mul_pos w e) (mul_le_mul_of_nonneg_left (by linarith) w.le) (mul_le_mul_of_nonneg_left (by linarith) w.le)).trans_eq ?_
    rw [←mul_sub,sub_sub_sub_cancel_right,abs_mul, abs_of_pos w]; field_simp

 rw [show _*‖(Lk s g) b‖*|p j-q j|=‖X b‖*((2/b*|p j-q j|)*‖Y b‖) from (by unfold X Y;ring)]
 apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
 exact (ContinuousLinearMap.le_opNorm ..).trans ((mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans_eq (by rw [P.cart_norm]))

variable {r:ℕ→ℕ} (H:P.Spots r x)(τ:Tendsto r atTop atTop)
include H τ
local notation "K" i:max=>P.sparkle x (r i) l g
lemma one_tattoo {ε t:ℝ}(w:0<t)(e:0<ε):
  ∃ b:ℝ,∃ N:Set ℝ,N∈𝓝 t ∧ 0<b ∧ (∀ h∈N,3*b<h) ∧
   (∀ᶠ i in atTop, P.faceWidth (r i)<b ∧∀ p q:Vantage, p j ∈N→ q j∈N→ (∀ k,k≠j→p k=q k) → dist ((K i) p) ((K i) q) ≤ ε) := by
 let b:=t/4; have hb:0<b:= div_pos w (by norm_num)
 obtain ⟨a,f,u⟩:=P.rough_bound x j H τ (j::l) hb
 obtain ⟨c,m,v⟩:=P.rough_bound x j H τ g hb
 let z:=a*(2/b)*c; have hp:0<z:=by unfold z; positivity
 let N:= Metric.ball t (ε/(2*z)) ∩ Set.Ioi (3*b)
 refine ⟨b,N,inter_mem (ball_mem_nhds _ (by positivity)) (Ioi_mem_nhds (show 3*b<t from by unfold b;linarith)),hb,fun _ h=>h.2,?_⟩

 filter_upwards [u,v,(P.face_t.comp τ).eventually (gt_mem_nhds hb)] with i A B q
 refine ⟨q,fun p k d y h=>?_⟩; refine (P.sparkle_lip x j J (r i) l g p k q d.2 y.2 h hb).trans ?_
 have h₁: |p j - k j|≤ ε/z:= by
    rw [← Real.dist_eq]
    refine (dist_triangle (p j) t (k j)).trans ?_
    rw [dist_comm t, show ε/z=ε/(2*z)+ε/(2*z) from by ring]
    exact add_le_add (mem_ball.mp d.1).le (mem_ball.mp y.1).le
 refine le_trans (b:=z*(ε/z)) ?_ (by rw [mul_div_cancel₀ _ hp.ne'])
 apply mul_le_mul _ h₁ (abs_nonneg _) hp.le
 exact mul_le_mul (mul_le_mul_of_nonneg_right (A b le_rfl) (by positivity)) (B b le_rfl) (norm_nonneg _) (by positivity)
lemma tattoo {ε t:ℝ}(w:t≠0)(e:0<ε):
 ∃ N:Set ℝ,N∈𝓝 t ∧
   (∀ᶠ i in atTop,∀ p q:Vantage, p j ∈N→ q j∈N→ (∀ k,k≠j→p k=q k) → dist ((K i) p) ((K i) q) ≤ ε) := by
 cases lt_or_gt_of_ne w with
 | inr h =>
   obtain ⟨b,N,h,_,_,p⟩:=P.one_tattoo x j J l g H τ h e; exact ⟨N,h,p.mono fun i h=>h.2⟩
 | inl h=>
   obtain ⟨b,N,h,q,y,t⟩:=P.one_tattoo x j J g l H τ (neg_pos.mpr h) e
   refine ⟨{w| -w∈N}, continuous_neg.continuousAt.preimage_mem_nhds h,?_⟩
   filter_upwards [t] with i u p₁ p₂ h₁ h₂ d; specialize h₁; specialize h₂
   rw [P.sparkle_minus x j J _ _ _ _ (u.1.trans (show b < (-p₁) j/2 from by rw [Pi.neg_apply]; linarith only [y _ h₁,q])), P.sparkle_minus x j J (r i) l g p₂ (u.1.trans (show b < (-p₂) j/2 from by rw [Pi.neg_apply]; linarith only [y _ h₂,q]))]
   exact u.2 _ _ h₁ h₂ (fun k h=>congrArg Neg.neg (d k h))

lemma parchment {y:Vantage} (h:∀ k,y k≠0){ε:ℝ}(e:0<ε):
 ∃ N∈𝓝 y, ∀ᶠ i in atTop,∀ p∈N,∀ q∈N,dist ((K i) p) ((K i) q)≤ ε:= by
 let F:= (Finset.univ: Finset Axis); let c:=ε/(F.card+1); have t:0<c:=by unfold c;positivity
 choose N a b using (fun k=> P.tattoo x k J l g H τ (h k) t)
 let M:=Set.univ.pi N
 refine ⟨M,set_pi_mem_nhds (Set.finite_univ) (fun k _=>a k),?_⟩
 filter_upwards [eventually_all.mpr b] with i v p p₀ q q₀
 suffices T:∀ d:Finset Axis,∀ r₀∈M,(∀ k,k∉d→p k=r₀ k)→ dist ((K i) p) ((K i) r₀) ≤ d.card*c by
    refine (T F q q₀ (fun k g=> (g (mem_univ k)).elim)).trans ?_
    unfold c; rw [←mul_div_assoc,div_le_iff₀ (by positivity : 0 < (F.card:ℝ)+1)]
    linarith
 intro d; induction d using Finset.induction_on with
 | empty =>
    intro r _ n; rw [show p=r from funext fun k=> n k (notMem_empty k),dist_self,card_empty,Nat.cast_zero,zero_mul]
 | @insert a d h ih =>
   intro y p' n
   let u:= Function.update y a (p a)

   have b:u∈M:=by
      intro k _
      by_cases w:k=a
      · subst k; rw [show u a=p a from Function.update_self ..]; exact p₀ a trivial
      rw [show u k=y k from Function.update_of_ne w ..]; exact p' k trivial
   have s:∀ k,k∉d → p k=u k:= by intro k U; unfold u; by_cases y:k=a; subst k; simp; rw [Function.update_of_ne y,n k (by simpa [y])]
   rw [Finset.card_insert_of_notMem h,Nat.cast_add_one,add_mul, one_mul]
   exact (dist_triangle _ ((K i) u) _).trans (
   add_le_add (ih u b s) (v a u y (b a trivial) (p' a trivial) (fun k u=>Function.update_of_ne u ..)))
