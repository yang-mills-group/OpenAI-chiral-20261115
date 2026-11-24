import YM.CF.Drapes.Open
set_option autoImplicit false
noncomputable section
namespace YM.CF.Drapes
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Filter Branch
attribute [local instance] opCStarAlgebra
variable {I Y D E G : Type*} [Fintype I][Fintype Y][DecidableEq I][DecidableEq Y] [TopologicalSpace D][TopologicalSpace E]
structure Towards (b:Stage Y I D G)(L:License D)(b':Stage Y I E G)(L': License E)(ρ: E→D)(e:ℝ):Prop where
  cont : Continuous ρ
  home : b'.home=b.home
  field : b'.F=b.F
  drive g x : ρ (b'.drive g x)=b.drive g (ρ x)
  restr (S:Seal Y) (x y) : b.eval S (ρ x) (ρ y)≤e*b'.eval S x y
  sustain (f:D→ℂ): L.valid f→ L'.valid (fun x=> f (ρ x))
variable {b:Stage Y I D G} {b':Stage Y I E G} {L:License D}{L':License E}{ρ:E→D}{e a r c m : ℝ}
namespace Towards
variable (T : Towards b L b' L' ρ e) {A:Raw D I}{s t:Tag b} {s' t':Tag b'}
include T
lemma suite {S C} (hS:s.run=s'.run)(hT:t.run=t'.run)(h:Suite L s t S C A)(he:e≤1): Suite L' s' t' S C (A ∘ ρ):=by
  refine ⟨⟨fun g x=>?_,fun i j=>?_⟩,fun i j=>T.sustain _ (h.fuel i j)⟩
  · simp only [comp_apply,← hS,← hT,T.drive]; exact h.frame ..
  refine ⟨h.nonn i j,fun e=> by rw [T.field,T.home]; exact (h.expo i j).triggered e,fun x=> (h.expo i j).bounded _, fun x y=> (h.expo i j|>.variation ..).trans (mul_le_mul_of_nonneg_left ((T.restr ..).trans (mul_le_of_le_one_left (b'.pos ..) he)) (h.nonn i j)), ((h.expo i j).connected.comp T.cont)⟩
lemma bring (hS:s.run=s'.run)(hT:t.run=t'.run)(h:Crown L s t a r A)(he:e≤1): Crown L' s' t' a r (A ∘ ρ) :=by
  obtain ⟨F,C,p,q,l⟩:=h; exact ⟨_,_,fun i=>T.suite hS hT (p i) he,q,fun x=> by simp only [comp_apply]; rw [l]⟩
-- evaluate trunc norm via cage at aligned input. witness per y. volume cost. re-emission directional gains.
lemma dusk (P : Seal Y → Raw D I)(V : Seal Y→ Toll I) (hn:∀ S, Suite L s t S (V S) (P S))(q:Ledger a V r)(u:Capacity b' c)(hc:0≤c)(ha:0≤a)(X: D)(w:ℕ)(hs : A X=∑ S,P S X)(he:e≤1)(hS:s.run=s'.run)(hT:t.run=t'.run)(y:ℝ)(hy:0≤y)(x:ℝ)(hx:0≤x)(ht:‖A X‖ ≤ x)
    (H : ∀ d i,∃ g:G, b.eval (bay b.F (b.home i) (w+w)) (b.drive g (ρ d)) X≤y) (ho: 0≤m):
    let B := (lop P w); let U := c*(((((w+w):ℕ):ℝ)+1)^4); let Y := x+(Real.exp (-a/2*w)*r)+r*(y+|e|)
    Crown L' s' t' m (U * Real.exp (m*U) * Y) (B ∘ ρ):=by
  intro B U W; let K:=B ∘ ρ
  have HB:= Crown.short P V (v:=w) hn q
  have HK : Crown L' s' t' a r K:= T.bring hS hT HB he
  let A0(d:D) :=∑ S,P S d
  have hm: Crown L s t (a/2) (Real.exp (-a/2*w)*r) (fun x=> A0 x-B x):= Crown.tail P V hn q (fun _=>rfl) ha
  have hp:= q.posP
  let δ:=Real.exp (-a/2*w)*r
  have hf:‖B X‖≤ x+δ :=by calc
     _ ≤ _:= norm_le_norm_sub_add _ (A0 X)
     _ ≤ δ+x:=add_le_add (by rw [norm_sub_rev]; exact hm.lib.boundOp (by linarith) X) (show ‖A0 X‖≤x from (by unfold A0; rw [← hs]; exact ht))
     _ = _:=add_comm ..
  have hl(d): FiniteOp b w (B d):=lop_rad P V (fun S=>(hn S).toTicket) d
  have hg(z):0≤ z → 0 ≤ Real.exp (-a/2*z) * r:=fun _=>by positivity
  have ha': Continuous B:=continuous_finsetSum _ (fun i _=>(hn i).toTicket.cont)
  have hR (d:E)(i j:I): b.F.span (b.home i) (b.home j) ≤ w→ ‖K d i j‖≤ W:=by
    intro hl
    let o:=b.home i; let S z:=strip b (bay b.F o z)
    obtain ⟨g,hu⟩:=H d i
    let x':= b.drive g (ρ d)
    let D₀(x:D):= cage b o w (B x)
    have hv : ∀ x, B x i j = D₀ x i j:=fun x=> by unfold D₀; rw [latched,if_pos ⟨by rw [show b.F.span o (b.home i)=0 from b.F.reflex _]; omega,hl⟩]
    have hz := HB.lib.tiesK.frame g (ρ d)
    have hm : D₀ x'=(s.run g).val*D₀ (ρ d) * star (t.run g).val:=by
      change S w*B (b.drive g (ρ d))*S w=_*(S w*_ *S w)*_
      change B (b.drive g (ρ d))=(s.run g).val*B (ρ d)*star (t.run g).val at hz; rw [hz]; simp only [← mul_assoc]; rw [strip_tag]; rw [mul_assoc _ (star (t.run g).val), ← strip_inv, ← mul_assoc]
    calc
      _ ≤ ‖D₀ (ρ d)‖ := by rw [show K d i j= _ from (hv (ρ d))]; exact norm_entry ..
      _ = ‖D₀ x'‖:=by rw [hm, show star (t.run g).val=(star (t.run g)).val from rfl, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
      _ ≤ ‖D₀ x'-D₀ X‖+‖D₀ X‖:=norm_le_norm_sub_add ..
      _ ≤ r*y+(x+δ):= add_le_add ((cage_lip P V (fun S=>(hn S).toTicket) q ha o x' X w w).trans (mul_le_mul_of_nonneg_left hu hp)) ((locker (X:=B) (lop P w X) o).trans hf)
      _ ≤ _:=by unfold W δ; linarith [mul_nonneg hp (abs_nonneg e)]
  refine Crown.sheet u hc ho HK.lib.tiesK (ha'.comp T.cont) (show 0 ≤ W by unfold W; positivity) _ HK.air (fun d=> ?_) (fun i j d=> ?_) ?_
  · intro i j l; rw [T.field,T.home] at l; exact hl _ i j (lt_of_le_of_lt (Nat.le_add_right w w) l)
  · by_cases hd:b.F.span (b.home i) (b.home j) ≤ w
    · exact hR d i j hd
    rw [show K d i j=0 from hl _ i j (lt_of_not_ge hd),norm_zero]; unfold W; positivity
  intro i j d d'
  by_cases h:b.F.span (b.home i) (b.home j)≤w; swap
  · rw [show K d i j=0 from hl _ _ _ (lt_of_not_ge h),show K d' i j=0 from hl _ _ _ (lt_of_not_ge h),sub_self,norm_zero]; exact mul_nonneg (by unfold W; positivity) (b'.pos ..)
  let J (d:D):=cage b (b.home i) w (B d)
  have hh(d:E): K d i j=J (ρ d) i j:=by unfold J; rw [latched,if_pos ⟨by rw [b.F.reflex]; omega,h⟩]; rfl
  rw [T.field,T.home]
  let l:=b'.eval (bay b.F (b.home i) (w+w)) d d'; have ht:=b'.pos (bay b.F (b.home i) (w+w)) d d'
  calc
    _ ≤ ‖J (ρ d)-J (ρ d')‖ := by
      rw [hh,hh d']; exact norm_entry (J (ρ d)-J (ρ d')) _ _
    _ ≤ r * (e*l):=(cage_lip P V (fun S=>(hn S).toTicket) q ha (b.home i) _ _ w w).trans (mul_le_mul_of_nonneg_left (T.restr _ _ _) hp)
    _ ≤ _ := by change r*(e*l) ≤ W*l; rw [← mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ ht; unfold W; nlinarith [mul_nonneg hp (Real.exp_pos (-a/2*w)).le,mul_nonneg hp hy,mul_le_mul_of_nonneg_left (le_abs_self e) hp]
end Towards
end YM.CF.Drapes
