import YM.CF.Phase.Pot

/-! Exact extensive scalar, in native support terms, and candidates for assigning it. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Sample
open Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} {e : ℝ}
def sideS (z:ℂ) : ℂ := ↑z.im * Complex.I
lemma side_cont : Continuous sideS := by unfold sideS; fun_prop
lemma side_n (z : ℂ) : ‖sideS z‖≤ ‖z‖ := by simp only [sideS,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]; exact Complex.abs_im_le_norm _
lemma side_sum {I : Type*} (s : Finset I) (f : I→ℂ) : ∑ i∈s, sideS (f i)=sideS (∑ i∈s,f i) := by simp only [sideS,←sum_mul,Complex.ofReal_sum,Complex.im_sum]
lemma dim_sum {I : Type*} (s : Finset I) (f : I→ℂ) : ∑ i∈s, hsun (f i)=hsun (∑ i∈s,f i) := by simp only [hsun,Complex.ofReal_div,←Complex.ofReal_sum,Complex.ofReal_ofNat, ←sum_div,Complex.re_sum] -- tune
def faresF (m B : Side) (f g : Post m B→ℂ) (v : Hub m) (x : Pack m B) := dimP m B f v x+sideS (coastal m B (inks m B g v) x)
def gains (B : Side) (r s : ℝ) := r+(way B:ℝ)*s
structure SealX (m B : Side) (v : Hub m) (S : Stamp m B) (f : Pack m B→ℂ) (c e : ℝ) : Prop where
  cont : ContinuousOn f (payer m B e)
  pos : 0≤c
  norm (x) (k:x∈payer m B e) : ‖f x‖≤c
  gaugeEq (t) (g) (k:t∈payer m B e) : f (Lattice.gauge g t.1,partner m B g t.2)=f t
  connect : c≠0→ Grove (terr _) S
  matched (x y) (p:sanctioned m B S v) (g:x∈payer m B e) (l:y∈payer m B e) (K : AgreeF (chairs m B S) x.2 y.2)
    (h : Agrees (window m B S v) x.1 y.1) : f x=f y
lemma collapse {S : Stamp m B} {f g : Post m B→ℂ} {w K : ℝ} (p:Eck m B S w f) (v : Eck m B S K g) (a : Hub m) (b : Room B e) :
    SealX m B a S (faresF m B f g a) (gains B w K) e := by
  have he := irradiates v b a; have hm := darkL b a f p.continuousE
  let f₁ := dimP m B f a; let f₂ := coastal m B (inks m B g a)
  have C₀ : ContinuousOn f₂ (payer m B e) := he.coastalC
  have hl : ContinuousOn (faresF m B f g a) (payer m B e) := by
    change ContinuousOn (fun x=> f₁ x + (sideS ∘ f₂) x) _; exact (show ContinuousOn f₁ _ from hm).add (side_cont.comp_continuousOn C₀)
  refine ⟨hl, add_nonneg p.posT (mul_nonneg (Nat.cast_nonneg _) v.posT),fun x hx=> ?_,fun x t hx=>?_,fun c=>?_,fun x y H h l A V=>?_⟩
  · exact (norm_add_le ..).trans (add_le_add (dark_size p b hx a) ((side_n _).trans (he.portC _ hx)))
  · unfold faresF; rw [dark_g p b a hx t, he.gauged t x hx (fun _ _ H=>light_g v b a H t)]
  · by_cases h:w=0
    · apply v.conduct; rw [gains,h,zero_add] at c; exact right_ne_zero_of_mul c
    exact p.conduct h
  unfold faresF; rw [dark_local p b a H h l A V]; apply congrArg (fun u:ℂ=> dimP m B f a y + u)
  apply congrArg sideS
  refine voyage_eq he x y h l (chairs m B S) (nested_ch S) (fun i g=> fun k e₁ e₂=> V k (near_wire a i g H e₁) (near_wire a i g H e₂)) A ?_; intro x₁ x₂ y₁ y₂ u v' p₁ p₂
  -- requires y carry valid ZeroF? Arch symmetry ensures inherited via p.2 relation
  exact light_local v b a H (x:=((x,x₁),y₁)) (y:=((y,x₂),y₂)) ⟨⟨h,inherited p₁.2⟩, p₁⟩ ⟨⟨l,inherited p₂.2⟩,p₂⟩ u v' A V
-- sizes
variable (m B)
structure Scroll (c : Part m B) where
  hull : Stamp m B→ Post m B→ℂ
  phi : Stamp m B→ Post m B→ℂ
  dull : Stamp m B→ℝ
  din : Stamp m B→ℝ
variable {m B}
abbrev codify (c:Part m B) : IndexK := ⟨CSide m B,c⟩
structure ScaleK (a J : ℝ) {c : Part m B} (W : Scroll m B c) : Prop where
  t1 : Spends (slotK _) W.hull W.dull a J
  t2 : Spends (slotK _) W.phi W.din a J
  h1 x : Matrix.trace (tollX (codify (m:=m) (B:=B) c) x)=∑ S:Stamp m B,W.hull S x
  h2 x : Matrix.trace (billX (codify (m:=m) (B:=B) c) x)=∑ S:Stamp m B,W.phi S x
lemma SpendP {I Y D G : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y] [TopologicalSpace D] {L : Stage Y I D G} {F : Seal Y→D→ℂ} {K : Seal Y→ℝ} {a b p q : ℝ} (h : Spends L F K a b) (g : p≤a) (u : b ≤ q) : Spends L F K p q := by
  refine ⟨h.stamped,fun z=>?_⟩
  apply le_trans _ ((h.payline z).trans u); exact sum_le_sum fun i _=> mul_le_mul_of_nonneg_right (rent_up g i) (h.stamped i).posT
lemma composeK : ∃ a J : ℝ, 0<a ∧ 0<J ∧ ∀ (m B : Side) (c : Part m B),∃ W : Scroll m B c, ScaleK a J W := by
  obtain ⟨a,K,p₁,p₂,H⟩ := tours _ amp honored; obtain ⟨d,U,l₁,l₂,h⟩ := tours _ amp accorded
  refine ⟨min a d,max K U,lt_min p₁ l₁,lt_max_of_lt_right l₂,fun m B c=>?_⟩
  obtain ⟨F,k,p,v⟩ := H (codify (m:=m) (B:=B) c); obtain ⟨t,j,e,Y⟩ := h (codify (m:=m) (B:=B) c)
  exact ⟨⟨F,t,k,j⟩,SpendP p (min_le_left ..) (le_max_left ..),SpendP e (min_le_right ..) (le_max_right ..), v,Y⟩
def Scroll.value {c : Part m B} (W : Scroll m B c) S := faresF m B (W.hull S) (W.phi S)
def Scroll.mint {c : Part m B} (W : Scroll m B c) S := gains B (W.dull S) (W.din S)
variable {c : Part m B} {A d : ℝ} {W : Scroll m B c}
lemma currency (h : ScaleK A d W) (b : Room B e) (S : Stamp m B) (a : Hub m) : SealX m B a S (W.value S a) (W.mint S) e := collapse (h.t1.stamped S) (h.t2.stamped S) a b
lemma Scroll.covers (h : ScaleK A d W) (x) : hitE A W.mint x ≤ d+(way B:ℝ)*d := by
  let t := (way B:ℝ)
  unfold hitE mint gains; simp only [mul_add,sum_add_distrib];
  apply add_le_add (h.t1.payline x)
  simp_rw [mul_left_comm _ (way B:ℝ), ←mul_sum]; exact mul_le_mul_of_nonneg_left (h.t2.payline x) (Nat.cast_nonneg _)
lemma river (h : ScaleK A d W) (b : Room B e) {t:Tide m B} (g:t∈checked m B e) : ∑ S:Stamp m B, inks m B (W.phi S) none t=bill m B c t.1.1.1 t.1.2 t.1.1.2 t.2 := by
  let x := t.1.1.2; let y := t.2; let l := t.1.2; let U := t.1.1.1
  have H : Guard U e := g.1.1.1
  have he (x) (k:EdgeP m B U x y) (i) (p:i<way B) : ∑ S:Stamp m B, glow m B (W.phi S) none U x y i=rad m B c U (twin m x y) (stick 0) (stick 1) i := by
    let T : Post m B := ⟨_,gear0 b none H k i p⟩; unfold glow; simp_rw [entrance (f:=_) (gear0 b none H k i p),←sum_div]; rw [←h.h2 T]; unfold rad spark; rw [bille]; rfl
  simp only [inks]; rw [sum_comm,bill,amount,amount,ray,ray,←sum_sub_distrib]; apply sum_congr rfl; intro i hi; rw [sum_sub_distrib,he _ g.2.2 i (mem_range.mp hi),he _ g.2.1 i (mem_range.mp hi)]
lemma taxed (h : ScaleK A d W) (b : Room B e) {x :Pack m B} (g:x∈payer m B e) : ∑ S:Stamp m B,W.value S none x=fund m B c x.1 x.2 := by
  simp only [Scroll.value,faresF,sum_add_distrib,side_sum]; unfold fund; apply congrArg₂ (· + ·)
  · let T : Post m B := ⟨_,dark0 b none g⟩; unfold dimP; simp_rw [entrance (f:=_) (dark0 b none g)]; rw [dim_sum, ←h.h1 T,wallet]; rfl
  rw [←freighted x g univ _ _ (fun S _=> irradiates (h.t2.stamped S) b none)]; rw [returns c b g (fun i=>_) (fun z q=>river h b q)]; rfl
end YM.CF.Phase
