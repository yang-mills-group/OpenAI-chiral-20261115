import YM.CF.BPress.SheetCost
import YM.CF.BPress.Grid.Memorize
/-! V of eq:B-frames, built directly on the law of eq:B-mood. Keep `Keeps` on this purchase. L_f delay/numerical dyadic estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function MeasureTheory LocalH Lattice SU Mag Cube Grid Filter Branch Sheet
open scoped Topology BigOperators Classical Matrix
variable {s : Side} {T : Atlas} {y C Lf : ℝ}

structure Net (s : Side) (T : Atlas) (Lf y C C' : ℝ) (B : ℕ) where
 φ : Grid.Half.Flow s → HFrame s
 borel : Measurable φ
 leave : ∀ x o, o∈mesh (frameWidth Lf y).val → φ x o=x.2 o
 paid : Grid.Half.Keeps (frameWidth Lf y).val (rFrame Lf y) B φ
 rate : ∀ (m:ℝ)(U:Horiz s)(F:HFrame s), Flat U m → ((frameWidth Lf y).val:ℝ)^2*m ≤1 → arcFee 1 U (φ (U,F)) (C/(frameWidth Lf y).val)
 flat (a:HFrame s)(U : Horiz s) : (∀ x,T.passes y U x) → Flat (adjust a U) (C'*mA y)
 buys : ((frameWidth Lf y).val:ℝ)^2*(C'*mA y) ≤1

namespace Net
variable {C' : ℝ}{B : ℕ} (F : Net s T Lf y C C' B)
open Pressure
lemma wR_lt {W : GapSize} {X:Bands s (W.select y)} (v : Dyadic W Lf y X) : (frameWidth Lf y).val < s.val:=by have he:= v.fits; have hx:0<(frameWidth Lf y).val:=(frameWidth Lf y).property; omega
lemma w_late (p: 0<Lf): Tendsto (fun y:ℝ=> ((frameWidth Lf y).val:ℝ)) atTop atTop:=by
 refine tendsto_atTop_mono' _ ((frame_bounds p).mono fun y q=> q.1) ?_; simp_rw [div_eq_mul_inv]; apply Filter.Tendsto.const_mul_atTop p; apply tendsto_inv_nhdsGT_zero.comp; refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩; simpa using npl_temp.drop.sqrt; exact ((eventually_gt_atTop (0:ℝ)).mono fun y p=>Real.sqrt_pos.mpr (temp_pos p))
lemma radixR (p:0<Lf) : Tendsto (rFrame Lf) atTop atTop:=by
 refine tendsto_atTop.mpr fun a=>?_ ; filter_upwards [(w_late p).eventually_ge_atTop ((2:ℝ)^a)] with y v; simp only [frameWidth,PNat.pow_coe] at v; push_cast at v; exact (pow_le_pow_iff_right₀ (by norm_num : 1<(2:ℝ))).mp v -- tune
lemma mass_late (p:0<Lf)(h:0<C') : ∀ᶠ y in atTop, ((frameWidth Lf y).val:ℝ)^2 * (C'*mA y) ≤ 1:=by
 filter_upwards [frame_bounds p, eventually_gt_atTop (0:ℝ),((npl_power heigh_npl 2 (by decide)).const_mul (4*Lf^2*C')).drop.eventually (ge_mem_nhds zero_lt_one)] with y v t l; have hm:=mA_pos t; have hv : 0 < temp y:=temp_pos t; have ht : mA y = temp y * (heigh y)⁻¹^2:=by rw [temp_price t,mA_price t]; have hx:=heigh_pos y; field_simp
 refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) v.2.le _) (by positivity : 0≤C'*mA y)).trans (le_trans ?_ l); rw [ht, mul_pow,div_pow,Real.sq_sqrt hv.le]; field_simp; ring_nf; rfl -- tune
lemma purchase (T:Atlas) : ∃ C C' : ℝ, 0<C∧0<C'∧ ∃ B:ℕ, ∀ L:ℝ, 0<L→∀ᶠ y:ℝ in atTop, ∀ (W:GapSize)(s:Side)(X:Bands s (W.select y)), Dyadic W L y X→ Nonempty (Net s T L y C C' B):=by
 obtain ⟨l,b,C,h,H⟩:= Half.frames; obtain ⟨K,g,G⟩:= T.horizon; refine ⟨C,K,h,g,b,?_⟩; intro L q; filter_upwards [(radixR q).eventually_ge_atTop l,mass_late q g,eventually_gt_atTop (0:ℝ)] with y p k a W s X P
 have ht:(frameWidth L y).val=2^(rFrame L y):=by simp [frameWidth]
 obtain ⟨φ,h,f,x,A⟩:= H s (rFrame L y) p (ht ▸ P.frame) (ht ▸ wR_lt P); rw [←ht] at x f A; exact ⟨⟨φ,h,f,x,A,G s y a,k⟩⟩

def frame (U : Horiz s)(h : HFrame s): HFrame s:= F.φ (adjust h U,1)*h
lemma frame_meas : Measurable (fun x:Horiz s × HFrame s=> F.frame x.1 x.2):= Measurable.mul (F.borel.comp ((adj_cont.measurable.comp measurable_swap).prodMk measurable_const)) measurable_snd -- tune
lemma frame_left (U : Horiz s)(a h:HFrame s) : F.frame (adjust a U) (h*a⁻¹)=F.frame U h*a⁻¹:=by unfold frame; rw [adjust_seq, inv_mul_cancel_right,mul_assoc]
lemma frame_small {U : Horiz s}(h : HFrame s)(p : ∀ x,T.passes y U x)(i : FlatLink s) : group.chord (adjust (F.frame U h) U i) ≤ C/(frameWidth Lf y).val:=by
 let q:=adjust h U; have ht:= F.rate (C'*mA y) q 1 (F.flat h U p) F.buys; rcases i with ⟨x,i⟩; rw [frame,← adjust_seq]; specialize ht x (by simp [Grid.mesh,aligned]) i; rw [line_one] at ht; exact ht
-- Keep reads even without acceptance. Not using any link gauge choices besides h,U here. Frame label computations of h evaluated as functions of discrete parameters use additional plaquette reads, priced later by halo.
lemma frame_pays (S : Finset (Tri s))(p : Grove (field 3 s) S): ∃ A, Grove (field 3 s) A ∧ S⊆A ∧ A⊆ broad (field 3 s) S (B*(frameWidth Lf y).val) ∧ A.card≤ B*((frameWidth Lf y).val+(rFrame Lf y+1)*S.card) ∧
    ∀ (U V: Horiz s) (h q : HFrame s), equalOn U V A→ Set.EqOn h q A→ Set.EqOn (F.frame U h) (F.frame V q) S:=by
 obtain ⟨A,v,t,u,a,b⟩:= F.paid.memo S p; refine ⟨A,v,t,u,a, fun U V h q w p x hx=>?_⟩; unfold frame; simp only [Pi.mul_apply]; rw [p (t hx)]; apply congrArg₂ (·*·) _ rfl -- tune rw rewrites both h?
 refine b (adjust h U,1) (adjust q V,1) (fun i c d=> ?_) (fun _ _=> rfl) hx; dsimp; unfold adjust; rw [p c,p d,w i c d]
end Net
end YM.CF.BPress
