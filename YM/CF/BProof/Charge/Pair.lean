import YM.CF.BProof.Charge.Atom

/-! Micro-supported terms of the omitted part of the kept row squares (pair indexed). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge
open Function Filter RG Wilson Lattice Finset Push.AbsoluteSums Work Micro Moment MeasureTheory Push.AbsoluteSums.Paths ConnectedActivityE6.Raw
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {s:Side} {G:Gauge} (c:Clip)(p:BudgetPoint)(T:PathData G)(M:ℕ)(σ: Signed)(β:ℝ)(U : Config G s){t W C Λ:ℝ}(a:PlaqAxes)

def ValidR := ∀ k : ℕ,p.threshold*Real.exp ((k:ℝ)/c.relaxation)<2→ k+2 ≤ M+2
abbrev Duo(s:Side):= Site s × (ℕ×ℕ)
def pairT(i:Duo s)(U:Config G s):ℝ:= β * pairTail T c M 1 p.threshold (i.1,a) (pull σ 0 U) i.2
def pairS(i:Duo s):ℝ:= |β| * pairPrice T M 1 a i.2
def pairF(i:Duo s):= move σ (pairFoot (M+2) T (i.1,a) i.2)
lemma pair_ne (i:Duo s): (pairF T M σ a i).Nonempty:=⟨spin σ i.1,moves σ (mem_union_left _ (halo_subset (M+2) _ (mem_singleton_self _)))⟩ -- tune
lemma pair_bound (i:Duo s): ‖pairT c p T M σ β a i U‖≤pairS T M β a i:=by rw [pairT,norm_mul,pairS,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (pair_le ..) (abs_nonneg _)
lemma pairG (i:Duo s)(g:Site s→G.El): pairT c p T M σ β a i (Lattice.gauge g U)=pairT c p T M σ β a i U := by
 unfold pairT; rw [F05.pull_gauge_zero]
 let x:=pull σ 0 U; let t(y:Site s):=g (affine σ 0 y); have hh : PathData.kept c p.threshold i.1 (Lattice.gauge t x)=PathData.kept c p.threshold i.1 x:=by unfold PathData.kept; simp only [face_gauge,G.chord_conj]
 let q:=G.adjoint (t i.1); have ht(n:ℕ):T.ellTerms (i.1,a) n (Lattice.gauge t x)=q (T.ellTerms (i.1,a) n x):=by unfold PathData.ellTerms; rw [F05.slot_gauge,map_smul]
 unfold pairTail; dsimp only; rw [hh]; split; rw [ht,ht]; let L : G.Color →ₗᵢ[ℝ] G.Color:=⟨q,G.norm_adjoint _⟩; exact congrArg (fun u:ℝ=>β*(u/2)) (L.inner_map_map _ _); rfl -- tune

abbrev pairRate (W:ℝ)(M:ℕ) := W/(8*(2*(M+2)+1:ℝ)^4)
def pairUnit (W C:ℝ)(M:ℕ) := (Real.exp (-(W/2*M)) *2)*Real.exp W*((2*(M+2)+1:ℝ)^4)*((W/4)⁻¹^4*(4:ℕ).factorial*Real.exp (W/4))*(C*C)
variable (h:T.Bounds c W C Λ)
include h
lemma pair_p (s:Side) : Toll (pairF (s:=s) T M σ a) (pairS T M β a) (pairRate W M) (|β| * pairUnit W C M) := by
 have hW:=h.width; let ε:=W/4; have he:0<ε:=by unfold ε; positivity
 let u(i:ℕ×ℕ):= length (duplex T a i); let f(i:ℕ×ℕ):=Real.exp (W/2*u i)*mate T a i
 have hh(i:ℕ×ℕ): f i*Real.exp (- (W/2*u i))=mate T a i:=by unfold f; rw [mul_comm (Real.exp _),mul_assoc,← Real.exp_add]; simp
 have hp:0≤C*C:=mul_self_nonneg _; have hv:SumBudget (fun i=>Real.exp (W/2*u i)*f i) (C*C):=by
    convert budget_prod (h.rows a) (h.rows a) using 1; ext1 i; unfold f u; rw [duplex_price, ← mul_assoc, ← Real.exp_add, show W/2*(↑((T.row a i.1).2.length+(T.row a i.2).2.length):ℝ)+W/2*_ = W*((↑((T.row a i.1).2.length+(T.row a i.2).2.length)):ℝ) from ?_]; -- tune term
    · unfold mate; push_cast; rw [mul_add, Real.exp_add]; ring
    push_cast; ring
 let D:=|β| * (Real.exp (- (W/2*M))*2); have hd:0≤D:=by unfold D; positivity
 have hr:0≤pairRate W M:=by unfold pairRate; positivity
 convert scan (pairF (s:=s) T M σ a) (equiv σ) (M+2) u (pairS T M β a) (fun i=> mul_nonneg (abs_nonneg β) (pairPrice_nonneg T M 1 a i.2)) (pairRate W M) he hp f hv hd (Real.exp_pos W).le (fun i=>?_) (fun i=> ?_) (fun i j p=> ?_) using 1 -- p absent from lemma body
 · unfold D ε pairUnit; push_cast; ring
 · unfold pairS pairPrice; split <;> rename_i H; swap; exact le_trans (Eq.le (mul_zero _)) (mul_nonneg hd (by unfold f mate; positivity))
   have hu:u i.2 ≥ M:=by unfold long at H; unfold u; rw [duplex_price]; simp only [mul_one] at H; omega
   rw [←hh]; unfold D; calc
     _ ≤ |β| * (2*(f i.2*Real.exp (- (W/2*M)))):=by gcongr; unfold f mate; positivity
     _ ≤ _:= Eq.le (by ring)
 · rw [pairF,move_card, ← Real.exp_add]; apply Real.exp_monotone
   apply le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (pair_card (i.1,a) T i.2 (M+2))) hr); change pairRate W M* (((2*(M+2)+1)^4+u i.2+3:ℕ):ℝ) ≤ _
   have ht:1≤(2*((M:ℝ)+2)+1)^4 := one_le_pow₀ (by linarith only [show 0≤(M:ℝ) by positivity])
   let k:= (2*((M:ℝ)+2)+1)^4; let v:ℝ:=u i.2; have hL:0≤v:=by unfold v; positivity
   unfold pairRate; push_cast; change W/(8*k)*(k+v+3)≤W+ (W/2-ε)*v; unfold ε
   apply le_trans (b:=W/(8*k)*k+W/8*(v+3)) _ _
   · have hb:W/(8*k)≤ W/8:=by gcongr; change 8≤8*k; nlinarith only [show 1≤k from ht]
     linarith only [mul_le_mul_of_nonneg_right hb (show 0≤v+3 by positivity)]
   have hb:W/(8*k)*k=W/8:=by have hz:0<k:=zero_lt_one.trans_le ht; field_simp
   rw [hb]; nlinarith
 obtain ⟨j,hj,rfl⟩:= mem_image.mp p; have hg:=pair_span (i.1,a) T i.2 (M+2) j hj; change separation (σ.act _) (σ.act _)≤_; rw [separation_signed,separation_comm]; unfold u; nlinarith [hg] -- tune

def pairBook (c:Clip)(p:BudgetPoint)(T:PathData G)(M:ℕ)(σ:Signed)(β:ℝ)(a:PlaqAxes){W C Λ:ℝ}(h:T.Bounds c W C Λ)(hk:ValidR c p M):Letters G s (Duo s) where
 foot:=pairF T M σ a
 map:= pairT c p T M σ β a
 size:=pairS T M β a
 spot:=pair_ne T M σ a
 loc i:=move_loc σ (pair_loc (i.1,a) T _ _)
 pushes i U V g:=congrArg (β*·) (pair_local _ _ M _ _ _ _ _ hk _ _ (agrees_turn σ _ _ _ g)) -- tune
 kept i t U:=pairG ..
 meas i:=measurable_const.mul ((pair_measurable ..).comp (continuous_pull σ (0:Site s)).measurable) -- tune
 weight i U:=pair_bound ..
 saved := ((pair_p c T M σ β a h s).total (S:=pairF T M σ a) (v:=pairS (s:=s) T M β a) (by have := h.width; unfold pairRate; positivity) (pair_ne T M σ a)).2.1 -- p reference from theorem
lemma pair_paid (k:ValidR c p M) : ((pairBook (s:=s) c p T M σ β a h k).charge).price U = β * ∑ x:Site s,tails T c M 1 p.threshold (x,a) (pull σ 0 U):=by
 let D:= pairBook (s:=s) c p T M σ β a h k; rw [Letters.recorded]; change (∑' i:Duo s,D.map i U)=_
 rw [(D.sum_point U).tsum_prod,tsum_fintype,mul_sum]; apply sum_congr rfl; intro x hx; exact ((pair_sum h M 1 p.threshold (x,a) (pull σ 0 U)).mul_left β).tsum_eq
end YM.CF.BProof.Charge
