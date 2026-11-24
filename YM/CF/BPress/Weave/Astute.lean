import YM.CF.BPress.Weave.Dusk
/-! PL purchasing in y. Receipts before terminal x. Note p from Clip d fixed at actual top. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Weave
open Function Filter Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Branch Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
open SU Gauge
attribute [local instance] Gauge.frobInner
structure Budget where
 n : ℝ→ℕ
 p : ℝ→ℝ
 low : ℝ→ℝ
 upper : ℝ
 reach : ℝ→ℕ
 chunks : ℝ→ℕ
 heightClose : ℝ→ℕ
 p_PL : PL p
 n_PL : PL (fun i=>(n i:ℝ))
 pLow : ∀ᶠ i in atTop, 0 < low i ∧ low i≤ upper
 ipLow : PL fun i=>(low i)⁻¹
 r_PL : PL (fun i=>(reach i:ℝ))
 c_PL : PL (fun i=>(chunks i:ℝ))
 h_PL : PL (fun i=>(heightClose i:ℝ))
namespace Budget
variable (P:Budget)(y:ℝ)(D:ℕ)
def γ:= grassRate (P.chunks y * P.reach y)
def jrate:= P.γ y/2
def choose_c:=grainSelect D (P.reach y) (P.chunks y)
def jcostB := 2*geoBill D (P.γ y) (P.choose_c y D)
def jq:=stipendJ (P.heightClose y) (P.jrate y) (P.jcostB y D)
def ShortJ:=NPL fun y=> P.jq y D
def flank:= P.upper⁻¹ * P.choose_c y D
def fore:= grainFee D (P.reach y) * P.upper
lemma gg : ∀ y,0<P.γ y:= fun y=> gr_pos _
lemma buy_size :PL (fun i=> ((P.chunks i*P.reach i:ℕ):ℝ)):=by simp only [Nat.cast_mul]; exact P.c_PL.mul P.r_PL
lemma buy_ig : PL (fun i=> (P.γ i)⁻¹):= gr_PL _ P.buy_size
lemma buy_ctc : PL (fun i=>P.choose_c i D):= ((PL.const 2).mul P.c_PL).mul (grain_PL D _ P.buy_size)
lemma buy_for : PL (fun i=> P.fore i D):= (grain_PL D _ P.r_PL).mul (PL.const _)
lemma buy_fla : PL (fun i=>P.flank i D):=(PL.const _).mul (P.buy_ctc D)
lemma half_pl {p:ℝ→ℝ}(h:PL fun i=>(p i)⁻¹) : PL fun i=>(p i/2)⁻¹:=by simp_rw [inv_div,div_eq_mul_inv]; exact (PL.const 2).mul h
lemma buy_jcost : PL (fun i=>P.jcostB i D):= (PL.const 2).mul (((P.buy_ctc D).mul (PL.const (n_ang D:ℝ))).mul (pl_harm 3 _ _ (half_pl P.buy_ig) (PL.const 4)))
variable {s:Side}{B:BandWidth}(X:Bands s B)(R:PathData group)(d:Clip)(M:ℕ)(β:ℝ){σ C Λ:ℝ}(H:R.Bounds d σ C Λ)
def flies (S:Finset X.Hcols):= flying X (P.p y) (P.n y) M R d β y H S
structure Ready (M:ℕ) :Prop where
 poly (S): Poly X S (wave X M R d β y H S) (P.flies y X R d M β H S) (P.low y) P.upper (y⁻¹^2)
 summer : Summer X (P.flies y X R d M β H) P.upper (P.low y) (P.reach y) (P.chunks y)
lemma buy_jac (h: P.Ready y X R d β H M) : ∃ A b, JacData X (P.flies y X R d M β H) A b (P.jrate y) (P.jcostB y B.D):= h.summer.j_cost
end Budget

variable (G:GapSize)(d:Clip)(C σ:ℝ)(M:ℝ→ℕ)
abbrev dimensional : ℕ:= G.blank.val+2*G.collar
def wideSeason (P:Budget) (y:ℝ): Prop:= ∀ (s:Side) (X:Bands s (G.select y)) (R:PathData group) (Λ β:ℝ)(H:R.Bounds d σ C Λ), High (G.select y) (M y) → β∈Set.Icc (y/2) (2*y) → P.Ready y X R d β H (M y)
lemma purchaseB (h:PL (fun i=>(M i:ℝ))) : ∃ (P:Budget), (P.ShortJ (dimensional G)) ∧ ∀ᶠ y in atTop, wideSeason G d C σ M P y:=by
 let D:=dimensional G; let p(y):= payUpper d (M y) D C; let a:=massL (G.select 1) d; have h₁:= mass_pos d (G.select 1); let u:=peak a; let l:=fun i=> peak (p i); have he:PL p:=upper_PL d D _ h; have hv(i):1≤p i:= by unfold p payUpper; apply le_add_of_nonneg_right; positivity [d.quadratic_pos,chPrice_pos]
 have H:PL fun i=>(l i)⁻¹:= ip_PL p he (Eventually.of_forall hv); have hA:0<a:=h₁; have hu:0<u:= inv_pos.mpr (Real.sqrt_pos.mpr hA); obtain ⟨n,Hn,hn⟩:= fullseat p a he (Eventually.of_forall hv) hA; let r(i):= n i*(6*M i); have hr:PL fun i=>(r i:ℝ):=by unfold r; push_cast; exact Hn.mul ((PL.const 6).mul h)
 have hl(i:ℝ):0<l i∧ l i≤u:= by have hp:= zero_lt_one.trans_le (hv i); have hx:=Real.sqrt_pos.mpr hp; exact ⟨inv_pos.mpr hx, inv_anti₀ (Real.sqrt_pos.mpr hA) (Real.sqrt_le_sqrt (le_trans (min_le_left ..) (hv i)))⟩
 obtain ⟨k,Hk,hk⟩:= buy_chunks r l u hr H hu (Eventually.of_forall fun i=>(hl i).1) D
 let P: Budget:= ⟨n,p,l,u,r,k,(fun _=>1),he,Hn,Eventually.of_forall hl,H,hr,Hk,by push_cast; exact PL.const _⟩; obtain ⟨x,Q,q⟩:=k_bill (P.jrate) (fun i=>P.jcostB i D) (Eventually.of_forall fun t=>half_pos (P.gg t)) (Budget.half_pl P.buy_ig) (P.buy_jcost D); let U:Budget:={P with heightClose:=x,h_PL:=Q}; refine ⟨U,q,?_⟩; filter_upwards [eventually_gt_atTop (0:ℝ),hk,hn] with y p' u' i; intro s X R Λ β HH e g; have hT(i':Finset X.Hcols):= flight X (p y) (n y) (M y) R d β y HH p' e g a le_rfl le_rfl (hv y) hA i i'; exact ⟨hT,⟨(hl y).1,(hl y).2,fun i'=>(hT i').lid.self,fun i'=>(hT i').bound,purchased X (p y) (n y) (M y) R d β y HH e,u'.2,u'.1⟩⟩ -- tune
end YM.CF.BPress.Weave
#print axioms YM.CF.BPress.Weave.purchaseB
#print axioms YM.CF.BPress.Weave.JacData.bill_long
#print axioms YM.CF.BPress.Weave.Budget.buy_jac
