import YM.CF.BProof.Angular.Open

/-! Ball densities used in eq:B-ang-M. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular
open Function Lattice Gauge Mag CF.BProof.Face SU MeasureTheory Wilson Finset Filter
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
local notation "G" => SU.group
variable {s : Side} (a x : Per s)(l:ℕ)(y:ℝ)(S:Hall s)(U:Config G s)

/-- Price all links of marked Dirichlet band. -/
def starts (i:Axis) := Fin.cases (motive:=fun _=> E) 1 (bg y) i
def mag (b:Bond s) := starts y b.2
@[simp] lemma mag_h (p: Space s)(i:TAxis) : mag y (horiz x p i)=bg y i:=rfl
@[simp] lemma mag_v (p:Space s) : mag y (vert x p)=1:=rfl

def washes := univ.filter (Wet a l)
def shut := ∏ b∈ washes a l,density G (xi y) (mag y b) (U b)
def Loud (b:Bond s) := if b.2=0 then along a (time b.1)=cut l else along a (time b.1)≠0 ∧ along a (time b.1)≠l
def watches := (washes a l).filter (Loud a l)
@[simp] lemma mem_wash (b:Bond s): b∈washes a l↔Wet a l b:= by simp [washes]
@[simp] lemma mem_watch (b:Bond s): b∈watches a l↔Wet a l b∧Loud a l b:= by simp [watches]
lemma watch_h (p:Space s)(i:TAxis) : horiz x p i∈watches a l ↔ 0<along a x∧along a x<l:=by rw [mem_watch,wet_h]; unfold Loud horiz; simp only [Fin.succ_ne_zero,↓reduceIte,time_join]; omega
lemma watch_v (p:Space s)(hl:0<l)(he:l+1<s.val) : vert x p∈watches a l ↔ along a x=cut l:=by
 rw [mem_watch,wet_v a _ he]; unfold Loud vert; simp only [↓reduceIte,time_join]; exact and_iff_right_of_imp fun h=> h ▸ cut_lt l hl -- tune

variable (b:Eyes s)
/-- Multiply N density (cut plus all marked interior horizontal links). -/
def stream := ∏ p∈watches a l,density G (xi y) (formal a l S U b p) (hall a l S U b p)
lemma stream_local (he:l+1<s.val)(W:Config G s)(h:Agrees (↑(strip a l)) U W) : stream a l y S U b=stream a l y S W b:=by
 rw [stream,stream,formal_local a _ S U b (by omega) W h]; apply prod_congr rfl; intro p hp; obtain ⟨hp,hq⟩:= ((mem_watch ..).1 hp).1; rw [hall_local a _ S U b he W h p hp hq]
lemma stream_rot (t): stream a l y S (Lattice.gauge t U) (b*(eye a l t)⁻¹) = stream a l y S U b:=by unfold stream; rw [formal_rot,hall_rot]
lemma shut_local : LocalOn (↑(strip a l)) (shut a l y):=by intro U V h; apply prod_congr rfl; intro p hp; obtain ⟨hp,hq⟩ := (mem_wash ..).1 hp; rw [h _ hp hq]
lemma pay_watch (hl:l<s.val): (watches a l).card≤ (l+1)*s.val^3*4:=by
 apply (card_le_card (filter_subset (Loud a l) (washes ..))).trans; apply (card_le_card (t:=strip a l×ˢ(univ: Finset Axis)) (fun x hx=> mem_product.mpr ⟨((mem_wash ..).1 hx).1,mem_univ _⟩)).trans; simp [Axis,strip_card _ hl]
lemma pay_density (T:Finset (Bond s))(k j:Config G s)(he:T⊆washes a l)(hx:xi y≤1)(hl:l<s.val) :
    let f:=∏ p∈T,density G (xi y) (k p) (j p); 0≤f ∧ f≤ ((4/xi y)^matDim G)^((l+1)*s.val^3*4) := by
 have hh:(washes a l).card≤ (l+1)*s.val^3*4:=by
    apply (card_le_card (t:=strip a l×ˢ(univ: Finset Axis)) (fun x hx=> mem_product.mpr ⟨((mem_wash ..).1 hx).1,mem_univ _⟩)).trans; simp [Axis,strip_card _ hl]
 have h:0<xi y:=coin_pos ..
 refine ⟨prod_nonneg (fun p hp=>(density_pay G _ _ h hx).1),?_⟩ -- tune dots
 apply le_trans (b:=∏ _∈ T,((4/xi y)^matDim G)) (prod_le_prod (fun p hp=>(density_pay G _ _ h hx).1) (fun p hp=>(density_pay G _ _ h hx).2)); rw [prod_const]; exact pow_le_pow_right₀ (one_le_pow₀ ((le_div_iff₀ h).2 (by linarith))) ((card_le_card he).trans hh)

lemma awake (e t : E) : density G (xi y) e t≠0→cd G e t≤xi y:=by contrapose!; intro h; rw [density_apply,if_neg h.not_ge]
lemma shut_pays (H:shut a l y U≠0)(p:Bond s)(hp:Wet a l p) : cd G (mag y p) (U p)≤xi y:= by
 apply awake y; intro h; exact H (Finset.prod_eq_zero ((mem_wash ..).mpr hp) h)
lemma stream_pays (H:stream a l y S U b≠0)(p:Bond s)(hp:p∈watches a l): cd G (formal a l S U b p) (hall a l S U b p)≤xi y:= by apply awake y; intro h; exact H (Finset.prod_eq_zero hp h)

lemma shut_m : Measurable (shut a l y):=Finset.measurable_prod (washes a l) fun p hp=> (density_c G _).comp (f:=fun U : Config G s=>(mag y p,U p)) (by fun_prop)
lemma stream_m : Measurable (Function.uncurry (stream a l y S)):=by
 have e(X : Config G s→Eyes s→ Config G s)(hX:Measurable (Function.uncurry X))(p:Bond s): Measurable (fun v : Config G s × Eyes s=> (X v.1 v.2 : Config G s) p):= (measurable_pi_apply (X:=fun _ : Bond s=>E) p).comp hX -- tune meta
 unfold Function.uncurry stream; refine Finset.measurable_prod (watches a l) ?_; intro p hp; exact (density_c G (xi y)).comp (f:=fun v : Config G s × Eyes s=>(formal a l S v.1 v.2 p,hall a l S v.1 v.2 p)) ((e _ (formal_m a l S) p).prodMk (e _ (hall_m a l S) p))
end YM.CF.BProof.Angular
