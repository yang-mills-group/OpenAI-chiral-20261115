/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.AnalyticBridge.VERIFIED_RESET_STEP.Quadratic
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Local
/-!
 `D:Lips2`: W uses exactly the four based plaquette prices about a site
 in each coordinate plane; `colorScale_norm` in FiniteGaugeData conventions makes cH=4.
 Compute its Press/Medal and flux charges (thus not substituting an
 untransported path cost or the average clover curvature squared).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Compass
open StressFlux Function Filter Set Lattice Wilson RG UVNext.PricedKernels Next.Scheduling Work.F03 WilsonStartup
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
attribute [local instance] Gauge.frobInner
variable {G : Gauge}{n : Side}{p : BudgetPoint}

lemma cH (G : Gauge) (u : G.Simple) : 4*‖G.colorMat (spike G)‖^2/(G.repDim:ℝ)=4:=by
 rw [G.colorMat_norm,spike_norm u,mul_one,G.colorScale_sq]; apply mul_div_cancel_right₀; exact_mod_cast G.dimPos.ne'

def compass(U: Config G n)(o: Site n)(i j:Step):=G.price (travel U o (Lattice.oriented i j))
abbrev around(U:Config G n)(o:Site n)(i j:Axis):= ∑ a:Bool,∑ b:Bool, compass U o ⟨i,a⟩ ⟨j,b⟩
def W(o:Site n)(U:Config G n):ℝ:= (4:ℝ)⁻¹ * ∑ i:PlaqAxes,around U o i.val.1 i.val.2
@[simp] lemma W_one(o:Site n): W o (1:Config G n)=0:=by simp [W,around,compass,unitTravel,G.price_one]
lemma W_local(o:Site n):LocalOn (halo 2 {o}) (W (G:=G) o):=by
 intro U V h; have hl(a b:Step):travel U o (oriented a b)=travel V o (oriented a b):= travel_local _ _ _ _ (agrees_mono h (fun x hx => show x ∈ halo 2 {o} from halo_spec.mpr ⟨_,Finset.mem_singleton_self _, Square.nearby o a b hx⟩))
 simp only [W,around,compass,hl]
lemma W_gauge(o:Site n) (U:Config G n) (g:Site n→ G.El): W o (gauge g U)= W o U:=by simp only [W,around,compass,travel_gauge,stop_oriented,G.price_conj]
@[fun_prop] lemma W_cont(o: Site n):Continuous (W (G:=G) o):=by unfold W around compass; fun_prop
lemma W_nn(o:Site n)(U:Config G n):0≤W o U:= mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _=> Finset.sum_nonneg fun a _=> Finset.sum_nonneg fun b _=> (G.price_range _).1))

lemma compass_bill(o:Site n)(i j:Step)(p:BudgetPoint)(ha:i.dir < j.dir): Bill p o (Healthy p.threshold {o}) (faceCost G p*p.threshold^2) fun U:Config G n => compass U o i j:=by
 let l:=oriented i j; let Z(U:Config G n):=Healthy p.threshold {o} U; have hl:l.length=4:=rfl
 have he:= word_fund o l p Z (fun U u=> Square.small i j ha u)
 let c := (G.colorScale^2*2)⁻¹; have h:= G.colorScale_pos; have hC:0≤c:=by unfold c; positivity
 have hp(U:Config G n): compass U o i j=c * inner ℝ (wordStamp o l U) (wordStamp o l U (G:=G)):=by
    rw [real_inner_self_eq_norm_sq]; have e:= G.chord_price (travel U o l); change (‖wordStamp o l U (G:=G)‖ / G.colorScale)^2 = 2*compass U o i j at e
    unfold c; field_simp at e ⊢; linarith
 rw [funext hp]; refine Bill.le (Bill.mul_left c (Bill.pair he he)) ?_; unfold faceCost; rw [abs_of_nonneg hC,hl]; unfold c; exact le_of_eq (by ring)
def compassCost(G:Gauge)(p:BudgetPoint):= (Fintype.card PlaqAxes:ℝ)*faceCost G p
lemma compass_cost_nn(G:Gauge)(p:BudgetPoint):0≤compassCost G p:=mul_nonneg (Nat.cast_nonneg _) (faceCost_nonneg ..)
lemma paid (p: BudgetPoint)(o:Site n) : Bill p o (Healthy p.threshold {o}) (compassCost G p*p.threshold^2) (W (G:=G) o):=by
 have he (i:PlaqAxes) (a b:Bool) := compass_bill (G:=G) o ⟨i.val.1,a⟩ ⟨i.val.2,b⟩ p i.property
 refine Bill.le (Bill.mul_left 4⁻¹ (Bill.sum Finset.univ fun i _ => Bill.sum Finset.univ fun a _=>Bill.sum Finset.univ fun b _=>he i a b)) ?_
 apply le_of_eq; simp [compassCost]; ring
lemma regular (p: BudgetPoint)(o:Site n): p.Regular (halo 2 {o}) (W (G:=G) o):= reg_bill (paid p o) (W_cont o).measurable (W_local o) (fun g u=> W_gauge o u g)

lemma curve (o:Site n){x:Site n}(j:LinearJet G)(hn:10*(separation x o+2)<n.val)(a:PlaqAxes)(i k: Bool):
 Tendsto (fun t:ℝ=> compass (line (j.field o) t) x ⟨a.val.1,i⟩ ⟨a.val.2,k⟩ / t^2) (𝓝[≠] 0) (𝓝 (‖j.positive a‖^2/2)):=by
 let c:Step:=⟨a.val.1,i⟩; let d:Step:=⟨a.val.2,k⟩
 have he := price_limit (V:=fun t => travel (line (j.field o) t) x (oriented c d)) (by simp [unitTravel]) (Square.word_deriv x _ _)
 rw [Square.word_sum c d j (by have :=Square.near_face x c d; have :=separation_triangle (atFace x c d) x o; omega) (by omega)] at he
 have hi : ‖(flag c*flag d) • j.curl c.dir d.dir‖=‖j.positive a‖:=by
    rw [norm_smul,Real.norm_eq_abs,abs_mul]; have h(y:Step): |flag y|=1:= by rcases y with ⟨i,p|p⟩<;>simp [flag];
    rw [h,h,mul_one,one_mul]; rfl
 rw [hi] at he; exact he
lemma limit(o: Site n){x:Site n}(j:LinearJet G)(hn:10*(separation x o+2)<n.val):
 Tendsto (fun t:ℝ=> W x (line (j.field o) t)/ t^2) (𝓝[≠] 0) (𝓝 ((∑ a:PlaqAxes,‖j.positive a‖^2)/2)):=by
 let Q(a:PlaqAxes):=‖j.positive a‖^2 / 2
 have l(a:PlaqAxes):∑ i:Bool,∑ b:Bool, Q a=(4:ℝ) * Q a:=by simp; ring
 have h := tendsto_finsetSum Finset.univ fun a _=>tendsto_finsetSum Finset.univ fun i _=>tendsto_finsetSum Finset.univ fun b _=>curve o j hn a i b
 have e:= h.const_mul 4⁻¹; change Tendsto _ _ (𝓝 ((4:ℝ)⁻¹ * ∑ a:PlaqAxes,∑ i:Bool, ∑ b:Bool,Q a)) at e; simp_rw [l] at e; rw [←Finset.mul_sum, ←mul_assoc, inv_mul_cancel₀ (by norm_num), one_mul] at e
 unfold W around; simp_rw [mul_div_assoc,Finset.sum_div]; exact e
lemma W_diag (p: BudgetPoint)(u:G.Simple)(o: Site n){x:Site n}(j:LinearJet G)(hn:10*(separation x o+2)<n.val)(α:ℝ): logHessian (α • W x) (j.field o) (j.field o) = α * ∑ a:PlaqAxes,‖j.positive a‖^2:=by
 have he := hessian_limit u (CouplingShape.reg_scale α (regular p x)) (by simp) (j.field o)
 have hp:= (limit o j hn).const_mul α; simp only [Pi.smul_apply,smul_eq_mul,mul_div_assoc] at he; have := tendsto_nhds_unique he hp; rw [←mul_div_assoc] at this; linarith only [this]
lemma W_proj (p: BudgetPoint)(u:G.Simple)(o: Site n)(hn:20 < n.val)(a:PlaqAxes)(α:ℝ): coeff (G:=G) (α • W o) o a a=α:=by
 change logHessian (α • W o) ((wedge a (spike G)).field o) _=α; rw [W_diag p u o _ (by simpa using hn)]; simp [curl_wedge,spike_norm u,apply_ite norm,ite_pow]

private lemma tilt(U:Config G n)(s:Signed)(v x:Site n)(a b:Step): compass (pull s v U) x a b=compass U (affine s v x) (a.rotate s) (b.rotate s):=by simp [compass,travel_pull,Lattice.oriented,Step.rev_rotate]
private lemma swirl(U:Config G n)(s:Signed)(x v:Site n)(i j:Axis): around (pull s v U) x i j= around U (affine s v x) (s.perm i) (s.perm j):=by
 unfold around; simp_rw [tilt]; rw [Fintype.sum_bool,Fintype.sum_bool]; simp_rw [Fintype.sum_bool]
 cases h:s.flip i<;>cases he:s.flip j<;> simp [Step.rotate,h,he]<;>abel_nf
lemma W_pull(U:Config G n)(s:Signed)(v x:Site n): W x (pull s v U)= W (affine s v x) U:=by
 unfold W; apply congrArg
 refine Fintype.sum_equiv (PlaqAxes.transform s) _ _ (fun a=>?_)
 rw [swirl]; let i:=s.perm a.val.1; let j:=s.perm a.val.2; let o:=affine s v x; change around U o i j = around U o (min i j) (max i j)
 rcases lt_or_gt_of_ne (show i ≠ j from s.perm.injective.ne a.property.ne) with h|h
 · rw [min_eq_left h.le,max_eq_right h.le]
 rw [min_eq_right h.le,max_eq_left h.le]; unfold around; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; rw [compass,oriented_swap, G.price_inv]; rfl
end YM.AnalyticBridge.VerifiedReset.Compass
