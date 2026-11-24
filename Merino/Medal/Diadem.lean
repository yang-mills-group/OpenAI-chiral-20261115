import YM.SU5.Thin.Woods.Fabric
set_option maxHeartbeats 1000000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Diadem
open Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory
open RG Buffered Branch Tenant Skye CF.Pannier.Chancel Brace
open Py.Rate
open Buffered.Afterglow
open Lamour.Bridge.Celeste.Clock Fabric
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{n m:Side}

local notation "D" => (More n).val^4
local notation "E"=>Real.exp

def glacier (d:ℕ):=Real.exp (-(d:ℝ)^5)
def Marble (μ ν: Mark n→ℂ):Prop:=
 ∀ (M:Mark n) c,Envelope M → (∀ x,‖M x‖≤c)→‖μ M-ν M‖≤glacier n.val*c
def Icicle (n:ℕ) (ε a d:ℝ):=
 glacier n*d^((n*2)^4)≤(E ε-1)*(E (-a))^((n*2)^4)

variable {ε a d:ℝ}
lemma ramp (h:0<ε)(ha:0≤a)(hd:1≤d) :
  ∀ᶠ n in atTop,Icicle n ε a d :=by
 have u:=Real.exp_log (show 0<E ε - 1 by
    have :=Real.one_lt_exp_iff.mpr h; linarith)
 let b:= |Real.log (E ε - 1)|
 let C:=a+Real.log d
 have hc:0≤C:=add_nonneg ha (Real.log_nonneg hd)


 filter_upwards [eventually_ge_atTop (1:ℕ),
   (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (b+C*16)]
      with t ht v
 have v₁:1≤(t:ℝ):=by exact_mod_cast ht
 have g:=mul_le_mul_of_nonneg_right v (by positivity:(0:ℝ)≤(t:ℝ)^4)
 have j:=le_trans (neg_le_abs (Real.log (E ε - 1))) (le_mul_of_one_le_right (show 0≤b from abs_nonneg _) (one_le_pow₀ v₁ (n:=4)))
 have x:=Real.exp_monotone (show -(t:ℝ)^5+((t*2:ℕ)^4:ℕ)*Real.log d ≤
          Real.log (E ε - 1)+((t*2:ℕ)^4:ℕ)*(-a) by
            push_cast; change b+C*16≤(t:ℝ) at v
            change (b+C*16)*(t:ℝ)^4 ≤ (t:ℝ)*(t:ℝ)^4 at g
            unfold C at g
            linarith only [g,j])
 unfold Icicle glacier
 simpa only [Real.exp_add,Real.exp_nat_mul,u,
       Real.exp_log (zero_lt_one.trans_le hd)] using x



def tariff (K:Calibration)(w:ℕ):ℝ:=↑(4*(w+addgap K):ℕ)^4
lemma tariff_pos (K w) : 0<tariff K w:=by
 have h:0<w+addgap K:=Nat.add_pos_right _ addgap_pos
 unfold tariff; positivity

variable {w l : ℕ}{μ ν:Mark n→ℂ}
lemma splitPrice (h:0<ε)(ha:0≤a)(hd:1≤d)
 (v:Icicle n.val ε a d)(u:Marble μ ν)(y:ℝ)(b:E (-a) ≤y)
 (c:ℕ)(j:c≤D)(X:Mark n)(p:Envelope X)(e:∀ x,‖X x‖≤d^c):
   ‖μ X-ν X‖≤(E ε-1)*y^c :=by
 have g:=u _ _ p fun x=>(e x).trans (pow_le_pow_right₀ hd j)
 have a₀:E (-a)≤1:=Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)
 exact g.trans <|v.trans <|
    mul_le_mul_of_nonneg_left
     ((pow_le_pow_of_le_one (Real.exp_pos _).le a₀ j).trans (pow_le_pow_left₀ (Real.exp_pos _).le b _))
     (sub_nonneg.mpr (Real.one_lt_exp_iff.mpr h).le)


variable {W: Fabric n→Prop}
lemma buffet_b (h:∀A,W A→∀ x,‖A.x x‖≤d)(hd:1≤d)
 (U: List (Fabric n))(f:Sylvan W l U)(x): ‖buffet U x‖≤ d^U.length:=by
 induction U with
 | nil=>rw [buffet_empty,List.length_nil,pow_zero,Pi.one_apply,norm_one]
 | cons A U ih=>
   rw [buffet_more,Pi.mul_apply,List.length_cons,pow_succ']
   have hh:Sylvan W l U:=⟨fun a v=>f.core a (List.mem_cons_of_mem _ v),
            (List.pairwise_cons.mp f.annex).2⟩
   exact (norm_mul_le ..).trans <|mul_le_mul (h A (f.core A List.mem_cons_self) x)
     (ih hh) (norm_nonneg _) (zero_le_one.trans hd)
#check trefoil


theorem chess {x:ℝ}(δ:ℝ)(D0:0<δ)(ha:0≤a)(hd:1≤d)(X:-a ≤x)
 (v:Icicle n.val (δ*tariff K w) a d)(s:Marble μ ν)
 (he : ∀ {x:Fabric n}, W x→∀i z,W (x.twistL i z))
 (hv : ∀ x,W x→AtSupport false x.S x.x)
 (hc : ∀ A,W A→∀V,‖A.x V‖≤d)
 (h : ∀ U,Sylvan W l U→‖μ (buffet U)‖≤ E (U.length*x+δ*sites n))
 (r:Twosome K n ν)(g:n=K.c m)
 (e:w+addgap K≤n.val)(A:Fabric n)(f:W A)(p:∀i,cows i (Lattice.halo l A.S) w):
 ‖μ A.x‖ ≤ E (x+3*(δ*tariff K w)) :=by
 obtain ⟨U,hU,z,q,b,a₁⟩:=trefoil he hv r g e A f p
 let θ:=tariff K w
 let ε:=δ*θ
 have e₀:0<ε:=mul_pos D0 (tariff_pos ..)
 have e₁:1<E ε:=Real.one_lt_exp_iff.mpr e₀
 let y:=E (x+ε)
 have ry:E (-a)≤y := Real.exp_monotone <|X.trans (le_add_of_nonneg_right e₀.le)
 have y0:0<y:=Real.exp_pos _
 have hw: ‖μ (buffet U)‖ ≤ y^U.length:=by
     apply (h U hU).trans; unfold y; rw [←Real.exp_nat_mul]
     have j:sites n≤U.length*θ:= by unfold sites θ tariff; exact_mod_cast b
     apply Real.exp_monotone; unfold ε; linarith only [mul_le_mul_of_nonneg_left j D0.le]


 have r :=splitPrice e₀ ha hd v s y ry
 have hh : ‖ν A.x‖≤E ε * y :=by
     have j:=r _ q _ (hU.occupy hv).env (buffet_b hc hd U hU)
     apply (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le y0.le) (Nat.ne_zero_of_lt z)).1
     rw [mul_pow]
     rw [norm_sub_rev] at j
     refine (a₁.trans (norm_le_norm_sub_add _ _)).trans <| (add_le_add j hw).trans ?_
     have t:E ε≤(E ε)^U.length:= by simpa using (pow_le_pow_right₀ (a:=E ε) e₁.le (show 1≤U.length from z))
     apply le_trans _ (mul_le_mul_of_nonneg_right t (pow_nonneg y0.le _)); ring_nf; exact le_rfl
 have k:=r 1 (Nat.le_trans z q) _ (hv A f).env (by rw [pow_one]; exact hc A f)
 rw [pow_one] at k
 apply (norm_le_norm_sub_add _ _).trans <|(add_le_add k hh).trans _
 change _ ≤ E (x+3*ε)
 rw [show x+3*ε=ε+(ε+(x+ε)) from by ring,Real.exp_add,Real.exp_add]
 nlinarith only [mul_nonneg (sq_nonneg (E ε-1)) y0.le]

end YM.CF.Merino.Diadem
