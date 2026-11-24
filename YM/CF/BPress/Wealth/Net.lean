import YM.CF.BPress.Wealth.Support
/-! Long and atom support prices. Sum arrays over sites using fidelity cost, preserve signs/channels. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Finset Filter MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
open Push.Local ConnectedActivityE6.Raw Work.F05 Paths
variable {s : Side}{G: Gauge}{r M:ℕ}{δ a σ C Λ:ℝ}
variable (z : ℕ→ Atom G r)(T:PathData G)(p : BudgetPoint)(q : Clip)(t:Signed)
local notation "Cell" => Face (Per s)
-- scope from lengths
def atomArea (i : Site s×ℕ) := photo t (inspected ((z i.2).footprint i.1)) -- `Atom.length` exact length.
def atomFee (x : Support s) :ℝ:= Ledger.lump (atomArea z t) (fun i=> ((z i.2).magnitude)*p.threshold^r) x
def atom (P : Support s) : Config G s→ℝ:= crop (atomArea z t) (fun i U=> (z i.2).placed p (pull t 0 U) i.1) P

lemma atom_unit {r:ℕ}(z:Atom G r)(v:z.Invariant)(i:Site s): GEM (inspected (z.footprint i)) (fun U=> z.placed p U i) (z.magnitude*p.threshold^r):=by
 refine ⟨?_, fun U=> healthy_atom z p U i, masked_measurable _ _ _ (Atom.unmasked_cont ..).measurable, placed_local z p i, fun g U=>?_⟩
 · unfold Atom.magnitude; positivity [p.threshold_pos]
 let P:=z.footprint i; have h: Healthy p.threshold P (gauge g U) ↔ Healthy p.threshold P U:= by simp only [Healthy,gauge_flags]
 unfold Atom.placed;
 by_cases k:Healthy p.threshold P U; · rw [masked_eq _ _ _ _ k,masked_eq _ _ _ _ (h.mpr k)]; unfold Atom.unmasked; simp_rw [slot_gauge]; exact v _ _
 rw [masked_ne _ _ _ _ k,masked_ne _ _ _ _ (fun p=> k (h.mp p))]
lemma area_bundle (x:Site s)(z: Atom G r): photo t (inspected (z.footprint x)) ⊆ halo (8+z.length) {turnSites t 0 x}:=by
 have hx: turnSites t 0 x=t.act x:=by simp [turnSites,Signed.actEquiv]
 rw [add_comm, hx,←halo_photo]; exact image_subset_image (atom_limit x z).2.2.1
lemma area_rate (v : a≥0)(f:a*17^4≤σ/2)(k:a*17^4*(r+1)≤1) (i:Site s×ℕ) : a*((atomArea z t i).card:ℝ) ≤ 1+ σ/2*((z i.2).length:ℝ):=by
 obtain ⟨o,z'⟩:= i; let l:=(z z').length; have he : (atomArea z t (o,z')).card≤ (l+r+1)*17^4:= card_image_le.trans (atom_limit o (z z')).2.2.2; refine le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr he) v) ?_; change _ ≤ 1+σ/2*l; push_cast; nlinarith only [f,k,Nat.cast_nonneg (α:=ℝ) l]
lemma atom_thin (h:SumBudget (fun i=> (z i).budget σ) C)(w : ∀ i,(z i).Invariant)(g:0<σ)(v:a≥0)(f:a*17^4≤σ/2)(k:a*17^4*(r+1)≤1) :
    Thinner (s:=s) (atom z p t) (atomFee z p t) a (Wt σ 8*(p.threshold^r*C)) ∧ ∀ U:Config G s, ∑ i,atom z p t i U=∑ o,PathData.atomSeries z p (pull t 0 U) o:=by
 let b(i : ℕ):=(z i).magnitude*p.threshold^r
 have he : Cash (atomArea (s:=s) z t) (fun i=> b i.2) a (Wt σ 8*(p.threshold^r*C)):= by
   refine current_bound (turnSites t 0) 8 (fun i=> (z i).length) (atomArea z t) (fun i=> area_bundle ..) (fun i=> (atom_unit p (z i) (w i) (0:Site s)).zero) g (fun i=>area_rate z t v f k i) ?_; convert! budget_scale (pow_nonneg p.threshold_pos.le r) h using 1; ext i; unfold Atom.budget; ring
 obtain ⟨l,j,H,P⟩:= crop_bound (r:=atomArea z t) (f:=fun i U=> (z i.2).placed p (pull t 0 U) i.1) (fun i=> (atom_unit p _ (w i.2) i.1).ship t) (fun i=> photo_g t _ (atom_limit i.1 (z i.2)).2.1) he v; refine ⟨P,fun U=>?_⟩; unfold atom; rw [H,(j U).tsum_prod]; nth_rw 1 [tsum_fintype]; rfl

variable (M) (x:PlaqAxes)
def longArea (i:Site s × (ℕ×ℕ)) := photo t (pairFoot (M+2) T (i.1,x) i.2)
def longFee (P : Support s):ℝ:=Ledger.lump (longArea M T t x) (fun i=> pairPrice T M 1 x i.2) P
def longG (P : Support s):= crop (longArea M T t x) (fun i U=> pairTail T q M 1 p.threshold (i.1,x) (pull t 0 U) i.2) P -- argument order

theorem pairCost : ∀ h:G.El, ∀ x y:G.Color, inner ℝ (G.adjoint h x) (G.adjoint h y)=inner ℝ x y:=by
 intro h x y; have e:= norm_add_sq_real (G.adjoint h x) (G.adjoint h y); rw [←map_add,G.norm_adjoint,G.norm_adjoint,G.norm_adjoint,norm_add_sq_real] at e; linarith
lemma pair_unit (h:Checks M p q)(x : Face (Per s))(i : ℕ×ℕ): GEM (pairFoot (M+2) T x i) (fun U=> pairTail T q M 1 p.threshold x U i) (pairPrice T M 1 x.2 i) := by
 refine ⟨pairPrice_nonneg ..,fun U=> pair_le ..,pair_measurable ..,pair_local _ _ _ _ _ _ _ (M+2) h,?_⟩ -- tune
 intro g U; unfold pairTail; dsimp only; rw [enough_p U g x]; split; next w =>
    have h(i):T.ellTerms x i (gauge g U)=G.adjoint (g x.1) (T.ellTerms x i U):=by rw [PathData.ellTerms, PathData.ellTerms,slot_gauge,map_smul]
    rw [h,h,pairCost];
 rfl
def refund (σ C:ℝ)(M:ℕ):= (2*Real.exp (-σ/2*M))*(C*C)
lemma pairs_base (h:T.Bounds q σ C Λ) : SumBudget (fun i=>pairPrice T M 1 x i * Real.exp (σ/2*length (duplex T x i))) (refund σ C M):=by
 have he:0 ≤ 2*Real.exp (-σ/2*M):=by positivity
 refine budget_mono (budget_scale he (budget_prod (h.rows x) (h.rows x))) (fun i=> mul_nonneg (pairPrice_nonneg ..) (Real.exp_pos _).le) ?_
 intro i; unfold pairPrice; split; next p=>
    rw [duplex_price,Nat.cast_add]; let a:=(T.row x i.1).2.length; let b:= (T.row x i.2).2.length; have hi:M ≤ a+b:=by unfold long at p; change ¬(a*1≤ M∧ b*1≤M) at p; omega
    calc
      _ ≤ 2*mate T x i * Real.exp (-σ/2*M+σ*a+σ*b) := by
        apply mul_le_mul_of_nonneg_left _ (by unfold mate; positivity); apply Real.exp_monotone; change σ/2*((a:ℝ)+(b:ℝ))≤_; have ht:=h.width; have p : (M:ℝ)≤ (a:ℝ)+(b:ℝ):=by exact_mod_cast hi
        nlinarith -- tune
      _ = _ := by unfold a b mate; rw [Real.exp_add,Real.exp_add]; ring
 next p=> rw [zero_mul]; exact (budget_scale he (budget_prod (h.rows x) (h.rows x))).1 i
lemma long_thin (h:T.Bounds q σ C Λ)(w:Checks M p q)(v:a≥0)(f:a≤σ/4)(k:a*(3+((2:ℝ)*M+5)^4)≤1) :
    Thinner (s:=s) (longG M T p q t x) (longFee M T t x) a (Wt (σ/2) (M+2)*refund σ C M) ∧ ∀ U:Config G s, ∑ i,longG M T p q t x i U =∑ o,tails T q M 1 p.threshold (o,x) (pull t 0 U):=by
 let l:= fun i=> length (duplex T x i); have pC : Cash (longArea (s:=s) M T t x) (fun i=> pairPrice T M 1 x i.2) a (Wt (σ/2) (M+2)*refund σ C M):=by
    refine current_bound (turnSites t 0) (M+2) l _ (fun i=>?_) (fun i=> pairPrice_nonneg ..) (half_pos h.width) (fun i=>?_) (pairs_base M T q x h) -- tune
    · rw [show M+2+l i.2=M+l i.2+2 by omega,show turnSites t (0:Site s) i.1=t.act i.1 from (by simp [turnSites,Signed.actEquiv]),←halo_photo]; exact image_subset_image (pair_limit (M:=M) (i.1,x) T i.2).2.2.1
    refine (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_image_le.trans (pair_limit (M:=M) (i.1,x) T i.2).2.2.2)) v).trans ?_; change a*((↑(l i.2+3+(2*M+5)^4:ℕ)):ℝ)≤_; push_cast; nlinarith only [Nat.cast_nonneg (α:=ℝ) (l i.2), f,k]
 obtain ⟨_,j,H,P⟩:= crop_bound (r:=longArea M T t x) (f:=fun i U=>pairTail T q M 1 p.threshold (i.1,x) (pull t 0 U) i.2) (fun i=> (pair_unit M T p q w (i.1,x) i.2).ship t) (fun i=> photo_g t _ (pair_limit (M:=M) (i.1,x) T i.2).2.1) pC v; refine ⟨P,fun U=>?_⟩; unfold longG; rw [H,(j U).tsum_prod]; nth_rw 1 [tsum_fintype]; exact sum_congr rfl fun i _=> (pair_sum h M 1 p.threshold (i,x) _).tsum_eq
end YM.CF.BPress.Wealth
