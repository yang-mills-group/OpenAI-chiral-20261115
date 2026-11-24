import YM.CF.BProof.Moment.Priced
import YM.CF.BProof.Grid.Connect

/-! Paying arrays translated once per site, allowing bounded root multiplicity resets. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Moment
open Function Filter Set RG Push.AbsoluteSums Finset MeasureTheory Grid Lattice
open scoped Topology BigOperators Classical
variable {n:ℕ} {s:Fin n→ Side}{A : Type*}{X:Type*}[Fintype X]
-- meridian counts; using degree estimate polynomial once, no extra worst volume.
theorem scan (S:X × A → Sites s) (x:X ≃ Vertex s) (C : ℕ) (v:A→ℕ) (d:X × A→ℝ) (h:∀ i,0≤d i)
    (u:ℝ){U E eps:ℝ} (he:0<eps)(hU:0≤U) (W:A→ℝ) (w:SumBudget (fun a=> Real.exp (E*v a)*W a) U) {K T:ℝ}(hK:0≤K)(hT:0≤T)
    (H:∀ p: X× A, d p ≤ K*W p.2)
    (hh:∀ p:X × A, Real.exp (u*(S p).card) ≤ T*Real.exp ((E-eps)*v p.2))
    (hx:∀ p: X × A, ∀ i∈ S p, Grid.dist (x p.1) i≤ C*(1+v p.2)):
    Toll S d u ((K*T*((2*C+1 :ℕ):ℝ)^n*(eps⁻¹^n*n.factorial*Real.exp eps))*U):=by
 have hv(a):0≤W a:= nonneg_of_mul_nonneg_right (w.1 a) (Real.exp_pos _) -- check
 let D:= ((2*C+1:ℕ):ℝ)^n; let k:= eps⁻¹^n*n.factorial*Real.exp eps
 have hg:0≤D:=by unfold D; positivity
 have hp:0≤k:=by unfold k; positivity
 refine ⟨h,fun i=>budget_fiberwise Prod.snd (fun p'=> by unfold hit; split; exact mul_nonneg (Real.exp_pos _).le (h p'); exact le_rfl) (fun a t hl=>?_) (budget_scale (show (0:ℝ)≤ K*T*D*k by positivity) w)⟩
 let q:=K*T*Real.exp ((E-eps)*v a)*W a; let r:=v a; let L:=t.filter (fun p => i∈ S p); have hk(p:X×A)(u:p∈L): p.2=a:=hl p (mem_filter.mp u).1; have hv':0≤q:=by unfold q; have := hv a; positivity
 let f(p:X×A):= x p.1
 have hr : L.card ≤ (2*C+1)^n*(1+r)^n:=by
   have h : (2*(C*(1+r))+1) ≤ (2*C+1)*(1+r) := by nlinarith
   have hi:Set.MapsTo f ↑L ↑(collar {i} (C*(1+r))) := fun p H=> collar_mem.mpr ⟨i,mem_singleton_self _,by simpa only [hk p H] using hx p i (mem_filter.mp H).2⟩
   refine (Finset.card_le_card_of_injOn f hi (fun p hp q hq g=>Prod.ext (x.injective g) ((hk p hp).trans (hk q hq).symm))).trans ((Grid.collar_volume ..).trans ?_)
   rw [Finset.card_singleton,one_mul,←mul_pow]; gcongr
 have H' : ∑ p∈t,hit S d u i p ≤ D*(1+(r:ℝ))^n*q:=calc
    _ ≤ ∑ p∈L,q:=by
       unfold L; rw [sum_filter]; refine sum_le_sum fun p hp=>?_ ; unfold hit; split; swap; exact le_rfl; next hx=> exact le_trans (mul_le_mul (hh p) (H p) (h p) (mul_nonneg hT (Real.exp_pos _).le)) (by rw [hl p hp]; unfold q; exact le_of_eq (by ring))
    _ ≤ _:=by
       rw [sum_const,nsmul_eq_mul]; gcongr; unfold D; exact_mod_cast hr
 refine H'.trans ?_
 apply le_trans (a:=D*(1+(r:ℝ))^n*q) (b:=D*(k*Real.exp (eps*r))*q) (by gcongr; apply polynomial_cost he (by positivity)) (Eq.le ?_)
 unfold q; rw [sub_mul, Real.exp_sub]; unfold r D k; field_simp -- tune
end YM.CF.BProof.Moment
