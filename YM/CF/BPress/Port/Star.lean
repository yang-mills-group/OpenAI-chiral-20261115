import YM.CF.BPress.Port.Spin
/-! Transmission on actual angular Mark sampler data. Pull exact Gaussian costs with support indicators; extract global lower later. No integrability *assumed* after transport. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Port
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Weave Branch
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ENNReal
open SU Gauge Next.SectorChange
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)(D:ℕ)(J:ChartRatio group)(κ y:ℝ)(A:BEnd X)(F:Fare X)(S:Seal X.Hcols)
-- pointwise bias (Gaussian hard unchanged). coastV all truncate iff Barrel.
def Barrel (x: Fills X): Prop:= ∀ b, ‖x b‖ ≤ truncv y
def hardHit (i:X.Hcols)(v:Fills X) := ‖v i‖^2/2
def tax_column (i:X.Hcols)(v:Fills X): ℝ:= N_v B.D y * gH B.D J y * Real.exp (logPay B.D J y (wjson (F S) v i) + hardHit X i v)
def taxG (v:Fills X): ℝ:=∏ i∈ Sᶜ, tax_column X J y F S i v
def bodyBase (x:Quarters X): Offers X:=issueT X y S (wjson (F S) x.1) x.2
lemma barrel_ne (x) : coastV X y x≠0 ↔ Barrel X y x.1:=by
 refine Finset.prod_ne_zero_iff.trans ?_; simp only [mem_univ,forall_true_left,Barrel,vcost,mul_ne_zero_iff,trunc_eq]; apply forall_congr'; intro i; by_cases h:‖x.1 i‖≤truncv y; rw [if_pos h,iff_true_intro h,iff_true]; exact ⟨inv_ne_zero (v_pos B.D y).ne',(c_pos B.D (x.1 i)).ne'⟩; rw [if_neg h,iff_false_intro h]; simp
lemma barrel_ae : ∀ᵐ x∂ knell X y, Barrel X y x.1:=by rw [read_volts, ae_withDensity_iff]; exact Eventually.of_forall fun i t=> (barrel_ne X y i).mp (fun v=>t (by simp [v])); exact (volts_meas X y).ennreal_ofReal
lemma body_meas : Measurable (bodyBase X y F S):= by
 let f:Quarters X→Fills X:=wjson (F S) ∘ Prod.fst; have he: Measurable f:= (wjson_meas (F S)).comp measurable_fst; let he':= he.prodMk (show Measurable (Prod.snd (α:=Fills X) (β:=Offers X)) from measurable_snd); convert! (issue_meas X y S).comp he' using 1
def aware (v:Quarters X): Prop:= pick X κ y (bodyBase X y F S v)=S
variable {X F A J y κ} {T:Sheet.Atlas}{P:Weave.Budget}
namespace Afford
variable (q:Afford J T P B.D κ y)(r:LocalRatio J)(e:Summer X F P.upper (P.low y) (P.reach y) (P.chunks y))(f:Whole X S (F S) 1)
include q r e f
set_option maxRecDepth 4000 in
set_option maxHeartbeats 330000 in
lemma fares (v:RaySpace X)(K:Offers X)(p:aware X κ y F S (offer X v,K)) : coast X J y S (wheel (F S) (offer X v,K)) = coastV X y (offer X v,K)* taxG X J y F S (offer X v):=by
 let w:=F S v; let x:=offer X v; let y':= offer X w; let V:= wheel (F S) (x,K); have hx: V.1=y':=by apply wjson_r
 have Hp:S=pick X κ y (issueT X y S y' K):= by
   have m:pick X κ y (issueT X y S (wjson (F S) (offer X v)) K)=S:=p; rw [wjson_r] at m; exact m.symm -- tune type
 let b:=coordinate X y' (ratev X J y S); unfold coast; rw [show (wheel (F S) (_,K)).1=_ from hx]; change b=_; by_cases u:Barrel X y x; swap
 · rw [show coastV X y (offer X v,K)=0 from not_not.mp (mt (barrel_ne X y _).1 u),zero_mul]; by_contra h; have he:= Finset.prod_ne_zero_iff.mp (show ∏ i,ratev X J y S i (y' i) ≠0 from ?_ ) -- parens (bigop greed)
   · apply u; apply q.homebound r S e f v K w rfl Hp -- tune order
     · intro i hx; apply not_not.mp; intro a; apply he i (mem_univ _); rw [ratev,if_neg hx]; exact Set.indicator_of_notMem a _
     intro i hx; by_contra t; apply he i (mem_univ _); rw [ratev,if_pos hx,vcost,trunc_eq,if_neg (show ¬ ‖y' i‖≤truncv y from t),mul_zero]
   exact h
 have h1 (i): y' i∈ mouthP B.D J y:=by rw [show y'=wjson (F S) x from (wjson_r _ v).symm]; exact q.outward r S e v u i -- tune
 have ha (i:X.Hcols): ratev X J y S i (y' i)= vcost B.D y (x i) * (if i∈S then 1 else tax_column X J y F S i x):=by
   unfold ratev; split; next h=> rw [mul_one,show y' i= _ from whole_he _ f v i h]
   next h=>
     unfold tax_column hardHit; rw [billH,Set.indicator_of_mem (h1 i),vcost,trunc_eq,if_pos (u i), low_v, show wjson (F S) x=y' from wjson_r _ v]; have he:= Real.exp_ne_zero (logPay B.D J y (y' i)+‖x i‖^2/2); have hp:0<N_v B.D y:= v_pos B.D y; have hq:Real.exp (-‖x i‖^2/2)* Real.exp (logPay B.D J y (y' i)+‖x i‖^2/2)=Real.exp (logPay B.D J y (y' i)):=by rw [← Real.exp_add]; congr 1; ring
     nth_rw 1 [← hq]; field_simp -- tune
 unfold b coordinate coastV coordinate taxG; simp_rw [ha]; rw [prod_mul_distrib]; congr 1; rw [show Sᶜ= univ.filter fun i=> i∉ S from ?_,prod_filter]; refine prod_congr rfl (fun i _=>?_ ); split_ifs <;> tauto; ext; simp -- tune
end Afford
end YM.CF.BPress.Port
