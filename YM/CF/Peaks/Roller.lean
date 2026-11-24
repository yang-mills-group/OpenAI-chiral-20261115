import YM.CF.Peaks.Foil
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
lemma typical (σ:ℝ)(h:0<σ)(w:ℕ): ∃ C:ℝ,0<C ∧ ∀ (L:Side),∃ e:ℝ,0<e∧e≤1∧∀ (n m:ℕ), m≤16*L.val+8*L.val*n→
    let s:= (m+16*L.val+3:ℕ)
    (1+(L.val:ℝ)⁻¹*s)^w * Real.exp (e*s)*((m*e+1:ℝ)*(1+e)^m)≤C*Real.exp (σ*n):=by
  let a:=min (σ/32) 1; have ha:0<a:=lt_min (by linarith) one_pos; have hm:a≤1:=min_le_right ..; have hx:a ≤ σ/32:=min_le_left ..
  let C:= ((a/(w+1:ℝ))⁻¹)^w
  have hg:0<C:= by unfold C; positivity
  refine ⟨C*Real.exp (4*a*35),by positivity,fun L=>?_⟩
  let y:ℝ:=L.val; have hy: 0<y:=side_pos _; have H:1≤y:=by unfold y; exact_mod_cast L.property
  let e:= a/y; have he:0<e:=div_pos ha hy
  refine ⟨e,he, (div_le_self ha.le H).trans hm,fun n m p=>?_⟩
  intro s
  have hb:e*m ≤ e*s := mul_le_mul_of_nonneg_left (by unfold s; exact_mod_cast (show m≤_ by omega)) he.le
  have hc:y⁻¹*s≤ 35+8*(n:ℝ):=by
    rw [inv_mul_eq_div,div_le_iff₀ hy]
    have hk:(m:ℝ) ≤ 16*y+8*y*n:=by unfold y; exact_mod_cast p
    unfold s; push_cast; change (m:ℝ)+16*y+3≤_; nlinarith
  have hl : a * (y⁻¹*s)=e*s:=by unfold e; ring
  calc
    _ ≤ C * Real.exp (a*(y⁻¹*s))* Real.exp (e*s)*(Real.exp (e*s)*Real.exp (e*s)):=by
      have ht: (1+e)^m ≤ Real.exp (e*s) :=by
        calc
          _ ≤ (Real.exp e)^m:=pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp e]) m
          _ = Real.exp (e*m):=by rw [mul_comm e,Real.exp_nat_mul]
          _ ≤ _:= Real.exp_monotone hb
      have hh : m*e+1≤Real.exp (e*s):=by have := Real.add_one_le_exp (e*s); linarith
      gcongr; exact alpine ha hm w _ (mul_nonneg (inv_nonneg.mpr hy.le) (Nat.cast_nonneg _))
    _ = C *Real.exp (4*e*s):=by simp only [hl,mul_assoc,←Real.exp_add]; ring_nf
    _ ≤ _:=by
      rw [mul_assoc C,←Real.exp_add]; apply mul_le_mul_of_nonneg_left _ hg.le; apply Real.exp_monotone; rw [mul_assoc (4:ℝ),← hl]; nlinarith [mul_le_mul_of_nonneg_left hc ha.le,mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg n)]
variable {N P:Side}(G:Ratio N P)(u v:Bool)
def drawer (r t:St G.count)(z:Cover)(c:ℂ)(o:Lattice.Order)(δ:ℝ)(i:Iota G):=if i.1.2=r then δ else (0:ℝ)
lemma comic (ho:Odd G.count.val)(r t:St G.count)(z:Cover)(c:ℂ)(o:Lattice.Order)(e δ:ℝ)(m:ℕ)(he:0<e)(hp:e≤1)
    (H: let ℓ:= (runD u v G.count r t z o).length; let s:=(ℓ+16*G.count.val+3:ℕ);
        (Fintype.card Slot:ℝ)*((1+(G.count.val:ℝ)⁻¹*s)^m*Real.exp (e*s)*(((ℓ*e+1:ℝ)*(1+e)^ℓ)*‖c‖))≤δ): Street (badge _) (parcel G u e) (parcel G v e) m ((G.count.val:ℝ)⁻¹) e (drawer G r t z c o δ) (fun x=> drag G u v r t z c o x.val):=by
  let f(x:Site N):=(x,r); let g(x:Site N):=(x+wrap N z,t); let p:=runD u v G.count r t z o; let ℓ:=p.length; let W:=((ℓ*e+1:ℝ)*(1+e)^ℓ)*‖c‖; let K(x):=conduit G u v (f x) (g x) p
  let s:= (ℓ+16*G.count.val+3:ℕ); let E:= Real.exp (e*s); let x:ℝ:=(G.count.val:ℝ)⁻¹; have hx:0≤x:=inv_nonneg.mpr (side_pos _).le
  have hh (i): rent e (K i)≤E:=Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast conduits ..) he.le)
  have hp' (x:Site N): Suite (badge _) (parcel G u e) (parcel G v e) (K x) (reed (f x) (g x) W) (fun i=>panel (x,r) (x+wrap N z,t) ((Rush.wind x z*c) • (track i.val.1 (touch G u (x,r)) p).1)):=by
    have hw:=corset G u v (p:=p) ho (f x) (g x) (Rush.wind x z*c) e he hp (worn G u v ho r t z o x)
    dsimp only at hw; rw [norm_mul,Rush.wind,fee_norm,one_mul] at hw; exact hw
  apply mergeW K _ _ hp' (fun _=> rfl); intro i; by_cases hc:i.1.2=r
  · let k:=i.1.1; have h1:i.1=f k:=Prod.ext rfl hc
    have hr(j:Iota G): ∑ l:Site N,rent e (K l)*reed (f l) (g l) W i j=if j.1=g k then rent e (K k)*W else 0:=by
      rw [sum_eq_single k]; simp only [reed,h1,true_and,mul_ite,mul_zero]; intro b _ he; have ht:f k ≠ f b:= fun h=> he ((congr_arg Prod.fst h).symm); simp [reed,h1,ht]; simp
    rw [drawer,if_pos hc]; simp_rw [hr]; rw [Fintype.sum_prod_type]; rw [Finset.sum_eq_single (g k)]; swap
    · intro b _ he; simp [he]
    swap; simp
    simp only [ite_true];
    apply le_trans _ H
    rw [← nsmul_eq_mul,← Finset.card_univ,← sum_const (s:= (univ:Finset Slot))] -- card_univ problem
    refine Finset.sum_le_sum fun b _=> ?_
    let q:= ((tempo G e).F.span ((tempo G e).home i) ((tempo G e).home (g k,b)))
    change (1+x*q)^m*_ ≤ (1+x*s)^m * E * W
    by_cases hl:W=0
    · simp [hl]
    obtain ⟨hG,t',s'⟩:= ((hp' k).expo i (g k,b)).triggered (by simp [reed,h1,hl])
    have hq:(q:ℝ)≤ s:= by exact_mod_cast ((Grove.lim hG _ t' _ s').le.trans (show Finset.card (K k)≤s from conduits ..) : q ≤ s)
    rw [mul_assoc ((1+x*s)^m)]; have hw:0≤W:=by unfold W; positivity
    exact mul_le_mul (by gcongr) (mul_le_mul_of_nonneg_right (hh _) hw) (mul_nonneg (rent_pos ..).le hw) (by positivity)
  unfold drawer; rw [if_neg hc]; have he(j:Iota G)(y:Site N): reed (f y) (g y) W i j=0:=if_neg fun q=> hc (congr_arg Prod.snd q.1)
  simp_rw [he]; simp
end YM.CF.Peaks
