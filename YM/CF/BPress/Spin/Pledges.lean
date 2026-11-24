import YM.CF.BPress.Spin.Pledge
import YM.CF.Dial.Winter
/-! Uniform powers budget. `invertible` uses real PSD order with c•1 lower (arbitrary gap);
 analogous purchase for pencil version of the log from Support/Ln. Use that one directly in
 plogre (scaled argument). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Finset Filter NormedSpace Fock Branch
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
attribute [local instance] opCStarAlgebra
namespace Pledge
variable (P:Pledge) {k C:ℝ}
theorem geometric (c:0≤C)(h:0<k)(w:k<1) : ∃ (T:Pledge) (r:ℝ), 0<r ∧ r<1 ∧ ∀ {I Y D: Type} [Fintype Y][DecidableEq Y][Fintype I][DecidableEq I] [Nonempty I] [TopologicalSpace D] (b : Stage Y I D Empty) (f : Raw D I), Capacity b C→P.Costs b f→(∀x,‖f x‖≤k)→ ∀ n:ℕ, RootedK (solo b) (solo b) T.rate (T.price*r^n) (fun x=> f x^n) := by
 obtain ⟨R,t,y⟩:= exists_between w; obtain ⟨n,hn,v,d,V,B,X,Y⟩:= grouping c P.pos P.bought t (h.trans t) y (show 0<(1:ℝ)/4 by norm_num); obtain ⟨r,hr,u,H⟩:= drift_name hn (show 0<(1:ℝ)/2 by norm_num) (by norm_num)
 have hp:=P.bought; refine ⟨⟨d,2*(Real.exp d*(r^n)⁻¹*(Real.exp d*(max 1 (2*P.price))^n)),V,by positivity⟩,r,hr,u,?_⟩
 intro I A D _ _ _ _ _ _ b F U N J m; exact tariff hn N (power_low C P.rate P.price R (1/4) k n v d c P.pos.le (h.trans t).le V.le B X Y U N J) (B.trans (half_le_self P.pos.le)) V hr H _
theorem over (c:0≤C)(h:0<k)(w:k<1): ∃ T:Pledge, ∀ {I Y D: Type} [Fintype Y][DecidableEq Y][Fintype I][DecidableEq I] [Nonempty I] [TopologicalSpace D] {b:Stage Y I D Empty}{f: Raw D I}, Capacity b C→ P.Costs b f→(∀ x, ‖f x‖≤k)→ ∀ d:ℕ→ℝ,(∀ i, ‖d i‖≤1)→∀ j:ℕ,T.Costs b (fun x=> ∑' n:ℕ,d n • f x^(n+j)):=by
 obtain ⟨T,r,p,t,H⟩:= P.geometric c h w; let d₀(n:ℕ):=T.price*r^n
 have hx:Summable d₀:=(summable_geometric_of_lt_one p.le t).mul_left _
 have hp:=T.bought; refine ⟨⟨T.rate,(∑' n,d₀ n),T.pos,hx.tsum_pos (fun i=>by unfold d₀; positivity) 0 (by simp [hp,d₀])⟩,?_⟩; intro I A D _ _ _ _ _ _ b F X N J d v j
 refine RootedK.tsK d₀ (fun i=> ?_) T.pos.le hx
 have he (x:D) : d i • F x^(i+j) =(d i:ℂ) • F x^(i+j):=by ext l m; simp [Complex.real_smul]
 simp_rw [he]; apply ((H b F X N J _).raise _).books; rw [Complex.norm_real]
 exact (mul_le_of_le_one_left (by positivity) (v _)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one p.le t.le (Nat.le_add_right ..)) T.bought.le)
theorem zoom (c:0≤C)(h:0<k)(w:k<1) : ∃ T:Pledge, ∀ {I Y D: Type} [Fintype Y][DecidableEq Y][Fintype I][DecidableEq I] [Nonempty I] [TopologicalSpace D] {b: Stage Y I D Empty}{f: Raw D I}, Capacity b C→P.Costs b f→(∀ x,‖f x‖≤k)→
 T.Costs b (fun x=> (1-f x)⁻¹) ∧ T.Costs b (fun x=> pencil (f x)) := by
 obtain ⟨T,H⟩:= P.over c h w; refine ⟨T,?_⟩; intro I Y D _ _ _ _ _ _ b f B F L
 refine ⟨?_,H B F L bcoef bc_norm 1⟩; have ht := H B F L (fun _=>1) (by simp) 0; simp only [one_smul, add_zero,route_inv ((L _).trans_lt w)] at ht; exact ht
variable {I D : Type*}[Fintype I][DecidableEq I][Nonempty I]{A: Op I}{z r:ℝ}
lemma normal_calc (h:0<z)(t:z<r)(p:z • (1: Op I)≤ A)(u:A ≤ r • (1:Op I)) : let δ : ℝ:=1-z/r; 0<δ ∧ δ<1∧ ‖1-r⁻¹ • A‖ ≤ δ:=by
 intro δ
 have he := h.trans t
 have hp : 0<δ:= sub_pos.mpr ((div_lt_one he).mpr t)
 have hv :0≤1-r⁻¹ • A:= sub_nonneg.mpr ((smul_le_smul_of_nonneg_left u (inv_pos.mpr he).le).trans_eq (inv_smul_smul₀ he.ne' _))
 refine ⟨hp, sub_lt_self _ (div_pos h he), (CStarAlgebra.norm_le_iff_le_algebraMap _ hp.le hv).mpr ?_⟩
 have hl : r⁻¹*z=z/r := (mul_comm ..).trans (div_eq_mul_inv ..).symm
 have hg:= smul_le_smul_of_nonneg_left p (inv_pos.mpr he).le; rw [smul_smul,hl] at hg
 rw [Algebra.algebraMap_eq_smul_one]; unfold δ; rw [sub_smul,one_smul]; exact sub_le_sub_left hg _
lemma Gap_inv (h:0<z)(p:z • (1:Op I)≤ A): IsUnit A ∧ ‖A⁻¹‖≤z⁻¹ := by
 obtain ⟨X,y,H⟩:= Dial.norms_le_inv h p; have ht:= live_of y; refine ⟨ht,?_⟩
 rwa [← show A⁻¹=X from by rw [←mul_one A⁻¹, ←y,←mul_assoc,(live ht).2,one_mul]] at H
lemma selfU (h:0≤z)(p:z • (1:Op I)≤ A): IsSelfAdjoint A:= IsSelfAdjoint.of_nonneg ((smul_nonneg h zero_le_one).trans p)

theorem invertible (c:0≤C)(h:0<k) : ∃ T:Pledge, ∀ {I Y D: Type} [Fintype Y][DecidableEq Y][Fintype I][DecidableEq I] [Nonempty I] [TopologicalSpace D] {b: Stage Y I D Empty}{f: Raw D I}, Capacity b C→P.Costs b f→(∀ x,k • (1:Op I) ≤ f x)→ T.Costs b (fun x=> (f x)⁻¹) := by
 let r:=P.price+k; let Q:=unary.plus (P.scales ‖r⁻¹‖); have ht:k<r:=lt_add_of_pos_left k P.bought; have hx:=h.trans ht; let δ : ℝ:=1-k/r
 obtain ⟨S,H⟩:= Q.zoom c (show 0<δ from sub_pos.mpr ((div_lt_one hx).mpr ht)) (show δ<1 from sub_lt_self _ (div_pos h hx)); refine ⟨S.scales ‖r⁻¹‖,?_⟩; intro I Y D _ _ _ _ _ _ b f B F L; let g : Raw D I:=fun x=> 1-r⁻¹ • f x
 have he x : ‖1-r⁻¹ • f x‖≤ δ := (normal_calc h ht (L x) ((op_le_norm_one (selfU h.le (L x))).trans (smul_le_smul_of_nonneg_right ((F.bound x).trans (le_add_of_nonneg_right h.le)) zero_le_one))).2.2
 have hj:= ((H B (Costs.one.sub (F.scale r⁻¹)) he).1).scale r⁻¹
 have hg x : r⁻¹ • ((1-g x)⁻¹)=(f x)⁻¹:=by
    have hU:= (Gap_inv h (L x)).1; have hX : (k/r) • (1:Op I)≤1-g x:=by unfold g; rw [sub_sub_cancel,← inv_mul_eq_div, mul_smul]; exact smul_le_smul_of_nonneg_left (L x) (inv_pos.mpr hx).le
                                                                        -- instead
    have hs:= (Gap_inv (div_pos h hx) hX).1; unfold g at *; rw [sub_sub_cancel] at *
    let X: Op I:=(r⁻¹ • f x)⁻¹; have hl: (r⁻¹ • X)*f x=1:=by rw [Algebra.smul_mul_assoc,←Algebra.mul_smul_comm]; exact (live hs).2 -- direction?
    calc
       _ = ((r⁻¹ • X)*f x)*(f x)⁻¹:=by rw [mul_assoc,(live hU).1,mul_one]
       _ = _:= by rw [hl,one_mul]
 rw [← (funext hg)] -- tune or simpa
 exact hj
end Pledge
end YM.CF.BPress.Spin
