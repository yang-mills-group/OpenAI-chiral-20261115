import YM.SU5.Relativistic.Ruffs
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Mosaic
open Function Finset Filter MeasureTheory Lattice Wilson Fixed.Pivots GaugeFlux
open scoped Matrix BigOperators
variable {N C: Side}(L:Ratio C N)
local notation "W_"=> L.count
local notation "T_"=> Site C
local notation "F_"=> Site N
local notation "P_"=> Site L.count
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
open RG RG.PathData Work.F03 Pharos
local notation "J"=> Link N
local notation "O"=> Face (Per N)
local notation "V"=> Site C
variable (G: Gauge)(p:Clip){σ a b:ℝ}(B:PathData G)
open scoped Classical
local notation "S"=> Config G N
open Pressure (temp radiusB)
open Precision Next.SectorChange
variable (D:ℕ)(Λ:ChartRatio G)(l:LocalRatio Λ)(X:B.Bounds p σ a b)(h:2≤ C.val)
local notation "δ"=> (Fintype.card G.ColorIndex:ℝ)
def oppZ (G:Gauge)(n:Side)(k:Bed) (Λ:ChartRatio G)(β:ℝ):= (3*(Fintype.card (Site n):ℝ)-3) * Real.log (spare Λ β) - (1/2)*Real.log (costDet G k n)
def oppo (r:ℝ):=4*δ*(Real.log (1+r)-Real.log (1-4*r))
def npm(x:ℕ):ℝ:=1+ (4*x^4*(Fintype.card G.ColorIndex):ℝ)*(5*(x:ℝ)+1)^2
def pound (p:Clip)(z K r:ℝ)(W:ℕ):= Real.log (Fintype.card Signed)+ Real.log 2*2 + 4*W^3*Real.log K+ (4*W^3*δ)*Real.log (Berry p z r)+
 (32*(2*(D:ℝ)+2)*W^3*δ)*Real.log (1+Berry p z r / (p.direct / npm G W))
lemma puffSoon (ε:ℝ)(u:0<ε)(p:Clip)(z K r:ℝ)(h:0<r) :∀ᶠ W:ℕ in atTop,pound G D p z K r W≤ ε*(W:ℝ)^4:=by
 let B:= Berry p z r; let U(x:ℕ):=1+B/(p.direct/npm G x)
 have he:=p.quadratic_pos; have hp:0<B:=by unfold B Berry; positivity
 have hV: Tendsto (fun x:ℕ=> Real.log (U x)/(x:ℝ)) atTop (𝓝 0):=by
    let C':ℝ:=1+B/p.direct*(1+4*δ*(6:ℝ)^2);
    have hs:0<C':=by unfold C'; positivity
    have hf:Tendsto (fun i:ℕ=> (Real.log C'+6*Real.log i)/(i:ℝ)) atTop (𝓝 0):=by
       have ht:Tendsto (fun i:ℕ=>Real.log (i:ℝ)/(i:ℝ)) atTop (𝓝 0):=by simpa only [pow_one] using! ((Real.isLittleO_pow_log_id_atTop (n:=1)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop)
       simp_rw [add_div,mul_div_assoc, div_eq_mul_inv (Real.log C') (_:ℝ)]; simpa only [mul_zero,add_zero,comp_apply] using! ((tendsto_inv_atTop_zero (𝕜:=ℝ)).comp tendsto_natCast_atTop_atTop|>.const_mul (Real.log C')).add (ht.const_mul 6) -- tune
    refine squeeze_zero' (Eventually.of_forall fun i=> div_nonneg (Real.log_nonneg ?_) (by positivity)) ?_ hf
    · unfold U; refine le_add_of_nonneg_right (by unfold npm; positivity)
    filter_upwards [eventually_ge_atTop (1:ℕ)] with i p'; have ht:(1:ℝ)≤ i:=by exact_mod_cast p'
    have hb:U i≤C'* i^6:=by
       let w:ℝ:=i; have ht':1≤ w:= ht; have hz:1≤ w^6:= one_le_pow₀ ht'
       have hv: npm G i≤ (1+4*δ*6^2)*w^6:=by
          unfold npm; change 1+(4*w^4*δ)*(5*w+1)^2≤_; have hi:(5*w+1)^2≤ 36*w^2:=by nlinarith only [ht']
          linarith only [hz,mul_le_mul_of_nonneg_left hi (show 0≤4*w^4*δ by positivity)]
       unfold U; rw [show B/(p.direct/npm G i)=B/p.direct*npm G i from (by field_simp)]; change 1+B/p.direct*npm G i≤C'*w^6; unfold C'; linarith only [mul_le_mul_of_nonneg_left hv (show 0≤B/p.direct by positivity),hz]
    apply div_le_div_of_nonneg_right _ (by positivity); apply le_trans (Real.log_le_log (show 0<U i by unfold U npm; positivity) hb); rw [Real.log_mul hs.ne' (by positivity), Real.log_pow]; norm_num
 let M(x:ℕ):ℝ:= x; have hx:Tendsto M atTop atTop:=tendsto_natCast_atTop_atTop; let N':= (fun i:ℕ=> Real.log (Fintype.card Signed:ℝ)+Real.log 2*2); let Z:= 4* Real.log K+ 4*δ*Real.log B; let W:=32*(2*(D:ℝ)+2)*δ
 have ht:Tendsto (fun i:ℕ=> pound G D p z K r i/(i:ℝ)^4) atTop (𝓝 0):=by
   let g(i:ℕ):= N' i*(M i)^(-4:ℤ)+Z*(M i)⁻¹+ W*(Real.log (U i)/M i)
   have hh:= (((tendsto_inv_atTop_zero (𝕜:=ℝ)).comp ((tendsto_pow_atTop (by decide :4≠0)).comp hx)|>.const_mul (N' 0)).add (((tendsto_inv_atTop_zero (𝕜:=ℝ)).comp hx).const_mul Z)).add (hV.const_mul W)
   simp only [mul_zero,add_zero] at hh; refine hh.congr' ?_; filter_upwards [eventually_gt_atTop (0:ℕ)] with i hi; unfold N' Z W U B; dsimp only [Function.comp_apply,pound,M]; field_simp; ring -- tune powers
 filter_upwards [ht.eventually (ge_mem_nhds u),eventually_gt_atTop (0:ℕ)] with i h hv; exact (div_le_iff₀ (by positivity)).mp h
lemma feePos (β θ:ℝ)(u:LocalRatio Λ)(v:0<θ)(x:0<β)(A:Side):0< fee G A β Λ θ (DueQ G B D X A).det:= mul_pos (pow_pos (spare_pos Λ u x) _) (inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos (pow_pos v _) (screenP G B D X A|>.1.det_pos))))
variable {a' b':ℝ}
set_option maxHeartbeats 1200000 in
lemma ticketPrice (H:Bed)(A:Floor H p N a' b')(x:Attached H B)(r β K:ℝ)(u:1≤ K)(f:0<r)(v:r<1/4)(b:0<β)(h:LocalRatio Λ)(pN:2≤N.val) (e:2 ≤ C.val)(ht:(1+1/r)*vane σ a D≤r*p.direct): Real.log (pubB L G p B D Λ X K β r)≤ oppZ G N H Λ β+ oppo G r*(N.val:ℝ)^4+(C.val:ℝ)^4*pound G D p a K r L.count.val:=by
 have hv:0<1-4*r:=by linarith
 have hi:=bulky L G B D X f A x ht e pN; let T:= costDet G H N; let B':=Berry p a r; let ν:ℕ:=Fintype.card (Fresco G W_); let Y:= DueQ G B D X W_; let n:ℝ:= L.count.val; let g:= C.val^4; let m:= (C.val:ℝ)^4; have hc:1≤ m:= one_le_pow₀ (by exact_mod_cast (Nat.succ_le_of_lt (show 0<C.val from C.property)))
 let U:=npm G L.count.val; have hp:hatp G W_= U:=by unfold hatp U npm limit; push_cast <;> rfl -- tune
 have hf := p.quadratic_pos; have hx: 1 ≤ B':= by unfold B' Berry; apply le_add_of_nonneg_right; positivity
 let α:ℝ:=1+B'/(p.direct/U); have hF:1 ≤ α:= by
    unfold α; apply le_add_of_nonneg_right; have hu:0≤U:=by rw [←hp]; unfold hatp; positivity
    positivity -- tune
 have hs:0<T:=(fairDet G H pN A X x).1.det_pos -- remove
 have hY:= (screenP G B D X W_).1.det_pos
 set w:= wires L
 let y:= (32*(2*D+2)*L.count.val^3*Fintype.card G.ColorIndex)
 let σK:=(4*C.val^4*L.count.val^3*Fintype.card G.ColorIndex)
 have hZ: Real.log T ≤ ( (ν:ℝ)*Real.log (1+r)+Real.log Y.det+(y:ℝ)*Real.log α)*m+(σK:ℝ)*Real.log B' :=by
    apply le_trans (Real.log_le_log hs hi); unfold boundD priceB Runt; rw [hp]; change Real.log (((1+r)^ν * Y.det*α^y)^g *B'^σK) ≤ _; have ht:0<Y.det:=hY; rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) ht.ne']; simp only [Real.log_pow]; rw [mul_comm (g:ℝ),show (g:ℝ)=m by unfold g m; push_cast <;> rfl] -- tune
 let s:=spare Λ β; have h0:0<s:= spare_pos _ h b; let θ:=fee G W_ β Λ (1-4*r) Y.det; have hz:0<θ:=feePos G p B D Λ X _ _ h hv b W_
 have hθ:Real.log θ=(livelies W_).card*Real.log s- (ν*Real.log (1-4*r)+ Real.log Y.det)/2:=by unfold θ fee; have hy:0<Y.det:=hY; have ht:=pow_pos hv ν; have hh:=mul_pos ht hy; change Real.log (s^_* _)=_; rw [Real.log_mul (pow_pos h0 _|>.ne') ((inv_pos.mpr (Real.sqrt_pos.mpr hh))|>.ne'),Real.log_pow,Real.log_inv,Real.log_sqrt hh.le,Real.log_mul ht.ne' hy.ne',Real.log_pow]; rw [show Fintype.card (Lo W_)=(livelies W_).card from Fintype.card_coe _]; unfold ν s; ring
 let D':ℝ:=Fintype.card Signed; have hg:D'≥1:=by unfold D'; exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α:=Signed))) -- zero<? Nat cast
 have hδ:(w.card:ℝ)+(livelies W_).card*m=3*Fintype.card (Site N)- (3:ℝ):=by
    have hu := viva_card L; have hv := congrArg Finset.card (vivot L); rw [card_union_of_disjoint (disjoint_left.mpr fun {x} p t=> (mem_sdiff.mp p).2 t), batch_card, hu] at hv
    have hx:= countLess (Y:=N); have hh:= card_compl_add_card (pivots N); rw [hx] at hh; change _+_= Fintype.card (Site N × Axis) at hh; rw [Fintype.card_prod,Lattice.site_card,show Fintype.card Axis=4 from rfl,←hv] at hh; rw [site_card]; unfold w m; have hQ:= congrArg (fun i:ℕ=> (i:ℝ)) hh; push_cast at hQ ⊢; linarith only [hQ]
 have hr:(ν:ℝ) ≤ 4*n^4*δ:=count_f G W_
 have hm:(w.card:ℝ) ≤ 4*m*n^3:=by have h:= woolV L; unfold m n w; exact_mod_cast h
 have hx' : (N.val:ℝ)^4= m*n^4:=by rw [L.exact_size]; push_cast; unfold n m; ring
 unfold pubB oppZ; change Real.log (D' * ((2:ℝ)^g*(K*s)^w.card)*(2*θ)^g)≤ ((3*(Fintype.card (Site N):ℝ) -3)*Real.log s-(1/2)*Real.log T)+_+_
 rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow]; rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity)]; rw [hθ,← hδ,hx']; -- tune momentum
 -- algebra
 let v':= Real.log (1+r)-Real.log (1-4*r); have he:0 ≤ v':= sub_nonneg.mpr (Real.log_le_log hv (by linarith)); let Z:= Real.log B'; have ht:0≤ Z:=Real.log_nonneg hx; have hu:0 ≤ Real.log α:= Real.log_nonneg hF
 have hp' : (σK:ℝ)=4*m*n^3*δ:=by unfold σK m n; push_cast <;> ring
 have hw': (y:ℝ)=32*(2*(D:ℝ)+2)*n^3*δ:=by unfold y n; push_cast <;> ring
 have hv:0 ≤ (ν:ℝ):=Nat.cast_nonneg _
 unfold pound oppo; rw [show (g:ℝ)=m by unfold g m; push_cast <;> rfl]
 -- provide v coefficients
 change _ ≤ _+ 4*δ*v'*(m*n^4)+m*(Real.log D'+Real.log 2*2+4*n^3*Real.log K+(4*n^3*δ)*Z+(32*(2*(D:ℝ)+2)*n^3*δ)*Real.log α)
 -- tune hc hv
 have k':(ν:ℝ)*v' ≤ 4*n^4*δ*v':=mul_le_mul_of_nonneg_right hr he
 have he':0≤ m:=by positivity
 rw [hp',hw'] at hZ; unfold v' Z at *
 linarith only [hZ,mul_le_mul_of_nonneg_right k' he',mul_nonneg (mul_nonneg ht (show 0 ≤ 4*m*n^3*δ by unfold n; positivity)) zero_le_one,mul_nonneg hu (show 0 ≤ m*(32*(2*(D:ℝ)+2)*n^3*δ) by unfold n; positivity),mul_le_mul_of_nonneg_right hm (Real.log_nonneg u),mul_le_mul_of_nonneg_left hc (Real.log_nonneg hg),mul_nonneg (mul_nonneg hv he) he']
end YM.CF.Papyrus.Mosaic
