import YM.SU5.Selected.Chene.Perks
import YM.SU5.Selected.Chene.Loom
import YM.SU5.Selected.Chene.Wrist
/-! The gauge part of retail price, actual frame. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Chene.Perks
open Function Filter MeasureTheory Metric Lattice Wilson RG Tree Precision Next.SectorChange AnalyticBridge.Annulus1AD SectorNext.Vacuum CF.Appel
open Next.Fluctuations Next.Fluctuations.Sector Pressure Pressure.Stores Matrix Trunk Pad Tail FreeResolvent AnalyticBridge.LocalGaussianLaws CF.Neige Next.Rank.Axial
open scoped Topology BigOperators ENNReal Classical MatrixOrder Matrix Kronecker
variable {G:Gauge}(L:ChartRatio G)(p:LocalRatio L)
variable {H:Bed}{c f:Side}{S:StepData c f}

abbrev bulk(c:Side) := (Fintype.card (Site c):ℝ)
abbrev quantity(c:Side) := Fintype.card (Reed c)
abbrev shoots(c:Side) := Fintype.card (axle c).Free
def schedule (c:Side) (H:Bed) (b:ℝ):ℝ:= shoots c* Real.log (Next.SectorChange.spare L b) - atoms0 G /2* Real.log (Trunk.Chene c H (axle c).trunks)
def tariff (T:Tube G S)(F:Forest S.ratio)(q:S.Choices)(b x H:ℝ) := Real.log (prefactor S G b*(Next.SectorChange.spare L b * point G H)^(Fintype.card F.Free)) - Real.log ((baseX T x (bareStores S) F q 1).det)/2
lemma sky_ok (Y:Bed) (h:1<c.val)(u:ℝ)(hp:0<u)(hg: Gap (Y.metric.acts c) u)(hs:(Y.metric.acts c)ᵀ=Y.metric.acts c) : 0<Trunk.Chene c Y (axle c).trunks:= pow_pos (lt_min hp zero_lt_one) (Fintype.card (axle c).Free) |>.trans_le (grain h Y _ _ (legal c (axle c)) (lt_min hp zero_lt_one) (min_le_right ..) (hg.mono (min_le_left ..)) hs)
lemma bulk_edge (c:Side): (quantity c:ℝ)=4*bulk c:=by unfold bulk quantity Reed; rw [Fintype.card_prod,Fintype.card_fin]; push_cast; ring
lemma root_sum (c:Side) : (shoots c:ℝ)=3*bulk c+1:=by unfold shoots; rw [free_count]; push_cast; rfl
lemma balance (S:StepData c f)(F:Forest S.ratio): (Fintype.card F.Free:ℝ)=(shoots f:ℝ)-shoots c+quantity c :=by
 have he: (Fintype.card F.Free:ℝ)+bulk f=quantity f + bulk c:=by exact_mod_cast FlatTree.count_clear F
 rw [root_sum,root_sum,bulk_edge]; rw [bulk_edge] at he; linarith only [he]

variable (T:Tube G S)(F:Forest S.ratio)(K K':Bed)(Q:Towers S.patch.L)(q:S.Choices){u d E C a X η :ℝ}
variable (t:T.up.Bounds T.high u E C)(w:Towers.Diagonal S K K' Q)(hX:Attached K T.up)(fX: Floor K T.high f a X)(t': Gap (K'.metric.acts c) d) (g:(K'.metric.acts c)ᵀ=K'.metric.acts c) (l:Bid.Larger (G:=G) S)
variable [Nonempty G.ColorIndex](i:Bid.Sworn K f G)(a0:0<a)(d0:0<d)

private lemma ash (w v x y f ψ c d K ℓ:ℝ)(k:0≤v)(l:0≤y)(d':0≤c)(h1:|w| ≤ d)(h2:|x| ≤ K)(h3:|f| ≤ K)(h4:|ψ| ≤ K)(Q:ℓ=v+y+c): |-(w/2)+v*x+y*f+c*ψ| ≤  K*ℓ+d/2:=by
 have h:|v*x| ≤ v*K:=by rw [abs_mul,abs_of_nonneg k]; gcongr
 have g:|y*f| ≤ y*K:=by rw [abs_mul,abs_of_nonneg l]; gcongr
 have hp:|c*ψ| ≤  c*K:=by rw [abs_mul,abs_of_nonneg d']; gcongr
 have hv:|-(w/2)| ≤  d/2:=by rw [abs_neg, abs_div,abs_two]; gcongr
 exact (abs_add_le ..).trans ((add_le_add ((abs_add_le ..).trans (add_le_add ((abs_add_le ..).trans (add_le_add hv h)) g)) hp).trans_eq (by rw [Q]; ring))
include w fX t' g l a0 d0
lemma growth_ (x:ℝ) : 1<f.val := by have he:1<c.val:=l.2.2; have h:= S.sizes; rw [h]; exact he.trans_le (Nat.le_mul_of_pos_right _ S.patch.L.property)
include t p i hX
lemma budget(z₁ z₂ :ℝ) (r b c' x :ℝ) (ha:0<r)(hB:0<b)(hC:0<c')
 (j:ℝ)(hj:z₁≤Real.log (baseX T x (bareStores S) F q 1).det - Real.log (treeMatrix G S F K.metric).det)(hk: Real.log (baseX T x (bareStores S) F q 1).det - Real.log (treeMatrix G S F K.metric).det ≤ z₂)
 (m : ℝ) (m0:0 ≤ m) (hm:max (abs z₁) (abs z₂)  ≤ m)
 (he: |Real.log (S.penaltyZ b G)-linkCost L S.kernel b| ≤ j)
 (hv:|Real.log (point G r)| ≤ j)
 (hu: |Real.log c' - Real.log b| ≤j) :
 |tariff L T F q b x r - (schedule L f K b-schedule L c K' c')| ≤ j * ( ( (quantity c:ℝ) + Fintype.card F.Free + ( (shoots c:ℝ) * atoms0 G / 2))) + m /2 :=by
 let u:= Real.log; let C':=Chene c K' (axle c).trunks; let F':=Chene f K (axle f).trunks; let d:= Further.CurvedGaussianJets.Flat.history S F K
 let D:= (baseX T x (bareStores S) F q 1).det
 let V:= S.kernel.penalty; have hV:0<V:=S.kernel.penalty_pos
 have hs:= fX.symmetric.1; have hT: Gap (K.metric.acts f) a:= ⟨fun x=>(fX.uniform.1 x).1⟩
 have hg:0<C':= sky_ok K' l.2.2 _ d0 t' g; have hf:0<F':= sky_ok K (growth_ T K K' Q w fX t' g l a0 d0 x) _ a0 hT hs -- tune
 have hp:D=D:=rfl; have ht:0<d.det:= (green S F K G a a0 l hT hs).det_pos
 have qE:(V^(quantity c))*F'=d.det*C':= quantization S F K K' Q G w a a0 l hT hs _ _ (legal _ _) (legal _ _)
 let Qc:=(quantity c:ℝ); let Wc:=(Fintype.card F.Free:ℝ); let FZ:=(shoots f:ℝ); let FC:=(shoots c:ℝ); let N:=atoms0 G
 have ht0:u (treeMatrix G S F K.metric).det=N*u d.det:=by unfold u; rw [Trunk.colors, det_kronecker,det_one,one_pow,mul_one,Real.log_pow]
 let k:=S.kernel; have hν: Qc*Real.log V+u F' = u d.det+u C':=by
    have he:=congrArg Real.log qE; rw [Real.log_mul (pow_pos hV _|>.ne') hf.ne',Real.log_pow,Real.log_mul ht.ne' hg.ne'] at he; exact he
 let M(x:ℝ):=Real.log (Next.SectorChange.spare L x); let Λ:=Real.log (S.penaltyZ b G); let Φ:= u (point G r)
 have hβ: linkCost L k b= M b - N/2*Real.log V:=rfl
 have hpref : tariff L T F q b x r=Qc*(-Λ)+Wc*(M b+ Φ) - u D/2:=by
    let ζ:=Next.SectorChange.spare L b * point G r; have h1:= spare_pos _ p hB; have h2:= point_p (G:=G) ha
    unfold tariff; rw [Real.log_mul (prefactor_pos b).ne' (pow_pos (mul_pos h1 h2) _|>.ne'),Real.log_pow (Next.SectorChange.spare L b * point G r),Real.log_mul h1.ne' h2.ne', prefactor, Real.log_pow,Real.log_inv]; -- order tune
 have hΛ : M c'-M b= - (N/2)*(u c'-u b):=by unfold M; rw [spare_formula L p.scale hB,spare_formula L p.scale hC]; unfold u N atoms0; ring
 let φ:= u D-N*u d.det; have hφ:|φ| ≤ m:=by
    unfold φ; rw [abs_le]; rw [←ht0]; exact ⟨le_trans (by linarith only [neg_abs_le z₁, (le_max_left _ _ : |z₁| ≤ max _ (abs z₂)).trans hm]) hj, hk.trans ((le_abs_self z₂).trans ((le_max_right ..).trans hm))⟩ -- ht0 defeq φ unfold
 rw [hpref]; change |Qc* (-Λ)+ Wc*(M b+Φ)-u D/2-(FZ*M b-N/2*u F' - (FC*M c'-N/2*u C'))| ≤ _; rw [show Qc*(-Λ)+Wc*(M b+Φ) -u D/2 -_= -(φ/2)+Qc*(linkCost L k b- Λ)+Wc*Φ+(FC*N/2)*(u b-u c') from ?_] -- dummy FC Nop
 swap; · have hW:Wc=FZ-FC+Qc:= balance S F; rw [hW,hβ]; unfold φ; linear_combination N/2 * hν + FC * hΛ
 rw [abs_sub_comm] at he hu
 exact ash φ Qc (linkCost L k b-Λ) Wc Φ (u b-u c') (FC*N/2) m j ((quantity c:ℝ)+(Fintype.card F.Free:ℝ)+shoots c * atoms0 G/2) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by norm_num)) hφ he hv hu rfl
end YM.Chene.Perks

#print axioms YM.Chene.Perks.budget
