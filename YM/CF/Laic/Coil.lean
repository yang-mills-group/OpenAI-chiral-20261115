import YM.CF.Laic.Pock
set_option autoImplicit false
noncomputable section
namespace YM.CF.Laic
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n c:Side}{ι:Type}[Fintype ι]{k m:ℕ}{Z:Positions ι→Bkg (More n)}{a b:ℝ}
private def jobL (m j:ℕ):TaxX m group→L[ℝ] ContinuousMultilinearMap ℝ (fun _: Fin j=> Fin m→group.Color) ℂ:= (show TaxX m group→ₗ[ℝ] _ from {
 toFun:=fun u=> iteratedFDeriv ℝ j (fun y=>u y) 0
 map_add':=fun u v=> iteratedFDeriv_add_apply u.contDiff.contDiffAt v.contDiff.contDiffAt
 map_smul':=fun c u=>by
    change iteratedFDeriv ℝ j (fun y=> c • u y) 0= c • iteratedFDeriv ℝ j (fun y=>u y) 0
    exact iteratedFDeriv_const_smul_apply' u.contDiff.contDiffAt }).toContinuousLinearMap
lemma mule (k m:ℕ): ∃ C:ℝ,0≤C ∧∀ U:TaxX m SU.group, Allows k U 0 (C*‖U‖):=by
 let C:= ∑ i∈Finset.range (k+1),normL (jobL m i); refine ⟨C,sum_nonneg (fun _ _=> norm_nonneg _), fun U=> ⟨U.contDiff.contDiffAt,fun i h=>?_⟩⟩
 let he:= single_le_sum (f:=fun i=>normL (jobL m i)) (fun _ _=> norm_nonneg _) (Finset.mem_range.mpr (show i<k+1 by omega)); exact ((jobL m i).le_opNorm U).trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
lemma eGrowth(k M:ℕ){A b C d:ℝ}(p:0<b)(h:0≤C)(g:0≤A)(v:k*b≤ d):composeCost k C (A*Real.exp (b*M))≤ composeCost k C A *Real.exp (d*M):=by
 unfold composeCost; have hx : 1+A*Real.exp (b*M)≤ (1+A)*Real.exp (b*M):=by rw [add_mul,one_mul]; apply add_le_add_left; exact Real.one_le_exp (by positivity)
 calc
   _ ≤ _:= by
      apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hx k) (by positivity : (0:ℝ)≤ (k.factorial:ℝ)*C))
      rw [mul_pow,←mul_assoc, ← Real.exp_nat_mul]; apply mul_le_mul_of_nonneg_left _ (by positivity); apply Real.exp_monotone; rw [←mul_assoc]; gcongr
lemma channelF(k:ℕ)(t:0<a)(y:0≤b) :∃ C:ℝ,0≤ C∧∀{n:Side}{Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y]{Z:Y→Bkg (More n)}, EnvM k Z 0 b→ Z 0=1→∀ (x z:HopK n)(w:ℕ), separation (terse x) (terse z)≤w→∀ i j:Slot, Allows k (fun y=>walkB x z (Z y) i j) 0 (C*Real.exp (a*w)):=by
 let s:= a/(k+1:ℝ); have hs:0<s:=by unfold s; positivity
 obtain ⟨C,hc,H⟩:=pf_b k s hs y; let F:=(coordL (k:=SU.F)).symm.toContinuousLinearMap; let X:=‖F‖*C; have hx:0≤X:=by unfold X; positivity
 have hv: ContDiffAt ℝ ω triple (fund 1):=by -- refactor later
   refine Nacre.tort.mpr ?_; rintro ⟨i,r⟩ ⟨j,s⟩; have he (i j:SU.F): ContDiffAt ℝ ω (fun p:Op SU.F=> p i j) (fund 1):=Nacre.tort.mp contDiffAt_id i j; refine ContDiffAt.mul contDiffAt_const ?_; cases r with
   | inl a=> cases s with
      | inl b=> change ContDiffAt ℝ ω (fun p=>SU.each p (.inl a) (.inl b)) _; simp_rw [each,Join.both,Matrix.fromBlocks_apply₁₁,ExTwo.wedge_entry]; exact ((he _ _).mul (he _ _)).sub ((he _ _).mul (he _ _))
      | inr b=> exact contDiffAt_const
   | inr a=> cases s with
      | inl b=> exact contDiffAt_const
      | inr b=> exact Complex.conjCLE.contDiff.contDiffAt.comp _ (he a b)
 obtain ⟨r,hr,V⟩:=exists_allows (s:={fund (1:E)}) isCompact_singleton (f:=triple) (fun x hx=> Set.mem_singleton_iff.mp hx ▸ hv) k
 let T:= (coordL (k:=Slot)).toContinuousLinearMap; let A:=composeCost k r X
 refine ⟨‖T‖*A,by unfold A composeCost; positivity,?_⟩; intro n Y _ _ Z p e x z w d i j; let V'(y):= fund (travel (Z y) (terse x) (shiftH (terse x) (terse z)))
 have hz:0≤C*Real.exp (s*w):=by positivity
 have hh: Allows k V' 0 (X*Real.exp (s*w)):= (((allows_pi hz fun i:SU.F=> allows_pi hz fun j:SU.F=> H p (terse x) (terse z) w d i j).linear F le_rfl).mono (le_of_eq (mul_assoc _ _ _).symm))
 have he:V' 0=fund 1:=by unfold V'; rw [e]; congr; exact (by simpa only [link_one] using (Push.stroll_zero (G:=group) (shiftH (terse x) (terse z)) (terse x))) -- tune congr
 let B:= composeCost k r (X*Real.exp (s*w)); let f:= T ∘ triple ∘ V'; have hf:Allows k f 0 (‖T‖*B):= ((V (V' 0) (Set.mem_singleton_iff.mpr he)).comp hh).linear T le_rfl
 let u:=(ContinuousLinearMap.proj (φ:=fun _:Slot=> ℂ) (R:=ℝ) j).comp (ContinuousLinearMap.proj i (φ:=fun _:Slot=> Slot→ℂ) (R:=ℝ)); have hx':‖u‖≤ 1:= u.opNorm_le_bound zero_le_one fun f=>by rw [one_mul]; exact (norm_le_pi_norm (f i) _).trans (norm_le_pi_norm f _)
 apply (hf.linear u hx').mono; rw [one_mul,mul_assoc]; apply mul_le_mul_of_nonneg_left (eGrowth k w hs hr hx ?_) (norm_nonneg _); have hh: s*((k:ℝ)+1)=a:=by unfold s; field_simp
 linarith
end YM.CF.Laic
