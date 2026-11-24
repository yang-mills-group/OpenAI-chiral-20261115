import YM.CF.Cay.Rose
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Cay
open Slate Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
local notation "G"=>SU.group
variable {K:Teller SU.group}{T:Tube SU.group S}
open Matrix Far AnalyticBridge.RelativeLogdet
section
lemma greek(Y:ℝ)(hy:0  ≤  Y)(n:ℕ): Y  ≤  composeCost n Y (1/2) :=by
 let t:ℝ:=n.factorial; unfold composeCost; change Y ≤  t*Y*_; exact (le_mul_of_one_le_left hy (Nat.one_le_cast.mpr (Nat.factorial_pos _))).trans (le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg _) hy) (one_le_pow₀ (by norm_num : (1:ℝ)  ≤  1+1/2))) -- tune
abbrev burn(s x:ℝ)(P:Patch):ℝ:= s*(lamp x+fiery SU.group x P.L)
lemma t_zero(s:ℝ)(P:Patch): Tendsto (fun x=>burn s x P) atTop (𝓝 0):=by
 have hx: Tendsto (fun x=>fiery G x P.L) atTop (𝓝 0):=by
       apply (tally_g G P.L 0 1).congr; intro x; rw [fi]; ring
 simpa only [add_zero,mul_zero] using (lamp_s.add hx).const_mul s
lemma sting (K:Teller G)(P:Patch)(p:P.Branches K.bind G)(n l j:ℕ)(hp:3  ≤  n)(hv:l ≤ 18)(W:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+3))(V:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+2))(D:ℝ)(hD:0 ≤  D):∃ a C v w L M E:ℝ,0<a∧0<C∧0<w∧0<E∧0<M ∧∀ᶠ x in atTop, let s:=burn a x P; temp x  ≤  s ∧ s ≤  1∧0<s∧ s ≤  E ∧ 1000 ≤ radiusB x ∧∀ β∈Set.Icc (y G P.L x/2) (2*y G P.L x), let b:=D*Scales.p G P.L x; 0<β ∧∀{c f:Side}(S:StepData c f)(T:Tube G S),Cert P K S T x →∀ (A: Monk G S)(p:Site c)(s':Chi),  (j+j+101)*radiusB x  ≤  c.val → sizedP G P K S T A.park→ A.key.flags=RG.flags (temp x) A.V→p∉ A.key.dome ((j+2)*radiusB x)→‖A.z‖  ≤  b→ Ready T x ∧ ShardIncome n x v L w T A.key A.park A.V A.k ∧ (∀ v:Mast G c,‖v‖<1→ Fire T x A.park A.k l s n C v) ∧ |coupling β| * (b*C)  ≤  s/2 ∧ (∀ i:Along S,∀ u:Signed,KnotP (lava T A.park x A.k l u i) n (M*s) M E) ∧∃ g R,Lamp T s x A p g R (j+1) n:=by
 obtain ⟨C,e,a,hC,he,ha,H⟩:=score K P p n l j hp hv W V D hD; obtain ⟨m,d,C',hm,hd,hc,H'⟩:= bear K P n p; obtain ⟨M,E,hM,hE,J⟩:=lava_p P K p n l hp V
 refine ⟨a,C,d,m,C',M,E,ha,hC,hm,hE,hM,?_⟩; filter_upwards [H,H',J, PatchReads.reserve K P,(t_zero a P).eventually (ge_mem_nhds hE), (year G P.L).eventually (eventually_gt_atTop (0:ℝ)),Work.E01.radiusB_tendsto.eventually_ge_atTop 1000,eventually_gt_atTop (0:ℝ)] with x hΛ hB hx Hx hz hG hk hY; intro s; obtain ⟨ht,hp,H⟩:= hΛ; refine ⟨hp,H.1,(Work.E09.temp_pos hY).trans_le hp,hz,hk,fun β t=>?_⟩; intro b; obtain ⟨hN,hP⟩:=H.2 _ t; refine ⟨(half_pos hG).trans_le t.1,fun S T hK A p s' hD' hf hF hr hA=>?_⟩
 obtain ⟨g,R,hR,hU,hX⟩:= hP S T hK A s' 0 p hD' hf hF hr hA
 have ht' : temp x ^(l+1)  ≤  s:= (pow_le_of_le_one (temp_nonneg _) (hp.trans H.1) (by omega)).trans hp
 refine ⟨Hx _ _ hK.got hK.size hK.funds.1,hB _ _ hK _ _ _ hF _,hU,le_trans (mul_le_mul_of_nonneg_left (greek _ (mul_nonneg ((norm_nonneg _).trans hA) hC.le) n) (abs_nonneg _)) hN,fun i u=> (hx S T A.park hK hf A.k i u).mono (mul_le_mul_of_nonneg_left ht' hM.le) le_rfl le_rfl,g,R,hR⟩ -- tune hB
end
end YM.CF.Cay
