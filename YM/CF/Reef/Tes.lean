import YM.CF.Reef.Aqua
import YM.Next.STATIONARY.Level.SliceGate
set_option autoImplicit false
noncomputable section
namespace YM.CF.Reef
open Function Filter NormedSpace SU Spire Lattice Wilson RG Finset Precision Exterior Tree
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace ContDiff
variable {R U:PathData SU.group} {p q:Clip}{B C D A E σ δ η α:ℝ}{c f:Side}{S:StepData c f}
variable {F:Forest S.ratio}{z:fieldDir SU.group c 1 → AxisChart SU.group F}
def cloak(ι:Type)[Fintype ι]: (ι→Ox) →L[ℝ] (ι→Ox):= ContinuousLinearMap.pi fun i=> frolic.toContinuousLinearMap.comp (ContinuousLinearMap.proj i)
lemma cloak_c(ι:Type)[Fintype ι](x:ι→Ox): cloak ι (cloak ι x)=x:= funext fun _=> fiz2 _
lemma repr_c (x:fieldDir SU.group c 1): represent (cloak _ x)=echo (represent x):=by funext i; simp only [represent,RG.increment,echo, Pi.one_apply,mul_one]; exact cool_a _
lemma lift_c {g: Ratio c f}(F:Forest g)(x:Config SU.group c)(b:AxisChart SU.group F): lifting F (echo x) (cloak _ b)=echo (lifting F x b):=by
 funext i; by_cases hi:i∈F.trunks
 · rw [show lifting F (echo x) _ i=1 from F.on_tree _ ⟨i,hi⟩,echo,show lifting F x b i=1 from F.on_tree _ ⟨i,hi⟩,map_one]
 have ht A (v:AxisChart SU.group F): lifting F A v i=SU.group.lieExp (v ⟨i,hi⟩)*replica g A i:= F.off_tree _ ⟨i,hi⟩
 rw [ht,echo,ht,map_mul]; congr 1
 · exact cool_a _
 unfold replica; split
 · rw [map_one]
 rfl
lemma tested_c (h:S.patch.Branches S.kernel SU.group)(g:R.Bounds p σ A B) (r:Rare R)(x:fieldDir SU.group c 1)(F:Forest S.ratio)(y:AxisChart SU.group F)(j:S.Choices):tested F j p R (cloak _ x) (cloak _ y) = tested F j p R x y:=by
 simp only [tested]; rw [repr_c, lift_c, lore r g]; unfold noiseTaylor; rw [(proceeds h _ j).1]; unfold echo; simp only [←map_inv, ←map_mul,cold]
lemma station_cp(h:S.patch.Branches S.kernel SU.group)(g:R.Bounds p σ A B) (r:Rare R)(t:Critical F p R z)(w:PriceGap F p R η)(k:0<η):∀ᶠ x in 𝓝 0,z (cloak _ x) = cloak _ (z x):=by
 let U : (F.Free→Ox) →L[ℝ] (F.Free→Ox):=cloak _
 let W : fieldDir SU.group c 1 →L[ℝ] fieldDir SU.group c 1 := cloak _
 let i:S.Choices:= Classical.arbitrary _; let E:=tested F i p R; let hz:Tendsto z (𝓝 0) (𝓝 0):= t.1 ▸ t.2.1.continuousAt.tendsto; have hw:Tendsto W (𝓝 0) (𝓝 0):=by convert W.continuous.tendsto 0; simp
 have ht:Tendsto U (𝓝 0) (𝓝 0):=by convert U.continuous.tendsto 0; simp
 have hv : z =ᶠ[𝓝 0] U∘ z ∘ W:=by
    apply Work.F05.station_unique (F:=tested F i p R) (t.2.2 i).1 (fun i' hi=> by by_contra y; exact (Work.F05.tested_diag k w i i' y).ne' hi) hz (ht.comp (hz.comp hw)) ((t.2.2 i).2.mono fun x hx=>hx.fderiv)
    filter_upwards [hw.eventually (t.2.2 i).2] with x hx; let A:=z (W x); rw [show tested F i p R x= E (W x) ∘ U from funext fun i'=> (tested_c h g r x F i' i).symm]; change fderiv ℝ ((E (W x))∘ U) (U A)=0; have he : HasFDerivAt (E (W x)) (0: AxisChart SU.group F→L[ℝ] ℝ) (U (U A)):=by rw [show U (U A)=A from cloak_c ..]; exact hx
    rw [(he.comp (U A) U.hasFDerivAt).fderiv, ContinuousLinearMap.zero_comp]
 filter_upwards [hv] with x hi; change z x=U (z (W x)) at hi; rw [hi, cloak_c]
-- jet specializing
lemma gear {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (L:X→L[ℝ] X)(f:X→ℝ)(h:ContDiffAt ℝ ω f 0)(j:ℕ): iteratedFDeriv ℝ j (f ∘ L) 0=(iteratedFDeriv ℝ j f 0).compContinuousLinearMap fun _=> L:=by
 -- maybe X aliases Trace; use Next.Foundations.jets_linear
 rw [Next.Foundations.jets_linear _ (h.of_le le_top)]
lemma reserve (h:S.patch.Branches S.kernel SU.group)(g:R.Bounds p σ A B)(e:U.Bounds q δ C E) (r:Rare R)(t:Critical F p R z)(w:PriceGap F p R η)(k:0<η)(f:ClassicalMatch F p q R U z):ClassicalMatch F p q R (solvent U) z:=by
 intro j ht i; obtain ⟨hk,hv,H⟩:= f j ht i
 let W: fieldDir SU.group c 1→L[ℝ] fieldDir SU.group c 1:= cloak _
 let f':=fun x:fieldDir SU.group c 1=> tested F i p R x (z x); let b:=fun x:fieldDir SU.group c 1=>mainTerm q U (represent x); let u:= (2:ℝ)⁻¹
 have ht:f'∘ W=ᶠ[𝓝 0] f':= (station_cp h g r t w k).mono fun x y=> by unfold f' Function.comp; dsimp only; rw [show z (W x)= _ from y]; exact tested_c h g r x F _ i
 have hl: ContDiffAt ℝ ω (b ∘ W) 0:=(show ContDiffAt ℝ ω b (W 0) from by rw [map_zero]; exact hv).comp _ W.contDiff.contDiffAt
 rw [SameJet,show (fun x: fieldDir SU.group c 1=> mainTerm q (solvent U) (represent x))= u • (b+(b∘ W)) from ?_]
 · have hd:ContDiffAt ℝ ω b 0:=hv; change ContDiffAt _ _ f' _ ∧ _; refine ⟨hk,((hd.add hl).const_smul u),?_⟩; change iteratedFDeriv _ _ f' _=_; have hs: iteratedFDeriv ℝ j f' 0=iteratedFDeriv ℝ j b 0:=H
   rw [iteratedFDeriv_const_smul_apply (show ContDiffAt ℝ ↑j (b+(b∘W)) 0 from (hd.add hl).of_le le_top),iteratedFDeriv_add_apply (hd.of_le le_top) (hl.of_le le_top),gear W b hd j,←hs, ← gear W f' hk j, (ht.iteratedFDeriv ℝ j).eq_of_nhds,←two_smul ℝ,smul_smul,show u*2=1 by unfold u; norm_num,one_smul] -- syntax
 funext x; rw [splits e]; simp only [Pi.smul_apply,Pi.add_apply,Function.comp_apply,b]; rw [show represent (W x)=echo (represent x) from repr_c x]; change _=(2:ℝ)⁻¹*_; ring
lemma rode {T:ChartRatio SU.group} (h: FiniteBound F R U p q α T z C D A) : FiniteBound F R (solvent U) p q α T z C D A:= ⟨h.branch,h.born,h.classicalResult,h.wave_price⟩
end YM.CF.Reef
