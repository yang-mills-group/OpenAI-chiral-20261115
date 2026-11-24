import YM.CF.Esti.River
import YM.CF.Vol.Celt
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {β e a':ℝ} -- tune
variable {F:Tree.Forest S.ratio}{Y: LinkArray G (Frozen A x F)}
abbrev axl (p:Support c)(x:Directions G c) : Directions G c:=fun i=> if i.1∈halo 15 p ∨ i.1+Lattice.step i.2∈halo 15 p then 0 else x i
lemma curtainP {v:E→ Directions G c}(p:∀ i, axl A.flags (v i)=v i): ∀ᶠ i in 𝓝 x', Agrees (halo 15 A.flags) (increment V (v i)) (increment V (v x')):=by
 apply Eventually.of_forall; intro a x l _; rw [←p a,←p x']; unfold increment axl; change x.1 ∈ halo 15 A.flags at l; rw [if_pos (Or.inl l),if_pos (Or.inl l)]
abbrev tutP(G':Gauge)(n:ℕ) (K:ℝ):ℝ:= Jet.composeCost n K 1
lemma bevel {V: Config G c}{p: E→L[ℝ] Directions G c} {F: Config G c→ Prices G (Active A x F)} (h:Allows n (F ∘ Vmove x V) 0 K)(hp:‖p‖≤1): Allows n ((F ∘ Vmove x V)∘ p) 0 (Jet.composeCost n K 1):=Allows.comp (f:=p) ((map_zero p).symm ▸ h) (allows_linear hp (by rw [map_zero,norm_zero]; exact zero_le_one))
lemma ready_heat (Y: LinkArray G (Frozen A x F))(R: LogArray G (Active A x F))(t:ℝ)(W:MossX n r x A F T V k C d t q)(K:ℝ)(hx:‖R‖≤K)(hp:0 ≤ C):
 let g:=fun y:Directions G c=>liftN T x (Vmove x V y) k A F q d Y r
 let f:=fun y:Directions G c=> realP β T F A (Vmove x V y) k x r q d Y R
 Allows n g 0 (C*t) ∧ Allows n f 0 (C*t+ |coupling β| * (2^n*C*K)):=by
 intro f g; obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩:= W.jumps Y; refine ⟨h2,?_⟩
 let Q(y: Directions G c):= credW T A F k q d x Y r (Vmove x V y); let N:Allows n (fun y:Directions G c=>Newt.paintO (Q y)) 0 C := h5
 have he: Allows n (fun y=> Q y *ᵥ tape.symm R) 0 (2^n*C*K):= airK N (allows_const _ ((loomP R).trans hx)) -- tune PaintO!. ranQ
 exact h2.add (he.smul _)
lemma leavesJ {f:E→ Prices G (Slots S)}(p:Allows n f x' K):Allows n (tape ∘ f) x' (Push.Uniform.shade G*K) :=p.linear (Push.Uniform.tint G _).toContinuousLinearMap (by apply ContinuousLinearMap.opNorm_le_bound _ (Push.Uniform.shade_pos _).le; exact fun p=>Push.Uniform.tint_le p) -- tune tune unused
lemma shelJ {g:E→ Prices G (Active A x F)}(p:Allows n g x' K):∀ i:Active A x F,Allows n (fun y=> tape (g y) i) x' (Push.Uniform.shade G*K):=by
 have hp:Allows n (fun y=> tape (g y)) x' (Push.Uniform.shade G*K):= p.linear (Push.Uniform.tint G _).toContinuousLinearMap (by apply ContinuousLinearMap.opNorm_le_bound _ (Push.Uniform.shade_pos _).le; exact fun p=>Push.Uniform.tint_le p)
 intro i; exact (hp.linear (ContinuousLinearMap.proj i) (by apply ContinuousLinearMap.opNorm_le_bound _ (show 0 ≤ (1:ℝ) from zero_le_one); exact fun p=> (norm_le_pi_norm p i).trans_eq (one_mul _).symm)).mono (one_mul _).le
lemma compare_v (M:Gauge)(L:Side)(x:ℝ)(h:β ∈Set.Icc (Scales.y M L x/2) (2*y M L x))(hp:0<y M L x):coupling β ≤2*Scales.g M L x∧Scales.g M L x≤ 2*coupling β:=by
 let y:=Scales.y M L x
 have ht:y/2 ≤ β∧β≤2*y:= h; have hB:0<β:= (half_pos hp).trans_le h.1
 have hx:=Real.sqrt_pos.mpr hp; have ht1:=Real.sqrt_pos.mpr hB; have hh:=Real.sq_sqrt hB.le; have hy:=Real.sq_sqrt (show 0 ≤ y from hp.le)
 change (Real.sqrt β)⁻¹ ≤ _∧(Real.sqrt y)⁻¹≤_; change _≤2*(Real.sqrt y)⁻¹∧_≤2*(Real.sqrt β)⁻¹; change 0<Real.sqrt y at hx; constructor<;> rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)] <;> nlinarith [ht.1,ht.2] -- tune
-- E mask.R Kin.Ex.Pr.
variable {z:E → Config G c}{rE:E→ Prices G (Active A x F)}
lemma tock (n:ℕ):∃ K:ℝ, 1≤K∧∀ {c f:Side} {S: StepData c f} (V:Config G c)(x:ℝ), temp x ≤ 1 → ∀ (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E](z:E→L[ℝ] Directions G c), ‖z‖ ≤ 1 →
 FuelG E (Vmove x V ∘ z) 0 n K ∧∀ (A:Stores S)(F:Forest S.ratio)(Y: LinkArray G (Frozen A x F))(u:E→ Prices G (Active A x F)), (∀ i:Active A x F, Allows n (fun y=> tape (u y) i) 0 1) → FuelG E (treeF Y (Vmove x V ∘ z) u) 0 n K:=by
 obtain ⟨C,h,H⟩:=Push.Uniform.exp_receipt G n; let K:= Jet.composeCost n C 1; let m:= SU.group.colorScale; let Z:=purM G n*K*m; let X:=max Z m; let D:=max X (purM G n*K*X); have hm:m≤D:= (le_max_right ..).trans (le_max_left ..); let R:=max 1 D
 refine ⟨R,le_max_left ..,@fun c f S V x hp E _ _ z hz=>?_⟩; let V':= (Vmove x V∘ z)
 have ht(v:E→SU.group.Color)(p:Allows n v 0 1):grantB n (SU.group.lieExp ∘ v) 0 K:=by
    let H:= H _ p.value; refine Jet.Allows.comp (g:=SU.group.mat ∘ SU.group.lieExp) (f:=v) (K:=C) ⟨H.1.of_le le_top,H.2⟩ p
 have hx (i:Bond c):grantB n (fun y=>V' y i) 0 X:=by
    let L: E→L[ℝ] SU.group.Color:=(temp x) • ((ContinuousLinearMap.proj i).comp z)
    have h:‖L‖≤1:=by
       apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
       intro w; rw [one_mul]; change ‖temp x • (z w i)‖≤ _; rw [norm_smul,Real.norm_of_nonneg (temp_nonneg _)] -- tune
       exact (mul_le_of_le_one_left (norm_nonneg _) hp).trans ((norm_le_pi_norm (z w) i).trans ((z.le_opNorm w).trans (mul_le_of_le_one_left (norm_nonneg _) hz)))
    exact (gall (ht L (allows_linear h (by rw [map_zero,norm_zero]; norm_num))) (gan _)).mono (le_max_left ..)
 refine ⟨fun i=> (hx i).mono ((le_max_left ..).trans (le_max_right ..)),fun A F Y u p i=>?_⟩; by_cases g:i∈ F.trunks
 · apply ((gan (1:SU.E)).mono (hm.trans (le_max_right 1 D))).germ; exact Eventually.of_forall fun j=>congrArg SU.group.mat (F.on_tree _ ⟨i,g⟩).symm -- tune param
 let t:F.Free:=⟨i,g⟩; by_cases h:chill A x F t
 · let b: Frozen A x F:=⟨t,h⟩; apply ((gan (Y b)).mono (hm.trans (le_max_right 1 D))).germ; exact Eventually.of_forall fun w=> congrArg SU.group.mat (held_physical x A F (V' w) Y (u w) b).symm
 let b:Active A x F:=⟨t,h⟩; have hv: grantB n (fun y=>replica S.ratio (V' y) i) 0 X:=by unfold replica; split; exact (gan _).mono (le_max_right ..); exact hx _
 exact ((gall (ht _ (p b)) hv).mono ((le_max_right ..).trans (le_max_right 1 D))).germ (Eventually.of_forall fun w=> congr_arg SU.group.mat (clear_physical x A F (V' w) Y (u w) b).symm)
end YM.CF.Esti
