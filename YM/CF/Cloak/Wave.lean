import YM.CF.Cloak.Bud
import YM.CF.Rill.Oboe
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cloak
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
open Forge Reine Rill
open Rill
local notation "m₀"=> SU.group.colorScale
section smooth
variable {Y Z:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y][NormedAddCommGroup Z][NormedSpace ℝ Z][FiniteDimensional ℝ Z]
open Cay AnalyticBridge.RelativeLogdet.Ink
-- lift Tang along inertia
variable {F₁:Y → Z}
omit [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z] in
lemma twist_b(v:ℝ)(p:Shake F₁ (0:Y) w n) : Shake (F₁∘ (@Prod.fst Y ℝ)) (0,v) w n:=by
 let L:=ContinuousLinearMap.fst ℝ Y ℝ; have hp:‖L‖ ≤ 1:=ContinuousLinearMap.norm_fst_le ℝ Y ℝ
 refine ⟨p.price,p.smooth.comp (0,v) contDiffAt_fst,fun k g h=>?_⟩; let t:= ((0:Y),v); change ‖iteratedFDeriv ℝ k (F₁∘ L) t‖ ≤ _; rw [Push.Uniform.iter_lin_at (L:=L) (show ContDiffAt ℝ ((k:ℕ):ℕ∞ω) F₁ (L t) from p.smooth.of_le (by exact_mod_cast h))]; refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ?_).trans (p.bill k g h)); simp only [prod_const,card_univ,Fintype.card_fin]; exact pow_le_one₀ (norm_nonneg _) hp
omit [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z] in
lemma turnB(v:ℝ)(p:Allows n F₁ (0:Y) w): Allows n (F₁∘ (@Prod.fst Y ℝ)) (0,v) w:= (twist_b v (Shake.pick p)).paid p.value|>.mono (max_self w).le
omit [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z] in
private lemma bouquet{u:ℝ}(x a L:ℝ)(F K:Y→ Z)(p:0<L)(hp:|x| ≤1)(ha:0≤a)(hF:Allows n F 0 t)(hK:Allows n K 0 (u*L)):
 Allows n (fun v:Y×ℝ=> F v.1 + v.2 • (a • (L⁻¹ • K v.1))) (0,x) (t+2^n*(a*u)):=by
 have hp':Allows n (@Prod.snd Y ℝ) (0,x) 1:= allows_linear (L:=ContinuousLinearMap.snd ℝ Y ℝ) (ContinuousLinearMap.norm_snd_le ℝ Y ℝ) (x:=((0:Y),x)) (by change ‖x‖≤_; exact hp)
 apply Allows.mono ((turnB x hF).add (hp'.bilinear (ContinuousLinearMap.lsmul ℝ ℝ) (((turnB x hK).smul L⁻¹).smul a) ContinuousLinearMap.opNorm_lsmul_le))
 rw [abs_of_nonneg ha,abs_of_pos (inv_pos.mpr p)]; exact le_of_eq (by field_simp) -- tune
end smooth
open Rill Matrix
variable {T:Tube G S} {M:Monk G S}{l:ℕ}{v' B u:ℝ}
lemma boa{a:ℝ}(p:MossX n l x M.key M.park T M.V M.k C d t q)(hx:‖M.z‖≤ L)(hp:0<L)(ha:0 ≤ a)(ht:|u| ≤1)(hC:0≤C): Allows n (bent T x M d l q a L) (0,u) (C*t+2^n*(a*(2^n*C))):=by
 obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩:=p.jumps (M.bush x); let f(U:Directions G c):= liftN T x (Vmove x M.V U) M.k M.key M.park q d (M.bush x) l
 let N(v:Directions G c):=credW T M.key M.park M.k q d x (M.bush x) l (Vmove x M.V v); let F':= f -- unused
 let K(v):= N v *ᵥ tape.symm (M.bell x); have hh:Allows n K 0 (2^n*C*L):=airK (A:=N) h5 (allows_const _ ((loomP _).trans ((pi_norm_le_iff_of_nonneg hp.le).mpr (fun i=> (norm_le_pi_norm M.z i.val.val).trans hx))))
 exact bouquet u a L f K hp ht ha h2 hh

lemma pulse_b{a:ℝ}(n:ℕ)(e C K:ℝ)(hp:0≤C)(hK:1 ≤K)(h:Wind e (·*·) n K)(hc:K*C ≤ e)(he:C≤1)(hX:∀ {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E](F:E→ SU.group.Color)(x:E),Allows n F x C→Tender (SU.group.lieExp∘F) x (K*C) n)(hv:Trow (Vmove x M.V) 0 (K*C) n)(p: Allows n (bent T x M d l q a L) (0,u) B)(hg:Push.Uniform.shade G*B≤ C): Trow (repine T x M d l q a L) (0,u) (K*(K*C)) n:=by
 intro i; let X(p:Directions G c×ℝ):=Vmove x M.V p.1; let Z:=bent T x M d l q a L; have h0:0 ≤ K:=zero_le_one.trans hK; have hc:0 ≤ K*C:=mul_nonneg h0 hp
 by_cases v:i∈M.park.trunks
 · refine ((Shake.holds (SU.group.mat 1)).bag (mul_nonneg h0 hc)).same (Eventually.of_forall fun u=> ?_); exact congrArg SU.group.mat (M.park.on_tree _ ⟨i,v⟩).symm
 let j:M.park.Free:=⟨i,v⟩; by_cases t:chill M.key x M.park j
 · let w:Frozen M.key x M.park:=⟨j,t⟩; exact ((Shake.holds (SU.group.mat (M.U i))).bag (mul_nonneg h0 hc)).same (Eventually.of_forall fun i=> congrArg SU.group.mat (held_physical x M.key M.park (X i) (M.bush x) (Z i) w).symm)
 let w:Active M.key x M.park:=⟨j,t⟩; let V(v):=tape (Z v) w; have hp:Allows n V (0,u) C:= (shelJ p w).mono hg; let P(v):=replica S.ratio (X v) i; have hV:Tender P (0,u) (K*C) n:=by
    unfold P Precision.replica; split
    · exact (Shake.holds (SU.group.mat 1)).bag hc -- tune costs
    exact twist_b _ (hv _)
 exact ((h.duty ‹K*C≤e› (hX V _ hp) hV).same (Eventually.of_forall fun i=>congrArg SU.group.mat (clear_physical x M.key M.park (X i) (M.bush x) (Z i) w).symm))
end YM.CF.Cloak
