import YM.SU5.FiniteGaugeData.Cuprite.Presidio
/-! # Transport earnings
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 600000
set_option linter.flexible false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Window.Presidio
open Parcel.Tanin Fock Fock.Reduction Reduction.Hutch Reduction.Drama Reduction.Drama.Pack Reduction.Jersey
open Next.Free Function Filter NormedSpace Lattice Laurent Bloch Wilson Precision Tree Finset Exterior
open Lat Rush Cube Scroll SU Peaks Dial Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Cour Fir Ember Aroma Cascade Gall
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]
variable {a r b M e Rμ μ d:ℝ}
namespace Spiny
variable (U:UNI n){Q T A X P R W:Op n}
local notation "q" X:max => twist U X
lemma kit_lit(h:lit A) : lit (q A):=by -- bind
 refine ⟨(map_zero (twist U)) ▸ twist_mono U h.1, h.2.map _⟩
lemma kinv(h:lit X): (q X)⁻¹=q X⁻¹:=by apply inv_red (kit_lit U h); rw [←map_mul,lit_mulin h,map_one]
lemma kTr(A:Op n): TrR (q A)=TrR A:= by unfold TrR; rw [trace_twist]
lemma ktw(A:Op n): kg (q A)=kg A:=by unfold kg; rw [←map_star,←map_mul]; exact kTr _ _
lemma klog(A:Op n): rueD (q A)=rueD A:= by unfold rueD; rw [det_twist]
variable (h:twist U Q = Q) (u:lit (spring Q (Q*P)))
local notation "Θ"=> spring Q (Q*P)
local notation "Θ'"=> spring Q (Q*q P)
include h
lemma town(P:Op n) : q (spring Q (Q*P))=spring Q (Q*q P):=by simp only [spring,map_star,map_mul,map_sub,map_add,map_one,h]
include u
lemma stageq : pLine Q (q P) μ b=pLine Q P μ b:=by unfold pLine horizonM; rw [← town U h P,klog,kinv _ u,kTr]
lemma stageJ(X:Op n): curlR Q (q P) X=curlR Q P (twist (star U) X):=by
 let T:=twist (star U) X; have he:q T=X:=(by nth_rw 1 [←star_star U]; exact twist_inv _ _); let R:=Q*(T-1)*P; unfold curlR Poem; nth_rw 2 [← kTr U]; -- likely n_th occurrence
 simp only [map_mul,map_star,map_sub, ←kinv U u,map_one,town U h,h,show q (twist (star U) X)=_ from he] -- tune town u expand Q*P before town
private lemma fire_tangle: star ((tangle Θ')*(Q*(1-q P)))*((tangle Θ')*(Q*(1-q P)))= q (star ((tangle Θ)*(Q*(1-P)))*((tangle Θ)*(Q*(1-P)))):=by
 rw [adams _ _ (show lit Θ' from (town U h _) ▸ kit_lit U u),adams _ _ u, map_mul,map_mul,map_star,←kinv U u,town U h]; simp only [map_mul,map_sub,map_one,h]
variable [Nonempty n] {C:ℝ}
private lemma rateY (S:Op n)(w:∀i:n, ‖acts (tangle Θ*S) (basisKet i)‖ ≤ C ) (x:Ket n): ‖acts (tangle Θ*S) x‖ ≤ dialZ x*C:=by
 nth_rw 1 [←basis_expand x]; rw [map_sum]; unfold dialZ; rw [sum_mul]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro i _; rw [map_smul,norm_smul]; exact mul_le_mul_of_nonneg_left (w i) (norm_nonneg _)
lemma Subway (V:pointM n Q P C)(hb:0≤C)(F:∀ i:n,dialZ (acts (star U.val) (basisKet i)) ≤ r):pointM n Q (q P) (r*C):=by
 intro i; let x:= basisKet i; let y:= acts (star U.val) x; let H:= tangle Θ'*(Q*(1-q P)); let G:=tangle Θ*(Q*(1-P))
 have he:‖acts H x‖=‖acts G y‖:=by
    have he(A:Op n)(x:Ket n): ‖acts A x‖^2=(inner ℂ x (acts (star A*A) x)).re:=by rw [act_mul,← act_inner,star_star]; exact (inner_self_eq_norm_sq (𝕜:=ℂ) _).symm
    have hc: ‖acts H x‖^2=‖acts G y‖^2:=by rw [he,he,show star H*H=_ from fire_tangle U h u,twist_formula,act_mul, act_mul,←act_inner U.val]
    nlinarith only [hc,norm_nonneg (acts H x),norm_nonneg (acts G y)]
 have hh:= rateY U h u (Q*(1-P)) V y; exact le_trans (he.trans_le hh) (mul_le_mul_of_nonneg_right (F i) hb)
end Spiny
-- invite ONLY at ambient real frequencies; keep thresholds tied to actual mass. suitable for election start
open Scree
variable {h C H K:ℝ}{k:ℕ}{N:Side} {R0:Bkg (More N)}{X:Op (Single N)}
structure Invites(k:ℕ)(C:ℝ)(N:Side):Prop where
 billP:0≤C
 issued(M:Tulip.Male)(g:Site (More N)→SU.E): let P:= spar k M (1:Bkg (More N)); let R:=twist (tradew N g) P; let Q:=tickA N; let T:=spring Q (Q*R); IsStarProjection P→ IsStarProjection R ∧ lit T ∧ TrR T⁻¹≤ C*N.val^4 ∧ pointM (Single N) Q R (45*Real.sqrt C) ∧ rueD T/2=photo_ψ k N M ∧∀ W:Op (Single N), curlR Q R W=curlR Q P (twist (star (tradew N g)) W)
lemma Sasha (p:1≤k): ∃ C:ℝ,0≤C∧∃ n:ℕ,∀ N:Side,n ≤ N.val→ Even N.val → Invites k C N:=by
 obtain ⟨C,t,n,W⟩:= meanA p; refine ⟨C,t,n,fun N v h=>⟨t,?_⟩⟩; intro M g P R Q T L; obtain ⟨u,p',z⟩:= W N v h M L; let U:=tradew N g; have he:twist U Q=Q:= tick_g g; let H:=spring Q (Q*P); have hm:T= twist U H:=(Spiny.town U he P).symm; have hu:lit H:=u; have hg: TrR T⁻¹= TrR H⁻¹:=by rw [hm,Spiny.kinv U hu,Spiny.kTr]
 refine ⟨L.map (twist U),hm ▸ Spiny.kit_lit U hu,hg.trans_le p',Spiny.Subway U he hu z (by positivity) (lurk_n g),?_, Spiny.stageJ U he hu⟩; rw [hm,Spiny.klog,springMeter p]; rfl -- tune
noncomputable def sponsor(k:ℕ)(p:1≤k):= (Sasha p).choose
lemma sponsor_v(k:ℕ)(p:1≤k):0 ≤ sponsor k p:= (Sasha p).choose_spec.1
abbrev spant(k:ℕ)(p:1≤k):=(Sasha p).choose_spec.2.choose
abbrev promise(k:ℕ)(p:1≤k):ℝ:=2*(45*Real.sqrt (sponsor k p))+2
lemma promise₁(k:ℕ)(p:1≤k): 1≤promise k p:= by unfold promise; linarith only [Real.sqrt_nonneg (sponsor k p)]
lemma sponsor_p(k:ℕ)(p:1≤k)(e:spant k p≤N.val)(h:Even N.val): Invites k (sponsor k p) N:= (Sasha p).choose_spec.2.choose_spec N e h
end YM.CF.Window.Presidio
