import YM.SU5.Regis.MirrorLine

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
local notation "Ξ"=> household W
open Papal Regis.Head Gleam
variable {I J:Type*}[Fintype I][Fintype J] (A:Etch SU.group I)(Z:Etch SU.group J) (ρ:ℝ)

abbrev tapestryRate(s:ℕ):ℝ:=ornament A P.run P.period P.cutoff s
abbrev liability := A.climax P.par.K.top.clip
variable {β u:ℝ}{X:Supplier}
-- portrait law on branch
lemma liability_non:0≤ P.liability A:=by unfold liability Etch.climax; positivity
lemma budgetMark(s:ℕ) : |P.tapestryRate A s| ≤ A.arc := (terrace_ultra ..).1
variable {P R}(B:uniform P R X β u)
include B
lemma epochP (ε:ℝ)(p:0<ε):∀ᶠ s in atTop, ‖P.E s (P.view A s).val-(P.tapestryRate A s:ℂ)‖≤ ε:=by obtain ⟨l,v,q,a,e,f,g,r⟩:= B.1.paper; exact panelThink A P.run P.large g B.2 B.1.nerve P.law ε p
omit B
variable (P)
lemma multilt (s:ℕ)(b:J→ℕ): let f:=P.view A s; let g:= P.view (A.ensemble (fun _=>1) (P.lineup j b)) s; ∀ x, P.singleState j s x g= (Fintype.card J:ℂ)*P.singleState j s x f:=by
 intro f g x; rw [show g=∑ i:J,P.halfShift j (b i) f from P.view_wing ..,map_sum]; let hc (a:P.Test) := P.singleState j s x a
 have he(i:J): (P.singleState j s x) (P.halfShift j (b i) f)=hc f:=by rw [P.single_state,P.halfReads]; rfl
 simp_rw [he]; simp [hc]
lemma rosaryV(s:ℕ)(f:P.Test)(t:∃ v:P.Vox j s,P.voxTest j s v=f) : (∫ x,‖P.singleState j s x f‖^2∂(P.pillars j))≤ ‖P.E s (P.reflectTest j f*f).val‖:=by
 obtain ⟨z,rfl⟩:= t; simp_rw [P.single_state,P.pillar_]; rw [at_label]; change ‖(P.compressed j s (P.voxTest j s z)) φ‖^2≤ ‖P.E s (mirror W j 0 z.val * z.val)‖; rw [←P.seed_pairing,inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _),P.seed]; exact pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_orthogonalProjectionOnto_apply_le ..) 2
/-- direct vector proof of integral bound avoiding interchanging even signed moments. -/
lemma view_bound {ε:ℝ}(b:J→ℕ)(s:ℕ)(v:∀ i,Tower.region j 0 P.calibration.ℓ (onFlight P.par.block (spanOf A) j (b i)))(c:‖P.E s (P.view (nexus j A (P.lineup j b)) s).val‖ ≤ ε):
    (Fintype.card J:ℝ)^2*(∫ x,‖P.singleState j s x (P.view A s)‖^2∂(P.pillars j)) ≤ ε:=by
 let f:= P.view A s; let Q₁:=A.ensemble (fun _=>1) (P.lineup j b); let mark:= P.view Q₁ s; let z:= (Fintype.card J:ℝ); apply le_trans ?_ c; let D:= P.rosaryV j s mark (P.located j A b s v); rw [P.nexus_sum]
 apply D.trans'; rw [← integral_const_mul]; apply le_of_eq; apply integral_congr_ae; filter_upwards with x; have h: P.singleState j s x mark=(Fintype.card J:ℂ)*P.singleState j s x f:=P.multilt j A s b x; rw [h,norm_mul,mul_pow, show ‖(Fintype.card J:ℂ)‖=z from (by simp [z])]
lemma viewpointV (c:ℝ)(s:ℕ)(x:P.Test): (∫ u,‖P.singleState j s u x-(c:ℂ)‖^2 ∂(P.pillars j))=(∫ u,‖P.singleState j s u x‖^2∂(P.pillars j))-2*c*(P.E s x.val).re+c^2:=by
 let WQ:= P.reading j s x; let G:= WQ-(c:ℂ) • (1:P.Ensemble j); have hx(i): P.singleState j s i x-(c:ℂ)=P.chi j i G:=by rw [P.single_state]; unfold G; rw [map_sub,map_smul,map_one,smul_eq_mul,mul_one]
 simp_rw [hx]; simp_rw [P.single_state,P.pillar_]; let U:= WQ.val φ
 change ‖U - (c:ℂ) • φ‖^2= ‖U‖^2- _ + _; rw [@norm_sub_sq ℂ, inner_smul_right]; have hp:inner ℂ U φ=star (P.E s x.val):=by
    rw [←P.occupied, show P.compressed j s x φ=U from rfl,Complex.star_def]; exact (inner_conj_symm ..).symm -- orientation
 rw [hp]; simp only [RCLike.re_eq_complex_re, Complex.star_def, Complex.mul_re,Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.conj_re,P.ground_norm,norm_smul,mul_one,Complex.norm_real,Real.norm_eq_abs, sq_abs]; ring
variable {P} {v:ℝ}
include B

lemma varianceP {ε:ℝ}(p:0<ε) : ∀ᶠ s in atTop, (∫ x,‖P.singleState j s x (P.view A s)-(P.tapestryRate A s:ℂ)‖^2∂ P.pillars j) ≤ ε:=by
 obtain ⟨l,hL⟩:= exists_nat_gt (P.liability A/(ε/3)); let N:=l+1; let M:=Fin N; have hN : 1 ≤ N:=Nat.le_add_left ..; letI : NeZero N:=⟨by omega⟩
 obtain ⟨t,E,T⟩:= P.keepAll (J:=M) j A; let o:= P.lineup j t; have ht:Injective o:= (P.stretchO_inj j).comp E; let F:= nexus j A o; have he:0 < ε/3:= by positivity
 
 let δ:= (ε/3)/(2*A.arc+1); have ha:= A.arc_non; have hp: 0<δ:=div_pos he (by positivity); let D:= P.liability A
 filter_upwards [epochP A B δ hp, epochP F B (ε/3) he,beefing A P.run P.large P.law (fun i=> (Signed.mirror j).act (o i)) o (fun _=> Signed.mirror j) (fun _=>1) ( ((Signed.mirror j).act_injective).comp ht) ht] with s u v w
 rw [P.viewpointV]; let p':= P.view A s; let a:= P.tapestryRate A s; let φ':= P.tapestryRate F s; let β':= P.E s (P.view F s).val; let k:ℝ:=N; let d:ℝ:=(Fintype.card M);
 have he: d=k:=congrArg NatCast.natCast (Fintype.card_fin _); have hk: 1 ≤ d:= he ▸ Nat.one_le_cast.mpr hN; have h: 0 < d:= zero_lt_one.trans_le hk
 let D':= ∫ x:P.Spectrum0 j, ‖P.singleState j s x p'‖^2∂P.pillars j
 have hq:D ≤ d*(ε/3):=by
    refine le_trans (le_of_lt ((div_lt_iff₀ (by positivity : 0 < ε/3)).1 hL)) ?_; gcongr; rw [he]; exact Nat.cast_le.mpr (Nat.le_add_right l 1)
 have hx: |φ'-(d*a)^2| ≤ d*D:=w
 have hv: ‖β'‖ ≤ (d*a)^2+d*D+ε/3:=by
    apply (norm_le_norm_sub_add β' (φ':ℂ)).trans; rw [Complex.norm_real,Real.norm_eq_abs] -- tune assoc
    have he: |φ'| ≤ (d*a)^2+d*D:= by nth_rw 1 [← sub_add_cancel φ' ((d*a)^2)]; apply (abs_add_le ..).trans; rw [abs_of_nonneg (sq_nonneg (d*a))]; exact (add_le_add hx le_rfl).trans_eq (add_comm ..)
    change ‖β'-(φ':ℂ)‖≤ _ at v; linarith only [v,he]
 have hψ: d^2*D' ≤ (d*a)^2+d*D+ε/3:= P.view_bound j A t s T hv -- P.view implicit order
 have hu: D' ≤ a^2+2*(ε/3):= by
    have ht:ε ≤ ε*d^2:= le_mul_of_one_le_right p.le (one_le_pow₀ hk)
    apply le_of_mul_le_mul_left (_:d^2*D'≤d^2*(a^2+_)) (pow_pos h 2); linarith only [hψ,mul_le_mul_of_nonneg_left hq h.le,ht]
 let x:= P.E s p'.val; have he'':2*a*(a-x.re) ≤ ε/3:=by
    have hp: ‖x-(a:ℂ)‖≤δ:=u; have hy:|x.re-a| ≤δ:= hp.trans' (by rw [← Complex.ofReal_re a,←Complex.sub_re]; exact Complex.abs_re_le_norm _)
    have hm:a ≤ A.arc:= (abs_le.mp (P.budgetMark A s)).2; have hl: |a*(a-x.re)|≤ A.arc*δ:=by rw [abs_mul,abs_sub_comm]; exact mul_le_mul (P.budgetMark A s) hy (abs_nonneg _) ha
    have hx:= (le_abs_self _).trans hl; linarith only [hx, show δ*(2*A.arc+1)=ε/3 from div_mul_cancel₀ _ (by positivity), (show 0≤δ from hp.trans' (norm_nonneg _))]
 change D'- 2*a*x.re + a^2 ≤_; linarith only [hu,he'']
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.varianceP
