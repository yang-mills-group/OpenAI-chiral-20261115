import YM.SU5.Relativistic.BoreDoc
/-! # Payments vary per MARK. Ask for d after z choice. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
set_option synthInstance.maxSize 25000
namespace YM.CF.Papyrus.Franc.Loaves
open Function Set Filter NormedSpace Fock Finset Thera MeasureTheory Metric Lattice Cube Lat Fir Onyx Rush Ember SU Scroll Skye Tulip Flare BPress.Spin.Blank
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered Emu
open Lifted Pea Omelet BProof.Wick
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra
-- source sending 1
abbrev whisper {I:Type*}[LinearOrder I][Fintype I](z y:ℂ)(F:FC I):= 1+z • (F+(-y) • 1)
variable {I:Type*} [LinearOrder I][Fintype I][Nonempty I]{L:List Wine}{S:Finset Cover}{t C δ ε :ℝ}{z:ℂ}{b:Bool}(u:LinksC){P:Op I}(p:IsStarProjection P)
local notation "F" => tickTea
private lemma closeH (T A:Pea I)(h:T.Zones A)(G:Bite→Ket I)(w:∀ i∈billP L, met A (G i) t)(p:∀ i∈billP L,‖G i‖≤ C)(x:1≤C)
    (e:∀ (U W:Bite→Ket I), (∀ i∈billP L,‖U i‖≤2*C ∧ ‖W i‖≤2*C ∧ ‖U i-W i‖≤2*t) → ‖tickTea U u L-tickTea W u L‖≤ε):
    ‖T.mint.glow (F G u L)- F (fun i=>acts A.robe (G i)) u L‖ ≤ ε:=by
 rw [shiftTea]; apply e; intro i y; let X:= G i; let V:=acts A.robe X; let Y:=if i.hand then star T.mint.buy else T.mint.sell; have hx: ‖X - V‖≤ t:=by rw [←show acts (1-A.robe) X=X-V from by rw [act_sub,act_one]]; exact w i y
 have hl: ‖Y‖≤2:=mntSize ..; refine ⟨(Flare.opy ..).trans (mul_le_mul hl (p i y) (norm_nonneg _) zero_le_two),((Flare.opy ..).trans (mul_le_mul (A.robe_p.norm_le A.robe|>.trans (by norm_num)) (p i y) (norm_nonneg _) zero_le_two)),?_⟩; change ‖acts Y X-V‖≤_; nth_rw 1 [←(show acts Y V=V from juice_arm T A h G i)]; rw [←map_sub]; exact (Flare.opy ..).trans (mul_le_mul hl hx (norm_nonneg _) zero_le_two)
variable (L:List Wine)(h:AreaW false S L)
include h
lemma counsel (C:ℝ)(p:1≤C)(ε:ℝ)(u:0<ε) : ∃ ζ> (0:ℝ),∀ z:ℂ, 0<‖z‖→‖z‖≤ζ→∃ η>(0:ℝ),4*η≤ε*‖z‖∧∀ {N:Side}(F':Fields N)(P:Op (Single N))(q:IsStarProjection P)(T:Finset (Single N))(k:ℕ)(A:Pea (Single N)), let U:=F'.1; let Q:= onC N U;let Y:=tickTea (Straw P k) Q L; Shell A T → A.leak P≤η→(∀ i∈billP L, ‖Straw P k i‖≤C ∧ met A (Straw P k i) η)→(∃ v:Wave (Single N),Sea P v∧‖inner ℂ v (acts Y v)-tallyW L‖ ≤η) →Nought (Saber (B:=tickA N) q k) (whisper z (tallyW L) (motet N L F')) P η (ε*‖z‖) T :=by
 obtain ⟨B,b,k⟩:=tipPower C L (zero_lt_one.trans_le p) h
 let y:= tallyW L; let D:= B+‖y‖; have hp:0<D:= by unfold D; positivity
 -- ensure coefficient ≤eps; μ=4*(η+η'+2*D*μs). z². constraints
 let d:= ε/100; let w:=min (1/2:ℝ) (d/(2*D)); have hD:0<d:=by unfold d; positivity
 have hw:0<w:=lt_min (by norm_num) (by positivity); have hg:w≤1/2:= min_le_left ..; have hh:2*D*w≤d:=by rw [mul_comm _ w]; exact (le_div_iff₀ (by positivity)).mp (min_le_right _ (d/(2*D)))
 obtain ⟨G,r,g⟩:= tipSlope (2*C) L (by linarith) h d hD
 let ζ:=ε/(16*D^2); have hx:0<ζ:=by unfold ζ; positivity
 have hy:∀ᶠ η:ℝ in 𝓝 0, Real.exp (4*η)^2 ≤ 1+3*w^2 :=by
    let A(x:ℝ):=Real.exp (4*x)^2; have hp:A 0=1:=by simp [A]
    exact (Continuous.tendsto (f:=A) (by unfold A; fun_prop) _).eventually (ge_mem_nhds (by rw [hp]; nlinarith only [pow_pos hw 2]))
 refine ⟨ζ,hx,fun z ht ht' => ?_⟩
 have hu:∀ᶠ x in 𝓝 (0:ℝ), x ≤ G/2 ∧ x≤ d ∧ x≤ ε*‖z‖/4:= Eventually.and (ge_mem_nhds (half_pos r)) (Eventually.and (ge_mem_nhds hD) (ge_mem_nhds (by positivity)))
 have hp:∀ᶠ x in 𝓝[>] (0:ℝ),0<x:= self_mem_nhdsWithin
 obtain ⟨η,hη,hγ,hv,hα,s⟩:=(hp.and (eventually_nhdsWithin_of_eventually_nhds (hy.and hu))).exists
 change 0<η at hη
 refine ⟨η,hη,by linarith only [s],?_⟩
 intro N Z P q T m A U Q Y j uK c e
 obtain ⟨V,z',w'⟩:=e
 let H:= fun i:Bite=>acts A.robe (Straw P m i); let P':= Saber (B:=tickA N) q m; let X0:= motet N L Z
 have hz':P'.glow X0=Y:= skyT q U Z rfl L m
 let W:= tickTea H Q L; let F0:= W+(-y) • 1
 have hf: ‖F0‖≤D:= (norm_add_le ..).trans (add_le_add (k _ _ (fun i w=> ((opy ..).trans (mul_le_of_le_one_left (norm_nonneg _) (A.robe_p.norm_le _))).trans (c i w).1)) (le_of_eq (by rw [norm_smul,norm_neg,norm_one,mul_one])))
 obtain ⟨R,X,X',v0,v1,v'⟩:=A.laid
 let W':=twist (quantU R) (cabin X X')
 have hb:A.GlowGap W':= glowGap A R X X' v0 v1 v'
 have he: ∃ s:ℂ,W'*F0*W'=s • W':=by
    apply pen_sect A R X X' v0 v1 v'
    unfold F0; rw [map_add, twist_scalar, map_one]; exact (scopeTea A R X X' v0 v1 L h Q H (fun i _=> by unfold H; rw [←act_mul,A.robe_p.isIdempotentElem]) v').add (Sector.one.scale _)
 have hB : ∀ T:Pea (Single N), T.Zones A → ‖T.mint.glow Y - W‖ ≤ d:=fun T' Z₀=> closeH Q T' A Z₀ (Straw P m) (fun i w=>(c i w).2) (fun i w=>(c i w).1) p (fun i x v=> g Q i x (fun j p=> by obtain ⟨l,r,g⟩:=v j p; exact ⟨l,r,g.trans (by linarith only [hv])⟩))
 let μ:=4*((η+d)+2*D*w); have ha: ‖inner ℂ V (acts F0 V)‖≤ η+d:=by
    let T:= slept (Single N); have hv: T.Zones A:=⟨by unfold T; rw [slept_r,zero_mul]⟩
    have hx:‖Y-W‖ ≤ d:= (hB T hv).trans' (le_of_eq (by rw [← T.vending]; unfold T; rw [slept_b.1,slept_b.2.1,one_mul,mul_one])) -- argument I implicit
    let c:= fun X:FC (Single N)=> inner ℂ V (acts X V)
    change ‖c F0‖ ≤_; rw [show c F0=(c Y - y)+c (W-Y) from (?_)];
    · exact (norm_add_le ..).trans (add_le_add w' ((pike_cross _ V z'.2).trans ((norm_sub_rev ..).trans_le hx)))
    unfold c F0; rw [act_add,act_sub,act_smul,act_one,inner_add_right,inner_sub_right,inner_smul_right,inner_self_eq_norm_sq_to_K,z'.2]; simp; abel
 constructor; refine ⟨A,j,uK,fun T Z' => ?_⟩
 let B':= T.mint.foldC P'; let Q:=peak μ D ‖z‖
 have hk:=gapFund A hb D μ z hf (aware q A hb (norm_nonneg _) ((pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp_of_le (by linarith only [uK])) _).trans hγ) hw.le hg z' he hf ha)
 unfold whisper; change ‖B'.glow _*A.hat‖≤_; rw [B'.glow_sum,B'.glow_nil,B'.glow_free, B'.glow_sum,B'.glow_free ( -_),B'.glow_nil,show B'.glow _= T.mint.glow Y from (by unfold B'; rw [Shaft.fold_use, hz'])] -- glow_free notation
 let a:=T.mint.glow Y
 rw [show (1+z • (T.mint.glow Y + (-y) • 1))*A.hat=(1+ z • F0)*A.hat+ z • ((a-W)* A.hat) by unfold F0 a; rw [←Algebra.smul_mul_assoc, ←add_mul]; congr 1; module]
 apply (norm_add_le ..).trans; apply (add_le_add hk ((norm_smul ..).le.trans (mul_le_mul_of_nonneg_left ((norm_mul_le ..).trans (mul_le_mul (hB _ Z') hb.cap (norm_nonneg _) hD.le)) (norm_nonneg _)))).trans
 apply (Real.add_one_le_exp _).trans'; unfold peak; rw [mul_one d]; have hh':8*D^2*‖z‖ ≤ ε/2:=by have h_ := (le_div_iff₀ (show 0<16*D^2 by positivity)).mp ht'; linarith
 have hN: μ ≤ 12*d:=by unfold μ; linarith only [hh,hα]
 unfold d at hN ⊢; nlinarith only [mul_le_mul_of_nonneg_right hN ht.le,mul_le_mul_of_nonneg_right hh' ht.le, mul_pos u ht]
end YM.CF.Papyrus.Franc.Loaves
#print axioms YM.CF.Papyrus.Franc.Loaves.counsel
