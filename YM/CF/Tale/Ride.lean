import YM.CF.Hove.Script
import YM.CF.Cascade.Oars
import YM.CF.Tale.Tree
set_option autoImplicit false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.CF.Tale
set_option quotPrecheck false
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Next Next.Free PhysicalNext.JointLoad Cube SU Exterior Cascade Bloch
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
-- Transverse linear gauge moment, transported spot. canonical blocks only. no t-period interpolation
variable (k:ℝ)(j t:ℕ)(h:0<k)(p:4≤j)(v:4≤t)(P:Flight j t)
variable (d:Axis)
open Flight Matrix
local notation "Z"=> Exterior.coord d
lemma ahead_K (p:Momentum)(x:p d=0)(l: Site P.L)(i:TypeFace 1):pilot k P p l i (Exterior.coord d)=ahead k P p l i Z:=by
 have h(u:TypeFace 0): sluice k P p u Z=0:=by
    unfold sluice; rw [Matrix.smul_apply,Matrix.mul_apply]; unfold priorG; rw [sum_eq_single Z]
    · have hu:u=vac:=vac_only ..
      rw [mirage,Matrix.transpose_apply,hu,signal_unit,blade0]; simp [Exterior.q,x]
    · intro j _ v; simp [mask_value,v]
    simp
 rw [pilot, Matrix.add_apply, Matrix.mul_apply]; simp_rw [h]; simp
private lemma gloom {ι:Type}(F:ι→Momentum→ℂ){v:ι→ℝ}(p:Moderate v F)(a:Axis)(i:ι): DifferentiableAt ℝ (fun x:ℝ=>F i (Tap.bout a x)) 0:=by
 obtain ⟨b,C,h,t,H⟩:= p; have hp:DifferentiableAt ℂ (F i) (Tap.bout a 0):=(H i).hol _ (by rw [Tap.bout_zero]; exact cube_zero _ h); apply (hp.restrictScalars ℝ).comp 0; unfold Tap.bout; fun_prop
variable {x y:ℝ}(a b:Axis)(o:Site P.L)(i:TypeFace 1)
local notation "L"=> P.L
local notation "z"=> Tap.bout b
local notation "ξ"=>Complex.I
local notation "R"=> (Lattice.lift o)
local notation "PL"=> pilot k P
lemma chip_h : HasDerivAt (fun x:ℝ=>listChip (aliasAt (z x) (0:Site P.L)) [a]) (if a=b then Complex.I/(P.L.val:ℂ) else 0) 0:=by
 simp_rw [listChip,alias_zero_eq,chip,Next.Free.narrow,Tap.bout,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,Pi.smul_apply,smul_eq_mul]; split; rename_i ht; swap; · rename_i ht; simp [ht]; exact hasDerivAt_const ..
 subst a; simp only [Lattice.step_apply,if_true,mul_one]; apply HasDerivAt.sub_const
 let k':ℂ:= P.L.val; have hp:= Complex.hasDerivAt_exp 0; let Q(t:ℂ):= ξ*(k'⁻¹*t)
 have hh: HasDerivAt (Complex.exp ∘ Q) (ξ/k') 0:=by
    have ht: HasDerivAt Q (ξ*k'⁻¹) 0:=by simpa only [mul_one] using (((hasDerivAt_id' (0:ℂ)).const_mul k'⁻¹).const_mul ξ)
    have hb: HasDerivAt Complex.exp (Complex.exp 0) (Q 0):=by change HasDerivAt _ _ (ξ*(k'⁻¹*0)); simp only [mul_zero]; exact hp
    exact (hb.comp _ ht).congr_deriv (by rw [Complex.exp_zero,one_mul,div_eq_mul_inv])
 have hW:HasDerivAt (fun i:ℝ=> (i:ℂ)) 1 0:= Complex.ofRealCLM.hasFDerivAt.hasDerivAt; exact ((show HasDerivAt (Complex.exp ∘ Q) (ξ/k') ((↑(0:ℝ)):ℂ) from by rwa [Complex.ofReal_zero]).scomp 0 hW).congr_deriv (by simp [k'])
include h p v
private lemma divT (o':b≠d)(r:Site P.L)(hr:r≠0) : HasDerivAt (fun x:ℝ=>PL (z x) r i Z) 0 0:=by
 have hp(a:Axis):=portD_budget k p (fun _ : Unit=>P) (fun _=>r) (fun _=>hr) (fun _=>a)
 let Vφ(p'):Frequency 1 1:= mask 1 (portD k P p' r)*flux P 1 (aliasAt p' r)*priorG k P p'
 have he:= ((Pay.expose_mask 1 hp).times (flux_budget (fun _: Unit=>P) 1 (fun _=>r))).times (prior_cost k h v (fun _:Unit=>P))
 have hv:DifferentiableAt ℝ (fun x:ℝ=> Vφ (z x) i Z) 0:=gloom _ (he.tap i Z) b () -- tune
 simp_rw [show ∀ x:ℝ, PL (z x) r i Z=ahead k P (z x) r i Z from fun x=> ahead_K k j t P d _ (by simp [Tap.bout,Ne.symm o']) r i]
 have hz(q':Momentum):ahead k P q' r i Z=P.span q' * Vφ q' i Z:=by unfold ahead; rw [if_neg hr]; rfl
 simp_rw [hz]; have hT:HasDerivAt (fun x:ℝ=>P.span (z x)) 0 0:=by
    unfold span divisor; -- tune
    have hp(i:Axis)(neg:Bool):DifferentiableAt ℝ (fun x:ℝ=> seedQ P.land.mass (if neg then -(z x) else z x) i) 0:=by
        have ht:=seed_control (fun _:Unit=>P.land.mass) (fun _=>i); cases neg; · simp only [ite_false,Bool.false_eq_true]; exact gloom _ ht b ()
        simp only [ite_true]; exact gloom _ (ht.reverse) b ()
    refine (HasDerivAt.fun_sum (A':=fun i=>0) (fun i (_:i∈(univ:Finset Axis))=>?_)).congr_deriv sum_const_zero -- tune
    have he:= hp i true; have hh:= hp i false; simp at he hh; exact (hh.hasDerivAt.mul he.hasDerivAt).congr_deriv (by simp [Tap.bout,seedQ,Next.Free.narrow])
 exact (hT.mul hv.hasDerivAt).congr_deriv (by simp [Tap.bout, Flight.span]) -- span P notation
local notation "Z_L"=> if a=b ∧ i= (Exterior.coord d) then ξ/(P.L.val:ℂ)^2 else 0
lemma entry_X (o':d ≠ b): HasDerivAt (fun x:ℝ=> spread (pilot k) 1 [a] P o (z x) i (Exterior.coord d)) Z_L 0:=by
 unfold spread; simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
 let F(r: Site P.L)(x:ℝ):=Laurent.mode (aliasAt (z x) r) R * ((toll L 1 * listChip (aliasAt (z x) r) [a])* pilot k P (z x) r i (Exterior.coord d)) -- notation conflict
 suffices h: HasDerivAt (fun x:ℝ=> ∑ r:Site P.L,F r x) Z_L 0 from h
 have P'(r:Site P.L):DifferentiableAt ℝ (fun x:ℝ=> Laurent.mode (aliasAt (z x) r) R) 0:=gloom _ (residue_cost (fun _:Unit=> P) (fun _=>r) (fun _=>o)) b ()
 have h₀(r:Site P.L)(t:r≠0): HasDerivAt (F r) 0 0:=by
    have hu:DifferentiableAt ℝ (fun x:ℝ=> toll P.L 1 * listChip (aliasAt (z x) r) [a]) 0:=gloom _ (differential_bound (fun _:Unit=>P) (fun _=>r) 1 [a]) b ()
    have he:P.span (z 0)=0:=by simp [Tap.bout, span]
    have hz:pilot k P (z 0) r=0:=by rw [Tap.bout_zero,pilot_none P k t] -- tune
    unfold F; refine ((P' r).hasDerivAt.mul (hu.hasDerivAt.mul (divT k j _ h p v P d b i (Ne.symm o') r t))).congr_deriv ?_ -- conflict
    simp only [Pi.mul_apply,hz, Matrix.zero_apply, mul_zero, add_zero]
 have hx: HasDerivAt (F 0) Z_L 0:=by
    have hp:= gloom _ ((pilot_cost k h p v (fun _ : Unit=>P) (fun _=>0)).tap i Z) b ()
    unfold F; refine ((P' 0).hasDerivAt.mul (((chip_h j t P a b).const_mul (toll P.L 1)).mul hp.hasDerivAt)).congr_deriv ?_
    simp only [Tap.bout_zero,alias_zero_eq, show Next.Free.narrow L 0=0 from (by simp [Next.Free.narrow]),mode_constant, mode_zero]; simp [listChip,toll,Next.Free.narrow]; split_ifs<;>simp_all [one_apply]<;> ring --] -- tune pilot lemma
 have he(x:ℝ):(∑ r:Site P.L,F r x)=F 0 x + ∑ r∈univ.erase (0:Site P.L), F r x:=(Finset.add_sum_erase _ (fun i=> F i x) (mem_univ (0:Site P.L))).symm -- args
 simp_rw [he]; exact (hx.add (HasDerivAt.fun_sum (fun i (_:i∈ univ.erase (0:Site P.L))=>h₀ i (Finset.ne_of_mem_erase ‹_›)))).congr_deriv (by simp)
end YM.CF.Tale
