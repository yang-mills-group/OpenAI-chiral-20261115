import GaugeFieldConstruction.SoulBreadNX
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3400
set_option linter.unusedSectionVars false
set_option maxHeartbeats 180000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup Ballad Six Glaze
-- Wipe.dll trick in actual unselected heat. Avoid restrictions projecting contents to Portion Hil.
variable {P:Spine}(i:Axis){A A':P.Glaze}{a b C g e:ℝ}{z y:ℂ}
lemma downWickNX(h:A.F=A'.F)(r:0<a)(p:0≤g)(t:0<e)
    (v:∀ᶠ s in atTop,‖P.meanBox i s (A'.w+A'.w) (P.shifts i A'.w (1+z•A'.F))‖≤1+g):
    ∀ᶠ s in atTop,∀u:P.Hil i,(z*inner ℂ u ((P.grantGapNX i s A.w A.F a a).1 u)).re ≤(e+g)*‖u‖^2:=by
 let Q:=A'.w+A'.w
 have hf:=A'.centers i
 let J:=A'.w
 let f:=P.shifts i J A'.F
 have hu:0<Q:=add_pos A'.pos A'.pos
 let S:=(P.publicH i).Time
 have H₀:∀ᶠ s in atTop, ‖S.wax (a-P.tock s J+(a-P.tock s J))- S.wax (a+a)‖ < e:=by
    have g':Tendsto (fun s=> a- P.tock s J) atTop (𝓝 a):=by simpa using tendsto_const_nhds (x:=a) |>.sub (P.tock_fades J)
    have v:= (S.wax_cont (add_pos r r)).tendsto.comp (g'.add g')
    exact (Metric.tendsto_nhds.mp v _ t).mono fun s h=>by rw[←dist_eq_norm]; exact h
 filter_upwards [v,H₀,P.tock_small J r,P.tock_small A.w r] with s hs gs d w u
 let G:(P.publicH i).H.Op := (P.HabBox i s Q f).1
 have e': ‖S.wax (P.tock s J+P.tock s J)+z•G‖≤1+g:=by
    rw [map_add,map_one,map_smul] at hs
    have ht :P.BEntry i Q 1:=BEntry.one _ _ hu
    rw[←heard_box s (ht.add (hf.smul z)),HabBox_add s ht (hf.smul z),HabBox_smul s hf,HabBox_one s P i hu] at hs
    have h:S.wax (P.tock s J + P.tock s J) =(P.Eucl i (whenly (timeMesh P.par) s Q)).1:=by
       show P.euclOp i _= _; rw [←P.tock_add,←Nat.cast_add,P.tock_when,Real.toNNReal_coe]; rfl -- tune
    unfold wax; have he: P.euclOp i ((P.tock s J + P.tock s J).toNNReal)= _:=h; change ‖P.euclOp i _ + z • (show P.Op0 i from (P.HabBox i s Q f).1)‖≤_; rw [he]; exact hs
 rw [h] -- ISSUE Width changing right
 have h0: P.BEntry i (A.w+A.w) (P.shifts i A.w A'.F):=h ▸ A.centers i
 rw [grantLargeNX i s A.w A'.w A'.F h0 hf w w d d]; exact wickTest S (P.tock_nonneg _ _) d p e' gs.le (P.grantAcrossNX i s A'.w A'.F _ _) u
lemma collectFourNX (v:P.Taste A.F A.S y)(r:0<a)(t:0<e):
    ∀ᶠ s in atTop, ‖P.grantGapNX i s A.w (A.soot y).F a a‖≤4*(2*e):=by
 let ε:=e/12; have ep:0<ε:=div_pos t (by norm_num)
 obtain ⟨c,u,h⟩:=v i _ ep
 let d:=min c (1/(6*ε)); have hd:0<d:=lt_min u (by positivity)
 let f:Finset ℂ:= {↑d,-↑d,Complex.I*↑d,-Complex.I*↑d}
 let g:= 2*(3*(ε*d)); have w: g+g=d*e:=by unfold g ε; ring
 have gp:0<g:=by positivity
 have K'(Z:ℂ)(q:Z∈f):∀ᶠ s in atTop,∀u:P.Hil i, (Z*inner ℂ u ((P.grantGapNX i s A.w (A.soot y).F a a).1 u)).re≤d*e*‖u‖^2:=by
   have e': ‖Z‖=d:=by
     simp only [f,Finset.mem_insert,Finset.mem_singleton] at q;rcases q with rfl|rfl|rfl|rfl <;> simp [Real.norm_of_nonneg hd.le]
   obtain ⟨N,w₀,p₀,t⟩:=h Z (e'.symm ▸ hd) (e'.trans_le (min_le_left ..))
   have g₀: 3*(ε*‖Z‖) ≤1/2:=by
      rw [e']; have z:d≤1/(6*ε):=min_le_right ..
      nlinarith only [(le_div_iff₀ (by positivity:0<6*ε)).mp z]
   let T:=A.soot y
   let T':P.Glaze:=⟨N,w₀,T.S,T.F,T.inlet,T.color,p₀⟩
   rw [←w]
   apply downWickNX i (A:=T) (z:=Z) (A':=T') rfl r gp.le gp
   refine t.mono (fun s u=>u.trans ?_)
   rw [e']; exact budget_exp_small _ (by positivity) (e' ▸ g₀)
 filter_upwards [(eventually_all_finite f.finite_toSet).mpr K'] with s h
 exact wickTest_four d e hd t.le (H:= P.publicH i|>.H) (fun z q=>h z q)
#print axioms collectFourNX
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
