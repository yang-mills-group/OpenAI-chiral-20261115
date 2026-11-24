import ExactRunning.Step.Rails

/-!
# Comparing joint, high and outgoing

`Test.separated`: apply Schur on shell (`Test.B`) with cuts, then come
back to both costs on the diagonal with `lead` (`zLaw` and `hiLaw`).
Through second order in repeating external probes, in each Test period.
-/


set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} {X : BlockTie E I}


namespace Test
variable (T : X.Test m)
/-- actual shell representative -/
private theorem separate {r : ℝ} (hd : 0<r) {k : ℝ → Link G m} (hk : ContDiffAt ℝ ω k 0)
    (h0 : k 0=0)
    (f : X.Rail r (fun t => T.B (k t)) (fun t => input G m (k t))) :
    let b t := T.B (k t)
    let v t := input G m (k t)
    Touch (fun t => X.zCost r (b t) (v t))
       (fun t => X.hCost r (b t) (v t) + epCost (ridge r) I.p I.r (v t)) := by
  intro b v
  let P := (ridge r).cut m (Entry G)
  let Q := (ridge r).cut m (Foot G)
  have hd' : Tendsto k (𝓝 0) (𝓝 0) := h0 ▸ hk.continuousAt.tendsto
  have hs := hd'.eventually T.stable
  have ha := hd'.eventually (X.full_fare T.thaw T.b01 (v:=input G m) (Army.powL contDiffAt_id))
  have hp := hd'.eventually (X.movers T.thaw T.b01)
  have hh := hd'.eventually T.high_live
  have hc := (T.schur_touched hk h0).cutdet P
  have hn : P.cutdet (X.schur (b 0) (v 0)) ≠ 0 := by
    dsimp only [b,v]; rw [show P.cutdet _ = _ from hc.zero,h0, input_zero]
    exact (I.endpoint.unit (D:=ridge r) hd m).ne_zero
  have hq : Q.cutdet (tonic (v 0))≠0 := by
    dsimp only [v];rw [h0,input_zero];exact (tonic_cut_unit (ridge r) m hd).ne_zero
  have ht := Det.log_schur (f.standing ha hs hp hh) f.settings f.fix (f.thick ha)
      f.full.pick12 f.throat (by
        rw [X.restored_stood hp.self_of_nhds]
        exact (grenade_safe _ X.hμ).det_pos.ne')
      (by filter_upwards [ha,hs] with _ u w using X.wort u w)
      hh.self_of_nhds.ne_zero
      (by rw [X.settings_stood,h0,T.b01];exact (tonic_cut_unit (X.back r) _ hd).ne_zero)
      hn
  -- splice to next classical jet
  have he := ((Touch.const (1/2:ℝ)).mul (hc.log hn))
  have hv := (f.front.tr.mul f.front).cutdet_cont.log hq
  have hg := (f.thick ha).add (f.fix.tr.mul f.fix)
  have hl := hg.cutdet_cont.log (Det.cutdet_nz hg.at_zero hh.self_of_nhds.ne_zero)
  have hy := f.faddeev.cutdet_cont.log
      (Det.cutdet_nz f.faddeev.at_zero ((grenade_safe _ X.hμ).det_pos.ne'))
  have hm : Touch (fun t => X.hCost r (b t) (v t)) (fun t => X.hCost r (b t) (v t)) :=
    Touch.refl ((continuousAt_const.mul hl).sub hy)
  refine (ht.congr .rfl (hp.mono fun t e => show _
      = X.hCost r (b t) (v t) + 1/2 * P.cutlog (X.schur (b t) (v t)) by dsimp only; rw [X.restored_stood e];rfl)).trans
     (hm.add he) |>.sub (Touch.refl hv) |>.congr ?_ (Eventually.of_forall fun _ => add_sub_assoc _ _ _)
  filter_upwards [ha] with t e
  dsimp only [b,v]
  rw [zCost,X.vibrant_shape e,X.settings_stood]
  rfl

include T
theorem separated {r : ℝ} (hv : X.HSafe m r) (hz : X.ZSafe m r) (w : X.Railings r m)
    (x : Link G m) (hx : (ridge r).repeats x) :
    Touch (fun t => X.zLaw m r (t•x))
       (fun t => X.hiLaw m r (t•x) + epCost (ridge r) I.p I.r (input G m (t•x))) := by
  let k := fun t:ℝ => t • x
  have h0 : k 0=0 := zero_smul ..
  have hk : ContDiffAt ℝ ω k 0 := by unfold k;fun_prop
  have h : deriv k 0=x := (ray_id x).deriv
  exact ((T.travel (C:=X.zCost r) (X.z_flat hz)).pre hk h0).touch.trans <|
    (T.separate hz.2 hk h0 (T.rail hk h0 (w hx h0 (hk.differentiableAt (by simp)) (by rw [h];exact hx)))).trans <|
    ((T.travel (C:=X.hCost r) (X.h_flat hv)).pre hk h0).touch.symm.add <|
    Touch.refl (ContinuousAt.comp (g:=epCost _ _ _ ∘ input _ _) (f:=k) (by rw [h0];exact
      (I.endpoint.data (D:=ridge r) hz.2 _).reg.continuousAt) hk.continuousAt)

end Test

end BlockTie
end ExactRunning
