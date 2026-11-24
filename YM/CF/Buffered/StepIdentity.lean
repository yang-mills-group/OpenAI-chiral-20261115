import YM.CF.Buffered.PushMark
import YM.CF.Buffered.Through

/-!
# Check the same-draw marked integral identity
No choice of independent colors, tags, anchors etc. No good-field shell
leftover.
-/
set_option autoImplicit false
set_option maxHeartbeats 530000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree RG
open Reed (Fine think)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
-- reading f immediately on the bra in the same CITY evaluation
variable {N : Side}
def letterRead (f : FC (Single N)) : Phys N →L[ℂ] ℂ := (innerSL ℂ (mateK N)).comp (acts f)
def markedRead (f : Mark N) (l : Loom N) (T : Orbit N → Phys N) := ∫ V, letterRead (f (V.1,l V)) (T V) ∂city N
lemma markvac (l : Loom N) (T : Orbit N → Phys N) : markedRead 1 l T=∫ V,beamZ N (T V) ∂city N := by
  unfold markedRead letterRead; simp only [Pi.one_apply,ContinuousLinearMap.comp_apply,act_one]; rfl
section
variable {A : Type*} [MeasurableSpace A] {f : A→FC (Single N)} {g : A → Phys N}
lemma env_letterRead (p : Envelope f) (h : Envelope g) : Envelope (fun i => letterRead (f i) (g i)) := Girt.kitE f g (fun v x=> letterRead v x) (show Continuous (fun x : FC (Single N) × Phys N=>letterRead x.1 x.2) from (beamL N).continuous.comp ((acts_cont.comp continuous_fst).clm_apply continuous_snd)) p h
end
namespace Advance
variable {M H B L : Side} {j : ℕ} {ho : Odd L.val} {Y : Pricing j L ho (Thread j)}{e : ℝ} {P : Grasp Y B e}
variable (G : Ratio (mid M B) (mid H B))
local notation "Nc" => mid M B
local notation "Nf" => mid H B
variable {X : GramM (mid M B)} {R : Loom (mid M B)} {Z : GramM (mid H B)} {R' : Loom (mid H B)} {d : ℝ} {q : Chi}
variable (K : Girt.BaseL P G Z R R' q d) (T : RG.StepData (More (mid M B)) (More (mid H B)))
  (B' : T.patch.Branches T.kernel SU.group) (p : T.ratio=ratio G) (Q : Haro.SpaceM) (w : Odd G.count.val)
  {D : ℕ} (v : Stencil.LaurentRadius j L D)
local notation "φ" => pushMark G T j Q.val Z.J.M w q d Z.beta R
variable {f : Mark (mid M B)} {S : Support (More (mid M B))} {b : Bool} (h : AtSupport b S f)
omit Q T B' in
private def rightOn (v : Phys N) : FC (Single N)→L[ℝ] ℂ := by
  let H : FC (Single N) →ₗ[ℂ] ℂ := ⟨⟨fun f=>letterRead f v,fun a b=> by simp only [letterRead,ContinuousLinearMap.comp_apply]; rw [act_add,map_add]⟩,fun a x=> by simp only [letterRead,ContinuousLinearMap.comp_apply]; rw [act_smul,map_smul]; rfl⟩
  exact H.toContinuousLinearMap.restrictScalars ℝ
include p B' h K v
theorem identity_step (u : ∀ᵐ x ∂city (mid M B), Scree.stove P R Z R' G T q d Q.val x = denZ X P R x) :
    markedRead f R (denZ X P R) = markedRead (φ f) R' (denZ Z P R') := by
  have uV : Stencil.LaurentRadius j G.count D := K.power.symm ▸ v
  let μ:=city (mid M B); let ν:=city (mid H B)
  obtain ⟨t,a,b',l,r⟩:= K.cap
  let x := denZ Z P R'; let W := integrated P R Z R' G T q d Q.val
  let w' := uncurry W; let Wp(V:Orbit (mid M B)×Orbit (mid H B)):= letterRead (f (drawn R V.1)) (w' V); let U := gathered G j Q.val Z.J.M w q d f
  have ht:Envelope w':= Girt.buoy K T p B' Q.val
  have hz(t):Integrable (fun s=>w' (t,s)) ν := Env.integrableX (Env.along (g:=Prod.mk t) ht (by fun_prop)) (city _)
  have hp := Env.integrableX (env_letterRead (f:=fun V : Orbit Nc × Orbit Nf=> f (drawn R V.1)) (Env.along (g:=fun v : Orbit Nc× Orbit Nf=> drawn R v.1) h.env ((drawn_m R l.bill).comp measurable_fst)) ht) ((city Nc).prod (city Nf))
  have hW(t s): Wp (t,s)= T.density Z.beta s.1 t.1 • letterRead (U (drawn R' s) (drawn R t)) (x s) := by
    let a:= (letterRead (f (drawn R t))).restrictScalars ℝ; let A(F: Forest (ratio G)):=carrier P R Z R' G T q d Q.val F t s
    let C:=Fintype.card (Forest (ratio G)); let X:=rightOn (x s)
    let b(i : Forest (ratio G)):= before G j Q.val Z.J.M w q d f i (drawn R' s) (drawn R t)
    have he(F: Forest (ratio G)): a (A F)=T.density Z.beta s.1 t.1 • X (b F):= projected G K T Q w F t s (h.allV (drawn R t))
    change a ((C:ℝ)⁻¹ • ∑ i, A i) = _ • X ((C:ℝ)⁻¹ • ∑ i, b i); rw [map_smul, map_smul,map_sum,map_sum,smul_sum]; simp_rw [he]; rw [←smul_sum, ← smul_sum, smul_comm ((C:ℝ)⁻¹)]
  have hY(s : Orbit Nf): Integrable (fun t:Orbit Nc=> T.density Z.beta s.1 t.1 • U (drawn R' s) (drawn R t)) μ := Env.integrableX (Env.scale (Env.along (slice_env T Z.beta B' _) measurable_fst) (Env.along (g:=fun t:Orbit Nc=>(drawn R' s,drawn R t)) (env_gathered G j Q.val Z.J.M w q d uV K.legal.1 K.legal.2 f h.env) (measurable_const.prodMk (drawn_m R l.bill)))) (city Nc)
  calc
    _ = ∫ t,(∫ s, Wp (t,s) ∂ν) ∂μ := by
      apply integral_congr_ae; filter_upwards [u] with z p; rw [←p]; exact ((letterRead (f (z.1,R z))).integral_comp_comm (hz z)).symm
    _ = ∫ s,(∫ t, Wp (t,s) ∂μ) ∂ν := (integral_prod Wp hp).symm.trans (integral_prod_symm Wp hp)
    _ = _:= by
      apply integral_congr_ae; refine Filter.Eventually.of_forall fun y=> ?_; change (∫ t,Wp (t,y) ∂μ)=rightOn (x y) (φ f (drawn R' y)); simp_rw [hW]; rw [outright G T j Q.val Z.J.M w q d Z.beta R uV l.bill B' K.legal.1 K.legal.2 f h.env]; have hh:= (rightOn (x y)).integral_comp_comm (hY y); simp_rw [map_smul] at hh; exact hh
end Advance
end YM.CF.Buffered
#print axioms YM.CF.Buffered.Advance.identity_step
