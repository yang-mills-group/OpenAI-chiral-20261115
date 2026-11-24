import SatinThinVersion
import YM.CF.Buffered.PushMark
import YM.CF.Buffered.Through

/-!
# Dual lift. Adapt Verified the same-draw marked integral identity
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
namespace Advance
open QuadClock Pressure Py Vale Vale.Grace
variable {M H B :Side}{L:ChartRatio SU.group}{R₀:Patch}{J:Teller SU.group}(ZL:Grace J R₀ L){e:ℝ}{P:Grasp ZL.U B e}
variable (G : Ratio (mid M B) (mid H B))
local notation "Nc" => mid M B
local notation "Nf" => mid H B
variable {X : GramM (mid M B)} {R : Loom (mid M B)} {Z : GramM (mid H B)} {R' : Loom (mid H B)} {d : ℝ} {q : Chi}
variable (K : Girt.BaseL P G Z R R' q d) (T : RG.StepData (More (mid M B)) (More (mid H B)))
  (B' : T.patch.Branches T.kernel SU.group) (p : T.ratio=ratio G) (Q : Haro.SpaceM) (w : Odd G.count.val)
  {D : ℕ} (v : Stencil.LaurentRadius J.j R₀.L D)
local notation "φ" => pushMark G T J.j Q.val Z.J.M w q d Z.beta R
variable {f : Mark (mid M B)} {S : Support (More (mid M B))} {b : Bool} (h : AtSupport b S f)
theorem projectedBelow (E:Girt.BaseL P G Z R R' q d) (T:RG.StepData (More Nc) (More Nf))
    (Q:Haro.SpaceM)(w : Odd G.count.val) (F:Forest (ratio G))(V:Orbit Nc)(W:Orbit Nf) {S : Finset (Single Nc)} {b : Bool} {A : FC (Single Nc)} (y :Phys Nf)(p : Fine (Tset (mid M B)) S b A) :
    let x:nomA M H B:=(seine G F q d (R' W) (R V),R V)
    beamL Nc (acts A (T.density Z.beta W.1 V.1 • placeL G Q.val Z.J.M x J.j y)) =
         T.density Z.beta W.1 V.1 • beamL Nf (acts (subF G J.j Q.val Z.J.M w x A) (y)) := by
  intro x; let y':=acts (subF G J.j Q.val Z.J.M w x A) y
  change beamL Nc (acts A (T.density Z.beta W.1 V.1 • placeL G Q.val Z.J.M x J.j y))=_
  have hp:JointB G x e:= E.trial F (R' W) V
  rw [show acts A (T.density Z.beta W.1 V.1 • placeL _ _ _ _ _ _) = T.density Z.beta W.1 V.1 • acts A _ from map_smul ((acts A).restrictScalars ℝ) _ _,map_smul,
    through G _ _ E.power E.size hp E.pe Q w p y]
  apply congrArg (fun z :ℂ=> T.density Z.beta W.1 V.1 • z)
  change beamL Nc (Volume.placeOp (j:=J.j) G Q.val Z.J.M x y')=beamL Nf y'
  unfold Volume.placeOp; rw [shoulderL]
  change inner ℂ (mateK Nc) _=beamZ _ y'
  rw [show inner ℂ _ _=_ from (Spire.shuttle G E.power E.size x hp E.pe Z.J.M).2 (cartsL (switchG G).symm y')]
  exact Fock.sigh (switchG G).symm.toEmbedding _ (shelfG ..) _ _
private def rightOn (v : Phys N) : FC (Single N)→L[ℝ] ℂ := by
  let H : FC (Single N) →ₗ[ℂ] ℂ := ⟨⟨fun f=>letterRead f v,fun a b=> by simp only [letterRead,ContinuousLinearMap.comp_apply]; rw [act_add,map_add]⟩,fun a x=> by simp only [letterRead,ContinuousLinearMap.comp_apply]; rw [act_smul,map_smul]; rfl⟩
  exact H.toContinuousLinearMap.restrictScalars ℝ
include K T B' v h
theorem pushCloud_step (x:Orbit Nf→Phys Nf)(z:Envelope x): markedRead f R (pushCloud (K:=J) d G T R R' Z q Q.val x)=markedRead (φ f) R' x:=by
  have uV : Stencil.LaurentRadius J.j G.count D := K.power.symm ▸ v
  let μ:=city (mid M B); let ν:=city (mid H B)
  obtain ⟨t,a,b',l,r⟩:= K.cap
  let W (y:Orbit Nc)(w:Orbit Nf):=lynx J T G R' R' R Z q d Q.val y w (x w)
  let w' := uncurry W; let Wp(V:Orbit (mid M B)×Orbit (mid H B)):= letterRead (f (drawn R V.1)) (w' V); let U := gathered G J.j Q.val Z.J.M w q d f
  have ht:Envelope w':= envelope_fly ZL Q.val (b:=K) B' x z
  have hz(t):Integrable (fun s=>w' (t,s)) ν := Env.integrableX (Env.along (g:=Prod.mk t) ht (by fun_prop)) (city _)
  have hp := Env.integrableX (env_letterRead (f:=fun V : Orbit Nc × Orbit Nf=> f (drawn R V.1)) (Env.along (g:=fun v : Orbit Nc× Orbit Nf=> drawn R v.1) h.env ((drawn_m R l.bill).comp measurable_fst)) ht) ((city Nc).prod (city Nf))
  have hW(t s): Wp (t,s)= T.density Z.beta s.1 t.1 • letterRead (U (drawn R' s) (drawn R t)) (x s) := by
    let a:= (letterRead (f (drawn R t))).restrictScalars ℝ; let A(F: Forest (ratio G)):=T.density Z.beta s.1 t.1 • placeL G Q.val Z.J.M (seine G F q d (R' s) (R t), R t) J.j (x s)
    let C:=Fintype.card (Forest (ratio G)); let X:=rightOn (x s)
    let b(i : Forest (ratio G)):= before G J.j Q.val Z.J.M w q d f i (drawn R' s) (drawn R t)
    have he(F: Forest (ratio G)): a (A F)=T.density Z.beta s.1 t.1 • X (b F):= projectedBelow ZL G K T Q w F t s (x s) (h.allV (drawn R t))
    unfold Wp w' uncurry; dsimp only; unfold W lynx; simp only [ContinuousLinearMap.smul_apply,Complex.coe_smul,ContinuousLinearMap.sum_apply]
    change a ((C:ℝ)⁻¹ • ∑ i, A i) = _ • X ((C:ℝ)⁻¹ • ∑ i, b i); rw [map_smul, map_smul,map_sum,map_sum,smul_sum]; simp_rw [he]; rw [←smul_sum, ← smul_sum, smul_comm ((C:ℝ)⁻¹)]
  have hY(s : Orbit Nf): Integrable (fun t:Orbit Nc=> T.density Z.beta s.1 t.1 • U (drawn R' s) (drawn R t)) μ := Env.integrableX (Env.scale (Env.along (slice_env T Z.beta B' _) measurable_fst) (Env.along (g:=fun t:Orbit Nc=>(drawn R' s,drawn R t)) (env_gathered G J.j Q.val Z.J.M w q d uV K.legal.1 K.legal.2 f h.env) (measurable_const.prodMk (drawn_m R l.bill)))) (city Nc)
  calc
    _ = ∫ t,(∫ s, Wp (t,s) ∂ν) ∂μ := by
      apply integral_congr_ae; refine Filter.Eventually.of_forall fun z=> ?_; exact ((letterRead (f (z.1,R z))).integral_comp_comm (hz z)).symm
    _ = ∫ s,(∫ t, Wp (t,s) ∂μ) ∂ν := (integral_prod Wp hp).symm.trans (integral_prod_symm Wp hp)
    _ = _:= by
      apply integral_congr_ae; refine Filter.Eventually.of_forall fun y=> ?_; change (∫ t,Wp (t,y) ∂μ)=rightOn (x y) (φ f (drawn R' y)); simp_rw [hW]; rw [outright G T J.j Q.val Z.J.M w q d Z.beta R uV l.bill B' K.legal.1 K.legal.2 f h.env]; have hh:= (rightOn (x y)).integral_comp_comm (hY y); simp_rw [map_smul] at hh; exact hh
omit K T B' v h in
lemma read_version (A: Mark N)(l:Scree.Loom N){f g:Orbit N→Phys N}(e: f=ᵐ[city N] g): markedRead A l f=markedRead A l g:=integral_congr_ae (e.mono fun i v=>congrArg _ v)
theorem liftCloud_step (F:Orbit Nf→Phys Nf)(p:Version (city _) F):
    markedRead f R (pushCloud (K:=J) d G T R R' Z q Q.val F) = markedRead (φ f) R' F:=by
 obtain ⟨k,t,x⟩:=p; rw [push_congr Q.val t, read_version _ R' t]; exact pushCloud_step ZL G K T B' Q w v h k x
#print axioms liftCloud_step
end Advance
end YM.CF.Buffered
