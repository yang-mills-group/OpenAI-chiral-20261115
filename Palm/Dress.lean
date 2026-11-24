import YM.CF.Buffered.StepIdentity
import YM.CF.Roots.Stare
set_option autoImplicit false
set_option maxHeartbeats 900000
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
variable (Kst:Pressure.Teller SU.group)(hj:Kst.j=j)
open Pressure Py
local notation "Up"=> lynx Kst T G R' R' R Z q d Q.val
include K h
lemma posted (F:Forest (ratio G))(p:Orbit Nc)(s:Orbit Nf)(y: Phys Nf):
    let x:nomA M H B:=(seine G F q d (R' s) (R p),R p)
    beamL Nc (acts (f (drawn R p)) (T.density Z.beta s.1 p.1 • placeL G Q.val Z.J.M x j y)) =
         T.density Z.beta s.1 p.1 • beamL Nf (acts (subF G j Q.val Z.J.M w x (f (drawn R p))) y) := by
  intro x; let y':=acts (subF G j Q.val Z.J.M w x (f (drawn R p))) y
  let A: FC (Single (mid M B)):=f (drawn R p)
  have hp:JointB G x e := K.trial F (R' s) p
  rw [show acts (f (drawn R p)) (T.density Z.beta s.1 p.1 • placeL _ _ _ _ _ _) = T.density Z.beta s.1 p.1 • acts A _ from map_smul ((acts A).restrictScalars ℝ) _ _,map_smul,
    through G _ _ K.power K.size hp K.pe Q w (h.allV _) y]
  apply congrArg (fun z :ℂ=> T.density Z.beta s.1 p.1 • z)
  change beamL Nc (Volume.placeOp (j:=j) G Q.val Z.J.M x y')=beamL Nf y'
  unfold Volume.placeOp; rw [shoulderL]
  change inner ℂ (mateK Nc) _=beamZ _ y'
  rw [show inner ℂ _ _=_ from (Spire.shuttle G K.power K.size x hp K.pe Z.J.M).2 (cartsL (switchG G).symm y')]
  exact Fock.sigh (switchG G).symm.toEmbedding _ (shelfG ..) _ _
omit h
include p B' w Q hj
lemma lynx_env (X: Orbit Nf→ Phys Nf) (t:RG.Envelope X) : RG.Envelope (fun i:Orbit Nc × Orbit Nf=> (Up i.1 i.2) (X i.2)):=by
 subst j
 let cn (F: Forest (ratio G))(i:Orbit Nc × Orbit Nf):= (coal_X (K:=Kst) (Y:=Z) (G₀:=R) (G₁:=R') (kL:=d) (q:=q) i.1 F i.2) (X i.2)
 let Tt(i:Orbit Nc × Orbit Nf):=T.density Z.beta i.2.1 i.1.1
 let n(F:Forest (ratio G))(i:Orbit Nc × Orbit Nf):=Tt i • scaleZ Q.val (cn F i)
 have hz:RG.Envelope Tt:=by unfold Tt StepData.density; exact RG.Envelope.sum univ _ (fun W=>env_tagged Z.beta W B' (by fun_prop) (by fun_prop))
 obtain ⟨a,b,b',v1,v2⟩:=K.cap
 have hp(F:Forest (ratio G)): RG.Envelope (cn F):=by
    obtain ⟨ss,a,h',dd,H,t',g⟩:= K.wick
    let Mz(i: Orbit Nc × Orbit Nf):=(seine G F q d (R' i.2) (R i.1), R i.1)
    have hm:Measurable Mz:= (((brake G q d F K.legal.1 K.legal.2).measurable.comp ((v2.bill.comp measurable_snd).prodMk (v1.bill.comp measurable_fst))).prodMk (v1.bill.comp measurable_fst))
    let F':=fun i:Orbit Nc × Orbit Nf=> X i.2
    exact Girt.heat_k (pM:=Z.J.M) K.power _ H t' g K.pe K.size Mz F' (fun i=>K.trial ..) hm (Env.along t measurable_snd)
 have H:RG.Envelope (fun i:Orbit Nc × Orbit Nf=> ((Fintype.card (Forest (ratio G)):ℝ)⁻¹) • ∑ F:Forest (ratio G),n F i):= Env.scale (Envelope.const _) (Env.total _ (fun F=>Env.scale hz (Girt.pole_w (cn F) _ (Girt.scaleW _ Q.val).continuous (hp F))))
 -- D may not infer type annotations. simp to H
 conv in ((Up _ _) _) =>
    unfold lynx
    simp only [ContinuousLinearMap.smul_apply, Complex.coe_smul, ContinuousLinearMap.sum_apply]
 exact H

include h v

theorem earnLynx (x: Orbit Nf → Phys Nf) (hcx:RG.Envelope x):
    markedRead f R (fun i=> ∫ v, Up i v (x v)∂city Nf) = markedRead (φ f) R' x := by
  subst j
  have uV : Stencil.LaurentRadius Kst.j G.count D := K.power.symm ▸ v
  let μ:=city (mid M B); let ν:=city (mid H B)
  obtain ⟨t,a,b',l,r⟩:= K.cap
  let W := fun i:Orbit Nc => fun j:Orbit Nf=> Up i j (x j)
  let w' := uncurry W; let Wp(V:Orbit (mid M B)×Orbit (mid H B)):= letterRead (f (drawn R V.1)) (w' V); let U := gathered G Kst.j Q.val Z.J.M w q d f
  have ht:Envelope w':= lynx_env G K T B' p Q w Kst rfl x hcx
  have hz(t):Integrable (fun s=>w' (t,s)) ν := Env.integrableX (Env.along (g:=Prod.mk t) ht (by fun_prop)) (city _)
  have hp := Env.integrableX (env_letterRead (f:=fun V : Orbit Nc × Orbit Nf=> f (drawn R V.1)) (Env.along (g:=fun v : Orbit Nc× Orbit Nf=> drawn R v.1) h.env ((drawn_m R l.bill).comp measurable_fst)) ht) ((city Nc).prod (city Nf))
  have hW(t s): Wp (t,s)= T.density Z.beta s.1 t.1 • letterRead (U (drawn R' s) (drawn R t)) (x s) := by
    let a:= (letterRead (f (drawn R t))).restrictScalars ℝ; let A(F:Forest (ratio G)):= T.density Z.beta s.1 t.1 • placeL G Q.val Z.J.M (seine G F q d (R' s) (R t), R t) Kst.j (x s)
    let C:=Fintype.card (Forest (ratio G)); let X:=rightOn (x s)
    let b(i : Forest (ratio G)):= before G Kst.j Q.val Z.J.M w q d f i (drawn R' s) (drawn R t)
    have he(F: Forest (ratio G)): a (A F)=T.density Z.beta s.1 t.1 • X (b F):= posted G K T Q w h F t s (x s)
    change a ((lynx Kst T G _ _ _ _ _ _ _ _ _) _) = _; unfold lynx; simp only [ContinuousLinearMap.smul_apply, Complex.coe_smul,ContinuousLinearMap.sum_apply]
    change a ((C:ℝ)⁻¹ • ∑ i, A i) = _ • X ((C:ℝ)⁻¹ • ∑ i, b i); rw [map_smul, map_smul,map_sum,map_sum,smul_sum]; simp_rw [he]; rw [←smul_sum, ← smul_sum, smul_comm ((C:ℝ)⁻¹)]
  have hY(s : Orbit Nf): Integrable (fun t:Orbit Nc=> T.density Z.beta s.1 t.1 • U (drawn R' s) (drawn R t)) μ := Env.integrableX (Env.scale (Env.along (slice_env T Z.beta B' _) measurable_fst) (Env.along (g:=fun t:Orbit Nc=>(drawn R' s,drawn R t)) (env_gathered G Kst.j Q.val Z.J.M w q d uV K.legal.1 K.legal.2 f h.env) (measurable_const.prodMk (drawn_m R l.bill)))) (city Nc)
  calc
    _ = ∫ t,(∫ s, Wp (t,s) ∂ν) ∂μ := by
      apply integral_congr_ae; filter_upwards with z; exact ((letterRead (f (z.1,R z))).integral_comp_comm (hz z)).symm
    _ = ∫ s,(∫ t, Wp (t,s) ∂μ) ∂ν := (integral_prod Wp hp).symm.trans (integral_prod_symm Wp hp)
    _ = _:= by
      apply integral_congr_ae; refine Filter.Eventually.of_forall fun y=> ?_; change (∫ t,Wp (t,y) ∂μ)=rightOn (x y) (pushMark G T Kst.j Q.val Z.J.M w q d Z.beta R f (drawn R' y)); simp_rw [hW]; rw [outright G T Kst.j Q.val Z.J.M w q d Z.beta R uV l.bill B' K.legal.1 K.legal.2 f h.env]; have hh:= (rightOn (x y)).integral_comp_comm (hY y); simp_rw [map_smul] at hh; exact hh
end Advance
end YM.CF.Buffered
#print axioms YM.CF.Buffered.Advance.earnLynx
