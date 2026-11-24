import YM.CF.Roots.Stare
import YM.CF.Buffered.StepIdentity
/- Lemmas in C4 Covenant; extends the StepIdentity & Through & Stare arguments to arbitrarily charged Envelope inputs. `Call_H` qualifier used separately. -/
set_option autoImplicit false
set_option maxHeartbeats 280000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Advance
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree RG Py Haro AnalyticBridge.LocalGaussianLaws Pressure
open Reed (Fine think)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {M H B L : Side} {j : ℕ} {K:Teller SU.group} {ho:Odd L.val} {Y: Pricing K.j L ho (Thread K.j)} {e:ℝ}{P:Grasp Y B e}
local notation "Nc" => mid M B
local notation "Nf" => mid H B
variable (G:Ratio (mid M B) (mid H B))
variable {R:Loom (mid M B)} {X:GramM (mid H B)}{R':Loom (mid H B)}{d:ℝ}{q:Chi}
open Girt
variable (E:BaseL P G X R R' q d) (T:StepData (Domain M B) (Domain H B))
  (Q:Haro.SpaceM)(w:Odd G.count.val)
abbrev ridgeK (F:Forest (ratio G))(V:Orbit Nc)(W:Orbit Nf)(y:Phys Nf): Phys Nc:= T.density X.beta W.1 V.1 • scaleZ Q.val (coal_X (K:=K) (Y:=X) (G₀:=R) (G₁:=R') (kL:=d) (q:=q) V F W y)
local notation "κ"=> ridgeK (K:=K) (R:=R) (R':=R') (X:=X) (d:=d) (q:=q) G T Q
local notation "Ω"=> lynx K T G R' R' R X q d Q.val
include E w
lemma out_H (F:Forest (ratio G))(V:Orbit Nc)(W:Orbit Nf) {S : Finset (Single Nc)} {b: Bool} {A : FC (Single Nc)} (p:Fine (Tset Nc) S b A) (y:Phys Nf):
    let x:nomA M H B:=(seine G F q d (R' W) (R V),R V)
    beamL Nc (acts A (κ F V W y))= T.density X.beta W.1 V.1 • beamL Nf (acts (subF G K.j Q.val X.J.M w x A) y):= by
  intro x; let y':=acts (subF G K.j Q.val X.J.M w x A) y
  change beamL Nc (acts A (T.density X.beta W.1 V.1 • placeL G Q.val X.J.M x K.j y))=_
  have hp:JointB G x e:= E.trial F (R' W) V
  rw [show acts A (T.density X.beta W.1 V.1 • placeL _ _ _ _ _ _) = T.density X.beta W.1 V.1 • acts A _ from map_smul ((acts A).restrictScalars ℝ) _ _,map_smul,
    through G _ _ E.power E.size hp E.pe Q w p y]
  apply congrArg (fun z :ℂ=> T.density X.beta W.1 V.1 • z)
  change beamL Nc (Volume.placeOp (j:=K.j) G Q.val X.J.M x y')=beamL Nf y'; unfold Volume.placeOp; rw [shoulderL]
  change inner ℂ (mateK Nc) _=beamZ _ y'; rw [show inner ℂ _ _=_ from (Spire.shuttle G E.power E.size x hp E.pe X.J.M).2 (cartsL (switchG G).symm y')]; exact Fock.sigh (switchG G).symm.toEmbedding _ (shelfG ..) _ _
omit w
variable (t:T.patch.Branches T.kernel SU.group) (p:T.ratio=ratio G) {f:Orbit (mid H B)→Phys (mid H B)}(htF:RG.Envelope f)
omit E in
lemma ozzy (x:Orbit Nc)(y:Orbit Nf)(z:Phys Nf): Ω x y z=((Fintype.card (Forest (ratio G)):ℝ)⁻¹) • ∑ F, κ F x y z :=by unfold lynx; simp only [ContinuousLinearMap.smul_apply, Complex.coe_smul, ContinuousLinearMap.sum_apply]; rfl
include t htF
lemma κ_env : RG.Envelope (fun x:Orbit Nc × Orbit Nf=> Ω x.1 x.2 (f x.2)):=by
 let L(x:Orbit Nc × Orbit Nf):=T.density X.beta x.2.1 x.1.1; have hr: RG.Envelope L:=by
   unfold L StepData.density; exact RG.Envelope.sum univ (fun i (x:Orbit (mid M B) × Orbit (mid H B))=>taggedKernel T X.beta i x.2.1 x.1.1) (fun i=>env_tagged X.beta i t (measurable_fst.comp measurable_snd) (measurable_fst.comp measurable_fst))
 simp_rw [ozzy]; refine Env.scale (H:=fun _=>_) (Envelope.const _) (Env.total (g:=fun i (x:Orbit Nc × Orbit Nf)=>κ i x.1 x.2 (f x.2)) _ fun i=> ?_)
 let m(x:Orbit Nc × Orbit Nf):=coal_X (K:=K) (Y:=X) (G₀:=R) (G₁:=R') (kL:=d) (q:=q) x.1 i x.2 (f x.2)
 obtain ⟨b,a0,w0,r,l⟩:=E.cap; obtain ⟨s,u,h,d',H',u',g⟩:= E.wick
 have hf:Measurable (fun z:Orbit (mid M B)×Orbit (mid H B)=> R z.1) := r.bill.comp measurable_fst
 refine Env.scale hr (pole_w m (scaleW _ Q.val) (scaleW _ Q.val).continuous ?_); exact heat_k E.power _ H' u' g E.pe E.size (fun z:Orbit Nc×Orbit Nf=>(seine G i q d (R' z.2) (R z.1), R z.1)) (fun z => f z.2) (fun z=>E.trial ..) ((((brake G q d i E.legal.1 E.legal.2).measurable.comp ((l.bill.comp measurable_snd).prodMk hf)).prodMk hf)) (Girt.snap htF measurable_snd)
omit t htF E
variable {D:ℕ} (v:Stencil.LaurentRadius K.j L D) {U : Mark (mid M B)} {S:Support (More (mid M B))} {o:Bool}(H': AtSupport o S U)
local notation "φ" => pushMark G T K.j Q.val X.J.M w q d X.beta R
private def onR {N:Side}(v:Phys N): FC (Single N)→L[ℝ] ℂ := by
  let H : FC (Single N) →ₗ[ℂ] ℂ := ⟨⟨fun f=>letterRead f v,fun a b=> by simp only [letterRead,ContinuousLinearMap.comp_apply]; rw [act_add,map_add]⟩,fun a x=> by simp only [letterRead,ContinuousLinearMap.comp_apply]; rw [act_smul,map_smul]; rfl⟩; exact H.toContinuousLinearMap.restrictScalars ℝ
include E t htF v H' w
theorem passport: markedRead U R (fun x=>∫ y, Ω x y (f y) ∂city Nf)= markedRead (φ U) R' f :=by
  have uV : Stencil.LaurentRadius K.j G.count D := E.power.symm ▸ v
  let μ:=city (mid M B); let ν:=city (mid H B); obtain ⟨t',a,b',l,r⟩:= E.cap
  let W'(x:Orbit Nc × Orbit Nf) := Ω x.1 x.2 (f x.2); let Wp(V:Orbit (mid M B)×Orbit (mid H B)):= letterRead (U (drawn R V.1)) (W' V); let U' := gathered G K.j Q.val X.J.M w q d U
  have ht:Envelope W':= κ_env G E T Q t htF
  have hz(k):Integrable (fun s=>W' (k,s)) ν := Env.integrableX (Env.along (g:=Prod.mk k) ht (by fun_prop)) (city _)
  have hp := Env.integrableX (env_letterRead (f:=fun V : Orbit Nc × Orbit Nf=> U (drawn R V.1)) (Env.along (g:=fun v : Orbit Nc× Orbit Nf=> drawn R v.1) H'.env ((drawn_m R l.bill).comp measurable_fst)) ht) ((city Nc).prod (city Nf))
  have hW(z s): Wp (z,s)= T.density X.beta s.1 z.1 • letterRead (U' (drawn R' s) (drawn R z)) (f s) := by
    let a:= (letterRead (U (drawn R z))).restrictScalars ℝ; let A(F: Forest (ratio G)):= κ F z s (f s); let C:=Fintype.card (Forest (ratio G)); let Y':=onR (f s)
    let b(i : Forest (ratio G)):= before G K.j Q.val X.J.M w q d U i (drawn R' s) (drawn R z)
    have he(F): a (A F)=T.density X.beta s.1 z.1 • Y' (b F):= out_H G E T Q w F z s (H'.allV (drawn R z)) (f s)
    change a (Ω z s (f s)) =_ • Y' ((C:ℝ)⁻¹ • ∑ i, b i); rw [show Ω z s (f s)=(C:ℝ)⁻¹ • ∑ i,A i from ozzy ..,map_smul,map_smul,map_sum,map_sum,smul_sum]; simp_rw [he]; rw [←smul_sum, ← smul_sum, smul_comm ((C:ℝ)⁻¹)]
  have hY(s : Orbit Nf): Integrable (fun t:Orbit Nc=> T.density X.beta s.1 t.1 • U' (drawn R' s) (drawn R t)) μ := Env.integrableX (Env.scale (Env.along (slice_env T X.beta t _) measurable_fst) (Env.along (g:=fun t:Orbit Nc=>(drawn R' s,drawn R t)) (env_gathered G K.j Q.val X.J.M w q d uV E.legal.1 E.legal.2 U H'.env) (measurable_const.prodMk (drawn_m R l.bill)))) (city Nc)
  calc
    _ = ∫ t,(∫ s,Wp (t,s) ∂ν) ∂μ := by apply integral_congr_ae; filter_upwards with z; exact ((letterRead (U (z.1,R z))).integral_comp_comm (hz z)).symm
    _ = ∫ s,(∫ t,Wp (t,s) ∂μ) ∂ν := (integral_prod Wp hp).symm.trans (integral_prod_symm Wp hp)
    _ = _:= by
      apply integral_congr_ae; refine Filter.Eventually.of_forall fun y=>?_ ; change (∫ t,Wp (t,y) ∂μ)=onR (f y) (φ U (drawn R' y)); simp_rw [hW]; rw [outright G T K.j Q.val X.J.M w q d X.beta R uV l.bill t E.legal.1 E.legal.2 U H'.env]; have hh:= (onR (f y)).integral_comp_comm (hY y); simp_rw [map_smul] at hh; exact hh
end YM.CF.Buffered.Advance
end
