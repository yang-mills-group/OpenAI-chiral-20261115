import YM.SU5.FiniteGaugeData.Signal.Breaths
import YM.SU5.FiniteGaugeData.Signal.Hatchet
import YM.CF.Pyx.Warp
import YM.CF.Buffered.Transfer
/-! # SAME gauge averages. Cost on physical moments.
 No independence of CAR/gauge; conjugate covariance at this one regulator.
 Needed to keep generous sector genuine singlet while limiting.
 -/
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option synthInstance.maxSize 16000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Signal.Scherzo
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Afterglow Buffered.Advance Reef Hom Tenant Branch Buffered.Concord Buffered.Afterglow.Satin Lifted
open Push.SectorMeasure Girt ProbabilityTheory
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate Pointwise
attribute [local instance] opCStarAlgebra
open Supplies Sparkle Sparkle.Condense Sparkle.Portage Sparkle.Circuit Pastel Momentum Furnace
variable {N n:Side}
namespace Plum

abbrev Troupe (N:Side) := Seat N→SU.E
local notation "A"=> Troupe N
lemma twistContinuous : Continuous (fun f: Troupe N=>(tradew N f).val):=by
 refine continuous_pi fun i=> continuous_pi fun j=>?_ ; unfold tradew; simp only [jump_apply]; split; exact (SU.matter_cont.comp (show Continuous (fun t:Troupe N=> t (node i.1.1)) from continuous_apply _)).matrix_elem _ _; exact continuous_const
lemma twistC : Continuous (fun a:A × FC (Single N)=>twist (quantU (tradew N a.1)) a.2):=by
 let q(a:A × FC (Single N)):= (quantU (tradew N a.1)).val; have hx:Continuous q:= quant_cont.comp (twistContinuous.comp continuous_fst); simp_rw [twist_formula]; exact (hx.mul continuous_snd).mul (continuous_star.comp hx)
lemma twistmul (u v:A) : (tradew N (u*v))=tradew N u*tradew N v:=by
 apply Subtype.ext; let F(g:A)(i:Site N×SpinIdx): Op SU.Slot:= (matter (g (node i.1))).val; change jump (Equiv.refl _) (F (u*v))=jump (Equiv.refl _) (F u) * jump (Equiv.refl _) (F v); rw [jump_mul,Equiv.trans_refl]; congr 1; funext i; unfold F; rw [Pi.mul_apply,map_mul]; rfl
local notation "U" i:max => quantU (tradew N i)
lemma twist_power (u v:A) : quantU (tradew N (u*v))= quantU (tradew N u)* quantU (tradew N v):= by rw [twistmul]; exact Subtype.ext (quant_mul ..)

variable (F: Evaluation N)
/-- like `moving` at cover. Always on gauge group of ENTIRE native torus. -/
def song (u:A) : Evaluation N:= fun x=> twist (U u) (F (Lattice.gauge u⁻¹ x))
abbrev suit (n:Side):Measure (Troupe n):= Measure.pi (fun _ => SU.group.probHaar)
def collect (F : Evaluation N) : Evaluation N:=fun x=>∫ u:A, song F u x ∂suit N
lemma envelopeS (h:Envelope F): Envelope (uncurry (song F)):=by
 let f(x:A × Pane N):=Lattice.gauge x.1⁻¹ x.2; have he:Continuous f:=by unfold f Lattice.gauge; fun_prop
 let X (p : Troupe N × FC (Single N)):=twist (quantU (tradew N p.1)) p.2; let Y(p:Troupe N × Pane N): Evaluation N:=F; let W(p:Troupe N × Pane N): Troupe N × FC (Single N) := (p.1,F (f p)); have hg: Measurable W:=Measurable.prodMk (f:=Prod.fst) (g:=F∘ f) measurable_fst (h.meas.comp he.measurable)
 have hm:Measurable X:= Continuous.measurable (f:=X) (twistC (N:=N)); constructor; · change Measurable (X∘ W); exact hm.comp hg
 exact ⟨h.cost.choose,fun x=> (twist_norm ..).trans_le (h.cost.choose_spec _)⟩
lemma localS {S:Support (More N)}(p:LocalOn S F)(u:A): LocalOn S (song F u):=fun x y t=> congrArg (twist _) (p _ _ (tied S _ _ _ _ t fun _ _=>rfl))
lemma envelope_right (h:Envelope F)(x: Pane N) : Envelope (fun u:A=> song F u x):=by
 exact Env.along (g:=fun u:A=>(u,x)) (envelopeS F h) (measurable_id.prodMk measurable_const)
lemma envelopeG (h:Envelope F): Envelope (collect F):= Env.marginal (g:=uncurry (song F)) (envelopeS F h) (suit N)
lemma sitting {S:Support (More N)}(p:LocalOn S F): LocalOn S (collect F):= fun x y t=> integral_congr_ae (Eventually.of_forall fun u:A=> localS F p u x y t)
lemma price (C:ℝ)(p:∀ x,‖F x‖≤C)(v:Pane N):‖collect F v‖ ≤ C:= (norm_integral_le_of_norm_le_const (C:=C) (Eventually.of_forall fun u:A=> (show ‖song F u v‖≤_ from (twist_norm ..).trans_le (p _)))).trans_eq (by simp)
lemma collect_port {L:List (Site N)}{S:Finset (Site N)}{l:Flavor}(p:∀ x:Pane N, F x∈ generous l S L)(x:Pane N)(h:Envelope F): collect F x∈ generous l S L:=by
 let K:= (generous l S L).restrictScalars ℝ; exact K.convex.integral_mem K.closed_of_finiteDimensional (Eventually.of_forall fun i:A=> (show song F i x∈ K from twist_grip l S i L (p _))) (Env.integrableX (envelope_right F h x) _)
lemma lands (g:A)(x:Pane N): gauge g⁻¹ (gauge g x)=x:=congrArg Prod.fst (drawing g (x,x))
-- use measurable map cyclic in group; Haar left invariance follows products
lemma over_suit (u: Troupe N) :MeasurePreserving (MeasurableEquiv.mulLeft u) (suit N) (suit N):= measurePreserving_pi (fun _:Seat N=>SU.group.probHaar) (fun _=>SU.group.probHaar) (f:=fun i x=>u i*x) fun i=> measurePreserving_mul_left _ _
lemma closed_f (h:Envelope F) : covariant (toMark (collect F)):=by
 intro g x; let D : FC (Single N) →ₗ[ℂ] FC (Single N):={ toFun:= twist (U g), map_add':=fun _ _=>map_add _ _ _, map_smul':=fun a x=> twist_scalar _ _ _ }
 let T:= LinearMap.toContinuousLinearMap D; change (∫ i:A, song F i (gauge g x.1)∂ suit N) = T (∫ i:A, song F i x.1∂ suit N); rw [← T.integral_comp_comm (Env.integrableX (envelope_right F h x.1) _),← (over_suit g).integral_comp' (fun i=> song F i (Lattice.gauge g x.1))]; apply integral_congr_ae (Eventually.of_forall _); -- tune
 intro y; change twist _ (F (gauge (g*y)⁻¹ (gauge g x.1)))=twist (U g) (twist _ (F (gauge y⁻¹ x.1))); change twist (U (g*y)) _= _; rw [twist_power, Fock.twin, mul_inv_rev,←gauge_sq,lands]

lemma city_mp (g:Seat N→E) : MeasurePreserving (gird g) (city N) (city N):=(Wilson.prior_gauge g).prod (threads g)
def guild (g:A) : MeasurableEquiv (Orbit N) (Orbit N):= ⟨⟨gird g,gird g⁻¹,Pyx.gird_inv _,fun i=>by simpa only [inv_inv] using Pyx.gird_inv g⁻¹ i⟩,(city_mp g).measurable,(city_mp g⁻¹).measurable⟩
variable (L:Loom N)(D: Orbit N→ Phys N)
def Rotate (D:Orbit N→ Phys N):Prop:= ∀ g:A,∀ x:Orbit N,D (gird g x)=acts (U g).val (D x)
lemma track (u:A)(p: Rotate D) : markedRead (toMark (song F u)) L D=markedRead (toMark F) L D:=by
 simp only [markedRead,toMark]; rw [← (show MeasurePreserving (guild u) _ _ from city_mp u).integral_comp' (fun i: Orbit N => letterRead (song F u i.1) (D i))]; apply integral_congr_ae; filter_upwards with x; change inner ℂ _ (acts (twist (U u) (F (gauge u⁻¹ (gauge u x.1)))) (D (gird u x)))=_; rw [lands,p u x, ←Fock.swivel]; change inner ℂ (mateK N) _=inner ℂ (mateK N) (acts (F x.1) (D x)); nth_rw 1 [←(show acts (U u).val (mateK N)=_ from mastC u)]; rw [act_unit_inner]

def listen (x:Phys N): FC (Single N)→ₗ[ℂ]ℂ where
 toFun b:= letterRead b x
 map_add' a b:= (mark_linear a b x 0).1
 map_smul' c a:= (mark_linear a 0 x c).2
lemma covered (h:Envelope F)(t:Rotate D)(p:RG.Envelope D): markedRead (toMark (collect F)) L D=markedRead (toMark F) L D:=by
 let Q(u: Orbit N)(g:A):= letterRead (song F g u.1) (D u); let B(b:FC (Single N))(x:Phys N):=letterRead b x; have he:Continuous (uncurry B):= (beamL N).continuous.comp ((acts_cont.comp continuous_fst).clm_apply continuous_snd); let G(x:Orbit N × A):= (x.2,x.1.1); have hp: Measurable G := measurable_snd.prodMk (measurable_fst.comp (@measurable_fst (Orbit N) (Troupe N) _ _)); -- tune
 have hv: Envelope (fun i:Orbit N×A => Q i.1 i.2) := Girt.kitE _ _ B he (Env.along (g:=G) (envelopeS F h) hp) (Env.along p measurable_fst)
 have hz(u:Orbit N):∫ g:A,Q u g∂suit N= letterRead (collect F u.1) (D u):= by
    let T:=LinearMap.toContinuousLinearMap (listen (D u)); change (∫ g:A, T (song F g u.1)∂suit N) = T (∫ g:A, song F g u.1∂suit N)
    exact T.integral_comp_comm (Env.integrableX (envelope_right F h u.1) (suit N))
 unfold markedRead; change (∫ x:Orbit N, letterRead (collect F x.1) (D x) ∂ _) = markedRead (toMark F) L D; have hQ(g:A): ∫ x:Orbit N,Q x g∂city N=markedRead (toMark F) L D:=track F L D g t; simp_rw [←hz]; rw [integral_integral_swap (Env.integrableX hv _)]; simp_rw [hQ]; simp
end Plum
end YM.CF.Signal.Scherzo
#print axioms YM.CF.Signal.Scherzo.Plum.covered
