import YM.CF.BPress.Sweep
import YM.CF.BPress.Law
import YM.CF.Girt.East
import YM.CF.Girt.Oar
/-! Exact gauge fixing equality for equivariant integrands. Exterior covariance of `integrand` includes bra with occupancy. Apply conditional Haar on the `arrange` construction one time, no Mark-only normalization here. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function MeasureTheory LocalH Lattice SU Mag Cube Grid Filter Branch Sheet Tunnel Finset RG
open Wilson Law Push.SectorMeasure Env
open scoped Topology BigOperators Classical Matrix
variable {s : Side}{G:BandWidth}(X : Bands s G)
namespace Bands
def frozen (a:Mach s): Prop := ∀ i∈X.dc, Set.EqOn a 1 (X.band i)
def hold (U : Micro s) : Prop:= ∀ i∈ X.poles,U i=1
def tone (U : Micro s): Micro s:= rep X.poles 1 U
@[fun_prop] lemma tone_meas : Measurable X.tone:= (rep_joint X.poles).comp (f:=fun x:Micro s=>((1:Micro s),x)) (measurable_const.prodMk measurable_id)
lemma tone_hold (U : Micro s): X.hold (X.tone U):= fun i p=> if_pos p
-- `arrange U` depends ONLY on native forest links. Rep is over fresh prior on rest. Can apply the full gauge to the filler.
lemma collapse (U V:Micro s)(a:Mach s) (p : a=X.arrange U): gauge a (rep X.poles U V)=X.tone (gauge a V):=by
 funext i; by_cases w:i∈X.poles; have ht: a=X.arrange (rep X.poles U V):=p.trans (X.agree_p U fun i h=>(Law.rep_L X.poles U V i (Finset.mem_coe.mp h)).symm); rw [ht, X.poles_zero _ i w,tone,Law.rep_L _ _ _ i w]; rfl
 rw [tone, Law.rep_R _ _ _ i w,Lattice.gauge, Law.rep_R _ _ _ i w,Lattice.gauge]
open Scree Skye Girt
variable {N : Side}(Z:Bands (More N) G)
lemma freeze (f : Orbit N→ ℂ)(p:Envelope f)(v:∀ a:Mach (More N), Z.frozen a → ∀ x,f (gird a x)=f x):
 (∫ x, f x ∂city N) = ∫ U, (∫ y,f (Z.tone U,y) ∂depot N) ∂prior group (More N):=by
 let μ:=prior group (More N); let F(U : Micro (More N)):= ∫ y,f (U,y) ∂depot N; have he : Envelope F:= marginal (g:=fun x:Ids N× Micro (More N)=> f x.swap) (Env.along p measurable_swap) _
 have t (a:Mach (More N))(h:Z.frozen a)(U:Micro (More N)): F (gauge a U)= F U:=by
   unfold F; rw [restore _ _ _ (threads a) (fun y:Ids N=> f (gauge a U,y)) (integrableX (Env.along p (g:=fun y=> (gauge a U,y)) (measurable_const.prodMk measurable_id)) _)]; exact integral_congr_ae (Eventually.of_forall fun i=> v a h (U,i))
 rw [city, integral_prod _ (integrableX p _)]; change (∫ x,F x ∂chain group.probHaar _)=(∫ x,F (Z.tone x)∂μ); rw [splice_mem Z.poles _ F he]; let g:= ∫ x,F (Z.tone x)∂μ
 have h(U:Micro (More N)):(∫ x,F (rep Z.poles U x)∂μ)=g:=by
    let a:=Z.arrange U; have h(V:Micro (More N)): F (rep Z.poles U V)=F (Z.tone (gauge a V)):= (Eq.trans (t a (fun i h=> Z.fixes_D U i h) _).symm (congrArg F (Z.collapse U V a rfl))) -- tune
    simp_rw [h]; exact (restore _ _ _ (prior_gauge a) (fun x=> F (Z.tone x)) (integrableX (Env.along he Z.tone_meas) _)).symm
 change ∫ U, _ ∂μ=g; -- rw h via μ
 change ∫ U, (∫ x,F (rep Z.poles U x)∂μ)∂μ=g; simp_rw [h]; simp -- lhs simp maybe simp define μ
end Bands
open Tulip Lat Fixed Dial Fock Skye Girt Paige Peaks Scree
open scoped Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N:Side} (S : Support (More N)) (g:Mach (More N))
lemma put_a (e : Set.EqOn g 1 S) {i : Single N}(p:i∈matterRegion N S): acts (tradew N g).val (basisKet i)=basisKet i:=by
 apply PiLp.ext; rintro ⟨⟨x,j⟩,k⟩; rcases i with ⟨⟨y,l⟩,k'⟩; rw [basis_act,basis_apply]; by_cases l0:x=y <;> by_cases q:j=l <;> try solve| simp [tradew,jump_apply,Matrix.one_apply,l0,q]
 subst y; subst l; have ht:g (node x)=1:= e ((mem_matterRegion ..).mp p); simp only [tradew,jump_apply,ht, map_one]; simp [Matrix.one_apply] -- tune
lemma inactive (e : Set.EqOn g 1 S) {q : Bool} {A:FC (Single N)} (p:Sector (matterRegion N S) q A): twist (quantU (tradew _ g)) A=A:=by
 have h(i:Single N)(p:i∈ matterRegion N S): twist (quantU (tradew _ g)) (put i)=put i:= by rw [←create_put,twist_create, put_a S g e p]
 induction p with
 | zero=> exact map_zero _
 | one=> rw [twist_formula,mul_one]; exact (quantU _).property.2
 | up=> apply h; assumption
 | down=> rw [takeF,map_star, h _ (by assumption)]
 | add _ _ ih it=> rw [map_add, ih,it]
 | mul _ _ ih it=> rw [map_mul, ih,it]
 | scale _ c ih=> rw [twist_scalar, ih]
lemma idle {A: Fixed.Test N} {C : ℝ} (p : Set.EqOn g 1 S)(h:IsMark S A C)(U : Micro (More N)): A (gauge g U)=twist (quantU (tradew _ g)) (A U):=by
 rw [inactive S g p (h.even U)]; apply h.reads; intro i k l; unfold Lattice.gauge; simp only [p k,p l, Pi.one_apply, one_mul,inv_one,mul_one]
lemma integrand_env {S : Support (More N)}{F : Fixed.Test N}{f: Orbit N→ Phys N}{C:ℝ}(p:IsMark S F C)(h: Envelope f) : Envelope (integrand F f):=by
 obtain ⟨K,k⟩:=h.cost; have he :=p.nonneg; let g:=fun z : FC (Single N)× Phys N=> beamZ N (acts z.1 z.2); refine ⟨((show Continuous g from continuous_const.inner ((acts_cont.comp continuous_fst).clm_apply continuous_snd)).measurable).comp (f:=fun x:Orbit N=>(F x.1,f x)) ((p.borel.comp measurable_fst).prodMk h.meas), C*K,fun U=>?_ ⟩
 let i:=F U.1; let a:=f U; refine (norm_inner_le_norm (𝕜:=ℂ) (mateK N) (acts i a)).trans ?_; rw [(tickB N).2, one_mul]; have ht: ‖acts i‖ ≤ C:=(Matrix.l2_opNorm_toEuclideanCLM _).le.trans (p.cost U.1); exact ((acts i).le_opNorm a).trans ((mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left (k _) he))
lemma integrand_turn {F : Fixed.Test N}(p: ∀ x,F (gauge g x)=twist (quantU (tradew _ g)) (F x)){f: Orbit N→ Phys N} (h:∀ x,f (gird g x)= effectK (tradew _ g).val (f x))(x: Orbit N): integrand F f (gird g x)=integrand F f x:=by
 rw [integrand,h,gird,p (x.1)]; let U:=quantU (tradew _ g); change inner ℂ (mateK N) (acts (twist U _) (acts U.val (f x)))=_; rw [←swivel]; nth_rw 1 [←mastC g]; exact act_unit_inner U _ _
end YM.CF.BPress
