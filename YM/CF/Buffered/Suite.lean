/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Buffered.Airs
/-!
# Restrict physical link kernel to window on the seam-matched repeat. Use labels-on-site marginal & first-period-block match. Discard all seam-crossing costs only because perLink & perSite normalized POINTWISE and marked dependences do not use those bolts.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option maxHeartbeats 490000
noncomputable section
namespace YM.CF.Buffered.Mail.Radiant
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RG Wilson ProbabilityTheory
open Region Roost Rails Mil Fock Scroll Spire Push.SectorMeasure Ordered Cin Tree Tulip Rush Lifted Heat Solid Burn Advance Vale Skye
open Further.PhysicalPeriodLimitF933 Macrame Crust Grid Push.GridApprox
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
-- ignoring all links in outside the first block while remembering densities at its own boundaries (then massage boundary off).
section product
variable {I J X:Type*}[Fintype I][Fintype J] (e:I ↪ J)
abbrev other (e:I↪J): Type _:= {j:J // ¬ j∈Set.range e}
def keysZ : I⊕(other e)≃ J:= by classical exact ((Equiv.ofInjective e e.injective).sumCongr (Equiv.refl (other e))).trans (Equiv.sumCompl fun j=> j∈Set.range e)
lemma key_in (i:I) : keysZ e (Sum.inl i)=e i:=rfl
lemma key_out (j:other e): keysZ e (Sum.inr j)=j.val:=rfl
def mapa (X:Type*) := (Equiv.sumPiEquivProdPi (fun _: I⊕other e=> X)).symm.trans (Equiv.piCongrLeft (fun _:J=> X) (keysZ e))
variable {f:(J→X)→ℂ}{p:(I→X)→ℂ}(q:J→ X→ℂ)
lemma sums_t [Fintype (other e)] (x:I→X)(y:other e→X) : ∏ i,q i (mapa e X (x,y) i)=(∏ i,q (e i) (x i))*∏ i:other e,q i.val (y i):=by
 rw [← Equiv.prod_comp (keysZ e) (fun i=> q i (mapa e X (x,y) i)),Fintype.prod_sum_type]; unfold mapa; simp_rw [Equiv.trans_apply,Equiv.piCongrLeft_apply_apply,key_in,key_out]; rfl
variable (u:∀ X,f X=p (X ∘ e))
include u
lemma coats (x:I→X)(y:other e→X) : f (mapa e X (x,y))= p x:= by rw [u]; refine congrArg p (funext fun i=>?_); unfold mapa; dsimp only [Function.comp_apply,Equiv.trans_apply]; nth_rw 1 [←key_in]; rw [Equiv.piCongrLeft_apply_apply]; rfl
lemma countMP [Fintype X][DecidableEq J][DecidableEq I](v:∀ i,∑ s,q i s=1): (∑ t:J→X,(∏ i,q i (t i))*f t)=∑ t:I→X, (∏ i,q (e i) (t i))*p t:=by
 classical
 rw [← Equiv.sum_comp (mapa e X), Fintype.sum_prod_type]; refine sum_congr rfl fun i _=>?_ ; simp_rw [coats e u,sums_t e]; simp_rw [mul_right_comm (a:=∏ l,q (e l) (i l))]; rw [←mul_sum,← Fintype.prod_sum (fun i : other e => q i.val)]; simp [v]
lemma integrateMP [MeasurableSpace X](μ:Measure X)[IsFiniteMeasure μ](h:∀ i,∫ x,q i x ∂μ=1):
 (∫ x:J→X,(∏ i,q i (x i))*f x∂Measure.pi fun _=> μ)=(∫ x:I→X,(∏ i,q (e i) (x i))*p x∂Measure.pi fun _=> μ):=by
 classical
 let A: ((I→X)×(other e→X))≃ᵐ(J→X) :=(MeasurableEquiv.sumPiEquivProdPi (fun _: I⊕other e=> X)).symm.trans (MeasurableEquiv.piCongrLeft (fun _:J=>X) (keysZ e))
 let V:= (Measure.pi fun _:I=>μ); let Q:Measure (other e→ X):= Measure.pi fun _=>μ
 have he:MeasurePreserving A (V.prod Q) (Measure.pi fun _=>μ):= (measurePreserving_piCongrLeft (fun _: J=>μ) _).comp (measurePreserving_sumPiEquivProdPi_symm (X:=fun _=> X) (fun _=> μ))
 rw [←he.integral_comp' (fun x:J→X=> (∏ i,q i (x i))*f x)]; change (∫ x, (∏ i,q i (mapa e X x i))* f (mapa e X x) ∂V.prod Q)=_
 let k(x:I→X):=(∏ i,q (e i) (x i))*p x; let l(y:other e→X):=∏ i:other e,q i.val (y i)
 have ht(x:(I→X)×(other e→X)):(∏ i,q i (mapa e X x i))* f (mapa e X x)= k x.1 * l x.2:=by cases x; rw [coats e u,sums_t e]; unfold k l; ring
 simp_rw [ht]; rw [integral_prod_mul k l, show (∫ y,l y∂Q)=1 from ?_,mul_one]
 unfold l Q; rw [integral_fintype_prod_eq_prod (fun i: other e=> q i.val)]; simp [h]
end product
variable {K V C F k v N P L D M B B' l c f: Side} {G:Gauge} {S:Patch}
variable (A:Planck C c D) (a:2 ≤ c.val){ℓ:F.val=C.val*S.L.val}{d:f.val=c.val*S.L.val}
local notation "r" => decreed ℓ
local notation "t" => decreed d
local notation "F₀" => trim (ℓ:=ℓ) (d:=d) A a
local notation "Lq" => Lace.project (h:=d) (H:=ℓ) A.ratio a
variable (Q:KernelChoices)
local notation "Y" => stepped Q ℓ
local notation "T" => stepped Q d
local notation "Y₁" => (StepData.SitesChoice (stepped Q ℓ))
local notation "T₁" => (StepData.SitesChoice (stepped Q d))
local notation "s" => pointO A 0
variable (β:ℝ) {v:Support C}
private def siteT (R:StepData C F)(U:Config G F)(i:Site C)(v:R.patch.FrameTag):ℂ:= perSite R U i v
private def linkT (R:StepData C F)(β:ℝ)(U:Config G F)(z:R.SitesChoice)(i:Edge (Site C))(x:G.El):ℂ:=perLink R β U z i x
private lemma fundsS (R:StepData C F)(g:R.patch.Branches R.kernel G)(U:Config G F)(i): ∑ x,siteT R U i x=1:=by unfold siteT perSite; rw [←Complex.ofReal_sum,R.patch.frameMass_sum g]; rfl
private lemma fundsV (R:StepData C F)(U:Config G F)(z)(i):(∫ x,linkT R β U z i x∂G.probHaar)=1:= (integral_ofReal (𝕜:=ℂ) (f:=perLink R β U z i)).trans (by rw [perLink_mass]; rfl)
private lemma envV (R:StepData C F)(U:Config G F)(z)(i): Envelope (linkT R β U z i):= Envelope.compactC (Complex.continuous_ofReal.comp (perLink_cont ..))
private def purse (R:StepData C F)(β:ℝ)(U:Config G F)(z:R.SitesChoice)(V':Config G C→ℂ) :=∫ i,(∏ j,linkT R β U z j (i j)) * V' i∂prior G C
private lemma hands (R:StepData C F)(U:Config G F)(T':Config G C→ℂ)(u:Envelope T'):
 back R β T' U=∑ z:R.SitesChoice,(∏ i,siteT R U i (z i))*purse R β U z T' :=by
 unfold back; simp_rw [density_parts,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_prod,Finset.sum_mul,mul_assoc]; rw [integral_finsetSum]; · simp_rw [integral_const_mul]; rfl
 intro i _; refine Integrable.const_mul ?_ _; apply Envelope.integrableC; exact (Envelope.prodC _ (fun j (V:Config G C)=> linkT R β U i j (V j)) (fun j _=> (envV β R U i j).comp_env (measurable_pi_apply _))).mulC u
variable (X:Config G f)(z:(stepped Q ℓ).SitesChoice) (v:Support C)
local notation "Y₀" => weave (trim (ℓ:=ℓ) (d:=d) A a) X
lemma frame_rep (i:Site c): siteT Y Y₀ (s i)=siteT T X i:=by
 funext x; unfold siteT perSite; rw [show expandAt ((Y).ratio.embed _) (Y₀)=_ from (show expandAt ((r).embed _) ((Lq).high.links X)=_ from (Lq).high.expansion _ X),show (Lq).high.cut _=_ from (Lq).stake (s i),show (Lq).low.cut _=_ from stepR A 0 i]; -- tune
 rfl
local notation "y" => (z ∘ pointO A 0)
def boltX:= (pointO A 0).prodMap (Embedding.refl Axis)
variable (h:v⊆blockF A 0)(g: Config G C→ℂ)(p: LocalOn v g)(u:Envelope g)
include h
lemma connector (e: Edge (Site C))(w:e.1∈v)(t':e.1+step e.2∈v):
 StepData.connector Y Y₀ z e=(T).connector X (z ∘ pointO A 0) ((slump A).cut e.1,e.2):=by
 have he(i:Site C)(v:i∈blockF A 0) : expandAt ((Y).ratio.embed i) (Y₀)=expandAt ((T).ratio.embed ((slump A).cut i)) X := by
    rw [show expandAt ((Y).ratio.embed _) (Y₀)=_ from (show expandAt ((r).embed i) ((Lq).high.links X)=_ from (Lq).high.expansion _ X), show (Lq).high.cut _=_ from (Lq).stake i]; rfl
 unfold StepData.connector StepData.frames; dsimp only [Function.comp_apply]
 rw [he _ (h w),he _ (h t'),← Macrame.Window.step_up (slump A),restep A 0 (h w),restep A 0 (h t')]
private def combined (A:Planck C c D)(U:Config G C)(i:Edge (Site c)): G.El:=U (boltX A i)
include p u
private lemma purser : purse Y β Y₀ z g=purse T β X (z ∘ pointO A 0) (g ∘ weave A):=by
 let V_:=actualEdges (v : Set (Site C)); let Fv:= linkT Y β Y₀ z; let Uv:= linkT T β X (z ∘ pointO A 0)
 let pick(i:Edge (Site C)) :=if i.1∈blockF A 0 then Uv ((slump A).cut i.1,i.2) else Fv i
 have ht(i:Edge (Site c)): pick (boltX A i)=Uv i:=by
    obtain ⟨i,k⟩:=i; change (if s i∈blockF A 0 then Uv _ else Fv _)=Uv (i,k); rw [if_pos ((atF ..).2 (ledge_of ..))]; change Uv ((slump A).cut (pointO A 0 i),k)=_; rw [stepR]
 have hs(i): Envelope (pick i):=by unfold pick; split <;> exact envV ..
 have hx(i): (∫ x,pick i x∂G.probHaar)=1:=by unfold pick; split_ifs <;> exact fundsV ..
 have hg: Set.EqOn Fv pick V_:=by
    intro i a'; have hv: i.1 ∈ v∧ i.1+step i.2∈v:=a'; unfold pick; rw [if_pos (h hv.1)]; funext x; unfold Fv Uv linkT perLink; rw [connector A a Q X z v h i hv.1 hv.2]; rfl
 have hu(W: Config G C) : g W=(g ∘ weave A) (W ∘ boltX A):=by
    refine p _ _ fun i x s'=>?_ ; unfold Mail.weave Macrame.Window.links; change W i= W (pointO A 0 ((slump A).cut i.1),i.2); rw [restep A 0 (h x)]
 change (∫ i:Edge (Site C) → G.El,(∏ j,Fv j (i j)) * g i∂Measure.pi fun _=>G.probHaar)=_; rw [pi_ignores (μ:=G.probHaar) (q:=Fv) (q':=pick) (read_edges p) u (fundsV β _ _ z) hx (envV β _ _ z) hs hg]; rw [integrateMP (boltX A) pick hu G.probHaar hx]; simp_rw [ht]; rfl
include a X β h p u -- never try w/o law
variable (A₁:S.Branches Q G)
include A₁
lemma joint_step : back Y β g Y₀= back T β (g ∘ weave A) X:=by
 let R:=siteT Y Y₀; let f(z:T₁):=purse T β X z (g ∘ weave A); rw [hands β Y (Y₀) g u, hands β T X (g ∘ weave A) (u.comp_env (weave_cont A).measurable)]; rw [countMP (pointO A 0) R (p:=f) (fun z=> purser A a Q β X z v h g p u) (fundsS Y A₁ _)] -- tune z binder leaking? includes X
 apply sum_congr rfl; intro i _; change (∏ j:Site c, R (pointO A 0 j) (i j))* _=_; simp_rw [show ∀ j:Site c,R (pointO A 0 j)=siteT T X j from (frame_rep A a Q X)]; rfl
end YM.CF.Buffered.Mail.Radiant
#print axioms YM.CF.Buffered.Mail.Radiant.joint_step
