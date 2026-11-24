import YM.CF.Mint.Locket
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mint
open Function NormedSpace Filter Finset Graph Lattice Laurent Wilson Analysis Pressure Tulip Lat Cube SU Emu Rush Scree Graph RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {x y A:ℕ→ℝ}{c b w η r a e K b' v C' l s' γ μ τ H m L':ℝ}{S T:ℕ→Side}{β θ V L1 δ L:ℕ→ℝ}{J B:Side}{O:Odd J.val}{j k:ℕ}{Y:Pricing j J O (Thread j)}{P:Grasp Y B e}{hP:Pearl P}
-- nonuniform sequences. loop exponent update tracks budget. 
namespace Roe
variable {N:ℕ→Side} (D:Pic.Span hP K b' v C' l s' k) {I:∀ i,GramM (mid (N i) B)} {C Q h:ℝ}
local notation "NP"=> (fun i=> mid (N i) B)
variable (Z:WindS B N x h C r μ L' w γ c b V θ L I)
include D Z
open MeasureTheory Fock Dial
variable (F:∀ i,Loom (mid (N i) B)) (W:∀ᶠ i in atTop,SkinT (I i) (F i) e) {d vA r₀ C₀ E':ℝ}{n₀:ℕ} (U:Port D d E' C₀ vA r₀ n₀)(g:C₀ ≤h)
def prof {N:Side}(o: Site N)(i: Emu.TagT) : Opt (α:=Unit) N:=⟨o,0,[],fun _=> i⟩
-- use Nonempty.Basis tag from site. 
def tOpt(n:Side):Opt (α:= Empty) n:=⟨0,0,[],Empty.elim⟩
abbrev denQ (i:ℕ):ℂ:= Complex.exp (-(I i).v) * partitionZ (I i) P (F i)
-- bind F issue variable I implicit
omit D Z in
lemma porx(i:ℕ): (∫ y,recW (tOpt (NP i)) P (I i) (F i) y ∂city _)=denQ (P:=P) (I:=I) F i ∧ (∫ y,baseW (tOpt (NP i)) P (I i) (F i) y ∂city _)=Graph.start (I i) P (F i):=by
 let S:=tOpt (NP i); have he(v:Phys (NP i))(U:Pane (NP i)): feel (tOpt (NP i)) U v = inner ℂ (mateK (NP i)) v :=by unfold feel valA muni tOpt zoneA Emu.train; simp [rollC]
 unfold denQ partitionZ Graph.start integralF recW baseW recX Pic.beamM; simp_rw [he,inner_smul_right]; rw [MeasureTheory.integral_const_mul]; exact ⟨rfl,True.intro⟩
 
include W U g
lemma wageK: Aqua (eur NP) fun i=> ‖denQ (P:=P) (I:=I) F i -Graph.start (I i) P (F i)‖/drip (I i) P:=by
 let O(i):= tOpt (NP i); have hh: Charge Empty NP O:=⟨⟨0,Eventually.of_forall fun i=>rfl⟩,Eventually.of_forall fun i=>by simp [O,tOpt,Emu.gain]⟩
 refine (shot D Z U g O F W hh).clip Z.tend ?_
 filter_upwards [W,Z.support,touch D Z,Z.tend.eventually_ge_atTop k] with i p ⟨x,y,h,t⟩ ⟨u,q⟩ v; refine ⟨by positivity,?_⟩
 obtain ⟨A,B⟩:=Graph.integrable_s (I i) _ D p (bonB y h) (O i) (Nat.cast_le.mp v); obtain ⟨X,Y⟩:=porx (P:=P) (I:=I) F i; refine div_le_div_of_nonneg_right ?_ q.le; rw [←X,← Y,← integral_sub A B]; exact norm_integral_le_integral_norm _
def facing{n':Side}(V:GramM (mid n' B))(P:Grasp Y B e)(X:Loom (mid n' B)):= gleam n' P V.J.M * (Complex.exp (-V.v) * partitionZ V P X)
lemma costR: let c:=b'/(2*Nova.poseX); let t(i):= facing (I i) P (F i)
 (∀ᶠ i in atTop, Integrable (denZ (I i) P (F i)) (city _) ∧ 0 <Graph.angle (I i) ∧0<drip (I i) P∧ drip (I i) P * (c/2) ≤ (t i).re ∧ (t i)≠0∧ (t i).re >0 ∧ ‖denQ (P:=P) (I:=I) F i‖≥(drip (I i) P)*(c/2) ∧partitionZ (I i) P (F i) ≠0)∧ Aqua (eur NP) fun i=> |(t i).im| / drip (I i) P:=by
 intro c t; obtain ⟨T,V,v⟩:= caesar D Z; let R(i):= gleam (N i) P (I i).J.M; let a(i):=drip (I i) P; let G(i):=Graph.start (I i) P (F i); let D'(i):= R i*G i; let S:= denQ (P:=P) (I:=I) F
 have hc:0<c:=by unfold c; have ht:=D.pos; have he:= pose_p; positivity
 let Q(i):= ‖S i-G i‖/a i; have hA:Aqua (eur NP) Q:= wageK D Z F W U g; let Y(i):= duty (eur NP i) (T i) C' 0; have ht:Aqua (eur NP) Y:=by unfold Y duty; simp only [zero_mul,add_zero]; exact V.fed ((Gray.coef Z.tend C').mul ((Gray.arg Z.tend).powG Z.tend 10)) Z.tend
 have hx:∀ᶠ i in atTop, a i*c≤(D' i).re ∧ |(D' i).im| ≤ Y i*a i ∧ ‖R i‖=1:=by
    filter_upwards [Z.support,W,Mint.Roe.touch D Z,v] with i ⟨_,J,h,_⟩ w ⟨u,p⟩ e; have hu:= stoutC D (I i) (F i) (bonB J h) w e u.le; exact ⟨hu.1,hu.2.1,(gleams D e.frame _).1⟩
 have hp(i)(h:0<a i)(p:‖R i‖=1): ‖t i-D' i‖=Q i*a i:=by change ‖R i*S i-R i*G i‖ =_; unfold Q; rw [←mul_sub, norm_mul,p,one_mul,div_mul_cancel₀ _ h.ne']
 constructor
 · filter_upwards [hx,W,Z.support,v,touch D Z,hA.shrinks.eventually (ge_mem_nhds (by positivity :0<c/2))] with i ⟨p,y,h⟩ w ⟨_,J,u,_⟩ l ⟨pv,f⟩ k; have hq:Q i≤c/2:=k; have hf:0<a i:=f; have he:= Complex.abs_re_le_norm (t i-D' i); rw [hp i f h, Complex.sub_re] at he; have hg:a i*(c/2) ≤ (t i).re:=by nlinarith [abs_le.mp he]
   have hY:0<(t i).re:= (mul_pos hf (by positivity)).trans_le hg; have hz:t i≠0:=fun v=>by rw [v] at hY; exact (lt_irrefl _ hY); -- tune
   obtain ⟨x,l',m⟩:=w.wave; have hv:= sailW (I i) (bonB J u) hP D.stmt D.eP D.p l' (F i) m (D.plan _ l.frame).1
   exact ⟨Integrable.of_bound hv.meas.aestronglyMeasurable _ (Eventually.of_forall hv.cost.choose_spec),pv,f,hg,hz,hY,(hg.trans (Complex.re_le_norm _)).trans_eq (by change ‖R i*S i‖=_; rw [norm_mul,h,one_mul]),fun e=>hz (by unfold t facing; rw [e,mul_zero,mul_zero])⟩
 refine (ht.panel hA).clip Z.tend ?_; filter_upwards [hx,touch D Z] with i ⟨p,x,h⟩ ⟨u,l⟩; refine ⟨by positivity,?_⟩; apply (div_le_iff₀ l).mpr; have he:= Complex.abs_im_le_norm (t i-D' i); rw [hp i l h,Complex.sub_im] at he; change _ ≤ (Y i+Q i)*a i; rw [add_mul]; have hv:= abs_le.mp x; have hz:= abs_le.mp he; apply abs_le.mpr; constructor<;> linarith
end Roe
end YM.CF.Mint
