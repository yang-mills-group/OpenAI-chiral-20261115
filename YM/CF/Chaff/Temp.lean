import YM.CF.Chaff.Sky
import YM.Next.STATIONARY.Joint.OnShell
import YM.CF.Rill.Pott
import YM.CF.Skye.Hark
import YM.CF.Prism.Pecu
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Chaff
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Pressure
open Cube Lat Tenant Tulip Gully Spire Scroll Scree Jet Ave Skye Gas Pastry Dial Fock
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B N: Side}{a e v K H C:ℝ}{n:ℕ}
local notation "Λ" => CSide m B
local notation "ξ"=> Domain m B
local notation "G"=>SU.group
open Phase Branch
variable {D:Ave.Briar m B e→ Scree.Cipher (CSide m B)}{S:Stamp m B}
variable (p:0≤e)(h:Inscribed K e n S H D C)
local notation "Γ"=> tangD Λ
def floorP(m B:Side)(p:0≤e):Briar m B e:=⟨1, Tulip.guard0 p⟩
def polarU (m B:Side)(p:0≤e)(x:Pane (CSide m B)):Briar m B e:= if h:Guard x e then ⟨x,h⟩ else floorP m B p
lemma claw(U:Pane Λ)(g:Guard U e): polarU m B p U=⟨U,g⟩:=dif_pos g
include h
lemma floorQ (g:1≤K)(x:Briar m B e)(T:Finset (Dwell Λ)): H≥1→ ‖crumb (D x).val T‖ ≤ H⁻¹^T.card*C:=by -- include h manually
 -- tune includes
 intro u
 have hp:0<H:=zero_lt_one.trans_le u; have he:D x=D x:=rfl -- h erased. edit
 have hF: ‖dilF H (D x)‖ ≤ C:= (h.jets ℝ (fun _=>x) Set.univ isOpen_univ (fun i _ j=> allows_const _ ((CStarRing.norm_of_mem_unitary (SU.fund_U ..)).trans_le g)) 0 (Set.mem_univ _)).value
 have hg:= (norm_entry (dilF H (D x)).val T ∅).trans hF; change ‖crumb (dilF H (D x)).val T‖ ≤ C at hg; rw [dil_p,norm_mul, norm_pow,Complex.norm_real,Real.norm_of_nonneg hp.le] at hg; apply le_of_mul_le_mul_left (a:=H^T.card) (hg.trans (le_of_eq ?_)) (by positivity); rw [inv_pow,←mul_assoc,mul_inv_cancel₀ (pow_pos hp _).ne',one_mul]
omit h
lemma cPick {D E:Type}[LinearOrder D][Fintype D][NormedAddCommGroup E][NormedSpace ℝ E]{A:E→ Dough D}{x:E}(p:Allows n (fun i=>dilF H (A i)) x C)(u:0<H)(T:Finset D): Allows n (fun i=>crumb (A i).val T) x (H⁻¹^T.card * C):=by
 let W: Dough D →ₗ[ℝ] ℂ:=⟨⟨fun i=> crumb i.val T,fun _ _=> crumb_add ..⟩,fun _ _=> crumb_scaleR ..⟩ -- tune
 let L:= W.toContinuousLinearMap; have he:Allows n (fun i=>crumb (dilF H (A i)).val T) x (1*C):=by refine Allows.linear (F:=Dough D) L p ?_; apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro i; rw [one_mul]; exact norm_entry ..
 let s:=H⁻¹^T.card; have ht:= he.smul s; rw [one_mul,abs_of_pos (pow_pos (inv_pos.mpr u) _)] at ht; apply ht.germ (Eventually.of_forall fun i=>?_ ); dsimp only; rw [dil_p,Complex.real_smul,←mul_assoc]; simp [s,u.ne']
include h
abbrev VStar(n:ℕ)(K:ℝ):Prop:=∀(m:Side)(X:Pane m),∀ v:tangD m,‖v‖≤1 →TransK n (RG.increment X) v K
lemma cosy (q:VStar n K)(u:0<a)(l:a≤1)(U:Pane Λ)(g:∀ i:Γ,‖i‖<a →Guard (RG.increment U i) e):∀ i:tangD Λ, ‖i‖<a → Allows n (fun y=>dilF H (D (polarU m B p (RG.increment U y)))) i C:=by
 intro i t; let f:= polarU m B p ∘ RG.increment U; let Z:=ball (0:tangD Λ) a; refine h.jets (tangD Λ) f Z isOpen_ball (fun x h y=>?_ ) i (mem_ball_zero_iff.mpr t); have he:=mem_ball_zero_iff.mp h; apply (q Λ U x (he.le.trans l) y).germ; filter_upwards [isOpen_ball.mem_nhds h] with z hz; unfold f; rw [Function.comp_apply,claw p _ (g _ (mem_ball_zero_iff.mp hz))]
def bedH(p:0≤e)(D:Briar m B e→Cipher Λ)(X:Γ):= Pastry.pane (D (polarU m B p (RG.increment 1 X)))-Pastry.pane (D (floorP m B p))
lemma Music_p(i:Briar m B e)(g:Court m B): Pastry.pane (D (routeS g i))=Pastry.pane (D i):=by rw [h.gauge]; exact Pastry.center_b ..
lemma quest(p:0≤e)(u:SU.group.El) (v:Γ)(g:Guard (RG.increment (1:Pane Λ) v) e): bedH p D (fun i=> SU.group.adjoint u (v i))=bedH p D v:=by -- tune G notation
 unfold bedH; apply congrArg (fun y=> y-Pastry.pane (D (floorP m B p))); let V:=RG.increment (1:Pane Λ) v; let U:Court m B:=fun _=>u; rw [show RG.increment (1:Pane Λ) (fun i=>SU.group.adjoint u (v i))=Lattice.gauge U V from ?_,claw p _ (g.cov U),claw p _ g]; exact Music_p h ⟨V,g⟩ U
 funext i; simp only [RG.increment, V, Pi.one_apply,mul_one, Lattice.gauge]; exact Next.SectorChange.exp_adjoint ..
variable {t:ℝ}(q:VStar n K)(u:0<a)(l:a≤1)(g:∀ i:tangD (CSide m B),‖i‖<a→Guard (RG.increment 1 i) e)
include g q h l u
lemma fruitL(p:0≤e)(j:1 ≤n)(X:0 ≤t)(v:0<H): PhysicalNext.JointLoad.Heir.Portrait (bedH p D) 0 n t (a/2) (C+C):=by
 have he(i:Γ)(hx:‖i‖<a): Allows n (fun i=> Pastry.pane (D (polarU m B p (RG.increment 1 i)))) i C:=by
    have h' := cPick (A:=fun i=>D (polarU m B p (RG.increment 1 i))) (cosy p h q u l (1:Pane Λ) g i hx) v ∅; rw [card_empty,pow_zero,one_mul] at h'; exact h'
 have hp:a/2<a:=half_lt_self u; have ht:polarU m B p (RG.increment 1 0)=floorP m B p:=by rw [show RG.increment 1 0=(1:Pane Λ) from (funext fun i=>by simp [RG.increment]),claw p _ (guard0 p)]; rfl
 let D':=bedH p D
 have hh:= (he 0 (by rwa [norm_zero])).value; rw [ht] at hh
 have hK(i:Γ)(hx:‖i‖<a): Allows n D' i (C+C):= Newt.subtract_p (he i hx) (allows_const i hh)
 refine ⟨fun i x=>let p:=hK i (x.trans_lt hp); ⟨p.1,p.2⟩,by simp only [bedH,ht,sub_self],?_⟩
 change ‖fderiv ℝ D' 0-0‖ ≤ _; have hv: fderiv ℝ D' 0=0:=by
    apply ContinuousLinearMap.ext; apply Stationary.slot_fixed Thera.yet_one (fderiv ℝ D' 0); intro y z
    let L:Γ→L[ℝ]Γ:= ContinuousLinearMap.pi (fun i=> (SU.group.adjoint y).toContinuousLinearMap ∘L ContinuousLinearMap.proj i)
    apply Stationary.chain_fixed L _ ((hK 0 (by rwa [norm_zero])).smooth.differentiableAt (by exact_mod_cast (by omega: n≠0))) z
    filter_upwards [ball_mem_nhds 0 u] with x hx using quest h p _ _ (g _ (mem_ball_zero_iff.mp hx))
 rw [hv,sub_zero,norm_zero]; exact mul_nonneg (add_nonneg h.pos h.pos) X
end YM.CF.Chaff
