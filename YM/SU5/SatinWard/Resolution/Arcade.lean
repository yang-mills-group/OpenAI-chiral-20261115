import YM.SU5.SatinWard.Resolution.Berry
import YM.SU5.SatinWard.Resolution.Rivar
import YM.CF.BProof.Stave.Iso
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.LitCurrent.Surplus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open _root_.Zephyr.Chern
section frob
open SU
open scoped Matrix.Norms.Frobenius Matrix BigOperators
lemma polar_amount : ‖polarLie‖^2= (2:ℝ)/5 :=by
 have hp:= CF.BProof.Mesh.Stave.size_R (group.colorMat polarLie); rw [Gauge.colorMat_norm,mul_pow,Gauge.colorScale_sq,Gauge.colorMat_project_self _ focal_has] at hp; change (5:ℝ) * ‖polarLie‖^2=(focalLieᴴ*focalLie).trace.re at hp; have he:(focalLieᴴ*focalLie).trace.re=2:= by rw [focalLie,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal,Matrix.trace_diagonal]; change (Finset.sum (univ:Finset (Fin 5)) (fun i=> star (Complex.I* (dye.val i:ℂ)) * (Complex.I* (dye.val i:ℂ)))).re=_; norm_num [Fin.sum_univ_succ,dye]
 linarith only [hp,he]
end frob
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{P T:SOp N}{a b d v g t u:ℝ}{r k:ℕ}
variable {p:BudgetPoint} {K:Scree.Loom N}{e:ℝ}{q:ℕ} (z:Checked p K e d a k q)(E:Pattern P T r d a v)
variable (bI:Chamber.Division)(x:Site N)(s:Sweep N)(B:ℕ) (h: 2*(B+1)<(More N).val)
local notation "ξ" => node x
variable (yQ:4*(B+separation (node x) 1+2)+1< N.val) (pS:s.charge=false)(vX:QuadClock.Earlier s x x)
open Next.Rank Next.Rank.Spindle
local notation "AΘ" => _root_.Zephyr.Chern.arc
local notation "U" => turntable N
local notation "Y" => (flashA s ∘ (turntable N))
include z
local notation "J" => install B ξ ∘L collectF B ξ h
local notation "ϕ" => btax K p bI x k E
local notation "Φ" => orientF s.s B
local notation "H" => btaxpayer bI x E (k:=k)
private lemma germ_spell (X':tangD N):bud (fun q:ℝ=> ϕ (increment 1 (q • X'))) 2=H X' X':=by
 let f: tangD N→ℂ:= untouched (Chamber.grantA bI E x) k ∘ increment 1
 have he:(fun q:ℝ=>ϕ (increment 1 (q • X'))) =ᶠ[𝓝 0] fun q=>f (q • X'):= (bunhat_germ bI x z E).comp_tendsto (show Tendsto (fun q:ℝ=> q • X') (𝓝 0) (𝓝 0) from by simpa using (show Continuous fun q:ℝ=> q • X' by fun_prop).continuousAt.tendsto (x:=0))
 rw [bud_congr he]; change deriv (deriv fun q:ℝ=>f (q • X')) 0/2= (2:ℝ)⁻¹ • fderiv ℝ (fderiv ℝ f) 0 X' X'
 have h':=Spindle.upon X' f 2 (show ContDiffAt ℝ (↑(2:ℕ)) _ _ from (bunhat_smooth bI x z E).of_le (by norm_cast))
 rw [iteratedFDeriv_two_apply,iteratedDeriv_succ,iteratedDeriv_one] at h'; rw [h']; norm_num [Complex.real_smul]; ring
include yQ h pS vX 
lemma berry_calculus (t₀:B=p.B): blapAsset bI x k B h E Φ= bud (fun t=> ϕ (Y t)) 2:=by
 have hv:pose s x=x := unaryN (by rw [pose_node, Equiv.symm_apply_eq]; exact (show boxA s ξ=node x from vX).symm) -- vX neq synt

 change H (J Φ) (J Φ)=_; rw [← germ_spell z E bI x (J Φ)] -- bad
 refine congrFun (bud_congr ?_) _
 obtain ⟨v,tK⟩:= tanks_live z.angle; let Vp:=fun q:ℝ=> q • (J Φ); let V:= increment 1 ∘ Vp; let hF:ContinuousAt Vp 0:= (show Continuous Vp from by unfold Vp; fun_prop).continuousAt
 have ht: ∀ᶠ t in 𝓝 0, ‖Vp t‖ ≤ v:= hF.norm.tendsto.eventually (ge_mem_nhds (by unfold Vp; rw [zero_smul,norm_zero]; exact tK.size))
 have hj: Tendsto Vp (𝓝 0) (𝓝 0):=by simpa [ContinuousAt,Vp] using hF
 filter_upwards [ht,petal_on p (offsetMask p.B x) (_root_.Zephyr.Chern.stream N), hj.eventually (bunhat_germ bI x z E)] with t v hs hx
 change ϕ (V t) = untouched (Chamber.grantA bI E x) k (V t) at hx
 let hu:= tK.paid _ _ v
 symm; change ϕ (Y t)=ϕ (V t); rw [hx,← btax_invariant bI x z E (fingers (Y t) ξ)]; refine btax_degree bI x z E _ (V t) ((pingB ..).2 ?_) ?_ (agrees_mono (berry_guise x s B h yQ pS vX t) (Corona.halo_mono (by have hp:=z.extra; omega : k≤B) (Subset.refl _)))
 · -- adapt gauge term
   change pingS _ _ (flashA s (U t)); nth_rw 1[←hv]; rw [offset_pose]; exact (Salt.glowA _ _ _ _).mpr hs
 exact ⟨fun x i j g=>(hu.1 x i j g).trans (half_le_self z.angle.le), fun x i j g=>(hu.2 x i j g).trans (half_le_self z.angle.le)⟩
lemma style_receipt (pB:B=p.B)(w:Bud (btraceF bI E x K p k)):
    blapAsset bI x k B h E Φ=(if det_S s then (-1:ℂ) else 1)* bud (btraceF bI E x K p k) 2:=by
 have hp:pose s x=x:= unaryN (by rw [pose_node, Equiv.symm_apply_eq]; exact (show boxA s ξ=node x from vX).symm)
 let F:=fun t=>ϕ (Y t); let C:ℂ:=if det_S s then -1 else 1
 have hY:F = fun t=> C* btraceF bI E x K p k t:=by
    funext i; change ϕ (flashA s _)= _; have h₁:=btax_pose bI x z E s (U i); rw [hp] at h₁; rw [h₁]; unfold C; split <;> simp [*,btraceF]
 rw [berry_calculus z E bI x s B h yQ pS vX pB,show bud F= _ from show bud F=C • bud (btraceF bI E x K p k) from by rw [hY]; exact (w.bloom.scale C).bud_eq]; rfl
open AnalyticBridge.VerifiedReset
omit yQ pS vX
local notation "A"=> FrameA B
local notation "σ"=> s.s
noncomputable def berry_map (s:Signed)(B:ℕ): SU.group.Color→ₗ[ℝ] FrameA B:= LinearMap.pi (fun i=> orientAx s i.val.2 • (LinearMap.id (R:=ℝ) (M:=group.Color)))
lemma accountant_color (s:Signed) {v:group.Color} (t:‖v‖=1): blapAsset bI x k B h E (berry_map s B v)=(5/2:ℂ)* blapAsset bI x k B h E (orientF s B) :=by
 let L:=(J).toLinearMap.comp (berry_map s B)
 let a(x y:group.Color):ℂ := H (L x) (L y) + H (L y) (L x)
 let c:group.Color→ₗ[ℝ]group.Color→ₗ[ℝ]ℂ:= {
    toFun x:={ toFun y:=a x y
               map_add' y z:=by unfold a; simp only [map_add,_root_.add_apply]; abel
               map_smul' y z:=by unfold a; simp only [map_smul, _root_.smul_apply]; change _=_ • _; rw [smul_add]; rfl }
    map_add' x y:=by ext1 v; change a (x+y) v= a x v+a y v; unfold a; simp only [map_add,_root_.add_apply]; abel
    map_smul' x y:=by ext1 v; change a (x • y) v= x • a y v; unfold a; simp only [map_smul,_root_.smul_apply]; rw [smul_add] }
 let hM (g:group.El)(u:tangD N) : H (colorMove g u) (colorMove g u) = H u u:=by
    rw [←germ_spell z,←germ_spell z]; refine congrFun (congrArg bud (funext (fun i:ℝ=>?_))) _; rw [←map_smul,exp_move]; exact btax_invariant bI x z E _ _ -- x conflicts
 have he: H (L polarLie) (L polarLie) + H (L polarLie) (L polarLie) = inner ℝ polarLie polarLie • a v v:= by
   refine StressFlux.bilinear_invariant Thera.yet_one c ?_ t polarLie polarLie -- refine syntax
   intro g X' Y'; change a (group.adjoint g X') (group.adjoint g Y')=a X' Y'
   
   have ht(i:Word B)(X:group.Color): Spindle.stage i (berry_map s B (group.adjoint g X))= group.adjoint g (Spindle.stage i (berry_map s B X)):=by
      unfold Spindle.stage; rw [map_list_sum,List.map_map]; apply congrArg List.sum; apply List.map_congr_left; intro i _; simp only [berry_map,LinearMap.pi_apply] -- tune
      change (if i.2 then -(orientAx s i.1.val.2 • (group.adjoint g X)) else orientAx s i.1.val.2 • (group.adjoint g X))=(group.adjoint g) (if i.2 then -(orientAx s i.1.val.2 • X) else (orientAx s i.1.val.2 • X)); split <;> simp only [map_neg,map_smul]
   have hL(X:group.Color):L (group.adjoint g X)= colorMove g (L X):=by
      funext i; change (if t:i∈Spindle.Room (node x) B then _ else _) = group.adjoint g (if t:i∈Spindle.Room (node x) B then _ else _); split; next t=> exact ht _ _
      exact (map_zero _).symm
   have hx(x y:tangD N): H (x+y) (x+y) - H x x - H y y = H x y + H y x:=by simp only [map_add, _root_.add_apply]; abel
   unfold a; rw [hL,hL, ←hx, ←hx,←map_add (colorMove g),hM,hM,hM]
 change H (L v) (L v)= (5/2:ℂ)* H (L polarLie) (L polarLie); let b:= H (L polarLie) (L polarLie); let d:= H (L v) (L v); rw [real_inner_self_eq_norm_sq,polar_amount, Complex.real_smul] at he; change b+b= (↑((2:ℝ)/5):ℂ)*(d+d) at he; norm_num at he -- maybe fails since push
 change d=_*b
 calc _ = (5/2:ℂ)*(2:ℂ)⁻¹*((2:ℂ)/5*(d+d)):=by ring
      _ = _:=by rw [← he]; ring
#print axioms accountant_color
end YM.CF.LitCurrent.Surplus
