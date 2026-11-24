import Gingham.Ruff.Dizi
import WakeRoad.Dipole
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.SmallLog
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 230000
noncomputable section
namespace YM.WakeRoad
open Function Filter Topology NormedSpace Finset Lattice
open CF CF.Gingham.Ruff CF.Skye CF.Tulip CF.Cube CF.Scree
open scoped ContDiff
lemma qtot {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{f:E→ℂ}{c:ℝ} (H:Gallery 3 f c)(z:fderiv ℝ f 0=0)(m:ℝ→E){x:E}(w:m 0=0)(u:HasDerivAt m x 0): Tendsto (fun t:ℝ=> (t^2)⁻¹ • (f (m t)-f 0)) (𝓝[>] 0) (𝓝 (quadraticChi f x)) := by
 let J:=𝓝[>] (0:ℝ)
 let v(t:ℝ):E:=t⁻¹ • m t
 have hv:Tendsto v J (𝓝 x):= by
   refine Tendsto.mono_left ?_ (nhdsWithin_mono (0:ℝ) (show Set.Ioi (0:ℝ) ⊆ {0}ᶜ by intro y p; exact fun q=> (show (0:ℝ)<y from p).ne (Set.mem_singleton_iff.mp q).symm)) -- want singleton complement
   simpa [slope_fun_def,v,w] using u.tendsto_slope
 let V:= quadraticChi f
 have hc: Continuous V:=by
   unfold V quadraticChi
   fun_prop
 have he:Tendsto (fun t=>V (v t)) J (𝓝 (V x)):=hc.continuousAt.tendsto.comp hv
 suffices hz:Tendsto (fun r:ℝ=> ‖(r^2)⁻¹ • (f (m r)-f 0) - V (v r)‖) J (𝓝 0) from he.congr_dist (by simpa [dist_comm (V _),dist_eq_norm] using hz)
 have ht:Tendsto (fun t:ℝ=>t) J (𝓝 0):= tendsto_id.mono_left nhdsWithin_le_nhds
 refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x:=0)) (h:=fun t=> t*(c*‖v t‖^3)) (by simpa using (ht.mul ((hv.norm.pow 3).const_mul c))) (Eventually.of_forall fun _=>norm_nonneg _) ?_
 have t:Tendsto m J (𝓝 0):=by rw [←w]; exact u.continuousAt.mono_left nhdsWithin_le_nhds
 filter_upwards [t.norm.eventually (gt_mem_nhds (by simp:‖(0:E)‖<(1:ℝ))),self_mem_nhdsWithin] with r j k
 change 0<r at k
 have m1 : m r = r • v r:= (smul_inv_smul₀ k.ne' _).symm
 have h:‖f (m r)-f 0-V (m r)‖ ≤ c*‖m r‖^3:= H.cubic z j
 rw [show V (v r)=(r^2)⁻¹ • V (m r) from ?_,←smul_sub,norm_smul,Real.norm_of_nonneg (by positivity)]
 · refine (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq ?_; rw [m1,norm_smul,Real.norm_of_nonneg k.le]; have : r≠0:=k.ne'; field_simp
 unfold V; rw [m1, quadraticChi_smul f (v r) r]; rw [inv_smul_smul₀ (pow_ne_zero _ k.ne')]

open Wilson Laurent RG
section
open scoped Matrix Matrix.Norms.Frobenius
local notation "K"=>SU.group
local notation "E"=> SU.group.Color
private def curve (r:ℝ)(v:E)(t:ℝ) := SU.group.lieExp (t • r • v)
@[simp] private lemma c0(r:ℝ)(x:E):curve r x 0=1:=by simp [curve]
private lemma curf(r:ℝ)(v:E):Continuous (curve r v):= by unfold curve; fun_prop
private lemma c1(r:ℝ)(x:E): HasDerivAt (fun t:ℝ=> SU.group.mat (curve r x t)) (SU.group.colorMat (r • x)) 0 :=by
 unfold curve; simpa [map_smul] using! (hasDerivAt_exp_smul_const (SU.group.colorMat (r • x)) (0:ℝ))
private lemma m1(r:ℝ)(x y z:E):
 HasDerivAt (fun t:ℝ=> SU.group.mat (curve r x t * curve r y t * (curve r z t)⁻¹)) (SU.group.colorMat (r • (x+y-z))) 0 := by
 simp_rw [Gauge.mat_mul,Gauge.mat_inv]
 have w:HasDerivAt (fun t:ℝ=> star (SU.group.mat (curve r z t))) (-SU.group.colorMat (r • z)) 0 := by
   simp_rw [← SU.group.colorMat_skew]
   exact (c1 r z).star
 simpa only [Pi.mul_apply,c0,smul_neg,map_neg,Gauge.mat_one,mul_one,one_mul,star_one,smul_sub,smul_add,map_add,map_sub,sub_eq_add_neg] using! ((c1 r x).mul (c1 r y)).mul w

private lemma vot : ∀ (x:E),fderiv ℝ SU.group.plog 1 (SU.group.colorMat x)=x:=by
 let Z (x:E)(v:ℝ):= SU.group.mat (curve 1 x v)
 have he(x:E): HasDerivAt (Z x) (SU.group.colorMat x) 0:=by simpa only [one_smul] using c1 1 x
 have hs(x:E): Z x 0=1:=by simp [Z]
 have hp := (SU.group.plog_diff.differentiableAt (by simp)).hasFDerivAt
 intro x
 have ht : HasDerivAt (SU.group.plog ∘ Z x) x 0 := by
    have hu : Tendsto (fun v : ℝ => v • x) (𝓝 0) (𝓝 0) := by
      simpa using! (continuous_id.smul (continuous_const (y:=x))).tendsto (0:ℝ)
    apply HasDerivAt.congr_of_eventuallyEq (f:=fun v : ℝ => v • x)
    · simpa using! (hasDerivAt_id (0:ℝ)).smul_const x
    simpa only [Filter.EventuallyEq,Z,curve,comp_def,one_smul] using! hu.eventually SU.group.plog_left
 exact (hp.comp_hasDerivAt_of_eq _ (he x) (hs x).symm).unique ht

-- possibly any orientation and color direction, post-pose
variable {N:Side}
private def tracer(r:ℝ)(a:tangD N)(x: Seat N→ E)(t:ℝ): Pane N:=
 Lattice.gauge (fun i=>curve r (x i) t) (pencil r (t • (a,(0:tangD N))))
private lemma tracer_at (r:ℝ)(a:tangD N)(x: Seat N→ E)(t:ℝ)(i: Edge (Seat N)):tracer r a x t i = curve r (x i.1) t*curve r (a i) t *(curve r (x (i.1+step i.2)) t)⁻¹:=by
 unfold tracer Lattice.gauge pencil curve
 simp only [Prod.smul_fst,Pi.smul_apply,Prod.smul_snd,Pi.zero_apply,smul_zero, Gauge.mat_lieExp_zero, mul_one, smul_smul,mul_comm r t]

private def lacing(r:ℝ)(a:tangD N)(x: Seat N → E)(t:ℝ): Doub N:=
 (fun i=> r⁻¹ • (SU.group.plog (SU.group.mat (tracer r a x t i))),0)
def abridge (a:tangD N)(x:Seat N→E):tangD N:=fun i=>x i.1+a i-x (i.1+step i.2)
private theorem top_trim (a:tangD N)(x:Seat N→E){r:ℝ}(h:0<r): HasDerivAt (lacing r a x) (abridge a x,0) 0:= by
 let f(i:Edge (Seat N))(t:ℝ):=tracer r a x t i
 have z(i:Edge (Seat N)): HasDerivAt (fun t=>SU.group.mat (f i t)) (SU.group.colorMat (r • abridge a x i)) 0:=by
   unfold f; simp_rw [tracer_at]; exact m1 ..
 have th(i:Edge (Seat N)): SU.group.mat (f i 0)=1:= by simp [f,tracer_at]
 let hp := (SU.group.plog_diff.differentiableAt (by simp)).hasFDerivAt
 have hk(i:Edge (Seat N)):HasDerivAt (fun t=>r⁻¹ • SU.group.plog (SU.group.mat (f i t))) (abridge a x i) 0:= by
    refine ((hp.comp_hasDerivAt_of_eq _ (z i) (th i).symm).const_smul r⁻¹).congr_deriv ?_
    change r⁻¹ • ((fderiv ℝ SU.group.plog 1) (SU.group.colorMat (r • abridge a x i)))= _
    exact (congrArg (r⁻¹ • ·) (vot (r • abridge a x i))).trans (inv_smul_smul₀ h.ne' _)
 exact (hasDerivAt_pi.mpr hk).prodMk (hasDerivAt_const (0:ℝ) (0:tangD N))

lemma lap_gap (a:tangD N)(x:Seat N→E){r:ℝ}(h:0<r): ∃ u:ℝ→Doub N,u 0=0 ∧ HasDerivAt u (abridge a x,0) 0 ∧
  ∀ᶠ t:ℝ in 𝓝 0, ∃ F:Seat N→SU.E,pencil r (u t)=Lattice.gauge F (pencil r (t • (a,(0:tangD N)))):= by
 refine ⟨lacing r a x,?_,top_trim _ _ h,?_⟩
 · ext i; all_goals simp [lacing,tracer_at]
 have e:∀ i:Edge (Seat N), Tendsto (fun t:ℝ=>tracer r a x t i) (𝓝 0) (𝓝 1):=by
    intro i
    simp_rw [tracer_at]; let U(z:E):Tendsto (curve r z) (𝓝 0) (𝓝 1):=by simpa using (curf r z).tendsto 0
    simpa using ((U _).mul (U _)).mul (U (x _)).inv
 have t:∀ᶠ t:ℝ in 𝓝 0,∀ i:Edge (Seat N),SU.group.lieExp (SU.group.plog (SU.group.mat (tracer r a x t i)))= tracer r a x t i:= eventually_all.mpr (fun i => (e i).eventually SU.group.plog_right)
 filter_upwards [t] with t l; exact ⟨(fun p=> curve r (x p) t), (funext fun i=>by simp only [lacing,pencil,smul_inv_smul₀ h.ne']; change _ * SU.group.lieExp (r • (0:E))= tracer r a x t i; simp [l])⟩
end

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Classical
open CF.Drapes CF.Branch CF.Jet CF.Rill CF.Tenant
open CF.Sour CF.Peaks Fock
variable {N:Side}{S: Support (More N)}{w: Toll (Single N)}{r b e:ℝ}{F:Fob N e}
    (Y:Suite (badge _) (bail N e) (bail N e) S w F)
    (M:Rialto 6 e r b)

local notation "τ"=>SU.group.Color
local notation "◴"=> hum M F
local notation "χ"=> quadraticChi (hum M F)

include Y
private theorem awakening (u v:Doub N)(hu:‖u‖<1)(hv:‖v‖<1)
    (g:Seat N→SU.E)(q:Agrees (↑S) (pencil r v) (Lattice.gauge g (pencil r u))):
    (◴) u = (◴) v:= by
 have hp:(pate M u).val=profile (pencil r u):=by simp [pate,dabble,hu]
 exact ride M Y v (pate M u) g hv _ hp q

lemma qAbridge (hr:0<r)(a:tangD N)(x:Seat N→τ) :
   (χ) (a,0) = (χ) (abridge a x,0):=by
 let V:Doub N:=(a,0)
 obtain ⟨u,p,q,l⟩:=lap_gap a x hr
 let v(t:ℝ):= t • V
 have he:HasDerivAt v V 0:= by simpa [v] using! (hasDerivAt_id (0:ℝ)).smul_const V
 have k: Tendsto u (𝓝 0) (𝓝 0):= by rw [←p]; exact q.continuousAt
 have t : v 0=0:=zero_smul ..
 have gtk: Tendsto v (𝓝 0) (𝓝 0):=by rw [←t]; exact he.continuousAt
 have hz:(fun t=> (◴) (v t))=ᶠ[𝓝 (0:ℝ)] fun t=> (◴) (u t):=by
    filter_upwards [l,k.norm.eventually (gt_mem_nhds (by simp:‖(0:Doub N)‖< (1:ℝ))),gtk.norm.eventually (gt_mem_nhds (by simp:‖(0:Doub N)‖<(1:ℝ)))] with t e p q
    obtain ⟨g,e⟩:=e
    exact awakening Y M (v t) (u t) q p g fun i _ _=>congrFun e i
 have H:= Gallery.sub (aria M Y) 3 (by norm_num:3 ≤6)
 have z:=flat_aria M Y (by omega)
 apply tendsto_nhds_unique ((qtot H z v t he).congr' ((hz.filter_mono (show 𝓝[>] (0:ℝ) ≤ _ from nhdsWithin_le_nhds)).mono fun i e=>congrArg (fun c:ℂ=> (i^2)⁻¹ • (c-(◴) 0)) e))
 exact qtot H z u p q

lemma qAgree (v u:Doub N)(h:∀ i: Edge (Seat N), i.1 ∈ S → i.1+step i.2 ∈ S → v.1 i = u.1 i ∧ v.2 i = u.2 i): (χ) v = (χ) u:=by
 have hv(t:Doub N): HasDerivAt (fun r:ℝ=>r • t) t 0:= by simpa using! (hasDerivAt_id (0:ℝ)).smul_const t
 have H:= Gallery.sub (aria M Y) 3 (by norm_num:3 ≤6)
 have z:=flat_aria M Y (by omega)
 have hg(w:Doub N):∀ᶠ r:ℝ in 𝓝 0, ‖r • w‖ < 1:= ((continuous_id.smul continuous_const).norm.tendsto 0).eventually (gt_mem_nhds (by simp))
 have he:= ((hg v).and (hg u)).mono fun t w=> awakening Y M _ _ w.1 w.2 1 (show Agrees (↑S) (pencil r (t • u)) (Lattice.gauge 1 (pencil r (t • v))) from ?_)
 swap
 · intro i k v1; obtain ⟨hw,he⟩:= h i k v1; simp [CF.Gingham.Ruff.pencil,Lattice.gauge,hw,he]
 apply tendsto_nhds_unique ((quadraticChi_pressure H z v).congr' ((he.filter_mono (show 𝓝[>] (0:ℝ) ≤ _ from nhdsWithin_le_nhds)).mono fun i e=>congrArg (fun c:ℂ=> (i^2)⁻¹ • (c-(◴) 0)) e))
 exact quadraticChi_pressure H z u
#print axioms qAbridge
