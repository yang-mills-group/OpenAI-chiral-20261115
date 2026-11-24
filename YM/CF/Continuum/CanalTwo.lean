import YM.CF.Continuum.Canal
import YM.CF.Continuum.Loop
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 800000
set_option quotPrecheck false
namespace YM.CF.Window
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Lat Cube RP Push.GridApprox Next.Rank.Thirst
open scoped Topology BigOperators Classical
variable {c f B m:Side}(P:Patch)(s:Axis)
local notation "GX"=>SU.group
local notation "M"=> CSide m B
/-- `ξTape`: localized space/time cylinder, positive with a fixed-after-L margin. No positivity presupposed. -/
abbrev ξTape(s:Axis)(P:Patch)(c:Side)(X:Config SU.group (More c)→ℂ) := Cells.Interior (buffered s P c) X
abbrev θBack(s:Axis){c:Side}(X:Config SU.group c→ℂ): Config SU.group c→ℂ := star ∘ X ∘ pull (Signed.mirror s) 0
lemma ξ_fwd (H:StepData (More c) (More f))(hp:H.patch=P)(pP:H.patch.Branches H.kernel GX){X:Config GX (More c)→ℂ}(e:ξTape s P c X)(b:ℝ) : ξTape s P f (back H b X):=by
 let h:= H.isKernel pP b; have ht:Envelope X:=⟨e.borel,e.cost⟩; let F:=back H b X; have hf:=back_env h ht
 refine ⟨fun t U=>?_,hf.meas,(back_local pP ht e.localSites b _ (fun i hi=>by rw [hp]; exact buff_far P s H hp i hi)),hf.cost⟩ -- `hp ▸` changes all P (target f buffer!)
 let g:=t ∘ H.ratio.embed; have hv:= back_natural h ht (gauge t) (gauge g) (prior_gauge g) fun x v=>H.covary pP t b x v; rw [show X ∘ gauge g=X from funext fun x=>e.gauge g x] at hv; exact (congrFun hv U).symm
lemma θ_back_env {X: Config GX c→ℂ}(v:Envelope X):Envelope (θBack s X):= (v.comp_env (continuous_pull ..).measurable).starC
lemma ξ_fact (H:StepData (More c) (More f))(e:H.patch.Branches H.kernel SU.group)
   {X Y:Config GX (More c)→ℂ}(v:Envelope X)(w:Envelope Y)(h:LocalOn (↑(buffered s P c)) X)(t:LocalOn (↑(buffered s P c)) Y)(β:ℝ) : back H β ((θBack s X)*Y) =(θBack s (back H β X))*back H β Y :=by
 let U:= pull (Signed.mirror s) (0:Site (More c)) (K:=SU.group.El); let V:= pull (Signed.mirror s) (0:Site (More f)) (K:=SU.group.El)
 let k:= H.isKernel e β; have ht:back H β (θBack s X)=θBack s (back H β X):=by
    have he:=back_natural k v V U (prior_pull ..) (fun x y=> show H.density β (V x) (U y)= H.density β x y from (by unfold V; simpa only [← Ratio.root_embed, map_zero] using H.channel e (Signed.mirror s) 0 β x y)); apply (back_star k (F:=X ∘ U) (v.comp_env (prior_pull ..).measurable)).trans; exact congrArg (star ∘ ·) he
 rw [←ht]; exact back_factors e (θ_back_env s v) w (fun x y v=> congrArg star (p_local (Signed.mirror s) 0 _ h x y v)) t (buff_disjoint P s).symm _ -- tune p_local `..` can't chain
open SU Fock Scroll Tulip Reed Tenant
lemma ξ_obs (X: Bkg (More M)→ℂ)(v: Continuous X)(p: LocalOn (↑(buffered s P (CSide m B))) X)(e:GaugeInvariant X) : bosonic (CSide m B) X ∈ nonnegativeTime m B s:=by
 apply localObs_enlarge (G:=E₁ m B s) le_rfl (empty_subset _); apply bosonic_local X v _ _ e
 intro i j q; refine p i j (fun x h k=> q x (mem_filter.mpr ⟨mem_univ _, buff_up P s _ _ h,buff_up P s _ _ k⟩))
lemma θ_bosonic (X: Config SU.group (More (CSide m B))→ℂ) : flipTime m B s (bosonic (CSide m B) X)=bosonic (CSide m B) (θBack s X):=by funext x; unfold flipTime bosonic θBack; rw [mirrorPane_eq]; simp only [Fock.theta_smul,Fock.theta_one]; rfl
lemma boseP {n:Side}(A B:Config SU.group (More n)→ℂ) : bosonic n A * bosonic n B=bosonic n (A*B):=by
 funext x; change A x • 1 * (B x • 1) = (A x*B x) • (1:FC (Single n)); rw [Algebra.smul_mul_assoc,one_mul,smul_smul]
end YM.CF.Window
