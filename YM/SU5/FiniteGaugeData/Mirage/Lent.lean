import YM.SU5.FiniteGaugeData.Mirage.Lorne
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest.Chaperone
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Heat Brique Window.Brique Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
set_option quotPrecheck false
open Tint Window.Brique
open scoped ENNReal
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
variable {u v:ℕ→ℕ}{E:ℕ→Family (tent Y h)→ℂ} {I:ℕ→Family (tent Y h)→ℕ→ℂ} (s i k:ℕ)
section
open Journey FullBill
local notation "N"=> side Y i s
local notation "V"=> (tent Y h)
local notation "Fₛ"=> (Y.voyage i).CapeT s
local notation "W"=> ((Y.voyage i).X (Y.uv k)).gram s
private lemma sale_p (f:LinksC→ℂ): sold Y h s i (scalar V (f ∘ Prod.fst))= fun x=> f (onC N x.1) • 1:= by
 unfold sold; exact castK (terrain Y h (Y.ir i) s) f
where castK {n m:Side}(h:n=m)(V':LinksC→ℂ):ship h (fun x:Fields n=> V' (onC n x.1) • 1) =(fun x:Fields m=> V' (onC m x.1) • 1):=by subst m; rfl
variable {σ:Window.Family}{S U:Finset Cover}{t:List Cover}(Q:Finset (Face ℤ)){X:Family (tent Y h)} (p: InTest (tent Y h) true S false X) (q:carpet Q⊆S)
local notation "Yᵣ" x:max=> ((shineB x Q (tent Y h))*X)
include p q
/- strengthen assumption at a STORAGE wavelength regardless of N. Then transport neighborhood support selection. DCT does not appeal to continuum tape. -/
private lemma huy (e:MarkGate Y s i k):Tendsto (fun i'=> sharp Y h s i k (Yᵣ (germB i'))) atTop (𝓝 (sharp Y h s i k X)):=by
 have hs (r:ℝ):InTest V true S false (Yᵣ r):=((InTest.seed (amber_cost r Q|>.mono q) : InTest V false S false _).widen).mul p; let a(t:Family V)(x:Orbit N):= letterRead (sold Y h s i t (drawn Fₛ x)) (denZ W Λ.U Fₛ x); let K:= (∫ x,a X x∂city N)
 have he (x:Family V)(p:InTest V true S false x): Integrable (a x) (city N):=by
    obtain ⟨y,rfl⟩:=Hierarchy.certify _ _ _ p; exact mark_legit Y h S s i k e y
 have hx (r:ℕ)(x:Orbit N): a (Yᵣ (germB r)) x= amber (germB r) Q (onC N x.1) * a X x:=by
    simp only [a,sold_mult,shineB,sale_p,Pi.mul_apply, Algebra.smul_mul_assoc,one_mul]; exact (mark_linear _ 0 _ _).2 -- tune
 have hv:Tendsto (fun r:ℕ=> (∫ x, a (Yᵣ (germB r)) x∂city N)) atTop (𝓝 K):= by
    refine tendsto_integral_of_dominated_convergence (fun x=> ‖a X x‖) (fun r=> (he _ (hs _)).1) (he X p).norm (fun i=> Eventually.of_forall fun r=> ?_) ?_
    · rw [hx,norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (amber_bounded ..)
    exact (amber_house Q).mono (fun x h=> tendsto_const_nhds.congr' (h.mono fun i p=>by dsimp only; rw [hx,p,one_mul]))
 let C:= partitionZ W Λ.U Fₛ
 simp_rw [sold_sharp]; exact hv.div_const C -- tune
variable (K:Universal Y h u v I E)
include K
-- Strong DCT on E. Requires common support class S. (variant for fixed support, general pointwise in title; stronger lemma can be obtained for arbitrary sequence with bounded supports and optional prices in Vox + opaque birthday). Geometric rates not claimed.
lemma soles : Tendsto (fun r:ℕ=> E s (Yᵣ (germB r))) atTop (𝓝 (E s X)):=by
 let YF(x:ℕ):= Yᵣ (germB x); let C:= duration S * ‖certifyAs S V X p‖; have hc: ∀ i x, ‖X i x‖ ≤ C:=fun i x=> (Hierarchy.certified S V X p ▸ compose_price S V _ i x) -- dependent rewrite?
 let v':= v; have hW (r:ℕ)(i x):‖YF r i x‖ ≤ C:= (norm_mul_le ..).trans (le_trans (mul_le_of_le_one_left (norm_nonneg _) (amber_r _ Q V i _)) (hc i x)); have hb:0≤ C:= (norm_nonneg _).trans (hc 1 (1,1)) -- inhabit Fields
 refine Metric.tendsto_nhds.mpr fun ε ht=>?_; obtain ⟨w₀,hP⟩:= (roomy_sides S V).exists; let τ:=ε/4; have hk:0<τ:=(by unfold τ; positivity); let T:=C+1; have hΛ:0<T:= by unfold T; positivity
 obtain ⟨i,hV,W0⟩:= (((boutique Y h K S s).2 (τ/T) (div_pos hk hΛ)).and (often_offer Y h S s K)).exists; obtain ⟨k,qK⟩:= (cadence Y v' K.pick.grow_k (u i)).exists
 let Ψ:=sharp Y h s (u i) (v k); have β(f:Family V)(p:InTest V true S false f)(x:∀ x,‖f w₀ x‖ ≤ C):‖Ψ f-E s f‖≤τ:=by
    have h:∀ w,‖f w₀ w‖ ≤ C+1:=fun w=>(x w).trans (le_of_lt (lt_add_one C)); exact ((hV f p w₀ (roomy_hosp _ hP) T h).2 k qK).trans (div_mul_cancel₀ τ hΛ.ne').le
 have h':‖Ψ X-E s X‖ ≤ τ:= β X p (hc w₀)
 filter_upwards [((huy Y h s (u i) (v k) Q p q (markGate_o Y S s _ _ (W0 k qK)).1).eventually (Metric.ball_mem_nhds _ hk))] with r q'
 have h₀:=Metric.mem_ball.mp q'; rw [dist_eq_norm] at h₀; change dist (E s (YF r)) _<_; rw [dist_eq_norm];
 let x:=YF r; have hm:‖Ψ x- E s x‖ ≤ τ:= β x (((InTest.seed (amber_cost _ Q|>.mono q) : InTest V false S false _).widen).mul p) (hW r _); have he:‖Ψ x-Ψ X‖ < τ:= h₀; rw [norm_sub_rev] at hm; change ‖E s x-E s X‖ < ε; linarith only [hm,he,h',norm_sub_le_norm_sub_add_norm_sub (Ψ x) (Ψ X) (E s X),norm_sub_le_norm_sub_add_norm_sub (E s x) (Ψ x) (E s X), show 3*τ<ε from (by unfold τ; linarith)]
end
end YM.CF.Buffered.Afterglow.Hierarchy.Quest.Chaperone
