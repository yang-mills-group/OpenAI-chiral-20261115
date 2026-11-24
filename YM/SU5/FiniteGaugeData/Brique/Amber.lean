import YM.SU5.FiniteGaugeData.Brique.Chisel
import YM.CF.Fixed.Triangular
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest
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
local notation "ς"=> SU.group
local notation "μ"=> SU.group.probHaar
open Next.Rank
abbrev germB : ℕ→ℝ:= fun i=>Real.exp (-(i:ℝ))
private lemma droop:Tendsto germB atTop (𝓝 0):= Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop))
private lemma dust : (μ) (SU.group.shell 0) = 0 := by
 letI:=Gauge.Simple.nontrivial_color Thera.yet_one; have hu : SU.group.lieDim≠0:=by rw [Gauge.lieDim,← SU.group.colorIso.finrank_eq]; exact (Module.finrank_pos (R:=ℝ) (M:=SU.group.Color)).ne' -- tune
 rw [←measureReal_eq_zero_iff]; apply le_antisymm _ ENNReal.toReal_nonneg; obtain ⟨a,b,p,q,H⟩:= shell_volume SU.group; refine ge_of_tendsto (show Tendsto (fun i=> b* (germB i)^SU.group.lieDim) atTop (𝓝 0) from by simpa only [zero_pow hu,mul_zero] using (droop.pow (SU.group.lieDim)).const_mul b) (Eventually.of_forall (fun i=> le_trans ?_ (H (germB i) (Real.exp_pos _)).2))
 exact measureReal_mono (fun x h=> (show SU.group.chord x ≤0 from h).trans (Real.exp_pos _).le)
variable {m:Side}
-- the Haar pressure transfer to an elementary face, NO predicates on fields/period alignment. `m` denotes matter side.
local notation "Φ" => More m
lemma face_press (i:admiss m) : MeasurePreserving (fun v:Pane m=> faceValue v i) (Wilson.prior (ς) Φ) (μ):=by
 obtain ⟨x,⟨⟨a,b⟩,v'⟩⟩:= i; let i:= (x,a); change a<b at v'; let u':= v'.ne; let e:Set (Pane m):= Set.univ; let V(W:Pane m):= travel W x (square a b); let m':= More m
 let G(W:Pane m):= Function.update W i (V W); have hm:MeasurePreserving G (Wilson.prior (ς) (More m)) (Wilson.prior (ς) (More m)):= by
    refine Fixed.Pivots.update_preserve (μ) i V (continuous_travel _ _).measurable ?_; intro W; unfold V; simp_rw [Fixed.Pivots.square_formula (ς)]; have hvb: x + step b≠ x:=by
       intro h; have he: (1:Per (More m))=0:=(by simpa using congr_fun h b); haveI hx: Fact (1<(More m).val):= ⟨by change 1 < m.val*2; have he:=m.property; exact lt_of_lt_of_le one_lt_two (le_mul_of_one_le_left (by decide : (0:ℕ)≤2) he)⟩; exact one_ne_zero he
    simp_rw [show i=(x,a) from rfl, update_self, update_of_ne (show (x+step b,a)≠(x,a) from by simp [hvb]), update_of_ne (show (x+step a,b)≠(x,a) from by simp [u'.symm]),update_of_ne (show (x,b)≠(x,a) from by simp [u'.symm]),mul_assoc]; exact measurePreserving_mul_right (μ) _
 have hx:(fun v:Pane m=> V v)=(Function.eval i) ∘ G:= by funext v; change _=G v i; unfold G; rw [Function.update_self]
 change MeasurePreserving (fun v=> V v) _ _; rw [hx]; exact MeasurePreserving.comp (measurePreserving_eval _ _) hm
lemma wasted (i:Face ℤ):∀ᵐ x∂city m, 0 < SU.group.chord (faceValue (onC m x.1) i):=by
 have he : ∀ᵐ v∂μ, 0 < SU.group.chord v:= ae_iff.mpr (by simp_rw [not_lt]; exact dust)
 let t:admiss m:= (wrap Φ i.1,i.2)
 let H:= (face_press t).comp (show MeasurePreserving Prod.fst (city m) (Wilson.prior (ς) (More m)) from measurePreserving_fst); filter_upwards [H.quasiMeasurePreserving.ae he] with x h; rw [←press_face i (x.1,x.1)]; exact h
end
section
variable (r:ℝ) (Q:Finset (Face ℤ))(K:Calibration)
def amber (x:LinksC):ℂ:= ((∏ i∈Q, max 0 (min 1 (SU.group.chord (faceValue x i)/r-1))):ℝ)
lemma amber_bounded(V:LinksC): ‖amber r Q V‖ ≤ 1:= by
 unfold amber; rw [Complex.norm_real,Real.norm_of_nonneg (prod_nonneg (fun i _=>le_max_left ..))]; exact prod_le_one (fun i _=>le_max_left ..) (fun i _=>max_le zero_le_one (min_le_left ..))
def shineB := scalar K (amber r Q ∘ Prod.fst)
lemma amber_cost : Coeff false (carpet Q) (amber r Q ∘ Prod.fst):= by
 apply Coeff.fromC; · unfold amber faceValue; fun_prop
 intro x y t; unfold amber; apply congrArg ((↑):ℝ→ℂ); apply prod_congr rfl; intro i h; rw [show faceValue x i= faceValue y i from travel_local _ _ _ _ (fun i v w=> t i (mem_biUnion.mpr ⟨_,h,List.mem_toFinset.mpr v⟩) (mem_biUnion.mpr ⟨_,h,List.mem_toFinset.mpr w⟩))]
lemma amber_r (m:Side)(w:Fields (K.c m)) : ‖shineB r Q K m w‖ ≤ 1:=by simpa [shineB,scalar] using amber_bounded r Q (onC _ w.1)
lemma shine_spec {S U:Finset Cover}{F:Family K} {t:List Cover} {σ:Window.Family} (p: Copse K S U σ t F)(h:carpet Q⊆ S) : Copse K S U σ t (shineB r Q K* F) := by
 refine { p with output:=p.output.gauge _ ((amber_cost ..).mono h), coin:=?_ }; intro i g x; simp only [Pi.mul_apply,map_mul,p.coin i g]; apply congrArg (fun i' => i' * (twist (quantU (tradew (K.c i) g)) (F i x)))
 unfold shineB scalar; dsimp only [Function.comp_apply]; rw [twist_scalar,map_one]; refine congrArg (fun x:ℂ=> x • _) ?_; unfold amber; apply congrArg ((↑):ℝ→ℂ); apply prod_congr rfl; intro z k; rw [← press_face z (simultaneous g x),← press_face z x]; change max 0 (min 1 (SU.group.chord (faceValue (Lattice.gauge _ x.1) _)/_ -1))=_; rw [face_gauge,SU.group.chord_conj]
lemma amber_fades (p:0<r){n:Side}(U:Pane n)(v:amber r Q (onC n U) ≠ 0): ∀ i∈Q,r < SU.group.chord (faceValue (onC _ U) i):= by
 intro i hi; by_contra! t; apply v; have he:=div_le_one_of_le₀ t p.le; unfold amber; rw [Finset.prod_eq_zero hi ?_, Complex.ofReal_zero]; have hv:= sub_nonpos.mpr he; exact max_eq_left ((min_le_right ..).trans hv)
lemma amber_house {n:Side}: ∀ᵐ x∂city n, ∀ᶠ r:ℕ in atTop, amber (germB r) Q (onC n x.1)=1:= by
 filter_upwards [(eventually_all_finset Q).mpr fun i _=>wasted i] with x h; have ht:∀ᶠ r:ℕ in atTop, ∀ i∈ Q,2*germB r ≤ SU.group.chord (faceValue (onC _ x.1) i):= (eventually_all_finset Q).mpr fun i p=> (show Tendsto (fun r=>2*germB r) atTop (𝓝 0) from by simpa using droop.const_mul 2).eventually (ge_mem_nhds (h i p))
 refine ht.mono fun r p=> ?_; unfold amber; rw [Finset.prod_eq_one ?_,Complex.ofReal_one]; intro i h; have hz:= (le_div_iff₀ (Real.exp_pos _)).mpr (p i h); rw [min_eq_left (by linarith only [hz]),max_eq_right zero_le_one]
end
section
open Journey FullBill
local notation "N"=> side Y i s
local notation "V"=> (tent Y h)
local notation "Fₛ"=> (Y.voyage i).CapeT s
local notation "W"=> ((Y.voyage i).X (Y.uv k)).gram s
private lemma sale_p (f:LinksC→ℂ): sold Y h s i (scalar V (f ∘ Prod.fst))= fun x=> f (onC N x.1) • 1:= by
 unfold sold; exact castK (terrain Y h (Y.ir i) s) f
where castK {n m:Side}(h:n=m)(V':LinksC→ℂ):ship h (fun x:Fields n=> V' (onC n x.1) • 1) =(fun x:Fields m=> V' (onC m x.1) • 1):=by subst m; rfl
variable {σ:Window.Family}{S U:Finset Cover}{t:List Cover}(Q:Finset (Face ℤ)){X:Family (tent Y h)} (p:Copse (tent Y h) S U σ t X) (q:carpet Q⊆S)
local notation "Yᵣ" x:max=> ((shineB x Q (tent Y h))*X)
include p q
/- strengthen assumption at a STORAGE wavelength regardless of N. Then transport neighborhood support selection. DCT does not appeal to continuum tape. -/
private lemma huy (e:MarkGate Y s i k):Tendsto (fun i'=> sharp Y h s i k (Yᵣ (germB i'))) atTop (𝓝 (sharp Y h s i k X)):=by
 have hs (r:ℝ):= (shine_spec r Q V p q).narrow σ; let a(t:Family V)(x:Orbit N):= letterRead (sold Y h s i t (drawn Fₛ x)) (denZ W Λ.U Fₛ x); let K:= (∫ x,a X x∂city N)
 have he (x:Family V)(p:InTest V true S false x): Integrable (a x) (city N):=by
    obtain ⟨y,rfl⟩:=Hierarchy.certify _ _ _ p; exact mark_legit Y h S s i k e y
 have hx (r:ℕ)(x:Orbit N): a (Yᵣ (germB r)) x= amber (germB r) Q (onC N x.1) * a X x:=by
    simp only [a,sold_mult,shineB,sale_p,Pi.mul_apply, Algebra.smul_mul_assoc,one_mul]; exact (mark_linear _ 0 _ _).2 -- tune
 have hv:Tendsto (fun r:ℕ=> (∫ x, a (Yᵣ (germB r)) x∂city N)) atTop (𝓝 K):= by
    refine tendsto_integral_of_dominated_convergence (fun x=> ‖a X x‖) (fun r=> (he _ (hs _).widen).1) (he X (p.narrow σ).widen).norm (fun i=> Eventually.of_forall fun r=> ?_) ?_
    · rw [hx,norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (amber_bounded ..)
    exact (amber_house Q).mono (fun x h=> tendsto_const_nhds.congr' (h.mono fun i p=>by dsimp only; rw [hx,p,one_mul]))
 let C:= partitionZ W Λ.U Fₛ
 simp_rw [sold_sharp]; exact hv.div_const C -- tune
variable (K:Universal Y h u v I E)
include K
-- Strong DCT on E. Requires common support class S. (variant for fixed support, general pointwise in title; stronger lemma can be obtained for arbitrary sequence with bounded supports and optional prices in Vox + opaque birthday). Geometric rates not claimed.
lemma soles : Tendsto (fun r:ℕ=> E s (Yᵣ (germB r))) atTop (𝓝 (E s X)):=by
 let YF(x:ℕ):= Yᵣ (germB x); let C:= duration S * ‖certifyAs S V X (p.narrow σ).widen‖; have hc: ∀ i x, ‖X i x‖ ≤ C:=fun i x=> (Hierarchy.certified S V X (p.narrow σ).widen ▸ compose_price S V _ i x) -- dependent rewrite?
 let v':= v; have hW (r:ℕ)(i x):‖YF r i x‖ ≤ C:= (norm_mul_le ..).trans (le_trans (mul_le_of_le_one_left (norm_nonneg _) (amber_r _ Q V i _)) (hc i x)); have hb:0≤ C:= (norm_nonneg _).trans (hc 1 (1,1)) -- inhabit Fields
 refine Metric.tendsto_nhds.mpr fun ε ht=>?_; obtain ⟨w₀,hP⟩:= (roomy_sides S V).exists; let τ:=ε/4; have hk:0<τ:=(by unfold τ; positivity); let T:=C+1; have hΛ:0<T:= by unfold T; positivity
 obtain ⟨i,hV,W0⟩:= (((boutique Y h K S s).2 (τ/T) (div_pos hk hΛ)).and (often_offer Y h S s K)).exists; obtain ⟨k,qK⟩:= (cadence Y v' K.pick.grow_k (u i)).exists
 let Ψ:=sharp Y h s (u i) (v k); have β(f:Family V)(p:InTest V true S false f)(x:∀ x,‖f w₀ x‖ ≤ C):‖Ψ f-E s f‖≤τ:=by
    have h:∀ w,‖f w₀ w‖ ≤ C+1:=fun w=>(x w).trans (le_of_lt (lt_add_one C)); exact ((hV f p w₀ (roomy_hosp _ hP) T h).2 k qK).trans (div_mul_cancel₀ τ hΛ.ne').le
 have h':‖Ψ X-E s X‖ ≤ τ:= β X (p.narrow σ).widen (hc w₀)
 filter_upwards [((huy Y h s (u i) (v k) Q p q (markGate_o Y S s _ _ (W0 k qK)).1).eventually (Metric.ball_mem_nhds _ hk))] with r q'
 have h₀:=Metric.mem_ball.mp q'; rw [dist_eq_norm] at h₀; change dist (E s (YF r)) _<_; rw [dist_eq_norm];
 let x:=YF r; have hm:‖Ψ x- E s x‖ ≤ τ:= β x ((shine_spec _ Q V p q).narrow σ).widen (hW r _); have he:‖Ψ x-Ψ X‖ < τ:= h₀; rw [norm_sub_rev] at hm; change ‖E s x-E s X‖ < ε; linarith only [hm,he,h',norm_sub_le_norm_sub_add_norm_sub (Ψ x) (Ψ X) (E s X),norm_sub_le_norm_sub_add_norm_sub (E s x) (Ψ x) (E s X), show 3*τ<ε from (by unfold τ; linarith)]
end
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
