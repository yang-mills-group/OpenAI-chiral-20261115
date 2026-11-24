import GaugeFieldConstruction.GravifierN
set_option autoImplicit false
set_option synthInstance.maxSize 5000
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.GaugeFieldConstruction.Invoice
open Window Vouchers Abacus Cauchy Row Phys Calibration Function Wick Raster Gap Finset Mirror Floor Flavor
open MeasureTheory Set Filter
open scoped BigOperators Topology Classical ComplexOrder
-- mirror-positive PH. choose actual generation assignments cycling. real part system strength noncollapse when measurements pose neighborhoods. Basis slots at αΦ frame high.
-- dual evaluations
namespace curvΝ
abbrev SettingZN:=ClanZN → ClanZN → ℂ
local notation "ΑΥ"=> ClanZN → ℂ
local notation "κH" => SettingZN
abbrev PrecisionYN (ε:ℝ) :Set SettingZN:= {X|∀ v:ClanZN→ℂ, ‖v‖=1→ ε<(Formsν X v).re}
lemma XRayN :Continuous (fun x:SettingZN×(ClanZN→ℂ)=> (Formsν x.1 x.2).re):=by
 unfold Formsν
 fun_prop
lemma PlotN : IsCompact (Metric.sphere (0:ClanZN→ℂ) 1):= isCompact_sphere ..
private lemma Locusμ_N {X Y:Type} [TopologicalSpace X][TopologicalSpace Y](M:X×Y→ℝ)(K:Set Y)(ε:ℝ)(u:IsCompact K)(h:Continuous M) : IsOpen {x:X|∀ v∈K, ε < M (x,v)}:=by
 let S:= M ⁻¹' Set.Ioi ε; have U:IsOpen S:= isOpen_Ioi.preimage h; refine isOpen_iff_mem_nhds.mpr (fun t ht=>?_)
 obtain ⟨A,B,q,g,k,w,C⟩:=generalized_tube_lemma (isCompact_singleton (x:=t)) u U (show {t} ×ˢ K⊆ S from (by rintro ⟨y,i⟩ ⟨e,v⟩; obtain rfl:y=t:=e; exact ht _ v))
 apply mem_of_superset (q.mem_nhds (k (Set.mem_singleton t))); exact fun x p y u=> C (show (x,y)∈ A ×ˢ B from ⟨p,w u⟩)
lemma PlotβN(v:ΑΥ): v∈ Metric.sphere (0:ClanZN→ℂ) 1 ↔ ‖v‖=1:=by rw [Metric.mem_sphere,dist_zero_right]
lemma PointMatrix_μN (ε:ℝ) : IsOpen (PrecisionYN ε):=by
 let F:=fun x:SettingZN×(ClanZN→ℂ)=>(Formsν x.1 x.2).re
 let K:=Metric.sphere (0:ClanZN→ℂ) 1
 have h : IsOpen {x:SettingZN|∀ y∈K,ε<F (x,y)}:= Locusμ_N F K ε PlotN XRayN
 unfold PrecisionYN; simp_rw [← PlotβN]; exact h
lemma sib1N (k:ClanZN): ‖(Pi.single k (1:ℂ):ΑΥ)‖=1:=by rw [Pi.norm_single,norm_one] -- tune
private lemma HarvestLociN {A:Type} [TopologicalSpace A](K:Set A)(p:IsCompact K)(h:K.Nonempty)(f:A→ℝ)(v:Continuous f)(z:∀ a∈K,0<f a):∃ ε>0,∀ a∈K,ε<f a:=by
 obtain ⟨m,g,w⟩:= p.exists_isMinOn h v.continuousOn
 exact ⟨_,half_pos (z m g),fun a k=> (half_lt_self (z m g)).trans_le (w k)⟩
private lemma emitsLociN{A B:Type}[TopologicalSpace A][TopologicalSpace B](f:A ×B →ℝ)(p:Continuous f)(x:A): Continuous (fun b=>f (x,b)):= p.comp (continuous_const.prodMk continuous_id)
lemma PointProfitN (i:Axis): ∃ δ>0, MatrixWΦN i∈PrecisionYN δ:=by
 let f:=fun x:ClanZN→ℂ=> (Formsν (MatrixWΦN i) x).re; let K:=Metric.sphere (0:ClanZN→ℂ) 1; let F:=fun x:SettingZN×(ClanZN→ℂ)=>(Formsν x.1 x.2).re
 let k:ClanZN:=(0,false)
 have hc:Continuous f:= emitsLociN F XRayN (MatrixWΦN i)
 have hp(u:ClanZN→ℂ)(p:u∈K): 0<f u:= magnetΓN i u (fun h=>by have g:‖u‖=1:=(PlotβN u).1 p; rw [h,norm_zero] at g; exact zero_ne_one g)
 obtain ⟨ε,h,z⟩:= HarvestLociN K PlotN ⟨_,(PlotβN _).2 (sib1N k)⟩ f hc hp
 exact ⟨ε,h,fun v hv=> z v ((PlotβN v).2 hv)⟩
lemma visibleXN {M:SettingZN}{ε:ℝ}(h:M∈ PrecisionYN ε)(k: ClanZN): ε<(M k k).re:=by
 let X:ΑΥ:=Pi.single k 1
 have he:= (h _ (sib1N k)); rw [show Formsν M X=M k k from ?_] at he; exact he
 unfold Formsν; rw [sum_eq_single k]; rw [sum_eq_single k]; simp [X]
 · intro j _ u; change _*_ * M k j = _; rw [show X j=0 from Pi.single_eq_of_ne u _,mul_zero,zero_mul]
 · simp
 · intro j _ u; rw [sum_eq_zero]; intro i _; rw [show X j=0 from Pi.single_eq_of_ne u _,map_zero,zero_mul,zero_mul]
 simp
#print axioms PointProfitN
#print axioms visibleXN
end curvΝ
end YM.GaugeFieldConstruction.Invoice
end
