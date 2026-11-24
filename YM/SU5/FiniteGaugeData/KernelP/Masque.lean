import YM.SU5.FiniteGaugeData.KernelP.Voyager
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Hills
namespace KernelP
open Terrace
variable {H:Hilbert}
lemma strong_both {T T':ℕ→ H.Op}{S S':H.Op} {C:ℝ}(t:strong T S)(p:strong T' S')(b:∀n,‖T n‖≤ C): strong (fun i=>T i*T' i) (S*S'):=by
 intro i; let y:= S' i; let f n:= T n (T' n i - y)
 have ht:Tendsto (fun n=>‖f n‖) atTop (𝓝 0):= by
    apply squeeze_zero (fun n=>norm_nonneg _) (fun n=>(T n).le_of_opNorm_le (b n) _)
    simpa only [y,sub_self,norm_zero,mul_zero] using (((p i).sub (tendsto_const_nhds (x:=S' i))).norm.const_mul C)
 simpa only [f,y,map_sub,zero_add,mul_apply_eq_comp, sub_add_cancel] using ((tendsto_zero_iff_norm_tendsto_zero.mpr ht).add (t y))
variable {a:Axis}{L:Side}(T:Terrace H L a)
abbrev beamAve (s:ℕ)(j:Axis)(n:ℕ) : H.Op:= meanL (fun k:ℕ=> T.stepT s j k (fun _=> Nat.cast_nonneg' _)) n
lemma beam_le (s:ℕ)(j:Axis)(n:ℕ): ‖beamAve T s j n‖≤1:=by
 let x(k:ℕ):=T.stepT s j (k:ℤ) (fun _=> Nat.cast_nonneg' _); unfold beamAve meanL; change ‖((n:ℂ)⁻¹) • (∑ k∈range n,x k)‖≤1; rw [norm_smul,norm_inv, Complex.norm_natCast]
 rcases Nat.eq_zero_or_pos n with rfl|h; · norm_num
 have hh: ‖∑ k∈range n,x k‖ ≤ ∑ k∈range n,(1:ℝ):= (norm_sum_le ..).trans (sum_le_sum fun k _=> T.size_ s j _ _)
 rw [sum_const,card_range,nsmul_eq_mul,mul_one] at hh -- actually card
 exact le_trans (mul_le_mul_of_nonneg_left hh (by positivity)) (by rw [inv_mul_cancel₀]; positivity) -- tune
abbrev rectangular (s n:ℕ)(w:List Axis):=(w.map (fun i=>beamAve T s i n)).prod
lemma descry (s:ℕ)(w:List Axis) : strong (fun n=>rectangular T s n w) (planeP (T.pack s w)):=by
 rw [T.orchid]; induction w with
 | nil=> intro x; exact tendsto_const_nhds
 | cons i w ih=> exact strong_both (T.passage_fwd s i) ih (beam_le T s i)
lemma meanB (s n:ℕ)(w:List Axis) : ‖rectangular T s n w‖≤ 1:=by
 induction w with
 | nil=> exact ContinuousLinearMap.norm_id_le
 | cons i w ih=> exact (norm_mul_le (beamAve T s i n) (rectangular T s n w)).trans (mul_le_one₀ (beam_le T s i n) (norm_nonneg _) ih)
def unityAvg (s n:ℕ):= rectangular T s n Terrace.scheduleL
lemma levelAvg (s:ℕ): strong (unityAvg T s) (planeP (T.GalleryH s)):=by rw [← T.siding s _ Terrace.scheduleV]; exact descry T s _
end KernelP
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
local notation "D"=> Decko Y h a
variable (H:Harbor Y h W' R Φ a)(X:Engine Y h W' R a H)(x:Decko Y h a)
abbrev bearStep (s i n:ℕ)(x: Decko Y h a)(j:Axis) : Decko Y h a:= ((n:ℂ)⁻¹) • (∑ k∈range n, hoist Y h a j (Chrono.scaleR Λ s i k) (fun _=>by unfold Chrono.scaleR; positivity) x)
-- s observing engine; i≥ s leaf made
include X
lemma leaf_bear {y:D} (p:s ≤ i) (j:Axis): beamAve X.val s j k (H.leaf i y)= H.leaf i (bearStep Y h a s i k y j):=by
 unfold beamAve meanL bearStep; rw [map_smul (H.leaf i), map_sum (H.leaf i)]; simp only [_root_.smul_apply,_root_.sum_apply]; refine congrArg (((k:ℂ)⁻¹) • · ) ?_; exact sum_congr rfl fun u _=> Vessel Y h s i W' R a _ j H X y _ p
abbrev trainK (s i k:ℕ): List Axis→ Decko Y h a → Decko Y h a
 | [], x=>x
 | j::L,x=>bearStep Y h a s i k (trainK s i k L x) j
lemma leaf_k (p:s ≤ i) (V:List Axis): rectangular X.val s k V (H.leaf i x)= H.leaf i (trainK Y h a s i k V x):=by
 induction V with
 | nil=> rfl
 | cons z u ih=> change (beamAve X.val s z k * rectangular X.val s k u) (H.leaf i x)=_; rw [mul_apply_eq_comp,ih]; exact leaf_bear Y h s i k W' R a H X p z -- tune
omit X
def escalant (s:ℕ): (i:ℕ)→ D→ D
 | 0,x=>x
 | n+1,x=> nectar Y h (s+n) W' R a (escalant s n x)
lemma escalate : H.leaf (s+n) (escalant Y h W' R a s n x)= H.leaf s x:=by induction n with
 | zero=> rfl
 | succ n ih=> exact (H.up Y h (s+n) W' R a _).trans ih
-- fields Θ rank.Gold.
abbrev omegaV := H.value 1
lemma gold_leaf (s:ℕ): H.leaf s 1= omegaV Y h W' R a H:= by rw [H.fleets,seedling_one]
lemma goldPrice : inner ℂ (omegaV Y h W' R a H) (H.leaf s x)= Φ s x.val:=by rw [← gold_leaf Y h W' R a H s,H.measure]; unfold helve; rw [show (1:D).val=(1:W (tent Y h)) from rfl,ice_central,one_mul]
include S' in
lemma omegaBudget : ‖omegaV Y h W' R a H‖=1:=by
 apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp; rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℂ)]; let h:= goldPrice Y h 0 W' R a H 1; rw [gold_leaf] at h; rw [h,show (1:D).val=(1:W (tent Y _)) from rfl,S'.living,one_pow]; rfl -- notation h shadow
include X
local notation "Λ0"=> (X.val.Unity)
local notation "Ω"=> omegaV Y h W' R a H
lemma gold_fixed : omegaV Y h W' R a H∈ (X.val.Unity):=X.val.unityH _|>.2 fun s j z p=> by rw [←gold_leaf Y h W' R a H s, X.property, show hoist Y h a j z p (1:D)=1 from Subtype.ext (clock_one ..)]
abbrev royalMass : ℝ := ‖planeP X.val.Unity (H.leaf s x)‖^2
abbrev levelMass : ℝ := ‖planeP (X.val.GalleryH (s+n)) (H.leaf s x)‖^2
def planned (i n s:ℕ)(x:D): W (tent Y h):=
 let v:=trainK Y h a (s+n) (s+n) i Terrace.scheduleL (escalant Y h W' R a s n x)
 helve Kₜ a v.val v.val
lemma boasts (k:ℕ): ‖unityAvg X.val (s+n) k (H.leaf s x)‖^2= (Φ (s+n) (planned Y h W' R a k n s x)).re:= by
 rw [← escalate Y h s W' R a n H x, unityAvg, leaf_k Y h (s+n) (s+n) k W' R a H X _ le_rfl]
 unfold planned; rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℂ),H.measure]; rfl
lemma plate_limit : Tendsto (fun k:ℕ=>(Φ (s+n) (planned Y h W' R a k n s x)).re) atTop (𝓝 (levelMass Y h s W' R a n H X x)):= by simp_rw [← boasts Y h s W' R a n H X]; exact (levelAvg X.val _ (H.leaf s x)).norm.pow 2
lemma much_power : Tendsto (fun n=>levelMass Y h s W' R a n H X x) atTop (𝓝 (royalMass Y h s W' R a H X x)):= by
 let v:=H.leaf s x; let y:= X.val.retreat v
 exact ((y.comp ((tendsto_add_atTop_nat s).congr fun i=>add_comm i s)).norm.pow 2)
#print axioms boasts
#print axioms plate_limit
end KernelP
end YM.CF.Buffered.Afterglow.Hierarchy
