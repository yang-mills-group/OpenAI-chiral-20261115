import YM.SU5.Reconstruction.UVPrice.Warm
import YM.SU5.Reconstruction.UVPrice.Temper
/-!
# Optional soft stamp prices in the actual physical law. Build helpers.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open Roy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "F₀"=> osValue Y H V G a (C a) χ
variable (j j' : Axis) (hv:j'≠j)
local notation "N" i:max => flank i 0
local notation "L" i:max=> lowland i 0
local notation "Φ"=> move (tent Y H)
variable (p : ∀ j, saunters Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))=⊤)
variable (Hp : Victory Y H V G.history G.clipped false j (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j)))
local notation "Cq"=> cue (S₀ j)
local notation "Hq"=> Hearth (S₀ j) (Ω₀ j)
include p Hp
lemma solo_roll (v:IsCompact (Beneath (S₀ j) 0)): Hearth (S₀ j) (Ω₀ j):= by
 apply allHearth (S₀ j) (Ω₀ j) (vocation_norm ..) (fun i=> compass_origin _ _ _ _ _ _ _ _ _ i) (compass_invariant _ _ _ _ _ _ _ _ _ Hp) -- tune args
 intro x j' t s; let U:= ((S₀ j).U (s • Picket.cross j j' t)).comp Cq; let S := {x:G₀ j| U x=Cq x}
 have he:IsClosed S:= isClosed_eq U.continuous (cue (S₀ j)).continuous; refine closure_minimal ?_ he (compass_domain_dense Y H V G j (C j) (w j) x); rintro _ ⟨f,rfl⟩; exact timely_occupancy Y H V G C a χ j j' t p v f s
omit Hp
variable (u:Hearth (peninsula Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (vocation Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))))
include u p
lemma time_event (f x:G₀ j) : Tendsto (fun t=> inner ℂ f ((S₀ j).E t x)) atTop (𝓝 (inner ℂ f (Ω₀ j) * inner ℂ (Ω₀ j) x)):=by
 have he:= tendsto_const_nhds.inner (𝕜:=ℂ) (x:=f) (truth (S₀ j) x); rw [u] at he; simpa [mul_comm] using he -- tune
omit u
local notation "Θ"=> F₀
local notation "Gq"=> Ds Set.univ
noncomputable def lug (f:Gq):ℂ:= (F₀) (Submodule.inclusion (domain_loose Y H G _) f)
local notation "T"=> lug Y H V G C a χ
-- measure for any physical test. post-motion arrival from one corner.
noncomputable def plusOne (q:Set RSpace)(U:Set RSpace)(b:q⊆ U)(f:Ds q): Ds U:= Submodule.inclusion (domain_mono Y H G b) f
local notation "now" f:max=> plusOne Y H G _ univ (Set.subset_univ _) f
include p
lemma one_lug (x: Ds (N j)) : inner ℂ (Ω₀ j) ((Os j) x)= T (plusOne Y H G _ univ (Set.subset_univ _) x):= by
 let f : Ds (N j):=⟨1,domain_one ..⟩; obtain ⟨b,h⟩:=comeBy Y H V G C a χ j p f x 0 (by simp); have hp: (Pr j) 0=1:=by unfold bridgeEstate Schedule.route; simp only [map_zero,Pi.zero_apply,Real.toNNReal_zero, (S₀ j).eZero]; rw [show diameter (a:=j) 0=0 from Subtype.ext (by ext1 i; simp [diameter]),(S₀ j).uZero]; rfl
 have he:(Os j) f=Ω₀ j:= comesHome Y H V G C a χ j
 rw [hp,he] at h; refine h.trans (congrArg F₀ (Subtype.ext ?_)); change (θ j) 1 * Φ (0:placement Λ) x.val=x.val; rw [flipMark_unit,move_by_zero,one_mul]
local notation "X" j:max=> (N j)
lemma first_lug (x: Ds (N j)) (y:Gq)(g:y.val=(θ j) x.val) : inner ℂ ((Os j) x) (Ω₀ j)=T y:= by
 let f : Ds (N j):= ⟨1,domain_one ..⟩; have e: (0:placement Λ)=eject j 0:=(eject_zero j).symm; obtain ⟨q,k⟩:= comeBy Y H V G C a χ j p x f (eject j (0:Gt)) (by simp); have hp:(Os j) f=Ω₀ j:= comesHome Y H V G C a χ j
 rw [hp,bridge_time,AddSubgroup.coe_zero,Real.toNNReal_zero,(S₀ j).eZero] at k; refine k.trans (congrArg F₀ (Subtype.ext ?_)); change (θ j) x.val*Φ (eject j (0:Gt)) 1=y.val; rw [move_unit,mul_one,g]
omit p
-- real projection property if clustering in very same season. measure ANY disjoint product through presentation helpers. actually use prepared moves no need measure separately.
include V in
lemma locateRoll (z: placement Λ)(f:Gq) : Φ z f.val ∈ Ds univ := by simpa only [slides_univ] using (moving Y H V G z f.val f.property)
include V in
noncomputable def circus (z: placement Λ)(f:Gq): Gq:= ⟨Φ z f.val,locateRoll Y H V G z f⟩
lemma loose_fare (z: placement Λ)(f:Gq): T (circus Y H V G z f)= T f := moving_value Y H V G a (C a) χ z (domain_loose Y H G _ f.property) (domain_loose Y H G _ (locateRoll Y H V G z f))
include V in
lemma chooseDoors (f g:Gq) : ∃ b c:Gt, 0 < (b:ℝ) ∧ 0 < (c:ℝ) ∧ Φ (eject j (-b)) f.val∈Ds (L j) ∧ Φ (eject j c) g.val ∈ Ds (N j) := by
 obtain ⟨U,p₀,x,h⟩:= (compact_domain Y H G).1 f.property; obtain ⟨U',v,x',h'⟩:= (compact_domain Y H G).1 g.property
 obtain ⟨r,s,t,g₀⟩:= Schedule.shutters (daylight (timeMesh Λ)) j p₀; obtain ⟨r',s',c,k⟩:= Schedule.shutters (daylight (timeMesh Λ)) j v
 obtain ⟨u,d⟩:= Schedule.very_late (a:=max 0 (s:ℝ)) (daylight (timeMesh Λ)); obtain ⟨y,z⟩:= Schedule.very_late (a:=max (0:ℝ) (-(r':ℝ))) (daylight (timeMesh Λ))
 refine ⟨u,y,lt_of_le_of_lt (le_max_left ..) d, lt_of_le_of_lt (le_max_left ..) z,?_,?_⟩
 · apply domain_mono Y H G _ (moving Y H V G _ _ h); rintro x ⟨x,p,rfl⟩; change x j+coordinates Λ _ _ ≤ 0; rw [coordinates_eject,eject_at,AddSubgroup.coe_neg]; linarith [(g₀ x p).2,le_max_right (0:ℝ) (s:ℝ)]
 apply domain_mono Y H G _ (moving Y H V G _ _ h'); rintro x ⟨x,p,rfl⟩; change 0 ≤ x j+coordinates Λ _ _; rw [coordinates_eject,eject_at]; linarith [(k x p).1,le_max_right (0:ℝ) (-(r':ℝ))]
include u p
local notation "μ" z:max=> move (tent Y H) (eject j z)
-- product measurement defined here only when separated enough's. cluster in ANY height germs forever eventually
lemma clusters_roll (d : ℕ→Gt)(cv:Tendsto (fun i=> (d i:ℝ)) atTop atTop)(f g:Gq) : ∃ F: ℕ→ Gq, (∀ᶠ i in atTop,(F i).val= f.val* (μ (d i)) g.val) ∧ Tendsto (fun i=> T (F i)) atTop (𝓝 (T f * T g)):= by
 obtain ⟨b,c,b₁,c₁,h,k⟩:= chooseDoors Y H V G j f g
 have hx: (θ j) ((μ (-b)) f.val)∈ Ds (N j):= domain_mono Y H G ?_ (mirror_support Y H G j _ h)
 swap; · rintro x ⟨x,r,rfl⟩; change 0 ≤ mirrorE j 0 x _; rw [mirrorE,if_pos rfl]; linarith [(show x j≤ 0 from r)]
 let x: Ds (N j):= ⟨_,hx⟩; let y:Ds (N j):= ⟨_,k⟩; let s (i:ℕ):Gt:= d i-b-c
 have ht:Tendsto (fun i=> (s i:ℝ)) atTop atTop:= (by simpa only [s,sub_eq_add_neg,map_add,AddSubgroup.coe_add,AddSubgroup.coe_neg] using tendsto_atTop_add_const_right _ (-c.val) (tendsto_atTop_add_const_right _ (-b.val) cv))
 have hr: ∀ᶠ i in atTop, 0 ≤ (s i:ℝ):= ht.eventually (eventually_ge_atTop _)
 let T₁(z:Gt):= (S₀ j).E (ℜ z) ((Os j) y)
 have bound:∀ᶠ i in atTop, ∃ F:Gq, F.val=f.val* (μ (d i)) g.val ∧ T F=inner ℂ ((Os j) x) (T₁ (s i)):= by
   filter_upwards [hr] with i hi; have hu:0 ≤ coordinates Λ (eject j (s i)) j:=by simp; exact hi
   let y':= crawl Y H V G j _ hu y; let P':Gq:=⟨(θ j) x.val*y'.val,paired_forever Y H G j x.val y'.val x.property y'.property⟩; let G':= circus Y H V G (eject j b) P'; refine ⟨G',?_,?_⟩
   · change (μ b) ((θ j) ((θ j) ((μ (-b)) f.val)) * (μ (s i)) ((μ c) g.val)) = _
     rw [mirror_twice,move_prod,move_sum,move_sum,move_sum]; simp_rw [selectRay]; rw [add_neg_cancel,eject_zero,move_by_zero]; unfold s; abel_nf -- with x₀?
   rw [show G'= circus Y H V G (eject j b) P' from rfl, loose_fare]; obtain ⟨t,v⟩:= comeBy Y H V G C a χ j p x y _ hu; rw [bridge_time] at v; exact v.symm
 let c'(i):=ℜ (s i); have hk:Tendsto c' atTop atTop:= NNReal.tendsto_coe_atTop.mp (ht.congr' (hr.mono fun i q=>(Real.coe_toNNReal _ q).symm))
 have h1: inner ℂ (Ω₀ j) ((Os j) y)= T g:= by rw [one_lug Y H V G C a χ j p y]; exact loose_fare Y H V G C a χ (eject j c) g
 have h2: inner ℂ ((Os j) x) (Ω₀ j)= T f:= by rw [first_lug Y H V G C a χ j p x (circus Y H V G (eject j (-b)) f) (mirror_twice ..|>.symm), loose_fare]
 have he:= (time_event Y H V G C a χ j p u ((Os j) x) ((Os j) y)).comp hk
 rw [h2,h1] at he
 -- choose eventual. nonempty
 let Q(i:ℕ)(F:Gq):= F.val=f.val* (μ (d i)) g.val ∧ T F=inner ℂ ((Os j) x) (T₁ (s i)); let z :ℕ→Gq:= fun i=> if e:∃ F:Gq,Q i F then e.choose else f; have hz : ∀ᶠ i in atTop, Q i (z i):= by filter_upwards [bound] with i t; have e:∃ F,Q i F:=t; unfold z; rw [dif_pos e]; exact e.choose_spec
 exact ⟨z, hz.mono fun _ q=> q.1,he.congr' (hz.mono fun _ q=> q.2.symm)⟩
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
