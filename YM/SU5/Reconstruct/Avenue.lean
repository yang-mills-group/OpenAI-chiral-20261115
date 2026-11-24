import YM.SU5.Reconstruct.Folio
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 470000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude PhaseChoice
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
open Tower.Selected Set MeshClock Tapestry.Exhibition
open SelectionAnalysis Vacancy.Average
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  {L:Rack Λ l}{B:Clay Λ l}{T:ℕ→ℕ→Tariff}{t:ℕ→Tariff}(D:Fashion Y H i k I E L B T t)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "Dₚ" => D.toExhibition
local notation "V" => D.univ_
local notation "Q" => G.history
local notation "Qt" => G.clipped
local notation "χ" => Dome (tent Y H)
local notation "O" => Altitude.Cloud (Dome (tent Y H))
local notation "P₀" s:max => vistaFinish Y H s (Dₚ)

variable (s:ℕ) (j:Axis)
local notation "M"=> timeMesh Λ
section enclosure
-- translate down, use actual intervals to all heights at once
private lemma periodRoom (S:Finset Cover)(U:Set RSpace)(w:ℕ)(h: SupportedPhysically Λ l s S U) (p:∀ z∈U, 0≤z j ∧ z j ≤ bell (timeMesh Λ) s w): Between K j 0 (ruler Λ.block*w) S:=by
 let b:ℝ:=precisionAt Λ s; have hx:0<b:= positiveScale ..
 intro x t
 let r:ℤ:=reserve Λ l
 let y(a:ℤ): RSpace := fun i=>markZ Λ s (x i+a)
 have Hy (a:ℤ) (k:|a|≤r) : y a∈Tapestry.shield Λ l s x:=by
   intro i; change |b*y a i - x i|≤ _
   have he:b*y a i=(x i+a:ℤ):=by unfold y markZ b; rw [mul_comm,div_mul_cancel₀ _ hx.ne']
   rw [he]; push_cast; simp only [add_sub_cancel_left]; exact_mod_cast k
 have HL:=p _ (h _ t (Hy (-r) (by rw [abs_neg,abs_of_nonneg (show 0≤r from Int.natCast_nonneg _)]))) |>.1
 have HK:=p _ (h _ t (Hy r (by rw [abs_of_nonneg (show 0≤r from Int.natCast_nonneg _)]))) |>.2
 change 0 ≤ y (-r) j / 2 at HL; change y r j/2≤_ at HK
 have hc:0≤y (-r) j:=by linarith only [HL]
 have hg:r ≤ x j:=by
   change 0 ≤ ((x j + (-r):ℤ):ℝ)/b at hc; rw [le_div_iff₀ hx,zero_mul] at hc
   have h:= (show (0:ℤ) ≤ x j+(-r) by exact_mod_cast hc); omega
 have hq:x j+r ≤ ruler Λ.block * w:=by
   let w' : ℤ:= Heat.gaugeShift Λ.block (2*(w:ℤ))
   have hl: 2*w'=ruler Λ.block*w:= ruler_offset K _
   have he: y r j/2≤(w':ℝ)/b:= HK.trans_eq (calibrated_step ..)
   have hv:y r j≤2*((w':ℝ)/b):=by linarith only [he]
   change ((x j+r:ℤ):ℝ)/b ≤ _ at hv
   rw [←mul_div_assoc,div_le_div_iff_of_pos_right hx] at hv; rw [←hl]; exact_mod_cast hv
 exact ⟨by change (0:ℤ)+r ≤ x j; omega, hq⟩
lemma makeCard {U:Set RSpace}{x:Pol Y H U}(v:x.val∈PolAt Y H s U) (o:Cover)(w:ℕ)(k:0<w)
    (h:∀ z∈U, physPos Λ (meshPos Λ s o) j ≤ z j ∧ z j ≤ physPos Λ (meshPos Λ s o) j + bell (timeMesh Λ) s w) : ∃ Q':StripCard Y H D s j U x,Q'.origin_ = o ∧ Q'.span = w := by
 let X := (P₀ s) x.val; let y:= march Y H (-o) X; let U':=carried (physPos Λ (meshPos Λ s (-o))) U
 have hy: y∈ keep Λ l s K true (handstamp U') := travels Y H (-o) (retained Y H D s v)
 have hx: y∈enclave K:= tour_en Y H _ _ (D.toExhibition.finishCoherent Y H s x.val v (inside_budget Y H v))
 obtain ⟨S,p,t⟩:=hy
 have ht:Between K j 0 (ruler Λ.block*w) S:=by
   apply periodRoom Y H s j S U' w t
   rintro u ⟨x,r,rfl⟩; obtain ⟨a,b⟩:= h x r; simp only [map_neg,Pi.add_apply,Pi.neg_apply]; constructor <;> linarith
 let q: Tower.Field Y H s j 0 true:=⟨y.val, (purpose_ok ..).2 ⟨⟨S,p,fun a p=>by rw [area0]; exact (ht a p).1⟩,fun _=> (enclave_spec ..).1 hx⟩⟩
 exact ⟨⟨o,w,k,⟨q,S,(Tapestry.locates ..).1 p,ht⟩,v,rfl,h⟩,rfl,rfl⟩ -- locates conflicting

private lemma meshBracket {Λ:Preparation}{a b:ℝ}(t:a<b) : ∀ᶠ n:ℕ in atTop,∃ v:ℤ,bell (timeMesh Λ) n v∈ Set.Ioo a b:=by
 obtain ⟨x,h,p⟩:= (daylight (timeMesh Λ)).inter_open_nonempty _ isOpen_Ioo (Set.nonempty_Ioo.mpr t)
 obtain ⟨n,v,hv⟩:= existsZ (timeMesh Λ) ⟨x,p⟩
 filter_upwards [eventually_ge_atTop n] with i w; refine ⟨castor (timeMesh Λ) n i v,?_⟩
 rw [refineZ (timeMesh Λ) n i w v,hv]; exact h
lemma eventually_card {U:Set RSpace}{x:Pol Y H U}{a b:ℝ}(p:a≤b)(t:RSpace)(h:∀ z∈ carried t U, a ≤ z j ∧ z j ≤ b)(d:ℝ)(k:0<d):
    ∀ᶠ s:ℕ in atTop, ∃ Q':StripCard Y H D s j U x, a-d < StripCard.starts Y H D Q' t j ∧ StripCard.ends Y H D Q' t j < b+d := by
 let y:=a-t j; let w:=b-t j
 filter_upwards [meshBracket (Λ:=Λ) (show y-d<y by linarith), meshBracket (Λ:=Λ) (show w<w+d by linarith), eventually_inside Y H x.property] with n e b' r
 obtain ⟨m,c,v⟩:=e; obtain ⟨i,u,f⟩:=b'; have h₀:y≤w:=sub_le_sub_right p _
 have hi : m < i:= lt_of_not_ge (fun t=> not_lt_of_ge ((bell_le M _ i m).2 t) (v.trans (h₀.trans_lt u)))
 let k0 := (i-m).toNat; have hq : (k0:ℤ)=i-m:= Int.toNat_of_nonneg (by omega)
 let o:Cover:= m • step j; have ho: physPos Λ (meshPos Λ n o) j= bell M n m:=by change bell M n _ =_; simp [o]
 have hb:bell M n m+bell M n (k0:ℤ)=bell M n i:=by rw [←bell_add,hq]; congr 1 <;> omega
 obtain ⟨x',e,nv⟩:= makeCard Y H D n j r o k0 (by omega) (by
    intro z t'; obtain ⟨hy,hx⟩:= h (t+z) ⟨_,t',rfl⟩; rw [ho,hb]; change _ ≤ t j+z j at hy; change t j+z j ≤_ at hx; unfold w at u; unfold y at v; constructor <;> linarith)
 refine ⟨x',?_⟩
 rw [StripCard.before_h]; unfold StripCard.starts StripCard.fromBase; simp only [Pi.add_apply,e,nv,ho]; unfold y at c; unfold w at f; constructor <;> linarith
end enclosure
section
variable {σ:Type}(U:σ→ Set RSpace)(X:σ→RSpace)(z:List σ)
def AxisAperture := ∃ a b:σ→ ℝ,(∀ i,a i ≤ b i ∧ ∀ w∈ carried (X i) (U i), a i ≤ w j ∧ w j ≤ b i) ∧ z.Pairwise (fun i k=> b i < a k)
open StripCard
lemma clearance (a b:σ→ℝ)(t:z.Pairwise fun i k=> b i<a k) : ∀ᶠ ε in 𝓝 (0:ℝ), z.Pairwise fun i k=> b i + ε < a k-ε := by
 induction z with
 | nil=> exact Eventually.of_forall fun _=> List.Pairwise.nil
 | cons i u ih =>
   obtain ⟨v,t⟩:= List.pairwise_cons.mp t
   have he j (x:j∈u) : ∀ᶠ ε in 𝓝 (0:ℝ), b i+ε<a j-ε := by
     apply Filter.Tendsto.eventually_lt _ _ (show b i+0 < a j-0 from by simpa using v j x)
     · exact tendsto_const_nhds.add tendsto_id
     exact tendsto_const_nhds.sub tendsto_id
   classical
   filter_upwards [(Finset.eventually_all u.toFinset).mpr (fun i p=>he i (by simpa using p)),ih t] with j p t
   exact List.pairwise_cons.mpr ⟨fun x v=>p x (by simpa using v),t⟩
variable [Fintype σ] (g:∀ i,Pol Y H (U i))
lemma eventual_pages (p:AxisAperture j U X z): ∀ᶠ s:ℕ in atTop,∃ q: Board Y H D s j U g,OfferedOn Y H D z q X:= by
 obtain ⟨a,b,h,t⟩:=p
 obtain ⟨ε,k,d⟩:= ((Filter.Eventually.filter_mono (nhdsWithin_le_nhds (s:=Set.Ioi 0)) (clearance z a b t)).and self_mem_nhdsWithin).exists
 filter_upwards [Filter.eventually_all.mpr (fun i=>eventually_card (x:=g i) Y H D j (h i).1 (X i) (h i).2 ε d)] with i p
 choose q v y using p
 exact ⟨q,k.imp (fun {j k} p=> lt_trans (lt_trans (y j) p) (v k))⟩
lemma open_only {g:∀ i,Pol Y H (U i)}(q:Board Y H D s j U g)(p:OfferedOn Y H D z q X) : AxisAperture j U X z:=by
 refine ⟨fun i=> StripCard.starts Y H D (q i) (X i) j,fun i=> StripCard.ends Y H D (q i) (X i) j, fun i=>⟨?_, StripCard.contained Y H D (q i) (X i)⟩,p⟩
 have h:= StripCard.glassSize Y H D (q i); rw [StripCard.broad_own] at h; dsimp only; rw [StripCard.before_h]; exact le_add_of_nonneg_right h.le
include H D
lemma open_order : IsOpen {X | AxisAperture j U X z} := by
 rw [isOpen_iff_mem_nhds]; intro x p
 let x' : ∀ i,Pol Y H (U i):= fun _=>1
 obtain ⟨s,q,t⟩:= (eventual_pages Y H D j U x z x' p).exists
 apply Filter.mem_of_superset ((chart_open Y H D z q).mem_nhds t); intro y p
 exact open_only Y H D s j U y z q p
end
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
