import YM.SU5.FiniteGaugeData.Concord.Sightline
/-! # Physical footprint through TOP. Terminal coupling on mixed realization.

`area s+n`: concrete in cover fine gauge units at stage s+n; widths bounded by
`reserve Λ l` **in s units** including projection to the torus (AtSupport computed there).
Scaling of seam into physical units: level t gauge unit is L^{-t} level0 gauge units; e.g. all
lanterns from a preset S at s carry at most radius reserve there (much bigger than sharp bound).
Cost at TOP is only estimated for each FINITE regulator, NOT asserting comparable to observing-level
cost uniformly; this is not needed to estimate these readings (equality s to top exactly). -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical TensorProduct
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock Heat
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{P:Playhouse Λ l}
variable {i k:ℕ→ℕ} (W:Traced Y H i k F E P)
variable (s n d:ℕ)(S: Finset Cover)
local notation "K"=> tent Y H
local notation "ν" k:max=> side Y n k
local notation "ρ" v:max=> realizeStage Y H n d v W
local notation "L"=> Λ.R.L.val
local notation "S'"=> swept Λ l
variable {x:Hallspace (tent Y H)}

-- Cost through ANY extra step to top. may grow!!
section
open ContinuousLinearMap
private lemma sub_cap {N W:Side}(g:Ratio N W)(j R:ℕ)(Q:Op SU.Slot)(M: Male)(ho:Odd g.count.val)(p:LaurentRadius j g.count R) :
    ∃ b:ℝ,0 ≤ b ∧ ∀ v:Nom N W,∀ w:FC (Single N),‖subF g j Q M ho v w‖ ≤ b*‖w‖:=by
  let T (v:Nom N W): FC (Single N)→L[ℂ] FC (Single W):= (subF g j Q M ho v).toContinuousLinearMap
  let f := fun v:Nom N W × FC (Single N)=> subF g j Q M ho v.1 v.2
  obtain ⟨b,h⟩:= ((isCompact_univ.prod (ProperSpace.isCompact_closedBall (0:FC (Single N)) 1)).image (sub_cont g j Q M ho p).norm).bddAbove
  refine ⟨max 0 b,le_max_left ..,fun v w=>?_⟩; apply (T v).le_of_opNorm_le ?_ w; refine ContinuousLinearMap.opNorm_le_of_unit_norm (le_max_left 0 b) fun x e=>?_ ; exact (h ⟨(v,x),⟨Set.mem_univ _,mem_closedBall_zero_iff.mpr e.le⟩,rfl⟩).trans (le_max_right ..)

private lemma push_exp {N W:Side}(g:Ratio N W)(A : StepData (More N) (More W))(j R:ℕ)(Q:Op SU.Slot)(M: Male)(ho:Odd g.count.val)(p:LaurentRadius j g.count R)(χ:Chi)(d β:ℝ)(l:Loom N)(t:Measurable l)(a:A.patch.Branches A.kernel SU.group)(r:0<d)(s:2*d<firstRadius SU.group) :
    ∃ b:ℝ,0 ≤ b ∧ ∀ w:Mark N, Envelope w→ ∀ x:ℝ,(∀ v, ‖w v‖ ≤ x) → ∀ v, ‖pushMark g A j Q M ho χ d β l w v‖ ≤ b*x:=by
 obtain ⟨k,h,p'⟩:= (sub_cap g j R Q M ho p); let V:= kernel_env A β a; obtain ⟨M₀,U⟩:= V.cost
 refine ⟨max 0 M₀*k,mul_nonneg (le_max_left ..) h,fun w u x q v=>?_⟩
 letI:Nonempty (Forest (ratio g)):= Tree.select (ratio g) ho; let n:ℝ:=Fintype.card (Forest (ratio g)); have H:0<n:=by unfold n; positivity
 have he (a:Fields N) : ‖gathered g j Q M ho χ d w v a‖ ≤ k*x:=by
   unfold gathered avgF; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr H.le)]; apply le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) (inv_nonneg.mpr H.le)); apply le_trans (mul_le_mul_of_nonneg_left (sum_le_sum (fun i _=> (p' (middle g χ d i v a) _).trans (mul_le_mul_of_nonneg_left (q a) h))) (inv_nonneg.mpr H.le)); rw [sum_const,card_univ,nsmul_eq_mul,inv_mul_cancel_left₀ H.ne']
 rw [outright g A j Q M ho χ d β l p t a r s w u v]; apply le_trans (norm_integral_le_of_norm_le_const (C:=max 0 M₀*k*x) (Filter.Eventually.of_forall fun i=>?_))
 · simp
 rw [norm_smul]; rw [mul_assoc]; exact mul_le_mul ((U (v.1,i.1)).trans (le_max_right ..)) (he _) (norm_nonneg _) (le_max_left ..)
end
local notation "uA"=> steps Λ.V (Y.ir n) Λ.block (Y.uv d) s
lemma hike (p:PairIdx Y s n d) : ∃ b:ℝ,0 ≤ b ∧ ∀ f:Mark (side Y n s),Envelope f→∀ x:ℝ,(∀ v, ‖f v‖ ≤ x) →∀ y, ‖haul Y s n d f y‖ ≤ b*x:=
  push_exp (apt (Y.ir n) Λ.block Λ.R.L s) (uA) Λ.K.j (aliasLaw Λ) _ _ _ (Journey.legal Λ) _ _ _ _ ((Y.voyage n).ownership s).paid.bill ((fullness Y n d p.1).cap_grant.branch s p.2) (can_cane Y s p).1 (can_cane Y s p).2

def hurdle (s:ℕ) : ℝ:=if p:PairIdx Y s n d then (hike Y s n d p).choose else 0
lemma hurdle_size : 0 ≤ hurdle Y n d s:= by
 unfold hurdle; split
 next p=> exact (hike Y s n d p).choose_spec.1
 exact le_rfl -- indentation

lemma hurdle_hike (p:PairIdx Y s n d)(f:Mark (side Y n s))(e:Envelope f)(x:ℝ)(t:∀ v, ‖f v‖≤x)(y): ‖haul Y s n d f y‖≤ hurdle Y n d s*x:= by unfold hurdle; rw [dif_pos p]; exact (hike Y s n d p).choose_spec.2 f e x t y

def area (Λ:Preparation)(l:ℕ)(S:Finset Cover): ℕ→ Finset Cover
| 0=> S
| n+1=> swept Λ l (area Λ l S n)

def winch (k:ℕ):ℝ:=∏ i∈range k,hurdle Y n d (s+i)
theorem scenic_wind (h:x∈Style.atLeast (A:=↥(junior K)) s)(u:AtSupport false (region S (side Y n s)) ((ρ s) x).val)(p:(Y.voyage n).kick ≤ d)(y:ℝ)(e:∀ v, ‖((ρ s) x).val v‖ ≤ y)(j:ℕ)(r:s+j≤Y.uv d):
    AtSupport false (region (area Λ l S j) (ν (s+j))) ((ρ (s+j)) x).val ∧
    ∀ v, ‖((ρ (s+j)) x).val v‖ ≤ winch Y s n d j*y:=by
 induction j with
 | zero=> refine ⟨u,?_⟩; simpa [winch] using e
 | succ j ih=>
   let t':PairIdx Y (s+j) n d:= ⟨p,r⟩; obtain ⟨b,B⟩:= ih (show s+j≤ Y.uv d from by omega); have v:= (t':PairIdx Y (s+j) n d)
   change AtSupport false (region (swept _ _ _) _) ((ρ (s+j+1)) x).val ∧ _ -- might rw both
   have ht: ((ρ (s+(j+1))) x).val= _ := (show ((ρ (s+j+1)) x).val= haul Y (s+j) n d ((ρ (s+j)) x).val from by rw [stage_run Y H n d (s+j) W (Style.to_pepper ⊤ (Nat.le_add_right s j) h) , ticket_v Y n d (s+j) t'])
   refine ⟨?_,?_⟩
   · change AtSupport false (region _ _) ((ρ (s+(j+1))) x).val; rw [ht]; exact package Y (s+j) t' _ b
   rw [ht]; intro i; apply (hurdle_hike Y (s+j) n d t' _ b.env _ B i).trans_eq; rw [winch,winch,prod_range_succ]; ring

-- at-budget localization for every tensor (no clipping). use room rule directly; export uniform bound via Delivery when needed.
theorem embedded_box (R:ℕ→Finset Cover) (h:x∈limited (fun j=> club K (R j)) s)(p:(Y.voyage n).kick ≤ d)(v:s ≤ Y.uv d): AtSupport false (region (Meet.spread Λ l R s) (side Y n s)) (realizeStage Y H n d s W x).val:=by
 let T:= Meet.spread Λ l R
 have hm(i:ℕ){f h:Finset Cover}(t:f⊆h): region f (side Y n i)⊆region h (side Y n i):=Finset.image_subset_image t
 have he(f:ℕ→junior K) (s:ℕ)(p':∀ j ≤ s,f j∈ club K (R j)) (v:s ≤ Y.uv d) : AtSupport false (region (T s) (ν s)) (stagewrap Y H n d s f).val:=by
   induction s with
   | zero=> exact observe_support Y H n 0 (show InTest K true (R 0) false _ from p' _ le_rfl)
   | succ s ih=>
     let t:PairIdx Y s n d:= ⟨p,v⟩
     rw [stage_next]; change AtSupport false _ ((scenic Y n d s _).val*observe Y H n (s+1) (f _).val); rw [ticket_v Y n d s t _]
     exact AtSupport.mulM ((package Y s t _ (ih (fun i k=> p' i (by omega)) (Nat.le_of_lt v) -- v.le type issue nat le, use Nat.le_of_lt v
      )).mono (hm (s+1) (Meet.spread_pays ..))) ((observe_support Y H n (s+1) (show InTest K true (R (s+1)) false _ from p' _ le_rfl)).mono (hm (s+1) (Meet.spread_has ..)))
 refine Style.display (P:=fun x=> AtSupport false (region (T s) (ν s)) ((ρ s) x).val) ?_ ?_ ?_ ?_ (show x∈Style.pressed _ from h)
 · intro f t; have u:= (pepper_rule ..).1 t; rw [stage_e Y H n d s W f u.2]; exact he f s u.1 v
 · rw [map_zero]; exact AtSupport.zeroM
 · intro a b _ _ h k; rw [map_add]; exact h.addM k
 intro a b _ p; rw [map_smul]; exact p.smulM _

-- physical reserve and dilation (cover, all steps/s). Stronger buffer retention.
theorem physical_area (j:ℕ){x:Cover}(t:x∈area Λ l S j): ∃ y∈S,∀ a: Axis,
    |x a-(Λ.R.L.val:ℤ)^j*y a| + (reserve Λ l :ℤ) ≤ (Λ.R.L.val:ℤ)^j*reserve Λ l:= by
 induction j generalizing x with
 | zero=> exact ⟨x,t,fun i=>le_of_eq (by simp)⟩
 | succ j ih=>
   rw [area] at t; obtain ⟨i,v,d⟩:= mem_biUnion.mp t; obtain ⟨y,w,rfl⟩:= mem_image.mp v; obtain ⟨z,u,rfl⟩:= mem_image.mp d; obtain ⟨x,h,a⟩:= ih w; refine ⟨x,h,fun i=>?_⟩
   let r:= Journey.reserve Λ l; let D:ℤ:=Λ.R.L.val; let R:ℤ:=seamWidth Λ l
   change |z i + D*y i-D^(j+1)*x i|+ r≤D^(j+1)*r
   have he : (r:ℤ)+R ≤ D*r:=by unfold r R D seamWidth; exact_mod_cast margin_step (Journey.prepared Λ l) Λ.R.coarse
   have hz : |z i|≤R:= abs_le.mpr ⟨(box_test.mp u).1 i,(box_test.mp u).2 i⟩
   have hd : 0 ≤ D:= Int.natCast_nonneg _
   have hu : |D*(y i-D^j*x i)|+ D*r ≤ D*(D^j*r):=by rw [abs_mul,abs_of_nonneg hd,←mul_add]; exact mul_le_mul_of_nonneg_left (a i) hd
   have hk := abs_add_le (z i) (D*(y i-D^j*x i))
   rw [pow_succ', mul_assoc D _ (x i),mul_assoc D _ (r:ℤ), add_sub_assoc, ←mul_sub]; omega
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.scenic_wind
#print axioms YM.CF.Buffered.Concord.physical_area
#print axioms YM.CF.Buffered.Concord.embedded_box
