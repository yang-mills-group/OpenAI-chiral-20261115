import YM.SU5.FiniteGaugeData.Cirrus.Plisse
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus
open Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe Maison Flute
open Mink Mink.General Vp.Folio Real
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)(Ω:Bench S)(hΩ:∀ p:E4,M S p Ω.val=Ω.val)(o:‖Ω.val‖=1)
variable {ι:Type}(G:Canopy H ι)(J K:Set ι)
local notation "a"=>timeAxis
variable {m n:ℕ} (x:Points m)(y:Points n)(g:Fin m→G.Chip)(f:Fin n→G.Chip)(L:List (Fin (m+n)))(u:List (Fin m))(v:List (Fin n))(e:Ray)(s r:ℝ)
local notation "F"=> mingle x y
local notation "c"=> magnet e
abbrev Gather(r:ℝ) := (-r) • (magnet e).val
abbrev fleet(r:ℝ) (x:Points m):= moving (Gather e r) x
local notation "Y"=> fleet e
local notation "P"=> moveB e
lemma tryst (s:SO) (q:E4): turnO s.val (moving q x)=moving (walk s.val q) (turnO s.val x):= PiLp.ext fun i=>map_add ..
lemma pools (s:SO): turnO s.val (F)=mingle (turnO s.val x) (turnO s.val y):= by apply PiLp.ext; apply Fin.addCases; all_goals intro i; simp [turnO]
lemma wake: (P s).val=toll e s:=rfl
lemma twist_clock: time (walk (P s).val (Gather e r)) = sin s*r:=by simp [Gather, wake, ttake,magnet,Ray.along,e.property]; ring
lemma grows(h:0<s)(p:s< π): ∀ᶠ r:ℝ in atTop, ∀ (i:Fin m)(j:Fin n), clockV a (turnO (P s).val x) i<clockV a (turnO (P s).val (Y r y)) j:=by
 let g(r:ℝ):=sin s*r; have he:Tendsto g atTop atTop:= Tendsto.const_mul_atTop (sin_pos_of_pos_of_lt_pi h p) tendsto_id; refine eventually_all.mpr (fun i=> eventually_all.mpr (fun j=>?_)); let X:= turnO (P s).val x; let Z:=turnO (P s).val y; let l:= time (X i); let t:=time (Z j); filter_upwards [he.eventually (eventually_gt_atTop (l-t))] with u hu; change l<time ((turnO (P s).val (Y u y)) j); rw [fleet,tryst y _ _]
 change l<time (_ + _); rw [clock_add,twist_clock]; exact (sub_lt_iff_lt_add').1 hu -- orientation
-- all plane configs remain distinct for varieties
abbrev Taxi (m n:ℕ):=Fin.append (0:Fin m→ℝ) (-1:Fin n→ℝ)
lemma pride : mingle x (Y r y)=angled (F) (c) (Taxi m n) r:=by
 apply PiLp.ext; apply Fin.addCases <;> intro i <;> simp [angled,Taxi, fleet, moving, Gather]
variable (p:L.Perm (Each (m+n)))(h:ProofOrder (mingle x y) a L)
include h
lemma enrollment : ProofOrder (mingle x (fleet e r y)) a L:= by unfold ProofOrder; rw [pride, hclock]; exact h
lemma angleSmall : ∀ᶠ s:ℝ in 𝓝[>] 0,ProofOrder (turnO (P s).val (mingle x y)) a L:=by
 let T (s:ℝ):=turnO (P s).val (F); have H:Continuous T:=by convert turn_f (1:SO) e (F) using 1; simp [T]
 apply nhdsWithin_le_nhds; apply (H.tendsto' (0:ℝ) (F) (?_)).eventually ((PEye a L).mem_nhds h); unfold T; rw [wake,tiny,Luna]
include p
variable (B:Pale S Ω G J K)(H':G.Earned S Ω)(A₁:∀ i,(g i).fst∈ J)(A₂:∀ j,(f j).fst∈ K)
include hΩ o B H' A₁ A₂
lemma pour : ∀ᶠ r:ℝ in atTop, harmony S Ω G x (Y r y) g f:=by
 obtain ⟨s,h₁,h₂,h₃⟩:= ((show ∀ᶠ r:ℝ in 𝓝[>] 0,0<r from self_mem_nhdsWithin).and ((angleSmall x y L e h).and (nhdsWithin_le_nhds (gt_mem_nhds Real.pi_pos)))).exists -- h
 rw [pools] at h₂; let A:SO:= P s; let X:=turnO A.val x; let Z:=turnO A.val y; obtain ⟨j,k⟩:= splitClock X Z a (coilZ a (mingle X Z) L p h₂); obtain ⟨l,h₄,z⟩:= SortApp _ j; obtain ⟨m',h₅,w⟩:= SortApp _ k
 filter_upwards [grows x y e s h₁ h₃] with r t
 apply rotates S Ω G x _ g f H' A ( order_in _ a L p (enrollment x y L e r h)); refine adorn S Ω hΩ o G J K X (turnO A.val (Y r y)) _ _ l m' B H' A₁ A₂ h₄ h₅ z ?_ t; rw [fleet,tryst]; exact (convOrder ..).2 w -- clock & A₁ types tune
variable (q:Shelf S (magnet e))
include q
local notation "W"=> G.ornate S Ω
lemma every : harmony S Ω G x y g f:=by
 let D:=Fin.append g f; let K':= W x g* W y f; let F'(r:ℝ):= W (mingle x (Y r y)) D; let ξ:= clockV a (mingle x y); let J':= fun r=> G.Sr S Ω (angled (F) (c) (Taxi m n) r) D L; have hp:F'= J':= funext fun r=>  (H'.realRoad _ _ D L p (enrollment x y L e r h)).trans (congrArg (fun x=>G.Sr S Ω x D L) (pride x y e r))
 have h₁: ∀ᶠ r:ℝ in atTop,F' r=K':=by
    filter_upwards [pour S Ω hΩ o G J K x y g f L e p h B H' A₁ A₂] with r hr; have ht:= H'.Euclidean _ y (splitOK x y (order_in _ _ L p h)).2 f 1 (Gather e r); unfold K'; rw [ht]; unfold harmony at hr; rw [Canopy.Et]; exact hr
 obtain ⟨b,W'⟩:= eventually_atTop.mp h₁
 let X:=(b+1); have he:AnalyticOnNhd ℝ F' univ:=by rw [hp]; intro r k; exact meanMoves S Ω hΩ G (F) (c) _ _ L q r h
 have ht : (W (F) D)=F' 0:=by unfold F'; rw [fleet,Gather,neg_zero,zero_smul,zeroMove]
 refine ht.trans ((he.eqOn_of_preconnected_of_eventuallyEq (g:=fun _=> K') analyticOnNhd_const isPreconnected_univ (mem_univ X) ?_) (mem_univ _))
 exact (show ∀ᶠ r in 𝓝 X,r>b from Ioi_mem_nhds ( (lt_add_of_pos_right _ zero_lt_one))).mono (fun r t=> W' r t.le)
omit h p
lemma glories (z:(mingle x y)∈conf (m+n)): harmony S Ω G x y g f:=by
 obtain ⟨k,t,v,p⟩:= CountOra (F) z
 apply rotates S Ω G x y g f H' k z; rw [pools] at p; exact every S Ω hΩ o G J K _ _ _ _ t e v p B H' A₁ A₂ q
#print axioms glories
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus
