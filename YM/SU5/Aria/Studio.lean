import YM.SU5.Aria.Legion
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric Casting
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "Φ" => P.colorSpace j x
local notation "ω"=>P.colorZero j x
local notation "X"=> P.ColorHil j x
local notation "Χ"=> P.ManyF j x
local notation "ν"=> P.seasons j x
local notation "Ω"=> P.heaven j x
local notation "u₀"=>P.rayFare j
local notation "Σ₀"=> Prod.fst (α:=P.Apron) (β:=Vantage)
local notation "Σ₁"=> Prod.snd (α:=P.Apron) (β:=Vantage)
local notation "σ"=>P.commuteTight j x Σ₀ Σ₁
local notation "θ"=>P.wealth j x
local notation "κ"=> P.enter j x
local notation "W"=> P.cartage j x
local notation "E"=> (P.seasons j x).E
local notation "R"=> ruler P.par.block
variable (D:P.Apron) (Z:P.Model0) (s t:ℕ)
lemma parsesOne {y:ℝ≥0} (h:u₀ Z = ↑y): P.parses j x [Z] = E y (σ Z Ω):=by -- typo
 unfold parses; rw [Aria.rector_left,h,sub_zero,Real.toNNReal_coe]; rfl
lemma engine_view : D.engine P j x ω= P.viewF j x D.s (P.admitted_view j D.s (D.cardB P j) (D.color P j)):= P.attended j x D.s (add_pos (D.pos j) (D.pos j)) _ _ -- args implicit w
lemma tableMaps(p:Vantage): (P.tableau j x p (D.engine P j x)) Ω=W p (θ (D.engine P j x ω)):=by unfold tableau; simp only [ContinuousLinearMap.comp_apply,P.cart_empty]; rfl
lemma loneCrest (z:ℝ≥0)(p:0<z)(y:u₀ Z=z): [Z]∈ P.Crest0 j∩P.roll0 j:=by
 refine ⟨fun b h=> ?_, show List.Pairwise _ _ from List.pairwise_singleton ..⟩
 rw [List.mem_singleton.mp h,y]; exact p
-- `parses [Apron F(center)...]`
def actorCrew (L:P.Posy j): P.ManyF j x:= P.parses j x L.val
local notation "Ψ"=> P.actorCrew j x
lemma vac_apron (H:ℕ)(F:P.Test)(S:Finset Cover)(u:F∈ bay K S true)(p:F∈enclave K)(d:Between K j 0 (R*(t+t:ℤ)) S)(q:0<t) : ∃ D:P.Apron, D.s=H∧D.u j=t∧D.S=plow K j (-(t:ℤ)) S∧ P.shifts j t D.F=F:=by
 let T:=plow K j (-(t:ℤ)) S; let A:P.Test:=P.shifts j (-(t:ℤ)) F
 have hz: Between K j ((-R)*(t:ℤ)) (R*(t:ℤ)) T:= by
    have he:=d.relocate K j (-(t:ℤ)); rw [show ruler (K).B= R from rfl,mul_neg, add_zero,_root_.mul_add, ← add_assoc,neg_add_cancel,zero_add] at he; rw [neg_mul]; exact he
 have ht:0<R:=ruler_gene _
 have hh(i:Axis):∃ y:ℕ,0<y ∧ Between K i (-R*(y:ℤ)) (R*(y:ℤ)) T:=by
    have he(t:Cover):∀ᶠ n:ℕ in atTop, (-R)*(n:ℤ)+(K).ℓ≤t i∧ t i+(K).ℓ≤R*(n:ℤ):=by
       filter_upwards [eventually_ge_atTop ((t i).natAbs+(K).ℓ)] with n h; have hg:(n:ℤ) ≤ R*(n:ℤ):= le_mul_of_one_le_left (by positivity) ht; rw [neg_mul]; omega
    obtain ⟨v,f,h⟩:= ((eventually_gt_atTop (0:ℕ)).and (T.eventually_all.mpr fun t _=>he t)).exists; exact ⟨v,f,h⟩
 choose k a h using hh
 let u':= Function.update k j t; let Y:P.Apron:= ⟨H,u',(fun i=>by by_cases p:i=j<;> simp_all [u']),A,T, P.shifts_support j _ _ u,P.shifts_keep j _ p,fun i=>by by_cases p:i=j; subst i; simpa only [u',Function.update_self] using hz; simpa [u',p] using h i⟩
 exact ⟨Y,rfl,Function.update_self ..,rfl,(P.shifts_sum j F t (-(t:ℤ))).trans (show _ from (by rw [add_neg_cancel]; exact P.shifts_zero j F))⟩
lemma realizesView (f:P.Test)(p:P.birthF j s f): ∃ D: P.Apron,D.s=s∧ P.shifts j (D.u j) D.F=f∧ D.engine P j x ω=P.viewF j x s p:=by
 let y:=P.emmigrant j s p; obtain ⟨t,v,g,h⟩:=P.fits j s y.val; have he:(P.voxTest j s g.val)=f:=(congrArg (P.voxTest j s) h).trans (P.documented j s p); obtain ⟨S,hx,hq⟩:= g.property; have hg:f∈bay K S true:=he ▸ ((by exact hx): P.voxTest j s g.val∈bay K S true); have hv:f∈enclave K:=(P.documented j s p) ▸ y.property
 obtain ⟨D,s',w,_,f'⟩:=P.vac_apron j t s f S hg hv (fun i t'=>⟨(hq i t').1,(hq i t').2.trans (by rw [_root_.mul_add]; have ht:0≤ R*(t:ℤ):=mul_nonneg (ruler_gene (Λ).block).le (by positivity); linarith)⟩) v
 have h': P.voxTest j D.s (D.cardB P j).val=f:= (D.card_price P j).trans (by rw [w]; exact f')
 refine ⟨D,s', by rw [w,f'],?_⟩; subst s; exact (P.engine_view j x D).trans (P.identical_F j x D.s _ _ h') -- subst maybe op D
local notation "T₀"=> timeMesh P.par
variable (G:P.Test)(b:P.birthF j s G)
abbrev aislePt (r:ℝ) : Vantage:= Pi.single j r
lemma cart_aisle (r:ℝ) : P.cartage j x (aislePt j r)=ContinuousLinearMap.id ℂ _:=by
 apply Eq.trans _ (P.cart_zero j x)
 apply congrArg ((P.voyageF j x).aviation (daylight (timeMesh P.par)) (look j)); funext i
 change (Pi.single j _ : Vantage) i.val = 0; simp [i.property]
abbrev announce (r:ℝ≥0) : P.Model0:= (D, aislePt j (D.realWidth P j+r))
lemma timeFare (r:ℝ≥0) : u₀ (P.announce j D r)=r:=by change (Pi.single j _ :Vantage) j - _ = _; simp
lemma mayEnter (r:ℝ≥0)(v:0<r): [P.announce j D r]∈P.Crest0 j∩P.roll0 j:= P.loneCrest j _ _ v (P.timeFare j D r) -- syntax
lemma entersAt (r:ℝ≥0): P.parses j x [P.announce j D r]= E r (P.wealth j x (D.engine P j x ω)):=by
 let X':=P.announce j D r; let y:=D.realWidth P j+r; rw [P.parsesOne j x _ (P.timeFare j D r)]; change E _ ((P.tableau j x (aislePt j y) _) _) = _; rw [P.tableMaps j x D, P.cart_aisle]; rfl
include b
lemma wasTrue : ∃ (n:ℕ)(r:ℝ≥0),s≤n∧ 0 < r ∧ ∃ D:P.Apron,D.s=n∧ θ (P.viewF j x s b)=P.parses j x [P.announce j D r]:=by
 let u:=P.emmigrant j s b
 obtain ⟨w,p,h⟩:=predecessor P.run P.large s P.history.circuit j 0 false u.val; let y:=s+w; let f:= P.voxTest j y p; have hw:s≤y:=Nat.le_add_right ..; let T:=(P.conveying s (y-s) G)
 have hc: P.shifts j (1:ℤ) f=T:=by
   unfold T; rw [← P.documented j s b]; change _=P.voxTest j y (Raise P.run P.large P.history.circuit j 0 false s y hw u.val); rw [←h]; apply Subtype.ext; exact (timed_apply P.run P.large j false y 1 p).symm
 have ht: f=P.shifts j (-(1:ℤ)) T:= by rw [←hc,P.shifts_sum,neg_add_cancel,P.shifts_zero]
 have he:T∈ enclave K:= P.refine_keeps s G ((P.documented j s b) ▸ u.property) (y-s)
 have hg:P.birthF j y f:=⟨⟨p,(show f∈enclave K from ht ▸ P.shifts_keep j _ he)⟩,rfl⟩
 obtain ⟨D,e,t,F⟩:= P.realizesView j x y f hg
 let r:= whenly T₀ y 1; have hr:0<r:=when_pos _ _ 1 (by decide)
 have hu:P.viewF j x s b=P.viewF j x y (P.passesLater j y 1 hg):= (P.view_rig j x s y b hw).symm.trans (P.identical_F j x y _ _ hc.symm)
 refine ⟨y,r,hw,hr,D,e,?_⟩; rw [P.entersAt,F, hu, P.releasedLater]
 exact P.bankHeat ..
omit b
lemma roleTotal : Dense (Submodule.span ℂ (Set.range (P.actorCrew j x)) : Set Χ):=by
 let B:= P.ColorHil j x; let U:= Submodule.span ℂ (Set.range (P.actorCrew j x)); let V:=U.comap ((θ).toLinearMap)
 have ht:(Submodule.span ℂ (Set.range (P.oneSide j x)))≤ V := Submodule.span_le.mpr (by
    rintro v ⟨⟨s,u,h⟩,rfl⟩; obtain ⟨n,r,_,hr,X',t,g⟩:= P.wasTrue j x s u h; exact (show θ (P.viewF j x s h)∈ U from Submodule.subset_span (Set.mem_range.mpr ⟨⟨_,P.mayEnter j X' r hr⟩,g.symm⟩))) -- density
 intro v; exact (P.rewarded j x v) ▸ (show θ (P.enter j x v)∈ closure (U:Set Χ) from MapsTo.closure (f:= ((θ):B→Χ)) (s:=(V:Set B)) (fun i e=>e) (θ).continuous ((P.partner_dense j x).mono (SetLike.coe_mono ht) (P.enter j x v))) -- arguments tune
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.roleTotal
