import YM.SU5.Twilight.Flight
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
local notation "T"=> P.par
local notation "X"=>P.ColorHil j x
local notation "X₀"=>P.colorSpace j x
local notation "Y"=> P.physicalEnergy j x
local notation "C"=> P.walksColor j
local notation "π"=> P.pinJoint j
local notation "ω"=> P.colorZero j x
local notation "M"=> timeMesh P.par
local notation "Γ"=> marks M
local notation "N"=> notch M
local notation "ν"=> daylight M
local notation "κ"=> P.voyageF j x
local notation "V" i:max=> ((κ).crew i).play
local notation "F"=> look j
local notation "v"=> P.visitors j x
local notation "S"=>P.seasons j x
local notation "A"=> P.Viewers j x
local notation "Ω"=> P.heaven j x
local notation "ω'"=> P.bank j x
local notation "ϑ"=> P.enter j x
open WeakDual TopologicalSpace
open scoped Pointwise
section helper
variable (x':OS.Cross j)
-- real offset vector
noncomputable def transverse (p:Trans j→ℝ): OS.Cross j:=
 ⟨WithLp.toLp 2 (fun i:Axis=> if h:i = j then (0:ℝ) else p ⟨i,h⟩), by
    change dite _ _ _=0; simp⟩
lemma transverse_eyes (p:Trans j→ℝ)(a:Trans j) : (transverse j p).val a.val=p a:=dif_neg a.property
lemma eyes_toFace : x'=transverse j (fun i=>x'.val (i.val)):=by
 apply Subtype.ext; ext i; by_cases h:i=j
 · subst i; change x'.val _=dite _ _ _; rw [dif_pos rfl]; exact x'.property
 exact Eq.symm (transverse_eyes j _ ⟨i,h⟩)
-- algebraic plane map
local notation "o"=>transverse j
local notation "β" i:max=> (κ).raw i
lemma sails_smooth (p:Trans j→ℝ): (S).U (o p)= (κ).aviation (ν) (F) p:=by
  change Alliance.aviation _ _ _ (fun i:Trans j=>_) = _; congr 1; exact funext (transverse_eyes j p)
lemma lift_motions (p:Trans j→Γ)(b:P.ManyF j x): P.enter j x ((S).U (o (fun i=> ((p i):ℝ))) b)=(κ).raw F p (P.enter j x b):=by
  rw [P.sails_smooth]
  change (κ).flight (ν) (F) _ b.val= _; rw [Alliance.smooth_notch,ContinuousLinearMap.comp_apply, Alliance.grounded _ _ b.property]; rfl
lemma roll_motion (p : Trans j→ Γ)(z:X): (P.seasons j x).U (o (fun i=> ((p i):ℝ))) (ω' z)= ω' ((κ).raw F p z):=by
  apply (ϑ).injective; rw [P.lift_motions]
  change (κ).raw F p (v z) = v ((κ).raw F p z); exact DFunLike.congr_fun ((κ).ground (F) _ (fun i _ c=> ((κ).hard (F) _ (fun i _ k=>(κ).cCom ..) p).symm)) z
set_option maxHeartbeats 220000
private lemma band_life (p:Trans j→ Γ)(b:P.ColorHil j x)(L:List (Trans j))(g: ∀u:Grid j,X₀ (C u) b=b): (κ).raw L p b=b:=by
 induction L with
 | nil=> rfl
 | cons i t ih=> rw [Alliance.raw_step,ContinuousLinearMap.comp_apply,ih]; obtain ⟨s,c,h⟩:=notch_exists M (p i); rw [← h, P.meets,g]
private lemma realStep (b:P.ManyF j x)(q:∀u:Grid j, X₀ (C u) (ϑ b)=(ϑ b))(p:Trans j→ℝ): (κ).aviation (ν) (F) p b=b := by
  have hd : DenseRange fun y: Trans j→ Γ => fun i : Trans j=> ((y i):ℝ):= DenseRange.piMap fun i:Trans j=>(ν).denseRange_val -- ↑ properties
  refine congrFun (hd.equalizer (g:= fun p : Trans j→ℝ=> (κ).aviation (ν) (F) p b) (h:=fun _=>b) ((κ).aviation_cont (ν) (F) _ (fun i _=>continuous_apply i) b) continuous_const ?_) p
  funext y; apply (ϑ).injective; change P.enter j x ((κ).aviation (ν) (F) _ b)=_; rw [←P.sails_smooth,P.lift_motions]; exact P.band_life j x y (ϑ b) F q
-- converse: isolated motion; ease raw general helper independent parameters below or here
lemma motion_one (k:Trans j) (p:Γ) : (κ).raw F (fun i=> if i=k then p else 0) = ((P.voyageF j x).crew k).play p:=by
 let Vw(i:Trans j)(L:List (Trans j)):=i∈L
 let f(i:Trans j):Γ:=if i=k then p else 0
 have overall(L:List (Trans j))(t:L.Nodup): (κ).raw L f= if k ∈ L then ((κ).crew k).play p else ContinuousLinearMap.id ℂ _:=by
   clear Vw; induction L with
   | nil=> simp only [Alliance.raw_nil,List.not_mem_nil,if_false]
   | cons i L ih =>
     obtain ⟨u,ht⟩:=List.nodup_cons.mp t
     rw [Alliance.raw_step,ih ht]; simp only [List.mem_cons]; unfold f
     by_cases h:k=i
     · subst i; rw [if_pos rfl, if_pos (Or.inl rfl),if_neg u]; rfl
     rw [if_neg (Ne.symm h), ((κ).crew i).play_zero]; simp [h]
 change (κ).raw F f=_; rw [overall F (look_one j),if_pos (look_all j k)] -- implicit?
lemma motion_at (a:Trans j)(s:ℕ)(t:ℤ)(b:P.ManyF j x):
    P.enter j x ((S).U (transverse j (fun i=>((↑(if i=a then N s t else (0:Γ))):ℝ))) b) = X₀ (C (s,t,a)) (P.enter j x b):=by
 exact (P.lift_motions j x (fun i=>if i=a then N s t else 0) b).trans (DFunLike.congr_fun ((P.motion_one j x a (N s t)).trans (P.meets j x a s t)) _)
lemma cross_iff (b:P.ManyF j x): (∀ a:OS.Cross j,(S).U a b=b) ↔ ∀ u:Grid j, X₀ (C u) (ϑ b)=ϑ b:=by
 refine ⟨fun h ⟨s,t,k⟩=> (P.motion_at j x k s t b).symm.trans (congrArg (fun z=> P.enter j x z) (h _)), fun p a=>?_⟩
 rw [eyes_toFace j a,P.sails_smooth]; exact P.realStep j x b p _
lemma heavenRank (p:P.lodestarHere j x) (b:P.ManyF j x): b∈Submodule.span ℂ {Ω} ↔
 (∀ t:ℝ, (S).edge t b=b) ∧ (∀ c:OS.Cross j,(S).U c b=b):=by
 have h₁: b∈Submodule.span ℂ {Ω} ↔ (ϑ b)∈ Submodule.span ℂ {ω}:= by
    simp only [Submodule.mem_span_singleton]; refine exists_congr fun t=>?_; change t • Ω=b ↔ t • ω= _; rw [←(ϑ).injective.eq_iff,map_smul]; rfl

 rw [h₁,← (P.selected_physical j x p).2,P.actual_color]; refine and_congr (forall_congr' fun t=> ?_) ((P.cross_iff j x b).symm); rw [←P.soleEdge,(ϑ).injective.eq_iff]
end helper
-- density of Gram labels projected. remains with P.spirits but more work to check 
-- properties of the projected products.
open Set in
lemma bankSpan (R:P.Register): Dense (Submodule.span ℂ (Set.range (P.wealth j x ∘ P.operatorWord R j x)): Set (P.ManyF j x)):=by
 let f:= P.wealth j x; let L:= Submodule.span ℂ (Set.range (P.operatorWord R j x)); let D:=Submodule.span ℂ (Set.range (P.wealth j x ∘ P.operatorWord R j x)); have h: L.map f.toLinearMap=D:= by
   rw [show D=Submodule.span ℂ (Set.range (P.wealth j x ∘ P.operatorWord R j x)) from rfl,range_comp]; unfold L; rw [Submodule.map_span]; rfl -- notation lemma?
 have ht: MapsTo (⇑f) (L:Set X) D:= fun i p=> (show f i∈D by rw [←h]; exact ⟨i,p,rfl⟩)
 intro y; let a:=ϑ y; exact (show f a=y from P.rewarded j x y) ▸ MapsTo.closure ht f.continuous (P.quarterFull R j x a)
-- rank + sustaining spectral on every chosen purchase with `P.seasons` motions.
open OS.Semigroup
lemma char_positive (b:P.ManyF j x): ∀ᵐ p ∂ ((S).ℚmeasure.diagonal b), 0 ≤ p j:=(S).bright _
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.heavenRank
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.bankSpan
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.char_positive
