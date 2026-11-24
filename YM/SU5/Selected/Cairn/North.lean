import YM.SU5.Selected.Cairn.Sirene
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
set_option maxRecDepth 4200
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Attic.Cairn
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest Airy Rail Lantern Lantern.Bulb Attic Cuve
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 20000
local notation "I"=>Complex.I
open Mint Mezz Rubric Stencil
open Commission
open Afterglow Tower Tower.SlabMark Tapestry
attribute [local instance] opCStarAlgebra
namespace Giant
variable (A:Giant) {N:Side}(Z:A.Notes→basisRule){T:Type}[Fintype T][DecidableEq T] (P:Society T)(b y:Bool)(i:A.Block)(C:ℝ)(K:Calibration)
local notation "W" => P.qu.kin
local notation "Λ"=> A.patio b
local notation "L"=>A.Broad
local notation "β"=> Prize K L
local notation "Σ" S:max b:max=> Marble K W A.Zumba A.ascX A.ascY S (lv_one b) (lv_one (!b)) (priorityR b)
structure Fired (V:Window.Family)(b:Bool) (F:Buffered.Family K): Prop where
    tone: F∈ Marble K V A.Zumba A.ascX A.ascY (A.patio b) (lv_one b) (lv_one (!b)) (priorityR b)
    neutral: Neutral K F
lemma fire_mem {V:Window.Family}{F:Buffered.Family K}(p:Fired A K V b F): InTest K false (A.patio b) false F:= (show cameo (lv_one b) (lv_one (!b))=false from (by cases b <;> decide)) ▸ Marble.assign p.tone
variable {M:Tulip.Male}{m:Side} {γ δ:ℝ}(c:A.Pride Z C δ γ M (K.c m))(q:A.tokenS<(K.c m).val)
local notation "κ"=> K.c m
local notation "F₀"=> A.tonne (N:=κ) Z P b y i C
include c q
lemma ward (t:Roomy (Λ) (K.c m)): ∃ F:Buffered.Family K,F m = (F₀) ∧ Fired A K W b F:=by
 obtain ⟨F,p,h⟩:= Reach.extensionA (K:=K) t (A.tonne_guard Z P b y i C c q) (A.tonne_c Z P b y i C c q) (fun r s h=> congrArg (A.fleur Z P b y i C) h) (fun x:Fields (κ)=> lamp_age A Z P b y i C K c x.1); refine ⟨F,h,p,?_⟩; have hf:=Marble.assign p; rw [show cameo (lv_one b) (lv_one (!b))=false from (by cases b<;> decide)] at hf; exact onceNeutral hf.widen t.seats (by rw [h]; exact tonne_0 A Z P b y i C)
omit c q
structure SpireBook (V:Window.Family) where
 lamp (b:Bool) (i:A.Block): Buffered.Family K
 approved (b:Bool)(i:A.Block): Fired A K V b (lamp b i)
variable {V:Window.Family}(F:A.SpireBook K V)
noncomputable def SpireBook.arm (F:A.SpireBook K V) : β:= ⟨F.lamp b i,(fire_mem A b K (F.approved b i)).mono ((patio_2 A b).trans A.portT),(F.approved b i).neutral⟩ -- returns Proof
noncomputable def SpireBook.notes' (F:A.SpireBook K V) (i:A.Block): β:= F.arm A true i K*F.arm A false i K
noncomputable def SpireBook.bouquet : β:= ballet 1 univ (F.notes' A K)
#print SpireBook.arm
lemma bouquet_mi : (F.bouquet A K)=1-(10:ℂ)⁻¹ • ∑ i:A.Block,(F.notes' A K i):= ringtones_note ..
local notation "ρ·" b:max=> if (b:Bool) then -(10:ℂ)⁻¹ else (1:ℂ)
include c q
lemma dyes(t:∀ b, Roomy (A.patio b) (κ)) : ∃ F:SpireBook A K W, (F.bouquet A K).val m=(A.lobo Z P y c q).frame ∧ ∀ b (i:A.Block), F.lamp b i m=(ρ· b) • A.tonne Z P b y i C:=by
 choose X h g using fun b i=> ward A Z P b y i C K c q (t b); let H: SpireBook A K W:= ⟨fun b i=> (ρ· b) • X b i,fun b i=>⟨Submodule.smul_mem _ _ (g b i).tone, Commission.holdsC _ (g b i).neutral⟩⟩; let f:= poll K (A.Broad) m; let τ₀:= A.stable Z P y C c q; let S:=park (κ) L; refine ⟨H,?_,fun b i=>congrArg (fun x:Buffered.Mark _=> (ρ· b) • x) (h b i)⟩
 have he(i): f (H.notes' A K i)= polar Stencil.rho (Station.roster τ₀) i:=by
    apply Subtype.ext; funext x; let T:= tonne (N:=κ) A Z P false y i C; change ((-(10:ℂ)⁻¹ • X true i m x)*( (1:ℂ) • X false i m x))= flickH S x (tonality Stencil.rho (Station.roster τ₀ i)); rw [Station.pore τ₀ i P.club_card x]; rw [one_smul,h,h,neg_smul, neg_mul]; rfl
 change (f (ballet 1 univ (H.notes' A K))).val=_; rw [mapB,show ⇑f ∘ SpireBook.notes' A K H= _ from (show ⇑f ∘ SpireBook.notes' A K H=polar Stencil.rho τ₀.roster from funext he)]; rfl -- binder tune
omit c q
def wSpeed(N: Side): ℕ:=8*N.val
structure Equatorial (V:Window.Family) (X Y: SpireBook A K V): Prop where
 shifted (i:A.Block): Y.lamp true i= -relocate K 3 1 (X.lamp true i)
 early (i:A.Block):Y.lamp false i=X.lamp false i
-- horizon extension with only requested checks Roomy. d=1
include c q
local notation "Π"=> A.TourA.speed
omit q c in
private lemma echoes {N:Side}(h:ℤ)(Y:Buffered.Mark N)(v:ℂ): v • (-reflMark 3 h (reflMark 3 0 Y))= -reflMark 3 h (reflMark 3 0 (v • Y)):=by funext x; unfold reflMark; simp only [Pi.neg_apply,Pi.smul_apply,theta_smul,star_star,smul_neg]
omit q c in
lemma bottomY: tonne (N:=κ) A Z P false false i C= tonne A Z P false true i C:=by unfold tonne fleur Hours; simp
lemma uFocus (e:A.block=K.B)(z:∀ b,Roomy (A.patio b) (κ))(t:Roomy ((plow K 3 1 A.ascX) ∪ A.ascX) (κ)): ∃ F F':SpireBook A K W, (F.bouquet A K).val m=(A.lobo Z P false c q).frame∧(F'.bouquet A K).val m=(A.lobo Z P true c q).frame∧Equatorial A K W F F':=by
 obtain ⟨U,u,h⟩:= A.dyes Z P false C K c q z; obtain ⟨V,v,p⟩:= A.dyes Z P true C K c q z; refine ⟨U,V,u,v,fun i=>?_,fun i=>?_⟩
 · let X:=U.lamp true i; let Y:= V.lamp true i; let G:= relocate K 3 1 X; change Y= -G; have hx: InTest K true _ false G:= flow_port K 3 _ (A.fire_mem true K (U.approved true i)).widen
   have he:(Π:ℤ)=gaugeT K 1:=by change ( (↑(8*A.block.val:ℕ)):ℤ)= _; rw [e]; unfold gaugeT Heat.gaugeShift; push_cast; ring
   apply looksLike t.seats ((fire_mem A true K (V.approved true i)).widen.mono subset_union_right) (by rw [←neg_one_smul ℂ G]; exact (InTest.smul _ hx).mono subset_union_left); rw [p,Pi.neg_apply, show G m= reflMark 3 (Π) (reflMark 3 0 (U.lamp true i m)) from ?_]; · rw [h,toneness A Z P i C c q]; exact echoes ..
   rw [he]; rfl
 apply looksLike (z false).seats (fire_mem A false K (V.approved false i)).widen (fire_mem A false K (U.approved false i)).widen; rw [p,h,bottomY A Z P i C K]
end Giant
end YM.CF.Pannier.Chancel.Attic.Cairn
open YM.CF.Pannier.Chancel.Attic.Cairn.Giant
#print axioms dyes
#print axioms ward
#print axioms uFocus
#print SpireBook.notes'
#print axioms bouquet_mi
