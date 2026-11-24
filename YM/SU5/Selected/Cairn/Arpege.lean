import YM.SU5.Selected.Cairn.Note
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
namespace Voice
open Torrent
-- namespace Giant.Voice
variable (A:Giant)(K:Calibration){W:Window.Family}(F G:SpireBook A K W)(p:Equatorial A K W F G)(u:ℕ)(b:Bool)(i j:A.Block)
local notation "Ψ"=> (Prize K A.Broad)
local notation "λ₁" TTT:max i:max=> SpireBook.arm A true i K TTT
local notation "λ₀" i:max=> F.arm A false i K
local notation "τ" TTT:max i:max=> SpireBook.notes' A K TTT i
noncomputable def stroke := λ₁ F i + λ₁ G i
local notation "s" i:max=> stroke A K F G i
lemma strokes : (s i).val = F.lamp true i+G.lamp true i:= rfl
include p
lemma swept : (s i).val=F.lamp true i-relocate K 3 1 (F.lamp true i):= by rw [strokes,p.shifted,sub_eq_add_neg] -- need include p
include p
lemma studio : (λ₀ i)*(s i) = τ F i+τ G i:=by
 have ht:(λ₀ i)= G.arm A false i K:= Subtype.ext (p.early i).symm
 rw [mul_comm,stroke,add_mul,show (λ₁ F i)*(λ₀ i)=τ F i from rfl]; exact congrArg (fun x=> τ F i+ (λ₁ G i)*x) ht
-- linear and budget Criterion.
omit p
local notation "φ" x:max=> SpireBook.bouquet A K x
variable {T U: Buffered.Family K→ℂ}
noncomputable def reading (h: Scopes K A.Broad T) : Ψ→ₗ[ℂ] ℂ where
 toFun x:= T x.val
 map_add' x y:= h.plus_v x.val y.val (blush x).widen (blush y).widen
 map_smul' x y:= h.scale y.val (blush y).widen x
variable (t:Scopes K A.Broad T)(h:‖T (F.bouquet A K).val‖ < 1/2)(g:‖T (G.bouquet A K).val‖ < 1/2)
local notation "δ"=> (10:ℂ)⁻¹
local notation "ξ"=> reading A K t
include t
lemma chival (z:SpireBook A K W): 1-T (φ z).val =δ • ∑ k,T (τ z k).val:=by
 change 1-ξ (φ z)=δ • ∑ k, ξ (τ z k); rw [bouquet_mi,map_sub,map_smul,map_sum,show ξ 1=1 from t.unit]; abel
include t p h g
lemma boreal : 1< ‖δ • (∑ i:A.Block,T ((λ₀ i)*(s i)).val)‖:=by
 have ht: δ • ∑ i:A.Block,T ((λ₀ i)*(s i)).val=(1-T (φ F).val) +(1-T (φ G).val):=by
    rw [chival A K t F,chival A K t G,←smul_add,←sum_add_distrib]; refine congrArg _ (sum_congr rfl fun k _=>?_); rw [studio A K F G p]; exact (ξ).map_add (τ F _) (τ G _) -- p order
 rw [ht,show ((1:ℂ)-T (φ F).val)+(1-T (φ G).val)=2-(T (φ F).val +T (φ G).val) from (by ring)]
 have hx:= norm_sub_norm_le (2:ℂ) (T (φ F).val + T (φ G).val); rw [Complex.norm_two] at hx; linarith only [hx,h,g,norm_add_le (T (φ F).val) (T (φ G).val)] -- Complex.norm_ofNat?
lemma pique : ∃ i:A.Block, 1< ‖T ((λ₀ i)*(s i)).val‖:=by
 by_contra! z; apply (boreal A K F G p t h g).not_ge; rw [norm_smul]; apply le_trans (b:= ‖δ‖*(∑ _i:A.Block,(1:ℝ))) (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun k _=>z k))) (norm_nonneg _)); simp only [norm_inv,Complex.norm_natCast,Finset.sum_const,card_univ,show Fintype.card A.Block=10 from (by unfold Block Tour.Lolli; simp)]; norm_num -- tune
omit t p h g
structure Tonic where
    x : A.Block
    y : A.Block
    grid : Fin 5
local notation "B" x:max=> (( (Fin.val (Tonic.grid x)):ℂ))
variable (x:Tonic A)
noncomputable def ink := (λ₀ x.x)+ (B x) • (λ₀ x.y)
noncomputable def burnish := (s x.x)+(B x) • (s x.y)
noncomputable def flame := (λ₁ F x.x) +(B x) • (λ₁ F x.y) -- parent
local notation "y₀" x:max=> ink A K F x
local notation "y₁" x:max=> burnish A K F G x
local notation "y₂" x:max=> flame A K F x
noncomputable def premiere := (y₀ x)*(y₁ x)
local notation "V" x:max=> premiere A K F G x
-- no p order for t intersection. 
include t
lemma tone : T (V x).val=chord x.grid.val (T ((λ₀ x.x)*(s x.x)).val) (T (((λ₀ x.x)*(s x.y))+((λ₀ x.y)*(s x.x))).val) (T ((λ₀ x.y)*(s x.y)).val):=by
 change (ξ) (V x)= chord _ ((ξ) _) ((ξ) _) ((ξ) _); unfold premiere ink burnish; rw [mul_add,add_mul,Algebra.mul_smul_comm, Algebra.smul_mul_assoc,add_mul,Algebra.smul_mul_assoc] -- maybe `Algebra.mul_smul_comm` statement x•? check
 unfold chord; simp only [map_add,map_smul,smul_eq_mul]; ring
include p h g
lemma onReally (hu:Scopes K A.Broad U)(d:‖U (F.bouquet A K).val‖ < 1/2)(v:‖U (G.bouquet A K).val‖ < 1/2) : ∃ x:Tonic A, Torrent.fare< ‖T (V x).val‖ ∧ Torrent.fare< ‖U (V x).val‖:=by
 obtain ⟨i,z⟩:=pique A K F G p t h g; obtain ⟨j,z'⟩:= pique A K F G p hu d v; obtain ⟨n,hn,i0,i1⟩:= peacocks (T ((λ₀ i)*(s i)).val) (T (((λ₀ i)*(s j))+((λ₀ j)*(s i))).val) (T ((λ₀ j)*(s j)).val) (U ((λ₀ i)*(s i)).val) (U (((λ₀ i)*(s j))+((λ₀ j)*(s i))).val) (U ((λ₀ j)*(s j)).val) z z'
 let x:Tonic A:=⟨i,j,⟨n,hn⟩⟩; exact ⟨x,i0.trans_eq ((congrArg norm (tone A K F G t x)).symm), i1.trans_eq ((congrArg norm (tone A K F G hu x)).symm)⟩ -- includes p? omit
omit p t h g
lemma incense: Fired A K W false (y₀ x).val:= by
    let u:= (F.approved false x.x); let v:= F.approved false x.y; exact ⟨Submodule.add_mem _ u.tone ((Marble K ..).smul_mem _ v.tone),Commission.grown _⟩
lemma flame_pt : Fired A K W true (y₂ x).val:= by let u:= (F.approved true x.x); let v:= F.approved true x.y; exact ⟨Submodule.add_mem _ u.tone ((Marble K ..).smul_mem _ v.tone),Commission.grown _⟩
include p
local notation "f"=> (y₀ x)
local notation "g₁"=> (y₂ x)
local notation "g₂"=> (y₁ x)
lemma burn_lt : g₂= y₂ x+ flame A K G x:=by unfold flame burnish stroke; rw [smul_add]; abel
lemma burn_pt : Fired A K W true (g₂).val:= by let u:= flame_pt A K F x; let v:= flame_pt A K G x; rw [burn_lt A K F G p x]; exact ⟨Submodule.add_mem _ u.tone v.tone,Commission.grown _⟩
local notation "Ω" D:max=> relocate K 3 1 D
lemma mirrored : (flame A K G x).val= -Ω (g₁).val:= by change G.lamp true x.x+ (B x) • G.lamp true x.y= -Ω (F.lamp true x.x+(B x) • F.lamp true x.y); rw [p.shifted,p.shifted]; unfold relocate; rw [chime_plus,chime_scale,smul_neg,neg_add] -- neg_add?
lemma flamed_delta : (g₂).val=(g₁).val - Ω (g₁).val:=by rw [sub_eq_add_neg, ←mirrored A K F G p x]; exact congrArg Subtype.val (burn_lt A K F G p x)
noncomputable def roc := A.ascX ∪ A.ascY
local notation "Λ"=> roc A
-- factorization tests at same support, not requiring gauge coefficient days. Direct use p ok. 
omit p in
set_option maxHeartbeats 500000 in
private lemma fuse {F H:Buffered.Family K}(u:Fired A K W false F)(v:Fired A K W true H) : F*H∈ Marble K W A.Zumba A.ascX A.ascY (Λ) 10 10 1:=by
 have q:A.patio false⊆ roc A:=by rw [show A.patio false=A.ascY from rfl,roc]; exact subset_union_right
 have t:A.patio true⊆ roc A:=by rw [show A.patio true=A.ascX from rfl,roc]; exact subset_union_left
 have h₀:= Marble.grip (Marble.wider u.tone q) (Marble.wider v.tone t)
 rw [show lv_one false+lv_one true=10 from rfl, show lv_one (!false)+lv_one (!true)=10 from rfl, show priorityR false+priorityR true=1 from rfl] at h₀
 exact h₀
lemma opal : (f).val*(g₂).val∈ Marble K W A.Zumba A.ascX A.ascY (Λ) 10 10 1 := fuse A K (incense A K F x) (burn_pt A K F G p x)
lemma premium {Q:Buffered.Family K→ℂ}(h:Scopes K A.Broad Q): Q (V x).val= Q ((f).val*(g₁).val)-Q ((f).val*Ω (g₁).val):=by
 let a:= flame A K G x; let Φ:= reading A K h; have hp : Φ (V x) =Φ (f*g₁)- Φ (f*(-a)):=by rw [←map_sub,←mul_sub,sub_neg_eq_add]; exact congrArg (fun x=> Φ (f*x)) (burn_lt A K F G p x)
 change Q (V x).val=_; have hs:(f*(-a)).val=(f).val*Ω (g₁).val:=congrArg ((f).val*·) (show -a.val=Ω (g₁).val from (by rw [show a.val=_ from mirrored A K F G p x,neg_neg])); rw [←hs]; exact hp
end Voice
end Giant
end YM.CF.Pannier.Chancel.Attic.Cairn
open YM.CF.Pannier.Chancel.Attic.Cairn.Giant.Voice
#print axioms opal
#print axioms premium
#print axioms flamed_delta
#print axioms onReally
