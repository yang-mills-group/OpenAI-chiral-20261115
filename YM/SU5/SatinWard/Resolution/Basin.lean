import YM.SU5.Assay.CharterCost
import YM.SU5.SatinWard.Resolution.Sandstone
import YM.SU5.Assay.RawLag
import YM.SU5.Aria.Silhouette
import YM.SU5.Aria.Marquee
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
local notation "ψ"=> P.physicalEnergy j x
local notation "Ω"=> P.heaven j x
local notation "E"=> (P.seasons j x).E
local notation "T" r:max=> Real.toNNReal r
local notation "W"=> P.cartage j x
local notation "V"=> P.tableau j x
local notation "ρ"=> P.wealth j x
local notation "κ"=> P.enter j x
open OS.Semigroup OS.Semigroup.Marble
namespace MarbleFace
local notation "L"=>[false,true]
variable (A:Bool→ P.Apron)(p q:Bool→ Vantage)
local notation "ι₀"=>Bool
local notation "ι₁"=>false
local notation "L✩" b:max=> [b, !b]
local notation "B"=> true
variable (b:Bool)
lemma imPrev: Immutable (ψ) (P.colorZero j x):=⟨fun t=> P.sector_hot j x _, origin_norm _ (P.unit_too j x)⟩ -- edit
lemma imMemo: Immutable (ν) (P.heaven j x):=⟨fun t=> P.heaven_hot j x _, origin_norm _ (P.unit_too j x)⟩
local notation "Ω₀"=> P.colorZero j x
local notation "𝜉"=> P.laysM
local notation "C"=> P.commonWell j x
local notation "P₀"=> P.preview j x
local notation "C₁"=> P.memorial j x
local notation "q✩" i:max=> P.porchY j A i
local notation "v✩" i:max=> P.resignY j A i
local notation "Υ"=> P.charter j x
local notation "f" x:max b:max=> (A b).engine P j x
variable (r:Bool→P.VMark)
noncomputable def preMosaic := P₀ A (L✩ b) r-P₀ A [false] r*P₀ A [true] r
noncomputable def scoreMosaic:= C A p L-C A p [false]*C A p [true]
noncomputable def memMosaic:= C₁ A (L✩ b) p-C₁ A [false] p*C₁ A [true] p
lemma mem_one: C₁ A [b] p= whisper Ω ((V) (p b) (f x b)):=by unfold memorial; rw [← rector_view (ν) Ω _ _ _ (P.heaven_hot j x) 0]; change inner ℂ Ω ( E _ (V _ _ Ω))=_; rw [← OS.Semigroup.swing, P.heaven_hot]
lemma prev_one: P₀ A [b] r= whisper Ω₀ (Υ (r b) (f x b)):=by unfold preview; rw [←rector_view (ψ) Ω₀ _ _ _ (P.sector_hot j x) 0]; change inner ℂ Ω₀ ( (ψ).E _ (Υ _ _ Ω₀))=_; rw [← OS.Semigroup.swing (ψ), P.sector_hot]
local notation "Z"=> (q✩ p) (!b) - (v✩ p) b
lemma mem_pair: C₁ A (L✩ b) p= hotPair (ν) Ω Z ((V) (p b) (f x b)) ((V) (p (!b)) (f x (!b))):=by unfold memorial; rw [←rector_view (ν) Ω _ _ _ (P.heaven_hot j x) 0]; change inner ℂ Ω (E _ (V _ _ ((ν).wax Z (V _ _ Ω))))= _; rw [←OS.Semigroup.swing,P.heaven_hot]; rfl
local notation "Z₀"=> (q✩ (𝜉 ∘ r)) (!b) - (v✩ (𝜉 ∘ r)) b
lemma pre_pair: P₀ A (L✩ b) r= Marble.hotPair (ψ) Ω₀ Z₀ (Υ (r b) (f x b)) (Υ (r (!b)) (f x (!b))):=by unfold preview; rw [←rector_view (ψ) Ω₀ _ _ _ (P.sector_hot j x) 0]; change inner ℂ Ω₀ ((ψ).E _ (Υ _ _ ((ψ).wax Z₀ (Υ _ _ Ω₀))))=_; rw [←OS.Semigroup.swing (ψ),P.sector_hot]; rfl
lemma mem_sum:memMosaic P j x A p b= OS.Semigroup.Marble.seam (ν) Ω Z ((V) (p b) (f x b)) ((V) (p (!b)) (f x (!b))):=by unfold memMosaic OS.Semigroup.Marble.seam; rw [mem_pair,mem_one,mem_one]; cases b; rfl; rw [mul_comm]; rfl
lemma pre_sum:preMosaic P j x A b r= OS.Semigroup.Marble.seam (ψ) Ω₀ Z₀ (Υ (r b) (f x b)) (Υ (r (!b)) (f x (!b))):=by unfold preMosaic OS.Semigroup.Marble.seam; rw [pre_pair,prev_one,prev_one]; cases b; rfl; rw [mul_comm]; rfl
lemma both_perm : (L).Perm (L✩ b):=by cases b; exact List.Perm.refl _; exact List.Perm.swap ..
variable (J:P.Ellis j x)(k:Axis)
include J
lemma mem_ready (v:P.Turnstile k A (L✩ b) p): memMosaic P k (P.advocate j x k) A p b= scoreMosaic P j x A p:=by unfold scoreMosaic memMosaic; rw [P.common_cult j x _ _ L J (both_perm b) v]; rw [P.common_cult j x _ _ [false] J (List.Perm.refl _) (show P.Turnstile k A [false] p from List.pairwise_singleton ..),P.common_cult j x _ _ [true] J (List.Perm.refl _) (show P.Turnstile k A [true] p from List.pairwise_singleton ..)]
-- all Character and order. Tessellated by translates (common).Plenum a call 
local notation "S"=>scoreMosaic P j x A
lemma score_pose (v:Vantage) (c:P.Turnstile k A (L✩ b) p): S (fun i=>v+p i)=S p:=by change S (settler p v)=_; unfold scoreMosaic; rw [(P.common_shift j x A p L J ⟨k,L✩ b,both_perm b,c⟩ v).2,(P.common_shift j x A p [false] J (?_) v).2, (P.common_shift j x A p [true] J (?_) v).2]; all_goals exact ⟨k,_,List.Perm.refl _, List.pairwise_singleton ..⟩
lemma preScore (u:P.Turnstile k A (L✩ b) (P.laysM∘ r))(c:P.Plenum A (L✩ b) (P.laysM ∘ r)): preMosaic P k (P.advocate j x k) A b r=S (P.laysM ∘ r):=by
 unfold preMosaic; rw [←mem_ready P j x A (𝜉 ∘ r) b J k u, P.entirely_now j x A _ J k r u c]; unfold memMosaic; have h(i:Bool):P.preview k (P.advocate j x k) A [i] r=P.memorial k (P.advocate j x k) A [i] (P.laysM∘r):=P.entirely_now j x A _ J _ r (List.pairwise_singleton ..) ⟨fun _=>⟨_,List.Perm.refl _, List.pairwise_singleton ..⟩⟩; rw [h,h]
-- any Vantage all.Fin real consistency. alt. Need tuple height. Aria transfers. provide linear grid lemma.
omit J
lemma reveal_here (t:Bool→ Cover) (s:ℕ)(w:P.Turnstile j A (L✩ b) (P.laysM ∘ P.vtile s ∘ t))(e:∀i,(A i).s=s): let g(i:Bool):= P.chartAll (t i) (A i).F; let Q:= P.singleState j s x; preMosaic P j x A b (P.vtile s ∘ t)= Q (g b *g (!b))-Q (g b)*Q (g (!b)):=by
 intro g Q; have h(i:Bool):(A i).full P s=(A i).F:=by unfold Apron.full; rw [e,Nat.sub_self]; rfl
 unfold preMosaic; rw [P.turn_purchase j _ A t s (L✩ b) w (fun i _=>(e i).le),P.turn_purchase j _ A t s [false] (List.pairwise_singleton ..) (fun i _=>(e i).le), P.turn_purchase j _ A t s [true] (List.pairwise_singleton ..) (fun i _=>(e i).le)]; unfold fullScroll; simp only [List.map_cons,List.prod_cons,List.prod_nil,List.map_nil,h,mul_one]; cases b; rfl; rw [mul_comm (P.singleState j s x _) (P.singleState j s x _)]; rfl
-- time stamp packaging for centers Y on either Color/Many. Width costs unchanged.
local notation "Γ"=> P.charter j x
local notation "Ψ"=> P.tableau j x
local notation "δ"=> P.locate j x
local notation "ε"=> P.reprise j x
-- fix
lemma anchor_duo (β:ℝ)(l l' r r':ℝ)(e:0 ≤ β)(p₀:0≤ r)(t₀:0 ≤ l')(u:r+β+l'=Z) :
 memMosaic P j x A p b= Marble.seam (ν) Ω β ((ν).sand (P.tableau j x (p b) (f x b)) l r) ((ν).sand (P.tableau j x (p (!b)) (f x (!b))) l' r'):=by rw [mem_sum, Marble.outside (ν) Ω β (imMemo ..) _ _ _ _ _ _ p₀ t₀ e,u]
lemma anchor_pre (β:ℝ)(l l' s s':ℝ)(e:0≤β)(p₀:0≤ s)(t₀:0 ≤ l')(u:s+β+l'=Z₀) :
 preMosaic P j x A b r= Marble.seam (ψ) Ω₀ β ((ψ).sand (Γ (r b) (f x b)) l s) ((ψ).sand (Γ (r (!b)) (f x (!b))) l' s'):=by rw [pre_sum, Marble.outside (ψ) Ω₀ β (imPrev ..) _ _ _ _ _ _ p₀ t₀ e,u]
lemma charter_bank_arm (r:Vantage) (Z':(P.ManyF j x).Op): quietArm (P.heaven j x) (δ r Z')= W r (quietArm (P.heaven j x) Z'):=by
 change (δ r _) _ - whisper _ _ • _= W r (Z' _- _); rw [map_sub,P.cart_vac, (show whisper Ω (δ r Z')=whisper Ω Z' from P.cart_wash j x Z' r)]; change _=W r _- W r (_ • _); rw [map_smul,P.cart_empty]
lemma charter_previous (r:P.VMark) (Z':(P.ColorHil j x).Op): quietArm (P.colorZero j x) (Γ r Z')= P.truck j x r (quietArm (P.colorZero j x) Z'):=by
 change (Γ r _) _ - whisper _ _ • _= P.truck j x r (Z' _- _); rw [map_sub,P.truck_vac, (show whisper Ω₀ (Γ r Z')=whisper Ω₀ Z' from P.truck_wash ..)]; change _=P.truck j x r _- P.truck j x r (_ • _); rw [map_smul,P.truck_empty]
lemma pushed_arm (G:(P.ColorHil j x).Op): quietArm Ω (P.reprise j x G)= P.wealth j x (quietArm Ω₀ G):=by
 change (ε G) Ω - whisper Ω _ • Ω= P.wealth j x (G Ω₀ - whisper Ω₀ G • Ω₀); rw [map_sub,map_smul,(show whisper Ω (ε G)=whisper Ω₀ G from P.reprise_vac ..)]; change _ = ε G Ω- _ • P.wealth j x (P.enter j x Ω); rw [P.reprise_empty]
lemma push_arm_cost (G:(P.ColorHil j x).Op): ‖quietArm Ω (ε G)‖ ≤ ‖quietArm Ω₀ G‖:=by rw [pushed_arm]; exact ((P.wealth j x).le_of_opNorm_le (P.enter_wealth j x) _).trans_eq (one_mul _) -- check
end MarbleFace
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
