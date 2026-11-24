import SatinPP.Clerestory

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option maxRecDepth 4500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria
open Hierarchy.Celeritas Land Hierarchy.Seld.Leal
variable (P:Spine)(x:P.Spectrum0 3)
open Germ Alliance Selected FirstWindows

variable (j:Axis)
local notation "C" => P.room
local notation "χ"=>P.chateau x j
local notation "L"=>P.sitting x j
local notation "ξ"=>P.advocate 3 x j
local notation "H"=>P.ColorHil j (P.advocate 3 x j)
local notation "B" s:max f:max=> Selected.bud P.run P.large P.law s P.history P.projection.clipped j false (C j) (χ) f
local notation "ℱ"=>P.voxTest j

local notation "R"=>P.revolving x j
local notation "Θ"=>P.physicalEnergy j (P.advocate 3 x j)
local notation "δ"=>Selected.ride P.run P.large P.law P.history P.projection.clipped j false (C j) (χ)
local notation "M"=>timeMesh P.par
local notation "ℛ"=>P.voyageF j ξ
local notation "ℛ'"=>turnstile P.run P.large P.law P.history P.projection.clipped j false (C j) (χ)

open ConePrice SelectionAnalysis
open LightBudget Six
local notation "D"=>P.darkHalf (flank j 0)
local notation "T'"=>tent P.run P.large
local notation "Known"=> FirstWindows.Domain P.run P.large P.projection false Set.univ
local notation "V"=>osValue P.run P.large P.law P.projection j (C j) (χ)
local notation "N"=>P.litKet x j
local notation "O"=>P.glitter x j
local notation "Ms"=>gram j (tent P.run P.large)
local notation "Y₁"=>shop j (tent P.run P.large)
local notation "Y₂"=>floor j (tent P.run P.large)


/-- Quantitative version of the dictionary in Cone/Test. -/
lemma parking (z:placement P.par)(a:D)(c d:ℝ)
 (t:0≤coordinates P.par z j) (s:0≤c)(s':0≤d)
 (p:dist (N a) (transverse_play (O) z (N a)) ≤ c)
 (q:d ≤ dist (N a) ((δ).E (coordinates P.par z j).toNNReal (N a))) :
 ∃ h:Ms (Y₁ z a)∈ Known, ∃i:Ms (Y₂ z a)∈ Known, 
   (V ⟨Ms (Y₁ z a),h⟩).re ≤ c^2 ∧ d^2 ≤ (V ⟨Ms (Y₂ z a),i⟩).re:=by
 have g:0 ≤ coordinates P.par (onlyTime j z) j := by simp;exact t
 let b:D:= ⟨(move (T') z) a,budget_base P.run P.large P.law P.projection j 0 a z a.2 t⟩
 let y:D:= ⟨(move (T') (onlyTime j z)) a,budget_base P.run P.large P.law P.projection j 0 a _ a.2 g⟩
 let u:= (coordinates P.par z j).toNNReal
 refine ⟨gram_covered _ _ _ _ _ (b-y).property,gram_covered _ _ _ _ _ (a-y).property,?_⟩
 have hy : N y=(δ).E u (N a):=by
   dsimp only [u]; rw [←LightBudget.plaza]; exact physical_move P.run P.large P.law P.projection j (C j) (χ) a a.property _ g y.property
 have hb : N b=(δ).E u (transverse_play (O) z (N a)):= physical_move P.run P.large P.law P.projection j (C j) (χ) a a.property _ t b.property
 change (V ⟨Ms (b-y:↥(D)),_⟩).re ≤ c^2∧d^2 ≤ (V ⟨Ms (a-y:↥(D)),_⟩).re
 rw [gram_pays P.run P.large P.law P.projection j (C j) (χ) _ (b-y).property,
   gram_pays P.run P.large P.law P.projection j (C j) (χ) _ (a-y).property]
 change ‖N (b-y)‖^2≤ c^2 ∧ d^2≤‖N (a-y)‖^2
 rw [map_sub,map_sub,hb,hy,← map_sub]
 have v:= (δ).E u |>.le_of_opNorm_le ((δ).shrinks _) (transverse_play (O) z (N a) - N a)
 rw [one_mul,←dist_eq_norm,dist_comm] at v
 rw [dist_eq_norm] at q
 exact ⟨pow_le_pow_left₀ (norm_nonneg _) (v.trans p) _,pow_le_pow_left₀ s' q _⟩



abbrev post(k:Axis)(t:ℕ)(n:ℤ):= Picket.byStamp j k (notch M t n)
lemma label_cost(k:Axis)(y:k≠j)(t:ℕ)(n:ℤ):
 coordinates P.par (P.post j k t n) j=P.gradeZ t n :=by
 change ((P.post j k t n) j:MeshClock.marks _).val=P.gradeZ t n
 unfold post Picket.byStamp
 rw [update_of_ne y.symm,update_self]
 rfl
lemma parlor_walk(k:Axis)(y:k≠j)(t:ℕ)(n:ℤ)(v:H):
 transverse_play (O) (P.post j k t n) (R v)= R (P.truck j ξ (P.vtile t (wheel k n)) v):=by
 rw [←P.play_gate]
 unfold transverse_play truck
 have g : (fun i:Trans j=>(P.post j k t n) i.val)=(P.vtile t (wheel k n)) ∘ Subtype.val:=by
    funext i;by_cases h:i.val=k
    · simp [post,Picket.byStamp,h,vtile,wheel]
    simp [post,Picket.byStamp,h,i.property,vtile,wheel,MeshClock.notch,MeshClock.bell] ;rfl
 rw [g];rfl


open MacroGrid
abbrev mix (m:Lead.Clan→ℂ)(f:Lead.Clan→ ↥(D)):D:=∑i,m i • f i
abbrev PaidStamp (f:Lead.Clan → ↥(D))(t:ℕ)(d ϵ:ℝ):Prop:=
 ∀ k:Axis,k≠j→∀n:ℤ,0<P.gradeZ t n→P.gradeZ t n ≤ ϵ →∀m,fanSet m→
   let z := P.post j k t n
   let a := P.mix j m f
   let l:= P.gradeZ t n
   ∃ h:Ms (Y₁ z a)∈ Known,∃i:Ms (Y₂ z a)∈ Known, 
   (V ⟨Ms (Y₁ z a),h⟩).re ≤ (l*((13/2)/d))^2 ∧ (l*((27/4)/d))^2 ≤ (V ⟨Ms (Y₂ z a),i⟩).re

lemma check_post
 (d ϵ:ℝ)(y:0<d)(t:ℕ)
 (L':Lead.Clan → (P.ColorHil 3 (P.advocate 3 x 3)).space)
 (b: P.HardRide x L' t d ϵ)
 (f:Lead.Clan→↥(P.darkHalf (flank 3 0)))
 (w:∀i,P.litKet x 3 (f i)=P.revolving x 3 (L' i)):
 P.PaidStamp x 3 f t d ϵ:=by
 intro k u n a h m g
 have e:= b k u n a h m g
 obtain ⟨i,l⟩:= e
 have q:P.litKet x 3 (P.mix 3 m f)=P.revolving x 3 (ounce m L'):=by
    unfold mix ounce
    simp only [map_sum,map_smul,w]
 refine P.parking x 3 (P.post 3 k t n) (P.mix 3 m f) _ _ ((P.label_cost 3 k u t n).symm ▸ a.le)
    (by positivity) (by positivity) ?_ ?_
 · rw [q,P.parlor_walk _ _ _ u, LinearIsometryEquiv.dist_map];exact i
 rw [q,P.label_cost _ _ u, ←P.spins_heat,LinearIsometryEquiv.dist_map]; exact l
