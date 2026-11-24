import Velour.Crepe.Sheen
import Velour.Tassel.Table
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 800000
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
open Aria Set TopologicalSpace Metric
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "Y₀"=> P.run
local notation "Φ" => P.colorSpace j x
local notation "ω"=>P.colorZero j x
local notation "u"=> enclave P.calibration
local notation "X"=> P.ColorHil j x

local notation "E"=> (P.physicalEnergy j x).E
local notation "m"=> timeMesh P.par
local notation "Q" => P.shifts j
local notation "L"=> P.par.R.L.val
variable {s t v w:ℕ}
open Papal Lamour.Bridge.Celeste Sonnet VelourBoard
variable {Z:Weaver}{A:Finset Cover}(h:Lamour.Bridge.Celeste.Voice Z A)
local notation "B'"=>P.par.block
local notation "r'"=>ruler P.par.block
local notation "ℓ"=>P.calibration.ℓ

/-- recentred by b full ticks along the chess time-axis j -/
def xStart (j:Axis)(b:ℕ):VelourBoard.Cell := fun i=> if i=j then 0 else -(b:ℤ)
lemma xStart_zero (j:Axis)(b:ℕ): xStart j b j=0:=by rw [xStart,if_pos rfl]

variable (p b:ℕ)
local notation "D"=>  xStart j b
local notation "W"=>  (b+b:ℕ)
structure Wig (P:Spine) (A:Finset Cover) (p b:ℕ): Prop where
 vol:0<b
 spatial (j:Axis):VelourBoard.Parcel P.calibration (b+b) (xStart j b) 0 (plow P.calibration j b A)
 rural (j:Axis):∀ y∈ plow P.calibration j b A, Secured P.calibration (b+b) (xStart j b) (p+1) 0 y

lemma ready_wig (A:Finset Cover): ∀ᶠ b:ℕ in atTop, P.Wig A p b:=by
 let d:=ℓ+p+1
 have fits:∀ᶠ b:ℕ in atTop,∀ z∈A,∀ i:Axis, -(r'*(b:ℤ))+d ≤ z i ∧ z i+d≤ r'*b:=by
    apply (A.eventually_all).mpr 
    intro z _
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [eventually_ge_atTop (d+(z i).natAbs)] with b hb
    have h:=le_mul_of_one_le_left (show 0≤(b:ℤ) by positivity) (ruler_gene P.par.block)
    omega

 filter_upwards [fits,eventually_gt_atTop (0:ℕ)] with b f v
 suffices G:∀ c≤d,∀ j:Axis,∀ y∈plow K j b A, Secured K (b+b) (xStart j b) c 0 y from
    ⟨v,fun j i y h=>G ℓ (by unfold d; omega) j y h i,G (p+1) (by unfold d; omega)⟩
 intro c t j y hh i
 obtain ⟨z,k,rfl⟩:= plow_stays K j _ _ hh
 unfold Wall xStart
 have h:= f z k i
 have ht:(c:ℤ)≤(d:ℕ):=by exact_mod_cast t
 have hx:(K).B = P.par.block:=rfl
 rw [SlabMark.moves,hx]
 by_cases a:i=j
 · simp only [a,ite_true, Pi.zero_apply,Nat.cast_add]
   subst j; constructor <;> linarith only [h.1,h.2,ht]
 rw [if_neg a,if_neg a]; simp only [Pi.zero_apply,Nat.cast_add]; constructor <;> linarith only [h.1,h.2,ht]




variable (N:Side)
def sourceSong (A:Finset Cover)(Z:Papal.Weaver): Sonnet N:=⟨Z N, dBook N A,0⟩
lemma driftBook :
 (( (sourceSong N A Z).twistL j 0).twistL j (gaugeT K b)).S=dBook N (plow K j b A):=by
    unfold twistL sourceSong
    dsimp only
    rw [← d_Book_flip, ←d_Book_flip,Tower.support_translation,sub_zero]; rfl
lemma driftSong (i s:ℕ):
 exhibit Y₀ H s (P.nomadic i) (P.shifts j b (P.tuneK h)).val=
 (((sourceSong (Papal.count P.run s (P.nomadic i)) A Z).twistL j 0).twistL j (gaugeT K b)).x:=by
 change exhibit _ _ _ _ (household P.calibration (traction j (gaugeT K b) Z))=_
 rw [P.vel_ex, P.commuter]; rfl


variable {C B ε σ:ℝ}
include h in
lemma flickCost (z:0∈A)(g:Clarity Z P.par.K.j (B/4))
 (q:∀ (N:Side)(y:Fields N),‖Z N y‖≤C)(e:0<ε) :
 ∀ᶠ t:ℝ in 𝓝[>] (0:ℝ),∀ᶠ N:Side in atTop,Even N.val → ∀ M:Tulip.Male, 
 Cost P.par.K.j (breadth 0 A) A.card M ε t C B (sourceSong N A Z):=by
 filter_upwards [h.1.fee ε e] with t ht
 filter_upwards [g,breadthMoney 0 A] with N p z' v M
 rw [map_zero] at z'
 exact ⟨⟨q N,ht N⟩,h.2 N,h.1.bounded N,card_image_le,z',by simpa only [sourceSong,map_zero] using (Finset.mem_image_of_mem (wrap (More N)) z),p v _ ⟩

-- the cap body's charge, still at mean
abbrev Tonal (s b:ℕ)(g:P.Test)(ρ:ℝ):Prop :=
 ∃ (a:P.Card j s (b+b))(p:0<b+b), P.voxTest j s a.val=Q b g ∧ ‖P.Box j s (b+b) p a‖ ≤ ρ


variable {p b} {r d:ℕ}{ξ θ:ℝ}
local notation "ν"=> P.par.K.j
lemma tremor
 (a:∀ᶠ N:Side in atTop,Even N.val → ∀ M:Tulip.Male, 
  Cost P.par.K.j r d M ε ξ C σ (sourceSong N A Z))
 (g:Meringue.{0} P.run p r (180*d) ε ξ C σ θ)
 (pos:0<σ)(c:0≤θ)
 (z:θ*((↑(2*VelourBoard.pitch P.calibration (b+b):ℕ):ℝ)^4) ≤1)
 (wig:P.Wig A p b) (cold:P.NightCop):
 ∀ᶠ s:ℕ in atTop, P.Tonal j s b (P.tuneK h) (4*(Real.exp 1 * σ)):=by
 let T:= plow K j b A
 let W₁ := b+b
 let f:= Q b (P.tuneK h)
 have e:f∈bay K T true:=P.shifts_support j _ _ ((Tapestry.locates ..).mpr (h.1.narrow K).widen)
 have D0:xStart j b j=0:= xStart_zero ..
 have fit:Between K j 0 (ruler P.par.block*↑(b+b)) T:=by
    have v:= wig.spatial j j
    unfold Wall at v
    simpa only [Pi.zero_apply,D0,zero_add,mul_zero,mul_one] using! v
 filter_upwards [feast Y₀ H (xStart j b) g pos c z] with s pay
 let c0:= P.positiveVox j s T f e (fun y t=>(fit y t).1)
 let card:P.Card j s (b+b):=⟨c0,T,(Tapestry.locates ..).mp e,fit⟩

 refine ⟨card, add_pos wig.vol wig.vol,rfl,?_⟩
 refine boardPrice Y₀ H P.law s P.projection j (b+b) (fun _ => f.val) T 
   id tendsto_id (xStart j b) cold (wig.spatial j) D0 _ _ (by positivity) ?_ _ card (P.pallet ((Tapestry.locates ..).mp e))
 unfold Settle
 filter_upwards [P.stockGo.eventually pay,P.stockGo.eventually ((count_la P.run s).eventually a),P.history.finance s] with i pay hx q l L₁ U deck
 obtain ⟨v,V⟩:= pay
 refine V (P.engine i) q f.val _ (P.driftSong j h b i s) (?_) ?_ l L₁ U deck
 · exact ((hx (Vale.val_e ..) _).reflect v j 0).reflect v _ _
 rw [driftBook]
 intro y hy; obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
 exact ⟨x,wig.rural j x hx,rfl⟩



open Lamour.Bridge
open VelourBoard
/-- Uniform purchase `P` is enough: no need to spend more in base
prep even for very bad cost prices or tiny tolerance σ on our song.
Bring Voice and Clarity at that tolerance;
note order σ, song BEFORE b grid budget BEFORE s (eventual). -/
theorem hammockTremor {R:P.Register}{U : Supplier}{e v:ℝ}
 (paid:uniform P R U e v) (cold:P.NightCop) 
 (p0:0∈A)(read:Clarity Z P.par.K.j (σ/4))
 (pos:0<σ):
 ∀ᶠ b:ℕ in atTop,∀ᶠ s:ℕ in atTop, ∀j:Axis,P.Tonal j s b (P.tuneK h) (4*(Real.exp 1 * σ)):=by
 obtain ⟨C,c,C₀⟩:=h.1.rent
 have jp:1≤ν:= by rw [P.par.kJ]; decide
 obtain ⟨a,pc⟩:= paid.1.nerve
 have geo:Geometry P.par:=by
    obtain ⟨_,_,_,_,_,_,g,_⟩:=paid.1.paper
    exact g
 obtain ⟨m',k,V,Y,f₀,g₀,T⟩:=choose_optic jp (180*A.card) c pos
 have oY:=T.zephyr
 obtain ⟨δ,p,s0⟩:= (Filter.Eventually.and 
   (show ∀ᶠ t in 𝓝[>] (0:ℝ),0<t from self_mem_nhdsWithin)
   (P.flickCost h p0 read C₀ oY)).exists
 filter_upwards [P.ready_wig k A] with b R
 let z:=VelourBoard.pitch K (b+b)
 have zs:0<z:=by unfold z VelourBoard.pitch; have hp:0<(K).B.val:=(K).B.property; have hw:=R.vol; positivity
 let θ:= ((↑(2*z:ℕ):ℝ)^4)⁻¹
 have t1:0<θ:= by unfold θ; positivity
 have d1:θ*((↑(2*z:ℕ):ℝ)^4) ≤ 1:= le_of_eq (inv_mul_cancel₀ (by positivity))
 obtain ⟨x,hx,w,h',hX⟩:=choose_floor ν jp (show 0<θ*(8/9) by positivity) oY
 rw [show θ*(8/9)/8=θ/9 by ring] at hX
 have t:Meringue.{0} Y₀ k (breadth 0 A) (180*A.card) Y δ C σ θ:= salon P.run T hx w pc h' hX t1 geo paid.2 p c pos _
 exact Filter.eventually_all.mpr fun j=> P.tremor j h s0 t pos t1.le d1 R cold
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.hammockTremor
