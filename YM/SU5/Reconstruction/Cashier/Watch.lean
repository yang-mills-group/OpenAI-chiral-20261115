import YM.SU5.Reconstruction.Cashier.Receivables
import YM.SU5.Reconstruction.Cashier.Addition
import YM.SU5.Selected.Parish
/-!
# Coherent path adjusted and payment by Board along it.
Keep Fashion etc afterward as appropriate. Give specifically actual test from
Korn itself and both unaveraged and averaged expressions suspending along UV
histories (not changing those). Works all s suff. large with this grid-lock pricing.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock _root_.YM.Analysis
open Tapestry
open SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {S:Finset Cover}{w:ℕ}
variable (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "π" r:max=>i (G.rows r)
local notation "ζ" r:max=> k (G.columns r)
local notation "Z" u:max r:max f:max=> train Y H s u (π r) (ζ r) S f
local notation "W" t:max=> volumeAround Λ l t S
local notation "uM" t:max=> (L₀^t*w)
local notation "b₀"=>ruler Λ.block
open CF.Pannier.Chancel
section schedule
variable (d q u:ℕ)
local notation "Φ"=>payout d q u
local notation "ρ"=>grain (payout d q u)
local notation "Ψ"=>Sen ρ Φ
structure Matching (j b:ℕ)(z:SU.Slot)(F: Family (tent Y H)): Prop where
 transcription : ∃ f:Family (tent Y H), f∈ Filigree (tent Y H) (Window.family z) (booty (grain (payout d q u)) d q) (Sen (grain (payout d q u)) (payout d q u)) ∧ F=f+1
 note : exhibit Y H s j F = (Papal.taggin Y s j b q d u (ρ) z).frame
 public_ : ∃ (f: Vacancy.observable (tent Y H) true), f.val∈ Filigree (tent Y H) (Window.family z) (booty (grain (payout d q u)) d q) (Sen (grain (payout d q u)) (payout d q u)) ∧
      exhibit Y H s j f.val = Papal.aliquot Y s j b q d u (grain (payout d q u)) z
structure Attendance (w:ℕ)(C:ℝ)(j b:ℕ) : Prop where
 receipt:Papal.Consumes Y H C q d u w s j b
 format:Roomy (Sen (grain (payout d q u)) (payout d q u)) (Papal.count Y s j)
 crew : ∀ z:SU.Slot,∃ F,Matching Y H s d q u j b z F
-- care variable order d q u; Korn uses q d w etc
variable {u q d}
variable {C A:ℝ} (P:Papal.Cellarer Y H C A q d u w)
section quest
include P
lemma guide : ∀ᶠ s in atTop,∀ᶠ e in atTop,∀ᶠ f in atTop, Attendance Y H s d q u w C e f:= by
 filter_upwards [P.company,P.here,P.pairs] with s t u0 b
 filter_upwards [t,u0 ρ,b, Tapestry.roomyTail Y H s Ψ] with i t u b q
 filter_upwards [t,u,b] with k t u b
 refine ⟨t,q,fun z=>?_⟩; obtain ⟨a,F,f,h⟩:= b z; obtain ⟨q,hp,T',X,Y0,Z₁,g,lg,ph,he,v⟩:=u z
 refine ⟨F+1,⟨F,f,rfl⟩,?_,⟨⟨g,?_⟩,lg,he⟩⟩ -- tune subtype
 · rw [actual_add,h,actual_one,sub_add_cancel]
 exact ⟨aux_test (FilTest lg).widen,fun _=>ph⟩
include V
lemma purchasing : ∃ G:GroundExtension (i:=i) (k:=k) (E:=E) Y H,∀ᶠ s in atTop,∀ᶠ e in atTop,
    Attendance Y H s d q u w C ((i∘ G.rows) e) ((k∘G.columns) e):=by
 let D(a b:ℕ):Prop:=∀ s≤a, (∀ᶠ i' in atTop,Attendance Y H s d q u w C a i') → Attendance Y H s d q u w C a b
 have he(a:ℕ):∀ᶠ b in atTop,D a b:=by
    have ht(s:ℕ):∀ᶠ b in atTop,(∀ᶠ i' in atTop,Attendance Y H s d q u w C a i') → Attendance Y H s d q u w C a b:=by
        by_cases p:(∀ᶠ i' in atTop,Attendance Y H s d q u w C a i'); exact p.mono fun b u _=>u
        exact Eventually.of_forall fun b h=> (p h).elim
    exact ((eventually_all_finset (Iic a)).mpr fun s _=>ht s).mono fun b g s u=> g s (mem_Iic.mpr u)
 obtain ⟨r,Q⟩:= purchase_line Y H V
 obtain ⟨G,h⟩:= grant_more Y H V Q D he; refine ⟨G,?_⟩
 let j:=i∘G.rows; have ht:Tendsto j atTop atTop:=(V.pick.grow_i.comp G.history.growsA).tendsto_atTop
 filter_upwards [guide Y H P] with s e
 exact ((ht.eventually_ge_atTop s).and (ht.eventually e)).mono fun n p=> h n s p.1 p.2
end quest
end schedule
/-- Uniform width estimate on these lines delivered on sharp histories along fixed coherent path. -/
def Rolls (F:ℕ→Family (tent Y H))(w:ℕ) : Prop := ∀ j:Axis,∀ᶠ e:ℕ in atTop,∀ n:ℕ,∀ v:ℤ,
 0<n→2*(b₀*w*n) ≤ (((Journey.side Y (π e) s).val:ℕ):ℤ)→ (((Journey.side Y (π e) s).val:ℕ):ℤ) ≤ (4*(b₀*w*n))→
 ‖sharp Y H s (π e) (ζ e) (banner j w v n (F e))‖ ≤ Real.exp (-3000*(n:ℝ)) -- need Type annotation implicit $ss
section schedule
variable {d q u:ℕ}{C A:ℝ}
local notation "Φ"=>payout d q u
local notation "ρ"=>grain (payout d q u)
local notation "Ψ"=>Sen ρ Φ
local notation "Rx"=>Tapestry.render Ψ (tent Y H)
lemma enlist {z:SU.Slot} {j b:ℕ} {F:Family (tent Y H)} (x:Matching Y H s d q u j b z F) {w:ℕ}
 (t:Attendance Y H s d q u w C j b) : ∃ u:Swatch (Sen (grain (payout d q u)) (payout d q u)), ‖u‖≤C∧F= render _ (tent Y H) u := by -- shadow u
 obtain ⟨f,h,rfl⟩:= x.transcription; obtain ⟨v,e⟩:= rendered Ψ K (InTest.add (FilTest h |>.widen) InTest.one)
 have hv : present Y H s j Ψ v= _:= (present_exhibit Y H s j Ψ v).trans ((congrArg (exhibit Y H s j) e).trans x.note) -- order
 exact ⟨v,present_sample Y H s j Ψ t.format.seats v (fun y=>by rw [hv]; exact (t.receipt.offers z).1 y),e.symm⟩

lemma rolls_of {u':ℕ→ Swatch (Sen (grain (payout d q u)) (payout d q u))} {z:SU.Slot}
 (h:∀ᶠ e in atTop, Attendance Y H s d q u w C (π e) (ζ e))
 (p:∀ᶠ e in atTop, Matching Y H s d q u (π e) (ζ e) z ((Rx) (u' e))) :
 Rolls Y H s G (fun i=> (Rx) (u' i)) w:= by
 intro j; filter_upwards [h,p] with i h p n v _ he hw
 apply (h.receipt.offers z).2 _ n v j p.note
 · change 2*(16*Λ.block.val)*w*n ≤ _
   unfold ruler at he
   change _ ≤ (↑(Papal.count Y s (π i)).val:ℤ) at he
   exact_mod_cast (le_trans (show _ ≤ _ from (show (2*(16*(Λ.block.val:ℤ))*w*n:ℤ) ≤ 2*(16*(Λ.block.val:ℤ)*w*n) from le_of_eq (by ring))) he)
 change _ ≤ 4*(16*Λ.block.val)*w*n; unfold ruler at hw; change (↑(Papal.count Y s (π i)).val:ℤ) ≤ _ at hw
 exact_mod_cast (hw.trans_eq (show 4*((16:ℤ)*Λ.block.val*w*n)=4*(16*(Λ.block.val:ℤ))*w*n from by ring))

lemma equip {z:SU.Slot} (v:0≤ C)(h:∀ᶠ e in atTop, Attendance Y H s d q u w C (π e) (ζ e)) : ∃ f:ℕ→ Swatch (Sen (grain (payout d q u)) (payout d q u)),
  (∀ i,‖f i‖≤C)∧Rolls Y H s G (fun i=> (Rx) (f i)) w ∧ ∀ᶠ e in atTop, Matching Y H s d q u (π e) (ζ e) z ((Rx) (f e)):=by
 let P(e:ℕ):=Matching Y H s d q u (π e) (ζ e) z
 let p(e:ℕ):=Attendance Y H s d q u w C (π e) (ζ e)
 classical
 have ht (e:ℕ):∃ x:Swatch Ψ, ‖x‖≤C∧(p e→P e ((Rx) x)):=by
    by_cases g:p e
    · obtain ⟨F,hx⟩:=g.crew z; obtain ⟨i,q,rfl⟩:= enlist Y H s hx g; exact ⟨i,q,fun _=>hx⟩
    exact ⟨0,(by simpa),fun h=>(g h).elim⟩
 choose f a b using ht; have q:= h.mono fun i k=> b i k
 exact ⟨f,a,rolls_of Y H s G h q,q⟩
end schedule
end YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll.purchasing
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll.equip
