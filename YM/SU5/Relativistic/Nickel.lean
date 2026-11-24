import YM.SU5.Relativistic.Thunder
import YM.SU5.Relativistic.ActualWeights
import YM.SU5.Relativistic.TrueSeparation
/-!
# Wedges physically: one aperture.

This includes genuine persistence of offdiag excitation in the multiresolution
field problem. This is propagation about the USEFUL contour, not Fort speed. 
-/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
open CF.Pannier.Chancel.ScreeV Crest.Sleet Crest.Sleet.UpStart FermionSlab
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}
    (D : Exhibition Y H a b I E L B)
local notation "V"=>D.univ_
variable (G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (u:ℕ→ℕ) {T:ℕ→Bool→Family (tent Y H)→Family (tent Y H)}(t:GradesAll (i:=a) (a:=G.rows) (k:=b) (b:=G.columns) Y H u T)
variable (d j:Axis) (c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (x:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ)
local notation "χ" i:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) x i (c i)
local notation "ψ"=>evaluate Y H D.univ_ G d c (SameCharacter.resident Y H D.univ_ G d false (c d) x)
local notation "P" s:max v:max=>stream Y H (fun s=>T s v) s
local notation "Q"=> G.history
variable (s n:ℕ)
-- physical separation matches true chiral budgets, not merely center pins
lemma regionGap {S W:Finset Cover}(z:ℤ)(A:ℕ)(h: Till K A j z S W)(x y:RSpace)(a:x∈ footprint Λ l s S)(t:y∈ footprint Λ l s W) : x j + (2:ℝ)*A*gaugeMesh Λ s ≤ y j:=by
 obtain ⟨i,hp⟩:= Set.mem_iUnion.mp a; obtain ⟨hx,p⟩:= Set.mem_iUnion.mp hp; obtain ⟨b,u⟩:= Set.mem_iUnion.mp t; obtain ⟨hw,v⟩:= Set.mem_iUnion.mp u; let f:=reserve Λ l; have hx':= (p : x∈collar Λ l s i).2 j; have he:= (v:y∈collar Λ l s b).1 j
 rw [upper_gauge] at hx'; rw [lower_gauge] at he
 have hv:= h.stay i hx; have ht:=h.start b hw; change _+ (f:ℤ)+_ ≤ _ at hv; change _+(f:ℤ)+_≤_ at ht; have hV: i j+(2:ℤ)*f+2*A ≤ b j:=by omega
 have hF: (i j:ℝ)+2*f+(2:ℝ)*A ≤ b j:=by exact_mod_cast hV
 unfold gaugePosition at he hx'; unfold f at hF; nlinarith only [mul_le_mul_of_nonneg_right hF (gaugeMesh_pos Λ s).le,he,hx']
include s in
lemma till_phys {S W:Finset Cover}(z:ℤ){A:ℕ}(p:0<A)(h:Till K A j z S W) : Detached Λ l S W:= by
 apply separated_in_foot Λ l s S W; apply Set.disjoint_left.mpr; intro i t g
 have hp:= regionGap Y H j s z A h i i t g; linarith [show 0<(2:ℝ)*A*gaugeMesh Λ s by have ht:= gaugeMesh_pos Λ s; positivity]

-- selected and Euclidean values via **literal** Grade extensions
namespace Pays5
local notation "Ψ" n:max v:max=>Lariat.discount ψ v n
variable {p q:Finset Cover}{F:Family (tent Y H)} {Y':Family (tent Y H)} {v:Bool}(h:InTest (tent Y H) false p v F)(f:InTest (tent Y H) false q v Y')
include D G t h
lemma northern : (Ψ (s+n) v) ((P s v) n F)= (Ψ s v) F:=by
 unfold Lariat.discount; cases v; swap; · simp
 rw [t.originally Y H D.univ_ G.history u s n (aux_test h.widen)]; exact elect_refine Y H V G d c (SameCharacter.resident Y H V G d false (c d) x) (aux_test h.widen) s n
include f
lemma requires_wedge (z:ℤ){A:ℕ}(e:0<A)(l': Till K A j z p q) (r:ℝ)
    (P': r≤ ‖ψ s (F*Y')- Lariat.discount (ψ) v s F* Lariat.discount (ψ) v s Y'‖):
    r≤ ‖ψ (s+n) ((P s v) n F*(P s v) n Y')- (Ψ (s+n) v) ((P s v) n F)* (Ψ (s+n) v) ((P s v) n Y')‖:=by
 have hV:TestFamily K true (F*Y'):=by apply aux_test (_ : InTest K true (p∪q) false (F*Y')); exact (Bool.xor_self v) ▸ (h.widen.mono subset_union_left).mul (f.widen.mono (subset_union_right (s₁:=p)))
 rw [northern Y H D G u t d c x s n h,northern Y H D G u t d c x s n f,← t.allCrossing Y H V Q u s n h.widen f.widen (till_phys Y H j s z e l'),Bool.xor_self, t.originally Y H V Q u s n (x:=F*Y') hV] -- arg implicit x
 rw [elect_refine _ _ _ _ _ _ _ hV]; exact P'

end Pays5
variable (W U:Finset Cover)(F Y':Family (tent Y H)) (v:Bool)
structure FundX (z:ℤ)(N:ℕ):Prop where
 gap:Till K N j z W U
 input:InTest K false W v F
 certified:InTest K false U v Y'
 gauge:Neutral K F ∧ Neutral K Y'
 physical(x y:RSpace)(h:x∈ footprint Λ l s W)(p:y∈ footprint Λ l s U):
    x j + 2*N*gaugeMesh Λ s≤ y j
 uplift (n:ℕ) :
    let P' := (P s v) n F; let Q':= (P s v) n Y';
    Neutral K P' ∧ Neutral K Q' ∧ (∃ X:Finset Cover, SupportedPhysically Λ l (s+n) X (footprint Λ l s W) ∧ InTest K true X v P') ∧ (∃ X:Finset Cover,SupportedPhysically Λ l (s+n) X (footprint Λ l s U) ∧ InTest K true X v Q')
 nonfactorCoordinate : ∃ r:ℝ,0<r ∧ ∀ n:ℕ,
     r≤ ‖ψ (s+n) ((P s v) n F*(P s v) n Y')- Lariat.discount ψ v (s+n) ((P s v) n F)*Lariat.discount ψ v (s+n) ((P s v) n Y')‖

-- useful API compilation from hopeful Stout opened. Reuse registration with ACTUAL apertures
include t
lemma at_this_character (J:Fin 3)(M q w:ℕ)(F:Waxy)(i:Finset ℤ)(x':∀ a∈ plusHalf,∀ t:ℤ,t∉i→ F a t=0)(r:ℕ)(e:0<r)(p:Stout K M q w F J r i ((ψ) s)):
   ∃ (W W':List (XGr M))(S:Finset Cover)(j:Axis)(Q':Buffered.Family K)(z:ℤ), W≠[] ∧ W'≠[] ∧ IsBay K M q w F J i W' Q' S ∧ FundX Y H D G d j c x s (T:=T) (floorline M w q W) S (rolls (Toes M q w K J) W) Q' (stripeP W.length) z r:=by
 obtain ⟨Z,V',X,S,j,z,nZ,nV,_,_,hp,p',t',u'⟩:= p.isStout
 let G₁:= floorline M w q Z; let v:= stripeP Z.length; let K₁:= rolls (Toes M q w K J) Z; have hx:InTest K false G₁ v K₁:= topsB J K M q w _
 have he: Lariat.discount ψ v s K₁= CF.Pannier.Chancel.ScreeV.price (ψ s) v K₁:= rfl
 have hv: InTest K false S v X ∧ Neutral K X:= by unfold v; rw [hp]; cases p' with
   | out h k=> rw [h,k]; exact ⟨wingB F J K M q w i x' V', honestL _ _ (fun i=>glebe_N (tent Y H) _ _ F w J)⟩
   | foot h k=> rw [h,k]; exact ⟨topsB J K M q w _,honestL _ _ (fun i=> gyre_N (tent Y H) _ J)⟩
 have hU:Neutral K K₁:= honestL _ _ (fun i=>gyre_N (tent Y H) _ J)
 let R:= ‖ψ s (K₁ * X)-Lariat.discount ψ v s K₁*Lariat.discount ψ v s X‖
 refine ⟨Z,V',S,j,X,z,nZ,nV,p', t',hx,hv.1,⟨hU,hv.2⟩,fun i z' e h=>regionGap Y H j s z r t' _ _ e h,fun n=> ⟨t.neutrally Y H V Q _ s n hx.widen hU,t.neutrally Y H V Q _ s n hv.1.widen hv.2,⟨_,(has_footprint Λ l s G₁).persists n,t.allSupport Y H V Q _ s n hx.widen⟩,⟨_,(has_footprint Λ l s S).persists n,t.allSupport Y H V Q _ s n hv.1.widen⟩⟩,R,?_,fun n=>Pays5.requires_wedge Y H D G _ t d j c x s n hx hv.1 z e t' R le_rfl⟩
 apply norm_pos_iff.mpr; apply sub_ne_zero.mpr
 change ψ s (K₁*X) ≠ CF.Pannier.Chancel.ScreeV.price (ψ s) v K₁ * CF.Pannier.Chancel.ScreeV.price (ψ s) v X
 change ψ s (K₁*X) ≠ CF.Pannier.Chancel.ScreeV.price _ v K₁ * CF.Pannier.Chancel.ScreeV.price _ (stripeP V'.length) X at u'; rw [←hp] at u'; exact u'
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.at_this_character
