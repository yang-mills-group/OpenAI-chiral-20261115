import YM.SU5.Relativistic.ApexBill
import YM.SU5.Relativistic.StringWeights
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
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
local notation "D₀"=> Dome (tent Y H)
local notation "Ξ"=> Cloud (Dome (tent Y H))
local notation "φ" n:max => response Y H V n G.history G.clipped j false (c j) (χ j)
local notation "PP" s:max F:max=>stream Y H (fun s=>T s true) s F
local notation "Q"=> G.history

variable {s n:ℕ}
local notation "μ" z:max=> gaugeShift Λ.block z
local notation "E₀" s:max f:max=> Lariat.rideL Y H T s f


open Lariat
section weights
variable (M:Panel Y H D.univ_ G.history G.clipped d false (c d)) (y:M.X)

variable (A:∀ i:ℕ, Future Y H d i)(w:ℕ→ℕ) (p: Subscribed Y H D G d c M y u T A w)
open Lariat
local notation "I₁" i:max=>a (G.rows (u (w i)))
local notation "K₁" i:max=>b (G.columns (u (w i)))
local notation "F₀" i:max=> (Future.kernelPath Y H d (A i)).val
local notation "Y'" i:max=>(A i).t
local notation "Φ" i:max=> sharp Y H (Y' i) (I₁ i) (K₁ i) (Future.kernelPath Y H d (A i)).val
local notation "R₀" s:max=>appeal Y H D G d c (M.character y) T s


-- place at same top, keep DISTINCT footprint to every height
include t p
-- inputs may not yet be at native cutoff. For simultaneous application, keep q path and guarantees even when n rescales. Charge of term represented by detached product in μ.
lemma actualWeights (s:ℕ)(f:Lariat K n) :∀ᶠ i:ℕ in atTop, let r:= (A i).t; let Tβ:=s+(n+(r-(s+n+1))+1);let g':=Lariat.parcel Y H d (A i) s f; let g:= priceAt Y H s (I₁ i) (K₁ i) g'; let l':= Future.opening Y H d (A i)∪Future.closing Y H d (A i); let W:= Lariat.box Λ l f; let S:=volumeAround Λ l (Tβ-(s+n)) W; let m:=Y.uv (K₁ i); let Vτ:=volumeAround Λ l (m-Tβ); let H₀:=side Y (I₁ i) m; let P:=distribute Y H m (I₁ i);let L:= sharp Y H Tβ (I₁ i) (K₁ i) g;let K0:=Φ i
          -- calibrated and no alias selected detector
          r=Tβ ∧ s+n < r ∧ Tβ ≤ m ∧ (Y.voyage (I₁ i)).kick ≤ K₁ i ∧ Disjoint (footprint Λ l (s+n) W) (footprint Λ l Tβ l') ∧ Host Y H (I₁ i) Tβ (S∪l') ∧ K0≠0 ∧
          ∃ (Q0:Mark H₀) (Q1:Family (tent Y H)), AtSupport f.hue (Satin.region (Vτ S) H₀) Q0 ∧ InTest (tent Y H) true (Vτ l') false Q1 ∧
              K0=sharp Y H m (I₁ i) (K₁ i) Q1 ∧ microscope Y (I₁ i) (K₁ i) 1≠0 ∧ microscope Y (I₁ i) (K₁ i) (P Q1)≠0 ∧ L/K0= microscope Y (I₁ i) (K₁ i) (Q0*P Q1)/microscope Y (I₁ i) (K₁ i) (P Q1):=by
 let W:=Lariat.box Λ l f; let F:=footprint Λ l (s+n) W
 filter_upwards [p.calibrated n s f,(pieceSame Y H D G u t d c M y A w p).eventually_ne one_ne_zero,eventually_sans Λ F d (footprint_compact _ _ _ _)] with i ⟨r,X,q,v',p0⟩ v₀ k0
 intro k τ g' g l' S0 S m V' H' P' L' K0
 let k':=k-(s+n+1); have hp:τ=k:=by unfold τ k at *; omega
 let X':=padTop f k'; have e:g'=stretch X' (counter Y H d (A i)):= rfl
 have h:footprint Λ l τ S⊆ F:=by
    have ht: τ =s+n+(τ-(s+n)):=by change s+n < k at r; omega
   
    change footprint Λ l τ _ ⊆ _; let z:=τ-(s+n); exact Eq.mpr (congrArg (fun i=> footprint Λ l i S ⊆ F) ht) (covers_footprint ..)
 have hi: Disjoint F (footprint Λ l τ l'):=by
    have z:= Future.labels_far Y H d (A i); unfold l'; rw [potential_union,hp]; exact Disjoint.mono_right (Set.union_subset_union z.1 z.2) k0
 have e₀: S=wingspan Λ l (Lariat.box Λ l X'):=by
    unfold X'; rw [pad_box]; unfold S S0
    have he: τ - (s+n)=k'+1:=by unfold k'; omega
    rw [he]; rfl
 let P₀:= I₁ i; let V₀:= K₁ i
 have e₁: (counter Y H d (A i)).S=l':= Finset.union_comm ..
 have hg:Lariat.box Λ l g'=S∪l':= by rw [e, Lariat.box, e₀, e₁]
 let l₁:= τ - (s+n)
 let D':=S∪l'
 have hG:Host Y H P₀ τ D':=by
    have h:(g').Costs X:=p0
    change Host Y H _ _ (S∪l'); rw [←hg,Lariat.hires (Λ:=Λ) (l:=l) _ X h]; exact (v' (n+(k-(s+n+1))+1) le_rfl).1
 have he:= q.1; have hy:τ ≤ m:=q.2; let y:=m-τ; have h0:τ+y=m:=by omega
 -- split actual polynomial pricing at Tβ, exactly, no support ind assumptions except already dues for full weights
 let Y0:= moveUp Y H (s+(n+k')) P₀ V₀ (Lariat.box Λ l X') (hue X') (priceAt Y H s P₀ V₀ X'); let Z:Family K:=F₀ i
 have hw:g=Y0*Z:=rfl
 have hs:hue X'=f.hue:=padHue k' f
 have ht0:InTest K true S f.hue Y0:=by rw [e₀,←hs]; exact stay ..
 have hz:InTest K true l' false Z:= e₁ ▸ (Lariat.counter Y H d (A i)).bill
 let X0:=apex Y H P₀ V₀ τ f.hue Y0 S y; let Z0:=apex Y H P₀ V₀ τ false Z l' y
 have Hv:Detached Λ l S l':=separated_in_foot _ _ _ _ _ (Disjoint.mono_left h hi)
 have hR: X0*Z0 = apex Y H P₀ V₀ τ (f.hue.xor false) (Y0*Z) D' y:= (apex_pair Y H P₀ V₀ τ S l' Hv hG ht0 hz y ⟨he,h0.le⟩).symm
 obtain ⟨q1,r1⟩:= apexLaw Y H P₀ V₀ τ S (Host.shrink Y H subset_union_left hG) ht0 y ⟨he,h0.le⟩
 obtain ⟨q2,r2⟩:= apexLaw Y H P₀ V₀ τ l' (Host.shrink Y H subset_union_right hG) hz y ⟨he,h0.le⟩
 have q1':InTest K true (V' S) f.hue X0:=q1; have q2':InTest K true (V' l') false Z0:=q2
 have hZ0:K0=sharp Y H m P₀ V₀ Z0:=by
    change sharp Y H k P₀ V₀ Z= _; rw [←hp]; exact r2.symm.trans (congrArg (fun i=>sharp Y H i P₀ V₀ Z0) h0)
 have hX: sharp Y H m P₀ V₀ (X0*Z0) = L':=by rw [hR, ← h0]; exact (apexLaw Y H P₀ V₀ τ D' hG ((ht0.mono subset_union_left).mul (hz.mono subset_union_right)) y ⟨he,h0.le⟩).2 -- hw defeq
 have vh:K0=microscope Y P₀ V₀ (P' Z0)/microscope Y P₀ V₀ 1:= hZ0.trans (topLens Y H _ _ q2' he)
 have h':L'=microscope Y P₀ V₀ (P' X0*P' Z0)/microscope Y P₀ V₀ 1:=by
    rw [←hX]; change Journey.compass Y P₀ V₀ m (distribute Y H m P₀ _) = _; rw [(distribute_arith Y H m _ X0 Z0 0).2.1]; unfold Journey.compass; rw [(same_denominator Y m P₀ V₀ he le_rfl).1]; exact congrArg (fun z:ℂ=> z/ microscope Y P₀ V₀ 1) (onePrior Y P₀ V₀ (P' X0 * P' Z0) (env_mult (parked Y H m P₀ _ q1').env (parked Y H m P₀ _ q2').env) he).2
 let hq:= (same_denominator Y m P₀ V₀ he le_rfl).2
 have v1:microscope Y P₀ V₀ (P' Z0)≠0:= fun z=> v₀ (vh.trans (by rw [z,zero_div]))
 refine ⟨hp.symm,r,hy,he,hi,hG,v₀,P' X0,Z0,parked Y H m _ _ q1', q2', hZ0,hq,v1,?_⟩
 rw [vh,h']; change _ = microscope Y P₀ V₀ (P' X0*P' Z0) /microscope Y P₀ V₀ (P' Z0); field_simp
end weights

end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
