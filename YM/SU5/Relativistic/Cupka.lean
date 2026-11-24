import YM.SU5.Relativistic.Sparkle
import YM.SU5.Relativistic.Sunclad
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
local notation "P" s:max F:max=>stream Y H (fun s=>T s true) s F
local notation "Q"=> G.history
variable (s:ℕ)
local notation "α" => walkV Y H j
local notation "F₀"=> Cabin (tent Y H) j
local notation "κ" u:max=>mirror K j u
local notation "Λ₀"=> Λ.R.L.val
local notation "B₁" s:max=> creed Y H D G d j c x s

open HostLegal MeshClock
local notation "R₁"=> timeMesh Λ
local notation "U"=>flier Y H D G u t d j c x
local notation "W₀" s:max=> Tower.Field Y H s j 0 false
local notation "Ωe"=> doorstep Y H V Q G.clipped j false (c j) (χ j)
local notation "Φ" s:max=> arriving Y H V s Q G.clipped j false (c j) (χ j)
local notation "Υ" s:max=> (U).entry s
local notation "E₁"=> indoor Y H V Q G.clipped j false (c j) (χ j)
local notation "E₂"=> (U).booth
local notation "Δ₀"=> relocate (tent Y H)
local notation "B₀"=> ruler Λ.block
open Germ SelectionAnalysis CF.Pannier.Chancel.ScreeV
local notation "Ms" n:max z:max=> notch (timeMesh Λ) n z
local notation "P₁"=> roadCrew Y H D G u t d j c x
local notation "Ξ₁"=> trueSun Y H D G u t d j c x
local notation "Up₁"=> upCycle Y H D G u t d j c x
local notation "Ξ₀"=> mainsea Y H V Q G.clipped j false (c j) (χ j)
local notation "Γ"=> marks (timeMesh Λ)
local notation "W" s:max k:max=> perroll Y H D G u t d j c x s k
variable {S T':Finset Cover}{v:Bool}{F H':Family (tent Y H)}
local notation "Ctr"=> Vacancy.chart (tent Y H)
noncomputable def promT (L:List (Trans j)) (p:Cover) (v:F₀): Cabin (tent Y H) j:= L.foldr (fun k t=> dwell Y H j k (p k) t) v
lemma promT_eq (L:List (Trans j))(p:Cover)(v:Cabin K j): (promT Y H j L p v).val= cad K (spare j L) p v.val:=by
 induction L with| nil=>rfl|cons a l ih=>exact congrArg (relocate (tent Y H) a.val _) ih
include t
lemma promT_spend (L:List (Trans j))(p:Cover)(v:Cabin K j): (P₁).raw L (fun i=>Ms s (p i.val)) ((Υ s) v)= (Υ s) (promT Y H j L p v):=by
 induction L with
 | nil=>rfl
 | cons a l ih=>
    rw [Alliance.raw_step,ContinuousLinearMap.comp_apply,ih]; let W':= promT Y H j l p v
    change carrU Y H D G u t d j c x a _ ((Υ s) W')=(Υ s) (dwell Y H j a (p a) W'); rw [carr_site]; exact stageWalk Y H D G u t d j c x s a.val a.property W' _
lemma dawn_tramp (p:Cover) (z z':Cabin K j)(h:0 ≤ p j): (Ξ₁).playback (Complex.I • ((Υ s) z)) ((Υ s) z') (fun i=>Ms s (p i)) []=ψ s (mirror K j 0 z.val*(Ctr p z'.val)):=by
 let V':= promT Y H j (look j) p z'; let k:=(p j).toNat; have hk: (k:ℤ)=p j:=Int.toNat_of_nonneg h; let a:=Complex.I; let Hf:= (hutSpec j K z').choose_spec.1
 rw [show Ctr p z'.val=Δ₀ j (p j) (cad K (spare j (look j)) p z'.val) from cad_rank (normal j) Hf p,←promT_eq,show p j=(k:ℤ) from hk.symm] -- rewrites binder lambda? only occurrence right? 
 change inner ℂ (a • _) ((Up₁).E (Real.toNNReal ((Ms s (p j)).val)) ((P₁).raw (look j) (fun i=>Ms s (p i.val)) ((Υ s) z')))=_
 rw [promT_spend,show p j=(k:ℤ) from hk.symm,mark_time, Real.toNNReal_coe,visits Y H D G u t d j c x s k _ (le_refl _),Nat.sub_self,pow_zero,one_mul,inner_smul_left,Tier.arrived]; let T₃:=walkV Y H j k V'; let Z':=mirror K j 0 z.val*T₃.val
 change starRingEnd ℂ a * ψ s (a • Z')= ψ s Z'
 rw [show ψ s (a • Z')=a * ψ s Z' from (audition Y H V G d c _ s).map_smul a (show Dome K from ⟨_,levied j K z T₃⟩)]
 unfold a; simp [← mul_assoc]
-- chart cost on raw for every higher n. define for odd and even alike.
structure Faze (v:Bool)(X Y':Family (tent Y H)){W₀':Hilbert} (Pk:Sunbelt j (marks R₁) W₀')(x' y:W₀') : Prop where -- P notation p error
 usher {r:ℕ} (h:s≤r)(p:Cover)(q: 0≤p j):
    Pk.playback x' y (fun i:Axis=>notch (timeMesh Λ) r (p i)) []= ψ r (stream Y H (fun s=>T s v) s (r-s) X*Ctr p (stream Y H (fun s=>T s v) s (r-s) Y'))
local notation "Haya" b:max=> Faze Y H D G (T:=T) d j c x s b
-- Pose xy representing X,Y at center. Faze irrespective v
variable {A:ℤ}
lemma roll_cur (p:InTest K true S v F)(q:InTest K true T' v H'){k:ℕ}(L:Cover)(z:ℤ) :
    ψ k (stream Y H (fun s=>T s v) s (k-s) (Δ₀ j z F)* Ctr L (stream Y H (fun s=>T s v) s (k-s) (Δ₀ j z H')))=ψ k (stream Y H (fun s=>T s v) s (k-s) F*Ctr L (stream Y H (fun s=>T s v) s (k-s) H')):=by
 rw [grade_ho Y H D G u t j s p,grade_ho Y H D G u t j s q]
 let W':=(Λ₀:ℤ)^(k-s)*z; unfold Vacancy.chart
 let hg:=t.allSupport Y H V Q u s (k-s) q; let hv:=t.allSupport Y H V Q u s (k-s) p
 have hu:=(hv.mono (subset_union_left (s₂:= drivePlot L K ordinate (volumeAround Λ l (k-s) T')))).mul ((tour_test L ordinate hg).mono subset_union_right); rw [Bool.xor_self] at hu
 rw [posedC ordinate j hg,←relocate_mul]; exact elect_slide Y H V G j d c _ (aux_test hu) (2*W') k
lemma early_faze (p:InTest K true S true F)(q:InTest K true T' true H'){x' y:Cabin K j}(X:mirror K j 0 x'.val= Δ₀ j A F)(z:y.val= Δ₀ j A H'): (Haya true) F H' (Ξ₁) (Complex.I • (Υ s) x') ((Υ s) y):=by
 constructor; intro k r d₀ pS
 rw [←Tier.increase _ r,←Tier.increase _ r] -- dbl occurrence? tune
 rw [dawn_tramp Y H D G u t d j c x k _ _ _ pS]
 let W₁:= k-s; change ψ k (mirror K j 0 ((P s W₁) x'.val)*Ctr d₀ ((P s W₁) y.val))=_
 have ht:= t.allTurning Y H V Q _ s W₁ (hutSpec j K x').choose_spec.1 j 0; rw [planeAt,mul_zero] at ht; rw [← ht,X,z]; exact roll_cur Y H D G u t d j c x s p q d₀ A
lemma meadowry (p:InTest K true S false F)(q:InTest K true T' false H'){x' y:Tower.Field Y H s j 0 false}(X:mirror K j 0 x'.val= Δ₀ j A F)(z:y.val= Δ₀ j A H'): (Haya false) F H' (Ξ₀) ((Φ s) x') ((Φ s) y):=by
 constructor; intro k r d₀ pS
 let χ':= χ j
 change Visits Y H V s Q G.clipped j false (c j) χ' x' y (fun i=>Ms k (d₀ i))=_
 have h:uptown j (fun i=> notch (timeMesh Λ) k (d₀ i)):= by have he : (notch R₁ k 0).val ≤ (notch R₁ k (d₀ j)).val:=(stamp_le R₁ k _ _).2 pS; rw [notch_zero] at he; exact he -- need notch_zero
 rw [visits_higher Y H V s Q G.clipped j false (c j) _ x' y _ h k r d₀ (fun _=>rfl)]; unfold χ'; rw [selected_here Y H D G d j c x k]; change ψ k (stream Y H G.refine s (k-s) (mirror K j 0 x'.val)* (relocateWorld Y H false d₀ _).val)=_
 rw [world_val]; change ψ k (stream Y H G.refine s (k-s) (mirror K j 0 x'.val)* Ctr d₀ (stream Y H G.refine s (k-s) y.val))=_
 rw [X,z,← t.originally Y H V Q u s (k-s) (aux_test (froll j p A)), ←t.originally Y H V Q u s (k-s) (aux_test (froll j q A))]; exact roll_cur Y H D G u t d j c x s p q d₀ A
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.early_faze
