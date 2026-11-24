import YM.SU5.Selected.Apart
/-!
# Local Euclidean translation covariance on visible meshes

Translation of arbitrary supported polynomials by available motions at their
levels. Scalar units are Level0 matter lattice; available translations here
by 2*z steps of matter lattice of a level s (4*z gauge); all fine levels of
same physical shift are then affordable. Terms explicitly billed to coarser
levels aren't yet asserted to move by that same ℝ-displacement (grid mismatch);
all OUR uses of e.g. finer-grid semantics must be justified separately: usually
by treating the whole polynomial coarsened at a permitted finer level to *one*
mark there and translating this version. Coincidence distinctions apply still,
at arbitrarily fine but FINITE pitch (see Apart). No representation for a real
group or direct random field claimed. Input caution continuous change-of-axes.
For Sturm know lattice region semantics, gauge and state preserved. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
open Set Theory MeshClock Tapestry Tapestry.Altitude Tapestry.Exhibition
variable {L:Rack Λ l}{B:Clay Λ l}(D:Exhibition Y H i k I E L B)
local notation "χ₀"=>Dome (tent Y H)
local notation "Cₚ"=>Cloud (Dome (tent Y H))
local notation "F₀"=>vistaDressing Y H D
local notation "P₀" n:max=>vistaFinish Y H n D
local notation "D₀" n:max=> Exhibition.liftD Y H n D
variable (d:Axis)(T:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
local notation "R"=>catalog Y H V G d false (T d)

variable (x:Resident (catalog Y H V G d false (T d)))
local notation "Mx"=>evaluate Y H V G d T x
local notation "Θ"=> onDrawing Y H V G D d T x

section displacement
variable (W:Calibration) (z:ℤ)
noncomputable def cruise : Dome W →ₐ[ℂ] Dome W := AlgHom.ofLinearMap ((aureole W j z).comp (aureole W j 0)) (by rw [LinearMap.comp_apply,aureoleUnit,aureoleUnit]) fun i t=>by simp_rw [LinearMap.comp_apply, aureoleProduct]
local notation "μ" z:max=>cruise j W z -- order j W
lemma sailsTo (x: Dome W): ((μ z) x).val= chime W j z x.val:=rfl
lemma sailsBy (a:ℤ)(x:Dome W): (μ z) ((μ a) x)=(μ (z+a)) x:= Subtype.ext (Tower.bumps W j z a ((marque ..).1 x.property).paid.choose_spec)
lemma sailsBack (x:Dome W): (μ 0) x=x:=Subtype.ext (Tower.wake W j ((marque ..).1 x.property).paid.choose_spec)

-- RSpace simple slides
noncomputable def glint (Λ:Preparation) (s:ℕ) (x:ℤ):ℝ:= (x:ℝ)/Tapestry.precisionAt Λ s -- matter units
noncomputable def steer (i:ℝ) (x:RSpace):RSpace:=fun a=> if a=j then x a+i else x a
local notation "δ"=>steer j
lemma about (Λ:Preparation)(s:ℕ)(a:ℤ)(x:RSpace) : δ (2*glint Λ s a) x = mirrorE j (markZ Λ s a) (mirrorE j 0 x):= by
  funext i; unfold steer mirrorE; split
  · unfold markZ glint; ring
  rfl
lemma steer_sum (a b:ℝ)(x:RSpace):δ a (δ b x)=δ (a+b) x:=by funext i; unfold steer; split; ring; rfl
lemma steer0 (x:RSpace):δ 0 x=x:=by funext i; unfold steer; split; ring; rfl

variable (Λ:Preparation)(l s r:ℕ) (V': Set RSpace)
local notation "Ω"=>handstamp V'
local notation "θ" z:max=>glint Λ s z
lemma sti (a:ℝ) : δ (2*a) '' handstamp V'=handstamp (δ a '' V'):=by
  set T:=(fun z:RSpace=>fun i:Axis=> z i/2)
  have he(a:ℝ)(x): T (δ (2*a) x)=δ a (T x):=by funext i; by_cases h:i=j <;> simp [steer,T,h]; ring
  ext x; constructor
  · rintro ⟨p,t,rfl⟩; exact ⟨T p,t,(he a p).symm⟩
  rintro ⟨v,p,(t:δ a v=T x)⟩; let y:=δ (2*(-a)) x; have h:T y=v:=by unfold y; rw [he,←t,steer_sum,neg_add_cancel,steer0]
  exact ⟨y,(show T y∈V' from h.symm ▸ p),(by unfold y; rw [steer_sum,←mul_add,add_neg_cancel,mul_zero,steer0])⟩
-- need clearance; motion from s to finer t.
lemma glintRef (h:s≤r) : glint Λ r (smill Λ s r z)= glint Λ s z:=by
  unfold glint smill Tapestry.precisionAt; push_cast
  have ht: (Λ.R.L.val:ℝ) ≠0:=by exact_mod_cast Λ.R.L.property.ne'
  field_simp; rw [show (Λ.R.L.val:ℝ)^r=(Λ.R.L.val:ℝ)^s*(Λ.R.L.val:ℝ)^(r-s) by rw [←pow_add,Nat.add_sub_of_le h]]; ring -- tune
lemma hand_steer {x:Dome W}{wide:Bool} (p:x∈ keep Λ l s W wide Ω): (μ z) x ∈ keep Λ l s W wide (handstamp (δ (θ z) '' V')):=by
  rw [← sti j V']; change (μ z) x ∈ keep Λ l s W wide (steer j _ '' Ω); rw [show δ _= mirrorE j (markZ Λ s z) ∘ mirrorE j 0 from funext (about j Λ s z),Set.image_comp]; -- funext theorem LHS eq to Fun.comp?
  have h:=facingBay Λ l W wide (z:=0) (α:=j) p; rw [show markZ Λ s 0=0 by simp [markZ]] at h; exact facingBay Λ l W wide h -- reflect0 markZ = 0 tune
lemma glintGauge (g: GPhysical)(u: Dome W): (μ z) (pennant W (restrictG Λ s (g ∘ δ (2*glint Λ s z))) u) = pennant W (restrictG Λ s g) ((μ z) u):= by -- RHS after transforming by + != composed? need check sign
  let R₁(x:Dome W):= aureole W j (0:ℤ) x
  let Z:=restrictG Λ s g
  let F(p:Cover→SU.E)(q:ℤ):= reflectGauge j q p
  have hg : F (F Z z) 0=restrictG Λ s (g∘δ (2*glint Λ s z)):=by
     let m:ℤ→ Cover → Cover:= fun z=>(plane j z).motion
     have he (z:ℤ)(y):addressG Λ s (m z y)= mirrorE j (θ z) (addressG Λ s y):=by
       funext i; unfold m addressG mirrorE; rw [fling_move]; by_cases h:i=j
       · rw [if_pos h,if_pos h.symm]; unfold glint markZ; push_cast; ring
       rw [if_neg h, if_neg (Ne.symm h)]
     funext i; change g (addressG Λ s (m z (m 0 i)))=g (δ _ _); rw [he,he,show θ 0=0 by simp [glint],about]; rfl
  rw [← hg]; change _= pennant W Z (aureole W j z (aureole W j 0 u)); rw [pennantReflect,pennantReflect]; rfl
end displacement

section ward
variable (Λ:Preparation)(l:ℕ)(s n:ℕ)(z:ℤ) (W:Calibration)
local notation "μ" u:max=>cruise j W u
noncomputable def stratus : Cloud (Dome W)→ₐ[ℂ] Cloud (Dome W):= AlgHom.ofLinearMap (plume (fun i=> (cruise j W (smill Λ s i z)).toLinearMap)) (plumeUnit _ fun i=>map_one (μ (smill Λ s i z))) (plumeTimes _ fun i x y=> map_mul (μ (smill Λ s i z)) x y)
local notation "C₀" z:max=>stratus j Λ s z W
noncomputable def flockMove : sequenceOf W→ sequenceOf W := plumeTail (fun i=> (cruise j W (smill Λ s i z)).toLinearMap)
local notation "Δ" z:max=>flockMove j Λ s z W
@[simp] lemma flockAt (f:sequenceOf W) (i:ℕ): ((Δ z) f i)=(μ (smill Λ s i z)) (f i):=rfl
lemma flockLength {f:sequenceOf W} (h:Enough n f): Enough n ((Δ z) f):= plumeEnough (χ:=RingHom.id ℂ) (o:=fun i=>(cruise j W (smill Λ s i z)).toLinearMap) (fun i=>map_one (cruise j W (smill Λ s i z))) h
lemma flockAll (f:sequenceOf W): (C₀ z) (pureShot W f)=pureShot W ((Δ z) f) := pluage (fun i=>(cruise j W (smill Λ s i z)).toLinearMap) f
lemma stratusPile (v:ℤ)(x:Cloud (Dome W)): (C₀ z) ((C₀ v) x)=(C₀ (z+v)) x:=by
  induction x using PiTensorProduct.induction_on with
  | add a b q r=> rw [map_add,map_add,q,r,map_add]
  | smul_tprod c t=>
    rw [map_smul,map_smul,map_smul]
    change _ • (C₀ z) ((C₀ v) (pureShot W t))= _ • (C₀ _) (pureShot W t); rw [flockAll,flockAll,flockAll]; exact congrArg (fun x=> c • (pureShot W x)) (funext fun i=>by simp only [flockAt,sailsBy,smill_add])
lemma stratus_start (x:Cloud (Dome W)):(C₀ 0) x=x:=by
  induction x using PiTensorProduct.induction_on with
  | add a b q r=> rw [map_add,q,r]
  | smul_tprod a b=>
    rw [map_smul]
    change _ • (C₀ 0) (pureShot W b)=_; rw [flockAll]; exact congrArg (fun t=> a • pureShot W t) (funext fun i=>by simp only [flockAt,smill,mul_zero,sailsBack])
local notation "u'ᵣ" t:max=> (smill Λ s t z) -- orientation
local notation "β" => glint Λ s z
local notation "λz" => steer j β
-- authorize V and levels
variable (wide: Bool){U: Set RSpace} {S:Set ℕ} {x: Altitude.Cloud (Dome W)}(h: S⊆ Set.Ici s)
local notation "T" x:max => jetty Λ l W wide (handstamp x) S
include h
lemma jetsMove (p:x∈ T U) : (C₀ z) x∈ T ((λz) '' U) :=by
  apply plumeExtend (χ:=RingHom.id ℂ) (o:=fun i=> (cruise j W (smill Λ s i z)).toLinearMap) (P:={f|Officer S (fun i=> keep Λ l i W wide (handstamp U)) f}) (Q:={f| Officer S (fun i=> keep Λ l i W wide (handstamp ((λz) '' U))) f}) _ p
  intro f v; have he := (v: Officer _ _ f); change Officer _ _ ((Δ z) f); have hw(i) (p:i∉ S): (Δ z) f i=1:=by rw [flockAt,he.forbids i p,map_one];
  refine ⟨⟨he.toll.choose, flockLength j Λ s _ z W he.toll.choose_spec⟩,fun i=>?_,hw⟩; by_cases q:i∈S
  · rw [←glintRef z Λ s i (h q),flockAt]; exact hand_steer j W _ Λ l i U (he.observes i)
  rw [hw i q]; exact Subalgebra.one_mem _
lemma transportsG (g:GPhysical)(p:x∈ T U) : rainfall Λ W g ((C₀ z) x)=(C₀ z) (rainfall Λ W (g∘ steer j (2*β)) x) := by
  let Z:= g∘ steer j (2*β)
  apply boarded (P:={f| Officer S (fun i=> keep Λ l i W wide (handstamp U)) f}) (M:=fun x=>_) ?_ ?_ ?_ ?_ p
  · intro f (hF:Officer _ _ _); change rainfall Λ W g ((C₀ z) (pureShot W f))=(C₀ z) (rainfall Λ W (g∘ steer j (2*β)) (pureShot W f)); rw [flockAll,rainfallPure,rainfallPure,flockAll]; apply congrArg; funext i; by_cases q:i∈S
    · simp only [rainyTail,flockAt] -- use glintRef
      rw [← glintRef z Λ s i (h q),glintGauge]
    simp only [rainyTail,flockAt, map_one,hF.forbids i q]
  · simp
  · intro a b i j u v; rw [map_add,map_add,map_add,map_add,u,v]
  intro a b z v; rw [map_smul,map_smul,map_smul,map_smul,v]
lemma soldWell (p:x∈ circum Λ l W wide U S) : (C₀ z) x∈ circum Λ l W wide ((λz) '' U) S:= by
  obtain ⟨p,b⟩:= (well_spec ..).1 p; exact (well_spec ..).2 ⟨jetsMove j Λ l s z W wide h p,fun g=> (transportsG j Λ l s z W wide h g p).trans (congrArg (C₀ z) (b (g∘ steer j (2*β))))⟩
end ward
section transaction
local notation "μ" u:max=>cruise j K u
variable (s n:ℕ)(z:ℤ)
local notation "p'" z:max=>stratus j Λ s z K
local notation "Δ" z:max=>flockMove j Λ s z K
local notation "a₀"=>smill Λ s n z
local notation "A'" x:max=>smill Λ s x z
variable (U:Set RSpace)
include G V
lemma updatedShelter {f:Cₚ}(p:f∈jetty Λ l K true (handstamp U) (Set.Ici s ∩ Set.Iic n))(v:s≤n): (P₀ n) ((p' z) f)=(μ a₀) ((P₀ n) f) := by
  let Z:Set ℕ:= Set.Ici s ∩ Set.Iic n
  apply boarded (P:={f| Officer (Set.Ici s ∩ Set.Iic n) (fun i=> keep Λ l i K true (handstamp U)) f}) (M:=fun x=>_) ?_ ?_ ?_ ?_ p
  · intro f (p:Officer Z _ f)
    have he := p.visible Z _ Set.inter_subset_right
    change (P₀ n) ((p' z) (pureShot _ _))=(μ a₀) ((P₀ n) (pureShot _ _)); rw [flockAll,vistaFinish, Decking.reckon_paid _ _ _ (flockLength j Λ s n z K he), Decking.reckon_paid _ _ _ he]; exact trail f (fun i h=>p.forbids i (fun t=>h.not_ge t.1)) n v
  · simp
  · intro x y p q h t; rw [map_add,map_add,map_add,map_add,h,t]
  intro k x p h; rw [map_smul,map_smul,map_smul,map_smul,h]
where
 trail (f:sequenceOf (tent Y H)) (p:∀ i<s,f i=1) (n:ℕ)(v:s≤n): Decking.finish (F₀) n ((Δ z) f)=(μ (A' n)) (Decking.finish (F₀) n f):=by
    induction n,v using Nat.le_induction with
    | base=> rw [Decking.finish_alone (F₀) _ ((Δ z) _) (fun n e=>by rw [flockAt,p n e,map_one]), Decking.finish_alone (F₀) _ f p]; rfl
    | succ n i h=>
      rw [Decking.finish, Decking.finish,h,map_mul]; congr 1
      let x:= Decking.finish (F₀) n f; apply Subtype.ext
      change ((D₀ n) ((μ (A' n)) x)).val=( (μ (A' (n+1))) ((D₀ n) x)).val; rw [sailsTo,lifts_here Y H V G,sailsTo,lifts_here Y H V G]
      have hx:= acreage_X Y H G j n 1 (F:=x.val) x.property (A' n); rw [pow_one] at hx; rw [show (A' (n+1))=(Λ.R.L.val:ℤ)*(A' n) by unfold smill; rw [show n+1-s=n-s+1 by omega,pow_succ',mul_assoc]]; exact hx
lemma billMoves {f:Cₚ}(p:f ∈ jetty Λ l K true (handstamp U) (Set.Ici s)) : Θ ((p' (2*z)) f)=Θ f:=by
  obtain ⟨n,p⟩:= entrusted Λ l K true (handstamp U) (Set.Ici s) p
  let m:= max s n; let X:=Set.Ici s ∩ Set.Iic m
  have h:f∈ jetty Λ l K true (handstamp U) X:=by apply admits Λ l K true _ _ (Set.Ici s ∩ Set.Iic n) X _ Set.Subset.rfl p; exact fun i p=> ⟨p.1, Set.mem_Iic.mpr (le_trans p.2 (le_max_right s n))⟩
  let z':=2*z
  have hg:= jetsMove j Λ l s (2*z) K true (U:=U) (show X ⊆ Set.Ici s from Set.inter_subset_left) h
  rw [drawAt Y H V G D d T x (jettyBan Λ l K true _ (Set.Ici s) m hg),drawAt Y H V G D d T x (jettyBan Λ l K true _ (Set.Ici s) m h),updatedShelter Y H V G j D s _ (2*z) U h (le_max_left ..), show smill Λ s m (2*z)=2*smill Λ s m z by unfold smill; ring]; exact elect_sold Y H V G j m d T x _ (((P₀ m) f).property)
end transaction
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.billMoves
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.soldWell
