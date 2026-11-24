import YM.SU5.Reconstruction.LinkMeasures.PayWhole
import YM.SU5.Reconstruction.PolarArchives.Console
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satori
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Tapestry
open Tower Tower.SatinVerification PaymentCamera
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    (V:Universal Y H i k I E)(G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (S:Finset Cover)(s:ℕ)(w:Evens S)
local notation "μS" => actual S Λ l
local notation "W" => wingspan Λ l S
local notation "Bx" => PhaseChoice.transfer Y H G S s
local notation "Tx" => singer S w
local notation "rᵢ" i1:max => i (G.rows i1)
local notation "rₖ" i1:max => k (G.columns i1)

open Tower.Vacancy Tower.Selected Tower.FirstWindows PaymentCamera
local notation "q★" => Satori.qty S Λ l
open Tower.FirstWindows.PolarArchives Tower.Tilted Tower.Tilted.Ramp Tower.FirstWindows.WindRose Tower.PhaseChoice
variable (P:Tower.Tilted.Ramp)(gap:ℝ≥0)
local notation "U₀" => Acres P gap
variable (Γ:Calibration)
local notation "J"=> P.survey S
local notation "R"=> S ∪ P.survey S
variable (p:PhaseChoice.SupportedPhysically Λ l s S (Acres P gap))
-- static epoch geography around off-axis reflection
lemma tilted_sheet {U:Set RSpace}(h: PhaseChoice.SupportedPhysically Λ l s S U) : PhaseChoice.SupportedPhysically Λ l s (P.survey S) (P.s.act '' U):=by
 apply (supported_iff ..).2; rintro y v
 obtain ⟨x,c,w,h',rfl⟩:= Set.mem_iUnion₂.mp v; obtain ⟨x,g,rfl⟩:= Finset.mem_image.mp c
 rw [P.mode_motion] at h'; have hp:=rotates_shield P s h'; rw [P.act_act] at hp
 refine ⟨toMatterUnits (P.s.act w), (supported_iff ..).1 h (Set.mem_iUnion₂.mpr ⟨x,g,_,hp,rfl⟩),?_⟩; rw [matter_turn,P.act_act]
include p
lemma holy_grid (a:Cover)(u:a∈ P.survey S) (t:a∈ S):False:=by
 have hp:= tilted_sheet S s P p
 exact Set.disjoint_left.mp (unpaired P gap) ((supported_iff ..).1 hp (center_in_hull Λ l s (P.survey S) u)) ((supported_iff ..).1 p (center_in_hull Λ l s S t)) -- pipe all? tune
omit p
-- move any piece on this Swatch footprint through Θ. Cost remains accounted. Linear and REAL continuous.
noncomputable def tiltOne : Swatch S →ₗ⋆[ℂ] Swatch (J) where
 toFun x:=fabric (P.survey S) Γ (P.faces Γ (texture S Γ x))
 map_add' x y:=render_inj _ Γ (by rw [render_fabric,map_add,map_add, render_fabric,render_fabric, P.over_add]) -- order
 map_smul' z x:=render_inj _ Γ (by rw [render_fabric,map_smul,map_smul,render_fabric,P.over_z]; rfl)
lemma tilted_quantity (x:Swatch S): render J Γ (tiltOne S P Γ x)=P.cuspF Γ (render S Γ x):= render_fabric _ _ (P.faces Γ (texture S Γ x))
noncomputable def luster: Swatch S→SL[starRingEnd ℂ] Swatch (P.survey S):= (tiltOne S P Γ).mkContinuous (Tapestry.spread S) fun x=>by
 obtain ⟨m,u⟩:= (Buffered.separates Γ (P.survey S)).exists
 refine Tapestry.sampling _ _ _ ⟨u⟩ _ fun v=>?_ ; rw [←appearRender,tilted_quantity]; unfold cuspF Ramp.bill Fock.theta; rw [twist_norm, Scroll.norm_cc]; exact renderLe ..
local notation "t₀" => luster S P K
noncomputable def aptR : Swatch S × Swatch S → Swatch (S ∪ P.survey S):= fun x=> brocade K (R) (Tapestry.broad K (J) R Finset.subset_union_right (t₀ x.1)) (Tapestry.broad K S R Finset.subset_union_left x.2)
lemma apt_c:Continuous (aptR Y H S P):=by
 unfold aptR; simp_rw [←brocadeL_eq]; exact ((brocadeL K R).continuous.comp ((Tapestry.broad K J R Finset.subset_union_right).continuous.comp ((t₀).continuous.comp continuous_fst))).clm_apply ((Tapestry.broad K S R Finset.subset_union_left).continuous.comp continuous_snd)
local notation "θF" => windTilt P K
lemma badge_apt (x y:Swatch S): θF (badge (tent Y H) S x) * badge K S y= badge K (S∪P.survey S) (aptR Y H S P (x,y)):=by apply Subtype.ext; unfold aptR; rw [domTag,bareMult,broadRender,broadRender]; change _ * _ = render J K (tiltOne S P K x)*_; rw [tilted_quantity]; rfl
noncomputable def optic (x y: Swatch S):ℂ:= beforeSelection Y H V s (windTilt P K (badge K S x)* badge K S y)
local notation "L" => optic Y H V S s P
lemma optic_c:Continuous (Function.uncurry (optic Y H V S s P)):=by
 rw [show Function.uncurry L=(fun x:Swatch R=> E s (render R K x)) ∘ (aptR Y H S P) from funext fun ⟨i,j⟩=> by change beforeSelection Y H V s (windTilt P K (badge K S i)*badge K S j)=_; rw [badge_apt]; rfl]; exact (E_lookup Y H V _ _).comp (apt_c ..)
noncomputable def leanView (x:Swatch S): Swatch S →ₗ[ℂ] ℂ where
 toFun y:= optic Y H V S s P x y
 map_add' i j:= (by unfold optic; rw [map_add, mul_add,map_add])
 map_smul' z y:= (by unfold optic; rw [map_smul, Algebra.mul_smul_comm,map_smul]; rfl)
private lemma con_fix {X Z:Type*}[TopologicalSpace X][TopologicalSpace Z](g:X→X→Z)(h:Continuous (Function.uncurry g))(x:X):Continuous (g x):= h.comp (continuous_const.prodMk continuous_id)
lemma leanSeen (x:Swatch S): Continuous (leanView Y H V S s P x):=con_fix (Z:=ℂ) (optic Y H V S s P) (optic_c Y H V S s P) x
noncomputable def rView (x:Swatch S): Swatch S →L[ℂ] ℂ:=⟨leanView Y H V S s P x, leanSeen Y H V S s P x⟩
lemma optic_mirror(x y:Swatch S): L x y=star (L y x):=by
 let f:= θF (badge K S y)*badge K S x
 have he:L y x=E s f.val:=rfl
 have ht: (θF f)= θF (badge K S x)*badge K S y:=by unfold f; rw [show ∀ u v:Dome K, θF (u*v)=θF u*θF v from fun _ _=>Subtype.ext (P.over_times (tent Y H)), twice_dome, mul_comm]
 rw [he]; unfold optic; rw [←ht]; change E s (P.cuspF K f.val) = _; exact step_Price Y H P s V ((marque ..).1 f.property)

-- geometric currency, through D using trajectory path funding
local notation "Q" =>Domain Y H G false Set.univ
include p
lemma custodies (F:Dome K)(h:InTest K true S false F.val) : F ∈ insideAt Λ l K false (Acres P gap) s := (mem_insideAt F s).mpr ⟨⟨S,h,p⟩,nofun⟩
local notation "Qₜ" => Domain Y H G false (Acres P gap)
local notation "φ" => gust P (tent Y H)
lemma opamount (x y:Swatch S)(h:φ (ticket Y H G s (badge K S x))* ticket Y H G s (badge K S y)∈Q): L x y=courseValue Y H V G ⟨φ (ticket Y H G s (badge K S x))* ticket Y H G s (badge K S y),h⟩ :=by
 let z:=θF (badge K S x)*badge K S y
 have e : ticket Y H G s z=φ (ticket Y H G s (badge K S x))* ticket Y H G s (badge K S y) := by
    rw [gust_ticket Y H V]; exact ticket_separated Y H G (protects P s _ _ _ (custodies Y H S s P gap p _ (texture ..))) (custodies Y H S s P gap p (badge K S y) (texture ..)) (unpaired P gap)
 rw [show (⟨_,h⟩:Q)=⟨ticket Y H G s z,ticket_loose ..⟩ from Subtype.ext e.symm,course_ticket_val]; rfl
lemma optic_up (x y:Swatch S): L x y=optic Y H V W (s+1) P ((Bx) x) ((Bx) y):= by
 have e:∀ i:Swatch S, ticket Y H G s (badge K S i)=ticket Y H G (s+1) (badge K (W) (Bx i)):= fun x=>by rw [← step_badge, ticket_spread Y H G (Nat.le_succ s)]
 let h: φ (ticket Y H G s (badge K S x))*ticket Y H G s (badge K S y)∈ Q:= by exact pay_your Y H V G _ _ (ticket_mem _ _ _ (custodies Y H S s P gap p _ (texture ..))) (ticket_mem Y H G (custodies Y H S s P gap p _ (texture ..)))
 have h':PhaseChoice.SupportedPhysically Λ l (s+1) (wingspan Λ l S) (Acres P gap):=p.persists 1
 have hop:=fun x y=> opamount Y H V G W (s+1) P gap h' x y
 let t:(Domain Y H G false Set.univ):=⟨_,h⟩
 rw [opamount Y H V G S s P gap p x y h,opamount Y H V G (W) (s+1) P gap h']; · apply congrArg; apply Subtype.ext; dsimp only; rw [←e,←e]
 rw [←e,←e]; exact h

end YM.CF.Buffered.Afterglow.Satori
#print axioms YM.CF.Buffered.Afterglow.Satori.optic_up
#print axioms YM.CF.Buffered.Afterglow.Satori.optic_mirror
#print axioms YM.CF.Buffered.Afterglow.Satori.holy_grid
