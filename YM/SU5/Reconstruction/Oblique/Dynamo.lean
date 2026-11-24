import YM.SU5.Reconstruction.Oblique.SupportRose
/-!
# Rotation symmetry of finally ON the resulting PVM channels. Unit rotation VERIFICATION. width carried. No need even Rank or particle recognition etc. Docs for hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "wk" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (wk i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (wk i)
local notation "U₀" i:max=> mainsea Y H V G.history G.clipped i false (C i) (wk i)
local notation "A₀" i:max=> ride Y H V G.history G.clipped i false (C i) (wk i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (wk i)
local notation "Os" i:max=> OSvector Y H V G i (C i) (wk i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "ℜ" t:max=> Real.toNNReal (t:ℝ)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "Ω" =>whiff Y H V G C a χ
local notation "au"=>move K
open LightBudget Chambers -- provide BootBacking later
local notation "Fs" i:max=> fort Y H V G.history G.clipped i false (C i) (wk i)
local notation "N" i:max=>Domain Y H G false (flank i 0)
local notation "V₀" i:max=>coreOs Y H V G i (C i) (wk i)
local notation "X₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (wk i)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (wk i)
local notation "℘" i:max=>Picket.trans (S₀ i)
local notation "Qv" i:max=> Follows Y H V G i (C i) (wk i)
local notation "π" i:max=> opCarries Y H V G i (C i) (wk i)
variable (B:BoostBacking Y H V G C a χ) {s:Signed}(A:Pave Y H V G C a χ s) {j z:Axis} (t:Oriented s j z)

include t
lemma orientMark (x:N j): A.shift x.val∈N z:= (orientation_Flank t 0) ▸ (A.shifts _ _ _).1 x.property
lemma orientBack(y:N z):A.shift.symm y.val∈N j:= orientMark Y H V G C a χ (Pave.reflected Y H V G C a χ A) t.return_z y
noncomputable def ferryN: (N j)≃ₗ[ℂ](N z) where
 toFun x:=⟨_,orientMark Y H V G C a χ A t x⟩
 invFun x:=⟨_,orientBack Y H V G C a χ A t x⟩
 left_inv x:=Subtype.ext (A.shift.symm_apply_apply x.val)
 right_inv x:=Subtype.ext (A.shift.apply_symm_apply x.val)
 map_add' x y:=Subtype.ext (map_add _ x.val y.val)
 map_smul' c x:=Subtype.ext (map_smul _ c x.val)
local notation "Yf" => ferryN Y H V G C a χ A t
omit t
include B in
lemma leg_comp (j:Axis)(x y:N j): inner ℂ ((V₀ j) x) ((V₀ j) y)= Ω ((θ j) x.val * y.val):=by
 change inner ℂ (((V₀ j) x).val:J₀ j) (((V₀ j) y).val:J₀ j)= _; rw [voice_full Y H V G j _ _ (B.present j),voice_full Y H V G j _ _ (B.present j), registered_pair,whiff_turn Y H V G C a χ j _ (paired_forever Y H G j _ _ x.property y.property)]
include t B in
lemma legitimacy (x y:N j): inner ℂ ((V₀ z) (Yf x)) ((V₀ z) (Yf y)) = inner ℂ ((V₀ j) x) ((V₀ j) y):= by
 simp only [leg_comp Y H V G C a χ B]; change Ω ((θ z) (A.shift _) * A.shift _) = _
 rw [show flipMark z K (A.shift x.val)=A.shift ((θ j) x.val) from by rw [A.mirror,t.peer], ← A.muls,A.fuel _ (paired_forever Y H G j _ _ x.property y.property)]
lemma worth (j:Axis): DenseRange (V₀ j):= (compass_domain_dense Y H V G j (C j) (wk j)).mono (fun y e=> by obtain ⟨d,h⟩:=e; exact ⟨Submodule.inclusion (domain_loose Y H G _) d,h⟩)
include t B
lemma permitted_frame: ∃ U:(Fs j) ≃ₗᵢ[ℂ] (Fs z),∀ x:N j,U ((V₀ j) x)= (V₀ z) (Yf x):= by
 refine Selected.gram_impl («A»:=Fs j) («B»:= Fs z) (g:=fun x=> (V₀ z) (Yf x)) (worth Y H V G C a χ j) ?_ (fun x y=>(legitimacy Y H V G C a χ B A t x y).symm); refine (worth Y H V G C a χ z).mono ?_; rintro _ ⟨x,rfl⟩; obtain ⟨w,rfl⟩:= (Yf).surjective x; exact ⟨w,rfl⟩
noncomputable def motor: (Fs j) ≃ₗᵢ[ℂ](Fs z):= (permitted_frame Y H V G C a χ B A t).choose
local notation "α"=> motor Y H V G C a χ B A t
lemma motoring (x:N j)(y:N z)(p:y.val=A.shift x.val):α ((V₀ j) x)= (V₀ z) y:= (Classical.choose_spec (permitted_frame Y H V G C a χ B A t) x).trans (congrArg _ (Subtype.ext p.symm))
lemma motor_source: α (X₀ j)=X₀ z:=by
 let h(i:Axis):=(⟨1,domain_one ..⟩:N i); have ht(i):X₀ i= (V₀ i) (h i):= (comesHome Y H V G C a χ i).symm -- tune parentheses
 rw [ht,ht]; exact motoring Y H V G C a χ B A t _ _ A.unit.symm
lemma motor_return : motor Y H V G C a χ B (Pave.reflected Y H V G C a χ A) t.return_z= (α).symm:=by
 let M:= motor Y H V G C a χ B (Pave.reflected Y H V G C a χ A) t.return_z; change M=_
 apply DFunLike.coe_injective; apply (worth Y H V G C a χ z).equalizer M.continuous (α).symm.continuous; funext x; obtain ⟨x,rfl⟩:= (Yf).surjective x; apply (α).injective; change α (M ((V₀ z) _)) = α ((α).symm _); rw [LinearIsometryEquiv.apply_symm_apply,show M ((V₀ z) (Yf x))=(V₀ j) x from motoring Y H V G C a χ B _ t.return_z _ _ (A.shift.symm_apply_apply x.val).symm]; exact motoring Y H V G C a χ B A t _ _ rfl
-- intertwinement operator prices.Backlight.
lemma follows_move {x:Sky (tent Y H)}(u:Gt)(p:0<(u:ℝ))(X:(J₀ j).Op)(v:(Qv j) x u X) : ∃ D':(J₀ z).Op,(Qv z) (A.shift x) u D' ∧ (π z) D'=(α).conjStarAlgEquiv ((π j) X):= by
 have he:A.shift x∈Domain Y H G false (strip z 0 (u:ℝ)):= (orientation_strip t 0 _) ▸ ((A.shifts ..).1 v.pose)
 obtain ⟨A',q⟩:=fits Y H V G z (C z) (wk z) u p _ he; refine ⟨A',q,?_⟩; apply Crease.chamberEd; intro y; obtain ⟨Y₁,rfl⟩:= (Yf).surjective y
 obtain ⟨l,h,w⟩:= voice_follows Y H V G j (C j) (wk j) (B.present j) v Y₁; obtain ⟨l',g,v'⟩:= voice_follows Y H V G z (C z) (wk z) (B.present z) q (Yf Y₁)
 have hv:(Yf l)=l':= by apply Subtype.ext; change A.shift l.val= l'.val; rw [h,A.muls,A.strips,t.axis_eject u,g]; rfl
 rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,← show α ((V₀ j) Y₁)=(V₀ z) (Yf Y₁) from motoring Y H V G C a χ B A t _ _ rfl, LinearIsometryEquiv.symm_apply_apply, ←w, show α ((V₀ j) l)= (V₀ z) l' from motoring Y H V G C a χ B A t _ _ (congrArg Subtype.val hv.symm),motoring Y H V G C a χ B A t Y₁ (Yf Y₁) rfl]; exact v'.symm
lemma turn_appointment(p:placement Λ)(t':0≤ (p j).val): (α).conjStarAlgEquiv ((Pr j) p)= (Pr z) (s.act p):= by
 apply Crease.chamberEd; intro x; obtain ⟨x,rfl⟩:= (Yf).surjective x
 let y: N j:= ⟨_,later_frame Y H V G j x.val p x.property t'⟩; have hy:x=x:=rfl; have hz:0≤(s.act p z).val:=by rw [t.height]; exact t'
 let y':N z:=⟨_,later_frame Y H V G z (Yf x).val (s.act p) (Yf x).property hz⟩ -- notation projection parser
 rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,show (α).symm ((V₀ z) (Yf x))=(V₀ j) x from (α).symm_apply_eq.mpr (motoring Y H V G C a χ B A t x (Yf x) rfl).symm, ← show (V₀ j) y= _ from voice_move Y H V G j _ _ (B.present j) _ x t' y.property, ←show (V₀ z) y'= _ from voice_move Y H V G z _ _ (B.present z) _ (Yf x) hz y'.property]; exact motoring Y H V G C a χ B A t _ _ (A.strips p x.val).symm
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
