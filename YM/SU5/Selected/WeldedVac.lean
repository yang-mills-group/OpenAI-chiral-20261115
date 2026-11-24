import YM.SU5.Selected.Railroad
import YM.SU5.Selected.Awoken
/-!
# Exact movement of all two matter-pitches (4 gauge sites) in selected vac
& expected continuation, i.e. honest agreement with Permit clock at the
indicated positive times. Applies to NT builds (strict arbitrary). Use for
small-motion estimates on grid as GAP remains for continuous space. -/
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
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open Theory Set MeshClock
local notation "Ρ" s:max=> weld Y H V G j strict C s
local notation "Q"=>advance Y H V G.history.circuit j 0 strict C
local notation "δ" s:max v:max=>pitchMill Λ s v
local notation "J" s:max=>bout Y H j strict s
local notation "S₀" =>stationC Y H V G j strict C
local notation "M"=>timeMesh Λ
local notation "Qe"=>heatOp Y H V G j strict C
local notation "Be"=>boxElement Y H V G j strict C
local notation "a₀"=> 8*Λ.block.val
section
variable (s i':ℕ){w:ℕ}(x:Entry Y H s j strict w)
include V C
lemma soldFrame (u v W:ℕ)(y:Entry Y H s j strict W)(p: (8*Λ.block.val)*w + u + v = (8*Λ.block.val)*W) (h:y.val=(J s) u x.val) (e:0<w)(q:0<W) :
    B s y q= (Ρ s) u * B s x e * (Ρ s) v:=by
  apply test_high Y H V s G.history j strict C; intro t z f
  let N:=Λ.R.L.val^(t-s)
  change _=(Ρ s) u ((B s x e) ((Ρ s) v ((κ t) f)))
  let X:=furnished Y H s G.history j strict w x t z; let Y₁:=furnished Y H s G.history j strict W y t z
  rw [weld_at Y H V G j strict C s v z,snatch Y H V s G.history G.clipped j strict C w _ _ z,snatch Y H V s G.history G.clipped j strict C W _ _ z,weld_at Y H V G j strict C s u z]
  have a: Y₁.val=(J t) (N*u) X.val:=by
    rw [show Y₁.val=Raise Y H G.history.circuit j 0 strict s t z y.val from rfl,h]; exact (stride_up Y H G j strict s u t x.val z).symm
  apply congrArg _; apply Subtype.ext
  change Y₁.val.val * (tick Y H t j 0 strict (2*(N*W)) f).val = chime K j ((N*u:ℕ):ℤ) (X.val.val * (tick Y H t j 0 strict (2*(N*w)) ((J t) (N*v) f)).val)
  rw [a,chime_product,← stride_gauge,← stride_gauge]
  let r:= 4*Λ.block.val
  change _* _ = ((J t) (N*u) X.val).val * ((J t) (N*u) ((J t) (4*Λ.block.val*(2*(N*w))) ((J t) (N*v) f))).val
  rw [stride_sum,stride_sum]
  have hx:N*u + r*(2*(N*w))+N*v=r*(2*(N*W)) :=
    calc _ = N*((8*Λ.block.val)*w+u+v) := by unfold r; ring
         _ = _ := by rw [p]; unfold r; ring
  unfold r at hx; rw [hx]

lemma soldEven (u v W:ℕ)(y:Entry Y H s j strict W)(p:(4*Λ.block.val)*w+u+v=(4*Λ.block.val)*W)(h:y.val=(J s) (2*u) x.val)(e:0<w)(q:0<W) :
    B s y q= Q (δ s (2*u))* B s x e * Q (δ s (2*v)):=by
  rw [← weld_clock,←weld_clock]; apply soldFrame Y H V G j strict C s x (2*u) (2*v) W y _ h e q
  have hx(t:ℕ):8*Λ.block.val*t= 2*(4*Λ.block.val*t):=by ring
  simp_rw [hx]; omega

omit V C
lemma extensionDate (u v:ℕ)(hp:0<v) : ∃ W k:ℕ,4*Λ.block.val*w+i'+k=4*Λ.block.val*W ∧ v≤ W ∧
    ∃ y:Entry Y H s j strict W,y.val=(J s) (2*i') x.val:=by
 let r:=4*Λ.block.val; have t:0 < r:=by unfold r; positivity
 obtain ⟨W,h,t,y,e⟩:= ((eventually_ge_atTop v).and ((Tendsto.const_mul_atTop' t (tendsto_id (x:=atTop))).eventually_ge_atTop (r*w+i')|>.and (field_entry Y H j strict s ((J s) (2*i') x.val)))).exists
 obtain ⟨k,hk⟩:= Nat.exists_eq_add_of_le (show _≤ r*W from t)
 exact ⟨W,k,hk.symm,h,y,e⟩
include V C
local notation "F" => x.val
lemma cap_sold {y y':observable (tent Y H) strict}(p:y'.val=chime K j ((2*i':ℕ):ℤ) y.val) : (P s) y'=(P s) y := by
 obtain ⟨v⟩:= anyporch Y H s j strict y
 obtain ⟨W,k,t,w,yx,q'⟩:=extensionDate Y H j strict s i' v.fwd 1 1 Nat.zero_lt_one
 have h:v.fwd.val= v.fwd.val:=rfl
 have a:yx.val.val=relocate K j v.rise y'.val:=by rw [q']; change chime K j _ _=_; rw [v.yes,p]; unfold relocate; rw [Tower.bumps K j _ _ y.property.1.paid.choose_spec,Tower.bumps K j _ _ y.property.1.paid.choose_spec,add_comm]
 rw [cap_moved_entry Y H V G j strict C s W yx y' w v.rise a,cap_moved_entry Y H V G j strict C s v.span v.fwd y v.pos v.rise v.yes,soldEven Y H V G j strict C s v.fwd i' k W yx t q' v.pos w]
 change (π).comp ((((Q _).comp _).comp (Q _)).comp ι₀)=_
 rw [ContinuousLinearMap.comp_assoc,behind',← ContinuousLinearMap.comp_assoc (π),← ContinuousLinearMap.comp_assoc (π),behind,ContinuousLinearMap.comp_assoc]
variable (d:Axis) (T:Arena Y H G.history.circuit d 0 strict)
lemma seal_sold {y x₀: observable (tent Y H) strict}(z:ℤ)(p:x₀.val=chime K j (2*z) y.val): seal₀ Y H V G d strict T s x₀=seal₀ Y H V G d strict T s y := by
  wlog hz:0≤z generalizing x₀ y z
  · refine (this (-z) ?_ (by omega)).symm
    rw [p,Tower.bumps K j _ _ y.property.1.paid.choose_spec,←mul_add,neg_add_cancel,mul_zero,wake K j y.property.1.paid.choose_spec]
  have hp := cap_sold Y H V G j strict C s z.toNat (y:=y) (y':=x₀) (by rw [Nat.cast_mul,Nat.cast_ofNat,Int.toNat_of_nonneg hz]; exact p)
  apply Transaction.mono_ (bank Y H V G j strict C d T); rw [corner,corner]; exact hp
omit C
variable (D:∀ i:Axis,Arena Y H G.history.circuit i 0 false) (x':Resident (catalog Y H V G d false (D d)))
local notation "ʆ"=>evaluate Y H V G d D x'
lemma elect_sold {f:Family K}(z:ℤ)(p:TestFamily K true f): ʆ s (chime K j (2*z) f)=ʆ s f:=by
 unfold evaluate; let a:= aux_test (flow_port K j (2*z) p.paid.choose_spec); rw [dif_pos a,dif_pos p]; unfold markE; rw [seal_sold Y H V G j false (D j) s d (D d) (y:=observe p) (x₀:= observe a) z rfl]
lemma elect_glassUp {f:Family K}(z:ℤ)(p:TestFamily K true f): ʆ s (mirror K j (2*z) f)=star (ʆ s f):=by
 let Z:=p.paid.choose_spec
 rw [slidesPlane j Z (2*z), elect_sold Y H V G j s d D x' z (reflect_ok K j 0 p), show mirror K j 0 f=mirror K j (Heat.gaugeShift Λ.block 0) f by unfold Heat.gaugeShift; simp]
 exact elect_mirror Y H V G j d D x' p 0 s -- fill
include C
namespace Acting
variable (T:Acting Y H V G j strict C)
local notation "Qₜ"=>clock Y H V G j strict C T
local notation "Beₜ"=>watches Y H V G j strict C T
local notation "γ" s:max=>voice Y H V G j strict C T s
lemma sold_est (u v W:ℕ)(y:Entry Y H s j strict W)(p:(4*Λ.block.val)*w+u+v=(4*Λ.block.val)*W)(h:y.val=(J s) (2*u) x.val)(e:0<w)(q:0<W) : Beₜ s _ y q = Qₜ (δ s (2*u)) * Beₜ s w x e * Qₜ (δ s (2*v)) := by
    unfold watches clock; rw [← map_mul, ← map_mul]; exact congrArg T.showL (Subtype.ext (soldEven Y H V G j strict C s x u v W y p h e q))
lemma read_stride (f:Fₛ s) : (γ s) ((J s) (2*i') f)= Qₜ (δ s (2*i')) ((γ s) f):=by
  obtain ⟨u,h,x,rfl⟩ := ((eventually_gt_atTop (0:ℕ)).and (field_entry Y H j strict s f)).exists
  obtain ⟨W,k,t,v,y,e⟩:=extensionDate Y H j strict s i' x 1 1 Nat.zero_lt_one
  rw [← e,T.notes Y H V G j strict C s v y,T.notes Y H V G j strict C s h x]
  rw [T.sold_est Y H V G j strict C s x i' k W y t e h v]
  exact congrArg (Qₜ _ * Beₜ s u x h) (vacuum_time ..)
end Acting
end

end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Acting.read_stride
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.elect_sold
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.elect_glassUp
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.seal_sold
