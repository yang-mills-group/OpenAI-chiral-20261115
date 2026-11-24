import YM.SU5.Reconstruction.Seams.Court
/-! Billing Follows on this real grid graph. No buying Strong momentum. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Gt" => marks (timeMesh Λ)
local notation "K₀"=> tent Y H
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
open Chambers LightBudget Germ
local notation "J₀"=> indoor Y H V G.history G.clipped j false C χ
local notation "Jₛ"=> (turnstile Y H V G.history G.clipped j false C χ)
local notation "C₀"=> saunters Y H V G.history G.clipped j false C χ
local notation "G₀"=> fort Y H V G.history G.clipped j false C χ
local notation "Ω₀"=> mainsea Y H V G.history G.clipped j false C χ
local notation "w'₀"=> doorstep Y H V G.history G.clipped j false C χ
local notation "L"=> ride Y H V G.history G.clipped j false C χ
local notation "S"=> peninsula Y H V G.history G.clipped j false C χ
local notation "F"=> osValue Y H V G j C χ
local notation "A₀"=> flank j 0
local notation "K₁"=> OSvector Y H V G j C χ
local notation "Pr"=> atEstate Y H V G.history G.clipped j false C χ
local notation "LpK" => Follows Y H V G j C χ
variable {A B : (indoor Y H V G.history G.clipped j false C χ).Op}
open Alliance
/- `charted`: pure spatial. Timing coordinate is completely ignored here. -/
noncomputable def charted (p: placement Λ): (indoor Y H V G.history G.clipped j false C χ).Op:= Alliance.raw (turnstile Y H V G.history G.clipped j false C χ) (look j) (fun i=> p i.val)
local notation "U"=>charted Y H V G j C χ
@[simp] lemma charted_nil : U 0=1:= Alliance.raw_zero ..
lemma concert (v t : placement Λ): U (v+t)= U v* U t:= Alliance.travelR (Jₛ) (look j) (fun i=> v i.val) (fun i=> t i.val)
lemma concert_one (X:placement Λ): U X* U (-X)=1:=by rw [←concert,add_neg_cancel,charted_nil]
lemma concert_heat (t:ℝ≥0)(v:placement Λ): Commute (U v) ((L).E t):= Alliance.hard (Jₛ) (look j) _ (fun _ _ _=> follows_road ..) _ -- maybe function annotation
lemma concert_bill (v: placement Λ): ‖U v‖ ≤1:=by
 apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; rw [one_mul]
 have h(t:List (Trans j)): ‖(Jₛ).raw t (fun i=>v i.val) x‖ ≤ ‖x‖:=by
   induction t with|nil=>exact le_rfl|cons i t ih=> rw [raw_step,ContinuousLinearMap.comp_apply]; exact (((Jₛ).crew i).pulls ..).trans ih
 exact h _
lemma concert_omega (v: placement Λ): U v w'₀=w'₀:=by
 have h(t:List (Trans j)): (Jₛ).raw t (fun i=>v i.val) w'₀=w'₀:=by
   induction t with|nil=> rfl|cons i t ih=> rw [raw_step,ContinuousLinearMap.comp_apply, ih]; exact (resides_real ..).2 _ _
 exact h _
lemma chart_away (x y:placement Λ) (p:∀ i:Trans j,x i.val=y i.val): U x= U y := by unfold charted; rw [funext (show ∀ i:Trans j, x i.val=y i.val from p)]
lemma chart_time (v: Gt): U (eject j v) =1:= by
 rw [chart_away Y H V G j C χ _ (0:placement Λ) (fun i=> eject_away j v i.val i.property),charted_nil]
lemma ensemble (p:placement Λ): Pr p=(L).E ((p j:ℝ).toNNReal)*U p:=rfl
local notation "hTr" x:max=> (L).E (Real.toNNReal (x:ℝ))
lemma heatbill (v:Gt): Pr (eject j v)=hTr v:= by rw [ensemble,chart_time,eject_at,mul_one]
lemma fare_less (p:placement Λ): ‖Pr p‖≤1:=by rw [ensemble]; exact (norm_mul_le ..).trans ((mul_le_mul ((L).shrinks _) (concert_bill ..) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
lemma bought_heat (s:ℝ≥0): (L).E s w'₀=w'₀:= ride_affordable Y H V G.history G.clipped j false C χ (fun _ _=> hinges ..) s
lemma staysVacuum (p:placement Λ): Pr p w'₀=w'₀:=by rw [ensemble,ContinuousLinearMap.mul_apply]; rw [concert_omega,bought_heat] -- tune
variable {x y: Sky (tent Y H)}{u v: marks (timeMesh Λ)}
lemma answer_oper (h: LpK x u A){v:Domain Y H G false (flank j 0)}(g : v.val=x): OSvector Y H V G j C χ v=A w'₀:=by
 obtain ⟨y,b,f⟩:= h.graph ⟨1,domain_one ..⟩
 rw [move_unit,mul_one] at b; rw [vacuum_ticket] at f; exact (congrArg K₁ (Subtype.ext (g.trans b.symm))).trans f -- notation h
lemma addScore (h: LpK x v A)(g: LpK y v B): Follows Y H V G j C χ (x+y) v (A+B):=by
 constructor
 · exact (D _).add_mem h.pose g.pose
 intro t; obtain ⟨a,h',m⟩:= h.graph t; obtain ⟨u,g',l⟩:=g.graph t
 refine ⟨a+u,by simp only [Submodule.coe_add,h',g',add_mul],?_⟩
 rw [map_add,m,l]; rfl
lemma subScore (h: LpK x v A)(g: LpK y v B): Follows Y H V G j C χ (x-y) v (A-B):=by
 refine ⟨(D _).sub_mem h.pose g.pose,fun t=>?_⟩
 obtain ⟨a,h',m⟩:= h.graph t; obtain ⟨u,g',l⟩:=g.graph t
 refine ⟨a-u,by simp only [Submodule.coe_sub,h',g']; exact (_root_.sub_mul x y _).symm,?_⟩
 rw [map_sub,m,l]; rfl
lemma scaleScore (h: LpK x v A)(c:ℂ): Follows Y H V G j C χ (c•x) v (c•A):=by
 refine ⟨(D _).smul_mem _ h.pose,fun t=>?_⟩
 obtain ⟨a,q,e⟩:= h.graph t; refine ⟨c • a,?_,?_⟩
 · rw [Submodule.coe_smul,q,sky_smul_mul Y H]; -- needs params?
 rw [map_smul,e]; rfl
lemma unitScore (u:Gt)(t:0≤(u:ℝ)): LpK 1 u (hTr u):=by
 constructor
 · exact domain_one ..
 intro x; have hy:0≤(eject j u j).val:= by simpa using t
 let hx:=later_frame Y H V G j x.val (eject j u) x.property hy
 refine ⟨⟨_,hx⟩,(by rw [one_mul]),?_⟩
 rw [transported_ket Y H V G j C χ x.val x.property _ hy,heatbill]
lemma zeroScore (u:Gt): Follows Y H V G j C χ 0 u 0:= ⟨(D _).zero_mem,fun _=>⟨0,(show _ from (zero_mul _).symm),map_zero _⟩⟩ -- mapzero defeq?

-- If B starts at z, and clocks allow the housing. Need tick gap positive for multiplying in Domain, here generic posit.
variable (p:placement Λ) (d: MeshClock.marks (timeMesh Λ))
local notation "p₂" => p-eject j u
local notation "p₃" => eject j d - (p+eject j v)
include V in
lemma allow_product (tu : (u:ℝ)<(p j:ℝ))(tv:0 ≤ (v:ℝ))(hp : ((p j+v: Gt):ℝ) ≤ (d:ℝ)) {q:Bool} (h: x∈Domain Y H G q (strip j 0 (u:ℝ)))(g:y∈Domain Y H G q (strip j 0 (v:ℝ)))(tz:0≤(u:ℝ)) : x*move K p y∈Domain Y H G q (strip j 0 (d:ℝ)):=by
 let z:=coordinates Λ p; change (p j:ℝ)+(v:ℝ)≤_ at hp
 apply domain_mult_to Y H G h (moving Y H V G p _ g)
 · apply Set.disjoint_left.mpr; rintro _ a ⟨y,t,rfl⟩; have hl:=t.1; have hh:=a.2; change y j+(p j:ℝ) ≤ _ at hh; linarith
 · exact fun i ht=>⟨ht.1,(ht.2 : i j ≤ (u:ℝ)).trans (by linarith)⟩
 rintro _ ⟨x,t,rfl⟩; change 0≤x j+(p j:ℝ) ∧ x j+(p j:ℝ)≤_; have hz:=t.1; have hw:=t.2; constructor <;> linarith

lemma boxAfter (tu : 0≤(u:ℝ)) (tv:0≤(v:ℝ)) (hp : (u:ℝ)<(p j:ℝ))(e : ((p j+v: Gt):ℝ) ≤ (d:ℝ))(h: LpK x u A)(g: LpK y v B): Follows Y H V G j C χ (x*move K p y) d ( A * Pr (p₂) * B * Pr (p₃)) :=by
 constructor
 · exact allow_product Y H V G j p d hp tv e h.pose g.pose tu
 let b:=p₂; let b':=p₃; have he:0≤(b j:ℝ):=by
   change 0≤(p j:ℝ)-((eject j u j).val); rw [eject_at]; linarith
 have hv:0≤(b' j:ℝ):= by change 0≤ ((eject j d j).val)- ((p j+ eject j v j: Gt):ℝ); rw [eject_at,eject_at]; exact sub_nonneg.mpr e
 intro t; obtain ⟨x',q,f⟩:= g.graph ⟨_,later_frame Y H V G j t.val b' t.property hv⟩
 obtain ⟨y',q',f'⟩:= h.graph ⟨_,later_frame Y H V G j x'.val b x'.property he⟩
 refine ⟨y', ?_,?_⟩
 · rw [q']; change x* move K (eject j u) (move K b x'.val)=_; rw [q]; change x* move K (eject j u) (move K b (y*move K (eject j v) (move K b' t.val)))=_; rw [move_sum]; simp only [move_prod,move_sum]; rw [show eject j u+b=p from (by unfold b; abel)];
   rw [show p + (eject j v+b')=eject j d from (by unfold b'; abel),mul_assoc]
 change _=A (Pr b (B (Pr b' (K₁ t))))
 rw [f',transported_ket Y H V G j C χ x'.val x'.property _ he,f,transported_ket Y H V G j C χ t.val t.property _ hv]
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.boxAfter
